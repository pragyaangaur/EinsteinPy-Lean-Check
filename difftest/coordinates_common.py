"""Shared helpers for the Coordinates difftests.

A float travels as the 16 hex digits of its IEEE bit pattern, every NaN as ``nan``. This matches
``EinsteinpyLean.Coordinates.Diff`` on the Lean side.

The ``@jit`` functions of einsteinpy.coordinates.utils run under numba, and they call the C library
for hypot, atan2, acos, sin and cos. Lean cannot call the same C library for ``hypot``, so every case
carries a table of the C library calls that the code made, with their exact arguments and results. The
table is recorded by running the plain Python bodies of the same functions (``py_func``) with a
recording stand-in for ``numpy``, whose libm functions are numba-compiled so that they are the very
functions that the real run uses. The expected answer always comes from the real run, never from the
recording.
"""

import ast
import contextlib
import inspect
import textwrap
import math
import struct

import numpy as np
from numba import njit

import einsteinpy.coordinates.utils as cu

INF = float("inf")
NAN = float("nan")


def hexf(x):
    x = float(x)
    if math.isnan(x):
        return "nan"
    return format(struct.unpack(">Q", struct.pack(">d", x))[0], "016x")


@njit
def _hypot(a, b):
    return np.hypot(a, b)


@njit
def _atan2(a, b):
    return np.arctan2(a, b)


@njit
def _acos(a):
    return np.arccos(a)


@njit
def _sin(a):
    return np.sin(a)


@njit
def _cos(a):
    return np.cos(a)


@njit
def _sincos(a):
    return np.sin(a), np.cos(a)


class Recorder:
    """Stands in for ``numpy`` inside ``utils.py`` and records the libm calls."""

    def __init__(self):
        self.entries = {}

    def _two(self, k, f, a, b):
        r = f(float(a), float(b))
        self.entries[(k, hexf(a), hexf(b))] = hexf(r)
        return np.float64(r)

    def _one(self, k, f, a):
        r = f(float(a))
        self.entries[(k, hexf(a))] = hexf(r)
        return np.float64(r)

    def hypot(self, a, b):
        return self._two("H", _hypot, a, b)

    def arctan2(self, a, b):
        return self._two("T", _atan2, a, b)

    def arccos(self, a):
        return self._one("O", _acos, a)

    def _sc(self, a, which):
        # LLVM fuses sin(a) and cos(a) of the same argument into one sincos call, whose answers
        # can differ in the last bit from separate sin and cos calls, so record the pair.
        s, c = _sincos(float(a))
        self.entries[("S", hexf(a))] = hexf(s)
        self.entries[("C", hexf(a))] = hexf(c)
        return np.float64(s if which == 0 else c)

    def sin(self, a):
        return self._sc(a, 0)

    def cos(self, a):
        return self._sc(a, 1)

    def __getattr__(self, name):
        return getattr(np, name)

    def table(self):
        if not self.entries:
            return "-"
        return ",".join(":".join(k) + ":" + v for k, v in self.entries.items())


_JITTED = ["cartesian_to_spherical", "cartesian_to_spherical_novel", "cartesian_to_bl",
           "cartesian_to_bl_novel", "spherical_to_cartesian", "spherical_to_cartesian_novel",
           "bl_to_cartesian", "bl_to_cartesian_novel"]


class _Square(ast.NodeTransformer):
    """``x ** 2`` becomes ``np.square(x)``: numba compiles it to ``x * x``, NumPy scalars use ``pow``."""

    def visit_BinOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, ast.Pow) and isinstance(node.right, ast.Constant) and node.right.value == 2:
            return ast.copy_location(ast.Call(
                func=ast.Attribute(value=ast.Name(id="np", ctx=ast.Load()), attr="square", ctx=ast.Load()),
                args=[node.left], keywords=[]), node)
        return node


_PLAIN = {}


def _plain(fn):
    """The Python body of a jitted function, with squares as products."""
    name = fn.py_func.__name__
    if name not in _PLAIN:
        _PLAIN[name] = _plain_build(fn)
    return _PLAIN[name]


def _plain_build(fn):
    tree = ast.parse(textwrap.dedent(inspect.getsource(fn.py_func)))
    tree.body[0].decorator_list = []
    tree = ast.fix_missing_locations(_Square().visit(tree))
    ns = {}
    exec(compile(tree, "<plain>", "exec"), cu.__dict__, ns)  # noqa: S102
    return ns[fn.py_func.__name__]


@contextlib.contextmanager
def recording():
    """Run the plain Python bodies of the jitted functions with a recording ``np``."""
    rec = Recorder()
    saved = {n: getattr(cu, n) for n in _JITTED}
    saved["np"] = cu.np
    plain = {n: _plain(saved[n]) for n in _JITTED}
    try:
        for n in _JITTED:
            setattr(cu, n, plain[n])
        cu.np = rec
        yield rec
    finally:
        for n, v in saved.items():
            setattr(cu, n, v)


def record(fn):
    """The libm table of one call. Errors of the recording run are ignored, the real run decides."""
    with np.errstate(all="ignore"):
        with recording() as rec:
            try:
                fn()
            except Exception:  # noqa: BLE001
                pass
    return rec.table()


def render_result(res):
    return ",".join(hexf(x) for x in res)


def render_error(e):
    name = type(e).__name__
    if name == "ZeroDivisionError":
        return "E:ZeroDivisionError"
    return f"E:{name}:{e}"


def real(fn):
    """Run ``fn`` on the real (jitted) code and render a tuple of floats or the exception."""
    with np.errstate(all="ignore"):
        try:
            return render_result(fn())
        except Exception as e:  # noqa: BLE001
            return render_error(e)


def classify(ans):
    if ans.startswith("E:"):
        return ans.split(":")[1]
    return "nan" if "nan" in ans else "ok"


# ---- random floats

EDGE = [INF, -INF, NAN, 1e200, -1e200, 1e-200, 5e-324, 1e154, -1e154, 1e308]
SPECIAL = [0.0, -0.0, 1.0, -1.0, 2.0, -2.0, 0.5, -0.5, 3.0, 4.0, 10.0, 0.25]
ANGLES = [0.0, -0.0, math.pi, -math.pi, math.pi / 2, -math.pi / 2, 2 * math.pi, math.pi / 4,
          3 * math.pi / 4, 1e-9, math.pi - 1e-9, 1.0, 2.0, -1.0]


def val(rng, edge=0.06, scale=10.0):
    r = rng.random()
    if r < 0.3:
        return rng.choice(SPECIAL)
    if r < 0.3 + edge:
        return rng.choice(EDGE)
    if r < 0.8:
        return rng.uniform(-scale, scale)
    if r < 0.9:
        return rng.uniform(-1e6, 1e6)
    return rng.randint(-40, 40) / 8.0


def ang(rng):
    r = rng.random()
    if r < 0.35:
        return rng.choice(ANGLES)
    if r < 0.4:
        return rng.choice(EDGE)
    if r < 0.9:
        return rng.uniform(-7, 7)
    return rng.uniform(-1e3, 1e3)


def alpha_val(rng):
    r = rng.random()
    if r < 0.2:
        return 0.0
    if r < 0.3:
        return rng.choice([1.0, 0.5, -1.0, 1e-3, 1e5, 2.0])
    if r < 0.35:
        return rng.choice(EDGE)
    return rng.uniform(0, 5)
