"""Differential test of einsteinpy.utils.dual (DualNumber, _deriv, _diff_g, _jacobian_g).

Floats are compared bit for bit, every NaN as ``nan``. The operands are Python floats, Python
ints, ``numpy.float64`` and ``DualNumber`` itself, with many values at the edges (zeros,
infinities, NaN, 1e200, 1e308, denormals) so that the exceptions Python raises are hit. A case
answers with the dual, a float, a boolean or ``E:<exception class>``.
"""

import fractions
import math
import random

import numpy as np

from harness import run
from utils_common import INF, NAN, hexf, moderate, pool, tag, with_errors

from einsteinpy.utils.dual import DualNumber, _deriv, _diff_g, _jacobian_g

BIG = 10**400


def rd(d):
    return f"D{hexf(d.val)}:{hexf(d.deriv)}"


def cls(r):
    """Outcome class of an answer: its first letter, or the exception class."""
    return r[0] if r[0] in "DFBJ" else r.split(":")[1]


def render(r):
    if isinstance(r, DualNumber):
        return rd(r)
    if isinstance(r, (bool, np.bool_)):
        return f"B:{int(r)}"
    return f"F{hexf(r)}"


# ---- operands: ('f', x), ('i', n), ('n', x), ('d', (v, dv))

def tok(o):
    k, v = o
    if k == "f":
        return "f" + hexf(v)
    if k == "n":
        return "n" + hexf(v)
    if k == "i":
        return f"i{v}"
    return f"d{hexf(v[0])}:{hexf(v[1])}"


def obj(o):
    k, v = o
    if k == "f":
        return float(v)
    if k == "n":
        return np.float64(v)
    if k == "i":
        return int(v)
    return DualNumber(v[0], v[1])


def gen_dual(rng, mode="any"):
    f = moderate if mode == "mod" else pool
    return ("d", (f(rng), f(rng)))


def gen_scalar(rng, mode="any", kinds="fin"):
    k = rng.choice(list(kinds))
    f = moderate if mode == "mod" else pool
    if k == "i":
        if mode == "any" and rng.random() < 0.05:
            return ("i", rng.choice([BIG, -BIG]))
        return ("i", rng.choice([0, 0, 1, -1, 2, 3, -2, 5, rng.randint(-20, 20), rng.randint(-2**52, 2**52)]))
    return (k, f(rng))


def new_case(rng):
    a = gen_scalar(rng) if rng.random() < 0.85 else gen_dual(rng)
    b = gen_scalar(rng) if rng.random() < 0.85 else gen_dual(rng)
    r = with_errors(lambda: rd(DualNumber(obj(a), obj(b))))
    return f"dual.new {tok(a)} {tok(b)}", r, "new:" + cls(r)


OPS = ["add", "radd", "sub", "rsub", "drsub", "mul", "rmul", "div", "rdiv", "drdiv", "pow", "eq", "ne"]


def apply(op, a, b):
    if op == "add":
        return a + b
    if op == "radd":
        return b + a
    if op == "sub":
        return a - b
    if op == "rsub":
        return b - a
    if op == "drsub":
        return a.__rsub__(b)
    if op == "mul":
        return a * b
    if op == "rmul":
        return b * a
    if op == "div":
        return a / b
    if op == "rdiv":
        return b / a
    if op == "drdiv":
        return a.__rtruediv__(b)
    if op == "pow":
        return a**b
    if op == "eq":
        return a == b
    if op == "ne":
        return a != b
    raise ValueError(op)


def bin_case(rng):
    op = rng.choice(OPS)
    if op == "pow":
        # a moderate dual and a moderate exponent, sometimes a dual (no __rpow__) or the edge pool
        mode = "mod" if rng.random() < 0.8 else "any"
        a = gen_dual(rng, mode)
        b = gen_scalar(rng, mode) if rng.random() < 0.95 else gen_dual(rng)
        if rng.random() < 0.15:
            b = ("f", rng.choice([0.0, 1.0, 2.0, 3.0, 0.5, -1.0, -2.0, 400.0, 1e10, -0.5, 1/3]))
    else:
        mode = "any" if rng.random() < 0.7 else "mod"
        a = gen_dual(rng, mode)
        b = gen_dual(rng, mode) if rng.random() < (0.8 if op in ("eq", "ne") else 0.4) else gen_scalar(rng, mode)
        if op in ("rsub", "rdiv", "drsub", "drdiv", "radd", "rmul") and b[0] == "n":
            b = ("f", b[1])  # numpy scalar on the left goes through numpy, tested separately below
        if rng.random() < 0.1:  # equal values to hit the 0/0 branch
            a = ("d", (0.0, pool(rng)))
            b = ("d", (0.0, pool(rng))) if b[0] == "d" else b
    r = with_errors(lambda: render(apply(op, obj(a), obj(b))))
    return f"dual.bin {op} {tok(a)} {tok(b)}", r, f"bin:{op}:{cls(r)}"


def un_case(rng):
    op = rng.choice(["neg", "sin", "cos", "tan", "log", "exp"])
    a = gen_dual(rng)
    d = obj(a)
    fn = {"neg": lambda: -d, "sin": d.sin, "cos": d.cos, "tan": d.tan, "log": d.log, "exp": d.exp}[op]
    r = with_errors(lambda: rd(fn()))
    return f"dual.un {op} {tok(a)}", r, f"un:{op}:{cls(r)}"


# ---- programs

UN = ["neg", "sin", "cos", "tan", "log", "exp"]
CONST_OPS = ["addc", "raddc", "subc", "rsubc", "mulc", "rmulc", "divc", "rdivc"]


def instr_tok(i):
    name, c = i
    return name if c is None else f"{name}={tok(c)}"


def py_run(prog, x):
    st = [DualNumber(x, 1.0)]
    ret = None
    for name, c in prog:
        if name == "dup":
            st.append(st[-1])
        elif name in ("add", "sub", "mul", "div"):
            b = st.pop()
            a = st.pop()
            st.append({"add": a + b, "sub": a - b, "mul": a * b, "div": a / b}[name] if False else
                      (a + b if name == "add" else a - b if name == "sub" else a * b if name == "mul" else a / b))
        elif name == "neg":
            st.append(-st.pop())
        elif name in ("sin", "cos", "tan", "log", "exp"):
            st.append(getattr(st.pop(), name)())
        elif name == "pow":
            st.append(st.pop() ** obj(c))
        elif name == "retc":
            ret = obj(c)
        else:
            t = st.pop()
            k = obj(c)
            st.append({"addc": lambda: t + k, "raddc": lambda: k + t, "subc": lambda: t - k,
                       "rsubc": lambda: k - t, "mulc": lambda: t * k, "rmulc": lambda: k * t,
                       "divc": lambda: t / k, "rdivc": lambda: k / t}[name]())
    return st[-1], ret


def gen_prog(rng):
    depth = 1
    prog = []
    for _ in range(rng.randint(1, 6)):
        r = rng.random()
        if r < 0.1 and depth < 3:
            prog.append(("dup", None))
            depth += 1
        elif r < 0.3 and depth >= 2:
            prog.append((rng.choice(["add", "sub", "mul", "div"]), None))
            depth -= 1
        elif r < 0.55:
            prog.append((rng.choice(UN), None))
        elif r < 0.65:
            c = rng.choice([("i", 2), ("i", 2), ("i", 3), ("i", 0), ("i", -1), ("f", 0.5), ("f", 2.0), ("f", -1.5), ("f", 1 / 3), ("n", 0.5), ("n", -1.0)])
            prog.append(("pow", c))
        else:
            name = rng.choice(CONST_OPS)
            kinds = "fi" if name.startswith("r") else "fin"
            prog.append((name, gen_scalar(rng, "mod", kinds)))
    if rng.random() < 0.03:
        prog.append(("retc", rng.choice([("f", 2.5), ("i", 3), ("n", -1.0)])))
    return prog


def prog_case(rng):
    prog = gen_prog(rng)
    x = moderate(rng) if rng.random() < 0.85 else pool(rng)
    mode = rng.choice("dv")
    ptxt = ",".join(instr_tok(i) for i in prog)

    def f():
        top, ret = py_run(prog, x)
        if mode == "d":
            # _deriv: the function returns a plain number if the program ends with retc
            return render(_deriv(lambda q: ret if ret is not None else top, x))
        return render(ret if ret is not None else top) if not isinstance(ret if ret is not None else top, int) \
            else f"F{hexf(float(ret))}"
    r = with_errors(f)
    return f"dual.prog {mode} {hexf(x)} {ptxt}", r, f"prog:{mode}:{cls(r)}"


# ---- metrics

def arr(rows):
    a = np.empty((4, 4), dtype=object)
    for i in range(4):
        for j in range(4):
            a[i, j] = rows[i][j]
    return a


def m_schw(q, M):
    r = q[1]
    th = q[2]
    f = 1 - 2 * M / r
    gtt = -1 / f
    gthth = 1 / (r**2)
    s = th.sin()
    gpp = 1 / (r**2 * s**2)
    z = 0.0
    return arr([[gtt, z, z, z], [z, f, z, z], [z, z, gthth, z], [z, z, z, gpp]])


def m_kerr(q, a, M):
    r = q[1]
    th = q[2]
    c = th.cos()
    s = th.sin()
    a2 = a**2
    r2 = r**2
    c2 = c**2
    s2 = s**2
    sig = r2 + a2 * c2
    delta = r2 - 2 * M * r + a2
    big = (r2 + a2) ** 2
    t = a2 * delta
    gtt = -(big - t * s2) / (sig * delta)
    k = -2 * M * a
    gtp = k * r / (sig * delta)
    grr = delta / sig
    gthth = 1 / sig
    gpp = (delta - a2 * s2) / (sig * delta * s2)
    z = 0.0
    return arr([[gtt, z, z, gtp], [z, grr, z, z], [z, z, gthth, z], [gtp, z, z, gpp]])


def m_poly(q):
    return arr([[q[i] * (j + 1) + q[j] ** 2 * (i - 1) for j in range(4)] for i in range(4)])


def m_scaled(q, s):
    return arr([[q[0] * s for _ in range(4)] for _ in range(4)])


def m_const(q):
    return arr([[(-1.0 if i == 0 else 1.0) if i == j else 0 for j in range(4)] for i in range(4)])


METRICS = {"schw": (m_schw, 1), "kerr": (m_kerr, 2), "poly": (m_poly, 0), "scaled": (m_scaled, 1), "const": (m_const, 0)}


def gen_coords(rng, metric):
    def coord(kind):
        r = rng.random()
        if r < 0.1:
            return pool(rng)
        if kind == "r":
            return rng.uniform(0.3, 12.0) if r < 0.8 else rng.choice([0.0, 1.0, 2.0, 1e-3])
        if kind == "th":
            return rng.uniform(0.05, 3.1) if r < 0.8 else rng.choice([0.0, math.pi, math.pi / 2, 1.0])
        return rng.uniform(-5, 5)
    n = 4 if rng.random() < 0.97 else 3
    return [coord("t"), coord("r"), coord("th"), coord("p")][:n]


def gen_params(rng, metric):
    n = METRICS[metric][1]
    if metric == "scaled":
        return [rng.choice([1e308, -1e308, 2.0, 1e300, 0.5, 1e154])]
    if metric == "schw":
        return [rng.choice([1.0, 0.5, 2.0, 0.0, 1e10]) if rng.random() < 0.7 else pool(rng)]
    if metric == "kerr":
        return [rng.choice([0.0, 0.5, 0.9, 1.0, rng.uniform(-1, 1)]) if rng.random() < 0.85 else pool(rng),
                rng.choice([1.0, 0.5, 2.0]) if rng.random() < 0.9 else pool(rng)]
    return [pool(rng) for _ in range(n)]


def prms_tok(p):
    return ",".join(hexf(x) for x in p) if p else "-"


def gen_idx(rng):
    n = rng.choice([2] * 30 + [1, 3, 0])
    lst = [rng.choice([0, 1, 2, 3] * 6 + [-1, -4, 4, -5, 7]) for _ in range(n)]
    form = "t" if rng.random() < 0.88 else "l"
    return form, lst


def gen_wrt(rng):
    r = rng.random()
    if r < 0.9:
        return ("i", rng.randint(0, 3))
    if r < 0.96:
        return ("i", rng.choice([-1, 4, 5, -2, 100]))
    return ("f", rng.choice([0.0, 1.0, 2.0, 3.0, 4.0, -1.0, 7.0, -0.0]))


def wrt_tok(w):
    return f"i{w[1]}" if w[0] == "i" else f"f{hexf(w[1])}"


def wrt_obj(w):
    return w[1]


def diffg_case(rng):
    m = rng.choice(list(METRICS))
    fn = METRICS[m][0]
    prm = gen_params(rng, m)
    coords = gen_coords(rng, m)
    form, lst = gen_idx(rng)
    w = gen_wrt(rng)
    idx = tuple(lst) if form == "t" else list(lst)
    r = with_errors(lambda: f"F{hexf(_diff_g(fn, tuple(prm), coords, idx, wrt_obj(w)))}")
    line = f"dual.diffg {m} {prms_tok(prm)} {','.join(hexf(c) for c in coords) or '-'} {form}{'/'.join(map(str, lst))} {wrt_tok(w)}"
    return line, r, f"diffg:{m}:{cls(r)}"


def jacg_case(rng):
    m = rng.choice(list(METRICS))
    fn = METRICS[m][0]
    prm = gen_params(rng, m)
    coords = gen_coords(rng, m)
    w = gen_wrt(rng) if rng.random() < 0.3 else ("i", rng.randint(0, 3))

    def f():
        J = _jacobian_g(fn, tuple(prm), coords, wrt_obj(w))
        return "J" + " ".join(hexf(x) for x in J.flatten())
    r = with_errors(f)
    line = f"dual.jacg {m} {prms_tok(prm)} {','.join(hexf(c) for c in coords) or '-'} {wrt_tok(w)}"
    return line, r, f"jacg:{m}:{cls(r)}"


# ---- exact rationals

def rat_tok(q):
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def dy(rng):
    return fractions.Fraction(rng.randint(-40, 40), 2 ** rng.randint(0, 5))


def rat_case(rng):
    o1 = rng.choice(["add", "sub", "mul"])
    o2 = rng.choice(["add", "sub", "mul"])
    ds = [(dy(rng), dy(rng)) for _ in range(3)]
    pd = [DualNumber(float(v), float(d)) for v, d in ds]

    def ap(o, x, y):
        return x + y if o == "add" else x - y if o == "sub" else x * y
    res = ap(o2, ap(o1, pd[0], pd[1]), pd[2])
    exp = f"{rat_tok(fractions.Fraction(res.val))}:{rat_tok(fractions.Fraction(res.deriv))}"
    line = f"dual.rat {o1} {o2} " + " ".join(f"{rat_tok(v)}:{rat_tok(d)}" for v, d in ds)
    return line, exp, f"rat:{o1}"


def gen(rng):
    r = rng.random()
    if r < 0.06:
        return new_case(rng)
    if r < 0.38:
        return bin_case(rng)
    if r < 0.46:
        return un_case(rng)
    if r < 0.66:
        return prog_case(rng)
    if r < 0.8:
        return diffg_case(rng)
    if r < 0.9:
        return jacg_case(rng)
    return rat_case(rng)


if __name__ == "__main__":
    run(gen, default_cases=50000, exe="epdiff_utils")
