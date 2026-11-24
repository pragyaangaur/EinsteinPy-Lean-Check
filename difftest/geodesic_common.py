"""Shared helpers for the Geodesic difftests.

A float travels as the 16 hex digits of its IEEE bit pattern, every NaN as ``nan``, as in
``EinsteinpyLean.Utils.Codec``. Lists are comma separated and ``-`` is the empty list. Answers
are rendered the same way, or as ``E:<exception class>``.
"""

import math
import struct
import warnings

import numpy as np

from einsteinpy.geodesic.utils import _kerr, _kerrnewman, _sch

INF = float("inf")
NAN = float("nan")

KINDS = {"sch": _sch, "kerr": _kerr, "kn": _kerrnewman}
NPARAMS = {"sch": 0, "kerr": 1, "kn": 2}
NAMES = {"sch": "Schwarzschild", "kerr": "Kerr", "kn": "KerrNewman"}


def hexf(x):
    x = float(x)
    if math.isnan(x):
        return "nan"
    return format(struct.unpack(">Q", struct.pack(">d", x))[0], "016x")


def hl(xs):
    xs = list(xs)
    return ",".join(hexf(x) for x in xs) if xs else "-"


def hopt(x):
    return "-" if x is None else hexf(x)


def err(e):
    return f"E:{type(e).__name__}"


def real(fn):
    """Run ``fn`` returning a string. NumPy and Python warnings are silenced, exceptions become tags."""
    with np.errstate(all="ignore"), warnings.catch_warnings():
        warnings.simplefilter("ignore")
        try:
            return fn()
        except Exception as e:  # noqa: BLE001
            return err(e)


def classify(ans):
    if ans.startswith("E:"):
        return ans
    return "nan" if "nan" in ans else "ok"


def flat(a):
    return [float(x) for x in np.asarray(a, dtype=object).ravel()]


def arr(xs, obj=False):
    if obj:
        a = np.empty(len(xs), dtype=object)
        for i, x in enumerate(xs):
            a[i] = np.float64(x)
        return a
    return np.array(xs, dtype=float)


# ---- random numbers

EDGE = [INF, -INF, NAN, 1e200, -1e200, 1e-200, 5e-324, 1e154, 1e308, -1e308]
SPECIAL = [0.0, -0.0, 1.0, -1.0, 2.0, -2.0, 0.5, -0.5, 3.0, 4.0, 10.0, 0.25]
ANGLES = [0.0, -0.0, math.pi, -math.pi, math.pi / 2, -math.pi / 2, 2 * math.pi, math.pi / 4,
          math.pi / 3, 1e-9, math.pi - 1e-9, 1.0, 2.0, -1.0, 3 * math.pi / 2]


def fl(rng, edge=0.05, scale=5.0):
    r = rng.random()
    if r < 0.2:
        return rng.choice(SPECIAL)
    if r < 0.2 + edge:
        return rng.choice(EDGE)
    if r < 0.85:
        return rng.uniform(-scale, scale)
    return rng.randint(-40, 40) / 8.0


def radius(rng, edge=0.04):
    """A Boyer-Lindquist radius, biased to horizon-like values."""
    r = rng.random()
    if r < 0.15:
        return rng.choice([2.0, 1.0, 3.0, 0.0, 4.0, 6.0, 10.0, 0.5, 1.5, 2.5, 5.0])
    if r < 0.15 + edge:
        return rng.choice(EDGE)
    if r < 0.8:
        return rng.uniform(1.0, 30.0)
    if r < 0.9:
        return rng.uniform(-3.0, 3.0)
    return rng.uniform(0.01, 1e4)


def angle(rng, edge=0.03):
    r = rng.random()
    if r < 0.3:
        return rng.choice(ANGLES)
    if r < 0.3 + edge:
        return rng.choice(EDGE)
    if r < 0.9:
        return rng.uniform(0.05, math.pi - 0.05)
    return rng.uniform(-7, 7)


def spin(rng):
    r = rng.random()
    if r < 0.25:
        return rng.choice([0.0, 0.5, 0.9, 1.0, 0.99, -0.5, 2.0, 1e-3])
    if r < 0.3:
        return rng.choice(EDGE)
    return rng.uniform(-1.2, 1.2)


def charge(rng):
    r = rng.random()
    if r < 0.25:
        return rng.choice([0.0, 0.5, 0.1, 1.0, -0.3, 2.0])
    if r < 0.3:
        return rng.choice(EDGE)
    return rng.uniform(-1.2, 1.2)


def params(rng, kind):
    if kind == "sch":
        return [rng.choice([0.0, 0.5, 1.0, 7.0])] if rng.random() < 0.3 else []
    if kind == "kerr":
        return [spin(rng)]
    return [spin(rng), charge(rng)]


def position(rng, kind=None):
    return [radius(rng), angle(rng), angle(rng)]


def q4(rng):
    return [rng.choice([0.0, 0.0, 1.0, -2.0, fl(rng)]), radius(rng), angle(rng), angle(rng)]


def good_radius(rng, kind, prm):
    """A radius outside the horizon so integrations behave."""
    a = abs(prm[0]) if prm else 0.0
    q = abs(prm[1]) if len(prm) > 1 else 0.0
    rp = 1 + math.sqrt(max(0.0, 1 - a * a - q * q))
    return rp + rng.uniform(1.5, 25.0)


def good_angle(rng):
    return rng.uniform(0.3, math.pi - 0.3)


def moderate(rng, scale=0.4):
    return rng.choice([0.0, rng.uniform(-scale, scale), rng.uniform(-scale, scale)])
