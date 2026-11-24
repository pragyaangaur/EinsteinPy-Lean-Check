"""Shared helpers for the Metric difftests: float encoding, a stub coordinate object, parameter pools.

A float travels as the 16 hex digits of its IEEE bit pattern, every NaN as ``nan``, as in
``EinsteinpyLean.Utils.Codec``. An array answer is ``A:`` and the entries in row-major order.
"""

import math
import sys

import numpy as np
from astropy import units as u

sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))
from utils_common import hexf, tag, with_errors  # noqa: E402,F401

from einsteinpy import constant  # noqa: E402

C = constant.c.value
G = constant.G.value
CC = constant.coulombs_const.value
SQRT_G_OVER_CC = math.sqrt(G / CC)

SYS = {"S": "Spherical", "B": "BoyerLindquist", "C": "Cartesian"}


class Coords:
    """Only the ``system`` attribute of a coordinate object is read by the metric classes."""

    def __init__(self, system):
        self.system = system


def fl(x):
    return "F" + hexf(x)


def arr(a):
    return "A:" + " ".join(hexf(v) for v in np.asarray(a, dtype=float).ravel())


def classify(ans):
    if ans.startswith("E:"):
        return ans.split(":")[1]
    if ans.startswith("A:") or ans.startswith("F") or ans.startswith("S:"):
        toks = ans[2:].split() if ans[0] in "AS" else [ans[1:]]
        bad = any(t == "nan" or t.lower().startswith(("7ff", "fff")) for t in toks if len(t) == 16 or t == "nan")
        return "nonfinite" if bad else "finite"
    return "other"


# ---- parameter pools ---------------------------------------------------------------------------------------

def mass(rng):
    r = rng.random()
    if r < 0.82:
        return 10 ** rng.uniform(22, 33)
    if r < 0.9:
        return rng.choice([1.989e30, 5.972e24, 1.0, 1e40, 1e-5])
    if r < 0.94:
        return rng.choice([0.0, -0.0, -1e30])
    return rng.choice([float("inf"), float("nan"), 5e-324, 1e300])


def spin(rng):
    r = rng.random()
    if r < 0.7:
        return rng.random()
    if r < 0.82:
        return rng.choice([0.0, 1.0, 0.5, 0.999999, 1e-9])
    if r < 0.92:
        return rng.choice([-0.1, 1.5, -1e-12, 1.0000000000000002, 2.0, -0.0])
    return rng.choice([float("nan"), float("inf"), -float("inf")])


def charge(rng, M):
    """A charge in coulombs, around the extremal value ``M * sqrt(G / Cc)`` of the mass."""
    r = rng.random()
    if r < 0.2:
        return 0.0
    if r < 0.85 and math.isfinite(M) and M > 0:
        return M * SQRT_G_OVER_CC * rng.uniform(0, 1.2) * rng.choice([1, 1, -1])
    if r < 0.92:
        return 10 ** rng.uniform(5, 25)
    return rng.choice([-0.0, float("nan"), float("inf"), 1e-300, 1e200])


def radius(rng, M):
    """A radius in metres, in units of the Schwarzschild radius most of the time."""
    rs = 2 * G * M / C ** 2 if math.isfinite(M) and M > 0 else 1.0
    r = rng.random()
    if r < 0.8:
        return rs * 10 ** rng.uniform(-1, 1.5)
    if r < 0.88:
        return rng.choice([rs, 0.5 * rs, 2 * rs, rs * 1.5, 1.0, 1e4])
    if r < 0.94:
        return rng.choice([0.0, -0.0, -rs, 1e-300, 1e200, 1e-200])
    return rng.choice([float("inf"), float("nan"), -float("inf"), 1e154, 1e155])


def angle(rng):
    r = rng.random()
    if r < 0.8:
        return rng.uniform(0.01, math.pi - 0.01)
    if r < 0.9:
        return rng.choice([math.pi / 2, math.pi / 3, math.pi / 4, 1.0, 2.0, 0.5])
    if r < 0.96:
        return rng.choice([0.0, -0.0, math.pi, 1e-300, -1.0, 4.0, 7.0, 2 * math.pi, 1e-10])
    return rng.choice([float("nan"), float("inf"), 1e22])


def arg_vec(rng):
    r = rng.random()
    if r < 0.85:
        return rng.uniform(-3, 3)
    if r < 0.95:
        return rng.choice([0.0, 1.0, -1.0, 0.5, 2.0, C, 1e8])
    return rng.choice([float("nan"), float("inf"), 1e300])


def qpm(rng):
    r = rng.random()
    if r < 0.4:
        return 0.0
    if r < 0.85:
        return rng.uniform(-1, 1) * 10 ** rng.uniform(-12, 12)
    return rng.choice([1e18, -1e18, 1.0, -1.0, 1e-30, float("nan")])


def cx(*xs):
    return " ".join(hexf(x) for x in xs)
