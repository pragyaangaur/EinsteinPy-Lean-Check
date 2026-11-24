"""Shared helpers for the Utils difftests: float encoding and exception tags.

A float travels as the 16 hex digits of its IEEE bit pattern, every NaN as ``nan``. This
matches ``EinsteinpyLean.Utils.Codec`` on the Lean side.
"""

import math
import struct

import numpy as np

INF = float("inf")
NAN = float("nan")


def hexf(x):
    x = float(x)
    if math.isnan(x):
        return "nan"
    return format(struct.unpack(">Q", struct.pack(">d", x))[0], "016x")


def tag(e):
    name = type(e).__name__
    if isinstance(e, ValueError) and name == "ValueError":
        return f"E:ValueError:{e}"
    return f"E:{name}"


def with_errors(fn):
    """Run ``fn``, rendering an exception as its tag. Warnings from numpy are silenced."""
    with np.errstate(all="ignore"):
        try:
            return fn()
        except Exception as e:  # noqa: BLE001
            return tag(e)


def pool(rng, extra=()):
    """A float biased toward the edges of IEEE arithmetic."""
    r = rng.random()
    if r < 0.45:
        return rng.choice([0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 3.0, 0.25, 10.0, 1.5, *extra])
    if r < 0.6:
        return rng.choice([1e-200, -1e-200, 1e200, -1e200, 1e308, -1e308, 5e-324, 1e-310,
                           INF, -INF, NAN, math.pi, math.pi / 2, 1e154, 1e-154])
    if r < 0.8:
        return rng.uniform(-5, 5)
    if r < 0.9:
        return rng.randint(-64, 64) / 16.0
    return rng.uniform(-1e6, 1e6)


def moderate(rng):
    r = rng.random()
    if r < 0.4:
        return rng.choice([0.0, 1.0, -1.0, 0.5, 2.0, -2.0, 3.0, 0.25, 1.5, -0.5, 4.0, 10.0])
    return rng.uniform(-4, 4) if r < 0.8 else rng.randint(-32, 32) / 8.0
