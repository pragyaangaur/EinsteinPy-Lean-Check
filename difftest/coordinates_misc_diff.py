"""Differential test of ``lorentz_factor`` and ``v0`` in coordinates/utils.py.

``v0`` is a jitted function (division by zero raises), ``lorentz_factor`` is plain NumPy (it gives
``inf`` and ``nan`` without an exception). Floats are compared bit for bit.
"""

import numpy as np

from einsteinpy.coordinates.utils import lorentz_factor, v0

from coordinates_common import EDGE, classify, hexf, real, val
from coordinates_classes_diff import gmatrix, gtok
from harness import run


def speed(rng):
    r = rng.random()
    if r < 0.25:
        return rng.choice([0.0, -0.0, 299792458.0, -299792458.0, 1.0, 1e8, 2e8])
    if r < 0.3:
        return rng.choice(EDGE)
    if r < 0.85:
        return rng.uniform(-3e8, 3e8)
    return val(rng, scale=1e9)


def gen_lorentz(rng):
    v = [speed(rng) for _ in range(3)]
    if rng.random() < 0.2:
        v = [0.0, 0.0, 0.0]
    want = real(lambda: (lorentz_factor(*v),))
    return f"coord.lorentz {' '.join(hexf(x) for x in v)}", want, f"lorentz:{classify(want)}"


def gen_v0(rng):
    g = gmatrix(rng)
    v = [speed(rng) if rng.random() < 0.7 else val(rng) for _ in range(3)]
    want = real(lambda: (v0(np.ascontiguousarray(g, dtype=np.float64), *v),))
    return f"coord.v0 {gtok(g)} {' '.join(hexf(x) for x in v)}", want, f"v0:{classify(want)}"


def gen(rng):
    return gen_lorentz(rng) if rng.random() < 0.4 else gen_v0(rng)


if __name__ == "__main__":
    run(gen, exe="epdiff_coordinates")
