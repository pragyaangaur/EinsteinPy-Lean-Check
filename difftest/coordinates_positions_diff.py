"""Differential test of coordinates/utils.py position and velocity conversions and conversion.py.

Handlers: ``coord.fast`` (the four ``*_fast`` functions, with and without velocities) and
``coord.conv`` (the ``convert_*`` methods of the conversion classes, including the two that go through
Cartesian coordinates, the ``KeyError`` for a missing ``M`` or ``a``, and a partly missing velocity).
Floats are compared bit for bit. See ``coordinates_common.py`` for the libm table.
"""

import numpy as np

import einsteinpy.coordinates.utils as cu
from einsteinpy.coordinates.conversion import (
    BoyerLindquistConversion,
    CartesianConversion,
    SphericalConversion,
)

from coordinates_common import (
    ang, alpha_val, classify, hexf, real, record, val,
)
from harness import run

FAST = {
    ("cart", "sph"): cu.cartesian_to_spherical_fast,
    ("cart", "bl"): cu.cartesian_to_bl_fast,
    ("sph", "cart"): cu.spherical_to_cartesian_fast,
    ("bl", "cart"): cu.bl_to_cartesian_fast,
}
CLS = {"cart": CartesianConversion, "sph": SphericalConversion, "bl": BoyerLindquistConversion}
DST = {"cart": "convert_cartesian", "sph": "convert_spherical", "bl": "convert_bl"}


def coords(rng, src, dst):
    """Three coordinates. For Cartesian input, bias toward axes, planes and the ring disc."""
    if src == "cart":
        a, b, c = val(rng), val(rng), val(rng)
        r = rng.random()
        if r < 0.1:
            a = 0.0
        elif r < 0.2:
            b = 0.0
        elif r < 0.3:
            a, b = 0.0, 0.0
        elif r < 0.4:
            c = 0.0
        return a, b, c
    return val(rng, scale=5), ang(rng), ang(rng)


def vel3(rng):
    return val(rng), val(rng), val(rng)


def gen_fast(rng):
    src, dst = rng.choice(list(FAST))
    t = val(rng)
    p = coords(rng, src, dst)
    vel = vel3(rng) if rng.random() < 0.55 else None
    need_alpha = "bl" in (src, dst)
    al = alpha_val(rng) if need_alpha else None
    if need_alpha and src == "cart" and rng.random() < 0.12:
        p = (rng.uniform(-1, 1) * (al or 1.0) * 0.5, rng.uniform(-1, 1) * (al or 1.0) * 0.5, 0.0)

    f = FAST[(src, dst)]

    def call(T=float):
        a = [T(x) for x in p]
        v = [T(x) for x in vel] if vel else []
        if need_alpha:
            return f(T(t), *a, T(al), *v, True) if vel else f(T(t), *a, T(al))
        return f(T(t), *a, *v, True) if vel else f(T(t), *a)

    # numba sees the same float64 values whatever the Python type, so vary it
    want = real(lambda: call(float if rng.random() < 0.5 else np.float64))
    table = record(lambda: call(np.float64))
    line = (f"coord.fast {src} {dst} {table} {hexf(al) if need_alpha else '-'} {hexf(t)} "
            f"{' '.join(hexf(x) for x in p)} {','.join(hexf(x) for x in vel) if vel else '-'}")
    return line, want, f"fast:{src}>{dst}:{'v' if vel else 'p'}:{classify(want)}"


def gen_conv(rng):
    src = rng.choice(list(CLS))
    dst = rng.choice([s for s in CLS if s != src] + [src] * 0)
    t = val(rng)
    p = coords(rng, src, dst)
    r = rng.random()
    vel = [None, None, None]
    if r < 0.5:
        vel = list(vel3(rng))
    elif r < 0.6:
        vel = list(vel3(rng))
        vel[rng.randrange(3)] = None
    M = rng.choice([1e30, 2e30, 1.0, 0.0, -1e30, 1e27, 5e30, 1e31]) if rng.random() < 0.8 else val(rng)
    a = rng.choice([0.0, 0.5, 1.0, 0.99, 0.1, 1.5, -0.1, float("nan")]) if rng.random() < 0.85 else val(rng)
    kw = {}
    r = rng.random()
    if r < 0.85:
        kw = {"M": M, "a": a}
    elif r < 0.92:
        kw = {"M": M}
    elif r < 0.97:
        kw = {"a": a}

    def call(T=float):
        obj = CLS[src](T(t), *[T(x) for x in p], *[None if x is None else T(x) for x in vel])
        return getattr(obj, DST[dst])(**{k: T(v) for k, v in kw.items()})

    want = real(call)
    table = record(lambda: call(np.float64))
    tok = lambda x: "-" if x is None else hexf(x)  # noqa: E731
    line = (f"coord.conv {src} {dst} {table} {tok(kw.get('M'))} {tok(kw.get('a'))} {hexf(t)} "
            f"{' '.join(hexf(x) for x in p)} {' '.join(tok(v) for v in vel)}")
    return line, want, f"conv:{src}>{dst}:{classify(want)}"


def gen(rng):
    return gen_fast(rng) if rng.random() < 0.6 else gen_conv(rng)


if __name__ == "__main__":
    run(gen, exe="epdiff_coordinates")
