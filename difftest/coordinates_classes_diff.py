"""Differential test of core.py and differential.py: the classes with units, and ``velocity(metric)``.

Handlers: ``coord.cls`` (a class with astropy units, one of its methods), ``coord.alpha``
(``BaseMetric.alpha``, which every Boyer-Lindquist conversion calls) and ``coord.vel``
(``velocity(metric)`` with a stand-in metric that has only ``coords.system`` and
``metric_covariant``). Floats are compared bit for bit, exceptions by class and message.
"""

import numpy as np
from astropy import units as u

from einsteinpy.coordinates.core import BoyerLindquist, Cartesian, Spherical
from einsteinpy.coordinates.differential import (
    BoyerLindquistDifferential,
    CartesianDifferential,
    SphericalDifferential,
)
from einsteinpy.metric import BaseMetric

from coordinates_common import (
    EDGE, ang, alpha_val, classify, hexf, real, record, render_error, val,
)
from harness import run

CORE = {"cart": Cartesian, "sph": Spherical, "bl": BoyerLindquist}
DIFF = {"cart": CartesianDifferential, "sph": SphericalDifferential, "bl": BoyerLindquistDifferential}
NAME = {"cart": "cartesian", "sph": "spherical", "bl": "bl"}
LONG = {"cart": "Cartesian", "sph": "Spherical", "bl": "BoyerLindquist"}

TIME = [u.s, u.s, u.ms, u.min, u.hour, u.day, u.yr]
LEN = [u.m, u.m, u.km, u.cm, u.au, u.pc]
ANG = [u.rad, u.rad, u.deg, u.arcmin, u.arcsec, u.cycle]
SPEED = [u.m / u.s, u.m / u.s, u.km / u.s, u.km / u.h, u.cm / u.s]
ANGSPEED = [u.rad / u.s, u.rad / u.s, u.deg / u.s, u.arcsec / u.yr, u.deg / u.h]
BAD = [u.kg, u.Hz, u.dimensionless_unscaled, u.C, u.K, u.m ** 2, u.m / u.s ** 2, u.rad / u.m,
       u.s, u.m, u.rad, u.m / u.s, u.rad / u.s, u.deg, u.km]
BASES = {"m": 0, "kg": 1, "s": 2, "rad": 3}


def unit_token(unit, value):
    d = unit.decompose()
    ex = [0, 0, 0, 0]
    other = 0
    for b, p in zip(d.bases, d.powers):
        if str(b) in BASES:
            ex[BASES[str(b)]] += int(p)
        else:
            other = 1
    return "_".join(map(str, ex)) + f"_{other}:{hexf(unit.si.scale)}:{hexf(value)}"


def slots(sys, diff):
    pos = [TIME, LEN, LEN, LEN] if sys == "cart" else [TIME, LEN, ANG, ANG]
    vel = [SPEED] * 3 if sys == "cart" else [SPEED, ANGSPEED, ANGSPEED]
    return pos + (vel if diff else [])


def quantities(rng, sys, diff):
    toks, objs = [], []
    for i, fam in enumerate(slots(sys, diff)):
        is_ang = fam is ANG
        x = ang(rng) if is_ang else val(rng, scale=5)
        if rng.random() < 0.08:
            x = rng.choice(EDGE)
        r = rng.random()
        if r < 0.012:
            toks.append(f"none:{hexf(x)}")
            objs.append(x)
        else:
            un = rng.choice(fam) if r < 0.975 else rng.choice(BAD)
            toks.append(unit_token(un, x))
            objs.append(x * un)
    return toks, objs


def gen_cls(rng):
    sys = rng.choice(list(CORE))
    diff = rng.random() < 0.5
    toks, objs = quantities(rng, sys, diff)
    cls = (DIFF if diff else CORE)[sys]
    others = [s for s in CORE if s != sys]
    r = rng.random()
    if r < 0.12:
        meth, mtok = "values", "values"
    elif r < 0.24:
        meth, mtok = "position", "position"
    elif r < 0.5:
        d = rng.choice(others)
        meth, mtok = f"convert_{ {'cart': 'cartesian', 'sph': 'spherical', 'bl': 'bl'}[d] }", f"convert:{d}"
    else:
        d = rng.choice(others)
        meth = f"{NAME[d]}_differential" if diff else f"to_{ {'cart': 'cartesian', 'sph': 'spherical', 'bl': 'bl'}[d] }"
        mtok = f"to:{d}"
    M = rng.choice([1e30, 2e30, 1.0, 0.0, -1e30, 1e27, 5e30]) if rng.random() < 0.85 else val(rng)
    a = rng.choice([0.0, 0.5, 1.0, 0.99, 0.1, 1.5, -0.1, float("nan")]) if rng.random() < 0.85 else val(rng)
    kw = {}
    r = rng.random()
    if r < 0.85:
        kw = {"M": M, "a": a}
    elif r < 0.92:
        kw = {"M": M}
    elif r < 0.97:
        kw = {"a": a}
    wrap = rng.random() < 0.25

    def call():
        obj = cls(*objs)
        k = dict(kw)
        if wrap and "M" in k:
            k["M"] = k["M"] * u.kg
        if wrap and "a" in k:
            k["a"] = k["a"] * u.dimensionless_unscaled
        if mtok == "values":
            return obj.values()
        if mtok == "position":
            return obj.position()
        res = getattr(obj, meth)(**k)
        return res if mtok.startswith("convert") else res.values()

    want = real(call)
    table = record(call)
    tok = lambda x: "-" if x is None else hexf(x)  # noqa: E731
    line = f"coord.cls {sys} {int(diff)} {mtok} {table} {tok(kw.get('M'))} {tok(kw.get('a'))} {' '.join(toks)}"
    return line, want, f"cls:{'d' if diff else 'c'}:{mtok.split(':')[0]}:{classify(want)}"


def gen_alpha(rng):
    M = rng.choice([1e30, 2e30, 1.0, 0.0, -1e30, 1e27, 5e30, 1e308, 1e-300]) if rng.random() < 0.7 else val(rng)
    a = rng.uniform(0, 1) if rng.random() < 0.6 else rng.choice([0.0, 1.0, 0.5, 1.0000000000000002, -1e-300, float("nan"), 2.0])
    want = real(lambda: (BaseMetric.alpha(np.float64(M), np.float64(a)),))
    return f"coord.alpha {hexf(M)} {hexf(a)}", want, f"alpha:{classify(want)}"


class StubCoords:
    def __init__(self, system):
        self.system = system


class StubMetric:
    def __init__(self, system, g):
        self.coords = StubCoords(system)
        self._g = g

    def metric_covariant(self, position):
        return self._g


def gmatrix(rng):
    r = rng.random()
    if r < 0.4:
        g = np.diag([1.0, -1.0, -1.0, -1.0]) * rng.choice([1.0, 1.0, 0.5, 2.0, 1.0 - 1e-6])
        if rng.random() < 0.5:
            g = g + np.array([[rng.uniform(-1e-3, 1e-3) for _ in range(4)] for _ in range(4)])
        return g
    if r < 0.55:
        rr = rng.uniform(2, 20)
        f = 1 - 1 / rr
        th = rng.uniform(0.2, 2.9)
        return np.diag([f, -1 / f, -rr ** 2, -(rr * np.sin(th)) ** 2])
    if r < 0.85:
        return np.array([[val(rng, scale=3) for _ in range(4)] for _ in range(4)])
    g = np.diag([rng.choice([0.0, 1.0, -1.0, 1e-300]), -1.0, -1.0, -1.0])
    return g


def gtok(g):
    return ",".join(hexf(x) for x in np.asarray(g, dtype=float).reshape(-1))


def gen_vel(rng):
    sys = rng.choice(list(CORE))
    toks, objs = quantities(rng, sys, True)
    # a velocity of the order of c is more interesting than a few metres per second
    if rng.random() < 0.6:
        for i in (4, 5, 6):
            x = rng.uniform(-3e8, 3e8) if rng.random() < 0.8 else val(rng, scale=1e9)
            fam = slots(sys, True)[i]
            un = rng.choice(fam)
            toks[i] = unit_token(un, x)
            objs[i] = x * un
    name = LONG[sys] if rng.random() < 0.65 else rng.choice(["Cartesian", "Spherical", "BoyerLindquist", "Kerr", "Other"])
    g = gmatrix(rng)

    def call():
        return DIFF[sys](*objs).velocity(StubMetric(name, g))

    want = real(call)
    line = f"coord.vel {sys} {name} {gtok(g)} {' '.join(toks)}"
    return line, want, f"vel:{name == LONG[sys]}:{classify(want)}"


def gen(rng):
    r = rng.random()
    if r < 0.62:
        return gen_cls(rng)
    if r < 0.72:
        return gen_alpha(rng)
    return gen_vel(rng)


if __name__ == "__main__":
    run(gen, exe="epdiff_coordinates")
