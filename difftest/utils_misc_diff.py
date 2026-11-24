"""Differential test of scalar_factor.py, constant.py, units.py, exceptions.py and bodies.py.

Floats are compared bit for bit. Text that may hold spaces or newlines travels as hex.
"""

import random

import numpy as np
from astropy import units as u

from harness import run
from utils_common import NAN, hexf, moderate, pool, with_errors

from einsteinpy import constant
from einsteinpy.bodies import Body
from einsteinpy.coordinates.differential import (
    BoyerLindquistDifferential,
    CartesianDifferential,
    SphericalDifferential,
)
from einsteinpy.units import primitive
from einsteinpy.utils.exceptions import BaseError, CoordinateError
from einsteinpy.utils.scalar_factor import scalar_factor, scalar_factor_derivative

UNITS = {"s": u.s, "ms": u.ms, "us": u.us, "ks": u.ks, "min": u.min, "h": u.hour, "d": u.day,
         "yr": u.yr, "Myr": u.Myr, "Gyr": u.Gyr, "kg": u.kg, "g": u.g, "Msun": u.M_sun,
         "C": u.C, "mC": u.mC, "km": u.km, "m": u.m, "au": u.au, "pc": u.pc, "Hz": u.Hz,
         "deg": u.deg, "dimless": u.dimensionless_unscaled, "statC": u.statC}
TIME = ["s", "ms", "us", "ks", "min", "h", "d", "yr", "Myr", "Gyr"]
MASS = ["kg", "g", "Msun"]
CHARGE = ["C", "mC"]
LENGTH = ["km", "m", "au", "pc"]
BAD = ["Hz", "deg", "dimless", "statC", "kg", "m", "C"]


def with_msgs(fn):
    """Like with_errors, but TypeError and UnitsError keep their messages, which are mirrored."""
    try:
        return with_errors_raw(fn)
    except Exception as e:  # noqa: BLE001
        name = type(e).__name__
        return f"E:{name}:{e}" if name in ("TypeError", "UnitsError", "ValueError") else f"E:{name}"


def with_errors_raw(fn):
    with np.errstate(all="ignore"):
        return fn()


def hx(s):
    return s.encode().hex()


def hans(s):
    return "H" + hx(s)


def cls(r):
    return r[0] if r[0] in "FH" else r[:40]


# ---- scalar factor

def sf_case(rng):
    fd = rng.choice("fd")
    era = rng.choice(["md", "rd", "ded", "md", "rd", "ded", "", "MD", "x y", "mdd", None, "ded "])
    era_tok = "N" if era is None else "s" + hx(era)
    kind = rng.random()
    if kind < 0.08:
        t, t_tok = rng.choice([3.0, 3, None, "a"]), "p"
    else:
        un = rng.choice(TIME) if kind < 0.9 else rng.choice(BAD)
        val = pool(rng, extra=(1e10, 1e17, 1e30)) if rng.random() < 0.7 else rng.uniform(0, 100)
        t, t_tok = val * UNITS[un], f"q{hexf(val)}:{un}"
    tk = rng.choice("fin" if rng.random() < 0.8 else "f")
    tv = rng.choice([1.0, 1.5, 0.0, -2.0, 1e-30, pool(rng)]) if tk != "i" else rng.randint(-5, 5)
    tp_tok = {"f": "f" + hexf(tv), "n": "n" + hexf(tv), "i": f"i{tv}"}[tk]
    tp = {"f": float(tv), "n": np.float64(tv), "i": tv}[tk]
    fn = scalar_factor if fd == "f" else scalar_factor_derivative

    def f():
        return "F" + hexf(fn(t, era, tp))
    r = with_msgs(f)
    return f"sf.eval {fd} {era_tok} {tp_tok} {t_tok}", r, f"sf:{fd}:{cls(r)}"


def const_case(rng):
    n = rng.choice(["c", "G", "eps0", "coulombs_const", "Cosmo_Const", "Solar_Mass", "R_sun"])
    v = getattr(constant, n)
    v = v.value if hasattr(v, "value") else v
    return f"const.get {n}", "F" + hexf(v), f"const:{n}"


def body_row_case(rng):
    names = ["Sun", "Earth", "Moon", "Mercury", "Venus", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune", "Pluto"]
    n = rng.choice(names)
    from einsteinpy import bodies
    b = getattr(bodies, n)
    return (f"body.row {n}",
            f"F{hexf(b.mass.to(u.kg).value)} F{hexf(b.R.to(u.km).value)} {b.parent.name if b.parent else 'N'}",
            f"row:{n}")


# ---- exceptions

def rand_text(rng):
    alpha = "abc XYZ'\"\\\n\t01,/:;()[]e"
    return "".join(rng.choice(alpha) for _ in range(rng.randint(0, 6)))


def item(rng, nested=True):
    r = rng.random()
    if r < 0.35:
        s = rand_text(rng)
        return s, "s" + hx(s)
    if r < 0.6:
        n = rng.choice([0, 1, -1, 42, 10**30, -(10**20)])
        return n, f"i{n}"
    if r < 0.7:
        b = rng.random() < 0.5
        return b, "bT" if b else "bF"
    if r < 0.8:
        return None, "N"
    if nested:
        els = [item(rng, False) for _ in range(rng.randint(0, 3))]
        lst = rng.random() < 0.5
        if lst:
            return [e[0] for e in els], "L" + "/".join(e[1] for e in els)
        return tuple(e[0] for e in els), "T" + "/".join(e[1] for e in els)
    return None, "N"


def exc_case(rng):
    cl = rng.choice(["BaseError", "CoordinateError"])
    items = [item(rng) for _ in range(rng.randint(0, 4))]
    cls_ = {"BaseError": BaseError, "CoordinateError": CoordinateError}[cl]
    e = cls_(*[i[0] for i in items])
    assert repr(e) == str(e)
    tok = ",".join(i[1] for i in items) or "-"
    return f"exc.repr {cl} {tok}", hans(repr(e)), f"exc:{cl}:{len(items)}"


# ---- primitive

def prim_item(rng):
    r = rng.random()
    if r < 0.2:
        n = rng.randint(-5, 5)
        return n, f"i{n}"
    if r < 0.4:
        x = pool(rng)
        return x, "f" + hexf(x)
    if r < 0.5:
        x = pool(rng)
        return np.float64(x), "n" + hexf(x)
    if r < 0.58:
        return None, "N"
    if r < 0.68:
        s = rand_text(rng)
        return s, "s" + hx(s)
    if r < 0.78:
        un = rng.choice(list(UNITS))
        return UNITS[un], "u" + un
    un = rng.choice(list(UNITS))
    x = pool(rng)
    return x * UNITS[un], f"q{hexf(x)}:{un}"


def prim_render(x):
    if isinstance(x, u.Quantity):
        raise AssertionError
    if x is None:
        return "N"
    if isinstance(x, bool):
        raise AssertionError
    if isinstance(x, int):
        return f"i{x}"
    if isinstance(x, np.float64):
        return "n" + hexf(x)
    if isinstance(x, float):
        return "f" + hexf(x)
    if isinstance(x, str):
        return "s" + hx(x)
    if isinstance(x, u.UnitBase):
        for k, v in UNITS.items():
            if v is x or v == x:
                return "u" + k
    raise AssertionError(repr(x))


def prim_case(rng):
    items = [prim_item(rng) for _ in range(rng.randint(0, 5))]
    out = primitive(*[i[0] for i in items])
    # the unit objects of this table can compare equal (u.dimensionless and statC differ), keep the name
    rendered = []
    for (orig, t), o in zip(items, out):
        rendered.append("u" + t[1:] if isinstance(orig, u.UnitBase) else prim_render(o))
    return f"units.prim {','.join(i[1] for i in items) or '-'}", "[" + ",".join(rendered) + "]", f"prim:{len(items)}"


# ---- Body

def make_diff(kind):
    t = 0 * u.s
    if kind == "cart":
        return CartesianDifferential(t, 1 * u.m, 2 * u.m, 3 * u.m, 1 * u.m / u.s, 2 * u.m / u.s, 3 * u.m / u.s)
    if kind == "sph":
        return SphericalDifferential(t, 1 * u.m, 1 * u.rad, 1 * u.rad, 1 * u.m / u.s, 1 * u.rad / u.s, 1 * u.rad / u.s)
    if kind == "bl":
        return BoyerLindquistDifferential(t, 1 * u.m, 1 * u.rad, 1 * u.rad, 1 * u.m / u.s, 1 * u.rad / u.s, 1 * u.rad / u.s)
    return {"none": None, "falsy": 0, "other": "abc"}[kind]


def body_new_case(rng):
    args = {}
    toks = []
    base = {"mass": "kg", "q": "C", "R": "km"}
    for name, units in (("mass", MASS), ("q", CHARGE), ("R", LENGTH)):
        r = rng.random()
        if r < 0.15:
            toks.append(f"q{hexf(0.0)}:{base[name]}")  # the default value 0 * unit
        elif r < 0.2:
            args[name] = rng.choice([5, 3.0, "x", None])
            toks.append("p")
        else:
            un = rng.choice(units) if r < 0.85 else rng.choice(BAD)
            x = rng.choice([1.0, 5.0, 0.0, pool(rng)])
            args[name] = x * UNITS[un]
            toks.append(f"q{hexf(x)}:{un}")
    kind = rng.choice(["none", "falsy", "cart", "sph", "bl", "other"])

    def f():
        b = Body(coords=make_diff(kind), **args)
        return "ok:posvec" if hasattr(b, "pos_vec") and hasattr(b, "vel_vec") else "ok:noposvec"
    r = with_msgs(f)
    return f"body.new {' '.join(toks)} {kind}", r, f"bodynew:{kind}:{r[:8]}"


def body_str_case(rng):
    alpha = "ab  \t\nZ"
    name = "".join(rng.choice(alpha) for _ in range(rng.randint(0, 6)))
    pname = None if rng.random() < 0.3 else "".join(rng.choice(alpha) for _ in range(rng.randint(0, 5)))
    parent = Body(name=pname) if pname is not None else None
    b = Body(name=name, mass=rng.choice([1, 5.5]) * u.kg, R=rng.choice([0, 3]) * u.km, parent=parent)
    ptok = "N" if pname is None else "s" + hx(pname)
    line = f"body.str {hx(name)} {ptok} {hx(str(b.mass))} {hx(str(b.q))} {hx(str(b.R))} {hx(str(b.coords))}"
    return line, hans(str(b)), f"bodystr:{pname is None}:{'\n' in name}"


def gen(rng):
    r = rng.random()
    if r < 0.4:
        return sf_case(rng)
    if r < 0.45:
        return const_case(rng)
    if r < 0.5:
        return body_row_case(rng)
    if r < 0.65:
        return exc_case(rng)
    if r < 0.8:
        return prim_case(rng)
    if r < 0.92:
        return body_new_case(rng)
    return body_str_case(rng)


if __name__ == "__main__":
    run(gen, default_cases=50000, exe="epdiff_utils")
