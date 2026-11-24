"""Differential test of the predefined metrics against the Lean model.

Every metric function of ``einsteinpy.symbolic.predefined`` is called for real and its
sympy components are evaluated at random rational points. Parameters that are plain
rationals (``c``, ``G``, ``eps_0``, ``sch``, ``a``, ``Q``, ``k``, ``B``, ``M``, ``gam``,
``lambd``) are passed to the function. The coordinates are replaced by rationals
afterwards with ``xreplace``.

The transcendental pieces cannot be rational, so they are replaced in the real sympy
components by extra rational inputs, which the Lean model also takes:

* ``sin(theta)`` and ``cos(theta)`` by a Pythagorean pair ``s``, ``co`` with ``s^2+co^2=1``
  (also ``cos(t)`` in AntiDeSitter); ``sinh`` and ``cosh`` by a hyperbolic pair.
* ``exp(...)`` in DeSitter, BertottiKasner and Godel by a given value ``E`` (in Godel the
  call with twice the exponent becomes ``E**2``), in BesselGravitationalWave by the
  given ``eu = exp(U)`` and ``ek = exp(K)`` (``exp(2K-2U)`` becomes ``ek^2/eu^2``).
* ``tanh`` in AlcubierreWarp by three given values, ``pi`` in KerrNewman and
  ReissnerNordstorm by a given rational, and in Davidson ``t`` and ``1+r^2`` by cubes
  and fifth powers of given rationals so that the fractional powers become rational.
* The undefined functions ``a(t)`` (FLRW), ``f(x)`` and ``h(y)`` (CMetric) by given values.

A component with ``zoo`` or ``nan`` in it counts as the single error ``zerodiv``.
"""

import sys
import warnings

import sympy
from sympy import Rational as Q
from sympy.core.function import AppliedUndef

from harness import render, rat_str, run

from einsteinpy.symbolic.predefined import (
    AlcubierreWarp,
    AntiDeSitter,
    AntiDeSitterStatic,
    BarriolaVilekin,
    BertottiKasner,
    BesselGravitationalWave,
    CMetric,
    Davidson,
    DeSitter,
    Ernst,
    FriedmannLemaitreRobertsonWalker,
    Godel,
    JanisNewmanWinicour,
    Kerr,
    KerrNewman,
    KerrNewmanDeSitter,
    MinkowskiCartesian,
    MinkowskiPolar,
    ReissnerNordstorm,
    Schwarzschild,
)

warnings.filterwarnings("ignore")

VALUES = [Q(v) for v in (-3, -2, -1, Q(-1, 2), Q(1, 3), Q(1, 2), Q(2, 3), 1, Q(5, 4), 2, 3, 5)]
ZERO = Q(0)
PI_VALUES = [Q(22, 7), Q(355, 113), Q(3), Q(157, 50), ZERO]


def rv(rng, zero=0.06):
    return ZERO if rng.random() < zero else rng.choice(VALUES)


def trig_pair(rng):
    """(s, co) with s^2 + co^2 = 1, including the corner cases 0 and +-1."""
    k = rng.random()
    if k < 0.08:
        return ZERO, Q(rng.choice((1, -1)))
    if k < 0.16:
        return Q(rng.choice((1, -1))), ZERO
    u, v = rng.randint(-4, 4), rng.randint(-4, 4)
    if u == 0 and v == 0:
        return ZERO, Q(1)
    return Q(2 * u * v, u * u + v * v), Q(u * u - v * v, u * u + v * v)


def hyp_pair(rng):
    """(sinh, cosh) with cosh^2 - sinh^2 = 1."""
    if rng.random() < 0.08:
        return ZERO, Q(1)
    u, v = rng.choice([1, 2, 3, 4]), rng.choice([1, 2, 3, 4, -1, -2, -3])
    return Q(u * u - v * v, 2 * u * v), Q(u * u + v * v, 2 * u * v)


def sym(arr, name):
    for s in arr.free_symbols:
        if s.name == name:
            return s
    return None


def entries(arr):
    return list(sympy.flatten(arr.tolist()))


def finish(arr, rules=(), subs=None, func_rules=()):
    """Apply the replacement rules, substitute the symbols and render or flag zerodiv."""
    out = []
    for e in entries(arr):
        for kind, fn in rules:
            e = e.replace(kind, fn)
        for pred, fn in func_rules:
            e = e.replace(lambda x: isinstance(x, AppliedUndef) and pred(x), fn)
        if subs:
            e = e.xreplace({k: v for k, v in ((sym_ if False else k, v) for k, v in subs.items())})
        out.append(e)
    if any(e.has(sympy.zoo, sympy.nan, sympy.oo, -sympy.oo) for e in out):
        return "ERR zerodiv", "zerodiv"
    for e in out:
        assert e.is_Rational, (e, "not rational")
    return render((4, 4), out), "ok"


def by_name(arr, **vals):
    """Map symbol objects found in ``arr`` (by name) to the given values."""
    d = {}
    for name, v in vals.items():
        s = sym(arr, name)
        if s is not None:
            d[s] = v
    return d


def toks(*xs):
    return " ".join(rat_str(x) for x in xs)


def tensor_of(m):
    return m.tensor()


# ---- one generator per metric: returns (line, expected, class)


def g_mink(rng):
    c = rv(rng)
    m = MinkowskiCartesian(c=c)
    exp, cls = finish(m.tensor())
    return f"predef.mink {toks(c)}", exp, cls


def g_minkp(rng):
    c, r = rv(rng), rv(rng)
    s, _ = trig_pair(rng)
    m = MinkowskiPolar(c=c)
    a = m.tensor()
    exp, cls = finish(a, [(sympy.sin, lambda x: s)], by_name(a, r=r))
    return f"predef.minkp {toks(c, r, s)}", exp, cls


def g_schw(rng):
    c, sch, r = rv(rng), rv(rng), rv(rng)
    s, _ = trig_pair(rng)
    a = Schwarzschild(c=c, sch=sch).tensor()
    exp, cls = finish(a, [(sympy.sin, lambda x: s)], by_name(a, r=r))
    return f"predef.schw {toks(c, sch, r, s)}", exp, cls


def g_kerr(rng):
    c, sch, aa, r = rv(rng), rv(rng), rv(rng), rv(rng)
    s, co = trig_pair(rng)
    a = Kerr(c=c, sch=sch, a=aa).tensor()
    exp, cls = finish(a, [(sympy.sin, lambda x: s), (sympy.cos, lambda x: co)], by_name(a, r=r))
    return f"predef.kerr {toks(c, sch, aa, r, s, co)}", exp, cls


def g_kn(rng):
    c, g, e0, sch, aa, q, r = [rv(rng) for _ in range(7)]
    pi = rng.choice(PI_VALUES)
    s, co = trig_pair(rng)
    a = KerrNewman(c=c, G=g, eps_0=e0, sch=sch, a=aa, Q=q).tensor()
    exp, cls = finish(
        a,
        [(sympy.sin, lambda x: s), (sympy.cos, lambda x: co)],
        {**by_name(a, r=r), sympy.pi: pi},
    )
    return f"predef.kn {toks(c, g, e0, sch, aa, q, pi, r, s, co)}", exp, cls


def g_rn(rng):
    c, g, e0, sch, q, r = [rv(rng) for _ in range(6)]
    pi = rng.choice(PI_VALUES)
    s, _ = trig_pair(rng)
    a = ReissnerNordstorm_(c, g, e0, sch, q)
    exp, cls = finish(a, [(sympy.sin, lambda x: s)], {**by_name(a, r=r), sympy.pi: pi})
    return f"predef.rn {toks(c, g, e0, sch, q, pi, r, s)}", exp, cls


def ReissnerNordstorm_(c, g, e0, sch, q):
    return ReissnerNordstorm(c=c, G=g, eps_0=e0, sch=sch, Q=q).tensor()


def g_ads(rng):
    ct, _ = trig_pair(rng)
    sh, _ = hyp_pair(rng)
    s, _ = trig_pair(rng)
    a = AntiDeSitter().tensor()
    exp, cls = finish(
        a, [(sympy.cos, lambda x: ct), (sympy.sinh, lambda x: sh), (sympy.sin, lambda x: s)]
    )
    return f"predef.ads {toks(ct, sh, s)}", exp, cls


def g_adss(rng):
    sh, ch = hyp_pair(rng)
    s, _ = trig_pair(rng)
    a = AntiDeSitterStatic().tensor()
    exp, cls = finish(
        a, [(sympy.cosh, lambda x: ch), (sympy.sinh, lambda x: sh), (sympy.sin, lambda x: s)]
    )
    return f"predef.adss {toks(ch, sh, s)}", exp, cls


def g_ds(rng):
    e = rng.choice(VALUES + [ZERO])
    a = DeSitter().tensor()
    exp, cls = finish(a, [(sympy.exp, lambda x: e)])
    return f"predef.ds {toks(e)}", exp, cls


_x_s, _sigma, _R, _v = sympy.symbols("x_s sigma R v")
_X, _Y, _Z = sympy.symbols("x y z")
_RS = sympy.sqrt((_X - _x_s) ** 2 + _Y**2 + _Z**2)


def g_alc(rng):
    v = rv(rng)
    t1, t2, t3 = rv(rng), rv(rng), rv(rng)
    a = AlcubierreWarp(v=v).tensor()
    targets = [(_sigma * (_RS + _R), t1), (_sigma * (_RS - _R), t2), (_sigma * _R, t3)]

    def th(arg):
        for tgt, val in targets:
            if sympy.expand(arg - tgt) == 0:
                return val
            if sympy.expand(arg + tgt) == 0:
                return -val
        raise AssertionError(f"unmatched tanh argument {arg}")

    exp, cls = finish(a, [(sympy.tanh, th)])
    return f"predef.alc {toks(v, t1, t2, t3)}", exp, cls


def g_bv(rng):
    c, k, r = rv(rng), rv(rng), rv(rng)
    s, _ = trig_pair(rng)
    a = BarriolaVilekin(c=c, k=k).tensor()
    exp, cls = finish(a, [(sympy.sin, lambda x: s)], by_name(a, r=r))
    return f"predef.bv {toks(c, k, r, s)}", exp, cls


def g_bk(rng):
    c, lam = rv(rng), rv(rng)
    e = rng.choice(VALUES)
    s, _ = trig_pair(rng)
    # keyword arguments: the second positional parameter is the unused `k`
    a = BertottiKasner(c=c, lambd=lam).tensor()
    exp, cls = finish(a, [(sympy.exp, lambda x: e), (sympy.sin, lambda x: s)])
    return f"predef.bk {toks(c, lam, e, s)}", exp, cls


_C, _rho = sympy.symbols("C rho")
_J0, _J1, _t = sympy.besselj(0, _rho), sympy.besselj(1, _rho), sympy.Symbol("t")
_U = _C * _J0 * sympy.cos(_t)
_K = Q(1, 2) * _C**2 * _rho * (_rho * (_J0**2 + _J1**2) - 2 * _J0 * _J1 * sympy.cos(_t) ** 2)


def g_bessel(rng):
    rho = rv(rng)
    eu, ek = rng.choice(VALUES), rng.choice(VALUES)
    a = BesselGravitationalWave().tensor()

    def ex(arg):
        for p, q, val in [(2, 0, eu**2), (-2, 0, 1 / eu**2), (0, 2, ek**2), (-2, 2, ek**2 / eu**2)]:
            if sympy.expand(arg - (p * _U + q * _K / 2 * 1)) == 0 and False:
                pass
        for pu, pk, val in [(2, 0, eu**2), (-2, 0, 1 / eu**2), (0, 2, ek**2), (-2, 2, ek**2 / eu**2)]:
            if sympy.expand(arg - (pu * _U + pk * _K)) == 0:
                return val
        raise AssertionError(f"unmatched exp argument {arg}")

    exp, cls = finish(a, [(sympy.exp, ex)], by_name(a, rho=rho))
    return f"predef.bessel {toks(rho, eu, ek)}", exp, cls


def g_cm(rng):
    fv, hv, x, y = rv(rng), rv(rng), rv(rng), rv(rng)
    a = CMetric().tensor()
    exp, cls = finish(
        a,
        subs=by_name(a, x=x, y=y),
        func_rules=[(lambda e: e.func.__name__ == "f", lambda e: fv),
                    (lambda e: e.func.__name__ == "h", lambda e: hv)],
    )
    return f"predef.cm {toks(fv, hv, x, y)}", exp, cls


def g_dav(rng):
    r, t3, w = rv(rng), rng.choice(VALUES + [ZERO]), rng.choice(VALUES)
    a = Davidson().tensor()
    t, rs = sym(a, "t"), sym(a, "r")
    T, W = sympy.Symbol("T", positive=True), sympy.Symbol("W", positive=True)
    ents = [e.subs(t, T**3).subs(1 + rs**2, W**5) for e in entries(a)]
    arr = sympy.Array(ents, (4, 4))
    exp, cls = finish(arr, subs={T: t3, W: w, rs: r})
    return f"predef.dav {toks(r, t3, w)}", exp, cls


def g_ernst(rng):
    b, m, r = rv(rng), rv(rng), rv(rng)
    s, _ = trig_pair(rng)
    a = Ernst(B=b, M=m).tensor()
    exp, cls = finish(a, [(sympy.sin, lambda x: s)], by_name(a, r=r))
    return f"predef.ernst {toks(b, m, r, s)}", exp, cls


def g_godel(rng):
    e = rng.choice(VALUES)
    a = Godel().tensor()
    om, x = sym(a, "omega"), sym(a, "x")
    base = sympy.sqrt(2) * om * x

    def ex(arg):
        k = sympy.simplify(arg / base)
        assert k in (1, 2), k
        return e**k

    exp, cls = finish(a, [(sympy.exp, ex)])
    return f"predef.godel {toks(e)}", exp, cls


def g_flrw(rng):
    av, k, r = rv(rng), rv(rng), rv(rng)
    s, _ = trig_pair(rng)
    a = FriedmannLemaitreRobertsonWalker().tensor()
    exp, cls = finish(
        a,
        [(sympy.sin, lambda x: s)],
        by_name(a, k=k, r=r),
        func_rules=[(lambda e: e.func.__name__ == "a", lambda e: av)],
    )
    return f"predef.flrw {toks(av, k, r, s)}", exp, cls


def g_jnw(rng):
    c, g, m, r = rv(rng), rv(rng), rv(rng), rv(rng)
    gam = rng.choice([-3, -2, -1, 0, 1, 1, 2, 3])
    s, _ = trig_pair(rng)
    a = JanisNewmanWinicour(c=c, G=g, gam=sympy.Integer(gam), M=m).tensor()
    exp, cls = finish(a, [(sympy.sin, lambda x: s)], by_name(a, r=r))
    return f"predef.jnw {toks(c, g)} {gam} {toks(m, r, s)}", exp, cls


def g_knds(rng):
    aa, q, lam, r = rv(rng), rv(rng), rv(rng), rv(rng)
    s, co = trig_pair(rng)
    a = KerrNewmanDeSitter().tensor()
    exp, cls = finish(
        a,
        [(sympy.sin, lambda x: s), (sympy.cos, lambda x: co)],
        by_name(a, a=aa, Q=q, Lambda=lam, r=r),
    )
    return f"predef.knds {toks(aa, q, lam, r, s, co)}", exp, cls


GENS = [g_mink, g_minkp, g_schw, g_kerr, g_kn, g_rn, g_ads, g_adss, g_ds, g_alc, g_bv, g_bk,
        g_bessel, g_cm, g_dav, g_ernst, g_godel, g_flrw, g_jnw, g_knds]


def gen(rng):
    g = rng.choice(GENS)
    line, exp, cls = g(rng)
    return line, exp, f"{g.__name__[2:]}:{cls}"


if __name__ == "__main__":
    run(gen, exe="epdiff_predefined")
