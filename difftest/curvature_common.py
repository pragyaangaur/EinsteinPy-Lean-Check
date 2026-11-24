"""Shared helpers for the curvature difftests: tokens, 2-jets and exact evaluation at a point."""

import fractions

import sympy
from sympy import Rational

from harness import arr_token, render

SMALL = [-3, -2, -1, 0, 0, 1, 1, 2, 3, Rational(1, 2), Rational(-2, 3), Rational(1, 3)]
COORD = [-2, -1, Rational(-1, 2), 0, Rational(1, 3), Rational(1, 2), 1, 2]


class Skip(Exception):
    """The case cannot be compared exactly (a pole at the point, or an unresolved float)."""


def err_name(e):
    return type(e).__name__


def cfg_tok(c):
    return c if c else "-"


def met_tok(arr, config):
    """``arr@config`` for a metric given as a nested list of sympy numbers."""
    d0 = len(arr)
    d1 = len(arr[0]) if d0 else 0
    flat = [x for row in arr for x in row]
    return arr_token((d0, d1), flat) + "@" + cfg_tok(config)


def flat_nested(a):
    """Flatten a sympy Array or nested list in row-major order."""
    return list(sympy.flatten(sympy.Array(a).tolist())) if sympy.Array(a).shape else [sympy.Array(a)[()]]


def exact(v, kappa=None):
    """Value at a point as an exact Rational. Floats come from einsteinpy itself (the
    ``1 / 2`` of ``EinsteinTensor`` and ``np.pi`` in the stress-energy tensor), so they are
    first divided by the known float factor and then matched to the nearest fraction with a
    small denominator. A float that is not close to such a fraction raises ``Skip``."""
    v = sympy.sympify(v)
    if v.is_Rational:
        return v
    if kappa is not None:
        v = v / kappa
    if v.is_Float or v.is_Number and v.is_finite:
        f = float(v)
        r = Rational(fractions.Fraction(f).limit_denominator(10**6))
        if abs(f - float(r)) <= 1e-11 * max(1.0, abs(f)):
            return r
        raise Skip("float not close to a small fraction")
    raise Skip(f"not a number at the point: {v}")


def at_point(arr, pt, kappa=None):
    """Substitute the point into a sympy Array and return (shape, list of Rational)."""
    a = sympy.Array(arr)
    data = [exact(x.subs(pt) if hasattr(x, "subs") else x, kappa) for x in sympy.flatten(a.tolist())] if a.shape else [exact(a[()].subs(pt) if hasattr(a[()], "subs") else a[()], kappa)]
    return a.shape, data


def jet(M, syms, pt):
    """``g, dg, ddg`` of a sympy matrix of polynomials at ``pt``, by sympy.diff of the
    polynomials themselves (not through einsteinpy)."""
    d = len(syms)
    g = [[M[i, j].subs(pt) for j in range(d)] for i in range(d)]
    dg = [[[sympy.diff(M[i, j], syms[k]).subs(pt) for j in range(d)] for i in range(d)] for k in range(d)]
    ddg = [[[[sympy.diff(M[i, j], syms[k], syms[l]).subs(pt) for j in range(d)] for i in range(d)]
            for l in range(d)] for k in range(d)]
    return g, dg, ddg


def tok_nested(a, shape):
    return arr_token(shape, sympy.flatten(a))


def render_point(arr, pt, kappa=None):
    shape, data = at_point(arr, pt, kappa)
    return render(shape, data)
