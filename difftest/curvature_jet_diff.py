"""Differential test of the ``from_metric`` chain of einsteinpy (Christoffel, Riemann, Ricci,
Ricci scalar, Einstein, Schouten, Weyl and stress-energy) against the Lean 2-jet model.

A case is a metric whose entries are polynomials in the coordinates, a rational point, and
an operation. einsteinpy runs symbolically on the polynomial metric and the result is
evaluated at the point. Lean is given only ``g``, ``dg`` and ``ddg`` at the point, computed
here with ``sympy.diff`` on the polynomials. Most metrics are built as ``B^T D B`` with
``B`` unit upper triangular and ``D`` a constant diagonal, so the inverse is a polynomial
too and sympy stays fast. In dimension 2 some metrics are generic quadratics, whose
inverse is a rational function.

``EinsteinTensor`` and the stress-energy tensor contain Python floats (``1 / 2`` and
``np.pi``), so their values at the point are matched to the nearest small fraction, see
``curvature_common.exact``. Cases where that is not possible are skipped and counted.
"""

import sys
import warnings

import sympy
from sympy import Rational

from curvature_common import COORD, SMALL, Skip, at_point, cfg_tok, err_name, jet, tok_nested
from harness import arr_token, render, run

from einsteinpy.symbolic.christoffel import ChristoffelSymbols
from einsteinpy.symbolic.constants import Cosmo_Const, G, c
from einsteinpy.symbolic.einstein import EinsteinTensor
from einsteinpy.symbolic.metric import MetricTensor
from einsteinpy.symbolic.ricci import RicciScalar, RicciTensor
from einsteinpy.symbolic.riemann import RiemannCurvatureTensor
from einsteinpy.symbolic.schouten import SchoutenTensor
from einsteinpy.symbolic.stress_energy_momentum import StressEnergyMomentumTensor
from einsteinpy.symbolic.weyl import WeylTensor

warnings.filterwarnings("ignore")

OPS = {
    "chr": ChristoffelSymbols.from_metric,
    "riem": RiemannCurvatureTensor.from_metric,
    "ric": RicciTensor.from_metric,
    "sca": RicciScalar.from_metric,
    "ein": EinsteinTensor.from_metric,
    "sch": SchoutenTensor.from_metric,
    "weyl": WeylTensor.from_metric,
}
KAPPA = sympy.Float((c**4 / (8 * __import__("numpy").pi * G)).subs({c: 1, G: 1}))
COEF = [-2, -1, 1, 2, Rational(1, 2), Rational(1, 3), -Rational(1, 2)]


def poly(rng, syms, deg, nterms):
    e = 0
    for _ in range(nterms):
        m = 1
        for _ in range(rng.randint(0, deg)):
            m *= rng.choice(syms)
        e += rng.choice(COEF) * m
    return e


def poly_inverse_metric(rng, d):
    """``B^T D B``, a polynomial matrix with constant nonzero determinant."""
    syms = sympy.symbols(f"x0:{d}")
    B = sympy.eye(d)
    density = 0.5 if d < 4 else 0.0
    for i in range(d):
        for j in range(i + 1, d):
            if rng.random() < density:
                B[i, j] = poly(rng, syms, 1 if d < 4 else 1, rng.randint(1, 2))
    if d == 4:
        i, j = sorted(rng.sample(range(4), 2))
        B[i, j] = poly(rng, syms, 1, 2)
        if rng.random() < 0.3:
            B[0, 3] = poly(rng, syms, 1, 1)
    D = sympy.diag(*[rng.choice([-1, 1, 1, 2, Rational(1, 2), -2]) for _ in range(d)])
    X = (B.T * D * B).applyfunc(sympy.expand)
    return syms, X


def generic_metric(rng, d):
    """Entries of degree at most 2, symmetric. The inverse is a rational function."""
    syms = sympy.symbols(f"x0:{d}")
    X = sympy.zeros(d, d)
    for i in range(d):
        for j in range(i, d):
            X[i, j] = X[j, i] = poly(rng, syms, 2, rng.randint(1, 3)) + (rng.choice([-2, -1, 1, 2]) if i == j else 0)
    return syms, X


def pick_dim(rng):
    r = rng.random()
    return 1 if r < 0.04 else 2 if r < 0.48 else 3 if r < 0.985 else 4


def gen_case(rng):
    d = pick_dim(rng)
    r = rng.random()
    if r < 0.06:
        syms = sympy.symbols(f"x0:{d}")
        # identically singular
        X = sympy.zeros(d, d)
        if d > 1 and rng.random() < 0.5:
            # all entries equal: rank 1, so identically singular
            X = sympy.ones(d, d) * syms[0]
        kind = "singular"
    elif r < 0.25 and d == 2:
        syms, X = generic_metric(rng, d)
        kind = "generic"
    else:
        syms, X = poly_inverse_metric(rng, d)
        kind = "poly"
    config = rng.choice(["ll", "ll", "ll", "uu", "uu", "ul", "lu"]) if kind != "singular" else rng.choice(["ll", "uu"])
    pt = {s: rng.choice(COORD) for s in syms}
    if kind != "singular" and X.subs(pt).det() == 0:
        raise Skip("singular at the point")
    return d, syms, X, config, pt, kind


def jet_args(d, syms, X, pt):
    g, dg, ddg = jet(X, syms, pt)
    return (arr_token((d, d), sympy.flatten(g)), arr_token((d, d, d), sympy.flatten(dg)),
            arr_token((d, d, d, d), sympy.flatten(ddg)))


def gen_one(rng):
    d, syms, X, config, pt, kind = gen_case(rng)
    op = rng.choice(["chr", "riem", "ric", "sca", "ein", "sch", "weyl", "stress", "stress"])
    if d == 4 and op in ("riem", "ric", "sca", "ein", "sch", "stress", "weyl") and rng.random() < 0.5:
        op = rng.choice(["chr", "weyl"])
    M = MetricTensor(X.tolist(), syms, config=config)
    g, dg, ddg = jet_args(d, syms, X, pt)
    try:
        if op == "stress":
            lam = rng.choice(SMALL)
            obj = StressEnergyMomentumTensor.from_metric(M)
            arr = obj.tensor().subs({c: 1, G: 1, Cosmo_Const: lam})
            shape, data = at_point(arr, pt, KAPPA)
            want = render(shape, data)
            line = f"curv.stress {config} {d} {g} {dg} {ddg} {lam}"
            cls = "stress:ok"
        else:
            obj = OPS[op](M)
            arr = obj.tensor()
            shape, data = at_point(arr, pt, None)
            want = render(shape, data)
            line = f"curv.fm {op} {config} {d} {g} {dg} {ddg}"
            cls = f"{op}:ok"
    except Skip:
        raise
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        if op == "stress":
            line = f"curv.stress {config} {d} {g} {dg} {ddg} {rng.choice(SMALL)}"
        else:
            line = f"curv.fm {op} {config} {d} {g} {dg} {ddg}"
        cls = f"{op}:{err_name(e)}"
    cls += f":{kind}:d{d}"
    return line, want, cls


skipped = 0


def gen(rng):
    global skipped
    while True:
        try:
            return gen_one(rng)
        except Skip:
            skipped += 1
        except ZeroDivisionError:
            skipped += 1


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    import atexit

    atexit.register(lambda: print(f"skipped (pole or unresolved float): {skipped}"))
    run(gen, default_cases=5000, exe="epdiff_curvature")
