"""Differential test of ``from_christoffels``, ``from_riemann`` and ``from_riccitensor``
against the Lean model.

``from_christoffels`` is given arbitrary Christoffel arrays whose entries are quadratic
polynomials (they need not come from a metric), so the index order of the Riemann formula
is tested on its own. Lean gets the values and the first derivatives at a rational point,
computed here with ``sympy.diff`` on the polynomials. The array can be in any config, with
a constant parent metric on the object, a constant metric as argument, both or neither,
which tests which metric each step of the chain picks and the `Parent Metric not found`
errors. ``from_riemann`` and ``from_riccitensor`` act on constant arrays.
"""

import sys
import warnings

import sympy
from sympy import Rational

from curvature_common import COORD, SMALL, Skip, at_point, cfg_tok, err_name, met_tok
from curvature_construct_diff import mk_met, rand_met_obj
from harness import arr_token, render, run, sympy_render

from einsteinpy.symbolic.christoffel import ChristoffelSymbols
from einsteinpy.symbolic.ricci import RicciScalar, RicciTensor
from einsteinpy.symbolic.riemann import RiemannCurvatureTensor

warnings.filterwarnings("ignore")
COEF = [-2, -1, 1, 2, Rational(1, 2), Rational(1, 3)]


def poly(rng, syms, deg=2):
    if rng.random() < 0.45:
        return 0
    e = 0
    for _ in range(rng.randint(1, 2)):
        m = 1
        for _ in range(rng.randint(0, deg)):
            m *= rng.choice(syms)
        e += rng.choice(COEF) * m
    return e


def rand_config(rng, k, ull_weight=0.55):
    full = {3: "ull", 4: "ulll", 2: "ll"}[k]
    if rng.random() < ull_weight:
        return full
    return "".join(rng.choice("ul") for _ in range(k))


def render_exact(shape, data):
    return render(shape, data)


def gen_fch(rng):
    d = rng.choice([1, 2, 2, 3, 3, 3, 3])
    if rng.random() < 0.01:
        d = 4
    syms = sympy.symbols(f"x0:{d}")
    arr = sympy.MutableDenseNDimArray.zeros(d, d, d)
    for i in range(d):
        for j in range(d):
            for k in range(d):
                arr[i, j, k] = poly(rng, syms)
    arr = sympy.ImmutableDenseNDimArray(arr)
    pt = {s: rng.choice(COORD) for s in syms}
    gam = [[[arr[t, s, n].subs(pt) for n in range(d)] for s in range(d)] for t in range(d)]
    dgam = [[[[sympy.diff(arr[t, s, n], syms[r]).subs(pt) for n in range(d)] for s in range(d)]
             for t in range(d)] for r in range(d)]
    config = rand_config(rng, 3)
    op = rng.choice(["riem", "ric", "sca"])
    pm, pmt = rand_met_obj(rng, d, 0.4)
    am, amt = rand_met_obj(rng, d, 0.5)
    try:
        pmo, amo = mk_met(pm, syms), mk_met(am, syms)
        ch = ChristoffelSymbols(arr, syms, config=config, parent_metric=pmo)
        res = {"riem": RiemannCurvatureTensor, "ric": RicciTensor, "sca": RicciScalar}[op].from_christoffels(
            ch, parent_metric=amo)
        shape, data = at_point(res.tensor(), pt)
        want = render(shape, data)
        cls = f"fch:{op}:ok"
    except Skip:
        raise
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        cls = f"fch:{op}:{err_name(e)}"
    line = (f"curv.fch {op} {cfg_tok(config)} {arr_token((d,) * 3, sympy.flatten(gam))} "
            f"{arr_token((d,) * 4, sympy.flatten(dgam))} {d} {pmt} {amt}")
    return line, want + "", cls + f":d{d}"


def gen_fri(rng):
    d = rng.choice([1, 2, 3, 3])
    syms = sympy.symbols(f"x0:{d}")
    shape = (d,) * 4
    data = [rng.choice(SMALL) for _ in range(d**4)]
    config = rand_config(rng, 4)
    op = rng.choice(["ric", "sca"])
    pm, pmt = rand_met_obj(rng, d, 0.4)
    am, amt = rand_met_obj(rng, d, 0.5)
    try:
        pmo, amo = mk_met(pm, syms), mk_met(am, syms)
        rt = RiemannCurvatureTensor(sympy.Array(data, shape), syms, config=config, parent_metric=pmo)
        res = (RicciTensor if op == "ric" else RicciScalar).from_riemann(rt, parent_metric=amo)
        want = sympy_render(res.tensor())
        cls = f"fri:{op}:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        cls = f"fri:{op}:{err_name(e)}"
    line = f"curv.fri {op} {arr_token(shape, data)} {cfg_tok(config)} {d} {pmt} {amt}"
    return line, want, cls


def gen_frt(rng):
    d = rng.choice([1, 2, 3, 4])
    syms = sympy.symbols(f"x0:{d}")
    shape = (d, d)
    data = [rng.choice(SMALL) for _ in range(d * d)]
    config = rand_config(rng, 2, 0.25)
    pm, pmt = rand_met_obj(rng, d, 0.4)
    am, amt = rand_met_obj(rng, d, 0.5)
    try:
        pmo, amo = mk_met(pm, syms), mk_met(am, syms)
        rt = RicciTensor(sympy.Array(data, shape), syms, config=config, parent_metric=pmo)
        res = RicciScalar.from_riccitensor(rt, parent_metric=amo)
        want = sympy_render(res.tensor())
        cls = "frt:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        cls = f"frt:{err_name(e)}"
    line = f"curv.frt {arr_token(shape, data)} {cfg_tok(config)} {d} {pmt} {amt}"
    return line, want, cls


def gen(rng):
    while True:
        try:
            r = rng.random()
            if r < 0.04:
                return gen_fch(rng)
            if r < 0.55:
                return gen_fri(rng)
            return gen_frt(rng)
        except Skip:
            pass


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    run(gen, default_cases=50000, exe="epdiff_curvature")
