"""Differential test of the constructors, ``change_config`` and ``lorentz_transform`` of
the curvature classes against the Lean model, on constant arrays.

Covers ``ctor`` (every class, bad configs, wrong ranks, wrong first axes), the
``MetricTensor`` methods ``change_config``, ``inv`` and ``lower_config`` (singular and
non-square matrices, the odd configs ``ul`` and ``lu``), ``change_config`` of every other
class with the metric given as an argument, as the parent metric, as both and as neither,
and ``lorentz_transform`` of every class.
"""

import sys
import warnings

import sympy

from curvature_common import SMALL, cfg_tok, err_name, met_tok
from harness import arr_token, run, sympy_render

from einsteinpy.symbolic.christoffel import ChristoffelSymbols
from einsteinpy.symbolic.einstein import EinsteinTensor
from einsteinpy.symbolic.metric import MetricTensor
from einsteinpy.symbolic.ricci import RicciScalar, RicciTensor
from einsteinpy.symbolic.riemann import RiemannCurvatureTensor
from einsteinpy.symbolic.schouten import SchoutenTensor
from einsteinpy.symbolic.stress_energy_momentum import StressEnergyMomentumTensor
from einsteinpy.symbolic.vector import GenericVector
from einsteinpy.symbolic.weyl import WeylTensor

warnings.filterwarnings("ignore")

CLASSES = {
    "metric": (MetricTensor, 2), "chris": (ChristoffelSymbols, 3), "riemann": (RiemannCurvatureTensor, 4),
    "ricci": (RicciTensor, 2), "scalar": (RicciScalar, 0), "einstein": (EinsteinTensor, 2),
    "weyl": (WeylTensor, 4), "schouten": (SchoutenTensor, 2), "stress": (StressEnergyMomentumTensor, 2),
    "vector": (GenericVector, 1),
}
NOTMETRIC = [k for k in CLASSES if k != "metric"]


def rand_data(rng, shape):
    n = 1
    for s in shape:
        n *= s
    return [rng.choice(SMALL) for _ in range(n)]


def mk_arr(shape, data):
    return sympy.Array(data, shape) if shape else sympy.Array(data[0])


def rand_config(rng, k, bad=0.06):
    s = "".join(rng.choice("ul") for _ in range(k))
    if s and rng.random() < bad:
        i = rng.randrange(len(s))
        s = s[:i] + rng.choice("xUz") + s[i + 1:]
    return s


def build(kind, arr, syms, config, pm):
    cls, _ = CLASSES[kind]
    if kind == "scalar":
        return cls(arr, syms, parent_metric=pm)
    return cls(arr, syms, config=config, parent_metric=pm) if kind != "metric" else cls(arr, syms, config=config)


def rand_square(rng, d, singular=0.1):
    while True:
        m = [[rng.choice(SMALL) for _ in range(d)] for _ in range(d)]
        if sympy.Matrix(m).det() != 0 or rng.random() < singular:
            return m


def gen_ctor(rng):
    kind = rng.choice(list(CLASSES))
    d = rng.choice([1, 2, 3])
    order = CLASSES[kind][1]
    k = order if rng.random() < 0.7 else rng.randint(0, 4)
    shape = tuple([d] * k)
    if shape and rng.random() < 0.15:
        shape = (d,) + tuple(rng.randint(1, 3) for _ in range(k - 1))
    nsyms = d if rng.random() < 0.85 else d + rng.choice([-1, 1]) if d > 1 else d + 1
    config = rand_config(rng, k if rng.random() < 0.85 else k + rng.choice([-1, 1]) if k else 1)
    if kind == "scalar":
        config = ""
        shape = tuple([d] * rng.choice([0, 0, 1]))
    data = rand_data(rng, shape)
    syms = sympy.symbols(f"x0:{nsyms}")
    try:
        build(kind, mk_arr(shape, data), syms, config, None)
        want, cls = "OK", "ctor:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        cls = f"ctor:{err_name(e)}"
    return f"curv.ctor {kind} {arr_token(shape, data)} {cfg_tok(config)} {nsyms}", want, cls


def rand_metric_arr(rng):
    d = rng.choice([1, 2, 2, 3])
    r = rng.random()
    if r < 0.07:
        e = d + rng.choice([-1, 1]) if d > 1 else 2
        m = [[rng.choice(SMALL) for _ in range(e)] for _ in range(d)]
    else:
        m = rand_square(rng, d, 0.15)
    return d, m


def gen_metric_method(rng):
    d, m = rand_metric_arr(rng)
    shape = (d, len(m[0]))
    data = [x for row in m for x in row]
    config = rng.choice(["ll", "ll", "uu", "uu", "ul", "lu", "x", "lll"])
    newconfig = rng.choice(["ll", "uu", "uu", "ul", "lu", "ll", config, "", "x"])
    which = rng.choice(["mcc", "mcc", "minv", "mlow"])
    syms = sympy.symbols(f"x0:{d}")
    try:
        M = MetricTensor(sympy.Array(data, shape), syms, config=config)
        res = {"mcc": lambda: M.change_config(newconfig), "minv": M.inv, "mlow": M.lower_config}[which]()
        want = f"{cfg_tok(res.config)} {sympy_render(res.tensor())}"
        cls = f"{which}:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        cls = f"{which}:{err_name(e)}"
    a = arr_token(shape, data)
    if which == "mcc":
        line = f"curv.mcc {a} {cfg_tok(config)} {cfg_tok(newconfig)} {d}"
    else:
        line = f"curv.{which} {a} {cfg_tok(config)} {d}"
    return line, want, cls


def rand_met_obj(rng, d, p_none):
    if rng.random() < p_none:
        return None, "-"
    m = rand_square(rng, d, 0.1)
    config = rng.choice(["ll", "ll", "uu", "ul"])
    return (m, config), met_tok(m, config)


def mk_met(spec, syms):
    if spec is None:
        return None
    m, config = spec
    return MetricTensor(sympy.Array(m), syms, config=config)


def gen_cc(rng):
    kind = rng.choice(NOTMETRIC)
    d = rng.choice([2, 2, 3])
    k = CLASSES[kind][1]
    shape = (d,) * k
    data = rand_data(rng, shape)
    config = "" if kind == "scalar" else rand_config(rng, k, 0.02)
    newconfig = rand_config(rng, k, 0.03) if rng.random() < 0.9 else rand_config(rng, k + 1)
    syms = sympy.symbols(f"x0:{d}")
    pm, pmt = rand_met_obj(rng, d, 0.45)
    am, amt = rand_met_obj(rng, d, 0.45)
    try:
        pmo, amo = mk_met(pm, syms), mk_met(am, syms)
        obj = build(kind, mk_arr(shape, data), syms, config, pmo)
        res = obj.change_config(newconfig, metric=amo)
        want = f"{type(res).__name__} {sympy_render(res.tensor())}"
        cls = "cc:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        cls = f"cc:{err_name(e)}"
    line = f"curv.cc {kind} {arr_token(shape, data)} {cfg_tok(config)} {cfg_tok(newconfig)} {d} {pmt} {amt}"
    return line, want, cls


def gen_lt(rng):
    kind = rng.choice(list(CLASSES))
    d = rng.choice([2, 2, 3])
    k = CLASSES[kind][1]
    shape = (d,) * k
    data = rand_data(rng, shape)
    config = "" if kind == "scalar" else rand_config(rng, k, 0.0)
    syms = sympy.symbols(f"x0:{d}")
    r = rng.random()
    if r < 0.85:
        tshape = (d, d)
    elif r < 0.95:
        tshape = (d + 1, d)
    else:
        tshape = (d, d + 1)
    tm = rand_data(rng, tshape)
    try:
        obj = build(kind, mk_arr(shape, data), syms, config, None)
        res = obj.lorentz_transform(sympy.Array(tm, tshape))
        want = f"{type(res).__name__} {sympy_render(res.tensor())}"
        cls = "lt:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_name(e)}"
        cls = f"lt:{err_name(e)}"
    line = f"curv.lt {kind} {arr_token(shape, data)} {cfg_tok(config)} {arr_token(tshape, tm)} {d}"
    return line, want, cls


def gen(rng):
    r = rng.random()
    if r < 0.2:
        return gen_ctor(rng)
    if r < 0.45:
        return gen_metric_method(rng)
    if r < 0.75:
        return gen_cc(rng)
    return gen_lt(rng)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    run(gen, default_cases=50000, exe="epdiff_curvature")
