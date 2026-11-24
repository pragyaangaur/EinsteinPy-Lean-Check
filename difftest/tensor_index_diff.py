"""Differential test of einsteinpy.symbolic.tensor index logic against the Lean model.

Covers ``_config_checker``, ``_change_config`` (through ``BaseRelativityTensor`` with
a ``MetricTensor``), ``tensor_product`` with every ``i``/``j`` combination including
``None`` and negative indices, and ``lorentz_transform``.
"""

import sys
import warnings

import sympy

from harness import arr_token, run, sympy_render

from einsteinpy.symbolic.metric import MetricTensor
from einsteinpy.symbolic.tensor import (
    BaseRelativityTensor,
    _change_config,
    _config_checker,
    tensor_product,
)

warnings.filterwarnings("ignore")
SMALL = [-3, -2, -1, 0, 0, 1, 1, 2, 3, sympy.Rational(1, 2), sympy.Rational(-2, 3)]


def rand_arr(rng, shape):
    n = 1
    for s in shape:
        n *= s
    data = [rng.choice(SMALL) for _ in range(n)]
    return sympy.Array(data, shape) if shape else sympy.Array(data[0]), data


def rand_config(rng, k):
    return "".join(rng.choice("ul") for _ in range(k))


def cfg_tok(c):
    return c if c else "-"


def rand_metric(rng, d):
    while True:
        m = [[0] * d for _ in range(d)]
        for i in range(d):
            for j in range(i, d):
                v = rng.choice(SMALL) if i != j or rng.random() < 0.3 else rng.choice([-1, 1, 2, -2])
                m[i][j] = m[j][i] = v
        if sympy.Matrix(m).det() != 0:
            return m


def err_tag(e):
    if isinstance(e, ValueError):
        return "ValueError:summation" if "summation" in str(e) else "ValueError"
    if isinstance(e, TypeError):
        return "TypeError"
    if isinstance(e, IndexError):
        return "IndexError"
    return "SympyError"


def gen_chk(rng):
    k = rng.randint(0, 4)
    alphabet = "ul" if rng.random() < 0.7 else "ulxU "
    c = "".join(rng.choice(alphabet) for _ in range(k)).replace(" ", "x")
    want = str(_config_checker(c))
    return f"tensor.chk {cfg_tok(c)}", want, f"chk:{want}"


def gen_cc(rng):
    d = rng.choice([2, 2, 3, 4])
    k = rng.randint(1, 3)
    syms = sympy.symbols(f"x0:{d}")
    arr, data = rand_arr(rng, (d,) * k)
    config = rand_config(rng, k)
    r = rng.random()
    if r < 0.8:
        newconfig = rand_config(rng, k)
    elif r < 0.9:
        newconfig = rand_config(rng, k + rng.choice([-1, 1]))
    else:
        newconfig = config[:-1] + "x"
    m = rand_metric(rng, d)
    metric = MetricTensor(m, syms, config="ll")
    t = BaseRelativityTensor(arr, syms, config=config, parent_metric=metric)
    try:
        want = sympy_render(_change_config(t, metric, newconfig))
        cls = "cc:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_tag(e)}"
        cls = f"cc:{err_tag(e)}"
    flat = [x for row in m for x in row]
    line = f"tensor.cc {arr_token((d,) * k, data)} {cfg_tok(config)} {cfg_tok(newconfig)} {arr_token((d, d), flat)}"
    return line, want, cls


def opt_tok(v):
    return "N" if v is None else str(v)


def gen_tp(rng):
    d = rng.choice([2, 3])
    syms = sympy.symbols(f"x0:{d}")
    k1, k2 = rng.choice([0, 1, 1, 2, 2, 3]), rng.choice([0, 1, 1, 2, 2, 3])
    a1, d1 = rand_arr(rng, (d,) * k1)
    a2, d2 = rand_arr(rng, (d,) * k2)
    c1, c2 = rand_config(rng, k1), rand_config(rng, k2)
    def pick(k):
        r = rng.random()
        if r < 0.15:
            return None
        if r < 0.7 and k > 0:
            return rng.randrange(k)
        if r < 0.9:
            return -rng.randint(1, 3)
        return rng.randint(0, 4)

    i, j = pick(k1), pick(k2)
    t1 = BaseRelativityTensor(a1, syms, config=c1)
    t2 = BaseRelativityTensor(a2, syms, config=c2)
    try:
        res = tensor_product(t1, t2, i, j)
        want = f"{cfg_tok(res.config)} {sympy_render(res.tensor())}"
        kind = "contract" if res.order < k1 + k2 else "product"
        if kind == "contract" and ((i is not None and i < 0) or (j is not None and j < 0)):
            kind = "negative-axis"
        cls = "tp:ok:" + kind
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_tag(e)}"
        cls = f"tp:{err_tag(e)}"
    line = (f"tensor.tp {arr_token((d,) * k1, d1)} {cfg_tok(c1)} "
            f"{arr_token((d,) * k2, d2)} {cfg_tok(c2)} {opt_tok(i)} {opt_tok(j)}")
    return line, want, cls


def gen_lt(rng):
    d = rng.choice([2, 3, 4])
    syms = sympy.symbols(f"x0:{d}")
    k = rng.randint(1, 3)
    arr, data = rand_arr(rng, (d,) * k)
    config = rand_config(rng, k)
    m = [[rng.choice(SMALL) for _ in range(d)] for _ in range(d)]
    t = BaseRelativityTensor(arr, syms, config=config)
    try:
        want = sympy_render(t.lorentz_transform(m).tensor())
        cls = "lt:ok"
    except Exception as e:  # noqa: BLE001
        want = f"ERR {err_tag(e)}"
        cls = f"lt:{err_tag(e)}"
    flat = [x for row in m for x in row]
    line = f"tensor.lt {arr_token((d,) * k, data)} {cfg_tok(config)} {arr_token((d, d), flat)}"
    return line, want, cls


def gen(rng):
    r = rng.random()
    if r < 0.15:
        return gen_chk(rng)
    if r < 0.45:
        return gen_cc(rng)
    if r < 0.75:
        return gen_tp(rng)
    return gen_lt(rng)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    run(gen, default_cases=50000, exe="epdiff_tensor")
