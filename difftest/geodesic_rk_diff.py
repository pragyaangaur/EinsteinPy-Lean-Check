"""Difftest for einsteinpy/integrators/runge_kutta.py: ``RK4naive`` and the arguments of ``RK45``.

``RK4naive`` is run on five right hand sides made of ``+ - *`` only, so the comparison is bit exact.
``RK45`` is a thin wrapper of scipy's class, so only einsteinpy's own logic is tested: the defaults
``rtol = 0.2 h``, ``atol = rtol / 800``, ``first_step = 0.8 h``, ``max_step = 8 h`` and
``vectorized = not isinstance(y0, float)``. The test captures the keyword arguments that reach
``scipy.integrate.RK45.__init__``.
"""
import os
import sys
import warnings

sys.path.insert(0, os.path.dirname(__file__))

import numpy as np
from scipy import integrate

import geodesic_common as C
from einsteinpy.integrators import RK4naive, RK45
from harness import run

RHS = {
    "exp": (lambda t, y: y, 1),
    "osc": (lambda t, y: np.array([y[1], -y[0]]), 2),
    "poly": (lambda t, y: t - y * y, 1),
    "lorenz": (lambda t, y: np.array([10 * (y[1] - y[0]), y[0] * (28 - y[2]) - y[1], y[0] * y[1] - (8 / 3) * y[2]]), 3),
    "const": (lambda t, y: 1.0, 1),
}


def tval(rng):
    r = rng.random()
    if r < 0.5:
        return rng.choice([0.0, 1.0, -1.0, 0.125, 1.125, 2.0, 0.5, -0.5, 10.0])
    if r < 0.58:
        return rng.choice([C.NAN, C.INF, -C.INF, -0.0])
    return rng.uniform(-5, 5)


def case_rk4(rng):
    name = rng.choice(list(RHS))
    f, dim = RHS[name]
    t0, tb = tval(rng), tval(rng)
    if rng.random() < 0.4:
        tb = t0 + rng.choice([1.0, -1.0, 0.5, 2.0, 0.0])
    h = rng.choice([0.1, 0.25, -0.25, 0.5, 1e-3, 1.0, 0.0, 1e300, rng.uniform(-1, 1), C.NAN, 0.125])
    y0 = [C.fl(rng, 0.03, 2.0) for _ in range(dim)]
    n = rng.choice([0, 1, 2, 3, 4, 5, 8])
    line = f"geo.rk4 {name} {C.hexf(t0)} {C.hexf(tb)} {C.hexf(h)} {C.hl(y0)} {n}"

    def fn():
        yy = y0[0] if dim == 1 else np.array(y0)
        s = RK4naive(f, t0, yy, tb, h)
        out_warn = 0
        with warnings.catch_warnings(record=True) as ws:
            warnings.simplefilter("always")
            for _ in range(n):
                s.step()
            out_warn = sum(1 for w in ws if str(w.message).startswith("Out of bounds"))
        return f"{C.hl([s.t] + list(np.atleast_1d(s.y)))};D{s.direction};W{out_warn}"

    return line, C.real(fn)


def case_rk45(rng):
    h = rng.choice([0.1, 0.25, 1.0, 1e-3, 0.0, -0.5, C.NAN, C.INF, 1e300, rng.uniform(0, 2)])
    rtol = None if rng.random() < 0.5 else rng.choice([0.0, 1e-3, 1e-6, C.NAN, 1.0, rng.uniform(0, 1)])
    atol = None if rng.random() < 0.5 else rng.choice([0.0, 1e-6, 1e-9, C.NAN, 1.0, rng.uniform(0, 1)])
    kind = rng.choice(["float", "float", "int", "arr", "np"])
    line = f"geo.rk45 {C.hexf(h)} {C.hopt(rtol)} {C.hopt(atol)} {kind}"
    y0 = {"float": 1.0, "int": 1, "arr": np.array([1.0, 2.0]), "np": np.float64(1.0)}[kind]
    captured = {}
    orig = integrate.RK45.__init__

    def fake(self, **kw):
        captured.update(kw)

    def fn():
        integrate.RK45.__init__ = fake
        try:
            RK45(lambda t, y: y, 0.0, y0, 1.0, h, rtol, atol)
        finally:
            integrate.RK45.__init__ = orig
        c = captured
        return C.hl([c["rtol"], c["atol"], c["first_step"], c["max_step"]]) + f";V{int(c['vectorized'])}"

    ans = C.real(fn)
    # an np.float64 is a float: the Lean side sees the kind "np" as not "float", so map it
    return line.replace(" np", " float") if kind == "np" else line, ans


CASES = [(case_rk4, 70), (case_rk45, 30)]


def gen(rng):
    r = rng.random() * sum(w for _, w in CASES)
    for fn, w in CASES:
        r -= w
        if r < 0:
            break
    line, ans = fn(rng)
    cls = ans if ans.startswith("E:") else ("nan" if "nan" in ans else "ok")
    return line, ans, line.split()[0] + ":" + cls


if __name__ == "__main__":
    run(gen, exe="epdiff_geodesic")
