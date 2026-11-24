"""Difftest of the base class: ``alpha``, ``sigma``, ``delta``, ``rho``, ``schwarzschild_radius``, ``singularities``,
the ``u.quantity_input`` check of the constructors, a user supplied ``metric_cov`` with a perturbation, the
precomputed and the computed list of nonzero Christoffel indices, and the deprecated ``calculate_trajectory``.

The static helpers are called with plain Python floats (flag 1, where ``x ** 2`` raises ``OverflowError``) and with
NumPy scalars (flag 0).
"""

import sys
import pathlib
import warnings

import numpy as np
from astropy import units as u

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import harness  # noqa: E402
from metric_common import *  # noqa: E402,F403
from einsteinpy.metric import BaseMetric, Kerr, KerrNewman, Schwarzschild  # noqa: E402

UNITS = {"kg": u.kg, "g": u.g, "Msun": u.Msun, "s": u.s, "C": u.C, "mC": u.mC, "one": u.one, "percent": u.percent,
         "rad": u.rad, "Ckg": u.C / u.kg, "mCkg": u.mC / u.kg}


def num(py, x):
    return float(x) if py else np.float64(x)


def static_case(rng):
    py = rng.choice([0, 1])
    M, a, Q = mass(rng), spin(rng), charge(rng, 1e30)
    r, th = radius(rng, M), angle(rng)
    op = rng.choice(["alpha", "sigma", "delta", "rho", "schrad"])
    if op == "alpha":
        line = f"m.alpha {cx(M, a)}"
        f = lambda: fl(BaseMetric.alpha(np.float64(M), np.float64(a)))  # noqa: E731
    elif op == "sigma":
        line = f"m.sigma {py} {cx(r, th, M, a)}"
        f = lambda: fl(BaseMetric.sigma(num(py, r), num(py, th), num(py, M), num(py, a)))  # noqa: E731
    elif op == "delta":
        line = f"m.delta {py} {cx(r, M, a, Q)}"
        f = lambda: fl(BaseMetric.delta(num(py, r), num(py, M), num(py, a), num(py, Q)))  # noqa: E731
    elif op == "rho":
        line = f"m.rho {py} {cx(r, th, M, a)}"
        f = lambda: fl(BaseMetric.rho(num(py, r), num(py, th), num(py, M), num(py, a)))  # noqa: E731
    else:
        line = f"m.schrad {cx(M)}"
        f = lambda: fl(BaseMetric.schwarzschild_radius(np.float64(M)))  # noqa: E731
    return line, op, f


def sing_case(rng):
    cls = rng.choice(["schw", "kerr", "kerr", "kn", "kn", "base"])
    system = rng.choice("SSBBBBC")
    M = mass(rng)
    a = spin(rng) if cls in ("kerr", "kn", "base") else 0.0
    Q = charge(rng, M) if cls in ("kn", "base") else 0.0
    th = angle(rng)
    line = f"m.sing {cls} {system} {cx(M, a, Q, th)}"

    def f():
        co = Coords(SYS[system])
        if cls == "schw":
            m = Schwarzschild(co, M * u.kg)
        elif cls == "kerr":
            m = Kerr(co, M * u.kg, a * u.one)
        elif cls == "kn":
            m = KerrNewman(co, M * u.kg, a * u.one, Q * u.C)
        else:
            m = BaseMetric(co, M * u.kg, a * u.one, Q * u.C)
        d = m.singularities()
        out = []
        for k in ("inner_ergosphere", "inner_horizon", "outer_horizon", "outer_ergosphere"):
            v = d[k](th) if callable(d[k]) else d[k]
            out.append(f"I{v}" if isinstance(v, int) else fl(v))
        return "S:" + " ".join(out)

    return line, "sing", f


def spec(rng, unit_pool, value):
    k = rng.choice(unit_pool + ["plain"] * 1)
    return f"{k}={hexf(value)}", k


def ctor_case(rng):
    cls = rng.choice("sknnk")
    M, a, Q = 10 ** rng.uniform(25, 32), rng.random(), 1e18 * rng.random()
    ms, mk = spec(rng, ["kg"] * 5 + ["g", "Msun", "s", "C"], M)
    as_, ak = spec(rng, ["one"] * 5 + ["percent", "rad", "kg"], a)
    qs, qk = spec(rng, ["C"] * 5 + ["mC", "kg", "one"], Q)
    qv = rng.random()
    qq, qqk = spec(rng, ["Ckg"] * 5 + ["mCkg", "C"], qv)
    line = f"m.ctor {cls} {ms} {as_} {qs} {qq}"

    def val(k, x):
        return x if k == "plain" else x * UNITS[k]

    def f():
        co = Coords("BoyerLindquist")
        Mq = val(mk, M)
        if cls == "s":
            m = Schwarzschild(co, Mq)
        elif cls == "k":
            m = Kerr(co, Mq, val(ak, a))
        else:
            m = KerrNewman(co, Mq, val(ak, a), val(qk, Q), val(qqk, qv))
        return fl(m.sch_rad)

    return line, "ctor", f


def base_case(rng):
    mode = rng.choice("npqqq")

    def shape(scale, dense):
        g = np.zeros((4, 4))
        for (i, j) in ((0, 0), (1, 1), (2, 2), (3, 3), (0, 3)):
            if rng.random() < 0.9:
                g[i, j] = rng.uniform(-1, 1) * scale * (1e17 if (i, j) == (0, 0) else 1)
        g[3, 0] = g[0, 3]
        return g

    G = shape(1.0, False)
    P = shape(rng.choice([0.0, 1e-3, 1.0]), False)
    line = f"m.base {mode} " + " ".join(hexf(x) for x in list(G.ravel()) + list(P.ravel()))

    def f():
        co = Coords("Spherical")
        kw = {}
        if mode != "n":
            kw["metric_cov"] = lambda x: G.copy()
        if mode == "q":
            kw["perturbation"] = lambda x: P.copy()
        m = BaseMetric(co, 1.0 * u.kg, **kw)
        x = np.zeros(4)
        outs = []
        for fn in (m.metric_covariant, m.metric_contravariant):
            outs.append(with_errors(lambda fn=fn: arr(fn(x))))
        return "|".join(outs)

    return line, "base" + mode, f


def misc_case(rng):
    k = rng.choice(["nzc", "nzp", "traj"])
    if k == "traj":
        def f():
            m = Schwarzschild(Coords("Spherical"), 1e30 * u.kg)
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                res = m.calculate_trajectory()
            return ("NONE" if res is None else "OTHER") + "".join("+" + x.category.__name__ for x in w)
        return "m.traj", "traj", f

    def tri(lst):
        return "L:" + ";".join(f"{i},{j},{k}" for i, j, k in lst)

    if k == "nzc":
        return "m.nzc", k, lambda: tri(Kerr.nonzero_christoffels())
    m = Kerr(Coords("BoyerLindquist"), 1e30 * u.kg, 0.5 * u.one)
    return "m.nzp", k, lambda: tri(m._nonzero_christoffels_list_bl)


def gen(rng):
    r = rng.random()
    if r < 0.4:
        line, cls, f = static_case(rng)
    elif r < 0.65:
        line, cls, f = sing_case(rng)
    elif r < 0.8:
        line, cls, f = ctor_case(rng)
    elif r < 0.95:
        line, cls, f = base_case(rng)
    else:
        line, cls, f = misc_case(rng)
    ans = with_errors(f)
    return line, ans, f"{cls}.{classify(ans) if ans[:1] in 'EAFS' else 'other'}"


if __name__ == "__main__":
    harness.run(gen, exe="epdiff_metric")
