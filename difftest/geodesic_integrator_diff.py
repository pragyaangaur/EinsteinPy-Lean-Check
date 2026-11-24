"""Difftest for einsteinpy/integrators/fantasy.py, integrators/utils.py and geodesic/geodesic.py.

Cheap handlers (``_Z``, ``_flow_mixed``, ``_flow_A``, ``_flow_B``) fill most of the 50,000 cases. A whole
``_ord_n`` step, a ``GeodesicIntegrator`` run and a ``Geodesic`` construction make the metric derivatives
by dual numbers in Python, which costs about a millisecond per flow and more than a second for a step of
order 8, so they are a small share of the cases and use short runs.
"""
import os
import sys
import warnings

sys.path.insert(0, os.path.dirname(__file__))

import numpy as np

import geodesic_common as C
from einsteinpy.geodesic import Geodesic, Nulllike, Timelike
from einsteinpy.integrators import GeodesicIntegrator
from einsteinpy.integrators.utils import _flow_A, _flow_B, _flow_mixed, _Z
from harness import run


def rkind(rng):
    return rng.choice(["sch", "kerr", "kn"])


def smooth_state(rng, k, prm):
    """A state (q, p) a few units from the black hole with a small momentum."""
    q = [rng.choice([0.0, rng.uniform(-1, 1)]), C.good_radius(rng, k, prm), C.good_angle(rng), rng.uniform(-3, 3)]
    p = [-rng.uniform(0.5, 1.5), C.moderate(rng, 0.3), C.moderate(rng, 0.3), C.moderate(rng, 3.0)]
    return q, p


def case_z(rng):
    r = rng.random()
    if r < 0.6:
        o = rng.choice([2, 4, 6, 8, 4, 6, 8])
    elif r < 0.9:
        o = rng.choice([0, 1, 3, 5, 7, 9, 10, 12, 20, -2, -1, 40])
    else:
        o = rng.choice([C.INF, -C.INF, C.NAN, 2.5, 3.5, 1e300, 1e-300, 1.5, 0.5])
    line = f"geo.z {C.hexf(o)}"

    def f():
        z0, z1 = _Z(o if isinstance(o, float) and not float(o).is_integer() else int(o) if abs(o) < 1e15 else o)
        return C.hl([z0, z1])

    return line, C.real(f)


def case_mixed(rng):
    d, om = C.fl(rng), C.fl(rng) if rng.random() < 0.8 else 1.0
    if rng.random() < 0.5:
        d, om = rng.uniform(-1, 1), rng.choice([1.0, 0.1, 0.01, rng.uniform(0, 2)])
    v = [[C.fl(rng) for _ in range(4)] for _ in range(4)]
    line = f"geo.mixed {C.hexf(d)} {C.hexf(om)} " + " ".join(C.hl(x) for x in v)

    def f():
        out = _flow_mixed(*[np.array(x) for x in v], d, om)
        return C.hl([x for o in out for x in o])

    return line, C.real(f)


def case_flow(rng):
    which = rng.choice("AB")
    k = rkind(rng)
    prm = C.params(rng, k)
    if rng.random() < 0.8:
        qs = [smooth_state(rng, k, prm) for _ in range(2)]
        q1, p1, q2, p2 = qs[0][0], qs[0][1], qs[1][0], qs[1][1]
        if rng.random() < 0.3:
            q2, p2 = q1, p1
    else:
        q1, q2 = C.q4(rng), C.q4(rng)
        p1, p2 = [C.fl(rng) for _ in range(4)], [C.fl(rng) for _ in range(4)]
    d = rng.choice([0.25, 0.5, 0.1, rng.uniform(-1, 1), 0.0, C.fl(rng)])
    mask = "".join(rng.choice("01") for _ in range(4)) if rng.random() < 0.8 else "0000"
    line = f"geo.flow {which} {k} {C.hl(prm)} {C.hexf(d)} {C.hl(q1)} {C.hl(p1)} {C.hl(q2)} {C.hl(p2)} {mask}"

    def f():
        a = [C.arr(x, m == "1") for x, m in zip((q1, p1, q2, p2), mask)]
        fn = _flow_A if which == "A" else _flow_B
        u, v = fn(C.KINDS[k], tuple(prm), *a, d)
        return C.hl(C.flat(u) + C.flat(v))

    return line, C.real(f)


def make_integrator(k, prm, q0, p0, steps, delta, rtol, atol, order, omega, sw, tl):
    return GeodesicIntegrator(metric=C.KINDS[k], metric_params=tuple(prm), q0=np.array(q0), p0=np.array(p0),
                              time_like=tl, steps=steps, delta=delta, rtol=rtol, atol=atol, order=order,
                              omega=omega, suppress_warnings=sw)


def pick_order(rng, heavy=False):
    """Mostly valid orders, with a few invalid ones. Order 8 costs 27 second order steps."""
    r = rng.random()
    if r < 0.12:
        return rng.choice([3.0, 5.0, 0.0, C.NAN, 4.5, -2.0, 10.0, 1.0])
    if r < 0.4:
        return 2.0
    if r < 0.7:
        return 4.0
    if r < 0.93 or not heavy:
        return 6.0
    return 8.0


def case_step(rng):
    k = rkind(rng)
    prm = C.params(rng, k)
    order = pick_order(rng, True)
    omega = rng.choice([1.0, 1.0, 0.01, 0.5, rng.uniform(0, 2), 0.0, C.fl(rng)])
    qs = [smooth_state(rng, k, prm) for _ in range(2)]
    q1, p1, q2, p2 = qs[0][0], qs[0][1], qs[1][0], qs[1][1]
    if rng.random() < 0.5:
        q2, p2 = q1, p1
    d = rng.choice([0.5, 0.1, 0.01, rng.uniform(-0.8, 0.8), 1.0])
    mask = "".join(rng.choice("01") for _ in range(4)) if rng.random() < 0.7 else "0000"
    line = (f"geo.step {k} {C.hl(prm)} {C.hexf(order)} {C.hexf(omega)} {C.hexf(d)} "
            f"{C.hl(q1)} {C.hl(p1)} {C.hl(q2)} {C.hl(p2)} {mask}")

    def f():
        ig = make_integrator(k, prm, q1, p1, 1, d, 0.01, 0.01, order, omega, True, True)
        a = [C.arr(x, m == "1") for x, m in zip((q1, p1, q2, p2), mask)]
        out = ig.integrator(*a, d)
        return C.hl(C.flat(out))

    return line, C.real(f)


def run_warn(fn):
    """Run ``fn``; its string answer gets the step numbers of the integrator's own warnings."""
    steps = []
    with np.errstate(all="ignore"), warnings.catch_warnings(record=True) as ws:
        warnings.simplefilter("always")
        try:
            ans = fn()
        except Exception as e:  # noqa: BLE001
            return C.err(e)
        for w in ws:
            m = str(w.message)
            if m.startswith("Numerical error has exceeded"):
                steps.append(int(m.rsplit("=", 1)[1].strip(" .")))
    return ans + ";W" + ";".join(map(str, steps))


def case_run(rng):
    k = rkind(rng)
    prm = C.params(rng, k)
    order = pick_order(rng, True)
    n = rng.choice([0, 1, 1, 2, 3, 4])
    omega = rng.choice([1.0, 1.0, 0.01, rng.uniform(0, 2)])
    d = rng.choice([0.5, 0.1, 0.01, rng.uniform(0.01, 1.0), 2.0])
    rtol = rng.choice([1e-2, 1e-6, 1e-3, 1e-12, 0.0, rng.uniform(0, 1e-3)])
    atol = rng.choice([1e-2, 1e-6, 1e-3, 1e-12, 0.0, C.NAN])
    sw = rng.random() < 0.25
    tl = rng.random() < 0.5
    q0, p0 = smooth_state(rng, k, prm)
    line = (f"geo.run {k} {C.hl(prm)} {C.hexf(order)} {C.hexf(omega)} {C.hexf(d)} {n} {C.hexf(rtol)} "
            f"{C.hexf(atol)} {int(sw)} {int(tl)} {C.hl(q0)} {C.hl(p0)}")

    def f():
        ig = make_integrator(k, prm, q0, p0, n, d, rtol, atol, order, omega, sw, tl)
        for _ in range(n):
            ig.step()
        return "R" + C.hl([x for r in ig.results for x in C.flat(r)])

    return line, run_warn(f)


def case_geodesic(rng):
    cls = rng.choice(["Geodesic", "Timelike", "Nulllike", "Timelike", "Nulllike"])
    r = rng.random()
    name = rng.choice(["Schwarzschild", "Kerr", "KerrNewman"]) if r < 0.95 else rng.choice(["schwarzschild", "Minkowski", "KerrX"])
    k = {"Schwarzschild": "sch", "Kerr": "kerr", "KerrNewman": "kn"}.get(name, "sch")
    prm = C.params(rng, k)
    if rng.random() < 0.05:
        prm = prm[:-1]
    pos = [C.good_radius(rng, k, prm), C.good_angle(rng), rng.uniform(-3, 3)]
    mom = [C.moderate(rng, 0.3), C.moderate(rng, 0.3), C.moderate(rng, 3.0)]
    if rng.random() < 0.1:
        pos = [C.radius(rng), C.angle(rng), C.angle(rng)]
    cart = rng.random() < 0.5
    tl = rng.random() < 0.5
    kw = {}
    kw["steps"] = rng.choice([1, 2, 3, 4, 0, -1, 2, 3])
    for key, opts in [("delta", [0.5, 0.1, 0.01, 1.0, -0.3]), ("rtol", [1e-2, 1e-6, 1e-12]),
                      ("atol", [1e-2, 1e-9]), ("order", [2.0, 4.0, 4.0, 6.0, 3.0, 8.0]),
                      ("omega", [1.0, 0.01, 0.5]), ("suppress_warnings", [True, False])]:
        if rng.random() < 0.5:
            kw[key] = rng.choice(opts)
    if kw.get("order") == 8.0 and kw["steps"] > 1:
        kw["order"] = 4.0

    def opt(key, fmt):
        return "-" if key not in kw else fmt(kw[key])

    line = (f"geo.geodesic {cls} {name} {C.hl(prm)} {C.hl(pos)} {C.hl(mom)} {int(cart)} {int(tl)} "
            f"{opt('steps', str)} {opt('delta', C.hexf)} {opt('rtol', C.hexf)} {opt('atol', C.hexf)} "
            f"{opt('order', C.hexf)} {opt('omega', C.hexf)} {opt('suppress_warnings', lambda b: str(int(b)))}")

    def f():
        args = dict(metric=name, metric_params=tuple(prm), position=pos, momentum=mom, return_cartesian=cart, **kw)
        if cls == "Geodesic":
            g = Geodesic(time_like=tl, **args)
        elif cls == "Timelike":
            g = Timelike(**args)
        else:
            g = Nulllike(**args)
        steps, tr = g.trajectory
        assert g.kind == ("Time-like" if (tl if cls == "Geodesic" else cls == "Timelike") else "Null-like")
        assert g.coords == ("Cartesian" if cart else "Spherical Polar")
        assert list(steps) == list(range(max(kw["steps"], 0)))
        return "P" + C.hl(g.momentum) + ";T" + C.hl(np.asarray(tr).ravel())

    return line, run_warn(f)


CASES = [(case_z, 5), (case_mixed, 20), (case_flow, 56), (case_step, 10), (case_run, 6), (case_geodesic, 3)]


def gen(rng):
    r = rng.random() * sum(w for _, w in CASES)
    for fn, w in CASES:
        r -= w
        if r < 0:
            break
    line, ans = fn(rng)
    cls = ans if ans.startswith("E:") else ("nan" if "nan" in ans else "ok")
    if ans.count(";W") and not ans.endswith(";W"):
        cls += "+warn"
    return line, ans, line.split()[0] + ":" + cls


if __name__ == "__main__":
    run(gen, exe="epdiff_geodesic")
