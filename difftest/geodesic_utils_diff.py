"""Difftest for einsteinpy/geodesic/utils.py: the three metric functions in both modes, ``sigma``, ``delta`` and ``_P``.

Handlers (see lean/EinsteinpyLean/Geodesic/Diff.lean): geo.metric, geo.dmetric, geo.jac, geo.sigma, geo.delta, geo.P.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

import numpy as np

import geodesic_common as C
from einsteinpy.geodesic.utils import _P, delta, sigma
from einsteinpy.utils.dual import DualNumber, _jacobian_g
from harness import run


def rkind(rng):
    return rng.choice(["sch", "kerr", "kn"])


def case_metric(rng):
    k = rkind(rng)
    prm = C.params(rng, k)
    q = C.q4(rng) if rng.random() < 0.9 else C.q4(rng)[: rng.choice([1, 2, 3])]
    if rng.random() < 0.05:
        prm = prm[:-1]
    line = f"geo.metric {k} {C.hl(prm)} {C.hl(q)}"

    def f():
        g = C.KINDS[k](np.array(q, dtype=float), *prm)
        return C.hl(C.flat(g))

    return line, C.real(f)


def case_dmetric(rng):
    k = rkind(rng)
    prm = C.params(rng, k)
    q = C.q4(rng)
    w = rng.randint(0, 3)
    line = f"geo.dmetric {k} {C.hl(prm)} {C.hl(q)} {w}"

    def f():
        dc = [DualNumber(x, 0.0) for x in q]
        dc[w].deriv = 1.0
        g = C.KINDS[k](dc, *prm)
        out = []
        for row in g:
            ents = []
            for e in row:
                ents.append(f"{C.hexf(e.val)}:{C.hexf(e.deriv)}" if isinstance(e, DualNumber) else "z")
            out.append(",".join(ents))
        return " ".join(out)

    return line, C.real(f)


def case_jac(rng):
    k = rkind(rng)
    prm = C.params(rng, k)
    q = C.q4(rng)
    w = rng.randint(0, 3)
    line = f"geo.jac {k} {C.hl(prm)} {C.hl(q)} {w}"

    def f():
        return C.hl(_jacobian_g(C.KINDS[k], tuple(prm), np.array(q, dtype=float), w).ravel())

    return line, C.real(f)


def case_sigma(rng):
    rk = rng.choice(["np", "py"])
    r = C.radius(rng) if rng.random() < 0.8 else rng.choice([1e154, -1e154, 1.4e154, 1e200, 1e100])
    th, a = C.angle(rng), C.spin(rng)
    line = f"geo.sigma {rk} {C.hexf(r)} {C.hexf(th)} {C.hexf(a)}"

    def f():
        if rk == "np":
            return "F" + C.hexf(sigma(np.float64(r), np.float64(th), a))
        return "F" + C.hexf(sigma(r, th, a))

    return line, C.real(f)


def case_delta(rng):
    rk = rng.choice(["np", "py"])
    r = C.radius(rng) if rng.random() < 0.8 else rng.choice([1e154, -1e154, 1.4e154, 1e200, 1e100])
    a = C.spin(rng) if rng.random() < 0.9 else rng.choice([1e154, 1.4e154, 1e200, -1e200])
    Q = None if rng.random() < 0.4 else C.charge(rng)
    line = f"geo.delta {rk} {C.hexf(r)} {C.hexf(a)} {C.hopt(Q)}"

    def f():
        rr = np.float64(r) if rk == "np" else r
        if Q is None:
            return "F" + C.hexf(delta(rr, a))
        return "F" + C.hexf(delta(rr, a, Q))

    return line, C.real(f)


def case_P(rng):
    k = rkind(rng)
    prm = C.params(rng, k)
    if rng.random() < 0.7:
        q = [0.0, C.good_radius(rng, k, prm), C.good_angle(rng), rng.uniform(-3, 3)]
    else:
        q = C.q4(rng)
    p = [C.moderate(rng, 3.0) for _ in range(3)]
    if rng.random() < 0.15:
        p = [C.fl(rng) for _ in range(3)]
    if rng.random() < 0.05:
        p = p[: rng.choice([0, 1, 2, 3])] + ([C.fl(rng)] if rng.random() < 0.5 else [])
    if rng.random() < 0.04:
        q = q[:3]
    tl = rng.random() < 0.5
    line = f"geo.P {k} {C.hl(prm)} {C.hl(q)} {C.hl(p)} {int(tl)}"

    def f():
        return C.hl(_P(C.KINDS[k], tuple(prm), np.array(q, dtype=float), p, tl))

    return line, C.real(f)


CASES = [(case_metric, 22), (case_dmetric, 10), (case_jac, 18), (case_sigma, 8), (case_delta, 8), (case_P, 34)]


def gen(rng):
    r = rng.random() * sum(w for _, w in CASES)
    for fn, w in CASES:
        r -= w
        if r < 0:
            line, ans = fn(rng)
            return line, ans, line.split()[0] + ":" + C.classify(ans)
    line, ans = CASES[-1][0](rng)
    return line, ans, line.split()[0] + ":" + C.classify(ans)


if __name__ == "__main__":
    run(gen, exe="epdiff_geodesic")
