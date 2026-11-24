"""Difftest of the metric components, their derivatives, the Christoffel symbols and ``_f_vec``.

Covers ``Schwarzschild``, ``Kerr`` and ``KerrNewman`` in each coordinate system. The Lean model mirrors the
operations of the source in the order NumPy evaluates them, so the answers are compared bit for bit.
"""

import sys
import pathlib

import numpy as np
from astropy import units as u

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import harness  # noqa: E402
from metric_common import *  # noqa: E402,F403
from einsteinpy.metric import Kerr, KerrNewman, Schwarzschild  # noqa: E402


def build(cls, system, M, a, Q, q=0.0):
    co = Coords(SYS[system])
    if cls == "s":
        return Schwarzschild(co, M * u.kg)
    if cls == "k":
        return Kerr(co, M * u.kg, a * u.one)
    return KerrNewman(co, M * u.kg, a * u.one, Q * u.C, q * u.C / u.kg)


def gen(rng):
    cls = rng.choice("sknnkkk")
    system = {"s": "SSSB", "k": "BBBBBBBBSC", "n": "BBBBBBBBSC"}[cls]
    system = rng.choice(system)
    if cls == "s" and rng.random() < 0.8:
        system = "S"
    M = mass(rng)
    a = spin(rng) if cls != "s" else 0.0
    Q = charge(rng, M) if cls == "n" else 0.0
    r = radius(rng, M)
    th = angle(rng)
    op = rng.choice(["g", "g", "gi", "dg", "ch", "ch", "f", "f"])
    if cls == "s" and op == "dg":
        op = "ch"
    head = f"{cls} {system} {cx(M, a, Q)}"
    if op == "f":
        q = qpm(rng) if cls == "n" else 0.0
        vec = [rng.uniform(-3, 3), r, th, rng.uniform(-3, 3)] + [arg_vec(rng) for _ in range(4)]
        line = f"m.f {head} {cx(q, *vec)}"

        def f():
            m = build(cls, system, M, a, Q, q)
            return arr(m._f_vec(0.0, np.array(vec, dtype=float)))
    else:
        line = f"m.{op} {head} {cx(r, th)}"
        x = np.array([0.37, r, th, 1.1])

        def f():
            m = build(cls, system, M, a, Q)
            if op == "g":
                return arr(m.metric_covariant(x))
            if op == "gi":
                return arr(m.metric_contravariant(x))
            if op == "dg":
                if system == "B":
                    return arr(m._dg_dx_bl(x))
                return "E:CoordinateError"
            return arr(m.christoffels(x))

    ans = with_errors(f)
    return line, ans, f"{cls}.{op}.{classify(ans)}"


if __name__ == "__main__":
    harness.run(gen, exe="epdiff_metric")
