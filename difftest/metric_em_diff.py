"""Difftest of the Kerr-Newman electromagnetic potential and field tensor, covariant and contravariant."""

import sys
import pathlib

import numpy as np
from astropy import units as u

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import harness  # noqa: E402
from metric_common import *  # noqa: E402,F403
from einsteinpy.metric import KerrNewman  # noqa: E402


def gen(rng):
    system = rng.choice("BBBBBBBBSC")
    M = mass(rng)
    a = spin(rng)
    Q = charge(rng, M)
    r = radius(rng, M)
    th = angle(rng)
    op = rng.choice(["pc", "pu", "fc", "fu", "fc", "fu"])
    line = f"m.{op} {system} {cx(M, a, Q, r, th)}"
    x = np.array([0.37, r, th, 1.1])

    def f():
        m = KerrNewman(Coords(SYS[system]), M * u.kg, a * u.one, Q * u.C)
        fn = {"pc": m.em_potential_covariant, "pu": m.em_potential_contravariant,
              "fc": m.em_tensor_covariant, "fu": m.em_tensor_contravariant}[op]
        return arr(fn(x))

    ans = with_errors(f)
    return line, ans, f"{op}.{classify(ans)}"


if __name__ == "__main__":
    harness.run(gen, exe="epdiff_metric")
