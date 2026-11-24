"""KerrNewman.em_tensor_contravariant and em_potential_contravariant mix the time coordinates t and c t.

For a Reissner-Nordstrom hole (spin zero) the Lorentz scalars F_ab F^ab and A_a A^a must not depend on the unit of the time
coordinate. The code gives the physical value divided by c squared. The contravariant tensor also fails Maxwell's equation
d_mu (sqrt(-g) F^(mu nu)) = 0, while the same tensor built consistently in t or in c t satisfies it.
"""
import numpy as np
from astropy import units as u

from einsteinpy import constant
from einsteinpy.metric import KerrNewman

c = constant.c.value


class Coords:
    system = "BoyerLindquist"


M, a, Q = 1e30 * u.kg, 0.0 * u.one, 1e19 * u.C
m = KerrNewman(Coords(), M, a, Q)
x = np.array([0.0, 5e3, 1.2, 0.0])
r = x[1]
rQ = m.geometrized_charge(Q.value)
E = rQ / r**2

F = m.em_tensor_covariant(x)
Fu = m.em_tensor_contravariant(x)
inv = float(np.sum(F * Fu))
print("F_ab F^ab from the code:", inv)
print("physical value -2 E^2   :", -2 * E**2)
print("ratio code / physical   :", inv / (-2 * E**2), " 1 / c^2 =", 1 / c**2)

A = m.em_potential_covariant(x)
Au = m.em_potential_contravariant(x)
g00_ct = 1 / (1 - m.sch_rad / r + rQ**2 / r**2)
print("A_a A^a from the code   :", float(A @ Au), " physical:", A[0] ** 2 * g00_ct)


def sqrtg(xx):
    return np.sqrt(-np.linalg.det(m.metric_covariant(xx)))


def maxwell_residual(fn):
    """Relative residual of d_r(sqrt(-g) F^(r t)) + d_th(sqrt(-g) F^(th t))."""
    tot, mag = 0.0, 0.0
    for mu in (1, 2):
        h = 1e-5 * abs(x[mu])
        e = np.zeros(4)
        e[mu] = h
        t = (sqrtg(x + e) * fn(x + e)[mu, 0] - sqrtg(x - e) * fn(x - e)[mu, 0]) / (2 * h)
        tot += t
        mag += abs(t)
    return tot / mag


def fu_ct(xx):
    g = m.metric_covariant(xx).copy()
    g[0, :] /= c
    g[:, 0] /= c
    gi = np.linalg.inv(g)
    return gi @ m.em_tensor_covariant(xx) @ gi


# use a spinning hole for the Maxwell test, where the residual of the code is large
m = KerrNewman(Coords(), M, 0.6 * u.one, Q)
res_code = maxwell_residual(m.em_tensor_contravariant)
res_ct = maxwell_residual(fu_ct)
print("Maxwell residual, code  :", res_code)
print("Maxwell residual, c t   :", res_ct)

if abs(inv / (-2 * E**2) - 1) > 1e-3 and abs(res_code) > 1e-3 and abs(res_ct) < 1e-6:
    print("REPRODUCED")
