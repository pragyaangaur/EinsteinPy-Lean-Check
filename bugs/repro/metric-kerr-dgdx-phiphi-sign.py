"""Kerr._dg_dx_bl has the wrong sign in one term of d g_phiphi / d r, so the Kerr Christoffel symbols are off.

The derivative array is compared with a fourth order central difference of Kerr.metric_covariant, and the Christoffel symbol
Gamma^r_{phi phi} with the one computed from that difference. Kerr-Newman is shown for comparison: it agrees.
"""
import numpy as np
from astropy import units as u

from einsteinpy.metric import Kerr, KerrNewman


class Coords:
    system = "BoyerLindquist"


M = 1e30 * u.kg
x = np.array([0.0, 2000.0, 1.0, 0.0])


def fd(m, k):
    h = 1e-4 * abs(x[k])
    e = np.zeros(4)
    e[k] = h
    f = lambda s: m.metric_covariant(x + s * e)  # noqa: E731
    return (-f(2) + 8 * f(1) - 8 * f(-1) + f(-2)) / (12 * h)


def gamma_rpp(m):
    dg = np.zeros((4, 4, 4))
    for k in (1, 2):
        dg[k] = fd(m, k)
    gi = np.linalg.inv(m.metric_covariant(x))
    return 0.5 * sum(gi[1, l] * (dg[3][l][3] + dg[3][l][3] - dg[l][3][3]) for l in range(4))


kerr = Kerr(Coords(), M, 0.99 * u.one)
kn = KerrNewman(Coords(), M, 0.99 * u.one, 1e18 * u.C)
for name, m in (("Kerr", kerr), ("Kerr-Newman", kn)):
    code, ref = m._dg_dx_bl(x)[1, 3, 3], fd(m, 1)[3, 3]
    print(f"{name:12s} dg[1,3,3] code {code:.8g}  difference quotient {ref:.8g}  relative error {abs(code - ref) / abs(ref):.2e}")
    cg, rg = m.christoffels(x)[1, 3, 3], gamma_rpp(m)
    print(f"{name:12s} Gamma^r_phiphi code {cg:.8g}  from the metric {rg:.8g}  relative error {abs(cg - rg) / abs(rg):.2e}")
e_kerr = abs(kerr._dg_dx_bl(x)[1, 3, 3] - fd(kerr, 1)[3, 3]) / abs(fd(kerr, 1)[3, 3])
e_kn = abs(kn._dg_dx_bl(x)[1, 3, 3] - fd(kn, 1)[3, 3]) / abs(fd(kn, 1)[3, 3])
if e_kerr > 1e-2 and e_kn < 1e-6:
    print("REPRODUCED")
