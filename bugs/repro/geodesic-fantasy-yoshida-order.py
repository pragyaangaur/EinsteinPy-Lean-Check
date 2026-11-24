"""GeodesicIntegrator with order 6 or 8 converges only at second order, because every level reads _Z(self.order)."""
import warnings

import numpy as np
from scipy.integrate import solve_ivp

warnings.simplefilter("ignore")
from einsteinpy.geodesic.utils import _P, _sch
from einsteinpy.integrators import GeodesicIntegrator
from einsteinpy.integrators.utils import _Z
from einsteinpy.utils.dual import _jacobian_g

PRM = (0.0,)
q0 = np.array([0.0, 10.0, np.pi / 2, 0.0])
p0 = _P(_sch, PRM, q0, [0.0, 0.0, 0.03], True)
T = 8.0


def rhs(_, y):
    """Hamilton's equations for H = g^{mu nu} p_mu p_nu / 2 with the metric of einsteinpy."""
    q, p = y[:4], y[4:]
    r, th = q[1], q[2]
    f = 1 - 2 / r
    g = np.diag([-1 / f, f, 1 / r**2, 1 / (r * np.sin(th)) ** 2])
    dp = [-0.5 * (_jacobian_g(_sch, PRM, q, i) @ p @ p) for i in range(4)]
    return np.concatenate([g @ p, dp])


ref = solve_ivp(rhs, [0, T], np.concatenate([q0, p0]), method="DOP853", rtol=1e-13, atol=1e-14).y[:, -1]


class Fixed(GeodesicIntegrator):
    """The same integrator, with each level reading _Z of its own order."""

    def _ord_4(self, q1, p1, q2, p2, delta):
        z0, z1 = _Z(4)
        s = self._ord_2(q1, p1, q2, p2, delta * z1)
        s = self._ord_2(*s, delta * z0)
        return self._ord_2(*s, delta * z1)

    def _ord_6(self, q1, p1, q2, p2, delta):
        z0, z1 = _Z(6)
        s = self._ord_4(q1, p1, q2, p2, delta * z1)
        s = self._ord_4(*s, delta * z0)
        return self._ord_4(*s, delta * z1)


def observed_order(cls, order):
    errs = []
    for n in (32, 64):
        gi = cls(_sch, PRM, q0, p0, steps=n, delta=T / n, order=order, omega=1.0, suppress_warnings=True)
        for _ in range(n):
            gi.step()
        r = gi.res_list
        y = np.concatenate([np.array(r[0], float), np.array(r[1], float)])
        errs.append(np.abs(y - ref).max())
    return np.log2(errs[0] / errs[1])


res = {o: observed_order(GeodesicIntegrator, o) for o in (2, 4, 6, 8)}
fix = {o: observed_order(Fixed, o) for o in (6,)}
print("observed order of convergence of einsteinpy:", {o: round(v, 2) for o, v in res.items()})
print("with _Z(4) and _Z(6) at the inner levels (order 6):", {o: round(v, 2) for o, v in fix.items()})
print("_Z(6) =", _Z(6), " 2 Z1^3 + Z0^3 =", 2 * _Z(6)[1] ** 3 + _Z(6)[0] ** 3, "(0 for a fourth order jump)")
if res[4] > 3 and res[6] < 3 and res[8] < 3 and fix[6] > 5:
    print("REPRODUCED")
