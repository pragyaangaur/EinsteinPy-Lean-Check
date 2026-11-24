"""velocity(metric) returns dt/dtau for a Schwarzschild metric but tags it as a speed in m/s."""
import warnings

from astropy import units as u

warnings.simplefilter("ignore")
from einsteinpy.coordinates.differential import SphericalDifferential
from einsteinpy.metric import Schwarzschild
from einsteinpy.coordinates.core import Spherical
from einsteinpy import constant

M = 1e30 * u.kg
rs = (2 * constant.G * M / constant.c ** 2).to(u.m)
r = 5 * rs
pos = Spherical(0 * u.s, r, (3.141592653589793 / 2) * u.rad, 0 * u.rad)
g = Schwarzschild(coords=pos, M=M)
d = SphericalDifferential(0 * u.s, r, (3.141592653589793 / 2) * u.rad, 0 * u.rad, 0 * u.m / u.s, 0 * u.rad / u.s, 0 * u.rad / u.s)
vt = d.velocity(g)[0]
print("v_t of a particle at rest at r = 5 r_s:", vt, d.v_t.unit)
print("expected dt/dtau:", 1 / (1 - 1 / 5) ** 0.5)
if abs(vt - 1 / (1 - 1 / 5) ** 0.5) < 1e-9 and str(d.v_t.unit) == "m / s":
    print("REPRODUCED")
