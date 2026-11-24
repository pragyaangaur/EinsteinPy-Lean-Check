"""The Boyer-Lindquist velocity conversion raises ZeroDivisionError on the plane x = 0."""
import warnings

import numpy as np
from astropy import units as u

warnings.simplefilter("ignore")
from einsteinpy.coordinates.differential import CartesianDifferential

pos_ok = CartesianDifferential(0 * u.s, 1 * u.m, 2 * u.m, 1 * u.m, 1 * u.m / u.s, 1 * u.m / u.s, 1 * u.m / u.s)
print("x = 1:", pos_ok.bl_differential(M=1e30 * u.kg, a=0.5).values())
pos = CartesianDifferential(0 * u.s, 0 * u.m, 2 * u.m, 1 * u.m, 1 * u.m / u.s, 1 * u.m / u.s, 1 * u.m / u.s)
from einsteinpy.coordinates.core import Cartesian

print("x = 0, position only:", Cartesian(0 * u.s, 0 * u.m, 2 * u.m, 1 * u.m).to_bl(M=1e30 * u.kg, a=0.5).values())
try:
    pos.bl_differential(M=1e30 * u.kg, a=0.5)
except ZeroDivisionError as e:
    print("x = 0, with velocity: ZeroDivisionError:", e)
    print("REPRODUCED")
