"""cartesian_to_bl finds theta with arccos(z / r) and loses it near the axis, where arctan2 is exact."""
import warnings

warnings.simplefilter("ignore")
from einsteinpy.coordinates.utils import cartesian_to_bl_fast, cartesian_to_spherical_fast

x = 1e-9
bl = cartesian_to_bl_fast(0.0, x, 0.0, 1.0, 0.0)
sph = cartesian_to_spherical_fast(0.0, x, 0.0, 1.0)
print("theta, Boyer-Lindquist with a = 0:", bl[2])
print("theta, spherical:", sph[2])
if bl[2] == 0.0 and sph[2] == 1e-9:
    print("REPRODUCED")
