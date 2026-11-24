"""cartesian_to_bl raises ZeroDivisionError on the ring disc and just above it, and loses digits there."""
import warnings

warnings.simplefilter("ignore")
from einsteinpy.coordinates.utils import cartesian_to_bl_fast

alpha = 1.0
crashed = []
for z in (0.0, 1e-9, 1e-12):
    try:
        cartesian_to_bl_fast(0.0, 0.5, 0.0, z, alpha)
        crashed.append(False)
    except ZeroDivisionError as e:
        print(f"z = {z}: ZeroDivisionError: {e}")
        crashed.append(True)

# exact radius at (0.5, 0, 1e-7) is 1.1547005383792489e-07 (200 digit arithmetic)
r = cartesian_to_bl_fast(0.0, 0.5, 0.0, 1e-7, alpha)[1]
print("r at z = 1e-7:", r, "exact 1.1547005383792489e-07")
inaccurate = abs(r - 1.1547005383792489e-07) / 1.1547005383792489e-07 > 1e-6
if all(crashed) and inaccurate:
    print("REPRODUCED")
