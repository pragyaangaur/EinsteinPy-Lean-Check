"""Shadow keeps no ray: newton returns the right root with a tiny imaginary part and np.isreal rejects it."""
import warnings

import numpy as np
from astropy import units as u
from scipy.optimize import newton

warnings.simplefilter("ignore")
from einsteinpy.rays import Shadow

s = Shadow.__new__(Shadow)
s.mass = 1.0 * u.kg
for b in (6.0, 20.0):
    root = newton(s._root_equation, 0.1, args=(b,))
    # the real turning point r satisfies r / sqrt(1 - 2/r) = b
    resid = abs(root.real / np.sqrt(1 - 2 / root.real) - b)
    print(f"b = {b}: root = {root}, residual of the real part {resid:.1e}, np.isreal = {bool(np.isreal(root))}")

shadow = Shadow(mass=1 * u.kg, fov=30 * u.km, n_rays=20)
print("rays kept:", len(shadow.z), "of", len(shadow.b), "; intensity values:", len(shadow.intensity))
if len(shadow.z) == 0 and len(shadow.b) == 20:
    print("REPRODUCED")
