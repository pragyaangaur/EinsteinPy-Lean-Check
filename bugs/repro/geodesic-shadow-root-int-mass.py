"""Shadow._root_equation truncates the mass to int(mass), while b_crit, horizon and the intensities use the mass."""
import warnings

import numpy as np
from astropy import units as u

warnings.simplefilter("ignore")
from einsteinpy.rays import Shadow

s = Shadow.__new__(Shadow)
s.mass = 1.5 * u.kg
r, b = 4.0, 0.0
code = s._root_equation(np.float64(r), np.float64(b))
M = 1.5
correct = r / np.sqrt(1 - 2 * M / r) - b
print(f"root equation at r = 4 for M = 1.5: code {code:.6f}, r / sqrt(1 - 2M/r) = {correct:.6f}")
print("the code's value is the one for M = int(1.5) = 1:", 4 / np.sqrt(1 - 2 / 4))
if abs(code - 4 / np.sqrt(0.5)) < 1e-12 and abs(code - correct) > 1:
    print("REPRODUCED")
