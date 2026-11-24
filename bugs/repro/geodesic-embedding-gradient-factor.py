"""SchwarzschildEmbedding.gradient has an extra factor sqrt(R) and is not the slope of any embedding of the optical geometry."""
import warnings

import numpy as np
from astropy import units as u

warnings.simplefilter("ignore")
from einsteinpy.hypersurface import SchwarzschildEmbedding


def optical_slope(M, r):
    """dz/dr from dR^2 + dz^2 = dr^2 / f^2, with R = r / sqrt(f), f = 1 - 2M/r."""
    f = 1 - 2 * M / r
    return np.sqrt(4 * M * r - 9 * M * M) / (r * f**1.5)


emb = SchwarzschildEmbedding(4e24 * u.kg)  # M.value = 40, the case of upstream's own test_gradient
M, r = emb.M.value, 1200.0
f = 1 - 2 * M / r
R = emb.radial_coord(r)
g = emb.gradient(r)
s = optical_slope(M, r)
print(f"M = {M}, r = {r}: gradient = {g:.4f}, slope of the optical geometry = {s:.4f}, ratio = {g / s:.4f}, sqrt(R) = {np.sqrt(R):.4f}")

# the isometry condition, with dR/dr by a centred difference
h = 1e-4
dR = (emb.radial_coord(r + h) - emb.radial_coord(r - h)) / (2 * h)
print(f"dR^2 + gradient^2 = {dR**2 + g**2:.4f}, dR^2 + slope^2 = {dR**2 + s**2:.4f}, 1/f^2 = {1 / f**2:.4f}")

# a slope is dimensionless: scaling M and r by 2 must not change it
emb2 = SchwarzschildEmbedding(4e24 * u.kg)
emb2.M = 2 * emb.M
g2 = emb2.gradient(2 * r)
print(f"gradient at (2M, 2r) / gradient at (M, r) = {g2 / g:.4f} (sqrt 2 = {np.sqrt(2):.4f})")
if abs(g / s - np.sqrt(R)) < 1e-6 * np.sqrt(R) and abs(dR**2 + s**2 - 1 / f**2) < 1e-4 and abs(g2 / g - np.sqrt(2)) < 1e-6:
    print("REPRODUCED")
