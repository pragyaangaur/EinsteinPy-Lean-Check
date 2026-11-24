"""Schwarzschild(coords, 1 * u.Msun) uses the number 1 as a mass in kilograms."""
from astropy import units as u

from einsteinpy import constant
from einsteinpy.metric import Schwarzschild


class Coords:
    system = "Spherical"


sun_kg = constant.Solar_Mass.value
a = Schwarzschild(Coords(), 1 * u.Msun).sch_rad
b = Schwarzschild(Coords(), sun_kg * u.kg).sch_rad
c = Schwarzschild(Coords(), 1000 * u.g).sch_rad
d = Schwarzschild(Coords(), 1 * u.kg).sch_rad
print("radius of 1 Msun   :", a)
print("radius of Msun in kg:", b)
print("radius of 1000 g   :", c, " radius of 1 kg:", d)
if abs(a / b - 1) > 1e-3 and abs(c / d - 1) > 1e-3:
    print("REPRODUCED")
