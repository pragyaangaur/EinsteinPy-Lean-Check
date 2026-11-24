"""The CoordinateError messages of BaseMetric.singularities have no space where two string literals meet."""
from astropy import units as u

from einsteinpy.metric import Kerr, Schwarzschild
from einsteinpy.utils import CoordinateError


class Coords:
    def __init__(self, system):
        self.system = system


msgs = []
for m in (Kerr(Coords("Spherical"), 1e30 * u.kg, 0.5 * u.one), Schwarzschild(Coords("Cartesian"), 1e30 * u.kg)):
    try:
        m.singularities()
    except CoordinateError as e:
        msgs.append(str(e))
        print(e)
if len(msgs) == 2 and "inBoyer" in msgs[0] and "inSpherical" in msgs[1]:
    print("REPRODUCED")
