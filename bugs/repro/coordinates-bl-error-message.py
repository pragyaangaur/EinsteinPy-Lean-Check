"""The CoordinateError message of BoyerLindquistDifferential prints a placeholder."""
from astropy import units as u

from einsteinpy.coordinates.differential import BoyerLindquistDifferential, SphericalDifferential


class Coords:
    system = "Cartesian"


class Metric:
    coords = Coords()


args = (0 * u.s, 1 * u.m, 1 * u.rad, 1 * u.rad, 1 * u.m / u.s, 1 * u.rad / u.s, 1 * u.rad / u.s)
msgs = {}
for cls in (SphericalDifferential, BoyerLindquistDifferential):
    try:
        cls(*args).velocity(Metric())
    except Exception as e:  # noqa: BLE001
        msgs[cls.__name__] = str(e)
        print(cls.__name__, "->", e)
if "( Cartesian )" in msgs["SphericalDifferential"] and "{g.coords.system}" in msgs["BoyerLindquistDifferential"]:
    print("REPRODUCED")
