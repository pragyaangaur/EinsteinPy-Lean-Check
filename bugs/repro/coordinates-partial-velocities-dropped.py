"""A velocity given next to a missing one is dropped without a word."""
from einsteinpy.coordinates.conversion import CartesianConversion

full = CartesianConversion(0.0, 1.0, 2.0, 3.0, 1.0, 2.0, 3.0)
part = CartesianConversion(0.0, 1.0, 2.0, 3.0, v_x=1.0, v_z=3.0)
print(len(full.values()), len(part.values()))
print(part.values(), len(part.convert_spherical()))
if len(full.values()) == 7 and len(part.values()) == 4 and len(part.convert_spherical()) == 4:
    print("REPRODUCED")
