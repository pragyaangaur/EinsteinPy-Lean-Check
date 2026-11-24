"""DualNumber ** 0 at value 0 raises ZeroDivisionError although x ** 0 is the constant 1."""
from einsteinpy.utils.dual import DualNumber

x = DualNumber(0.0, 1.0)
print("x ** 1:", x**1)
print("x ** 2:", x**2)
try:
    print("x ** 0:", x**0)
except ZeroDivisionError as e:
    print("x ** 0 raised ZeroDivisionError:", e)
    print("REPRODUCED")
