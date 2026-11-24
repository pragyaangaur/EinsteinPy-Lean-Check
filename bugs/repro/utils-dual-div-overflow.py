"""DualNumber division by a large value raises OverflowError, although the quotient is finite."""
from einsteinpy.utils.dual import DualNumber

a = DualNumber(1e200, 1.0)
print("1e200 * 1e200 =", 1e200 * 1e200)
try:
    print(a / a)
except OverflowError as e:
    print("a / a raised OverflowError:", e)
    print("REPRODUCED")
