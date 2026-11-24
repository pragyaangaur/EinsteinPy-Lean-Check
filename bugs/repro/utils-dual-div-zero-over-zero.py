"""x * x / x at x = 0 has derivative 0 in DualNumber, but the function is x and its derivative is 1."""
from einsteinpy.utils.dual import DualNumber

x = DualNumber(0.0, 1.0)
r = (x * x) / x
print("x * x / x =", r, "(true derivative of x is 1)")
assert r.deriv == 0.0
print("REPRODUCED")
