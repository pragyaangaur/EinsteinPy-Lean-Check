"""TransformationMatrix.from_new2old and inv take element-wise reciprocals, not matrix inverses."""
import sympy
from sympy import cos, sin, symbols

from einsteinpy.symbolic import TransformationMatrix

x, y, u, v, r, th = symbols("x y u v r theta")

# Linear map x = 2u + v, y = u + v, Jacobian [[2, 1], [1, 1]] with determinant 1.
T = TransformationMatrix.from_new2old([x, y], [u, v], [2 * u + v, u + v])
J = sympy.Matrix([[2, 1], [1, 1]])
print("from_new2old:", T)
print("true inverse:", J.inv())
print("T.inv():", T.inv())
assert sympy.Matrix(T.tolist()) != J.inv()
assert sympy.Matrix(T.inv().tolist()) * sympy.Matrix(T.tolist()) != sympy.eye(2)

# Polar coordinates: a zero-free Jacobian is still not inverted, and einsteinpy's own
# test expects 1/cos(theta) where the inverse Jacobian has cos(theta).
P = TransformationMatrix.from_new2old([x, y], [r, th], [r * cos(th), r * sin(th)])
print("polar from_new2old:", P)
assert sympy.simplify(P[0, 0] - 1 / cos(th)) == 0

# A zero derivative becomes complex infinity.
Z = TransformationMatrix.from_new2old([x, y], [u, v], [u, v])
print("identity map:", Z)
assert Z[0, 1] is sympy.zoo
print("REPRODUCED")
