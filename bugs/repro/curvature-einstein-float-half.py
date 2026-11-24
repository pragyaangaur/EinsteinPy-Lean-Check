"""EinsteinTensor.from_metric returns floats where exact rationals are expected."""
import sympy
from sympy import Rational, symbols

from einsteinpy.symbolic import EinsteinTensor, MetricTensor, RicciScalar, RicciTensor

t, x, y = symbols("t x y")
g = MetricTensor(sympy.diag(-1, 1 + x**2 / 3, 1 + t * x / 5).tolist(), (t, x, y))
E = EinsteinTensor.from_metric(g)
Ric = RicciTensor.from_metric(g)
R = RicciScalar.from_riccitensor(Ric, g).expr
pt = {t: Rational(1, 3), x: Rational(1, 2), y: 0}
got = E.tensor()[2, 2].subs(pt)
exact = (Ric.tensor()[2, 2] - Rational(1, 2) * R * g.tensor()[2, 2]).subs(pt)
got00 = E.tensor()[0, 0].subs(pt)
exact00 = (Ric.tensor()[0, 0] - Rational(1, 2) * R * g.tensor()[0, 0]).subs(pt)
print("yy:", got, "exact:", exact)
print("tt:", got00, "exact:", exact00)
assert exact == 0 and got != 0 and got.is_Float
assert exact00 == Rational(900, 162409) and got00.is_Float and got00 != exact00
print("REPRODUCED")
