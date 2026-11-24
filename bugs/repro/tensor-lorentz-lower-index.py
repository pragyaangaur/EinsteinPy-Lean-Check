"""lorentz_transform transforms a lower index with the matrix instead of its inverse."""
import sympy
from sympy.abc import t, x

from einsteinpy.symbolic.metric import MetricTensor
from einsteinpy.symbolic.tensor import BaseRelativityTensor

L = [[sympy.Rational(5, 4), sympy.Rational(3, 4)], [sympy.Rational(3, 4), sympy.Rational(5, 4)]]
eta = MetricTensor([[-1, 0], [0, 1]], (t, x))
v = BaseRelativityTensor([1, 2], (t, x), config="u", parent_metric=eta)
w = BaseRelativityTensor([1, 2], (t, x), config="l", parent_metric=eta)

vl = v.tensor()[0] * w.tensor()[0] + v.tensor()[1] * w.tensor()[1]
v2, w2 = v.lorentz_transform(L).tensor(), w.lorentz_transform(L).tensor()
vl2 = v2[0] * w2[0] + v2[1] * w2[1]
print("v^a w_a before:", vl, "after:", vl2)
assert vl == 5 and vl2 != vl
print("REPRODUCED")
