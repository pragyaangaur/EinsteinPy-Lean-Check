"""tensor_product with a negative index returns a wrong tensor instead of contracting or raising."""
import sympy
from sympy.abc import t, x

from einsteinpy.symbolic.tensor import BaseRelativityTensor, tensor_product

v = BaseRelativityTensor([1, 2], (t, x), config="u")
m = BaseRelativityTensor([[1, 0], [0, 1]], (t, x), config="lu")

ok = tensor_product(v, m, 0, 0)  # v^a delta_a^b = v^b
bad = tensor_product(v, m, -1, 0)  # index -1 of a rank 1 tensor is index 0
print("i=0 :", ok.config, ok.tensor())
print("i=-1:", bad.config, bad.tensor())
assert ok.config == "u" and list(ok.tensor()) == [1, 2]
assert bad.config == "uu" and bad.tensor().shape == (2, 2)
print("REPRODUCED")
