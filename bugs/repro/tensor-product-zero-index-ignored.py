"""tensor_product(t1, t2, i=0) silently skips the contraction because 0 is falsy."""
from sympy.abc import t, x

from einsteinpy.symbolic.tensor import BaseRelativityTensor, tensor_product

v = BaseRelativityTensor([1, 2], (t, x), config="u")
w = BaseRelativityTensor([3, 4], (t, x), config="l")

r0 = tensor_product(v, w, 0)  # asks to contract index 0 of v, j left out
print("i=0, j=None:", r0.config, r0.tensor())
assert r0.config == "ul" and r0.order == 2  # no contraction happened, no error

m = BaseRelativityTensor([[1, 0], [0, 1]], (t, x), config="ul")
r1 = tensor_product(m, w, 0)  # rank 2 tensor, i = 0: again no contraction
assert r1.order == 3
try:
    tensor_product(m, w, 1)  # same call with i = 1 reaches config[None]
except TypeError as e:
    print("i=1, j=None: TypeError:", e)
else:
    raise AssertionError("expected TypeError")

try:
    tensor_product(v, w, None, 0)
except TypeError as e:
    print("i=None, j=0: TypeError:", e)
else:
    raise AssertionError("expected TypeError")
print("REPRODUCED")
