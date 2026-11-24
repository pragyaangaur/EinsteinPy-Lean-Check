"""_jacobian_g gives inf on the diagonal for a derivative of 1e308."""
import warnings

import numpy as np

from einsteinpy.utils.dual import _jacobian_g

warnings.filterwarnings("ignore")


def g(q):
    a = np.empty((4, 4), dtype=object)
    for i in range(4):
        for j in range(4):
            a[i, j] = q[0] * 1e308
    return a


J = _jacobian_g(g, (), [1.0, 1.0, 1.0, 1.0], 0)
print("J[0, 0] =", J[0, 0], "(the derivative is 1e308)")
print("J[0, 1] =", J[0, 1])
if np.isinf(J[0, 0]) and J[0, 1] == 1e308:
    print("REPRODUCED")
