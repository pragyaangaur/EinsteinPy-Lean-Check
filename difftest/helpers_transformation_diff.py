"""Differential test of einsteinpy.symbolic.helpers.TransformationMatrix.

Every case is a linear map ``old_i = sum_j c_ij new_j`` with small rational
coefficients, so the derivatives are rational and sympy is exact. Zero coefficients
are frequent on purpose, because ``1/0`` becomes sympy's ``zoo``.
"""

import warnings

import sympy

from harness import arr_token, rat_str, run

from einsteinpy.symbolic import TransformationMatrix

warnings.filterwarnings("ignore")
VALUES = [0, 0, 1, -1, 2, -3, sympy.Rational(1, 2), sympy.Rational(-3, 4)]


def num_str(x):
    return "zoo" if x is sympy.zoo else rat_str(x)


def gen(rng):
    n = rng.choice([1, 2, 3, 4])
    pool = VALUES if rng.random() < 0.5 else [v for v in VALUES if v != 0]
    c = [[rng.choice(pool) for _ in range(n)] for _ in range(n)]
    old = sympy.symbols(f"x0:{n}")
    new = sympy.symbols(f"u0:{n}")
    new2old = [sum(c[i][j] * new[j] for j in range(n)) for i in range(n)]
    t = TransformationMatrix.from_new2old(list(old), list(new), new2old)
    ti = t.inv()
    fwd = " ".join(num_str(x) for x in sympy.flatten(t.tolist()))
    back = " ".join(num_str(x) for x in sympy.flatten(ti.tolist()))
    zeros = sum(row.count(0) for row in c)
    cls = f"n={n}:" + ("has-zoo" if zeros else "no-zero")
    return f"helpers.tm {arr_token((n, n), [x for row in c for x in row])}", f"{fwd} | {back}", cls


if __name__ == "__main__":
    run(gen, default_cases=50000)
