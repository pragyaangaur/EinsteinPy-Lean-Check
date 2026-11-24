"""Differential test of constants.py (SymbolicConstant, get_constant) against the Lean model.

A case is a short script of operations on the module level constants:
`new:<name>:<desc>` calls `SymbolicConstant(name, desc)` (`_` is None) and `get:<key>`
calls `get_constant(key)`. Each answer is `<symbol name>/<descriptive name>` or `ERR KeyError`.
sympy caches Symbol construction, so `new` of an existing name returns the same object and
overwrites its descriptive name. This test runs in its own process and creates few symbols,
so the cache is never evicted (with SYMPY_USE_CACHE=no the behaviour differs).
"""
from einsteinpy.symbolic import constants as C

from harness import run

ORIG = {"c": "Speed Of Light", "G": "Gravitational Constant",
        "Lambda": "Cosmological Constant", "eps_0": "Permittivity of free space"}
OBJ = {"c": C.c, "G": C.G, "Lambda": C.Cosmo_Const, "eps_0": C.eps_0}
NAMES = ["c", "G", "Lambda", "eps_0", "foo", "bar"]
KEYS = ["c", "G", "Cosmo_Const", "eps_0", "Lambda", "foo", "C", "g"]
DESCS = ["_", "_", "X", "Speed", "Other", "Y"]


def gen(rng):
    for k, o in OBJ.items():
        o._descriptive_name = ORIG[k]
    ops, outs, cls = [], [], set()
    for _ in range(rng.randint(1, 5)):
        if rng.random() < 0.5:
            n, d = rng.choice(NAMES), rng.choice(DESCS)
            ops.append(f"new:{n}:{d}")
            o = C.SymbolicConstant(n, None if d == "_" else d)
            outs.append(f"{o.name}/{o.descriptive_name}")
            cls.add("new")
        else:
            k = rng.choice(KEYS)
            ops.append(f"get:{k}")
            try:
                o = C.get_constant(k)
                outs.append(f"{o.name}/{o.descriptive_name}")
                cls.add("get")
            except KeyError:
                outs.append("ERR KeyError")
                cls.add("keyerror")
    return "predef.consts " + " ".join(ops), ",".join(outs), "+".join(sorted(cls))


if __name__ == "__main__":
    run(gen, default_cases=50000, exe="epdiff_predefined")
