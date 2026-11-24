"""Differential test of predefined.find against the Lean model.

Search strings are ASCII (Lean's toLower and Python's lower differ elsewhere). An empty
string is sent as `-`.
"""
import random

import einsteinpy.symbolic.predefined as P
from einsteinpy.symbolic.predefined import find

from harness import run

NAMES = [n for n in dir(P)] + ["Nordstrom", "Vilenkin", "Minkowski", "de", "ADS", "kerr"]
LETTERS = "abcdeklmnorstuvwxyzABCDEKLMNRSTUVWXYZ_"


def gen(rng):
    k = rng.random()
    if k < 0.08:
        s = ""
    elif k < 0.55:
        n = rng.choice(NAMES)
        i = rng.randrange(len(n))
        j = rng.randint(i + 1, len(n))
        s = n[i:j]
        if rng.random() < 0.5:
            s = s.swapcase() if rng.random() < 0.5 else s.lower()
    else:
        s = "".join(rng.choice(LETTERS) for _ in range(rng.randint(1, 5)))
    res = find(s)
    return f"predef.find {s or '-'}", ",".join(res) or "-", "hit" if res else "empty"


if __name__ == "__main__":
    run(gen, default_cases=50000, exe="epdiff_predefined")
