"""Shared driver for every differential test.

A test module defines ``gen(rng) -> (line, expected, outcome_class)`` and calls
``run(gen)``. The driver feeds every line to the Lean executable ``epdiff`` in one
process, compares the answers with the expected strings computed from real
einsteinpy, and prints outcome counts so a reader can see that each branch was hit.
"""

import argparse
import collections
import pathlib
import random
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
EPDIFF = ROOT / "lean" / ".lake" / "build" / "bin" / "epdiff"


def arr_token(shape, data):
    """Encode an array as ``shape:data`` with exact rationals."""
    return ",".join(map(str, shape)) + ":" + ",".join(rat_str(x) for x in data)


def rat_str(x):
    import sympy

    x = sympy.Rational(x)
    return str(x.p) if x.q == 1 else f"{x.p}/{x.q}"


def render(shape, data):
    """Same rendering as ``Arr.render`` in Lean."""
    return f"[{', '.join(map(str, shape))}] " + " ".join(rat_str(x) for x in data)


def sympy_render(arr):
    import sympy

    arr = sympy.Array(arr)
    if arr.shape == ():
        return render((), [arr[()]])
    return render(arr.shape, list(sympy.flatten(arr.tolist())))


def run(gen, default_cases=50000):
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=default_cases)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--show", type=int, default=5, help="mismatches to print")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    t0 = time.time()
    cases = []
    for _ in range(args.cases):
        cases.append(gen(rng))
    t1 = time.time()

    proc = subprocess.run(
        [str(EPDIFF)],
        input="\n".join(c[0] for c in cases) + "\n",
        capture_output=True,
        text=True,
        check=True,
    )
    got = proc.stdout.splitlines()
    if len(got) != len(cases):
        print(f"epdiff returned {len(got)} lines for {len(cases)} cases")
        sys.exit(2)

    outcomes = collections.Counter()
    bad = 0
    for (line, want, cls), have in zip(cases, got):
        outcomes[cls] += 1
        if have != want:
            bad += 1
            if bad <= args.show:
                print(f"MISMATCH\n  in:   {line}\n  lean: {have}\n  py:   {want}")
    t2 = time.time()
    print(f"seed {args.seed}: {len(cases) - bad}/{len(cases)} agree "
          f"(python {t1 - t0:.1f}s, lean {t2 - t1:.1f}s)")
    for k, v in sorted(outcomes.items()):
        print(f"  {k}: {v}")
    sys.exit(1 if bad else 0)
