"""Cross-check of the numerical metrics against the symbolic predefined metrics of einsteinpy.

For Schwarzschild, Kerr and Kerr-Newman at random points, the numerical covariant metric must be `c**2` times the symbolic
one (the numerical code uses `ds^2 = c^2 d tau^2`, the symbolic code `d tau^2`; both have signature (+, -, -, -)), and the
numerical metric derivatives `_dg_dx_bl` and Christoffel symbols, every index and each entry on its own scale, must equal
those computed from the symbolic metric by sympy differentiation and a numerical matrix inverse at 40 digits. This also
tests the hand-coded off-diagonal Kerr symbols. There is no Lean side: the Lean model is compared with the numerical code
bit for bit in the other difftests, so this closes the triangle. It reports the entries that disagree.

    .venv/bin/python difftest/metric_symbolic_diff.py --points 40 --seed 0
"""
import argparse
import random
import warnings

import numpy as np
import sympy as sp
from astropy import units as u

from einsteinpy import constant
from einsteinpy.metric import Kerr, KerrNewman, Schwarzschild
from einsteinpy.symbolic.predefined import vacuum_solutions as vs

warnings.simplefilter("ignore")
c, G, Cc, eps0 = (constant.c.value, constant.G.value, constant.coulombs_const.value, constant.eps0.value)
t, r, th, ph = sp.symbols("t r theta phi")
X = [t, r, th, ph]


class Coords:
    def __init__(self, s):
        self.system = s


def christoffels(gm, pt):
    """Christoffel symbols and the derivative array `dg[k, i, j] = d_k g_ij` of a symbolic metric at a point."""
    gis = gm.subs(pt).evalf(40).inv()
    dg = [[[sp.diff(gm[i, j], X[k]).subs(pt).evalf(40) for k in range(4)] for j in range(4)] for i in range(4)]
    ch = np.zeros((4, 4, 4))
    for i in range(4):
        for j in range(4):
            for k in range(4):
                ch[i, j, k] = float(sum(gis[i, l] * (dg[l][j][k] + dg[l][k][j] - dg[j][k][l]) for l in range(4)) / 2)
    d = np.array([[[float(dg[i][j][k]) for j in range(4)] for i in range(4)] for k in range(4)])
    return ch, d


def entry_error(a, b):
    """Largest error of an entry relative to that entry, ignoring entries below 1e-9 of the largest, and its index."""
    scale = np.abs(b).max()
    err = np.where(np.abs(b) > 1e-9 * scale, np.abs(a - b) / np.maximum(np.abs(b), 1e-300), 0.0)
    return err.max(), tuple(int(v) for v in np.unravel_index(err.argmax(), err.shape))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--points", type=int, default=40)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    worst = {}
    for name in ("schwarzschild", "kerr", "kerr-newman"):
        for _ in range(args.points):
            Mv = 10 ** rng.uniform(25, 33)
            a = rng.random() * 0.9
            rs = 2 * G * Mv / c**2
            alpha = a * G * Mv / c**2
            Qv = Mv * np.sqrt(G / Cc) * rng.uniform(0, 0.4) if name == "kerr-newman" else 0.0
            rv, thv = rs * rng.uniform(1.5, 10), rng.uniform(0.2, 2.9)
            x = np.array([0, rv, thv, 0.0])
            F = lambda v: sp.Float(v, 30)  # noqa: E731
            if name == "schwarzschild":
                m, sym = Schwarzschild(Coords("Spherical"), Mv * u.kg), vs.Schwarzschild(c=F(c), sch=F(rs))
            elif name == "kerr":
                m, sym = Kerr(Coords("BoyerLindquist"), Mv * u.kg, a * u.one), vs.Kerr(c=F(c), sch=F(rs), a=F(alpha))
            else:
                m = KerrNewman(Coords("BoyerLindquist"), Mv * u.kg, a * u.one, Qv * u.C)
                sym = vs.KerrNewman(c=F(c), G=F(G), eps_0=F(eps0), sch=F(rs), a=F(alpha), Q=F(Qv))
            gm = sp.Matrix(sym.tensor())
            pt = {r: F(rv), th: F(thv), t: 0, ph: 0}
            gs = np.array(gm.subs(pt).evalf(30).tolist(), dtype=float)
            e1 = np.abs(m.metric_covariant(x) - c**2 * gs).max() / np.abs(gs).max() / c**2
            ch, dg = christoffels(gm, pt)
            e2, i2 = entry_error(m.christoffels(x), ch)
            e3, i3 = (0.0, ()) if name == "schwarzschild" else entry_error(m._dg_dx_bl(x), c**2 * dg)
            w = worst.get(name, (0.0, 0.0, (), 0.0, ()))
            worst[name] = (max(w[0], e1), max(w[1], e2), i2 if e2 > w[1] else w[2], max(w[3], e3), i3 if e3 > w[3] else w[4])
    bad = False
    for name, (e1, e2, i2, e3, i3) in worst.items():
        print(f"{name:14s} metric {e1:.1e}   christoffel {e2:.1e} at {i2}   dg_dx {e3:.1e} at {i3}")
        bad |= e1 > 1e-12 or e2 > 1e-8 or e3 > 1e-8
    print("AGREE" if not bad else "DISAGREE")
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
