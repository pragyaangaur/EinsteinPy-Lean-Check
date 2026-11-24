"""Difftest for einsteinpy/rays/shadow.py and einsteinpy/hypersurface/schwarzschildembedding.py.

Only einsteinpy's own formulas are compared, bit for bit: ``b_crit``, ``horizon`` and ``_compute_B`` (through
the real constructor of ``Shadow``, with scipy's ``newton`` and ``fixed_quad`` replaced by constants), the two
intensity integrands on an array of nodes, ``_root_equation`` (including its complex branch), and the
embedding's ``M``, ``r_init``, ``radial_coord``, ``gradient`` and ``get_values``.
"""
import math
import os
import sys
from unittest import mock

sys.path.insert(0, os.path.dirname(__file__))

import numpy as np
from astropy import units as u

import geodesic_common as C
from einsteinpy.hypersurface import SchwarzschildEmbedding
from einsteinpy.rays import Shadow
from harness import run


def mass(rng):
    r = rng.random()
    if r < 0.3:
        return rng.choice([1.0, 2.0, 0.5, 1.5, 3.0, 10.0, 2.9, 0.0, -1.0, 1e-3])
    if r < 0.35:
        return rng.choice(C.EDGE)
    return rng.uniform(0.1, 20.0)


def make_shadow(m, fov, n):
    with mock.patch("einsteinpy.rays.shadow.newton", lambda *a, **k: 1.0), \
            mock.patch("einsteinpy.rays.shadow.fixed_quad", lambda *a, **k: (0.0, None)):
        return Shadow(mass=m * u.kg, fov=fov * u.km, n_rays=n)


def bare(m):
    s = Shadow.__new__(Shadow)
    s.mass = m * u.kg
    return s


def case_consts(rng):
    m = mass(rng)
    line = f"geo.sh.consts {C.hexf(m)}"

    def f():
        s = make_shadow(m, 30.0, 2)
        return C.hl([s.b_crit.value, s.horizon])

    return line, C.real(f)


def case_b(rng):
    m = mass(rng)
    fov = rng.choice([30.0, 10.0, 5.0, 100.0, 1.0, rng.uniform(1, 50), 0.0, -4.0, C.NAN, C.INF, 1e-300, 1e300])
    n = rng.choice([0, 1, 2, 3, 5, 7, 10, 12, -1, 4, 6])
    line = f"geo.sh.b {C.hexf(m)} {C.hexf(fov)} {n}"

    def f():
        s = make_shadow(m, fov, n)
        return C.hl(s.b)

    return line, C.real(f)


def nodes(rng, m):
    out = []
    for _ in range(5):
        r = rng.random()
        if r < 0.1:
            out.append(rng.choice([2 * m, 3 * m, 0.0, -1.0, C.NAN, C.INF, 1e200]))
        elif r < 0.2:
            out.append(rng.uniform(0.1, 2.5 * m + 0.1))
        else:
            out.append(rng.uniform(2 * m + 0.01, 60.0))
    return out


def case_int(rng):
    which = rng.choice(["blue", "red"])
    m = rng.choice([1.0, 2.0, 0.5, rng.uniform(0.1, 5), mass(rng)])
    b = rng.choice([5.196152422706632, 6.0, 10.0, rng.uniform(0, 30), 0.0, C.NAN, -3.0])
    rs = nodes(rng, abs(m) if math.isfinite(m) else 1.0)
    line = f"geo.sh.int {which} {C.hexf(m)} {C.hexf(b)} {C.hl(rs)}"

    def f():
        s = bare(m)
        fn = s._intensity_blue_sch if which == "blue" else s._intensity_red_sch
        return C.hl(fn(np.array(rs), np.float64(b)))

    return line, C.real(f)


def case_root(rng):
    m = rng.choice([1.0, 2.0, 0.5, 1.5, 3.7, 10.0, 0.0, -2.5, mass(rng)])
    r = rng.choice([0.1, 1.0, 2.0, 3.0, 0.5, 10.0, rng.uniform(0.01, 20), -1.0, 0.0, -0.0, C.NAN, C.INF, 1e300, 5e-324])
    i = rng.choice([5.196152422706632, 0.0, 6.0, rng.uniform(-3, 30), C.NAN, C.INF])
    line = f"geo.sh.root {C.hexf(m)} {C.hexf(r)} {C.hexf(i)}"

    def f():
        s = bare(m)
        res = s._root_equation(np.float64(r), np.float64(i))
        if isinstance(res, complex):
            return "C" + C.hexf(res.real) + "," + C.hexf(res.imag)
        return "F" + C.hexf(res)

    return line, C.real(f)


def case_ctor(rng):
    m = rng.choice([5.972e24, 1e23, 4e24, 1e22, 1e30, 2e33, rng.uniform(1e20, 1e36), -1e23,
                    10 ** rng.uniform(5, 36)])
    line = f"geo.emb.ctor {C.hexf(m)}"

    def f():
        e = SchwarzschildEmbedding(m * u.kg)
        return C.hl([e.M.value, e.r_init.value])

    return line, C.real(f)


def case_embf(rng):
    M = rng.choice([1.0, 4e1, 5.972, 0.5, 2.0, rng.uniform(0.1, 100), -1.0, 0.0, C.NAN])
    a = abs(M) if M == M and abs(M) != C.INF else 1.0
    r = rng.choice([2 * a, 3 * a, 2.25 * a, 1200.0, 170000.0, rng.uniform(0, 10 * a + 1), -1.0, 0.0, C.NAN, rng.uniform(2.3 * a, 40 * a + 1)])
    line = f"geo.emb.f {C.hexf(M)} {C.hexf(r)}"

    def f():
        e = SchwarzschildEmbedding(1e23 * u.kg)
        e.M = M * e.M.unit
        return C.hl([e.radial_coord(np.float64(r)), e.gradient(np.float64(r))])

    return line, C.real(f)


def case_vals(rng):
    m = rng.choice([5.972e24, 1e23, 4e24, 1e22, 1e25, rng.uniform(1e22, 1e26)])
    a = rng.choice([1, 2, 5, 10, 20, 100, 3.5, 0.5, 7])
    line = f"geo.emb.vals {C.hexf(m)} {C.hexf(a)}"

    def f():
        e = SchwarzschildEmbedding(m * u.kg)
        x, y = e.get_values(a)
        return C.hl(x) + ";" + C.hl(y)

    return line, C.real(f)


CASES = [(case_consts, 6), (case_b, 14), (case_int, 24), (case_root, 18), (case_ctor, 6), (case_embf, 24),
         (case_vals, 8)]


def gen(rng):
    r = rng.random() * sum(w for _, w in CASES)
    for fn, w in CASES:
        r -= w
        if r < 0:
            break
    line, ans = fn(rng)
    cls = ans if ans.startswith("E:") else ("nan" if "nan" in ans else "ok")
    if ans.startswith("C"):
        cls = "complex"
    return line, ans, line.split()[0] + ":" + cls


if __name__ == "__main__":
    run(gen, exe="epdiff_geodesic")
