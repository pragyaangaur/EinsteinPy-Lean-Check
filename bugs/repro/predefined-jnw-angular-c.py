"""JanisNewmanWinicour with gam=1 is not Schwarzschild: the angular part is not divided by c**2."""
import sympy
from sympy import Rational as Q
from einsteinpy.symbolic.predefined import JanisNewmanWinicour, Schwarzschild

c, G, M = Q(2), Q(1), Q(1)
jnw = JanisNewmanWinicour(c=c, G=G, gam=sympy.Integer(1), M=M).tensor()
sch = Schwarzschild(c=c, sch=2 * G * M / c**2).tensor()
th = sympy.Symbol("theta")
print("JNW g_thth:", jnw[2, 2], " minus Schwarzschild g_thth:", -sch[2, 2])
print("JNW g_rr:", jnw[1, 1], " minus Schwarzschild g_rr:", -sch[1, 1])
assert sympy.simplify(jnw[1, 1] + sch[1, 1]) == 0
assert sympy.simplify(jnw[2, 2] + sch[2, 2]) != 0
print("REPRODUCED")
