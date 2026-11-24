"""Minkowski (-+++) and Schwarzschild with sch=0 (+---) disagree in sign."""
from sympy import S
from einsteinpy.symbolic.predefined import MinkowskiCartesian, Schwarzschild

m = MinkowskiCartesian(c=S(1)).tensor()
s = Schwarzschild(c=S(1), sch=S(0)).tensor()
print("Minkowski g_tt:", m[0, 0], " Schwarzschild(r_s=0) g_tt:", s[0, 0])
assert m[0, 0] == -1 and s[0, 0] == 1
print("REPRODUCED")
