"""FLRW and KerrNewmanDeSitter use real=True coordinate symbols, so they do not match the plain ones."""
import sympy
from einsteinpy.symbolic.predefined import FriedmannLemaitreRobertsonWalker, Schwarzschild

plain_r = sympy.Symbol("r")
f = FriedmannLemaitreRobertsonWalker()
s = Schwarzschild()
print("FLRW r is plain r:", plain_r in f.tensor().free_symbols, "; Schwarzschild r is plain r:", plain_r in s.tensor().free_symbols)
print("substituting r=2 into FLRW g_rr:", f.tensor()[1, 1].subs(plain_r, 2))
assert plain_r not in f.tensor().free_symbols and plain_r in s.tensor().free_symbols
print("REPRODUCED")
