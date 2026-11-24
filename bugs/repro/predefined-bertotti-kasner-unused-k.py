"""BertottiKasner(c, 2) puts 2 in the unused k, not in the cosmological constant lambd."""
import inspect
import re

import sympy
from sympy import S
from einsteinpy.symbolic.predefined import BertottiKasner

print(inspect.signature(BertottiKasner))
a = BertottiKasner(S(1), S(2)).tensor()
print("free symbols after BertottiKasner(1, 2):", a.free_symbols)
# the 2 went to k, so lambd is still the default symbol l
assert sympy.Symbol("l") in a.free_symbols
body = inspect.getsource(BertottiKasner).split('"""')[2]
assert not re.search(r"\bk\b", body)  # no line of the body reads k
print("REPRODUCED")
