"""SymbolicConstant("c") with no description wipes the description of constants.c."""
from einsteinpy.symbolic import constants

print("before:", constants.c.descriptive_name)
constants.SymbolicConstant("c")
print("after SymbolicConstant('c'):", constants.get_constant("c").descriptive_name)
assert constants.c.descriptive_name is None
print("REPRODUCED")
