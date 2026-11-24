"""DualNumber == number raises AttributeError, and DualNumber is unhashable."""
from einsteinpy.utils.dual import DualNumber

x = DualNumber(1.0, 0.0)
raised = []
for other in (1, None):
    try:
        x == other
    except AttributeError as e:
        raised.append(str(e))
print(raised)
try:
    hash(x)
except TypeError as e:
    print(e)
    if len(raised) == 2:
        print("REPRODUCED")
