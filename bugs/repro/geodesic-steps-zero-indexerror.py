"""Geodesic with steps=0 (or a negative number) raises IndexError instead of returning an empty trajectory."""
import warnings

warnings.simplefilter("ignore")
from einsteinpy.geodesic import Timelike

raised = []
for steps in (0, -3):
    try:
        Timelike("Schwarzschild", (), [10.0, 1.5707963267948966, 0.0], [0.0, 0.0, 0.1], steps=steps)
        raised.append(None)
    except IndexError as e:
        print(f"steps = {steps}: IndexError: {e}")
        raised.append(e)
if all(raised):
    print("REPRODUCED")
