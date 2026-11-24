"""StressEnergyMomentumTensor.change_config returns an EinsteinTensor."""
import sympy
from sympy.abc import t, x

from einsteinpy.symbolic.metric import MetricTensor
from einsteinpy.symbolic.stress_energy_momentum import StressEnergyMomentumTensor

metric = MetricTensor([[-1, 0], [0, 1 + x**2]], (t, x))
s = StressEnergyMomentumTensor.from_metric(metric)
u = s.change_config("ul")
lt = s.lorentz_transform([[1, 0], [0, 1]])
print("from_metric:", type(s).__name__)
print("change_config:", type(u).__name__)
print("lorentz_transform:", type(lt).__name__)
assert type(s).__name__ == "StressEnergyMomentumTensor"
assert type(lt).__name__ == "StressEnergyMomentumTensor"
assert type(u).__name__ == "EinsteinTensor"
print("REPRODUCED")
