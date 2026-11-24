"""RK4naive: the direction expression is always 0, so the t_bound guard never fires and the solver steps past t_bound."""
import warnings

warnings.simplefilter("ignore")
from einsteinpy.integrators import RK4naive

# y' = 1 from t = 0.125 to t_bound = 1.125 with h = 0.25: four steps reach the bound exactly (binary fractions)
solver = RK4naive(lambda t, y: 1.0, 0.125, 1.0, 1.125, 0.25)
print("direction forward :", solver.direction, "(scipy would give 1)")
for _ in range(4):
    solver.step()
print("after 4 steps     :", (solver.t, solver.y))
solver.step()
print("after a 5th step  :", (solver.t, solver.y), "(should stay at t_bound)")
back = RK4naive(lambda t, y: 1.0, 1.125, 1.0, 0.125, -0.25)
print("direction backward:", back.direction, "(scipy would give -1)")
if solver.direction == 0 and back.direction == 0 and solver.t > 1.125:
    print("REPRODUCED")
