"""find() cannot find the Reissner-Nordstrom or Barriola-Vilenkin metrics by their real names."""
from einsteinpy.symbolic.predefined import find

print("find('nordstrom'):", find("nordstrom"), " find('vilenkin'):", find("vilenkin"))
print("find('nordstorm'):", find("nordstorm"), " find('vilekin'):", find("vilekin"))
assert find("nordstrom") == [] and find("vilenkin") == []
assert find("nordstorm") == ["ReissnerNordstorm"] and find("vilekin") == ["BarriolaVilekin"]
print("REPRODUCED")
