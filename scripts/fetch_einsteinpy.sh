#!/bin/sh
# Put einsteinpy at the pinned commit in vendor/einsteinpy and install it into .venv.
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COMMIT=63e1c54537a385c9f56d7d4075b0261ddaa96069
cd "$ROOT"
if [ ! -d vendor/einsteinpy ]; then
  git clone https://github.com/einsteinpy/einsteinpy vendor/einsteinpy
fi
git -C vendor/einsteinpy fetch origin
git -C vendor/einsteinpy checkout -q "$COMMIT"
python3 -m venv .venv
.venv/bin/pip install -q ./vendor/einsteinpy pyyaml
.venv/bin/python -c "import einsteinpy, sympy; print(einsteinpy.__version__, sympy.__version__)"
