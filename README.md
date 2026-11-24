# EinsteinPy Lean Check

This repository checks einsteinpy, the Python package for general relativity, against a Lean 4 model built on Physlib. It uses the same method as [NumPy Lean Check](https://github.com/pragyaangaur/NumPy-Lean-Check). Each part of einsteinpy is mirrored in Lean line by line, the Lean model is run against the real library on random inputs until they agree on every case, and then properties are proved or refuted. A refuted property that real einsteinpy also shows becomes a bug record with a script that reproduces it.

The new part is Physlib. The executable model only uses core Lean and exact rational numbers, so it can be compared with sympy's exact answers. The specification layer states the same formulas over the real numbers and checks them against Physlib's definitions, such as `LorentzGroup d` and `minkowskiMatrix`. This lets a claim like "the boost preserves the contraction of a vector with a covector" be proved for every Lorentz transformation, and not only for the cases a test happens to try.

## Pinned versions

einsteinpy is pinned at commit `63e1c54` (main on 10 November 2026, version 0.6.dev0) with sympy 1.14.0. The Lean side is Lean 4.36.0 with Physlib at `cbd0223` and the Mathlib it pins.

## State

| Area | einsteinpy code | Difftest | Proven | Refuted |
| --- | --- | --- | --- | --- |
| Tensor | `symbolic/tensor.py`: config checks, `_change_config`, `tensor_product`, `lorentz_transform` | 150,000 of 150,000 agree on seeds 0, 1 and 2 | 6 | 4 |
| Helpers | `symbolic/helpers.py`: `TransformationMatrix` | 150,000 of 150,000 agree on seeds 0, 1 and 2 | 2 | 1 |

There is no `sorry` and no new axiom. Five `native_decide` calls evaluate the compiled model on single concrete inputs, and each file says so next to them.

## Bug records

| Record | Severity | Upstream |
| --- | --- | --- |
| `tensor-lorentz-lower-index`: `lorentz_transform` uses the matrix instead of its inverse on lower indices | high | Known as einsteinpy#374, fixed by the open PR einsteinpy#708. The Lean proofs show the rule in #708 is right for all of Physlib's Lorentz group |
| `helpers-transformation-matrix-reciprocal`: `TransformationMatrix` inverts each entry instead of the Jacobian, and its test expects the wrong values | medium | Not found in the tracker |
| `tensor-product-negative-index`: `tensor_product` with a negative index returns a wrong tensor of the wrong rank | medium | Not found in the tracker |
| `tensor-product-zero-index-ignored`: `tensor_product(t1, t2, 0)` skips the contraction, while `i=1` crashes with a TypeError | low | Not found in the tracker |

Each record is in `bugs/` with its reproducer in `bugs/repro/`.

## Running it

```sh
scripts/fetch_einsteinpy.sh
scripts/fetch_cache.sh
cd lean && lake build && cd ..
.venv/bin/python difftest/tensor_index_diff.py --cases 50000 --seed 0
.venv/bin/python scripts/check_props.py
.venv/bin/python scripts/check_bugs.py
```

`docs/MODELLING.md` explains how a new area is added.
