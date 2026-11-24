# How an area is modelled

This file is the instruction sheet for anyone, human or agent, who adds an area to this repository. `lean/EinsteinpyLean/Tensor/` and `difftest/tensor_index_diff.py` are the worked example, so read them first.

## The pinned versions

Everything is about einsteinpy at commit `63e1c54537a385c9f56d7d4075b0261ddaa96069` (main on 10 November 2026, version 0.6.dev0), with sympy 1.14.0 and NumPy 2.5.5. The source sits in `vendor/einsteinpy/` and `.venv/` has exactly that commit installed. Always run Python as `.venv/bin/python`. Every model cites the source as `path:line` relative to `vendor/einsteinpy/src/einsteinpy/`.

The Lean side is Lean 4.36.0 with Physlib at `cbd02238fd1414edd9fa34871acc2a0fcdc20c21` (and the Mathlib it pins). Fetch the prebuilt Physlib files with `scripts/fetch_cache.sh` before the first build, otherwise Lake compiles Physlib from source.

## Two layers

The NumPy project this one copies had no Mathlib at all. Here Physlib is the point, so every area has two layers.

- The executable model (`Model.lean`, `Diff.lean`, and `Props.lean`) uses only core Lean. It mirrors the Python code on exact rationals (`Rat`) and is linked into the `epdiff` executable, which therefore never links Mathlib. Shared code is in `lean/EinsteinpyLean/Common/`. `Arr.lean` mirrors `sympy.Array`, `tensorproduct`, `tensorcontraction` and `permutedims`, including what sympy does with negative axes.
- The specification (`Spec.lean`) imports Physlib and Mathlib and states the physics over the reals. It restates the formula the code computes as a Mathlib expression (for example `Λᵀ *ᵥ w` for a lower index) and proves or refutes the physical claim against Physlib's definitions: `LorentzGroup d`, `minkowskiMatrix`, the FLRW and Schwarzschild files, and so on.

The two layers meet in the difftest. The model is checked against einsteinpy case by case, and the spec states the same formula in general. When the link is not obvious, prove a concrete instance in `Props.lean` that evaluates the model on the same numbers as a spec counterexample.

## Files for an area called `Foo`

- `lean/EinsteinpyLean/Foo/Model.lean`, `Props.lean`, `Diff.lean` (core Lean only) and `Spec.lean` (Physlib).
- `difftest/foo_<topic>_diff.py`, one per handler group, built on `difftest/harness.py`.
- `bugs/foo-<slug>.yaml` and `bugs/repro/foo-<slug>.py`, one pair per bug record.

Each area also has `lean/exe/Foo.lean`, the root of its own executable `epdiff_foo`, which `lean/lakefile.toml` already declares. Copy `lean/exe/Tensor.lean` and change the two names. Difftests call `run(gen, exe="epdiff_foo")`.

Do not edit `lean/Main.lean`, `lean/EinsteinpyLean.lean`, `lean/lakefile.toml`, anything in `lean/EinsteinpyLean/Common/`, `difftest/harness.py` or another area's files. The maintainer wires finished areas into `epdiff` and the library root. If you need a shared helper, put a copy in your own area directory.

## Building

```sh
cd lean
lake build EinsteinpyLean.Foo.Model EinsteinpyLean.Foo.Props EinsteinpyLean.Foo.Spec epdiff_foo
```

Build only your own targets. Other areas are being written at the same time and may not compile yet. Plain `lake build` builds only the wired-in areas.

## The areas

| Area | einsteinpy code (under `src/einsteinpy/`), all modelled |
| --- | --- |
| Tensor | `symbolic/tensor.py` |
| Helpers | `symbolic/helpers.py` |
| Curvature | `symbolic/metric.py`, `christoffel.py`, `riemann.py`, `ricci.py`, `einstein.py`, `weyl.py`, `schouten.py`, `stress_energy_momentum.py`, `vector.py` |
| Predefined | `symbolic/predefined/*`, `symbolic/constants.py` |
| Utils | `utils/dual.py`, `utils/scalar_factor.py`, `utils/exceptions.py`, `units.py`, `constant.py`, `bodies.py` |
| Coordinates | `coordinates/conversion.py`, `core.py`, `differential.py`, `utils.py` |
| Metric | `metric/base_metric.py`, `schwarzschild.py`, `kerr.py`, `kerrnewman.py` |
| Geodesic | `geodesic/geodesic.py`, `geodesic/utils.py`, `integrators/*`, `rays/shadow.py`, `hypersurface/schwarzschildembedding.py` |

`plotting/` and `examples.py` are out of scope.

## Step 1: mirror the source

Follow the Python code line by line, with the same order of checks and the same error cases. Model what the code does, not what the documentation says. Anything sympy or NumPy does on the way is part of the code: if `simplify` is the identity on rationals say so in a comment, and if sympy has its own quirk (such as unnormalised negative axes) mirror it from sympy's source.

- Python truthiness, `None`, negative indices and slices all matter. `Tensor/Model.lean` has `truthy`, `pyOr`, `pyIndex`, `sliceBound` and `dropAt`.
- One constructor of an error type per raise site, with the message in a doc comment and a `tag` that matches the Python exception class.
- Floating point: symbolic code is tested with rational inputs, where sympy is exact. Numerical code (`metric/`, `coordinates/`, `geodesic/`) is tested with Lean `Float` against NumPy only where the operations are `+ - * / sqrt`, with an absolute and relative tolerance that the test file states. libm functions (`sin`, `exp`, `arctan2`) are out of scope for exact agreement, so test identities around them instead.

## Step 2: differential test

Write `gen(rng)` returning `(epdiff input line, expected string from einsteinpy, outcome class)`. Bias the generator toward edges: empty configs, rank 0, negative indices, `None`, zero, singular matrices. Check the printed outcome counts and rebalance until every class appears often.

The bar is 50,000 agreeing cases on each of seeds 0, 1 and 2:

```sh
.venv/bin/python difftest/foo_topic_diff.py --cases 50000 --seed 0
```

A mismatch means the model is wrong. Never change the expected side to make a test pass. If the mismatch shows einsteinpy doing something surprising, that is a lead for step 3. sympy is slow, so one seed of 50,000 takes about three minutes. Run the three seeds in parallel.

## Step 3: prove or refute

Each property has a doc comment whose first line is exactly

```
PROP <area>.<function>.<name> : PROVEN
```

with `PROVEN`, `REFUTED` or `OPEN`, and whose second line gives the source of the claim (docstring, comment, physics textbook, Physlib definition). `REFUTED` means the theorem states the negation and proves it with a concrete counterexample. Never weaken a false statement until it becomes true. `sorry` and new axioms are not allowed. `native_decide` is allowed for concrete evaluations of the model and the file must say why. Concrete examples that are not properties carry no `PROP` line.

After a property is refuted, rerun the counterexample in real einsteinpy. A theorem about a model that does not match the library is worth nothing.

## Step 4: bug records

A refuted property is a bug candidate when real einsteinpy shows the same behaviour and the behaviour is wrong by its documentation, by physics or by plain consistency. Write `bugs/foo-<slug>.yaml` with the fields `id`, `title`, `area`, `kind` (crash, wrong-result, wrong-error, docs-mismatch, inconsistent), `severity` (high, medium, low), `einsteinpy_commit`, `source`, `property`, `summary` and `upstream`, and `bugs/repro/foo-<slug>.py`, which prints `REPRODUCED` as its last line when the bug is present.

Before filling `upstream`, search open and closed issues and pull requests with `gh api -X GET search/issues -f q='repo:einsteinpy/einsteinpy ...'` and compare the cited code with current main. Use NEW, RELATED, KNOWN-OPEN, KNOWN-CLOSED or FIXED-ON-MAIN.

## Checks

```sh
cd lean && lake build && cd ..
.venv/bin/python scripts/check_props.py
.venv/bin/python scripts/check_bugs.py
```

## Rules

- Commit one file per commit with `scripts/commit_file.sh <path> "<message>"`. It also pushes. Commit work in progress too, and fix mistakes with new commits, never by rewriting history. Commit messages are plain English, with a scope such as `curvature:`, and never mention AI tools.
- Keep the laptop safe: 16 GB of RAM. Never build all of Physlib or Mathlib from source, and keep sympy cases small (dimension at most 4, rank at most 4).
- Nothing goes to einsteinpy or Physlib from this repository automatically. Physlib's AI policy requires a human to vouch for every line and to do all review communication.
