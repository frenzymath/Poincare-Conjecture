# Poincare Conjecture

Lean 4 formalization of the smooth and topological Poincare conjectures,
following Morgan--Tian. The Lean package is at the repository root and the
independent comparator is under `comparator/`.

The source package is `PoincareMT`, with `PoincareMT.lean` as its root entry
point. Pins are Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`,
Comparator `3927ad383f208ae977c340a91c48ac9b497d2097`, and lean4export
`15f6055e299ad5b89345e533cc2192f4cc00f659`.

## Build

```sh
lake exe cache get --repo=leanprover-community/mathlib4 --cache-from=master,legacy
LEAN_NUM_THREADS=192 lake build
```

The build should end with `Build completed successfully` and exit code 0.

## Comparator

`comparator/Challenge.lean` contains the Mathlib-only public statements.
`comparator/Solution.lean` repeats those declarations and delegates their proof
bodies to `PoincareMT.Proofs.Main`. `comparator/comparator.json` compares the
exported interfaces and permits only `propext`, `Classical.choice`, and
`Quot.sound`. Only the independent challenge declarations contain `sorry`;
the solution calls the project's endpoint theorems. The configuration also
enables the independent Nanoda kernel check.

Prepare the pinned comparator and exporter through Lake:

```sh
lake build @Comparator/comparator @lean4export/lean4export
```

On Linux, run it as an unprivileged user through a user systemd unit with
Landrun, lean4export, and Nanoda available:

```sh
COMPARATOR_LANDRUN=/path/to/landrun \
COMPARATOR_LEAN4EXPORT="$PWD/.lake/packages/lean4export/.lake/build/bin/lean4export" \
COMPARATOR_NANODA=/path/to/nanoda_bin \
  systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$PWD" -E PATH -E COMPARATOR_LANDRUN \
  -E COMPARATOR_LEAN4EXPORT -E COMPARATOR_NANODA -E LEAN_NUM_THREADS=192 \
  lake env .lake/packages/Comparator/.lake/build/bin/comparator \
  comparator/comparator.json
```

Comparator success prints `Your solution is okay!`.
