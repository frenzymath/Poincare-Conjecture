# Audit — `frenzymath/ALLBOOKS` › `SmoothManifoldsLee`

Findings from importing the upstream Lean formalization of Lee, *Introduction to
Smooth Manifolds* (GTM 218) into this workspace as the `LeeSmooth` project.

- **Repo**: <https://github.com/frenzymath/ALLBOOKS/tree/main/SmoothManifoldsLee>
- **Commit audited**: `cdd0f105` (`main` — the only branch)
- **Audited**: 2026-07-16

## Summary

**The formalization does not build, and is not complete.** `lake build` of all
618 item modules exits **1** with **106 compile errors** across **31 modules**,
and the Lean kernel reports **306 declarations that use `sorry`** across 97
files.

This contradicts the belief that the formalization is complete. The section
[Why it looks complete](#why-it-looks-complete) explains, we think, why.

## How it was verified

Built in exactly the environment the repo specifies — no substitutions:

| | |
|---|---|
| Toolchain | `leanprover/lean4:v4.30.0` (from `lean-toolchain`) |
| Mathlib | `c5ea00351c28e24afc9f0f84379aa41082b1188f` — exactly the rev in the repo's own `lake-manifest.json` |
| Edit to repo | **one line**: added `globs = ["SmoothManifoldsLee.+"]` to `lakefile.toml` |

That single line is the whole point (see below): it makes `lake build` actually
compile the item files. Nothing else was modified.

## Why it looks complete

`lakefile.toml` declares the library with **no `globs`**:

```toml
[[lean_lib]]
name = "SmoothManifoldsLee"
```

Lake's default for a `lean_lib` is to build **the root module only**. And the
root module `SmoothManifoldsLee.lean` imports nothing from the project:

```lean
import Mathlib

/-!
# SmoothManifoldsLee
Top-level Lean library module for this generated project.
Generated item files live at their repo-relative target paths.
-/
```

So the default `lake build`:

- exits **0** in about **six seconds**,
- reports `Build completed successfully (8476 jobs)` — of which 8475 are cached
  mathlib jobs,
- produces exactly **one** project olean (the root), and
- compiles **none** of the 618 item files.

Every `sorry` warning and all 106 errors are invisible, because Lean only
reports them for files it actually compiles. A green `lake build` here is not
evidence of anything. Adding the `globs` line is what surfaces the real state.

The original extraction audit also recorded `"fullBuildFailed": true` with 14
skipped modules in its dependency manifest.

## State of the 618 item modules

| Status | Modules |
|---|---|
| Compiles, own proof, no `sorry` of its own | 373 |
| `recall`/`#check` facade (declares nothing itself) | 124 |
| Proof is `sorry` | 90 |
| **Fails to compile** | 31 |

Only 552 of 618 modules produce an olean.

Note that "373" counts modules with no `sorry` **of their own**. It is an upper
bound on what is actually verified: a module can be `sorry`-free yet invoke a
sorried lemma from a module it imports, in which case its results still rest on
`sorryAx`. 216 of the 550 modules importable here have a `sorry` somewhere in
their transitive import cone. Establishing exactly which declarations are clean
requires a per-declaration axiom check, not a per-file one.

### `sorry` inventory (kernel-reported: `declaration uses 'sorry'`)

306 declarations across 97 files.

By item kind: 92 Problem, 67 Proposition, 43 Theorem, 39 Definition,
36 Example, 15 Exercise, 8 Corollary, 4 Remark, 2 Lemma.

By chapter: Ch1 4, Ch2 18, Ch3 32, Ch4 65, **Ch5 103**, Ch6 12, Ch7 36, Ch8 36.

Excluding end-of-chapter `Problem`s as arguably out of scope still leaves
**120 core results** (theorems, propositions, corollaries, lemmas) proved by
`sorry`.

## Three defects worth fixing upstream

### 1. The default build target verifies nothing

Covered above. Fix: add `globs = ["SmoothManifoldsLee.+"]` to the `lean_lib`, or
have the root module import the item modules. Without this, CI on this repo is
vacuous.

### 2. `recall` can silently point at a sorried local declaration

`recall X` re-states an existing declaration — it does **not** imply `X` comes
from mathlib. Example: `Chap01/Sec01/Theorem_1_2.lean` reads

```lean
/- Theorem 1.2: ... This is exactly the canonical owner theorem
`TopologicalManifold.dimension_eq_of_homeomorph`. -/
recall TopologicalManifold.dimension_eq_of_homeomorph
```

which reads as "this is already in mathlib". It is not:
`TopologicalManifold.dimension_eq_of_homeomorph` is declared in this project, in
`Chap01/Sec01/Definition_1_extra_1.lean`, and an axiom check shows it depends on
`sorryAx`. So Theorem 1.2 (topological invariance of dimension) presents as a
mathlib leaf but is **unproved**.

Any per-item status that classifies `recall` files as "already in mathlib" will
therefore over-report completion. Status must come from an axiom check
(`collectAxioms` / `#print axioms`), not from the presence of `recall`.

### 3. The library cannot be imported as a whole

Two modules declare the same name, so importing both fails:

```
import SmoothManifoldsLee.Chap01.Sec01_05.Proposition_1_40 failed,
environment already contains 'connectedComponent_connectedSpace'
from SmoothManifoldsLee.Chap01.Sec01.Proposition_1_11
```

This is not a one-off: **165 declaration names are declared in more than one
module**. `Chap04/Sec04_26/Exercise_4_38.lean` and
`Chap04/Sec04_26/Example_4_35.lean`, for instance, contain the same copy-pasted
block of `Manifold.IsSmoothCoveringMap.*` declarations. Only 437 of the 550
importable modules can be loaded into one environment without a clash.

Because item modules are compiled independently and the root imports none of
them, such collisions are never detected by the build. This is a direct
consequence of defect 1: no module ever imports two colliding item modules, so
the clash only materialises when something tries to import the library as a
whole — which nothing upstream does.

## The 31 modules that fail to compile

Error kinds: application type mismatch, unsolved goals, stuck typeclass
instances, `simp` made no progress, failure to synthesize instances.

```
Chap01.Sec01.Proposition_1_16
Chap02.Sec02_12.Problem_2_9_corecheck
Chap02.Sec02_12.Problem_2_9_prefixcheck
Chap02.Sec02_12.Problem_2_9_pre_north
Chap03.Sec03_20.Problem_3_8
Chap04.Sec04_24.Example_4_20
Chap05.Sec05_30.Corollary_5_13
Chap05.Sec05_31.Example_5_26
Chap05.Sec05_32.Example_5_28
Chap05.Sec05_35.Example_5_45
Chap05.Sec05_37.Problem_5_1
Chap05.Sec05_37.Problem_5_2
Chap05.Sec05_37.Problem_5_21
Chap06.Sec06_40.Theorem_6_15
Chap06.Sec06_42.Theorem_6_24
Chap07.Sec07_47.Example_7_4_torus
Chap07.Sec07_49.Exercise_7_20
Chap07.Sec07_50.Example_7_28
Chap07.Sec07_53.Problem_7_1
Chap07.Sec07_53.Problem_7_13
Chap07.Sec07_53.Problem_7_15
Chap07.Sec07_53.Problem_7_16
Chap07.Sec07_53.Problem_7_18
Chap08.Sec08_54.Definition_8_54_extra_2
Chap08.Sec08_60.Corollary_8_42
Chap08.Sec08_60.Example_8_40
Chap08.Sec08_61.Definition_8_61_extra_1
Chap08.Sec08_62.Corollary_8_50
Chap08.Sec08_63.Problem_8_13
Chap08.Sec08_63.Problem_8_17
Chap08.Sec08_63.Problem_8_4
```

## What is genuinely good here

This is not a bad formalization — it is an unfinished one, and the finished part
is solid. The 373 proved modules contain real proofs: sensible lemma
decomposition, `calc` chains, honest route comments. The `#check`/`recall`
facades are also a legitimate design choice where mathlib genuinely owns the
result (much of Chapters 1–3 is real mathlib territory) — the problem is only
that the facade is indistinguishable from a sorried local declaration without an
axiom check, per defect 2.

## Bearing on the `LeeSmooth` workspace project

- **mathlib pin**: this Lean needs mathlib `c5ea0035` (v4.30.0), which is a
  strict descendant of the workspace pin `5fc0241` by **946 commits (one
  month)**. The workspace shares a single mathlib checkout — every project
  symlinks `DoCarmo/.lake/packages/mathlib` — so `LeeSmooth` cannot use it and
  is configured with a private checkout at its own rev.
- **What was imported**: 67 of the 618 modules were dropped because they do not
  compile (the 31 above plus 36 that depend on them). The remaining **550 build
  clean** as `LeeSmooth`: `lake build` → exit 0, 0 errors, 550/550 oleans, and
  279 `declaration uses 'sorry'` warnings that are now visible rather than
  hidden behind an empty default target.
- **Blueprint scope**: per project decision, the blueprint carries only items
  whose Lean is verified; sorried and non-compiling items are omitted rather
  than marked `\notready`. Of 599 book items, **310 are carried** (231 `\leanok`,
  79 `\mathlibok`) and **289 omitted**.
- **Known conservatism**: 117 of those 289 are omitted only because their module
  imports a sorried module, not because their own result is unproved. A
  per-declaration axiom check would likely restore a large share of them. Lemma
  1.10 is a confirmed example: its declaration
  `isTopologicalBasis_isPrecompactCoordinateBall` is verifiably sorry-free, but
  its module imports `Definition_1_extra_1`, which contains unrelated sorried
  declarations. This is the main piece of follow-up work.
- The source extraction covers **Chapters 1–8 only**, not all 22 chapters of the
  book.
