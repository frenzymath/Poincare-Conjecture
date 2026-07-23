<h1 align="center">LeeSmooth — Introduction to Smooth Manifolds</h1>

<p align="center"><em>Chapters 1–8 imported from an upstream formalization. Builds clean; substantially incomplete. See <code>UPSTREAM_LEAN_AUDIT.md</code>.</em></p>

A Lean 4 formalization following John M. Lee, *Introduction to Smooth Manifolds*
(Graduate Texts in Mathematics 218, 2nd ed.).

Distinct from the sibling `LeeRiemannian/` project, which formalizes the same
author's *Introduction to Riemannian Manifolds* (GTM 176). GTM 218 is the
prerequisite volume: charts, smooth maps, tangent vectors, submersions, vector
bundles, Lie groups and vector fields — the groundwork the Riemannian material
rests on.

## Provenance

The Lean was **not written here**. It was imported from
<https://github.com/frenzymath/ALLBOOKS/tree/main/SmoothManifoldsLee> at commit
`cdd0f105`, and the blueprint is generated from a structured extraction of the
book covering **Chapters 1–8 only** (599 items across 63 sections).

**Read `UPSTREAM_LEAN_AUDIT.md` before trusting anything here.** In short: the
upstream formalization does not build as published and is roughly 20%
unfinished. Its default `lake build` compiles nothing and exits 0, which makes
it look complete when it is not.

## Layout

- `LeeSmoothLib/Ch<NN>/Sec<NN>_<MM>/<Item>.lean` — one module per book item, so
  each blueprint node maps to exactly one Lean module. 550 modules.
- `blueprint/src/` — the LaTeX blueprint. `content.tex` is the root and inputs
  one `chapterN.tex` file for each published chapter (1–8). `\lean{...}` names
  the backing declaration, `\leanok` marks checked Lean, `\mathlibok` marks a
  mathlib leaf.
- `blueprint/src/macros.tex` — deliberately parallel to the LeeRiemannian macros
  so shared notation renders identically across the two Lee projects.
- `UPSTREAM_LEAN_AUDIT.md` — what is wrong upstream, with evidence.

## What was imported, and what was left out

Of the upstream's 618 item modules, **67 were excluded because they do not
compile** (31 fail directly with 106 errors; 36 more depend on those). The
remaining **550 build clean** (`lake build` → exit 0, 0 errors, 550/550 oleans).
The excluded modules are listed in `UPSTREAM_LEAN_AUDIT.md`.

Of the 550 that build, **280 declarations still use `sorry`**. Per project
decision the blueprint carries only items whose Lean is verified sorry-free, so
sorried items are **omitted from the blueprint rather than marked `\notready`**.
That means:

> **The blueprint is not a faithful table of contents for Chapters 1–8.** It is
> the subset that is actually proved. Absence of a node does **not** mean the
> book lacks the result — it usually means the result is unproved upstream.

## How node status is decided

Not by reading the source, which is misleading here — `recall X` looks like a
mathlib citation but can name a local declaration proved by `sorry` (see audit
defect 2). Status comes from the Lean kernel:

- every module is compiled (`globs` in `lakefile.lean`),
- `collectAxioms` is run over each item's principal declaration,
- `\leanok` is set only when that declaration does **not** depend on `sorryAx`,
- `\mathlibok` is set when the principal declaration is mathlib-owned.

Where a module could not be included in the axiom pass (see below), a
conservative fallback applies: any `sorry` in the module or anywhere in its
transitive import cone disqualifies it. That under-credits rather than
over-credits.

## Build notes

1. **The root module imports no item module.** Two upstream modules declare the
   same name, so the library cannot be imported as a whole (audit defect 3).
   Modules are compiled via `globs := #[.andSubmodules \`LeeSmoothLib]` instead.
   **Do not remove that glob**: without it `lake build` verifies nothing.
2. **Library name is `LeeSmoothLib`**, renamed from upstream's
   `SmoothManifoldsLee` (a module path only — never a Lean namespace — so the
   rename was mechanical). Upstream `Chap07/` became `Ch07/` to match `LeeLib`.

## Build

```
lake build
```

Requires mathlib at the repository-wide SHA pinned in `lakefile.lean` and
toolchain v4.30.0. Expect about 280 `declaration uses 'sorry'` warnings;
they are real, and they are the point.

## Overlap with LeeRiemannian

`LeeRiemannian/LeeLib/AppendixA/` already formalizes smooth-manifold groundwork
it needed early — the submersion local normal form (`LocalSection`,
`SliceChart`), local frame and subbundle criteria — which is squarely GTM 218
Chapters 4, 5 and 10 territory. That duplication remains unresolved; the two
source-based projects are kept independent rather than forcing one book's
organization onto the other.
