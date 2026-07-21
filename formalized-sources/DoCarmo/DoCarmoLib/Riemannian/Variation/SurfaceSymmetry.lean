import DoCarmoLib.Riemannian.Jacobi.SurfaceCurvatureCommutation
import DoCarmoLib.Riemannian.Geodesic.SymmetryLemma

/-!
# The symmetry lemma in operator form: `D/∂s ∂f/∂t = D/∂t ∂f/∂s`

do Carmo, *Riemannian Geometry*, Ch. 3, Lemma 3.4 (the symmetry of the Riemannian
connection, read on a parametrized surface), in the form Ch. 9 §2 needs it.

The proof of the first variation formula (`prop:dc-ch9-2-4`) differentiates
`E(s) = ∫ ⟨∂f/∂t, ∂f/∂t⟩ dt` under the integral sign and, at the decisive step,
replaces `D/∂s ∂f/∂t` by `D/∂t ∂f/∂s` — "using the symmetry of the Riemannian
connection".  The same exchange is the first move of the second variation formula
(`prop:dc-ch9-2-8`).

Both halves of that exchange already exist in DoCarmoLib, but they had never been
connected:

* `Geodesic.covariant_sndFDeriv_symm_of_eventually` (`Geodesic/SymmetryLemma.lean`)
  is the symmetry statement, but in **raw coordinate-expression form** — an equation
  between `D²c v w + Γ(Dc v, Dc w)(c)` and `D²c w v + Γ(Dc w, Dc v)(c)`.  It never
  mentions a covariant derivative *operator*.
* `Jacobi.surfaceCovariantDerivS` / `surfaceCovariantDerivT`
  (`Jacobi/SurfaceCurvatureCommutation.lean`) are the two operators `D/∂s`, `D/∂t`
  along a parametrized surface, but nothing there says they commute on the velocity
  fields.

This file supplies the missing link, and it is exactly one instantiation wide: apply
the symmetry statement with `v = (1,0)`, `w = (0,1)` and recognize the two sides as
the two operators applied to `∂f/∂t`, resp. `∂f/∂s`.  The two mixed partials
`∂/∂σ(∂f/∂τ) = D²f(1,0)(0,1)` and `∂/∂τ(∂f/∂σ) = D²f(0,1)(1,0)` supply the `deriv`
terms, and the `Γ`-terms match because `chartChristoffelContraction` is symmetric in
its two vector slots (`chartChristoffelContraction_symm`) — which is precisely do
Carmo's hypothesis that the connection is *symmetric*.

Note that the curvature does **not** appear here.  `surface_covariant_commutator`
(the Ricci identity) compares `D/∂t D/∂s V` with `D/∂s D/∂t V` for an *arbitrary*
field `V` and picks up `R(∂f/∂s, ∂f/∂t)V`; the present lemma compares `D/∂s` and
`D/∂t` applied to the *velocity fields of `f` itself*, where the two sides differ
only by the mixed partial and the connection is symmetric, so the difference
vanishes identically.  The two statements are independent: this one is Ch. 3
Lemma 3.4, that one is Ch. 4 `lem:dc-ch4-4-1`.

## Scope

Chart level, like both of its inputs: `f : ℝ × ℝ → E` is the reading of a surface in
the fixed chart at `α`.  Unlike `surface_covariant_commutator_of_eventually`, no
`[I.Boundaryless]` and no `hmem : f (s₀,t₀) ∈ interior (extChartAt I α).target` is
needed — the symmetry statement it rests on needs neither.

Reference: do Carmo, *Riemannian Geometry*, Ch. 3, Lemma 3.4; used at Ch. 9, §2 in
the proofs of `prop:dc-ch9-2-4` and `prop:dc-ch9-2-8`.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 3, Lemma 3.4 (**the symmetry lemma**, operator form).  For
a `C²` parametrized surface `f` read in the chart at `α`, the two covariant
derivatives along `f` exchange on the velocity fields of `f`:
$$\frac{D}{\partial s}\frac{\partial f}{\partial t}
  = \frac{D}{\partial t}\frac{\partial f}{\partial s}.$$

Here `∂f/∂t = fun p => Df p (0,1)` and `∂f/∂s = fun p => Df p (1,0)`.

This is the step "using the symmetry of the Riemannian connection" in do Carmo's
proof of the first variation formula (`prop:dc-ch9-2-4`), and the opening move of the
second variation formula (`prop:dc-ch9-2-8`).

The proof is `Geodesic.covariant_sndFDeriv_symm_of_eventually` at `v = (1,0)`,
`w = (0,1)`: Schwarz gives `D²f(1,0)(0,1) = D²f(0,1)(1,0)` for the derivative terms
and `chartChristoffelContraction_symm` — the symmetry of the connection — matches the
two Christoffel terms.  No curvature appears; contrast
`surface_covariant_commutator_of_eventually`, which exchanges `D/∂s` and `D/∂t` on an
arbitrary field and does pick up `R`. -/
theorem surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst
    (g : RiemannianMetric I M) (α : M) (f : ℝ × ℝ → E)
    (Df : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E)) (D2f : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E)
    (s₀ t₀ : ℝ)
    (hf : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt f (Df p) p)
    (hf2 : HasFDerivAt Df D2f (s₀, t₀)) :
    surfaceCovariantDerivS (I := I) g α f (fun p => Df p (0, 1)) (s₀, t₀)
      = surfaceCovariantDerivT (I := I) g α f (fun p => Df p (1, 0)) (s₀, t₀) := by
  have hfs : HasFDerivAt f (Df (s₀, t₀)) (s₀, t₀) := hf.self_of_nhds
  -- the two velocity fields of `f` at the base point
  have hfs0 : deriv (fun σ => f (σ, t₀)) s₀ = Df (s₀, t₀) (1, 0) :=
    (hasDerivAt_comp_fst hfs).deriv
  have hft0 : deriv (fun τ => f (s₀, τ)) t₀ = Df (s₀, t₀) (0, 1) :=
    (hasDerivAt_comp_snd hfs).deriv
  -- the mixed partial `∂/∂σ (∂f/∂τ) = D²f(1,0)(0,1)`
  have hDFs : HasDerivAt (fun σ => Df (σ, t₀)) (D2f (1, 0)) s₀ := hasDerivAt_comp_fst hf2
  have hmixed_s : deriv (fun σ => Df (σ, t₀) (0, 1)) s₀ = D2f (1, 0) (0, 1) :=
    (HasFDerivAt.comp_hasDerivAt (x := s₀)
      (hl := (ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ)).hasFDerivAt)
      (hf := hDFs)).deriv
  -- the mixed partial `∂/∂τ (∂f/∂σ) = D²f(0,1)(1,0)`
  have hDFt : HasDerivAt (fun τ => Df (s₀, τ)) (D2f (0, 1)) t₀ := hasDerivAt_comp_snd hf2
  have hmixed_t : deriv (fun τ => Df (s₀, τ) (1, 0)) t₀ = D2f (0, 1) (1, 0) :=
    (HasFDerivAt.comp_hasDerivAt (x := t₀)
      (hl := (ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ)).hasFDerivAt)
      (hf := hDFt)).deriv
  simp only [surfaceCovariantDerivS, surfaceCovariantDerivT, covariantDerivCoord_def]
  rw [hmixed_s, hfs0, hmixed_t, hft0]
  exact Geodesic.covariant_sndFDeriv_symm_of_eventually g α hf hf2 (1, 0) (0, 1)

/-- **Math.** do Carmo Ch. 3, Lemma 3.4, under the globally-`C¹` hypothesis on `f`
(the `∀ p` specialization of
`surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst`), matching the shape of
`surface_covariant_commutator`. -/
theorem surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst_of_forall
    (g : RiemannianMetric I M) (α : M) (f : ℝ × ℝ → E)
    (Df : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E)) (D2f : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E)
    (s₀ t₀ : ℝ)
    (hf : ∀ p, HasFDerivAt f (Df p) p)
    (hf2 : HasFDerivAt Df D2f (s₀, t₀)) :
    surfaceCovariantDerivS (I := I) g α f (fun p => Df p (0, 1)) (s₀, t₀)
      = surfaceCovariantDerivT (I := I) g α f (fun p => Df p (1, 0)) (s₀, t₀) :=
  surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst (I := I) g α f Df D2f s₀ t₀
    (Filter.Eventually.of_forall hf) hf2

end Riemannian.Variation
