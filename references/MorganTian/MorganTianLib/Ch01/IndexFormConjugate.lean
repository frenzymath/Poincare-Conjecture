import MorganTianLib.Ch01.IndexFormNegative
import MorganTianLib.Ch01.ConjugateUnit

/-!
# Poincaré Ch. 1 — a conjugate point on the manifold makes the index form indefinite

`IndexFormNegative` proved, over an abstract inner-product space, that an interior
zero of a nontrivial solution of the Jacobi ODE forces the index form to take a
strictly negative value.  This file transports that statement to the **manifold**,
against Morgan–Tian's own hypothesis `IsConjugatePointAt` (`def:conjugate-point`).

The transport is the parallel-orthonormal-frame reduction of `FrameRadialBridge`:
along a geodesic `γ`, a parallel `g`-orthonormal frame `e` identifies each tangent
space `T_{γ t}M` isometrically with the fixed coefficient space `𝔼` (`frameVec`),
carries `∇_X` to `d/dt`, and carries the Jacobi operator `ℛ(·, γ′)γ′` to the
continuous self-adjoint `frameCurvOp` (`isJacobiSolOn_frameVec`,
`frameCurvOp_symm`, `continuousOn_frameCurvOp`).  So the index form of the
geodesic *is* the abstract index form of `frameCurvOp`, and

> **a conjugate point at an interior time forces the index form of `γ` on `[0, 1]`
> to be negative on some piecewise-`C¹` field vanishing at both endpoints.**

One wrinkle is dealt with here.  `IsConjugatePointAt g γ t₀` supplies a Jacobi
field only on `[0, t₀]`, whereas `isJacobiSolOn_frameVec` — like every frame lemma
— needs its data on a strictly larger interval `[a, b]`, `a < 0`, `t₀ < b` (the
frame coefficients are differentiated at interior times).  We bridge that by
*re-solving*: `exists_isJacobiFieldAlongOn_mem` produces a Jacobi field on all of
`[a, b]` with the **interior** data `(J 0, ∇J 0)` of the given one at `0`, and
`IsJacobiFieldAlongOn.eqOn_of_initial` identifies it with the given field on
`[0, t₀]` — so it still vanishes at `0` and at `t₀`, and is still nontrivial.
(Compare the memory note on interior-data Jacobi fields: one pins the field at an
interior time and re-solves; one does *not* argue by continuity.)

What remains for `prop:minimal-geodesic-no-conjugate` is the complementary half —
`I ≥ 0` for a **minimizing** geodesic — which genuinely needs the second variation
of energy, and is not proved here.  See the status note in the blueprint.

Blueprint: `claim:second-variation-minimal-geodesic`, `prop:minimal-geodesic-no-conjugate`,
`def:conjugate-point`.
-/

open Set Riemannian Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ### The coefficient vector of a vanishing field vanishes -/

/-- **Math.** The frame coefficient vector of a field that vanishes at `t` vanishes
at `t`, since each coefficient is `⟨V t, Eᵢ(t)⟩_g`.  (Converse of
`eq_zero_of_frameVec_eq_zero`; both directions are needed below.) -/
theorem frameVec_eq_zero_of_eq_zero {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {V : ℝ → E} {t : ℝ}
    (hV : V t = 0) : frameVec (I := I) g γ e V t = 0 := by
  classical
  have hcoeff : ∀ i, frameCoeff (I := I) g γ e V i t = 0 := by
    intro i
    have hz : (V t : TangentSpace I (γ t)) = 0 := hV
    show g.metricInner (γ t) (V t : TangentSpace I (γ t)) (e i t) = 0
    rw [hz]
    exact g.metricInner_zero_left (γ t) _
  simp [frameVec, hcoeff]

/-! ### The main theorem -/

/-- **Math.** **A conjugate point at an interior time makes the index form of the
geodesic indefinite.**

Let `γ` be a geodesic defined on `[a, b] ⊇ [0, 1]` with a little room at both ends
(`a < 0`, `1 < b`), and suppose `γ t₀` is **conjugate to `γ 0` along `γ`** for some
interior time `t₀ ∈ (0, 1)`.  Then there is a parallel `g`-orthonormal frame `e`
along `γ` and a **piecewise-`C¹` field `W` (read in that frame) vanishing at both
endpoints of `[0, 1]`** whose index form is **strictly negative**.

The conclusion exposes the frame `e` (with its parallelism and orthonormality), so
that a consumer can state the complementary inequality against the *same* frame;
and it records `W` together with `DW`, certifying that `DW` really is the
derivative of `W` on `[0, t₀]` and on `(t₀, 1]` — in a parallel frame `∇_X` *is*
`d/dt`, so this says `DW` is the covariant derivative of `W`, with the jump at
`t₀` that the corner of the truncated Jacobi field forces.  Without these clauses
the statement would not be usable by the second-variation half.

Combined with the (still unformalized) second-variation half — a *minimizing*
geodesic has nonnegative index form — this is exactly
`prop:minimal-geodesic-no-conjugate`: a minimizing geodesic has no interior
conjugate point.

Blueprint: `claim:second-variation-minimal-geodesic`, `def:conjugate-point`. -/
theorem exists_indexForm_neg_of_isConjugatePointAt
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b t₀ : ℝ}
    (ha : a < 0) (hb : 1 < b) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hconj : IsConjugatePointAt (I := I) g γ t₀) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (W DW : ℝ → 𝔼),
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b) ∧
      (∀ t ∈ Icc a b, ∀ i j,
        g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0) ∧
      W 0 = 0 ∧ W 1 = 0 ∧
      ContinuousOn W (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) t₀, HasDerivWithinAt W (DW t) (Icc 0 t₀) t) ∧
      (∀ t ∈ Ioc t₀ (1 : ℝ), HasDerivWithinAt W (DW t) (Icc t₀ 1) t) ∧
      indexForm (frameCurvOp (I := I) g γ e) 0 1 W DW W DW < 0 := by
  classical
  have hab : a < b := ha.trans (by linarith)
  have ht₀b : t₀ < b := ht₁.trans hb
  have h0ab : (0 : ℝ) ∈ Icc a b := ⟨ha.le, by linarith⟩
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Icc a b := Icc_subset_Icc ha.le hb.le
  have hIcc0t : Icc (0 : ℝ) t₀ ⊆ Icc a b := Icc_subset_Icc ha.le ht₀b.le
  -- ### a parallel `g`-orthonormal frame along `γ`
  obtain ⟨e, hPar, horth⟩ := exists_orthonormalParallelFrameAlong (I := I) hab hgeo hγc
  refine ⟨e, ?_⟩
  set R : ℝ → 𝔼 →L[ℝ] 𝔼 := frameCurvOp (I := I) g γ e with hR
  have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) :=
    (continuousOn_frameCurvOp (I := I) hPar hgeo hγc).mono hIcc01
  have hRsymm : ∀ t, ∀ x x' : 𝔼, ⟪R t x, x'⟫ = ⟪x, R t x'⟫ :=
    fun t x x' => frameCurvOp_symm (I := I) g γ e t x x'
  -- ### the conjugate-point Jacobi field, and its re-solution on the large interval
  obtain ⟨J, DJ, hJac, ⟨s, hs, hJs⟩, hJ0, hJt₀⟩ := hconj
  obtain ⟨J', DJ', hJac', hJ'0, hDJ'0⟩ :=
    exists_isJacobiFieldAlongOn_mem (I := I) hab hgeo hγc h0ab (J 0) (DJ 0)
  -- on `[0, t₀]` the re-solved field agrees with the given one (same interior data at `0`)
  have hgeo₀ : IsGeodesicOn (I := I) g γ (Icc 0 t₀) := hgeo.mono hIcc0t
  have hγc₀ : ∀ t ∈ Icc (0 : ℝ) t₀, ContinuousAt γ t := fun t ht => hγc t (hIcc0t ht)
  have hJac'₀ : IsJacobiFieldAlongOn (I := I) g γ J' DJ' 0 t₀ :=
    hJac'.mono ha.le ht₀ ht₀b.le
  have hagree : ∀ t ∈ Icc (0 : ℝ) t₀, J t = J' t ∧ DJ t = DJ' t :=
    IsJacobiFieldAlongOn.eqOn_of_initial (I := I) ht₀ hgeo₀ hγc₀ hJac hJac'₀
      (by rw [hJ'0]) (by rw [hDJ'0])
  have hJ'0' : J' 0 = 0 := by rw [hJ'0, hJ0]
  have hJ't₀ : J' t₀ = 0 := by
    rw [← (hagree t₀ ⟨ht₀.le, le_rfl⟩).1, hJt₀]
  have hJ's : J' s ≠ 0 := by
    rw [← (hagree s hs).1]; exact hJs
  -- ### read in the frame: an honest solution of the abstract Jacobi ODE on `[0, t₀]`
  set y : ℝ → 𝔼 := frameVec (I := I) g γ e J' with hy
  set v : ℝ → 𝔼 := frameVec (I := I) g γ e DJ' with hv
  have hsol : IsJacobiSolOn R 0 t₀ y v :=
    isJacobiSolOn_frameVec (I := I) hJac' hPar hgeo hγc horth ha ht₀b
  have hy0 : y 0 = 0 := frameVec_eq_zero_of_eq_zero (I := I) hJ'0'
  have hyt₀ : y t₀ = 0 := frameVec_eq_zero_of_eq_zero (I := I) hJ't₀
  have hyne : ∃ t ∈ Icc (0 : ℝ) t₀, y t ≠ 0 := by
    refine ⟨s, hs, fun hcon => hJ's ?_⟩
    exact eq_zero_of_frameVec_eq_zero (I := I) (horth s (hIcc0t hs)) hcon
  -- ### the abstract negative-index construction
  obtain ⟨W, DW, hW0, hW1, hWc, hWd₁, hWd₂, hneg⟩ :=
    exists_indexForm_neg_of_jacobi_vanishing (F := 𝔼) ht₀ ht₁ hRcont hRsymm hsol hy0 hyt₀ hyne
  exact ⟨W, DW, hPar, horth, hW0, hW1, hWc, hWd₁, hWd₂, hneg⟩

end MorganTianLib
