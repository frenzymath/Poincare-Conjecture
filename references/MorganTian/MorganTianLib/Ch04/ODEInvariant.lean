import MorganTianLib.Ch04.ConvexInvariant
import MorganTianLib.Ch04.ConvexProjection
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Morgan--Tian Ch. 4 - ODE invariance of a convex carrier

This file supplies the finite-dimensional viability argument used by the
tensor maximum principle.  The proof is phrased with the positive tangent
cone from `ConvexInvariant`: a nearest-point comparison gives a one-sided
upper slope for the squared distance, and Grönwall then forces that distance
to vanish.  No ODE-existence or invariance statement is hidden in a wrapper;
existence hypotheses occur explicitly in the criterion theorem at the end.
-/

open Filter Set
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ### The normal-component estimate -/

/--
The normal component of a globally Lipschitz vector field is controlled by the
distance to a closed convex carrier.  Here `p` is the canonical nearest point
chosen by `convexProjection`; the tangent-cone condition supplies the
nonpositive contribution of `ψ p`, while Lipschitz continuity controls the
remainder.
-/
theorem normal_component_le_lipschitz_mul_dist_sq
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ)
    (hpres : vectorFieldPreservesConvexSet Z ψ) (v : E) :
    ⟪v - convexProjection Z hZne hZclosed hZconv v,
      ψ v⟫_ℝ ≤ (L : ℝ) * (Metric.infDist v Z) ^ 2 := by
  let p := convexProjection Z hZne hZclosed hZconv v
  let d := v - p
  have hp : p ∈ Z := by
    exact convexProjection_mem Z hZne hZclosed hZconv v
  have hsupport : ⟪d, ψ p⟫_ℝ ≤ 0 := by
    let φ : E →L[ℝ] ℝ := innerSL ℝ d
    have hφ : φ (ψ p) ≤ 0 :=
      support_functional_nonpos_of_vectorFieldPreservesConvexSet
        (Z := Z) (ψ := ψ) hpres hp φ (by
          intro y hy
          have hgeom := convexProjection_inner_nonpos Z hZne hZclosed hZconv v y hy
          have hgeom' : ⟪d, y⟫_ℝ ≤ ⟪d, p⟫_ℝ := by
            rw [inner_sub_right] at hgeom
            linarith
          simpa [φ, innerSL_apply_apply] using hgeom')
    change ⟪d, ψ p⟫_ℝ ≤ 0
    change ⟪d, ψ p⟫_ℝ ≤ 0 at hφ
    exact hφ
  have hψdist : ‖ψ v - ψ p‖ ≤ (L : ℝ) * ‖d‖ := by
    have h := hψ.dist_le_mul v p
    simpa [dist_eq_norm, d, p] using h
  have hmain : ⟪d, ψ v⟫_ℝ ≤ (L : ℝ) * ‖d‖ ^ 2 := by
    have hsplit : ⟪d, ψ v⟫_ℝ = ⟪d, ψ v - ψ p⟫_ℝ + ⟪d, ψ p⟫_ℝ := by
      rw [inner_sub_right]
      ring
    calc
      ⟪d, ψ v⟫_ℝ = ⟪d, ψ v - ψ p⟫_ℝ + ⟪d, ψ p⟫_ℝ := hsplit
      _ ≤ ⟪d, ψ v - ψ p⟫_ℝ := by linarith
      _ ≤ ‖d‖ * ‖ψ v - ψ p‖ := real_inner_le_norm _ _
      _ ≤ ‖d‖ * ((L : ℝ) * ‖d‖) :=
        mul_le_mul_of_nonneg_left hψdist (norm_nonneg _)
      _ = (L : ℝ) * ‖d‖ ^ 2 := by ring
  have hdist : ‖d‖ = Metric.infDist v Z := by
    dsimp [d, p]
    rw [← dist_eq_norm,
      convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v]
  simpa [d, hdist] using hmain

/-! ### Squared-distance slope comparison -/

/--
For a curve with a right derivative, the squared distance to a closed convex
set has the upper right-slope bound dictated by the preceding normal estimate.
The statement is deliberately formulated with `liminf`/`Frequently`, which is
the interface consumed by Mathlib's Grönwall theorem and does not assert an
unavailable derivative for the metric projection.
-/
theorem squared_infDist_liminf_right_slope_le
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ)
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    {γ : ℝ → E} {a b t : ℝ} (ht : t ∈ Ico a b)
    (hγ : HasDerivWithinAt γ (ψ (γ t)) (Ici t) t) :
    ∀ r : ℝ, 2 * (L : ℝ) * (Metric.infDist (γ t) Z) ^ 2 < r →
      ∃ᶠ z in 𝓝[>] t,
        slope (fun s => (Metric.infDist (γ s) Z) ^ 2) t z < r := by
  let p := convexProjection Z hZne hZclosed hZconv (γ t)
  let F : ℝ → ℝ := fun s => ‖γ s - p‖ ^ 2
  have hp : p ∈ Z := by
    exact convexProjection_mem Z hZne hZclosed hZconv (γ t)
  have hγF : HasDerivWithinAt (fun s => γ s - p) (ψ (γ t)) (Ici t) t :=
    hγ.sub_const p
  have hF : HasDerivWithinAt F
      (2 * ⟪γ t - p, ψ (γ t)⟫_ℝ) (Ici t) t := by
    simpa [F] using hγF.norm_sq
  have hnormal := normal_component_le_lipschitz_mul_dist_sq
    hZne hZclosed hZconv hψ hpres (γ t)
  have hderiv : 2 * ⟪γ t - p, ψ (γ t)⟫_ℝ ≤
      2 * (L : ℝ) * (Metric.infDist (γ t) Z) ^ 2 := by
    have hnormal' : ⟪γ t - p, ψ (γ t)⟫_ℝ ≤
        (L : ℝ) * (Metric.infDist (γ t) Z) ^ 2 := by
      simpa [p] using hnormal
    linarith
  intro r hr
  have hFr : 2 * ⟪γ t - p, ψ (γ t)⟫_ℝ < r := lt_of_le_of_lt hderiv hr
  have hfreq : ∃ᶠ z in 𝓝[>] t, slope F t z < r :=
    hF.liminf_right_slope_le hFr
  have hqle : ∀ z : ℝ,
      (Metric.infDist (γ z) Z) ^ 2 ≤ ‖γ z - p‖ ^ 2 := by
    intro z
    have hd := Metric.infDist_le_dist_of_mem (x := γ z) (s := Z) hp
    rw [dist_eq_norm] at hd
    have hi : 0 ≤ Metric.infDist (γ z) Z := Metric.infDist_nonneg
    have hn : 0 ≤ ‖γ z - p‖ := norm_nonneg _
    nlinarith
  have hqt : (Metric.infDist (γ t) Z) ^ 2 = F t := by
    have hdist := convexProjection_dist_eq_infDist Z hZne hZclosed hZconv (γ t)
    have hnorm : ‖γ t - p‖ = Metric.infDist (γ t) Z := by
      simpa [p, dist_eq_norm] using hdist
    simp [F, hnorm]
  have hfreq' : ∃ᶠ z in 𝓝[>] t, slope F t z < r ∧ z ∈ Ioi t :=
    hfreq.and_eventually (show ∀ᶠ z in 𝓝[>] t, z ∈ Ioi t from self_mem_nhdsWithin)
  apply hfreq'.mono
  intro z hz
  have hzgt : t < z := hz.2
  have hzsl : slope F t z < r := hz.1
  have hqz := hqle z
  have hdiff : (Metric.infDist (γ z) Z) ^ 2 -
      (Metric.infDist (γ t) Z) ^ 2 ≤ F z - F t := by
    rw [hqt]
    linarith
  have hmul : (z - t)⁻¹ *
      ((Metric.infDist (γ z) Z) ^ 2 - (Metric.infDist (γ t) Z) ^ 2) ≤
      (z - t)⁻¹ * (F z - F t) := by
    exact mul_le_mul_of_nonneg_left hdiff
      (inv_nonneg.mpr (le_of_lt (sub_pos.mpr hzgt)))
  have hslopes : slope (fun s => (Metric.infDist (γ s) Z) ^ 2) t z ≤
      slope F t z := by
    simpa [slope_def_field, div_eq_inv_mul] using hmul
  exact hslopes.trans_lt hzsl

/-! ### The Nagumo implication -/

/--
An integral curve of a globally Lipschitz vector field that is tangent to a
closed convex carrier cannot leave that carrier.  The interval is explicit so
the theorem applies equally to local forward solutions and to restrictions of
global ones.
-/
theorem integralCurve_mem_of_vectorFieldPreservesConvexSet
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ)
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : IsIntegralCurveOn γ (fun _ : ℝ => ψ) (Icc a b))
    (hinit : γ a ∈ Z) :
    ∀ t ∈ Icc a b, γ t ∈ Z := by
  let q : ℝ → ℝ := fun s => (Metric.infDist (γ s) Z) ^ 2
  have hγcont : ContinuousOn γ (Icc a b) := hγ.continuousOn
  have hqcont : ContinuousOn q (Icc a b) := by
    dsimp [q]
    exact ((Metric.continuous_infDist_pt Z).comp_continuousOn hγcont).pow 2
  have hqa : q a = 0 := by
    simp [q, Metric.infDist_zero_of_mem hinit]
  have hslopes : ∀ t ∈ Ico a b, ∀ r : ℝ,
      2 * (L : ℝ) * q t < r →
        ∃ᶠ z in 𝓝[>] t, slope q t z < r := by
    intro t ht r hr
    have hγt : HasDerivWithinAt γ (ψ (γ t)) (Ici t) t := by
      exact (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    simpa [q] using
      (squared_infDist_liminf_right_slope_le hZne hZclosed hZconv hψ hpres ht hγt r
        (by simpa [q] using hr))
  have hbound : ∀ t ∈ Ico a b, 2 * (L : ℝ) * q t ≤
      (2 * (L : ℝ)) * q t + 0 := by
    intro t ht
    ring_nf
    exact le_rfl
  have hqgronwall := le_gronwallBound_of_liminf_deriv_right_le
    (f := q) (f' := fun t => 2 * (L : ℝ) * q t)
    (δ := 0) (K := 2 * (L : ℝ)) (ε := 0)
    hqcont hslopes (by simpa [hqa]) hbound
  intro t ht
  have hqnonneg : 0 ≤ q t := by
    exact sq_nonneg _
  have hqzero : q t = 0 := le_antisymm (by
    simpa [gronwallBound_ε0_δ0] using hqgronwall t ht) hqnonneg
  have hdistzero : Metric.infDist (γ t) Z = 0 := by
    dsimp [q] at hqzero
    nlinarith [Metric.infDist_nonneg (x := γ t) (s := Z)]
  exact (hZclosed.mem_iff_infDist_zero hZne).mpr hdistzero

/-! ### Integral-curve criterion with explicit local existence -/

/--
For a nonempty closed convex carrier and a globally Lipschitz field, the
integral-curve criterion is an iff once the forward local-existence package is
provided explicitly.  The existence hypothesis is needed only for the
integral-curve-to-tangent-cone direction supplied by `ConvexInvariant`.
-/
theorem integralCurvePreservesSet_iff_vectorFieldPreservesConvexSet_of_lipschitz
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ)
    (hexists : ∀ z ∈ Z, forwardIntegralCurveExistsAt ψ z) :
    integralCurvePreservesSet Z ψ ↔ vectorFieldPreservesConvexSet Z ψ := by
  constructor
  · intro hcurves
    exact vectorFieldPreservesConvexSet_of_integralCurvePreservesSet hcurves hexists
  · intro hpres γ s hs hγ t₀ ht₀ hγmem t ht hle
    by_cases hteq : t = t₀
    · simpa [hteq] using hγmem
    have hlt : t₀ < t := lt_of_le_of_ne hle (Ne.symm hteq)
    have hseg : Icc t₀ t ⊆ s := by
      intro u hu
      exact hs.out ht₀ ht hu
    have hγseg : IsIntegralCurveOn γ (fun _ : ℝ => ψ) (Icc t₀ t) :=
      hγ.mono hseg
    have hmemseg := integralCurve_mem_of_vectorFieldPreservesConvexSet
      hZne hZclosed hZconv hψ hpres hlt.le hγseg hγmem
    exact hmemseg t ⟨hle, le_rfl⟩

end MorganTianLib
