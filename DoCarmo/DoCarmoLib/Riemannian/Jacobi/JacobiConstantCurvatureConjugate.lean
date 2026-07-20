import DoCarmoLib.Riemannian.Jacobi.JacobiConstantCurvatureSolution
import DoCarmoLib.Riemannian.Jacobi.ParallelFieldAlong
import DoCarmoLib.Riemannian.Jacobi.JacobiVelocityField

/-!
# do Carmo Ch. 5, §3, Example 3.3 — conjugate points on constant-curvature spaces

do Carmo's Example 3.3 asserts that on the sphere `S^n` (constant sectional curvature
`1`) the antipodal point `γ(π)` is conjugate to `γ(0)` with multiplicity `n − 1`.  We
formalize the intrinsic statement of which `S^n` is the `K₀ = 1` instance: on **any**
manifold `M` of constant sectional curvature `K₀ > 0`, along a unit-speed geodesic
`γ`, the point `γ(π/√K₀)` is conjugate to `γ(0)` with multiplicity `n − 1`.

The classical argument (do Carmo Example 2.3) writes the Jacobi fields with `J(0) = 0`
normal to `γ'` explicitly as `J(t) = (sin(t√K₀)/√K₀) w(t)` with `w` a **parallel**
unit-normal field along `γ` — the field built at the manifold level in
`ParallelFieldAlong.lean`.  Such a field vanishes again exactly at `t = π/√K₀`, so
every normal initial velocity lies in the kernel of the endpoint map
`Θ : J'(0) ↦ J(π/√K₀)`.  The tangential direction `γ'(0)` does not
(`Θ(γ'(0)) = π/√K₀ · γ'(π/√K₀) ≠ 0`, `rem:dc-ch5-2-2`), so `ker Θ` is exactly the
hyperplane `γ'(0)^⊥` and the multiplicity is `dim γ'(0)^⊥ = n − 1`.

## Contents

* `isParallelFieldAlongOn_velocity` — the geodesic velocity `γ'` is a parallel field.
* `isJacobiFieldAlongOn_constCurvatureSol_pos` — the manifold constant-curvature
  Jacobi field `(sin(t√K₀)/√K₀) w(t)` for a parallel unit-normal field `w`.
* `conjugateMultiplicity_constCurvature_pos_eq` — **the multiplicity is `n − 1`**
  (do Carmo Example 3.3, multiplicity clause).
* `isConjugatePointAt_constCurvature_pos` — when `n ≥ 2`, `γ(π/√K₀)` is conjugate to
  `γ(0)` (do Carmo Example 3.3, conjugacy clause).

Blueprint: `ex:dc-ch5-3-3`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Example 3.3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The geodesic velocity is a parallel field -/

/-- **Math.** **do Carmo Ch. 5, Remark 2.2 (covariant-derivative clause).**  The
geodesic velocity `γ'(t) = mfderiv γ t 1` is a parallel field along `γ`
(`Dγ'/dt = 0`).  This is the first Jacobi equation of the velocity Jacobi field
`(γ', 0)` (`isJacobiFieldAlongOn_velocity`), whose covariant derivative slot is `0`. -/
theorem isParallelFieldAlongOn_velocity (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    IsParallelFieldAlongOn (I := I) g γ (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hJF⟩ :=
    isJacobiFieldAlongOn_velocity g hab hgeo hγc t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
  intro t ht
  have h1 := hJF.hasDerivWithinAt_fst t ht
  rw [show chartVectorRep (I := I) γ α (fun _ => (0:E)) t = 0 from by
    simp [chartVectorRep_apply], zero_sub] at h1
  exact h1

/-! ### The manifold constant-curvature Jacobi field -/

/-- **Math.** **do Carmo Ch. 5, Example 2.3 (manifold form, `K₀ > 0`).**  On a manifold
of constant sectional curvature `K₀ > 0`, given a **parallel** field `w` along the
unit-speed geodesic `γ` that is **normal** to `γ'` (`hperp`), the field
`J(t) = (sin(t√K₀)/√K₀) w(t)` is a Jacobi field along `γ`, with covariant derivative
`DJ(t) = cos(t√K₀) w(t)`.  Chart-locally this is
`isJacobiFieldOn_of_constantCurvature`: unit speed is `chartMetricInner_deriv_extChartAt`
(`speedSq = 1`), normality transfers by `metricInner_eq_chartMetricInner_rep`, and the
chart reading of `w` is parallel by localization (`isParallelSolOn_of_mem_source`). -/
theorem isJacobiFieldAlongOn_constCurvatureSol_pos (g : RiemannianMetric I M) {K₀ : ℝ}
    (hKpos : 0 < K₀) (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc a b, Geodesic.speedSq (I := I) g γ τ = 1)
    (w : ℝ → E) (hwPar : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hperp : ∀ τ ∈ Icc a b,
      g.metricInner (γ τ) (w τ : TangentSpace I (γ τ)) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) = 0) :
    IsJacobiFieldAlongOn (I := I) g γ
      (fun τ => (Real.sin (Real.sqrt K₀ * τ) / Real.sqrt K₀) • w τ)
      (fun τ => Real.cos (Real.sqrt K₀ * τ) • w τ) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, _⟩ := hwPar t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
  set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu_def
  have hwloc := hwPar.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
  have hu_tgt : ∀ t ∈ Icc a' b', u t ∈ (extChartAt I α).target := fun t ht =>
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  have hunit : ∀ t ∈ Icc a' b',
      chartMetricInner (I := I) g α (u t) (deriv u t) (deriv u t) = 1 := by
    intro t ht
    rw [chartMetricInner_deriv_extChartAt (I := I)
      (hgeo.hasGeodesicEquationAt (hsub ht)) (hγc t (hsub ht)) (hsrc t ht)]
    exact hspeed t (hsub ht)
  have hperp' : ∀ t ∈ Icc a' b',
      chartMetricInner (I := I) g α (u t) (chartVectorRep (I := I) γ α w t) (deriv u t) = 0 := by
    intro t ht
    have hv := chartVectorRep_velocity (I := I) g α
      (hgeo.hasGeodesicEquationAt (hsub ht)) (hγc t (hsub ht)) (hsrc t ht)
    rw [← hv, ← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht) w
      (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1)]
    exact hperp t (hsub ht)
  have hcert := isJacobiFieldOn_of_constantCurvature (I := I) g hK α u
    (chartVectorRep (I := I) γ α w)
    (fun t => Real.sin (Real.sqrt K₀ * t) / Real.sqrt K₀)
    (fun t => Real.cos (Real.sqrt K₀ * t))
    hu_tgt hunit hperp' hwloc
    (hasDerivAt_constCurvatureSol_pos hKpos) (hasDerivAt_constCurvatureSolDeriv_pos hKpos)
  refine hcert.congr ?_ ?_ <;>
    · intro τ hτ
      simp only [chartVectorRep_apply, map_smul]

/-! ### Example 3.3 — the multiplicity is `n − 1` -/

/-- **Math.** **do Carmo Ch. 5, Example 3.3 (multiplicity clause).**  On a manifold of
constant sectional curvature `K₀ > 0`, along a unit-speed geodesic
`γ : [0, π/√K₀] → M`, the multiplicity of the conjugate point `γ(π/√K₀)` is `n − 1`.

The endpoint map `Θ : J'(0) ↦ J(π/√K₀)` kills every normal initial velocity `w ⟂ γ'(0)`:
the parallel transport `w(t)` of `w` (`exists_parallelFieldAlongOn`) stays normal
(`metricInner_const`: parallel transport is an isometry, and `γ'` is parallel), so
`J(t) = (sin(t√K₀)/√K₀) w(t)` is a Jacobi field with `J(0) = 0`, `J'(0) = w`, and
`J(π/√K₀) = (sin π /√K₀) w(π/√K₀) = 0`; uniqueness identifies it with the chosen field,
giving `Θ w = 0`.  Hence `γ'(0)^⊥ ⊆ ker Θ`, so `n − 1 = dim γ'(0)^⊥ ≤ dim ker Θ`; the
opposite bound `dim ker Θ ≤ n − 1` is the sharp bound of `rem:dc-ch5-3-2`. -/
theorem conjugateMultiplicity_constCurvature_pos_eq (g : RiemannianMetric I M) {K₀ : ℝ}
    (hKpos : 0 < K₀) (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) {γ : ℝ → M}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 (Real.pi / Real.sqrt K₀)))
    (hγc : ∀ t ∈ Icc (0:ℝ) (Real.pi / Real.sqrt K₀), ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0:ℝ) (Real.pi / Real.sqrt K₀), Geodesic.speedSq (I := I) g γ τ = 1) :
    conjugateMultiplicity (div_pos Real.pi_pos (Real.sqrt_pos.2 hKpos)) hgeo hγc
      = Module.finrank ℝ E - 1 := by
  set L : ℝ := Real.pi / Real.sqrt K₀ with hL
  have hsqrt : Real.sqrt K₀ ≠ 0 := Real.sqrt_ne_zero'.2 hKpos
  have hLpos : (0:ℝ) < L := div_pos Real.pi_pos (Real.sqrt_pos.2 hKpos)
  set v₀ : E := mfderiv 𝓘(ℝ, ℝ) I γ 0 1 with hv₀
  set vL : E := mfderiv 𝓘(ℝ, ℝ) I γ L 1 with hvL
  -- `γ` is non-constant at both ends: `⟨v, v⟩ = 1`.
  have hv₀ne : v₀ ≠ 0 := by
    have h1 : g.metricInner (γ 0) v₀ v₀ = 1 := by
      have h := hspeed 0 ⟨le_rfl, hLpos.le⟩; rwa [Geodesic.speedSq_def] at h
    intro h0
    have hz : g.metricInner (γ 0) v₀ v₀ = 0 := by
      rw [h0]; exact g.metricInner_zero_left (γ 0) _
    rw [hz] at h1; exact one_ne_zero h1.symm
  have hvLne : vL ≠ 0 := by
    have h1 : g.metricInner (γ L) vL vL = 1 := by
      have h := hspeed L ⟨hLpos.le, le_rfl⟩; rwa [Geodesic.speedSq_def] at h
    intro h0
    have hz : g.metricInner (γ L) vL vL = 0 := by
      rw [h0]; exact g.metricInner_zero_left (γ L) _
    rw [hz] at h1; exact one_ne_zero h1.symm
  -- the key inclusion `γ'(0)^⊥ ⊆ ker Θ`
  have hincl : LinearMap.ker (velocityFunctional (I := I) g (γ 0) v₀)
      ≤ LinearMap.ker (jacobiEndpointOfVel hLpos hgeo hγc) := by
    intro w hw
    rw [LinearMap.mem_ker, velocityFunctional_apply] at hw
    rw [LinearMap.mem_ker, jacobiEndpointOfVel_apply]
    -- parallel transport of `w`
    obtain ⟨wp, hwpPar, hwp0⟩ := exists_parallelFieldAlongOn (I := I) hLpos hgeo hγc w
    -- `wp` stays normal to `γ'`
    have hperp : ∀ τ ∈ Icc (0:ℝ) L,
        g.metricInner (γ τ) (wp τ : TangentSpace I (γ τ)) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) = 0 := by
      intro τ hτ
      have hconst := IsParallelFieldAlongOn.metricInner_const (I := I) hLpos.le hwpPar
        (isParallelFieldAlongOn_velocity g hLpos hgeo hγc) hgeo hγc hτ
      rw [hconst, hwp0]
      simpa [hv₀] using hw
    -- the manifold constant-curvature Jacobi field
    have hJac := isJacobiFieldAlongOn_constCurvatureSol_pos (I := I) g hKpos hK hLpos hgeo hγc
      hspeed wp hwpPar hperp
    -- identify with the chosen Jacobi field via uniqueness
    have hJ0 : (fun τ => (Real.sin (Real.sqrt K₀ * τ) / Real.sqrt K₀) • wp τ) 0 = 0 := by
      simp only [mul_zero, Real.sin_zero, zero_div, zero_smul]
    have hDJ0 : (fun τ => Real.cos (Real.sqrt K₀ * τ) • wp τ) 0 = w := by
      simp only [mul_zero, Real.cos_zero, one_smul, hwp0]
    have heq := eqOn_jacobiJ hLpos hgeo hγc (0, w) hJac hJ0 hDJ0 L (right_mem_Icc.2 hLpos.le)
    -- the field vanishes at `L = π/√K₀`
    have hsqL : Real.sqrt K₀ * L = Real.pi := by
      rw [hL]; field_simp
    have hsinL : Real.sin (Real.sqrt K₀ * L) = 0 := by
      rw [hsqL, Real.sin_pi]
    rw [← heq.1]
    simp only [hsinL, zero_div, zero_smul]
  -- the finrank sandwich
  have hle1 : Module.finrank ℝ (LinearMap.ker (velocityFunctional (I := I) g (γ 0) v₀))
      ≤ Module.finrank ℝ (LinearMap.ker (jacobiEndpointOfVel hLpos hgeo hγc)) :=
    Submodule.finrank_mono hincl
  have hperpdim : Module.finrank ℝ (LinearMap.ker (velocityFunctional (I := I) g (γ 0) v₀))
      = Module.finrank ℝ E - 1 := finrank_velocityPerp_eq (I := I) g hv₀ne
  have hupper : conjugateMultiplicity hLpos hgeo hγc ≤ Module.finrank ℝ E - 1 :=
    conjugateMultiplicity_le_finrank_sub_one g hLpos hgeo hγc hvLne
  have hcm : conjugateMultiplicity hLpos hgeo hγc
      = Module.finrank ℝ (LinearMap.ker (jacobiEndpointOfVel hLpos hgeo hγc)) := rfl
  rw [hcm] at hupper ⊢
  omega

/-- **Math.** **do Carmo Ch. 5, Example 3.3 (conjugacy clause).**  On a manifold of
dimension `n ≥ 2` and constant sectional curvature `K₀ > 0`, along a unit-speed
geodesic, the point `γ(π/√K₀)` is conjugate to `γ(0)`: the multiplicity `n − 1` is
positive. -/
theorem isConjugatePointAt_constCurvature_pos (g : RiemannianMetric I M) {K₀ : ℝ}
    (hKpos : 0 < K₀) (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) {γ : ℝ → M}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 (Real.pi / Real.sqrt K₀)))
    (hγc : ∀ t ∈ Icc (0:ℝ) (Real.pi / Real.sqrt K₀), ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0:ℝ) (Real.pi / Real.sqrt K₀), Geodesic.speedSq (I := I) g γ τ = 1)
    (hn : 2 ≤ Module.finrank ℝ E) :
    IsConjugatePointAt (I := I) g γ (Real.pi / Real.sqrt K₀) := by
  have hLpos : (0:ℝ) < Real.pi / Real.sqrt K₀ := div_pos Real.pi_pos (Real.sqrt_pos.2 hKpos)
  rw [isConjugatePointAt_iff_conjugateMultiplicity_pos hLpos hgeo hγc,
    conjugateMultiplicity_constCurvature_pos_eq g hKpos hK hgeo hγc hspeed]
  omega

end Riemannian.Jacobi

end
