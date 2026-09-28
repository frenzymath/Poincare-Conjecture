import PetersenLib.Ch06.DiameterBound

/-!
# Petersen Ch. 6, §6.3 — intrinsic Bonnet--Synge variations

`BonnetSyngeVariation.lean` evaluates the second variation of a supplied sine-weighted
parallel field.  This file removes that remaining construction hypothesis.  Starting from a
unit-speed global geodesic, it completes the velocity to a parallel orthonormal frame, chooses
a perpendicular member, multiplies it by `sin (π t / l)`, and applies the jointly smooth
intrinsic exponential variation on a uniform slab.

The resulting proper variation has strictly negative second variation whenever
`sec ≥ k > 0` and `l > π / sqrt k`.  It also witnesses failure of a local minimum along this
one-parameter family.  This is the precise variational certificate behind Petersen's phrase
"not locally minimizing"; no distance-realizing or completeness hypothesis is used.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [LocallyCompactSpace M]
  [T2Space (TangentBundle I M)] [ConnectedSpace M]

/-- **Math.** Petersen Lemma 6.3.1 in callback-free intrinsic-variation form.  A unit-speed
geodesic of length `l > π / sqrt k` on a manifold with `sec ≥ k > 0` admits a jointly smooth
proper variation with strictly negative second variation of energy.  In particular, the energy
of the geodesic is not a local minimum along this variation.

The dimension assumption supplies a parallel unit direction perpendicular to the velocity.
The variation, its common open slab, fixed endpoints, curvature-weight integrability, and all
parallel-field identities are constructed internally. -/
theorem bonnetSynge_longGeodesicsNotMinimizing_of_secLowerBound
    (g : RiemannianMetric I M) {σ : ℝ → M} {l k : ℝ}
    (hk : 0 < k) (hlk : π / Real.sqrt k < l)
    (hσc : Continuous σ) (hσgeo : Geodesic.IsGeodesic (I := I) g σ)
    (hspeed : ∀ t, g.metricInner (σ t) (curveVelocity (I := I) σ t)
      (curveVelocity (I := I) σ t) = 1)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hsec : HasSecBoundedBelow g.leviCivita k) :
    ∃ (f : ℝ → ℝ → M) (δ a b : ℝ),
      0 < δ ∧ Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f)
        (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b) ∧
      f 0 = σ ∧
      (∀ s, f s 0 = f 0 0) ∧
      (∀ s, f s l = f 0 l) ∧
      deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) 0 l)) 0 < 0 ∧
      ¬ IsLocalMin (fun s : ℝ => energyFunctional (I := I) g (f s) 0 l) 0 := by
  classical
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos hsk) hlk
  let J : Set ℝ := Set.Ioo (-1) (l + 1)
  have hJopen : IsOpen J := isOpen_Ioo
  have hsubJ : Set.Icc (0 : ℝ) l ⊆ J := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht₀ : (0 : ℝ) ∈ J := by
    constructor <;> linarith
  have hcM : ∀ t ∈ Set.Icc (-1) (l + 1), ContMDiffAt 𝓘(ℝ, ℝ) I 2 σ t :=
    fun t _ => IsGeodesic.contMDiffAt_two (I := I) g hσgeo hσc t
  obtain ⟨e, n₀, hepar, heorth, hevel⟩ :=
    exists_velocitySeededParallelOrthonormalFrameOn_Ioo (I := I) g ht₀ hcM
      hσc hσgeo (hspeed 0)
  let s : Finset (Fin (Module.finrank ℝ E)) := Finset.univ.erase n₀
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs0
    have hcard0 : s.card = 0 := by rw [hs0, Finset.card_empty]
    have hcard : s.card = Module.finrank ℝ E - 1 := by simp [s]
    omega
  obtain ⟨i, hi⟩ := hs
  have hi_ne : i ≠ n₀ := (Finset.mem_erase.mp hi).1
  have hEpar : IsParallelSolOn (I := I) g σ J (e i) := hepar i
  have hEunit : ∀ t ∈ J,
      g.metricInner (σ t) (e i t) (e i t) = 1 := by
    intro t ht
    simpa using heorth t ht i i
  have hEperp : ∀ t ∈ J,
      g.metricInner (σ t) (e i t) (curveVelocity (I := I) σ t) = 0 := by
    intro t ht
    rw [← hevel t ht]
    simpa [hi_ne] using heorth t ht i n₀
  have hσsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ J := by
    intro t ht
    exact (IsGeodesic.contMDiffAt_infty (I := I) g hσgeo hσc t).contMDiffWithinAt
  have hEsm : IsVectorFieldAlong (I := I) σ (e i) J :=
    hEpar.isVectorFieldAlong_infty (I := I) g
      (fun t _ => IsGeodesic.contMDiffAt_infty (I := I) g hσgeo hσc t)
  let w : ℝ → ℝ := fun t => Real.sin (π / l * t)
  let W : ∀ t, TangentSpace I (σ t) := fun t => w t • e i t
  have hwsm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w J :=
    (by fun_prop : ContDiff ℝ ∞ w).contMDiff.contMDiffOn
  have hWsm : IsVectorFieldAlong (I := I) σ W J := hEsm.smul hwsm
  obtain ⟨δ, a, b, hδ, hsub, hfIntrinsic⟩ :=
    exists_intrinsicExpVariation_contMDiffOn_slab (I := I) g hJopen hl hsubJ hσsm hWsm
  -- Anchor the zero slice by reduction.  The anchored wrapper is propositionally equal to the
  -- intrinsic exponential everywhere, so it retains the slab smoothness while making the base
  -- curve definitionally `σ`, avoiding dependent tangent-space casts in the variation data.
  let f : ℝ → ℝ → M := fun u t =>
    if hu : u = 0 then σ t else intrinsicExpVariation (I := I) g σ W u t
  have hfEq : f = intrinsicExpVariation (I := I) g σ W := by
    funext u t
    by_cases hu : u = 0
    · subst u
      simp [f]
    · simp [f, hu]
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f)
      (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b) := by
    rw [hfEq]
    exact hfIntrinsic
  have hbase : f 0 = σ := by
    funext t
    simp [f]
  have hzero : W 0 = 0 := by simp [W, w]
  have hmul : π / l * l = π := by field_simp
  have hlast : W l = 0 := by simp [W, w, hmul]
  have hfix₀ : ∀ u, f u 0 = f 0 0 := by
    intro u
    simp [f, intrinsicExpVariation, hzero, geodesicMaximalCurve_zero]
  have hfixl : ∀ u, f u l = f 0 l := by
    intro u
    simp [f, intrinsicExpVariation, hlast, geodesicMaximalCurve_zero]
  have hgeo : ∀ t ∈ Set.Icc (0 : ℝ) l,
      curveAcceleration (I := I) g (f 0) t = 0 := by
    intro t _
    rw [hbase]
    exact IsGeodesic.curveAcceleration_eq_zero hσgeo t
  have hEpar' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      derivAlongCurve (I := I) g (f 0) (e i) t = 0 := by
    intro t ht
    rw [hbase]
    exact (hEpar t (hsubJ ht)).2
  have hEdiff' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) (e i)) t := by
    intro t ht
    rw [hbase]
    exact (hEpar t (hsubJ ht)).1
  have hEunit' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (e i t) (e i t) = 1 := by
    intro t ht
    rw [hbase]
    exact hEunit t (hsubJ ht)
  have hEperp' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (e i t) (curveVelocity (I := I) (f 0) t) = 0 := by
    intro t ht
    rw [hbase]
    exact hEperp t (hsubJ ht)
  have hspeed' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
        (curveVelocity (I := I) (f 0) t) = 1 := by
    intro t _
    rw [hbase]
    exact hspeed t
  have hVfield : variationField (I := I) f =
      fun t => Real.sin (π / l * t) • e i t := by
    rw [hfEq]
    funext t
    simpa [W, w] using variationField_intrinsicExpVariation (I := I) g σ W t
  have hintσ := intervalIntegrable_sine_sq_sectionalCurvature_of_parallel (I := I)
    g hl hσc hσgeo hEpar hEunit hEperp hspeed
  have hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
      sectionalCurvature (g.leviCivita) (f 0 t) (e i t)
        (curveVelocity (I := I) (f 0) t)) volume 0 l := by
    rw [hbase]
    exact hintσ
  have hsecond := bonnetSynge_secondVariation_eq_on_segment (I := I) g hl hδ hsub hf
    hgeo hfix₀ hfixl hEpar' hEdiff' hEunit' hEperp' hspeed' hVfield hint
  have hcurv : ∀ t ∈ Set.Icc (0 : ℝ) l,
      k ≤ sectionalCurvature (g.leviCivita) (f 0 t) (e i t)
        (curveVelocity (I := I) (f 0) t) := by
    intro t ht
    have hli : LinearIndependent ℝ ![e i t, curveVelocity (I := I) (f 0) t] := by
      by_contra h
      have hz := bivectorInnerProduct_self_eq_zero_of_not_linearIndependent g (f 0 t) h
      rw [show bivectorInnerProduct g (f 0 t) (e i t) (curveVelocity (I := I) (f 0) t)
            (e i t) (curveVelocity (I := I) (f 0) t) = 1 from by
          rw [bivectorInnerProduct, hEunit' t ht, hspeed' t ht, hEperp' t ht]
          ring] at hz
      exact one_ne_zero hz
    exact hsec (f 0 t) (e i t) (curveVelocity (I := I) (f 0) t) hli
  have hcore := bonnetSynge_index_core hl hk hlk hint hcurv
  rw [integral_cos_sq_window hl] at hcore
  have hneg : deriv (deriv (fun u : ℝ => energyFunctional (I := I) g (f u) 0 l)) 0 < 0 := by
    rw [hsecond]
    exact hcore
  have henergyDiff : DifferentiableAt ℝ
      (fun u : ℝ => energyFunctional (I := I) g (f u) 0 l) 0 :=
    (hasDerivAt_pieceEnergy_shift (I := I) g (s₀ := 0) (by simpa using hδ) hl
      (hf.mono (Set.prod_mono subset_rfl hsub))).differentiableAt
  have hnotMin : ¬ IsLocalMin
      (fun u : ℝ => energyFunctional (I := I) g (f u) 0 l) 0 := by
    intro hmin
    have hderiv0 : deriv (fun u : ℝ => energyFunctional (I := I) g (f u) 0 l) 0 = 0 :=
      hmin.deriv_eq_zero
    have hnonneg := isLocalMin_deriv_deriv_nonneg hmin hderiv0 henergyDiff.continuousAt
    linarith
  exact ⟨f, δ, a, b, hδ, hsub, hf, hbase, hfix₀, hfixl, hneg, hnotMin⟩

end PetersenLib
