import Topping.MaximumPrinciple.ScalarCurvature

/-!
# Scalar curvature consequences of the maximum principle

The weak minimum principle applied to the scalar-curvature evolution equation
controls scalar curvature from below along a Ricci flow.  Two barriers are used:
the constant one, available because the reaction term `(2/n) R ^ 2` is
nonnegative, and the explicit quadratic profile of `Topping.scalarLowerBarrier`.

Every statement here takes the scalar-curvature evolution equation as the
hypothesis `HasScalarCurvatureEvolutionOn`; the geometric derivation of that
equation from `IsRicciFlowOn` is not part of this module.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

/-- **Math.** The scalar-curvature evolution equation restricts to a smaller
time set. -/
theorem HasScalarCurvatureEvolutionOn.mono
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → RiemannianMetric I M} {J J' : Set ℝ}
    (h : HasScalarCurvatureEvolutionOn g J) (hsub : J' ⊆ J) :
    HasScalarCurvatureEvolutionOn g J' :=
  fun t ht p => (h t (hsub ht) p).mono hsub

/-- **Math.** A function whose time derivative dominates its Laplacian keeps any
constant lower bound.  This is the weak minimum principle with the zero
reaction term, whose comparison ODE has constant solutions. -/
theorem const_le_of_laplacian_le_time_deriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M} {u : M → ℝ → ℝ} {T alpha : ℝ}
    (hT : 0 < T)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      metricLaplacianAt (g t) (fun y => u y t) x ≤
        derivWithin (u x) (Icc 0 T) t)
    (hzero : ∀ x, alpha ≤ u x 0) :
    ∀ x t, t ∈ Icc 0 T → alpha ≤ u x t := by
  apply weak_minimum_principle
    (g := g) (X := fun _ => 0) (u := u)
    (φ := fun _ => alpha) (F := fun _ _ => 0)
    (T := T) (α := alpha) hT
  · fun_prop
  · exact hu
  · intro t ht x
    have hdrift :
        (0 : SmoothVectorField I M).dir (fun y => u y t) x = 0 := by
      rw [SmoothVectorField.dir, SmoothVectorField.zero_apply]
      exact map_zero _
    rw [hdrift]
    simpa using hpde t ht x
  · intro t _ht
    simpa using hasDerivWithinAt_const t (Icc 0 T) alpha
  · rfl
  · exact hzero

/-- **Math.** Constant lower-bound comparison when the heat inequality is
required only at strictly positive times. -/
theorem const_le_of_laplacian_le_time_deriv_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M} {u : M → ℝ → ℝ} {T alpha : ℝ}
    (hT : 0 < T)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      metricLaplacianAt (g t) (fun y => u y t) x ≤
        derivWithin (u x) (Icc 0 T) t)
    (hzero : ∀ x, alpha ≤ u x 0) :
    ∀ x t, t ∈ Icc 0 T → alpha ≤ u x t := by
  apply weak_minimum_principle_of_pos
    (g := g) (X := fun _ => 0) (u := u)
    (φ := fun _ => alpha) (F := fun _ _ => 0)
    (T := T) (α := alpha) hT
  · fun_prop
  · exact hu
  · intro t ht htpos x
    have hdrift :
        (0 : SmoothVectorField I M).dir (fun y => u y t) x = 0 := by
      rw [SmoothVectorField.dir, SmoothVectorField.zero_apply]
      exact map_zero _
    rw [hdrift]
    simpa using hpde t ht htpos x
  · intro t _ht
    simpa using hasDerivWithinAt_const t (Icc 0 T) alpha
  · rfl
  · exact hzero

section ScalarCurvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
  {g : ℝ → RiemannianMetric I M} {T alpha : ℝ}

omit [CompactSpace M] in
/-- **Math.** The scalar curvature of a Ricci flow is a supersolution of the
heat equation: its evolution equation has the nonnegative reaction term
`2 |Ric| ^ 2`. -/
theorem laplacian_scalarCurvature_le_time_deriv_of_evolution
    (hT : 0 < T) (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ∀ p,
      metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p ≤
        derivWithin (fun s => scalarCurvatureAt (g s) p) (Icc 0 T) t := by
  intro t ht p
  have hquad :=
    scalarCurvature_parabolic_inequality_of_evolution hT hevolution t ht p
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hreaction :
      0 ≤ (2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureAt (g t) p ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

omit [CompactSpace M] in
/-- **Math.** On the closed consumer interval, scalar curvature is a heat
supersolution at every strictly positive time when its genuine evolution is
known on Ioc 0 T. -/
theorem laplacian_scalarCurvature_le_time_deriv_of_evolution_on_Ioc
    (hT : 0 < T) (hevolution : HasScalarCurvatureEvolutionOn g (Ioc 0 T)) :
    ∀ t ∈ Icc 0 T, 0 < t → ∀ p,
      metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p ≤
        derivWithin (fun s => scalarCurvatureAt (g s) p) (Icc 0 T) t := by
  intro t ht htpos p
  have hquad :=
    scalarCurvature_parabolic_inequality_of_evolution_on_Ioc
      hT hevolution t ht htpos p
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hreaction :
      0 ≤ (2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureAt (g t) p ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- **Math.** Topping, Corollary 3.2.2: a lower bound on the scalar curvature of
a Ricci flow on a closed manifold is preserved for the whole time interval.
Unlike the quadratic barrier, this needs no restriction on `T`, because the
reaction term `(2/n) R ^ 2` is nonnegative. -/
theorem scalarCurvature_ge_of_initial_ge
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → alpha ≤ scalarCurvatureAt (g t) p := by
  apply const_le_of_laplacian_le_time_deriv
    (g := g) (u := fun p t => scalarCurvatureAt (g t) p) hT hR
  · exact laplacian_scalarCurvature_le_time_deriv_of_evolution hT hevolution
  · exact hzero

/-- **Math.** A scalar lower bound is preserved on a closed consumer interval
when the genuine scalar evolution is available on its positive-time part
Ioc 0 T. -/
theorem scalarCurvature_ge_of_initial_ge_of_evolution_on_Ioc
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Ioc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → alpha ≤ scalarCurvatureAt (g t) p := by
  apply const_le_of_laplacian_le_time_deriv_of_pos
    (g := g) (u := fun p t => scalarCurvatureAt (g t) p) hT hR
  · exact laplacian_scalarCurvature_le_time_deriv_of_evolution_on_Ioc
      hT hevolution
  · exact hzero

/-- **Math.** Topping, Corollary 3.2.3, weak half: weakly positive scalar
curvature is preserved under Ricci flow on a closed manifold. -/
theorem scalarCurvature_nonneg_of_initial_nonneg
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, 0 ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → 0 ≤ scalarCurvatureAt (g t) p :=
  scalarCurvature_ge_of_initial_ge hT hR hevolution hzero

/-- **Math.** Nonnegative scalar curvature is preserved with evolution known
only on Ioc 0 T. -/
theorem scalarCurvature_nonneg_of_initial_nonneg_on_Ioc
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Ioc 0 T))
    (hzero : ∀ p, 0 ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → 0 ≤ scalarCurvatureAt (g t) p :=
  scalarCurvature_ge_of_initial_ge_of_evolution_on_Ioc
    hT hR hevolution hzero

/-- **Math.** Topping, Corollary 3.2.3, strict half: positive scalar curvature is
preserved under Ricci flow on a closed manifold.  Compactness turns the
pointwise strict inequality at time zero into a uniform positive bound, which
the preceding corollary propagates. -/
theorem scalarCurvature_pos_of_initial_pos
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, 0 < scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → 0 < scalarCurvatureAt (g t) p := by
  cases isEmpty_or_nonempty M with
  | inl hM => intro p; exact (hM.false p).elim
  | inr hM =>
    have hcont : Continuous fun p : M => scalarCurvatureAt (g 0) p := by
      have h := contMDiff_spatial_slice_of_contMDiffOn_spacetime
        (u := fun p t => scalarCurvatureAt (g t) p) hR
        (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
      exact h.continuous
    obtain ⟨p₀, -, hp₀⟩ :=
      isCompact_univ.exists_isMinOn (univ_nonempty) hcont.continuousOn
    have hmin : ∀ p, scalarCurvatureAt (g 0) p₀ ≤ scalarCurvatureAt (g 0) p :=
      fun p => hp₀ (mem_univ p)
    have hprop := scalarCurvature_ge_of_initial_ge
      (alpha := scalarCurvatureAt (g 0) p₀) hT hR hevolution hmin
    intro p t ht
    exact lt_of_lt_of_le (hzero p₀) (hprop p t ht)

/-- **Math.** Strictly positive scalar curvature is preserved with evolution
known only on Ioc 0 T. -/
theorem scalarCurvature_pos_of_initial_pos_on_Ioc
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Ioc 0 T))
    (hzero : ∀ p, 0 < scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → 0 < scalarCurvatureAt (g t) p := by
  cases isEmpty_or_nonempty M with
  | inl hM => intro p; exact (hM.false p).elim
  | inr hM =>
    have hcont : Continuous fun p : M => scalarCurvatureAt (g 0) p := by
      have h := contMDiff_spatial_slice_of_contMDiffOn_spacetime
        (u := fun p t => scalarCurvatureAt (g t) p) hR
        (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
      exact h.continuous
    obtain ⟨p₀, -, hp₀⟩ :=
      isCompact_univ.exists_isMinOn (univ_nonempty) hcont.continuousOn
    have hmin : ∀ p, scalarCurvatureAt (g 0) p₀ ≤ scalarCurvatureAt (g 0) p :=
      fun p => hp₀ (mem_univ p)
    have hprop := scalarCurvature_ge_of_initial_ge_of_evolution_on_Ioc
      (alpha := scalarCurvatureAt (g 0) p₀) hT hR hevolution hmin
    intro p t ht
    exact lt_of_lt_of_le (hzero p₀) (hprop p t ht)

/-- **Math.** The quadratic scalar barrier consumes genuine evolution on
Ioc 0 T; only its positive-time parabolic inequality is needed. -/
theorem scalarLowerBarrier_le_of_scalarCurvatureEvolution_on_Ioc
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Ioc 0 T))
    (hdenom : ∀ t ∈ Icc 0 T,
      0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * alpha * t)
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T →
      scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤
        scalarCurvatureAt (g t) p := by
  have hn : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  apply scalarLowerBarrier_le_of_parabolic_inequality_of_pos
    (g := g) (R := fun p t => scalarCurvatureAt (g t) p)
    (n := Module.finrank ℝ E) hn hT hR
  · exact scalarCurvature_parabolic_inequality_of_evolution_on_Ioc
      hT hevolution
  · exact hdenom
  · exact hzero

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Math.** For a nonpositive initial bound the quadratic barrier has positive
denominator at every nonnegative time, so no restriction on the length of the
time interval is needed. -/
theorem scalarLowerBarrier_denom_pos_of_nonpos
    (halpha : alpha ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * alpha * t := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have : (2 / (Module.finrank ℝ E : ℝ)) * alpha * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) halpha) ht
  linarith

/-- **Math.** For a nonpositive initial lower bound, the quadratic barrier
holds on the whole closed consumer interval even when evolution is known only
on Ioc 0 T. -/
theorem scalarLowerBarrier_le_of_initial_nonpos_on_Ioc
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Ioc 0 T))
    (halpha : alpha ≤ 0)
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T →
      scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤
        scalarCurvatureAt (g t) p :=
  scalarLowerBarrier_le_of_scalarCurvatureEvolution_on_Ioc hT hR hevolution
    (fun _t ht => scalarLowerBarrier_denom_pos_of_nonpos halpha ht.1) hzero

/-- **Math.** Topping, Theorem 3.2.1 for a nonpositive initial bound: the
quadratic lower barrier then holds on the whole time interval of the flow. -/
theorem scalarLowerBarrier_le_of_initial_nonpos
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (halpha : alpha ≤ 0)
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T →
      scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤
        scalarCurvatureAt (g t) p :=
  scalarLowerBarrier_le_of_scalarCurvatureEvolution hT hR hevolution
    (fun _t ht => scalarLowerBarrier_denom_pos_of_nonpos halpha ht.1) hzero

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Math.** For a negative initial bound the quadratic barrier is strictly
above the universal profile `-n / (2 t)`: the barrier equals
`-1 / (1 / (-alpha) + 2 t / n)` and the extra positive term `1 / (-alpha)` in the
denominator makes it larger. -/
theorem neg_div_lt_scalarLowerBarrier
    (halpha : alpha < 0) {t : ℝ} (ht : 0 < t) :
    -((Module.finrank ℝ E : ℝ) / (2 * t)) <
      scalarLowerBarrier (Module.finrank ℝ E) alpha t := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hdenom : 0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * alpha * t :=
    scalarLowerBarrier_denom_pos_of_nonpos halpha.le ht.le
  have hne : (Module.finrank ℝ E : ℝ) - 2 * alpha * t ≠ 0 := by
    have hpos : 0 < (Module.finrank ℝ E : ℝ) - 2 * alpha * t := by
      nlinarith [mul_pos (mul_pos two_pos ht) (neg_pos.mpr halpha)]
    exact ne_of_gt hpos
  have hnpos : 0 < (Module.finrank ℝ E : ℝ) - 2 * alpha * t := by
    nlinarith [mul_pos (mul_pos two_pos ht) (neg_pos.mpr halpha)]
  have hbar : scalarLowerBarrier (Module.finrank ℝ E) alpha t =
      alpha * (Module.finrank ℝ E : ℝ) /
        ((Module.finrank ℝ E : ℝ) - 2 * alpha * t) := by
    rw [scalarLowerBarrier, quadraticBarrier]
    rw [div_eq_div_iff (ne_of_gt hdenom) hne]
    field_simp
  rw [hbar, neg_div' , div_lt_div_iff₀ (by positivity) hnpos]
  nlinarith [mul_pos hn hn]

/-- **Math.** Topping, Corollary 3.2.5: along a Ricci flow on a closed manifold
the scalar curvature satisfies the universal lower bound `R >= -n / (2 t)` at
every positive time, with no hypothesis on the initial data. -/
theorem neg_div_le_scalarCurvature
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T)) :
    ∀ p t, t ∈ Icc 0 T → 0 < t →
      -((Module.finrank ℝ E : ℝ) / (2 * t)) ≤ scalarCurvatureAt (g t) p := by
  cases isEmpty_or_nonempty M with
  | inl hM => intro p; exact (hM.false p).elim
  | inr hM =>
    have hcont : Continuous fun p : M => scalarCurvatureAt (g 0) p := by
      have h := contMDiff_spatial_slice_of_contMDiffOn_spacetime
        (u := fun p t => scalarCurvatureAt (g t) p) hR
        (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
      exact h.continuous
    obtain ⟨p₀, -, hp₀⟩ :=
      isCompact_univ.exists_isMinOn (univ_nonempty) hcont.continuousOn
    have hmin : ∀ p, scalarCurvatureAt (g 0) p₀ ≤ scalarCurvatureAt (g 0) p :=
      fun p => hp₀ (mem_univ p)
    set alpha₀ : ℝ := scalarCurvatureAt (g 0) p₀ with halpha₀
    intro p t ht htpos
    have hn : 0 < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
    rcases le_or_gt 0 alpha₀ with hsign | hsign
    · -- a nonnegative initial bound is preserved, and beats `-n / (2 t)`
      have hprop := scalarCurvature_ge_of_initial_ge
        (alpha := alpha₀) hT hR hevolution hmin
      have hneg : -((Module.finrank ℝ E : ℝ) / (2 * t)) ≤ 0 := by
        have : 0 < (Module.finrank ℝ E : ℝ) / (2 * t) := by positivity
        linarith
      exact hneg.trans (hsign.trans (hprop p t ht))
    · -- a negative initial bound gives the quadratic barrier, itself larger
      have hprop := scalarLowerBarrier_le_of_initial_nonpos
        (alpha := alpha₀) hT hR hevolution hsign.le hmin
      exact (neg_div_lt_scalarLowerBarrier hsign htpos).le.trans (hprop p t ht)

/-- **Math.** The quadratic comparison profile with a positive initial value is
unbounded as its time approaches the blow-up time `n / (2 alpha)`: every level
`B` is exceeded strictly before that time.  Stated over plain reals, since only
arithmetic is involved. -/
theorem exists_barrier_gt_of_pos {n alpha B : ℝ} (hn : 0 < n) (halpha : 0 < alpha)
    (hB : 0 < B) :
    ∃ t : ℝ, 0 < t ∧ t < n / (2 * alpha) ∧
      B < alpha * n / (n - 2 * alpha * t) := by
  refine ⟨(n - alpha * n / (B + alpha)) / (2 * alpha), ?_, ?_, ?_⟩
  · apply div_pos _ (by positivity)
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : 0 < alpha * n / (B + alpha) := by positivity
    nlinarith
  · have hkey : n - 2 * alpha * ((n - alpha * n / (B + alpha)) / (2 * alpha)) =
        alpha * n / (B + alpha) := by
      field_simp; ring
    rw [hkey, div_div_eq_mul_div, mul_comm, mul_div_assoc,
      div_self (by positivity : alpha * n ≠ 0), mul_one]
    linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Math.** For a positive initial bound the quadratic barrier has positive
denominator exactly before the blow-up time `n / (2 alpha)`. -/
theorem scalarLowerBarrier_denom_pos_of_pos (halpha : 0 < alpha) {t : ℝ}
    (ht : 0 ≤ t) (hlt : t < (Module.finrank ℝ E : ℝ) / (2 * alpha)) :
    0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * alpha * t := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  rw [lt_div_iff₀ (by positivity)] at hlt
  rw [sub_pos, ← lt_div_iff₀' (by positivity : (0:ℝ) < 2 / (Module.finrank ℝ E : ℝ) * alpha)]
  rw [lt_div_iff₀ (by positivity)]
  have hcancel : 2 / (Module.finrank ℝ E : ℝ) * alpha * (Module.finrank ℝ E : ℝ)
      = 2 * alpha := by field_simp
  nlinarith [hcancel]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **Math.** Closed form of the quadratic scalar barrier for a positive initial
value, valid strictly before the blow-up time `n / (2 alpha)`. -/
theorem scalarLowerBarrier_eq_of_lt_blowup (halpha : 0 < alpha) {t : ℝ}
    (ht : 0 ≤ t) (hlt : t < (Module.finrank ℝ E : ℝ) / (2 * alpha)) :
    scalarLowerBarrier (Module.finrank ℝ E) alpha t =
      alpha * (Module.finrank ℝ E : ℝ) /
        ((Module.finrank ℝ E : ℝ) - 2 * alpha * t) := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hdenom : 0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * alpha * t :=
    scalarLowerBarrier_denom_pos_of_pos halpha ht hlt
  rw [lt_div_iff₀ (by positivity)] at hlt
  have hnpos : 0 < (Module.finrank ℝ E : ℝ) - 2 * alpha * t := by nlinarith
  rw [scalarLowerBarrier, quadraticBarrier,
    div_eq_div_iff (ne_of_gt hdenom) (ne_of_gt hnpos)]
  field_simp

/-- **Math.** The quadratic barrier holds on any subinterval of `[0, T]` that
stays strictly before the blow-up time. -/
theorem scalarLowerBarrier_le_of_initial_pos
    (_hT : 0 < T) (halpha : 0 < alpha)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p)
    {t₀ : ℝ} (ht₀pos : 0 < t₀) (ht₀le : t₀ ≤ T)
    (ht₀lt : t₀ < (Module.finrank ℝ E : ℝ) / (2 * alpha)) :
    ∀ p, scalarLowerBarrier (Module.finrank ℝ E) alpha t₀ ≤
      scalarCurvatureAt (g t₀) p := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hsub : Icc (0 : ℝ) t₀ ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht₀le
  have hdenom : ∀ t ∈ Icc (0 : ℝ) t₀,
      0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * alpha * t := by
    intro t ht
    have hlt : t < (Module.finrank ℝ E : ℝ) / (2 * alpha) :=
      lt_of_le_of_lt ht.2 ht₀lt
    exact scalarLowerBarrier_denom_pos_of_pos halpha ht.1 hlt
  have hbarrier := scalarLowerBarrier_le_of_scalarCurvatureEvolution
    (alpha := alpha) (T := t₀) ht₀pos
    (hR.mono (fun z hz => ⟨hz.1, hsub hz.2⟩))
    (hevolution.mono hsub) hdenom hzero
  exact fun p => hbarrier p t₀ ⟨ht₀pos.le, le_rfl⟩

/-- **Math.** Topping, Corollary 3.2.4: a Ricci flow on a closed nonempty
manifold whose scalar curvature starts at least `alpha > 0` cannot be defined on
a closed interval `[0, T]` reaching the blow-up time `n / (2 alpha)`.  The
comparison solution diverges there, while the scalar curvature stays bounded on
the compact spacetime `M x [0, T]`; so a time strictly before the blow-up already
violates the barrier. -/
theorem lt_of_scalarCurvature_initial_pos [Nonempty M]
    (hT : 0 < T) (halpha : 0 < alpha)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    T < (Module.finrank ℝ E : ℝ) / (2 * alpha) := by
  rcases le_or_gt ((Module.finrank ℝ E : ℝ) / (2 * alpha)) T with hle | hlt
  · exfalso
    obtain ⟨z, -, hzmax⟩ :=
      (isCompact_univ.prod
          (isCompact_Icc (a := (0 : ℝ)) (b := T))).exists_isMaxOn
        ⟨(Classical.arbitrary M, 0), ⟨mem_univ _, le_rfl, hT.le⟩⟩ hR.continuousOn
    -- generalize the spacetime maximum to an opaque real before any arithmetic
    obtain ⟨B, hbound⟩ : ∃ B : ℝ, ∀ p t, t ∈ Icc 0 T →
        scalarCurvatureAt (g t) p ≤ B := by
      refine ⟨scalarCurvatureAt (g z.2) z.1, fun p t ht => ?_⟩
      have h := hzmax (a := (p, t)) ⟨mem_univ p, ht⟩
      simpa only [Set.mem_setOf_eq] using h
    clear hzmax
    have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
    have hBpos : (0 : ℝ) < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ 1)
    obtain ⟨t₀, ht₀pos, ht₀lt, ht₀gt⟩ :=
      exists_barrier_gt_of_pos hn halpha hBpos
    have ht₀le : t₀ ≤ T := ht₀lt.le.trans hle
    have hbarrier := scalarLowerBarrier_le_of_initial_pos hT halpha hR
      hevolution hzero ht₀pos ht₀le ht₀lt (Classical.arbitrary M)
    rw [scalarLowerBarrier_eq_of_lt_blowup halpha ht₀pos.le ht₀lt] at hbarrier
    have hb := hbound (Classical.arbitrary M) t₀ ⟨ht₀pos.le, ht₀le⟩
    have := le_max_left B 1
    linarith
  · exact hlt

/-- **Math.** Topping, Corollary 3.2.4 as the book states it: for a flow on the
*half-open* interval `[0, T)` with `R ≥ alpha > 0` initially, `T ≤ n / (2 alpha)`.

This follows from the closed-interval form by exhaustion.  If `n / (2 alpha) < T`
then the closed interval `[0, n / (2 alpha)]` sits inside `[0, T)`, so the
preceding theorem applies to it and yields `n / (2 alpha) < n / (2 alpha)`. -/
theorem le_of_scalarCurvature_initial_pos_Ico [Nonempty M]
    (halpha : 0 < alpha)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Ico 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Ico 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    T ≤ (Module.finrank ℝ E : ℝ) / (2 * alpha) := by
  have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  by_contra hlt
  rw [not_le] at hlt
  -- the closed interval up to the blow-up time lies inside `[0, T)`
  have hTpos : 0 < (Module.finrank ℝ E : ℝ) / (2 * alpha) := by positivity
  have hsub : Icc (0 : ℝ) ((Module.finrank ℝ E : ℝ) / (2 * alpha)) ⊆ Ico 0 T :=
    fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hlt⟩
  have hstrict := lt_of_scalarCurvature_initial_pos
    (T := (Module.finrank ℝ E : ℝ) / (2 * alpha)) hTpos halpha
    (hR.mono (fun z hz => ⟨hz.1, hsub hz.2⟩))
    (hevolution.mono hsub) hzero
  exact absurd hstrict (lt_irrefl _)

end ScalarCurvature

end Topping
