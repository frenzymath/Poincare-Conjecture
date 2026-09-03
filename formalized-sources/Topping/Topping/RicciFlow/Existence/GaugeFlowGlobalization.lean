import Topping.RicciFlow.Existence.GaugeFlow

/-!
# Globalization of the non-autonomous gauge flow

The compact-slice construction gives a uniform local flow box at each time.
The remaining global analytic input is an all-time, jointly smooth family of
integral curves for the autonomous suspension.  This file isolates that input
and derives the global flow laws and diffeomorphism slices from ODE uniqueness.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Function Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A global smooth flow for the autonomous suspension of a
time-dependent vector field.  This structure contains only the genuine
all-time ODE solution and its dependence on initial data; the time-coordinate,
cocycle, inverse, and diffeomorphism laws are consequences below. -/
structure GlobalTimeDependentFlow
    (V : SmoothTimeDependentVectorField (I := I) (M := M)) where
  Φ : (M × ℝ) → ℝ → (M × ℝ)
  apply_zero : ∀ x : M × ℝ, Φ x 0 = x
  integral_curve : ∀ x : M × ℝ,
    IsMIntegralCurveOn (Φ x) (fun q => V.suspension q) Set.univ
  joint_smooth : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
    (I.prod 𝓘(ℝ, ℝ)) ∞ (fun z : (M × ℝ) × ℝ => Φ z.1 z.2)

namespace GlobalTimeDependentFlow

variable {V : SmoothTimeDependentVectorField (I := I) (M := M)}

/-- **Math.** The spatial part of the global flow, based at absolute time
`t₀` and parametrized by elapsed time. -/
def spatialFlow (G : GlobalTimeDependentFlow V) (t₀ : ℝ) : M → ℝ → M :=
  fun p s => (G.Φ (p, t₀) s).1

/-! ## The suspended time coordinate -/

/-- **Math.** Every global suspended trajectory advances the time coordinate
at unit speed.  This is obtained from the integral-curve derivative and the
initial condition, rather than being included as an additional flow axiom. -/
theorem time_coord (G : GlobalTimeDependentFlow V) (x : M × ℝ) (s : ℝ) :
    (G.Φ x s).2 = x.2 + s := by
  let eta : ℝ := |s| + 1
  have heta : 0 < eta := by
    dsimp [eta]
    linarith [abs_nonneg s]
  have hs : s ∈ Ioo (-eta) eta := by
    dsimp [eta]
    constructor
    · linarith [neg_abs_le s]
    · linarith [le_abs_self s]
  have hderiv : ∀ u ∈ Ioo (-eta) eta,
      HasDerivWithinAt (fun r => (G.Φ x r).2 - (x.2 + r))
        0 (Ioo (-eta) eta) u := by
    intro u hu
    have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (G.Φ x) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V.suspension (G.Φ x u))) :=
      (G.integral_curve x u (mem_univ u)).hasMFDerivAt univ_mem
    have htime : HasDerivAt (fun r => (G.Φ x r).2) 1 u := by
      have hcomp :=
        MorganTianLib.hasDerivAt_comp_of_hasMFDerivAt
          (M := M × ℝ) (I := I.prod 𝓘(ℝ, ℝ))
          (F := (Prod.snd : M × ℝ → ℝ)) contMDiff_snd hγ
      convert hcomp using 1
      exact (suspension_time_derivative V (G.Φ x u)).symm
    have hlin : HasDerivAt (fun r : ℝ => x.2 + r) 1 u :=
      (hasDerivAt_id u).const_add x.2
    have hsub' := htime.sub hlin
    have hfun :
        (fun r => (G.Φ x r).2 - (x.2 + r)) =
          (fun r => (G.Φ x r).2) - (fun r => x.2 + r) := by
      funext r
      rfl
    have hsub : HasDerivAt
        (fun r => (G.Φ x r).2 - (x.2 + r)) 0 u := by
      rw [hfun]
      simpa only [sub_self] using hsub'
    exact hsub.hasDerivWithinAt
  have h0mem : (0 : ℝ) ∈ Ioo (-eta) eta :=
    ⟨neg_neg_iff_pos.mpr heta, heta⟩
  have hbound :
      ‖((G.Φ x s).2 - (x.2 + s)) -
          ((G.Φ x 0).2 - (x.2 + 0))‖ ≤
        0 * ‖s - 0‖ :=
    (convex_Ioo (-eta) eta).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => (G.Φ x r).2 - (x.2 + r)) (f' := fun _ => 0)
      hderiv (fun _ _ => by simp) h0mem hs
  rw [zero_mul, G.apply_zero x] at hbound
  have hzero' := norm_le_zero_iff.mp hbound
  linarith

/-! ## Global trajectory law -/

/-- **Math.** Translating one global suspended trajectory and restarting at its
value gives the same global trajectory.  This is the global ODE uniqueness
step behind the non-autonomous flow cocycle. -/
theorem trajectory_add (G : GlobalTimeDependentFlow V) (x : M × ℝ)
    (s u : ℝ) :
    G.Φ (G.Φ x s) u = G.Φ x (s + u) := by
  have hV : CMDiff 1
      (fun q : M × ℝ =>
        (⟨q, V.suspension q⟩ :
          TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
    exact V.suspension.smooth.of_le (by norm_num)
  have hcurve : IsMIntegralCurve (G.Φ x)
      (fun q => V.suspension q) :=
    (isMIntegralCurve_iff_isMIntegralCurveOn).mpr (G.integral_curve x)
  have hcurve' : IsMIntegralCurve (G.Φ (G.Φ x s))
      (fun q => V.suspension q) :=
    (isMIntegralCurve_iff_isMIntegralCurveOn).mpr
      (G.integral_curve (G.Φ x s))
  have hzero : ((G.Φ x) ∘ (· + s)) 0 = (G.Φ (G.Φ x s)) 0 := by
    simp [Function.comp_apply, G.apply_zero]
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (t₀ := (0 : ℝ)) hV (hcurve.comp_add s) hcurve' hzero
  have hu := congrFun heq u
  simpa [Function.comp_apply, add_comm] using hu.symm

/-- **Math.** A global suspended trajectory splits into its spatial value and
the translated absolute time. -/
theorem trajectory_eq_spatialFlow_prod_time
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s : ℝ) :
    G.Φ (p, t₀) s = (G.spatialFlow t₀ p s, t₀ + s) := by
  apply Prod.ext
  · rfl
  · exact G.time_coord (p, t₀) s

/-! ## Spatial cocycle and inverse laws -/

/-- **Math.** The spatial slices of a global time-dependent flow satisfy the
non-autonomous cocycle law. -/
theorem spatialFlow_comp
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s u : ℝ) :
    G.spatialFlow (t₀ + s) (G.spatialFlow t₀ p s) u =
      G.spatialFlow t₀ p (s + u) := by
  have h := G.trajectory_add (p, t₀) s u
  rw [G.trajectory_eq_spatialFlow_prod_time t₀ p s] at h
  simpa [spatialFlow] using congrArg Prod.fst h

@[simp] theorem spatialFlow_zero
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) :
    G.spatialFlow t₀ p 0 = p := by
  change (G.Φ (p, t₀) 0).1 = p
  rw [G.apply_zero]

/-- **Math.** Evolving for `s` and then reversing for `-s` recovers the
original point. -/
theorem spatialFlow_comp_inverse_left
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s : ℝ) :
    G.spatialFlow (t₀ + s) (G.spatialFlow t₀ p s) (-s) = p := by
  rw [G.spatialFlow_comp t₀ p s (-s)]
  simp

/-- **Math.** Reversing a global flow slice and then evolving forward also
recovers the original point. -/
theorem spatialFlow_comp_inverse_right
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s : ℝ) :
    G.spatialFlow t₀ (G.spatialFlow (t₀ + s) p (-s)) s = p := by
  have h := G.spatialFlow_comp_inverse_left (t₀ + s) p (-s)
  simpa [add_assoc, add_comm, add_left_comm] using h

/-- **Math.** Every fixed-time slice of a global gauge flow is bijective; the
inverse is the reverse-time slice based at the translated time. -/
theorem spatialFlow_bijective
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) :
    Function.Bijective (fun p : M => G.spatialFlow t₀ p s) := by
  constructor
  · intro p q hpq
    calc
      p = G.spatialFlow (t₀ + s)
          (G.spatialFlow t₀ p s) (-s) :=
        (G.spatialFlow_comp_inverse_left t₀ p s).symm
      _ = G.spatialFlow (t₀ + s)
          (G.spatialFlow t₀ q s) (-s) :=
        congrArg (fun r : M => G.spatialFlow (t₀ + s) r (-s)) hpq
      _ = q := G.spatialFlow_comp_inverse_left t₀ q s
  · intro q
    refine ⟨G.spatialFlow (t₀ + s) q (-s), ?_⟩
    exact G.spatialFlow_comp_inverse_right t₀ q s

/-! ## Smooth slice packaging -/

/-- **Math.** Joint smoothness of the global trajectory family restricts to a
smooth map on every fixed-time slice. -/
theorem contMDiff_spatialFlow_fixed
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) :
    ContMDiff I I ∞ (fun p : M => G.spatialFlow t₀ p s) := by
  let A : M → (M × ℝ) × ℝ := fun p => ((p, t₀), s)
  have hA : ContMDiff I ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞ A := by
    exact (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
  have hcomp := G.joint_smooth.comp hA
  have hfst := hcomp.fst
  simpa [A, spatialFlow] using hfst

/-- **Math.** A jointly smooth global gauge flow supplies a diffeomorphism for
each fixed-time slice, with inverse given by the reverse slice. -/
noncomputable def spatialDiffeomorph
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) :
    Diffeomorph I I M M ∞ :=
  { toEquiv :=
      { toFun := fun p : M => G.spatialFlow t₀ p s
        invFun := fun p : M => G.spatialFlow (t₀ + s) p (-s)
        left_inv := fun p => G.spatialFlow_comp_inverse_left t₀ p s
        right_inv := fun p => G.spatialFlow_comp_inverse_right t₀ p s }
    contMDiff_toFun := G.contMDiff_spatialFlow_fixed t₀ s
    contMDiff_invFun := by
      simpa using G.contMDiff_spatialFlow_fixed (t₀ + s) (-s) }

@[simp] theorem spatialDiffeomorph_apply
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) (p : M) :
    G.spatialDiffeomorph t₀ s p = G.spatialFlow t₀ p s :=
  rfl

@[simp] theorem spatialDiffeomorph_symm_apply
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) (p : M) :
    (G.spatialDiffeomorph t₀ s).symm p =
      G.spatialFlow (t₀ + s) p (-s) :=
  rfl

/-! ## Diffeomorphism-level cocycle -/

/-- **Math.** The fixed-time spatial diffeomorphisms satisfy the
non-autonomous cocycle law.  Thus evolving for `s` and then for `u` (from the
translated time) is the same diffeomorphism as evolving once for `s + u`.
-/
theorem spatialDiffeomorph_trans
    (G : GlobalTimeDependentFlow V) (t₀ s u : ℝ) :
    (G.spatialDiffeomorph t₀ s).trans
        (G.spatialDiffeomorph (t₀ + s) u) =
      G.spatialDiffeomorph t₀ (s + u) := by
  apply Diffeomorph.ext
  intro p
  simp only [Diffeomorph.coe_trans, Function.comp_apply,
    spatialDiffeomorph_apply]
  exact G.spatialFlow_comp t₀ p s u

#print axioms GlobalTimeDependentFlow.time_coord
#print axioms GlobalTimeDependentFlow.trajectory_add
#print axioms GlobalTimeDependentFlow.spatialFlow_comp
#print axioms GlobalTimeDependentFlow.spatialFlow_bijective
#print axioms GlobalTimeDependentFlow.contMDiff_spatialFlow_fixed
#print axioms GlobalTimeDependentFlow.spatialDiffeomorph
#print axioms GlobalTimeDependentFlow.spatialDiffeomorph_trans

end GlobalTimeDependentFlow

end Topping

end
