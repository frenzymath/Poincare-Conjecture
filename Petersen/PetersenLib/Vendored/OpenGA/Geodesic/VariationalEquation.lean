/- Vendored from DoCarmo `OpenGALib/Riemannian/Geodesic/VariationalEquation.lean`. Namespace `Riemannian` mapped to
   `PetersenLib`; engineering infrastructure only, not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Geodesic.FlowDependence

set_option linter.unusedSectionVars false
-- the sup-norm instance on curves valued in operators of the extended state space
-- `E × (E →L[ℝ] E)` needs nested pending instance synthesis beyond the default depth
set_option maxSynthPendingDepth 3

/-!
# The variational equation: second-order dependence on initial conditions

The C¹-dependence theory (`PetersenLib.FlowDependence.hasStrictFDerivAt_of_picardResidual_curve`)
differentiates a solution family `σ : E → C([0,T], E)` of the autonomous ODE `x' = f(x)` once
in its initial condition. This file sets up the classical bootstrap to the *second* derivative:
the derivative `Dσ(x)` is computed by the solution `W(x)` of the **variational equation**

  `W' (t) = f' (σ x t) ∘ W (t),  W (0) = 1`,

an operator-valued linear ODE along the base trajectory, and the pair `(σ x, W x)` is itself a
solution family of the autonomous **extended (variational) system**

  `variationalField f f' : (z, W) ↦ (f z, f' z ∘ W)`

on the state space `E × (E →L[ℝ] E)`. Applying the *existing* C¹ machinery to the extended
system therefore differentiates `x ↦ W x` once more — which is second-order dependence of `σ`
on its initial condition. Main results:

* `variationalField`, `variationalFieldDeriv`, `hasFDerivAt_variationalField`,
  `continuousAt_variationalFieldDeriv` — the extended field is differentiable with explicit
  derivative `(u, V) ↦ (f' z u, f' z ∘ V + (f'' z u) ∘ W)`, continuous where `f', f''` are.
* `applyCurve_opFlow_eq_flowDeriv` — **the variational flow computes the derivative of the
  flow**: if `D` solves the linearized integral equation characterizing `Dσ(x₀)` and `W`
  solves the variational Picard equation along the same base trajectory, then
  `D v = (t ↦ W t v)` for every `v` — both sides are fixed points of the same contraction.
* `exists_hasStrictFDerivAt_opFlow_of_picardResidual_curve` — **second-order dependence**:
  given the vector flow `σ` and the operator flow `τ` (the variational flow along `σ x`,
  packaged as zeros of the extended Picard residual), with `T ‖Â₀‖ < 1` for the linearization
  `Â₀` of the extended field along the base pair, the family `x ↦ τ x` is strictly
  differentiable at `x₀`. Combined with the previous point, `x ↦ Dσ(x)` is differentiable —
  `σ` is C² in its initial condition.

The geodesic-spray instantiation lives in `FlowC2Dependence.lean` (the variational flow is
built there by the Neumann series for the operator Volterra equation, fed into these theorems
through `picardResidual_variationalField_eq_zero` and `norm_variationalFieldDeriv_le` below),
leading to `exp_p ∈ C²` in `Exponential/C2Ball.lean`; the Gauss lemma is the next layer.
-/

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology

namespace PetersenLib.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ}

/-! ## Plumbing: products of curves, right composition, commutation with the primitive -/

section CompactDomain

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Math.** Pairing of curves as a continuous linear map
`C(K, E) × C(K, F) →L[ℝ] C(K, E × F)`, `(α, β) ↦ (t ↦ (α t, β t))`; it has norm `≤ 1`
(sup norms, the product carrying the max norm). -/
def curveProd : C(K, E) × C(K, F) →L[ℝ] C(K, E × F) :=
  LinearMap.mkContinuous
    { toFun := fun q => q.1.prodMk q.2
      map_add' := fun q r => by ext t <;> rfl
      map_smul' := fun c q => by ext t <;> rfl }
    1
    (fun q => by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg q)).mpr fun t => ?_
      show ‖(q.1 t, q.2 t)‖ ≤ ‖q‖
      rw [Prod.norm_def, Prod.norm_def]
      exact max_le_max (q.1.norm_coe_le_norm t) (q.2.norm_coe_le_norm t))

@[simp] lemma curveProd_apply (α : C(K, E)) (β : C(K, F)) (t : K) :
    curveProd (α, β) t = (α t, β t) := rfl

/-- **Math.** Right composition with a fixed operator `W₀`, as a continuous bilinear map on
operator curves: `(W₀, γ) ↦ (t ↦ γ t ∘ W₀)`, of norm `≤ 1`. Realizes the initial-condition
dependence of the variational flow: the solution with initial operator `W₀` is the solution
with initial operator `1` right-composed with `W₀`. -/
def compRightCurve :
    (E →L[ℝ] E) →L[ℝ] C(K, E →L[ℝ] E) →L[ℝ] C(K, E →L[ℝ] E) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun W₀ γ => postcomp ((ContinuousLinearMap.compL ℝ E E E).flip W₀) γ)
      (fun W₀ W₁ γ => by ext t; simp)
      (fun c W₀ γ => by ext t; simp)
      (fun W₀ γ γ' => by ext t; simp)
      (fun W₀ c γ => by ext t; simp))
    1
    (fun W₀ γ => by
      rw [one_mul]
      refine (ContinuousMap.norm_le _
        (mul_nonneg (norm_nonneg W₀) (norm_nonneg γ))).mpr fun t => ?_
      calc ‖(γ t).comp W₀‖ ≤ ‖γ t‖ * ‖W₀‖ := (γ t).opNorm_comp_le W₀
        _ ≤ ‖γ‖ * ‖W₀‖ :=
            mul_le_mul_of_nonneg_right (γ.norm_coe_le_norm t) (norm_nonneg W₀)
        _ = ‖W₀‖ * ‖γ‖ := mul_comm _ _)

@[simp] lemma compRightCurve_apply (W₀ : E →L[ℝ] E) (γ : C(K, E →L[ℝ] E)) (t : K) :
    compRightCurve W₀ γ t = (γ t).comp W₀ := rfl

/-- **Math.** Postcomposition by an operator-curve difference is the difference of the
postcompositions: `postcompCurve (A - B) = postcompCurve A - postcompCurve B` (the
assignment `A ↦ postcompCurve A` is linear). -/
lemma postcompCurve_sub (A B : C(K, E →L[ℝ] F)) :
    (postcompCurve (A - B) : C(K, E) →L[ℝ] C(K, F))
      = postcompCurve A - postcompCurve B := by
  refine ContinuousLinearMap.ext fun β => ?_
  ext t
  simp

/-- **Math.** Left-composition curves do not increase the sup norm:
`‖(t ↦ (A t) ∘L ·)‖ ≤ ‖A‖`, i.e. postcomposing an operator curve with the
left-composition operator `compL` is bounded by the curve's own norm. -/
lemma norm_postcomp_compL_le (A : C(K, E →L[ℝ] E)) :
    ‖postcomp (ContinuousLinearMap.compL ℝ E E E) A‖ ≤ ‖A‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg A)).mpr fun t => ?_
  show ‖ContinuousLinearMap.compL ℝ E E E (A t)‖ ≤ ‖A‖
  refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A t))
    fun B => ?_) (A.norm_coe_le_norm t)
  exact (A t).opNorm_comp_le B

end CompactDomain

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Math.** A continuous linear map commutes with the Volterra primitive:
`A ∘ ∫₀ᵗ β = ∫₀ᵗ A ∘ β` (postcomposition and the primitive commute on curve spaces). -/
lemma postcomp_intervalPrimitive (hT : (0:ℝ) ≤ T) (A : E →L[ℝ] F)
    (β : C(Set.Icc (0:ℝ) T, E)) :
    postcomp A (intervalPrimitive hT β) = intervalPrimitive hT (postcomp A β) := by
  ext t
  simp only [postcomp_apply, intervalPrimitive_apply]
  exact (A.intervalIntegral_comp_comm
    ((β.continuous.comp continuous_projIcc).intervalIntegrable (μ := volume) _ _)).symm

/-! ## The extended (variational) field -/

/-- **Math.** The variational extension of a vector field `f` with derivative `f'`: the
autonomous field `(z, W) ↦ (f z, f' z ∘ W)` on `E × (E →L[ℝ] E)`, whose flow pairs the flow
of `f` with the solution of the variational (linearized) equation along it. -/
def variationalField (f : E → E) (f' : E → E →L[ℝ] E) :
    E × (E →L[ℝ] E) → E × (E →L[ℝ] E) := fun q => (f q.1, (f' q.1).comp q.2)

@[simp] lemma variationalField_apply (f : E → E) (f' : E → E →L[ℝ] E)
    (q : E × (E →L[ℝ] E)) :
    variationalField f f' q = (f q.1, (f' q.1).comp q.2) := rfl

/-- **Math.** The derivative of the variational field at `q = (z, W)`:
`(u, V) ↦ (f' z u, f' z ∘ V + (f'' z u) ∘ W)` — the base direction differentiates through
both slots (the second via the second derivative `f''`), the operator direction through the
left-composition slot only. -/
def variationalFieldDeriv (f' : E → E →L[ℝ] E) (f'' : E → E →L[ℝ] E →L[ℝ] E)
    (q : E × (E →L[ℝ] E)) :
    (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)) :=
  ((f' q.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))).prod
    ((ContinuousLinearMap.compL ℝ E E E (f' q.1)).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
      + ((ContinuousLinearMap.compL ℝ E E E).flip q.2).comp
          ((f'' q.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))))

/-- **Math.** The variational field is differentiable wherever `f` is twice differentiable,
with derivative `variationalFieldDeriv`. -/
theorem hasFDerivAt_variationalField {f : E → E} {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {u : Set E}
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ u, HasFDerivAt f' (f'' x) x)
    {q : E × (E →L[ℝ] E)} (hq : q.1 ∈ u) :
    HasFDerivAt (variationalField f f') (variationalFieldDeriv f' f'' q) q := by
  have h1 : HasFDerivAt (fun p : E × (E →L[ℝ] E) => f p.1)
      ((f' q.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))) q :=
    (hd q.1 hq).comp q hasFDerivAt_fst
  have hc : HasFDerivAt (fun p : E × (E →L[ℝ] E) => f' p.1)
      ((f'' q.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))) q :=
    (hd2 q.1 hq).comp q hasFDerivAt_fst
  have h2 := hc.clm_comp (hasFDerivAt_snd (p := q))
  exact h1.prodMk h2

/-- **Math.** The derivative of the variational field is continuous wherever `f'` and `f''`
are: `q ↦ variationalFieldDeriv f' f'' q` is continuous at every `q` with `f'` and `f''`
continuous at `q.1`. -/
theorem continuousAt_variationalFieldDeriv {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {q : E × (E →L[ℝ] E)}
    (hc : ContinuousAt f' q.1) (hc2 : ContinuousAt f'' q.1) :
    ContinuousAt (variationalFieldDeriv f' f'') q := by
  have hfst : ContinuousAt (fun p : E × (E →L[ℝ] E) => p.1) q := continuousAt_fst
  have hsnd : ContinuousAt (fun p : E × (E →L[ℝ] E) => p.2) q := continuousAt_snd
  -- continuity of each block
  have hblock1 : ContinuousAt (fun p : E × (E →L[ℝ] E) =>
      (f' p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))) q :=
    (hc.comp hfst).clm_comp continuousAt_const
  have hblock2a : ContinuousAt (fun p : E × (E →L[ℝ] E) =>
      (ContinuousLinearMap.compL ℝ E E E (f' p.1)).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) q :=
    (((ContinuousLinearMap.compL ℝ E E E).continuous.continuousAt).comp
      (hc.comp hfst)).clm_comp continuousAt_const
  have hblock2b : ContinuousAt (fun p : E × (E →L[ℝ] E) =>
      ((ContinuousLinearMap.compL ℝ E E E).flip p.2).comp
        ((f'' p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)))) q := by
    refine ContinuousAt.clm_comp ?_ ((hc2.comp hfst).clm_comp continuousAt_const)
    exact ((ContinuousLinearMap.compL ℝ E E E).flip.continuous.continuousAt).comp hsnd
  -- assemble: `A.prod B = inl ∘ A + inr ∘ B`
  have hkey : variationalFieldDeriv f' f''
      = fun p =>
        (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)).comp
          ((f' p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)))
        + (ContinuousLinearMap.inr ℝ E (E →L[ℝ] E)).comp
            ((ContinuousLinearMap.compL ℝ E E E (f' p.1)).comp
                (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
              + ((ContinuousLinearMap.compL ℝ E E E).flip p.2).comp
                  ((f'' p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)))) := by
    funext p
    refine ContinuousLinearMap.ext fun w => ?_
    simp [variationalFieldDeriv, ContinuousLinearMap.prod_apply]
  rw [hkey]
  exact ((continuousAt_const.clm_comp hblock1).add
    (continuousAt_const.clm_comp (hblock2a.add hblock2b)))

/-- **Math.** The variational field is continuous on `u ×ˢ univ` when `f` is differentiable
on the open set `u` (so both `f` and `f'` are continuous there). -/
theorem continuousOn_variationalField {f : E → E} {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {u : Set E}
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ u, HasFDerivAt f' (f'' x) x) :
    ContinuousOn (variationalField f f') (u ×ˢ (Set.univ : Set (E →L[ℝ] E))) := by
  intro q hq
  have hq1 : q.1 ∈ u := hq.1
  have h1 : ContinuousAt f q.1 := (hd q.1 hq1).continuousAt
  have h2 : ContinuousAt f' q.1 := (hd2 q.1 hq1).continuousAt
  refine ContinuousAt.continuousWithinAt ?_
  have hfst : ContinuousAt (fun p : E × (E →L[ℝ] E) => p.1) q := continuousAt_fst
  exact (h1.comp hfst).prodMk ((h2.comp hfst).clm_comp continuousAt_snd)

/-! ## The extended Picard residual: right composition and component extraction -/

/-- **Math.** **Right composition scales the variational flow to arbitrary initial
operators**: if the pair `(α, W)` is a zero of the extended Picard residual with initial
condition `(x, 1)`, then `(α, W ∘ W₀)` is a zero with initial condition `(x, W₀)` — the
variational equation is linear in the operator slot, and right composition by a fixed `W₀`
commutes with the field, the constant embedding, and the primitive. -/
theorem picardResidual_variationalField_compRight
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {u : Set E}
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ u, HasFDerivAt f' (f'' x) x)
    {x : E} {α : C(Set.Icc (0:ℝ) T, E)} {W : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)}
    (hmem : ∀ t, α t ∈ u)
    (hres : picardResidual hT.le (variationalField f f')
      ((x, (1 : E →L[ℝ] E)), curveProd (α, W)) = 0)
    (W₀ : E →L[ℝ] E) :
    picardResidual hT.le (variationalField f f')
      ((x, W₀), curveProd (α, compRightCurve W₀ W)) = 0 := by
  classical
  set ψ : (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)) :=
    (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).prod
      (((ContinuousLinearMap.compL ℝ E E E).flip W₀).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) with hψdef
  have hcont : ContinuousOn (variationalField f f')
      (u ×ˢ (Set.univ : Set (E →L[ℝ] E))) := continuousOn_variationalField hd hd2
  have hval₁ : ∀ t, curveProd (α, W) t ∈ u ×ˢ (Set.univ : Set (E →L[ℝ] E)) :=
    fun t => ⟨hmem t, Set.mem_univ _⟩
  have hval₂ : ∀ t, postcomp ψ (curveProd (α, W)) t
      ∈ u ×ˢ (Set.univ : Set (E →L[ℝ] E)) := fun t => ⟨hmem t, Set.mem_univ _⟩
  -- the scaled pair is the `ψ`-image of the original pair
  have hψpair : curveProd (α, compRightCurve W₀ W) = postcomp ψ (curveProd (α, W)) := by
    ext t
    · rfl
    · rfl
  -- `ψ` sends the initial condition `(x, 1)` to `(x, W₀)`
  have hconst : ContinuousMap.const (Set.Icc (0:ℝ) T) ((x, W₀) : E × (E →L[ℝ] E))
      = postcomp ψ (ContinuousMap.const _ ((x, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E))) := by
    refine ContinuousMap.ext fun t => ?_
    show ((x, W₀) : E × (E →L[ℝ] E)) = ψ (x, (1 : E →L[ℝ] E))
    refine Prod.ext rfl ?_
    show W₀ = (1 : E →L[ℝ] E).comp W₀
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  -- `ψ` commutes with the variational field, hence with the superposition operator
  have hsup : superposition (variationalField f f') (postcomp ψ (curveProd (α, W)))
      = postcomp ψ (superposition (variationalField f f') (curveProd (α, W))) := by
    refine ContinuousMap.ext fun t => ?_
    simp only [postcomp_apply]
    rw [superposition_apply_of_continuousOn hcont _ hval₂ t,
      superposition_apply_of_continuousOn hcont _ hval₁ t]
    simp only [postcomp_apply]
    show variationalField f f' (ψ ((curveProd (α, W)) t))
      = ψ (variationalField f f' ((curveProd (α, W)) t))
    refine Prod.ext rfl ?_
    show (f' (α t)).comp ((W t).comp W₀) = ((f' (α t)).comp (W t)).comp W₀
    rw [ContinuousLinearMap.comp_assoc]
  -- assemble: the scaled residual is the `ψ`-image of the original residual
  have hkey : picardResidual hT.le (variationalField f f')
      ((x, W₀), curveProd (α, compRightCurve W₀ W))
      = postcomp ψ (picardResidual hT.le (variationalField f f')
          ((x, (1 : E →L[ℝ] E)), curveProd (α, W))) := by
    rw [picardResidual_apply, picardResidual_apply, hψpair, hconst, hsup,
      ← postcomp_intervalPrimitive, ← map_sub, ← map_sub]
  rw [hkey, hres, map_zero]

/-- **Math.** **The variational flow solves the linearized integral equation applied to any
vector**: if the pair `(α, W)` is a zero of the extended Picard residual with initial
condition `(x, 1)`, then for every `v : E` the vector curve `t ↦ W t v` solves the linearized
(variational) integral equation along `α` with initial value `v`. This extracts, from the
operator-valued variational flow, exactly the equation characterizing the derivative of the
scalar flow in its initial condition. -/
theorem applyCurve_sub_intervalPrimitive_of_picardResidual_variationalField
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {u : Set E}
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ u, HasFDerivAt f' (f'' x) x)
    {x : E} {α : C(Set.Icc (0:ℝ) T, E)} {W : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)}
    (hmem : ∀ t, α t ∈ u)
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α t))
    (hres : picardResidual hT.le (variationalField f f')
      ((x, (1 : E →L[ℝ] E)), curveProd (α, W)) = 0)
    (v : E) :
    postcomp (ContinuousLinearMap.apply ℝ E v) W
        - intervalPrimitive hT.le
            (postcompCurve A₀ (postcomp (ContinuousLinearMap.apply ℝ E v) W))
      = ContinuousMap.const _ v := by
  classical
  have hcont : ContinuousOn (variationalField f f')
      (u ×ˢ (Set.univ : Set (E →L[ℝ] E))) := continuousOn_variationalField hd hd2
  have hval₁ : ∀ t, curveProd (α, W) t ∈ u ×ˢ (Set.univ : Set (E →L[ℝ] E)) :=
    fun t => ⟨hmem t, Set.mem_univ _⟩
  -- the evaluation `(z, W) ↦ W v` on the extended state space
  set ev : (E × (E →L[ℝ] E)) →L[ℝ] E :=
    (ContinuousLinearMap.apply ℝ E v).comp
      (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)) with hevdef
  -- the `ev`-image of the superposition curve is the linearized integrand
  have hsupev : postcomp ev (superposition (variationalField f f') (curveProd (α, W)))
      = postcompCurve A₀ (postcomp (ContinuousLinearMap.apply ℝ E v) W) := by
    ext t
    rw [postcomp_apply, superposition_apply_of_continuousOn hcont _ hval₁ t]
    show (f' (α t)).comp (W t) v = A₀ t ((W t) v)
    rw [hA₀ t]
    rfl
  -- push the vanishing residual through `ev`
  have h := congrArg (fun γ => postcomp ev γ) hres
  simp only [map_zero] at h
  rw [picardResidual_apply, map_sub, map_sub, postcomp_intervalPrimitive, hsupev] at h
  have hWv : postcomp ev (curveProd (α, W))
      = postcomp (ContinuousLinearMap.apply ℝ E v) W := by
    ext t
    rfl
  have hconstv : postcomp ev
      (ContinuousMap.const (Set.Icc (0:ℝ) T) ((x, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)))
      = ContinuousMap.const _ v := by
    ext t
    show ((1 : E →L[ℝ] E)) v = v
    rfl
  rw [hWv, hconstv] at h
  have h2 : (postcomp (ContinuousLinearMap.apply ℝ E v) W
        - intervalPrimitive hT.le
            (postcompCurve A₀ (postcomp (ContinuousLinearMap.apply ℝ E v) W)))
      - ContinuousMap.const _ v = 0 := by
    rw [← h]; abel
  exact sub_eq_zero.mp h2

/-! ## Main theorems: the variational flow computes the derivative, and is itself C¹ -/

/-- **Math.** **The variational flow computes the derivative of the flow in its initial
condition**: along a base solution `α` with operator curve `A₀ = f' ∘ α` satisfying
`T ‖A₀‖ < 1`, if `D` solves the linearized integral equation characterizing the derivative
of the solution family (`hasStrictFDerivAt_of_picardResidual_curve`), and the pair `(α, W)`
is a zero of the extended Picard residual with initial condition `(x, 1)` (i.e. `W` is the
variational flow along `α`), then `D v = (t ↦ W t v)` for every `v` — both sides are fixed
points of the same contraction `1 - J ∘ M`. -/
theorem flowDeriv_eq_applyCurve_opFlow
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {u : Set E}
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ u, HasFDerivAt f' (f'' x) x)
    {x : E} {α : C(Set.Icc (0:ℝ) T, E)} {W : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)}
    (hmem : ∀ t, α t ∈ u)
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α t))
    (hTL : T * ‖A₀‖ < 1)
    {D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E)}
    (hD : ∀ v : E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
      = ContinuousMap.const _ v)
    (hres : picardResidual hT.le (variationalField f f')
      ((x, (1 : E →L[ℝ] E)), curveProd (α, W)) = 0)
    (v : E) :
    D v = postcomp (ContinuousLinearMap.apply ℝ E v) W := by
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcompCurve A₀) with hJP_def
  have hJPnorm : ‖JP‖ < 1 :=
    (norm_intervalPrimitive_comp_postcompCurve_le hT.le A₀).trans_lt hTL
  set w : (C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))ˣ :=
    Units.oneSub JP hJPnorm with hw_def
  have hWv := applyCurve_sub_intervalPrimitive_of_picardResidual_variationalField
    hT hd hd2 hmem hA₀ hres v
  -- both sides are solutions of `(1 - JP) β = const v`; the unit `1 - JP` is injective
  have h1 : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP) (D v)
      = ContinuousMap.const _ v := by
    simpa [hJP_def] using hD v
  have h2 : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP)
      (postcomp (ContinuousLinearMap.apply ℝ E v) W) = ContinuousMap.const _ v := by
    simpa [hJP_def] using hWv
  have hw1 : (↑w : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) (D v)
      = (↑w : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))
          (postcomp (ContinuousLinearMap.apply ℝ E v) W) := by
    show ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP) (D v) = _
    rw [h1, ← h2]
    rfl
  have hcancel : ∀ β : C(Set.Icc (0:ℝ) T, E),
      (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))
        ((↑w : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) β) = β := fun β =>
    calc (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))
          ((↑w : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) β)
        = ((↑w⁻¹ * ↑w : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))) β := rfl
      _ = (1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) β := by
          rw [w.inv_mul]
      _ = β := rfl
  have hfin := congrArg
    (fun β => (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) β) hw1
  simp only [hcancel] at hfin
  exact hfin

set_option maxHeartbeats 1600000 in
/-- **Math.** **Second-order dependence of a solution family on its initial condition** (the
key step of `C²` dependence, do Carmo Ch. 3, §2 — the regularity behind Theorem 2.2 beyond
`C¹`). Let `σ` be a solution family of `x' = f(x)` near `x₀` (zeros of the Picard residual,
continuous at `x₀`, with base curve `α₀ = σ x₀` valued in an open set `u` where `f` is twice
differentiable), and let `τ x` be the **variational flow** along `σ x` — the operator-valued
solution of `W' = f'(σ x (t)) ∘ W`, `W(0) = 1`, packaged as: the pair `(σ x, τ x)` is a zero
of the Picard residual of the extended field `variationalField f f'` with initial condition
`(x, 1)`. If the extended linearization `Â₀(t) = D(variationalField)(α₀ t, τ x₀ t)` satisfies
`T ‖Â₀‖ < 1`, then the family `x ↦ τ x` of variational flows is strictly differentiable at
`x₀`. Since `τ x` computes the first derivative of the flow
(`flowDeriv_eq_applyCurve_opFlow`), this is second-order differentiability of the flow in its
initial condition.

The proof extends `(σ, τ)` to a solution family of the extended field over the full extended
state space by right composition in the operator slot
(`picardResidual_variationalField_compRight`) and applies the C¹-dependence theorem
(`exists_hasStrictFDerivAt_of_picardResidual_curve`) to the extended system; membership of
the perturbed trajectories in `u` is automatic from continuity of `σ` (the compact base
trajectory has a uniform thickening inside `u`). -/
theorem exists_hasStrictFDerivAt_opFlow_of_picardResidual_curve
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ u, HasFDerivAt f' (f'' x) x)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc2 : ∀ t, ContinuousAt f'' (α₀ t))
    {σ : E → C(Set.Icc (0:ℝ) T, E)} (hσ0 : σ x₀ = α₀) (hσc : ContinuousAt σ x₀)
    {τ : E → C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hτc : ContinuousAt τ x₀)
    (hpair : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le (variationalField f f')
      ((x, (1 : E →L[ℝ] E)), curveProd (σ x, τ x)) = 0)
    {A₂ : C(Set.Icc (0:ℝ) T, (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)))}
    (hA₂ : ∀ t, A₂ t = variationalFieldDeriv f' f'' (α₀ t, τ x₀ t))
    (hTL2 : T * ‖A₂‖ < 1) :
    ∃ Dτ : E →L[ℝ] C(Set.Icc (0:ℝ) T, E →L[ℝ] E), HasStrictFDerivAt τ Dτ x₀ := by
  classical
  -- the extended solution family over the full extended state space
  set sigmaHat : (E × (E →L[ℝ] E)) → C(Set.Icc (0:ℝ) T, E × (E →L[ℝ] E)) :=
    fun q => curveProd (σ q.1, compRightCurve q.2 (τ q.1)) with hsigmaHatDef
  set alphaHat : C(Set.Icc (0:ℝ) T, E × (E →L[ℝ] E)) :=
    curveProd (α₀, τ x₀) with halphaHatDef
  have hone : ∀ γ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E),
      compRightCurve (1 : E →L[ℝ] E) γ = γ := fun γ => by
    refine ContinuousMap.ext fun t => ?_
    show (γ t).comp (1 : E →L[ℝ] E) = γ t
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  have hsigmaHat0 : sigmaHat ((x₀, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)) = alphaHat := by
    show curveProd (σ x₀, compRightCurve (1 : E →L[ℝ] E) (τ x₀)) = curveProd (α₀, τ x₀)
    rw [hσ0, hone]
  -- extended differentiability data
  have huHat : IsOpen (u ×ˢ (Set.univ : Set (E →L[ℝ] E))) := hu.prod isOpen_univ
  have hdHat : ∀ q ∈ u ×ˢ (Set.univ : Set (E →L[ℝ] E)),
      HasFDerivAt (variationalField f f') (variationalFieldDeriv f' f'' q) q :=
    fun q hq => hasFDerivAt_variationalField hd hd2 hq.1
  have hmemHat : ∀ t, alphaHat t ∈ u ×ˢ (Set.univ : Set (E →L[ℝ] E)) :=
    fun t => ⟨hmem t, Set.mem_univ _⟩
  have hcHat : ∀ t, ContinuousAt (variationalFieldDeriv f' f'') (alphaHat t) := fun t =>
    continuousAt_variationalFieldDeriv (q := (α₀ t, τ x₀ t))
      ((hd2 _ (hmem t)).continuousAt) (hc2 t)
  -- continuity of the extended family at the extended base point
  have hsigmaHatC : ContinuousAt sigmaHat ((x₀, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)) := by
    have c1 : ContinuousAt (fun q : E × (E →L[ℝ] E) => σ q.1)
        ((x₀, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)) := hσc.comp continuousAt_fst
    have c2 : ContinuousAt (fun q : E × (E →L[ℝ] E) => compRightCurve q.2 (τ q.1))
        ((x₀, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)) :=
      ContinuousAt.clm_apply
        (((compRightCurve (K := Set.Icc (0:ℝ) T)
          (E := E)).continuous.continuousAt).comp continuousAt_snd)
        (hτc.comp continuousAt_fst)
    exact (curveProd.continuous.continuousAt).comp (c1.prodMk c2)
  -- the perturbed base trajectories stay in `u`: uniform thickening of the compact range
  have hmemx : ∀ᶠ x in 𝓝 x₀, ∀ t, σ x t ∈ u := by
    have hrange : IsCompact (Set.range α₀) := isCompact_range α₀.continuous
    have hrangeu : Set.range α₀ ⊆ u := Set.range_subset_iff.mpr hmem
    obtain ⟨δ, hδ, hthick⟩ := hrange.exists_thickening_subset_open hu hrangeu
    have hball : ∀ᶠ x in 𝓝 x₀, σ x ∈ Metric.ball α₀ δ := by
      have h : ∀ᶠ x in 𝓝 x₀, σ x ∈ Metric.ball (σ x₀) δ :=
        hσc.eventually_mem (Metric.ball_mem_nhds _ hδ)
      rwa [hσ0] at h
    filter_upwards [hball] with x hx t
    refine hthick (Metric.mem_thickening_iff.mpr ⟨α₀ t, Set.mem_range_self t, ?_⟩)
    calc dist (σ x t) (α₀ t) ≤ dist (σ x) α₀ := ContinuousMap.dist_apply_le_dist t
      _ < δ := hx
  -- the extended residual vanishes near the extended base point
  have hresHat : ∀ᶠ q in 𝓝 ((x₀, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)),
      picardResidual hT.le (variationalField f f') (q, sigmaHat q) = 0 := by
    have hS : {x : E | picardResidual hT.le (variationalField f f')
        ((x, (1 : E →L[ℝ] E)), curveProd (σ x, τ x)) = 0 ∧ ∀ t, σ x t ∈ u} ∈ 𝓝 x₀ :=
      hpair.and hmemx
    have hpre := (continuousAt_fst
      (p := ((x₀, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)))).preimage_mem_nhds hS
    filter_upwards [hpre] with q hq
    exact picardResidual_variationalField_compRight hT hd hd2 hq.2 hq.1 q.2
  -- C¹ dependence of the extended family
  obtain ⟨DHat, -, hDHat⟩ :=
    exists_hasStrictFDerivAt_of_picardResidual_curve hT huHat hdHat hmemHat hcHat
      (fun t => hA₂ t) hTL2 hsigmaHat0 hsigmaHatC hresHat
  -- extract the operator component along `x ↦ (x, 1)`
  have hiota : HasStrictFDerivAt (fun x : E => ((x, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E →L[ℝ] E)) x₀ :=
    (hasStrictFDerivAt_id x₀).prodMk (hasStrictFDerivAt_const _ _)
  have hchain := ((postcomp (ContinuousLinearMap.snd ℝ E
      (E →L[ℝ] E))).hasStrictFDerivAt).comp x₀ (hDHat.comp x₀ hiota)
  have hτeq : (fun x : E => postcomp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
      (sigmaHat ((x, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)))) = τ := by
    funext x
    refine ContinuousMap.ext fun t => ?_
    show (τ x t).comp (1 : E →L[ℝ] E) = τ x t
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  rw [hτeq] at hchain
  exact ⟨_, hchain⟩

/-! ## Instantiation interface: norm bound and componentwise residual verification -/

/-- **Math.** Norm bound for the variational-field derivative: at `q = (z, W)` with
`‖f' z‖ ≤ C`, `‖f'' z‖ ≤ C₂` and `‖W‖ ≤ B`,
`‖D(variationalField)(q)‖ ≤ C + C₂ B` (max norm on the product). This is the estimate
that lets a caller choose a Picard time uniformly against the extended linearization. -/
lemma norm_variationalFieldDeriv_le {f' : E → E →L[ℝ] E}
    {f'' : E → E →L[ℝ] E →L[ℝ] E} {q : E × (E →L[ℝ] E)} {C C₂ B : ℝ}
    (h1 : ‖f' q.1‖ ≤ C) (h2 : ‖f'' q.1‖ ≤ C₂) (h3 : ‖q.2‖ ≤ B)
    (hC₂ : 0 ≤ C₂) (hB : 0 ≤ B) :
    ‖variationalFieldDeriv f' f'' q‖ ≤ C + C₂ * B := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) h1
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hw1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  have hw2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
  have happ : variationalFieldDeriv f' f'' q w
      = (f' q.1 w.1, (f' q.1).comp w.2 + (f'' q.1 w.1).comp q.2) := rfl
  rw [happ, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖f' q.1 w.1‖ ≤ ‖f' q.1‖ * ‖w.1‖ := (f' q.1).le_opNorm w.1
      _ ≤ C * ‖w‖ := mul_le_mul h1 hw1 (norm_nonneg _) hC
      _ ≤ (C + C₂ * B) * ‖w‖ := by
          have : 0 ≤ C₂ * B * ‖w‖ := by positivity
          nlinarith
  · calc ‖(f' q.1).comp w.2 + (f'' q.1 w.1).comp q.2‖
        ≤ ‖(f' q.1).comp w.2‖ + ‖(f'' q.1 w.1).comp q.2‖ := norm_add_le _ _
      _ ≤ ‖f' q.1‖ * ‖w.2‖ + ‖f'' q.1 w.1‖ * ‖q.2‖ :=
          add_le_add ((f' q.1).opNorm_comp_le w.2) ((f'' q.1 w.1).opNorm_comp_le q.2)
      _ ≤ C * ‖w‖ + (C₂ * ‖w‖) * B := by
          refine add_le_add (mul_le_mul h1 hw2 (norm_nonneg _) hC) ?_
          refine mul_le_mul ?_ h3 (norm_nonneg _) (by positivity)
          calc ‖f'' q.1 w.1‖ ≤ ‖f'' q.1‖ * ‖w.1‖ := (f'' q.1).le_opNorm w.1
            _ ≤ C₂ * ‖w‖ := mul_le_mul h2 hw1 (norm_nonneg _) hC₂
      _ = (C + C₂ * B) * ‖w‖ := by ring

/-- **Math.** **Componentwise verification of the extended Picard residual**: if the base
curve `α` is a zero of the Picard residual of `f` with initial condition `x`, and the
operator curve `W` satisfies the variational fixed-point equation
`W - 1 - ∫₀ᵗ A₀(s) ∘ W(s) ds = 0` along `α` (where `A₀ t = f' (α t)`), then the pair
`(α, W)` is a zero of the Picard residual of the extended field `variationalField f f'`
with initial condition `(x, 1)`. This is how a caller *constructs* the variational-flow
hypothesis of the second-order dependence theorem from a fixed point of the linear
Volterra equation. -/
theorem picardResidual_variationalField_eq_zero
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E}
    (hf : ContinuousOn f u) (hf' : ContinuousOn f' u)
    {x : E} {α : C(Set.Icc (0:ℝ) T, E)} {W : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)}
    (hmem : ∀ t, α t ∈ u)
    (hres : picardResidual hT.le f (x, α) = 0)
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α t))
    (hfix : W - ContinuousMap.const _ (1 : E →L[ℝ] E)
      - intervalPrimitive hT.le
          (postcompCurve (postcomp (ContinuousLinearMap.compL ℝ E E E) A₀) W) = 0) :
    picardResidual hT.le (variationalField f f')
      ((x, (1 : E →L[ℝ] E)), curveProd (α, W)) = 0 := by
  -- continuity of the extended field on the product region
  have hcont : ContinuousOn (variationalField f f')
      (u ×ˢ (Set.univ : Set (E →L[ℝ] E))) := by
    have hfst : ContinuousOn (fun q : E × (E →L[ℝ] E) => f q.1)
        (u ×ˢ (Set.univ : Set (E →L[ℝ] E))) :=
      hf.comp continuousOn_fst fun q hq => hq.1
    have hsnd : ContinuousOn (fun q : E × (E →L[ℝ] E) => (f' q.1).comp q.2)
        (u ×ˢ (Set.univ : Set (E →L[ℝ] E))) :=
      (hf'.comp continuousOn_fst fun q hq => hq.1).clm_comp continuousOn_snd
    exact hfst.prodMk hsnd
  have hval : ∀ t, curveProd (α, W) t ∈ u ×ˢ (Set.univ : Set (E →L[ℝ] E)) :=
    fun t => ⟨hmem t, Set.mem_univ _⟩
  -- components of the superposition curve
  have hsupfst : postcomp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
      (superposition (variationalField f f') (curveProd (α, W)))
      = superposition f α := by
    ext t
    rw [postcomp_apply, superposition_apply_of_continuousOn hcont _ hval t,
      superposition_apply_of_continuousOn hf α hmem t]
    rfl
  have hsupsnd : postcomp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
      (superposition (variationalField f f') (curveProd (α, W)))
      = postcompCurve (postcomp (ContinuousLinearMap.compL ℝ E E E) A₀) W := by
    refine ContinuousMap.ext fun t => ?_
    rw [postcomp_apply, superposition_apply_of_continuousOn hcont _ hval t]
    show (f' (α t)).comp (W t)
      = (ContinuousLinearMap.compL ℝ E E E) (A₀ t) (W t)
    rw [hA₀ t]
    rfl
  -- component projections of the pair curve and the constant curve
  have hfst_pair : postcomp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
      (curveProd (α, W)) = α := ContinuousMap.ext fun t => rfl
  have hsnd_pair : postcomp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
      (curveProd (α, W)) = W := ContinuousMap.ext fun t => rfl
  have hfst_const : postcomp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
      (ContinuousMap.const (Set.Icc (0:ℝ) T) ((x, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)))
      = ContinuousMap.const _ x := ContinuousMap.ext fun t => rfl
  have hsnd_const : postcomp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
      (ContinuousMap.const (Set.Icc (0:ℝ) T) ((x, (1 : E →L[ℝ] E)) : E × (E →L[ℝ] E)))
      = ContinuousMap.const _ (1 : E →L[ℝ] E) := ContinuousMap.ext fun t => rfl
  -- components of the extended residual
  have hres1 : postcomp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
      (picardResidual hT.le (variationalField f f')
        ((x, (1 : E →L[ℝ] E)), curveProd (α, W)))
      = picardResidual hT.le f (x, α) := by
    rw [picardResidual_apply, picardResidual_apply, map_sub, map_sub,
      postcomp_intervalPrimitive, hsupfst, hfst_pair, hfst_const]
  have hres2 : postcomp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
      (picardResidual hT.le (variationalField f f')
        ((x, (1 : E →L[ℝ] E)), curveProd (α, W)))
      = W - ContinuousMap.const _ (1 : E →L[ℝ] E)
        - intervalPrimitive hT.le
            (postcompCurve (postcomp (ContinuousLinearMap.compL ℝ E E E) A₀) W) := by
    rw [picardResidual_apply, map_sub, map_sub,
      postcomp_intervalPrimitive, hsupsnd, hsnd_pair, hsnd_const]
  -- a product-valued curve vanishes iff its components do
  refine ContinuousMap.ext fun t => ?_
  have e1 := congrArg (fun γ : C(Set.Icc (0:ℝ) T, E) => γ t) (hres1.trans hres)
  have e2 := congrArg (fun γ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E) => γ t) (hres2.trans hfix)
  simp only [postcomp_apply, ContinuousMap.zero_apply] at e1 e2
  refine Prod.ext ?_ ?_
  · exact e1
  · exact e2

end PetersenLib.FlowDependence
