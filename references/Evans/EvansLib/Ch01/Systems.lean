import EvansLib.Ch01.MoreExamples

/-!
# Evans, Ch. 1 §1.2.2 — Systems of partial differential equations

Evans (§1.1) notes that a *system* of `k`th-order PDE for an unknown
`𝐮 : U → ℝᵐ` is "classified in the obvious way as being linear, semilinear, etc."
This file makes that classification precise in the jet framework of
`EvansLib.Ch01.PDE`, mirroring the scalar predicates `EvansLib.IsLinearPDE` etc.
but with the vector-valued codomain `ℝᵐ`, together with the inclusion chain
homogeneous-linear ⊆ linear ⊆ semilinear ⊆ quasilinear ⊆ ¬fully-nonlinear.

It then validates the predicates on Evans' §1.2.2 catalogue:

* the **scalar reaction–diffusion system** `𝐮_t - Δ𝐮 = 𝐟(𝐮)` is *semilinear*;
* the **system of conservation laws** `𝐮_t + div 𝐅(𝐮) = 0` is *quasilinear*.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.2.2.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Classification of systems (Evans, Def. 2 for systems) -/

/-- **Evans, Def. 2(i) for systems.** A `k`th-order system symbol `Φ` valued in
`ℝᵐ` is **linear** if `Φ ξ x = (∑_{j ≤ k} A_j(x)(ξ_j)) - 𝐟(x)` for coefficient
maps `A_j x : PDEJetSlot j E ℝᵐ →L[ℝ] ℝᵐ` (matrices of functionals depending only
on `x`) and a source `𝐟`. -/
def IsLinearPDESystem (m k : ℕ)
    (Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m) : Prop :=
  ∃ (A : (j : Fin (k + 1)) → E →
      (PDEJetSlot (j : ℕ) E (EuclideanℝN m) →L[ℝ] EuclideanℝN m))
    (f : E → EuclideanℝN m),
    ∀ (ξ : PDEJet k E (EuclideanℝN m)) (x : E), Φ ξ x = (∑ j, A j x (ξ j)) - f x

/-- **Evans, Def. 2(i) for systems, homogeneous case.** `𝐟 ≡ 0`. -/
def IsHomogeneousLinearPDESystem (m k : ℕ)
    (Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m) : Prop :=
  ∃ A : (j : Fin (k + 1)) → E →
      (PDEJetSlot (j : ℕ) E (EuclideanℝN m) →L[ℝ] EuclideanℝN m),
    ∀ (ξ : PDEJet k E (EuclideanℝN m)) (x : E), Φ ξ x = ∑ j, A j x (ξ j)

/-- **Evans, Def. 2(ii) for systems.** `Φ` is **semilinear** if it is linear in the
top-order derivative with `x`-dependent coefficients, plus an arbitrary function of
the lower-order derivatives and `x`. -/
def IsSemilinearPDESystem (m k : ℕ)
    (Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m) : Prop :=
  ∃ (aTop : E → (PDEJetSlot k E (EuclideanℝN m) →L[ℝ] EuclideanℝN m))
    (a₀ : ((j : Fin k) → PDEJetSlot (j : ℕ) E (EuclideanℝN m)) → E → EuclideanℝN m),
    ∀ (ξ : PDEJet k E (EuclideanℝN m)) (x : E),
      Φ ξ x = aTop x (ξ (Fin.last k)) + a₀ (fun j => ξ j.castSucc) x

/-- **Evans, Def. 2(iii) for systems.** `Φ` is **quasilinear** if it is affine in
the top-order derivative with coefficients that may also depend on the lower-order
derivatives and on `x`. -/
def IsQuasilinearPDESystem (m k : ℕ)
    (Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m) : Prop :=
  ∃ (aTop : ((j : Fin k) → PDEJetSlot (j : ℕ) E (EuclideanℝN m)) → E →
      (PDEJetSlot k E (EuclideanℝN m) →L[ℝ] EuclideanℝN m))
    (a₀ : ((j : Fin k) → PDEJetSlot (j : ℕ) E (EuclideanℝN m)) → E → EuclideanℝN m),
    ∀ (ξ : PDEJet k E (EuclideanℝN m)) (x : E),
      Φ ξ x =
        aTop (fun j => ξ j.castSucc) x (ξ (Fin.last k)) + a₀ (fun j => ξ j.castSucc) x

/-- **Evans, Def. 2(iv) for systems.** `Φ` is **fully nonlinear** if it is not
quasilinear (depends nonlinearly on the highest-order derivatives). -/
def IsFullyNonlinearPDESystem (m k : ℕ)
    (Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m) : Prop :=
  ¬ IsQuasilinearPDESystem m k Φ

/-! ### The classification inclusions for systems -/

/-- A homogeneous linear system is linear (take `𝐟 = 0`). -/
theorem IsHomogeneousLinearPDESystem.isLinearPDESystem {m k : ℕ}
    {Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m}
    (h : IsHomogeneousLinearPDESystem m k Φ) : IsLinearPDESystem m k Φ := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, 0, ?_⟩
  intro ξ x
  simp [hA ξ x]

/-- Every linear system is semilinear. -/
theorem IsLinearPDESystem.isSemilinearPDESystem {m k : ℕ}
    {Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m}
    (h : IsLinearPDESystem m k Φ) : IsSemilinearPDESystem m k Φ := by
  obtain ⟨A, f, hA⟩ := h
  refine ⟨fun x => A (Fin.last k) x,
    fun ξlow x => (∑ j : Fin k, A j.castSucc x (ξlow j)) - f x, ?_⟩
  intro ξ x
  rw [hA ξ x, Fin.sum_univ_castSucc (fun j => A j x (ξ j)), add_sub_right_comm, add_comm]
  rfl

/-- Every semilinear system is quasilinear. -/
theorem IsSemilinearPDESystem.isQuasilinearPDESystem {m k : ℕ}
    {Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m}
    (h : IsSemilinearPDESystem m k Φ) : IsQuasilinearPDESystem m k Φ := by
  obtain ⟨aTop, a₀, h⟩ := h
  exact ⟨fun _ x => aTop x, a₀, h⟩

/-- A quasilinear system is not fully nonlinear. -/
theorem IsQuasilinearPDESystem.not_isFullyNonlinearPDESystem {m k : ℕ}
    {Φ : PDEJet k E (EuclideanℝN m) → E → EuclideanℝN m}
    (h : IsQuasilinearPDESystem m k Φ) : ¬ IsFullyNonlinearPDESystem m k Φ :=
  fun hfn => hfn h

/-! ## Vector-valued jet contractions -/

/-- Order-`0` vector jet evaluation `𝐮(x) ∈ ℝᵐ`. -/
def jetEvalV (n m : ℕ) :
    PDEJetSlot 0 (SpaceTime n) (EuclideanℝN m) →L[ℝ] EuclideanℝN m :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => SpaceTime n) (EuclideanℝN m) ![]

/-- Vector time derivative `𝐮_t ∈ ℝᵐ` on space–time. -/
def timeD1V (n m : ℕ) :
    PDEJetSlot 1 (SpaceTime n) (EuclideanℝN m) →L[ℝ] EuclideanℝN m :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => SpaceTime n) (EuclideanℝN m)
    ![timeDir n]

/-- Vector spatial directional derivative `𝐮_{xᵢ} ∈ ℝᵐ` on space–time. -/
def jetD1V (n m : ℕ) (i : Fin n) :
    PDEJetSlot 1 (SpaceTime n) (EuclideanℝN m) →L[ℝ] EuclideanℝN m :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => SpaceTime n) (EuclideanℝN m)
    ![spaceDir n i]

/-- Vector spatial Laplacian `Δ_x 𝐮 = ∑ᵢ 𝐮_{xᵢxᵢ} ∈ ℝᵐ` on space–time. -/
def spatialLaplaceV (n m : ℕ) :
    PDEJetSlot 2 (SpaceTime n) (EuclideanℝN m) →L[ℝ] EuclideanℝN m :=
  ∑ i : Fin n, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => SpaceTime n)
    (EuclideanℝN m) ![spaceDir n i, spaceDir n i]

/-! ## Scalar reaction–diffusion system (Evans §1.2.2b) — semilinear -/

/-- **Evans §1.2.2b, reaction–diffusion system** `𝐮_t - Δ𝐮 = 𝐟(𝐮)`, i.e.
`𝐮_t - Δ𝐮 - 𝐟(𝐮) = 0`, for `𝐮 : ℝ^{n+1} → ℝᵐ`. The top-order operator
`𝐮_t - Δ𝐮` (heat operator applied componentwise) is linear; the reaction
`𝐟(𝐮)` is an arbitrary function of `𝐮`. Second order. -/
def reactionDiffusionSystemSymbol (n m : ℕ) (f : EuclideanℝN m → EuclideanℝN m) :
    PDEJet 2 (SpaceTime n) (EuclideanℝN m) → SpaceTime n → EuclideanℝN m :=
  fun ξ _ => timeD1V n m (ξ 1) - spatialLaplaceV n m (ξ 2) - f (jetEvalV n m (ξ 0))

/-- **The reaction–diffusion system is a semilinear (2nd-order) system** (Evans
Def. 2(ii) for systems): the top-order coefficient is the constant linear
operator `-Δ`, and the reaction `𝐟(𝐮)` sits in the lower-order part. -/
theorem reactionDiffusionSystemSymbol_isSemilinearPDESystem (n m : ℕ)
    (f : EuclideanℝN m → EuclideanℝN m) :
    IsSemilinearPDESystem m 2 (reactionDiffusionSystemSymbol n m f) := by
  refine ⟨fun _ => -spatialLaplaceV n m,
    fun low _ => timeD1V n m (low 1) - f (jetEvalV n m (low 0)), ?_⟩
  intro ξ x
  show timeD1V n m (ξ 1) - spatialLaplaceV n m (ξ 2) - f (jetEvalV n m (ξ 0))
    = (-spatialLaplaceV n m) (ξ (Fin.last 2))
      + (timeD1V n m (ξ 1) - f (jetEvalV n m (ξ 0)))
  rw [ContinuousLinearMap.neg_apply]
  abel_nf
  ac_rfl

/-! ## System of conservation laws (Evans §1.2.2b) — quasilinear -/

/-- **Evans §1.2.2b, system of conservation laws** `𝐮_t + div 𝐅(𝐮) = 0`, for
`𝐮 : ℝ^{n+1} → ℝᵐ`. For a classical solution the chain rule turns
`div 𝐅(𝐮)` into `∑ᵢ (D𝐅ⁱ)(𝐮) 𝐮_{xᵢ}`, where `D𝐅ⁱ(𝐮) : ℝᵐ →L ℝᵐ` is the
Jacobian of the `i`-th flux component; we parametrize by `DF`. First order,
quasilinear: the top-order coefficients `D𝐅ⁱ(𝐮)` depend on `𝐮`. -/
def conservationLawSystemSymbol (n m : ℕ)
    (DF : EuclideanℝN m → Fin n → (EuclideanℝN m →L[ℝ] EuclideanℝN m)) :
    PDEJet 1 (SpaceTime n) (EuclideanℝN m) → SpaceTime n → EuclideanℝN m :=
  fun ξ _ => timeD1V n m (ξ 1)
    + ∑ i : Fin n, DF (jetEvalV n m (ξ 0)) i (jetD1V n m i (ξ 1))

/-- **The system of conservation laws is a quasilinear (1st-order) system** (Evans
Def. 2(iii) for systems): its top-order coefficients `D𝐅ⁱ(𝐮)` depend on the
lower-order jet `𝐮`. -/
theorem conservationLawSystemSymbol_isQuasilinearPDESystem (n m : ℕ)
    (DF : EuclideanℝN m → Fin n → (EuclideanℝN m →L[ℝ] EuclideanℝN m)) :
    IsQuasilinearPDESystem m 1 (conservationLawSystemSymbol n m DF) := by
  refine ⟨fun low _ => timeD1V n m
      + ∑ i : Fin n, (DF (jetEvalV n m (low 0)) i).comp (jetD1V n m i),
    fun _ _ => 0, ?_⟩
  intro ξ x
  show timeD1V n m (ξ 1)
      + ∑ i : Fin n, DF (jetEvalV n m (ξ 0)) i (jetD1V n m i (ξ 1))
    = (timeD1V n m
        + ∑ i : Fin n, (DF (jetEvalV n m (ξ 0)) i).comp (jetD1V n m i)) (ξ 1) + 0
  rw [add_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
  simp [ContinuousLinearMap.comp_apply]

/-! ## Equilibrium equations of linear elasticity (Evans §1.2.2a) — linear system -/

/-- The `i`-th standard basis vector `eᵢ` of `ℝⁿ`. -/
def euclidDir (n : ℕ) (i : Fin n) : EuclideanℝN n := EuclideanSpace.single i (1 : ℝ)

/-- Order-`2` vector contraction `D²𝐮(x)(v, w) ∈ ℝᵐ` on `ℝⁿ`. -/
def jetD2Vec (n m : ℕ) (v w : EuclideanℝN n) :
    PDEJetSlot 2 (EuclideanℝN n) (EuclideanℝN m) →L[ℝ] EuclideanℝN m :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanℝN n) (EuclideanℝN m) ![v, w]

/-- The **vector Laplacian** `Δ𝐮 = ∑ᵢ 𝐮_{xᵢxᵢ} ∈ ℝⁿ` (Laplace applied to each
component), as a linear functional of the second-order vector jet slot. -/
def vectorLaplace (n : ℕ) :
    PDEJetSlot 2 (EuclideanℝN n) (EuclideanℝN n) →L[ℝ] EuclideanℝN n :=
  ∑ i : Fin n, jetD2Vec n n (euclidDir n i) (euclidDir n i)

/-- The operator `D(div 𝐮) = ∇(∇·𝐮) ∈ ℝⁿ`, whose `k`-th component is
`∑ⱼ uʲ_{xⱼxₖ}`. Built from the second-order slot by extracting, for each pair
`(j, k)`, the `j`-th component of `D²𝐮(eⱼ, eₖ)` and depositing it in coordinate
`k`. Linear in the second-order slot. -/
def gradDiv (n : ℕ) :
    PDEJetSlot 2 (EuclideanℝN n) (EuclideanℝN n) →L[ℝ] EuclideanℝN n :=
  ∑ j : Fin n, ∑ k : Fin n,
    ((EuclideanSpace.proj j).comp (jetD2Vec n n (euclidDir n j) (euclidDir n k))).smulRight
      (euclidDir n k)

/-- **Evans §1.2.2a, equilibrium equations of linear elasticity**
`μ Δ𝐮 + (λ + μ) D(div 𝐮) = 0` for the displacement `𝐮 : ℝⁿ → ℝⁿ`, with Lamé
constants `μ`, `λ`. A second-order linear system. -/
def linearElasticityEquilibriumSymbol (n : ℕ) (μ lam : ℝ) :
    PDEJet 2 (EuclideanℝN n) (EuclideanℝN n) → EuclideanℝN n → EuclideanℝN n :=
  fun ξ _ => μ • vectorLaplace n (ξ 2) + (lam + μ) • gradDiv n (ξ 2)

/-- Linear-system coefficients for the elasticity equilibrium equations: the
top-order (`j = 2`) coefficient is `μ Δ + (λ + μ) D∘div`, the lower coefficients
vanish. -/
def linearElasticityEquilibriumCoeff (n : ℕ) (μ lam : ℝ) :
    (j : Fin 3) → EuclideanℝN n →
      (PDEJetSlot (j : ℕ) (EuclideanℝN n) (EuclideanℝN n) →L[ℝ] EuclideanℝN n) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => fun _ => μ • vectorLaplace n + (lam + μ) • gradDiv n
  | ⟨p + 3, h⟩ => absurd h (by omega)

/-- **The equilibrium equations of linear elasticity form a linear (2nd-order)
system** (Evans Def. 2(i) for systems). -/
theorem linearElasticityEquilibriumSymbol_isLinearPDESystem (n : ℕ) (μ lam : ℝ) :
    IsLinearPDESystem n 2 (linearElasticityEquilibriumSymbol n μ lam) := by
  refine ⟨linearElasticityEquilibriumCoeff n μ lam, 0, ?_⟩
  intro ξ x
  show μ • vectorLaplace n (ξ 2) + (lam + μ) • gradDiv n (ξ 2)
    = (∑ j, linearElasticityEquilibriumCoeff n μ lam j x (ξ j))
      - (0 : EuclideanℝN n → EuclideanℝN n) x
  rw [Fin.sum_univ_three]
  have h0 : linearElasticityEquilibriumCoeff n μ lam 0 x (ξ 0) = 0 := rfl
  have h1 : linearElasticityEquilibriumCoeff n μ lam 1 x (ξ 1) = 0 := rfl
  have h2 : linearElasticityEquilibriumCoeff n μ lam 2 x (ξ 2)
      = μ • vectorLaplace n (ξ 2) + (lam + μ) • gradDiv n (ξ 2) := by
    show (μ • vectorLaplace n + (lam + μ) • gradDiv n) (ξ 2) = _
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply]
  rw [h0, h1, h2]
  simp

/-! ## Evolution equations of linear elasticity (Evans §1.2.2a) — linear system -/

/-- Order-`2` vector contraction `D²𝐮(x)(v, w) ∈ ℝᵐ` on space–time `ℝ^{n+1}`. -/
def jetD2VecST (n m : ℕ) (v w : SpaceTime n) :
    PDEJetSlot 2 (SpaceTime n) (EuclideanℝN m) →L[ℝ] EuclideanℝN m :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => SpaceTime n) (EuclideanℝN m) ![v, w]

/-- The **spatial** `D(div 𝐮) = ∇_x(∇_x·𝐮) ∈ ℝⁿ` on space–time, `k`-th component
`∑ⱼ uʲ_{xⱼxₖ}` (spatial indices only). Linear in the second-order slot. -/
def spatialGradDiv (n : ℕ) :
    PDEJetSlot 2 (SpaceTime n) (EuclideanℝN n) →L[ℝ] EuclideanℝN n :=
  ∑ j : Fin n, ∑ k : Fin n,
    ((EuclideanSpace.proj j).comp (jetD2VecST n n (spaceDir n j) (spaceDir n k))).smulRight
      (euclidDir n k)

/-- The **elastic operator** `𝐮 ↦ μ Δ_x𝐮 + (λ + μ) D(div 𝐮)` on space–time, as a
continuous linear functional of the second-order slot. -/
def elasticOperatorST (n : ℕ) (μ lam : ℝ) :
    PDEJetSlot 2 (SpaceTime n) (EuclideanℝN n) →L[ℝ] EuclideanℝN n :=
  μ • spatialLaplaceV n n + (lam + μ) • spatialGradDiv n

/-- **Evans §1.2.2a, evolution equations of linear elasticity**
`𝐮_t - μ Δ𝐮 - (λ + μ) D(div 𝐮) = 0` for `𝐮 : ℝ^{n+1} → ℝⁿ`. A second-order
linear system. -/
def linearElasticityEvolutionSymbol (n : ℕ) (μ lam : ℝ) :
    PDEJet 2 (SpaceTime n) (EuclideanℝN n) → SpaceTime n → EuclideanℝN n :=
  fun ξ _ => timeD1V n n (ξ 1) - elasticOperatorST n μ lam (ξ 2)

/-- Linear-system coefficients for the elasticity evolution equations: the
first-order coefficient is `∂_t`, the second-order coefficient is `-(μΔ + (λ+μ)D∘div)`. -/
def linearElasticityEvolutionCoeff (n : ℕ) (μ lam : ℝ) :
    (j : Fin 3) → SpaceTime n →
      (PDEJetSlot (j : ℕ) (SpaceTime n) (EuclideanℝN n) →L[ℝ] EuclideanℝN n) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1V n n
  | ⟨2, _⟩ => fun _ => -elasticOperatorST n μ lam
  | ⟨p + 3, h⟩ => absurd h (by omega)

/-- **The evolution equations of linear elasticity form a linear (2nd-order)
system** (Evans Def. 2(i) for systems). -/
theorem linearElasticityEvolutionSymbol_isLinearPDESystem (n : ℕ) (μ lam : ℝ) :
    IsLinearPDESystem n 2 (linearElasticityEvolutionSymbol n μ lam) := by
  refine ⟨linearElasticityEvolutionCoeff n μ lam, 0, ?_⟩
  intro ξ x
  show timeD1V n n (ξ 1) - elasticOperatorST n μ lam (ξ 2)
    = (∑ j, linearElasticityEvolutionCoeff n μ lam j x (ξ j))
      - (0 : SpaceTime n → EuclideanℝN n) x
  rw [Fin.sum_univ_three]
  have h0 : linearElasticityEvolutionCoeff n μ lam 0 x (ξ 0) = 0 := rfl
  have h1 : linearElasticityEvolutionCoeff n μ lam 1 x (ξ 1) = timeD1V n n (ξ 1) := rfl
  have h2 : linearElasticityEvolutionCoeff n μ lam 2 x (ξ 2)
      = -elasticOperatorST n μ lam (ξ 2) := by
    show (-elasticOperatorST n μ lam) (ξ 2) = _
    rw [ContinuousLinearMap.neg_apply]
  rw [h0, h1, h2]
  simp [sub_eq_add_neg]

/-! ## Schrödinger's equation as a real system (Evans §1.2.1a) — linear system

Evans lists Schrödinger's equation `i u_t + Δu = 0` among the linear equations.
It is complex-valued; writing `u = u¹ + i u²` splits it into the real linear
`2 × 2` system
`Δu¹ - u²_t = 0`, `Δu² + u¹_t = 0`,
i.e. `Δ𝐮 + i·𝐮_t = 0` with `i` acting as the rotation `(a, b) ↦ (-b, a)` on `ℝ²`.
This realizes the complex equation faithfully within the real system framework. -/

/-- Multiplication by `i` on `ℝ² ≅ ℂ`, as the rotation `(a, b) ↦ (-b, a)`. -/
def rot2 : EuclideanℝN 2 →L[ℝ] EuclideanℝN 2 :=
  -(EuclideanSpace.proj (1 : Fin 2) : EuclideanℝN 2 →L[ℝ] ℝ).smulRight (euclidDir 2 0)
    + (EuclideanSpace.proj (0 : Fin 2) : EuclideanℝN 2 →L[ℝ] ℝ).smulRight (euclidDir 2 1)

/-- **Evans §1.2.1a, Schrödinger's equation** `i u_t + Δu = 0`, realized as the
real linear system `Δ𝐮 + i·𝐮_t = 0` for `𝐮 = (u¹, u²) : ℝ^{n+1} → ℝ²`
(`u = u¹ + i u²`). Second order, linear. -/
def schrodingerSystemSymbol (n : ℕ) :
    PDEJet 2 (SpaceTime n) (EuclideanℝN 2) → SpaceTime n → EuclideanℝN 2 :=
  fun ξ _ => spatialLaplaceV n 2 (ξ 2) + rot2 (timeD1V n 2 (ξ 1))

/-- Homogeneous-linear-system coefficients for Schrödinger's equation. -/
def schrodingerSystemCoeff (n : ℕ) :
    (j : Fin 3) → SpaceTime n →
      (PDEJetSlot (j : ℕ) (SpaceTime n) (EuclideanℝN 2) →L[ℝ] EuclideanℝN 2) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => rot2.comp (timeD1V n 2)
  | ⟨2, _⟩ => fun _ => spatialLaplaceV n 2
  | ⟨p + 3, h⟩ => absurd h (by omega)

/-- **Schrödinger's equation is a homogeneous linear (2nd-order) system** (Evans
Def. 2(i) for systems). -/
theorem schrodingerSystemSymbol_isHomogeneousLinearPDESystem (n : ℕ) :
    IsHomogeneousLinearPDESystem 2 2 (schrodingerSystemSymbol n) := by
  refine ⟨schrodingerSystemCoeff n, ?_⟩
  intro ξ x
  show spatialLaplaceV n 2 (ξ 2) + rot2 (timeD1V n 2 (ξ 1))
    = ∑ j, schrodingerSystemCoeff n j x (ξ j)
  rw [Fin.sum_univ_three]
  have h0 : schrodingerSystemCoeff n 0 x (ξ 0) = 0 := rfl
  have h1 : schrodingerSystemCoeff n 1 x (ξ 1) = rot2 (timeD1V n 2 (ξ 1)) := by
    show (rot2.comp (timeD1V n 2)) (ξ 1) = _
    rw [ContinuousLinearMap.comp_apply]
  have h2 : schrodingerSystemCoeff n 2 x (ξ 2) = spatialLaplaceV n 2 (ξ 2) := rfl
  rw [h0, h1, h2, zero_add]
  exact add_comm _ _

/-- Schrödinger's equation is, in particular, a linear system. -/
theorem schrodingerSystemSymbol_isLinearPDESystem (n : ℕ) :
    IsLinearPDESystem 2 2 (schrodingerSystemSymbol n) :=
  (schrodingerSystemSymbol_isHomogeneousLinearPDESystem n).isLinearPDESystem

end EvansLib
