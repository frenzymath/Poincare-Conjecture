import PetersenLib.Ch01.TensorConcepts
import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-!
# Petersen Ch. 2, §2.3.1 — Endomorphisms as Derivations

Pointwise linear algebra on a finite-dimensional real vector space `V` (no manifolds):
the natural `GL(V)`-action on tensors, its derivative — the action of endomorphisms
`L ∈ End(V)` as derivations — and the interaction with tensor inner products.

* `IsTensorDerivation`: a derivation on tensors, recorded through its components on
  scalars, vectors, covectors and `(0,k)`-tensors (blueprint
  `def:pet-ch2-tensor-derivation`).
* `glActionOnTensorAlgebra` (with `glActionOnDual`): the natural `GL(V)`-action
  `(g • T)(v₁, …, v_k) = T(g⁻¹v₁, …, g⁻¹v_k)`, with the action laws
  `glActionOnTensorAlgebra_one` / `glActionOnTensorAlgebra_mul`
  (blueprint `def:pet-ch2-gl-action-tensor-algebra`).
* `endomorphismDerivation`: the induced derivation
  `(L T)(v₁, …, v_k) = -∑ i, T(v₁, …, L vᵢ, …, v_k)` of `L ∈ End(V)`, a tensor
  derivation by `endomorphismDerivation_isTensorDerivation`
  (blueprint `def:pet-ch2-endomorphism-derivation`).
* Prop. 2.3.1 (`endomorphismDerivation_lieAlgebraHom`): `L ↦ (L·)` is a Lie algebra
  homomorphism; it preserves symmetries of tensors
  (`endomorphismDerivation_domDomCongr_eq_self`).
* Prop. 2.3.2 (`endomorphismAction_isDerivation`): the action of a `(1,1)`-tensor is a
  derivation — Leibniz rule for the outer product `formTensorMul` and commutation with
  the `(1,1)`-contraction (`trace_endomorphismDerivationOneOne`).
* `tensorAlgebraInnerProduct`: the inner product on `(0,k)`-tensors induced by an
  orthonormal basis of `V`, with Petersen's defining orthonormality
  `tensorAlgebraInnerProduct_coframeProdForm`
  (blueprint `def:pet-ch2-tensor-algebra-inner-product`).
* Prop. 2.3.3 (`endomorphismDerivation_adjoint_skew`): the adjoint of `L` acting on
  tensors is the action of the adjoint `L†`, and skew-adjoint endomorphisms commute
  with type change of tensors.

Design scope: as in `PetersenLib.Ch01.TensorConcepts`, full mixed `(s,t)`-tensor powers
are not built; the covariant tensors are `MultilinearMap ℝ (fun _ : Fin k => V) ℝ`,
`(1,1)`-tensors are `V →ₗ[ℝ] V` and `(0,2)`-tensors in curried form are
`V →ₗ[ℝ] V →ₗ[ℝ] ℝ`, connected through `lowerIndex`/`raiseIndex`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.3.1.
-/

open scoped InnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## Derivations on tensors -/

section TensorDerivation

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Petersen §2.3.1 (derivation on tensors): a *derivation* on tensors is a
type-preserving linear map `T ↦ D T` that commutes with contractions and satisfies the
product rule `D(T₁ ⊗ T₂) = (D T₁) ⊗ T₂ + T₁ ⊗ (D T₂)`.

Realization: full mixed `(s,t)`-tensor powers are not built (see the design scope of
`PetersenLib.Ch01.TensorConcepts`), so the derivation is recorded through its components
on the tensor types used in Petersen Ch. 1–3: scalars `ℝ`, vectors `V`, covectors
`Module.Dual ℝ V`, and `(0,k)`-tensors. Linearity of each component is imposed by the
bundled types of the parameters; the fields state that

* scalars are annihilated (`map_scalar`),
* `D` is Leibniz for the duality pairing, `D(φ(v)) = (Dφ)(v) + φ(Dv)` — i.e. `D` commutes
  with the `(1,1) → (0,0)` contraction of `v ⊗ φ` (`dual_contraction`), and
* `D` is Leibniz against the full contraction of `T ⊗ v₁ ⊗ ⋯ ⊗ v_k`:
  `(D T)(v₁, …, v_k) = D(T(v₁, …, v_k)) - ∑ i, T(v₁, …, D vᵢ, …, v_k)`
  (`form_contraction`).

This is precisely the shape in which Petersen applies derivations to tensors later on. -/
structure IsTensorDerivation (Dscalar : ℝ → ℝ) (Dvec : V →ₗ[ℝ] V)
    (Dcovec : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V)
    (Dform : ∀ k : ℕ, MultilinearMap ℝ (fun _ : Fin k => V) ℝ →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin k => V) ℝ) : Prop where
  map_scalar : ∀ a : ℝ, Dscalar a = 0
  dual_contraction : ∀ (φ : Module.Dual ℝ V) (v : V),
    Dscalar (φ v) = Dcovec φ v + φ (Dvec v)
  form_contraction : ∀ (k : ℕ) (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ)
    (v : Fin k → V),
    Dform k T v = Dscalar (T v) - ∑ i, T (Function.update v i (Dvec (v i)))

end TensorDerivation

/-! ## The natural `GL(V)`-action on tensors -/

section GLAction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Petersen §2.3.1 (the natural `GL(V)`-action on `T(V)`): `g ∈ GL(V)`
(realized as `V ≃ₗ[ℝ] V`) acts on tensors by `g • α = α` on scalars, `g • v = g(v)` on
vectors, `g • φ = φ ∘ g⁻¹` on covectors (`glActionOnDual`), and on `(0,k)`-tensors by
`(g • T)(v₁, …, v_k) = T(g⁻¹ v₁, …, g⁻¹ v_k)`, which is this definition. Together with
`glActionOnTensorAlgebra_one` and `glActionOnTensorAlgebra_mul` (and linearity,
`glActionOnTensorAlgebra_add`/`_smul`) this is the natural homomorphism
`GL(V) → GL(T(V))` on the covariant part of the tensor algebra. -/
def glActionOnTensorAlgebra (g : V ≃ₗ[ℝ] V) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    MultilinearMap ℝ (fun _ : Fin k => V) ℝ :=
  T.compLinearMap fun _ => (g.symm : V →ₗ[ℝ] V)

@[simp]
theorem glActionOnTensorAlgebra_apply (g : V ≃ₗ[ℝ] V) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) (v : Fin k → V) :
    glActionOnTensorAlgebra g T v = T fun i => g.symm (v i) :=
  rfl

/-- **Math.** Petersen §2.3.1: the `GL(V)`-action on covectors, `g • φ = φ ∘ g⁻¹`. -/
def glActionOnDual (g : V ≃ₗ[ℝ] V) : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V :=
  (g.symm : V →ₗ[ℝ] V).dualMap

@[simp]
theorem glActionOnDual_apply (g : V ≃ₗ[ℝ] V) (φ : Module.Dual ℝ V) (v : V) :
    glActionOnDual g φ v = φ (g.symm v) :=
  rfl

/-- **Math.** The identity of `GL(V)` acts as the identity: `1 • T = T`. -/
theorem glActionOnTensorAlgebra_one {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    glActionOnTensorAlgebra 1 T = T :=
  MultilinearMap.ext fun _ => rfl

/-- **Math.** Petersen §2.3.1: `GL(V) → GL(T(V))` is multiplicative — the action law
`(g₁ g₂) • T = g₁ • (g₂ • T)`, using `(g₁ g₂)⁻¹ = g₂⁻¹ g₁⁻¹` slotwise. -/
theorem glActionOnTensorAlgebra_mul (g₁ g₂ : V ≃ₗ[ℝ] V) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    glActionOnTensorAlgebra (g₁ * g₂) T =
      glActionOnTensorAlgebra g₁ (glActionOnTensorAlgebra g₂ T) :=
  MultilinearMap.ext fun _ => rfl

/-- **Math.** `g • (T₁ + T₂) = g • T₁ + g • T₂`: each `g` acts linearly on
`(0,k)`-tensors, so the action lands in `GL` of the tensor space. -/
theorem glActionOnTensorAlgebra_add (g : V ≃ₗ[ℝ] V) {k : ℕ}
    (T₁ T₂ : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    glActionOnTensorAlgebra g (T₁ + T₂) =
      glActionOnTensorAlgebra g T₁ + glActionOnTensorAlgebra g T₂ :=
  MultilinearMap.ext fun _ => rfl

theorem glActionOnTensorAlgebra_smul (g : V ≃ₗ[ℝ] V) (c : ℝ) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    glActionOnTensorAlgebra g (c • T) = c • glActionOnTensorAlgebra g T :=
  MultilinearMap.ext fun _ => rfl

/-- **Math.** Petersen §2.3.1: `GL(V)` acts trivially on scalars, `g • α = α` — the
`(0,0)`-tensors are the multilinear maps with no slots. -/
theorem glActionOnTensorAlgebra_scalar (g : V ≃ₗ[ℝ] V)
    (T : MultilinearMap ℝ (fun _ : Fin 0 => V) ℝ) :
    glActionOnTensorAlgebra g T = T :=
  MultilinearMap.ext fun _ => congrArg T (funext fun i => i.elim0)

end GLAction

/-! ## The induced derivation of an endomorphism -/

section EndomorphismDerivation

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Petersen §2.3.1 (induced derivation of `L ∈ End(V)`): differentiating the
`GL(V)`-action `glActionOnTensorAlgebra` at `t = 0` along `t ↦ exp(tL)` (so that
`g⁻¹`-slots contribute `-L`) gives a linear map `End(V) → End(T(V))`, `L ↦ (L T)`: on
vectors `L v`, on covectors `-φ ∘ L`, on scalars `0`, and on `(0,k)`-tensors

`(L T)(v₁, …, v_k) = -∑ i, T(v₁, …, L vᵢ, …, v_k)`,

which is this definition (`endomorphismDerivation_apply`); the differentiation itself is
not formalized. -/
def endomorphismDerivation (L : V →ₗ[ℝ] V) (k : ℕ) :
    MultilinearMap ℝ (fun _ : Fin k => V) ℝ →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin k => V) ℝ :=
  -∑ i : Fin k, MultilinearMap.compLinearMapₗ
    (Function.update (fun _ : Fin k => (LinearMap.id : V →ₗ[ℝ] V)) i L)

/-- **Math.** The defining slot formula
`(L T)(v₁, …, v_k) = -∑ i, T(v₁, …, L vᵢ, …, v_k)`. -/
theorem endomorphismDerivation_apply (L : V →ₗ[ℝ] V) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) (v : Fin k → V) :
    endomorphismDerivation L k T v = -∑ i, T (Function.update v i (L (v i))) := by
  have h : ∀ i : Fin k,
      (fun j => Function.update (fun _ : Fin k => (LinearMap.id : V →ₗ[ℝ] V)) i L j (v j)) =
        Function.update v i (L (v i)) := by
    intro i
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [Function.update_of_ne hj]
  simp only [endomorphismDerivation, LinearMap.neg_apply, LinearMap.coe_sum,
    Finset.sum_apply, MultilinearMap.neg_apply, MultilinearMap.sum_apply,
    MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply, h]

/-- **Math.** Petersen §2.3.1: on scalars (`(0,0)`-tensors) the induced derivation
vanishes, `L α = 0`. -/
theorem endomorphismDerivation_scalar (L : V →ₗ[ℝ] V) :
    endomorphismDerivation L 0 = 0 := by
  ext T v
  rw [endomorphismDerivation_apply]
  simp

/-- **Math.** Petersen §2.3.1: the action of `L ∈ End(V)` on tensors — on scalars `0`,
on vectors `L`, on covectors `φ ↦ -φ ∘ L` (i.e. `-L.dualMap`), on `(0,k)`-tensors
`endomorphismDerivation` — is a derivation in the sense of `IsTensorDerivation`. This is
part of Prop. 2.3.2 (see `endomorphismAction_isDerivation` for the product rule and the
`(1,1)`-contraction). -/
theorem endomorphismDerivation_isTensorDerivation (L : V →ₗ[ℝ] V) :
    IsTensorDerivation (fun _ : ℝ => 0) L (-L.dualMap) (endomorphismDerivation L) where
  map_scalar _ := rfl
  dual_contraction φ v := by simp
  form_contraction k T v := by simp [endomorphismDerivation_apply]

end EndomorphismDerivation

/-! ## Prop. 2.3.1: `L ↦ (L ·)` is a Lie algebra homomorphism preserving symmetries -/

section LieAlgebraHom

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Eng.** Composition formula: applying two induced derivations gives a diagonal term
(with the composite endomorphism) plus an off-diagonal double sum. -/
private theorem endomorphismDerivation_comp_apply (L₁ L₂ : V →ₗ[ℝ] V) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) (v : Fin k → V) :
    endomorphismDerivation L₁ k (endomorphismDerivation L₂ k T) v =
      ∑ i, T (Function.update v i (L₂ (L₁ (v i)))) +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          T (Function.update (Function.update v i (L₁ (v i))) j (L₂ (v j))) := by
  rw [endomorphismDerivation_apply]
  simp only [endomorphismDerivation_apply, Finset.sum_neg_distrib, neg_neg]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · rw [Function.update_self, Function.update_idem]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Math.** Petersen Prop. 2.3.1 (first half): `L ↦ (L ·)` is a **Lie algebra
homomorphism** `End(V) = 𝔤𝔩(V) → End(T(V))` — on `(0,k)`-tensors,
`[L₁, L₂] T = L₁ (L₂ T) - L₂ (L₁ T)` where `[L₁, L₂] = L₁ ∘ L₂ - L₂ ∘ L₁`.
The proof matches diagonal terms and cancels the two off-diagonal double sums against
each other by swapping the two updated slots. -/
theorem endomorphismDerivation_lieAlgebraHom (L₁ L₂ : V →ₗ[ℝ] V) (k : ℕ) :
    endomorphismDerivation (L₁ ∘ₗ L₂ - L₂ ∘ₗ L₁) k =
      endomorphismDerivation L₁ k ∘ₗ endomorphismDerivation L₂ k -
        endomorphismDerivation L₂ k ∘ₗ endomorphismDerivation L₁ k := by
  ext T v
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, MultilinearMap.sub_apply]
  rw [endomorphismDerivation_comp_apply, endomorphismDerivation_comp_apply,
    endomorphismDerivation_apply]
  have hswap : (∑ i, ∑ j ∈ Finset.univ.erase i,
        T (Function.update (Function.update v i (L₁ (v i))) j (L₂ (v j)))) =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        T (Function.update (Function.update v i (L₂ (v i))) j (L₁ (v j))) := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun i => Finset.univ.erase i)
      (s' := fun j => Finset.univ.erase j) (t' := Finset.univ)
      (fun i j => by simp [Finset.mem_erase, ne_comm])]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_comm (Finset.ne_of_mem_erase hj).symm]
  rw [hswap]
  have hdiag : ∀ i : Fin k, T (Function.update v i ((L₁ ∘ₗ L₂ - L₂ ∘ₗ L₁) (v i))) =
      T (Function.update v i (L₁ (L₂ (v i)))) - T (Function.update v i (L₂ (L₁ (v i)))) := by
    intro i
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      MultilinearMap.map_update_sub]
  simp only [hdiag]
  rw [Finset.sum_sub_distrib]
  ring

/-- **Eng.** Equivariance of the induced derivation under permutations of the slots:
`L (T ∘ σ) = (L T) ∘ σ` for `σ ∈ Perm (Fin k)` (acting by `domDomCongr`). -/
theorem endomorphismDerivation_domDomCongr (L : V →ₗ[ℝ] V) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    endomorphismDerivation L k (T.domDomCongr σ) =
      (endomorphismDerivation L k T).domDomCongr σ := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply, endomorphismDerivation_apply]
  congr 1
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · rw [Function.update_of_ne (σ.injective.ne hj), Function.update_of_ne hj]

/-- **Math.** Petersen Prop. 2.3.1 (second half): the induced derivation **preserves
symmetries of tensors** — if `T` is invariant under a permutation `σ` of its slots
(e.g. a transposition, for symmetric or alternating `T`), then so is `L T`. -/
theorem endomorphismDerivation_domDomCongr_eq_self (L : V →ₗ[ℝ] V) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ)
    (hT : T.domDomCongr σ = T) :
    (endomorphismDerivation L k T).domDomCongr σ = endomorphismDerivation L k T := by
  rw [← endomorphismDerivation_domDomCongr, hT]

end LieAlgebraHom

/-! ## Prop. 2.3.2: `(1,1)`-tensors act as derivations -/

section Derivation

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section UpdateLemmas

variable {α : Type*} {k₁ k₂ : ℕ}

private theorem update_castAdd_natAdd (v : Fin (k₁ + k₂) → α) (i : Fin k₁) (x : α) :
    (fun j => Function.update v (Fin.castAdd k₂ i) x (Fin.natAdd k₁ j)) =
      fun j => v (Fin.natAdd k₁ j) := by
  funext j
  refine Function.update_of_ne (fun h => ?_) _ _
  have hj := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hj
  omega

private theorem update_natAdd_castAdd (v : Fin (k₁ + k₂) → α) (j : Fin k₂) (x : α) :
    (fun i => Function.update v (Fin.natAdd k₁ j) x (Fin.castAdd k₂ i)) =
      fun i => v (Fin.castAdd k₂ i) := by
  funext i
  refine Function.update_of_ne (fun h => ?_) _ _
  have hi := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hi
  omega

private theorem update_castAdd_comp (v : Fin (k₁ + k₂) → α) (i : Fin k₁) (x : α) :
    (fun i' => Function.update v (Fin.castAdd k₂ i) x (Fin.castAdd k₂ i')) =
      Function.update (fun i' => v (Fin.castAdd k₂ i')) i x := by
  funext i'
  rcases eq_or_ne i' i with rfl | h
  · simp
  · rw [Function.update_of_ne (fun hc => h (Fin.castAdd_injective _ _ hc)),
      Function.update_of_ne h]

private theorem update_natAdd_comp (v : Fin (k₁ + k₂) → α) (j : Fin k₂) (x : α) :
    (fun j' => Function.update v (Fin.natAdd k₁ j) x (Fin.natAdd k₁ j')) =
      Function.update (fun j' => v (Fin.natAdd k₁ j')) j x := by
  funext j'
  rcases eq_or_ne j' j with rfl | h
  · simp
  · rw [Function.update_of_ne (fun hc => h (Fin.natAdd_injective _ _ hc)),
      Function.update_of_ne h]

end UpdateLemmas

/-- **Math.** The outer (tensor) product of covariant tensors:
`(T₁ ⊗ T₂)(v₁, …, v_{k₁}, w₁, …, w_{k₂}) = T₁(v₁, …, v_{k₁}) ⬝ T₂(w₁, …, w_{k₂})`, the
pointwise analogue of `TensorOperator.mul` in `PetersenLib.Ch02.LieDerivative` (slots
split by `Fin.castAdd`/`Fin.natAdd`). -/
def formTensorMul {k₁ k₂ : ℕ} (T₁ : MultilinearMap ℝ (fun _ : Fin k₁ => V) ℝ)
    (T₂ : MultilinearMap ℝ (fun _ : Fin k₂ => V) ℝ) :
    MultilinearMap ℝ (fun _ : Fin (k₁ + k₂) => V) ℝ :=
  ((TensorProduct.lid ℝ ℝ).toLinearMap.compMultilinearMap (T₁.domCoprod T₂)).domDomCongr
    finSumFinEquiv

theorem formTensorMul_apply {k₁ k₂ : ℕ} (T₁ : MultilinearMap ℝ (fun _ : Fin k₁ => V) ℝ)
    (T₂ : MultilinearMap ℝ (fun _ : Fin k₂ => V) ℝ) (v : Fin (k₁ + k₂) → V) :
    formTensorMul T₁ T₂ v =
      (T₁ fun i => v (Fin.castAdd k₂ i)) * T₂ fun j => v (Fin.natAdd k₁ j) := by
  simp [formTensorMul, MultilinearMap.domDomCongr_apply,
    LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
    TensorProduct.lid_tmul, smul_eq_mul, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]

/-- **Math.** Petersen Prop. 2.3.2 (product rule): the action of `L ∈ End(V)` on
`(0,k)`-tensors satisfies the Leibniz rule for the outer product,
`L (T₁ ⊗ T₂) = (L T₁) ⊗ T₂ + T₁ ⊗ (L T₂)`. -/
theorem endomorphismDerivation_formTensorMul (L : V →ₗ[ℝ] V) {k₁ k₂ : ℕ}
    (T₁ : MultilinearMap ℝ (fun _ : Fin k₁ => V) ℝ)
    (T₂ : MultilinearMap ℝ (fun _ : Fin k₂ => V) ℝ) :
    endomorphismDerivation L (k₁ + k₂) (formTensorMul T₁ T₂) =
      formTensorMul (endomorphismDerivation L k₁ T₁) T₂ +
        formTensorMul T₁ (endomorphismDerivation L k₂ T₂) := by
  ext v
  simp only [MultilinearMap.add_apply, endomorphismDerivation_apply, formTensorMul_apply]
  rw [Fin.sum_univ_add]
  simp only [update_castAdd_comp, update_castAdd_natAdd, update_natAdd_comp,
    update_natAdd_castAdd]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- **Math.** Petersen §2.3.1 / Prop. 2.3.2: the induced action of `L ∈ End(V)` on a
`(1,1)`-tensor `S` (also an endomorphism) is the **commutator** `L S = [L, S] = L∘S - S∘L`
— the slot in `V` contributes `L ∘ S` and the dual slot contributes `-S ∘ L`. -/
def endomorphismDerivationOneOne (L S : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  L ∘ₗ S - S ∘ₗ L

/-- **Math.** Petersen Prop. 2.3.2 (commutation with contractions): the action of `L`
commutes with the `(1,1) → (0,0)` contraction — since scalars are annihilated,
`tr (L S) = tr [L, S] = 0 (= L (tr S))`. This is Petersen's frame computation
`T^i_j L^k_i - T^k_j L^j_i` contracted over `k = j`; here it is `tr(LS) = tr(SL)`. -/
theorem trace_endomorphismDerivationOneOne (L S : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ V (endomorphismDerivationOneOne L S) = 0 := by
  rw [endomorphismDerivationOneOne, map_sub, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp, LinearMap.trace_mul_comm, sub_self]

/-- **Math.** Petersen Prop. 2.3.2: any `(1,1)`-tensor `L` defines a **derivation** on
tensors: the Leibniz rule `L (T₁ ⊗ T₂) = (L T₁) ⊗ T₂ + T₁ ⊗ (L T₂)` for the outer
product of covariant tensors, and commutation with the `(1,1)`-contraction (trace):
`tr (L S) = tr [L, S] = 0`, which equals `L (tr S)` since scalars are annihilated
(`endomorphismDerivation_scalar`). Linearity is part of the bundled types, and the
components form a tensor derivation by `endomorphismDerivation_isTensorDerivation`. -/
theorem endomorphismAction_isDerivation (L : V →ₗ[ℝ] V) {k₁ k₂ : ℕ}
    (T₁ : MultilinearMap ℝ (fun _ : Fin k₁ => V) ℝ)
    (T₂ : MultilinearMap ℝ (fun _ : Fin k₂ => V) ℝ) (S : V →ₗ[ℝ] V) :
    endomorphismDerivation L (k₁ + k₂) (formTensorMul T₁ T₂) =
        formTensorMul (endomorphismDerivation L k₁ T₁) T₂ +
          formTensorMul T₁ (endomorphismDerivation L k₂ T₂) ∧
      LinearMap.trace ℝ V (endomorphismDerivationOneOne L S) = 0 :=
  ⟨endomorphismDerivation_formTensorMul L T₁ T₂, trace_endomorphismDerivationOneOne L S⟩

/-- **Math.** The induced action of `L` on `(0,2)`-tensors in curried form
(`V →ₗ[ℝ] V →ₗ[ℝ] ℝ`, as in `PetersenLib.Ch01.TensorConcepts`): the slotwise formula
`(L B)(v, w) = -(B(Lv, w) + B(v, Lw))`, the `k = 2` instance of
`endomorphismDerivation`. -/
def endomorphismDerivationBilin (L : V →ₗ[ℝ] V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  -(B ∘ₗ L + B.compl₂ L)

@[simp]
theorem endomorphismDerivationBilin_apply (L : V →ₗ[ℝ] V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (v w : V) :
    endomorphismDerivationBilin L B v w = -(B (L v) w + B v (L w)) := by
  simp [endomorphismDerivationBilin]

end Derivation

/-! ## The inner product on the tensor algebra -/

section TensorInnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]

/-- **Math.** Petersen §2.3.1 (inner product on the tensor algebra): given an
orthonormal basis `e₁, …, e_n` of `V`, the induced inner product on `(0,k)`-tensors is
`⟨T₁, T₂⟩ = ∑_{i₁, …, i_k} T₁(e_{i₁}, …, e_{i_k}) ⬝ T₂(e_{i₁}, …, e_{i_k})`; under it
the coframe products `e^{i₁} ⊗ ⋯ ⊗ e^{i_k}` are an orthonormal basis
(`tensorAlgebraInnerProduct_coframeProdForm`), which is Petersen's defining declaration.

Design scope: the definition is taken with respect to the chosen orthonormal basis `b`
(basis-invariance is not formalized here); for `k = 2` it agrees with the basis-free
`pointwiseTensorInnerProduct` of `PetersenLib.Ch01.TensorConcepts` by
`tensorAlgebraInnerProduct_eq_pointwiseTensorInnerProduct`, which proves invariance in
the only case used. -/
def tensorAlgebraInnerProduct (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (T₁ T₂ : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) : ℝ :=
  ∑ f : Fin k → ι, T₁ (fun i => b (f i)) * T₂ (fun i => b (f i))

omit [FiniteDimensional ℝ V] in
theorem tensorAlgebraInnerProduct_comm (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (T₁ T₂ : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    tensorAlgebraInnerProduct b T₁ T₂ = tensorAlgebraInnerProduct b T₂ T₁ := by
  unfold tensorAlgebraInnerProduct
  exact Finset.sum_congr rfl fun f _ => mul_comm _ _

omit [FiniteDimensional ℝ V] in
theorem tensorAlgebraInnerProduct_self_nonneg (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    0 ≤ tensorAlgebraInnerProduct b T T := by
  unfold tensorAlgebraInnerProduct
  exact Finset.sum_nonneg fun f _ => mul_self_nonneg _

/-- **Math.** The elementary covariant tensor `e^{f(1)} ⊗ ⋯ ⊗ e^{f(k)}`: the product of
coframe `1`-forms `v ↦ ∏ i, ⟪e_{f(i)}, vᵢ⟫`, the `(0,k)` analogue of Ch. 1's
`tensorProdForm`. -/
def coframeProdForm (b : OrthonormalBasis ι ℝ V) {k : ℕ} (f : Fin k → ι) :
    MultilinearMap ℝ (fun _ : Fin k => V) ℝ :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compLinearMap fun i => innerₗ V (b (f i))

omit [FiniteDimensional ℝ V] in
@[simp]
theorem coframeProdForm_apply (b : OrthonormalBasis ι ℝ V) {k : ℕ} (f : Fin k → ι)
    (v : Fin k → V) :
    coframeProdForm b f v = ∏ i, ⟪b (f i), v i⟫_ℝ := by
  simp [coframeProdForm]

omit [FiniteDimensional ℝ V] in
/-- **Math.** Petersen §2.3.1: the coframe products `e^{i₁} ⊗ ⋯ ⊗ e^{i_k}` of an
orthonormal basis are **orthonormal** for `tensorAlgebraInnerProduct` — Petersen's
defining declaration for the inner product on the tensor algebra, on the covariant
part. -/
theorem tensorAlgebraInnerProduct_coframeProdForm [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ V) {k : ℕ} (f g : Fin k → ι) :
    tensorAlgebraInnerProduct b (coframeProdForm b f) (coframeProdForm b g) =
      if f = g then 1 else 0 := by
  unfold tensorAlgebraInnerProduct
  simp only [coframeProdForm_apply]
  have hprod : ∀ h : Fin k → ι,
      (∏ i, ⟪b (f i), b (h i)⟫_ℝ) * ∏ i, ⟪b (g i), b (h i)⟫_ℝ =
        ∏ i, ⟪b (f i), b (h i)⟫_ℝ * ⟪b (g i), b (h i)⟫_ℝ :=
    fun h => Finset.prod_mul_distrib.symm
  simp_rw [hprod]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset ι))
      (fun i x => ⟪b (f i), b x⟫_ℝ * ⟪b (g i), b x⟫_ℝ)]
  have hsum : ∀ i : Fin k, (∑ x : ι, ⟪b (f i), b x⟫_ℝ * ⟪b (g i), b x⟫_ℝ) =
      if f i = g i then (1 : ℝ) else 0 := by
    intro i
    have hcomm : ∀ x : ι, ⟪b (f i), b x⟫_ℝ * ⟪b (g i), b x⟫_ℝ =
        ⟪b (f i), b x⟫_ℝ * ⟪b x, b (g i)⟫_ℝ :=
      fun x => by rw [real_inner_comm (b (g i)) (b x)]
    simp_rw [hcomm]
    rw [b.sum_inner_mul_inner]
    exact orthonormal_iff_ite.mp b.orthonormal (f i) (g i)
  simp_rw [hsum]
  by_cases hfg : f = g
  · subst hfg
    simp
  · rw [if_neg hfg]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hfg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **Math.** Consistency with Ch. 1: for `k = 2` the basis-dependent
`tensorAlgebraInnerProduct` agrees with the basis-free `pointwiseTensorInnerProduct` of
`PetersenLib.Ch01.TensorConcepts` (through the curried encoding of `(0,2)`-tensors); in
particular it is basis-independent in this case. -/
theorem tensorAlgebraInnerProduct_eq_pointwiseTensorInnerProduct
    (b : OrthonormalBasis ι ℝ V) (T₁ T₂ : MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ)
    (B₁ B₂ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h₁ : ∀ v w : V, T₁ ![v, w] = B₁ v w)
    (h₂ : ∀ v w : V, T₂ ![v, w] = B₂ v w) :
    tensorAlgebraInnerProduct b T₁ T₂ = pointwiseTensorInnerProduct B₁ B₂ := by
  rw [pointwiseTensorInnerProduct_eq_sum b]
  unfold tensorAlgebraInnerProduct
  rw [← Equiv.sum_comp (piFinTwoEquiv fun _ : Fin 2 => ι).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hb : (fun t => b ((piFinTwoEquiv fun _ : Fin 2 => ι).symm (i, j) t)) =
      ![b i, b j] := by
    funext t
    fin_cases t <;> rfl
  rw [hb, h₁, h₂]

end TensorInnerProduct

/-! ## Prop. 2.3.3: adjoints, and skew-adjoint endomorphisms commute with type change -/

section AdjointSkew

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ V] in
/-- **Eng.** Expanding one slot of a multilinear map over an orthonormal basis
(Parseval slotwise). -/
private theorem map_update_eq_sum_inner (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) (w : Fin k → V) (i : Fin k) (u : V) :
    T (Function.update w i u) = ∑ x : ι, ⟪b x, u⟫_ℝ * T (Function.update w i (b x)) := by
  have h : T (Function.update w i u) = T.toLinearMap w i u := rfl
  rw [h]
  conv_lhs => rw [← b.sum_repr' u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply]

/-- **Eng.** The involutive reindexing `(f, x) ↦ (f[i ↦ x], f i)` of multi-indices used
to move an endomorphism from one factor of the tensor inner product to the other. -/
private def updateSlotEquiv {ι : Type*} {k : ℕ} (i : Fin k) :
    Equiv.Perm ((Fin k → ι) × ι) :=
  Function.Involutive.toPerm (fun p => (Function.update p.1 i p.2, p.1 i)) fun p => by
    simp [Function.update_idem, Function.update_eq_self]

/-- **Eng.** Moving `L` across the tensor inner product in one fixed slot `i` turns it
into `L†`. -/
private theorem sum_update_adjoint_slot (b : OrthonormalBasis ι ℝ V) (L : V →ₗ[ℝ] V)
    {k : ℕ} (T₁ T₂ : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) (i : Fin k) :
    ∑ f : Fin k → ι,
        T₁ (Function.update (fun j => b (f j)) i (L (b (f i)))) * T₂ (fun j => b (f j)) =
      ∑ f : Fin k → ι,
        T₁ (fun j => b (f j)) *
          T₂ (Function.update (fun j => b (f j)) i (LinearMap.adjoint L (b (f i)))) := by
  have expand₁ : ∀ f : Fin k → ι,
      T₁ (Function.update (fun j => b (f j)) i (L (b (f i)))) * T₂ (fun j => b (f j)) =
        ∑ x : ι, ⟪b x, L (b (f i))⟫_ℝ *
          (T₁ (Function.update (fun j => b (f j)) i (b x)) * T₂ (fun j => b (f j))) := by
    intro f
    rw [map_update_eq_sum_inner b T₁, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
  have expand₂ : ∀ f : Fin k → ι,
      T₁ (fun j => b (f j)) *
          T₂ (Function.update (fun j => b (f j)) i (LinearMap.adjoint L (b (f i)))) =
        ∑ x : ι, ⟪b x, LinearMap.adjoint L (b (f i))⟫_ℝ *
          (T₁ (fun j => b (f j)) * T₂ (Function.update (fun j => b (f j)) i (b x))) := by
    intro f
    rw [map_update_eq_sum_inner b T₂, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have key : ∀ p : (Fin k → ι) × ι,
      ⟪b (p.1 i), L (b (Function.update p.1 i p.2 i))⟫_ℝ *
          (T₁ (Function.update (fun j => b (Function.update p.1 i p.2 j)) i (b (p.1 i))) *
            T₂ (fun j => b (Function.update p.1 i p.2 j))) =
        ⟪b p.2, LinearMap.adjoint L (b (p.1 i))⟫_ℝ *
          (T₁ (fun j => b (p.1 j)) *
            T₂ (Function.update (fun j => b (p.1 j)) i (b p.2))) := by
    rintro ⟨f, x⟩
    have harg : (fun j => b (Function.update f i x j)) =
        Function.update (fun j => b (f j)) i (b x) := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    simp only [Function.update_self, harg, Function.update_idem]
    rw [show Function.update (fun j => b (f j)) i (b (f i)) = fun j => b (f j) from
      Function.update_eq_self i (fun j => b (f j))]
    rw [LinearMap.adjoint_inner_right, real_inner_comm]
  calc
    ∑ f : Fin k → ι,
        T₁ (Function.update (fun j => b (f j)) i (L (b (f i)))) * T₂ (fun j => b (f j))
      = ∑ f : Fin k → ι, ∑ x : ι, ⟪b x, L (b (f i))⟫_ℝ *
            (T₁ (Function.update (fun j => b (f j)) i (b x)) * T₂ (fun j => b (f j))) :=
        Finset.sum_congr rfl fun f _ => expand₁ f
    _ = ∑ p : (Fin k → ι) × ι, ⟪b p.2, L (b (p.1 i))⟫_ℝ *
            (T₁ (Function.update (fun j => b (p.1 j)) i (b p.2)) *
              T₂ (fun j => b (p.1 j))) :=
        (Fintype.sum_prod_type (f := fun p : (Fin k → ι) × ι =>
          ⟪b p.2, L (b (p.1 i))⟫_ℝ *
            (T₁ (Function.update (fun j => b (p.1 j)) i (b p.2)) *
              T₂ (fun j => b (p.1 j))))).symm
    _ = ∑ p : (Fin k → ι) × ι, ⟪b p.2, LinearMap.adjoint L (b (p.1 i))⟫_ℝ *
            (T₁ (fun j => b (p.1 j)) *
              T₂ (Function.update (fun j => b (p.1 j)) i (b p.2))) := by
        rw [← Equiv.sum_comp (updateSlotEquiv (ι := ι) i)]
        exact Finset.sum_congr rfl fun p _ => key p
    _ = ∑ f : Fin k → ι, ∑ x : ι, ⟪b x, LinearMap.adjoint L (b (f i))⟫_ℝ *
            (T₁ (fun j => b (f j)) * T₂ (Function.update (fun j => b (f j)) i (b x))) :=
        Fintype.sum_prod_type (f := fun p : (Fin k → ι) × ι =>
          ⟪b p.2, LinearMap.adjoint L (b (p.1 i))⟫_ℝ *
            (T₁ (fun j => b (p.1 j)) *
              T₂ (Function.update (fun j => b (p.1 j)) i (b p.2))))
    _ = ∑ f : Fin k → ι,
          T₁ (fun j => b (f j)) *
            T₂ (Function.update (fun j => b (f j)) i (LinearMap.adjoint L (b (f i)))) :=
        Finset.sum_congr rfl fun f _ => (expand₂ f).symm

/-- **Math.** Petersen Prop. 2.3.3 (1): the adjoint of `L : V → V` extends to the
adjoint of `L : T(V) → T(V)` — for the induced derivations on `(0,k)`-tensors,
`⟨L T₁, T₂⟩ = ⟨T₁, L† T₂⟩` in the tensor inner product. (Both sides carry the minus
sign of `endomorphismDerivation`, so the identity holds with `L†` and no sign.) -/
theorem tensorAlgebraInnerProduct_endomorphismDerivation (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] V) {k : ℕ} (T₁ T₂ : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    tensorAlgebraInnerProduct b (endomorphismDerivation L k T₁) T₂ =
      tensorAlgebraInnerProduct b T₁ (endomorphismDerivation (LinearMap.adjoint L) k T₂) := by
  unfold tensorAlgebraInnerProduct
  simp only [endomorphismDerivation_apply, neg_mul, mul_neg, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_neg_distrib, neg_inj]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_update_adjoint_slot b L T₁ T₂ i

/-- **Math.** Petersen Prop. 2.3.3 (2): a **skew-adjoint** `L ∈ 𝔰𝔬(V)` (i.e.
`L† = -L`) **commutes with type change**: lowering an index intertwines the commutator
action on `(1,1)`-tensors with the slotwise action on `(0,2)`-tensors,
`♭(L S) = L (♭S)`. (For general `L` the two sides differ by the `L + L†` term that the
metric sees; skew-adjointness kills it.) -/
theorem lowerIndex_endomorphismDerivationOneOne (L S : V →ₗ[ℝ] V)
    (hL : LinearMap.adjoint L = -L) :
    lowerIndex V (endomorphismDerivationOneOne L S) =
      endomorphismDerivationBilin L (lowerIndex V S) := by
  ext v w
  simp only [lowerIndex_apply, endomorphismDerivationOneOne,
    endomorphismDerivationBilin_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    inner_sub_left]
  have h : ⟪S v, L w⟫_ℝ = -⟪L (S v), w⟫_ℝ := by
    rw [← LinearMap.adjoint_inner_left, hL]
    simp
  rw [h]
  ring

/-- **Math.** Petersen Prop. 2.3.3: assume `V` has an inner product. (1) The adjoint of
`L : V → V` extends to the adjoint of `L : T(V) → T(V)`:
`⟨L T₁, T₂⟩ = ⟨T₁, L† T₂⟩` for the induced actions on `(0,k)`-tensors. (2) If
`L ∈ 𝔰𝔬(V)` is skew-adjoint (`L† = -L`), then `L` commutes with type change of tensors:
`♭(L S) = L (♭S)` through `lowerIndex`, where `L` acts on `(1,1)`-tensors by the
commutator and on `(0,2)`-tensors slotwise. -/
theorem endomorphismDerivation_adjoint_skew (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] V) {k : ℕ} (T₁ T₂ : MultilinearMap ℝ (fun _ : Fin k => V) ℝ)
    (S : V →ₗ[ℝ] V) :
    tensorAlgebraInnerProduct b (endomorphismDerivation L k T₁) T₂ =
        tensorAlgebraInnerProduct b T₁
          (endomorphismDerivation (LinearMap.adjoint L) k T₂) ∧
      (LinearMap.adjoint L = -L →
        lowerIndex V (endomorphismDerivationOneOne L S) =
          endomorphismDerivationBilin L (lowerIndex V S)) :=
  ⟨tensorAlgebraInnerProduct_endomorphismDerivation b L T₁ T₂,
    fun hL => lowerIndex_endomorphismDerivationOneOne L S hL⟩

end AdjointSkew

end PetersenLib

end
