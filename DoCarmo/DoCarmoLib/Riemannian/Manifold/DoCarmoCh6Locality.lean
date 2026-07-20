import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Fundamental
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# do Carmo Chapter 6 — pointwise locality of covariant-derivative-type operators

do Carmo Ch. 6 §2, after Prop. 2.1: "Because `B` is bilinear, we conclude that
`B(X, Y)(p)` depends only on `X(p)` and `Y(p)`." This file proves this pointwise
locality for the operators of the Chapter 6 interface:

* the value `(∇̄_X Z)(p)` of any affine connection depends only on `X(p)` in the
  direction slot (`AffineConnection.cov_congr_apply_left`);
* the value `B(X, Y)(p)` of the second fundamental form of an immersed patch
  depends only on `X(p)` and — for *tangent* `Y` — on `Y(p)`
  (`DCImmersedPatch.secondFundForm_congr_apply`);
* the same for the direction slot of the Weingarten operators
  (`DCImmersedPatch.shapeOperator_congr_apply`,
  `DCImmersedPatch.normalCov_congr_apply`, `DCImmersedPatch.inducedCov_congr_apply_left`).

The engine is the classical bump-function argument. A field `σ` vanishing at `p`
splits, via the local frame of a tangent-bundle trivialization at `p` and a smooth
bump at `p`, as `σ = Σᵢ fᵢ Wᵢ + τ` with globally smooth scalars `fᵢ` vanishing at
`p`, global fields `Wᵢ`, and `τ` vanishing on a neighbourhood of `p`
(`exists_decomposition_of_apply_eq_zero`). `𝒟(M̄)`-homogeneity kills each `fᵢ Wᵢ`
term at `p`, and a cutoff `1 − χ` kills the `τ` term
(`exists_smul_eq_self_of_eventuallyEq_zero`). For the second slot of `B` the same
decomposition is pushed through the tangential projection to make all its pieces
tangent (`exists_tangent_decomposition_of_apply_eq_zero`).

The file also provides the tangent/normal extension lemmas: every vector of
`T_pM` (resp. `(T_pM)^⊥`) is the value at `p` of a global tangent (resp. normal)
field (`DCImmersedPatch.exists_isTangentField_eq`,
`DCImmersedPatch.exists_isNormalField_eq`).

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-! ### Cutting off a field that vanishes near a point

If `τ` vanishes on a neighbourhood of `p`, then `τ = (1 − χ) τ` for a smooth bump
`χ` at `p` supported in that neighbourhood; the cutoff scalar `1 − χ` vanishes at
`p`. This turns "vanishes near `p`" into "is a smooth multiple, vanishing at `p`,
of a field" — the form that `𝒟(M̄)`-homogeneity of a connection-type operator can
annihilate. -/

omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- **Math.** A field `τ` vanishing near `p` is `f τ` for a globally smooth scalar
`f` with `f(p) = 0` (namely `f = 1 − χ` for a bump `χ` at `p` supported where `τ`
vanishes). -/
theorem exists_smul_eq_self_of_eventuallyEq_zero {τ : SmoothVectorField I M} {p : M}
    (hτ : ∀ᶠ q in nhds p, τ q = 0) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f), f p = 0 ∧
      SmoothVectorField.smul f hf τ = τ := by
  obtain ⟨U, hU_nhds, hU⟩ := hτ.exists_mem
  obtain ⟨χ, -, hχU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp hU_nhds
  refine ⟨fun q => 1 - χ q, contMDiff_const.sub χ.contMDiff, by
    show 1 - χ p = 0
    rw [χ.eq_one, sub_self], ?_⟩
  ext q
  rw [SmoothVectorField.smul_apply]
  by_cases hq : χ q = 0
  · rw [hq, sub_zero, one_smul]
  · have hqU : q ∈ U := hχU (subset_closure (by simpa using hq))
    rw [hU q hqU, smul_zero]

/-! ### The local-frame decomposition of a field vanishing at a point

do Carmo Ch. 6 §2 (implicit in the proof of Prop. 2.1): in the frame
`{s i}` of a tangent-bundle trivialization at `p`, a field `σ` with `σ(p) = 0` is
`σ = Σᵢ cᵢ sᵢ` near `p` with scalar coefficients `cᵢ` vanishing at `p`. Cutting
off with a bump at `p` globalizes both the coefficients and the frame fields, at
the price of a remainder `τ` vanishing near `p`. -/

open Bundle in
omit [CompleteSpace E] in
/-- **Math.** **Bump-frame decomposition.** A smooth field `σ` with `σ(p) = 0`
decomposes as `σ = Σᵢ fᵢ Wᵢ + τ` (pointwise) with finitely many globally smooth
scalars `fᵢ` vanishing at `p`, global smooth fields `Wᵢ`, and a remainder `τ`
vanishing on a neighbourhood of `p`. -/
theorem exists_decomposition_of_apply_eq_zero (σ : SmoothVectorField I M) {p : M}
    (hσ : σ p = 0) :
    ∃ (k : ℕ) (f : Fin k → M → ℝ) (_ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
      (W : Fin k → SmoothVectorField I M) (τ : SmoothVectorField I M),
      (∀ i, f i p = 0) ∧ (∀ᶠ q in nhds p, τ q = 0) ∧
        ∀ q, σ q = (∑ i, f i q • W i q) + τ q := by
  classical
  set e := trivializationAt E (TangentSpace I) p with he
  have hp_base : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb
  -- the frame coefficients of `σ`, smooth on the trivialization domain
  set c : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun i q => e.localFrame_coeff I b i q (σ q) with hc
  have hc_smooth : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (c i) e.baseSet := fun i =>
    contMDiffOn_baseSet_localFrame_coeff b (σ.smooth.contMDiffOn) i
  -- a smooth bump at `p`; its closed support lies in the chart source `= e.baseSet`
  let χ : SmoothBumpFunction I p := Classical.arbitrary _
  -- the cutoff coefficients are globally smooth and vanish at `p`
  set f : Fin (Module.finrank ℝ E) → M → ℝ := fun i q => χ q • c i q with hfdef
  have hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i) := fun i =>
    χ.contMDiff_smul (hc_smooth i)
  have hfp : ∀ i, f i p = 0 := fun i => by
    rw [hfdef]
    simp only [hc, hσ, map_zero, smul_zero]
  -- globalize the frame fields
  have hW_ex : ∀ i, ∃ Z : SmoothVectorField I M,
      ∀ᶠ y in nhds p, Z y = e.localFrame b i y := fun i =>
    exists_smoothVectorField_eventuallyEq e.open_baseSet
      (e.contMDiffOn_localFrame_baseSet ∞ b i) hp_base
  choose W hW using hW_ex
  -- the remainder
  have hτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, σ q - ∑ i, f i q • W i q⟩ : TangentBundle I M)) :=
    ContMDiff.sub_section σ.smooth
      (ContMDiff.sum_section fun i _ => ContMDiff.smul_section (hf i) (W i).smooth)
  refine ⟨Module.finrank ℝ E, f, hf, W,
    ⟨fun q => σ q - ∑ i, f i q • W i q, hτ_smooth⟩, hfp, ?_, ?_⟩
  · -- the remainder vanishes near `p`
    filter_upwards [χ.eventuallyEq_one, Filter.eventually_all.mpr hW,
      e.open_baseSet.mem_nhds hp_base] with q hq1 hq2 hq3
    show σ q - ∑ i, f i q • W i q = 0
    rw [sub_eq_zero]
    simp only [Pi.one_apply] at hq1
    calc σ q = ∑ i, c i q • e.localFrame b i q :=
          e.eq_sum_localFrame_coeff_smul (s := fun y => σ y) hq3
      _ = ∑ i, f i q • W i q := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hq2 i, hfdef]
          simp only [hq1, one_smul]
  · intro q
    show σ q = (∑ i, f i q • W i q) + (σ q - ∑ i, f i q • W i q)
    abel

namespace AffineConnection

variable (nabla : AffineConnection I M)

/-! ### Locality of the covariant derivative in the direction slot

do Carmo Ch. 2 §2 (Remark 2.3, used throughout Ch. 6): `(∇_X Z)(p)` depends only
on the value `X(p)`. The proof is the standard one: a direction field vanishing
at `p` is `Σᵢ fᵢ Wᵢ + τ` with `fᵢ(p) = 0` and `τ` vanishing near `p`; the sum
terms die at `p` by `𝒟(M̄)`-linearity in the direction slot, the remainder by the
cutoff trick. -/

omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- **Math.** `∇` annihilates, at `p`, direction fields vanishing near `p`. -/
theorem cov_apply_eq_zero_of_eventuallyEq_zero_left {τ : SmoothVectorField I M}
    (Z : SmoothVectorField I M) {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) :
    nabla.cov τ Z p = 0 := by
  obtain ⟨f, hf, hfp, hfτ⟩ := exists_smul_eq_self_of_eventuallyEq_zero hτ
  have h := nabla.smul_left f hf τ Z
  rw [hfτ] at h
  have h' := congrArg (fun F : SmoothVectorField I M => F p) h
  simp only [SmoothVectorField.smul_apply, hfp, zero_smul] at h'
  exact h'

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `∇` annihilates, at `p`, direction fields that are (pointwise) sums
`Σᵢ fᵢ Wᵢ` of smooth multiples of fields with all scalars vanishing at `p` —
the finite-sum core of tensoriality in the direction slot. -/
theorem cov_apply_eq_zero_of_forall_eq_sum {ι : Type*} (s : Finset ι)
    {f : ι → M → ℝ} (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
    (W : ι → SmoothVectorField I M) (Z : SmoothVectorField I M) {p : M}
    (hfp : ∀ i ∈ s, f i p = 0) {σ : SmoothVectorField I M}
    (hσ : ∀ q, σ q = ∑ i ∈ s, f i q • W i q) :
    nabla.cov σ Z p = 0 := by
  classical
  induction s using Finset.induction_on generalizing σ with
  | empty =>
    have hσ0 : σ = 0 := SmoothVectorField.ext fun q => by simpa using hσ q
    rw [hσ0]
    exact nabla.cov_zero_left Z p
  | @insert a s ha ih =>
    have key : ∀ q, (σ - SmoothVectorField.smul (f a) (hf a) (W a)) q
        = ∑ i ∈ s, f i q • W i q := by
      intro q
      rw [SmoothVectorField.sub_apply, SmoothVectorField.smul_apply, hσ q,
        Finset.sum_insert ha]
      abel
    have hzero := ih (fun i hi => hfp i (Finset.mem_insert_of_mem hi)) key
    have hsub := nabla.cov_sub_left σ (SmoothVectorField.smul (f a) (hf a) (W a)) Z p
    have hsm := congrArg (fun F : SmoothVectorField I M => F p)
      (nabla.smul_left (f a) (hf a) (W a) Z)
    simp only [SmoothVectorField.smul_apply] at hsm
    rw [hsub, hsm, hfp a (Finset.mem_insert_self a s), zero_smul, sub_zero] at hzero
    exact hzero

omit [CompleteSpace E] in
/-- **Math.** **Pointwise locality of `∇` in the direction slot** (do Carmo
Ch. 2, Remark 2.3): if `X(p) = X'(p)` then `(∇_X Z)(p) = (∇_{X'} Z)(p)`. -/
theorem cov_congr_apply_left {X X' : SmoothVectorField I M}
    (Z : SmoothVectorField I M) {p : M} (h : X p = X' p) :
    nabla.cov X Z p = nabla.cov X' Z p := by
  have hσp : (X - X') p = 0 := by
    rw [SmoothVectorField.sub_apply, h, sub_self]
  obtain ⟨k, f, hf, W, τ, hfp, hτ0, hdecomp⟩ :=
    exists_decomposition_of_apply_eq_zero (X - X') hσp
  have hkey : ∀ q, ((X - X') - τ) q = ∑ i, f i q • W i q := by
    intro q
    rw [SmoothVectorField.sub_apply, hdecomp q]
    abel
  have h1 : nabla.cov ((X - X') - τ) Z p = 0 :=
    nabla.cov_apply_eq_zero_of_forall_eq_sum Finset.univ hf W Z
      (fun i _ => hfp i) hkey
  have h2 : nabla.cov τ Z p = 0 :=
    nabla.cov_apply_eq_zero_of_eventuallyEq_zero_left Z hτ0
  have h3 := nabla.cov_sub_left (X - X') τ Z p
  rw [h1, h2, sub_zero] at h3
  have h4 := nabla.cov_sub_left X X' Z p
  rw [← h3] at h4
  exact sub_eq_zero.mp h4.symm

end AffineConnection

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)

/-! ### Extension lemmas: tangent and normal fields through a prescribed vector

do Carmo Ch. 6 §2 extends local fields on `M` to the ambient manifold; in the
identified picture the corresponding tool is: every tangent (resp. normal)
vector at `p` is the value at `p` of a global tangent (resp. normal) field —
project a global extension of the vector onto the distribution. -/

omit [CompleteSpace E] in
/-- **Math.** Every `v ∈ T_pM` is the value at `p` of a global tangent field. -/
theorem exists_isTangentField_eq (p : M) {v : TangentSpace I p}
    (hv : v ∈ D.tang p) :
    ∃ X : SmoothVectorField I M, D.IsTangentField X ∧ X p = v := by
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq p v
  refine ⟨D.tangentProj Z, D.isTangentField_tangentProj Z, ?_⟩
  rw [← hZ] at hv
  rw [D.tangentProj_apply_of_mem hv, hZ]

omit [CompleteSpace E] in
/-- **Math.** Every `w ∈ (T_pM)^⊥` is the value at `p` of a global normal
field. -/
theorem exists_isNormalField_eq (p : M) {v : TangentSpace I p}
    (hv : v ∈ D.normalSpace p) :
    ∃ X : SmoothVectorField I M, D.IsNormalField X ∧ X p = v := by
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq p v
  refine ⟨D.normalProj Z, D.isNormalField_normalProj Z, ?_⟩
  rw [← hZ] at hv
  rw [D.normalProj_apply, D.tangentProj_apply_of_mem_normalSpace hv, hZ, sub_zero]

variable (nabla : AffineConnection I M)

/-! ### Algebra of `B` in the second slot: subtraction and zero -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `B(X, Y₁ − Y₂) = B(X, Y₁) − B(X, Y₂)`, from additivity (companion
of `secondFundForm_sub_left`). -/
theorem secondFundForm_sub_right (X Y₁ Y₂ : SmoothVectorField I M) :
    D.secondFundForm nabla X (Y₁ - Y₂)
      = D.secondFundForm nabla X Y₁ - D.secondFundForm nabla X Y₂ := by
  have hcov : nabla.cov X (Y₁ - Y₂) = nabla.cov X Y₁ - nabla.cov X Y₂ := by
    ext q
    rw [SmoothVectorField.sub_apply]
    exact nabla.cov_sub_right X Y₁ Y₂ q
  simp only [secondFundForm, hcov, D.normalProj_sub]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `B(X, 0) = 0`, pointwise. -/
theorem secondFundForm_zero_right (X : SmoothVectorField I M) (p : M) :
    D.secondFundForm nabla X 0 p = 0 := by
  have h0 : (0 : SmoothVectorField I M) - 0 = 0 := by ext q; simp
  have h := D.secondFundForm_sub_right nabla X 0 0
  rw [h0] at h
  have h' := congrArg (fun F : SmoothVectorField I M => F p) h
  simp only [SmoothVectorField.sub_apply] at h'
  linear_combination (norm := module) h'

/-! ### Locality of `B` in the second slot -/

omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- **Math.** `B(X, ·)` annihilates, at `p`, *tangent* fields vanishing near
`p` — the cutoff trick through the tangent Leibniz cancellation
`secondFundForm_smul_right`. -/
theorem secondFundForm_apply_eq_zero_of_eventuallyEq_zero_right
    (X : SmoothVectorField I M) {τ : SmoothVectorField I M}
    (hτt : D.IsTangentField τ) {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) :
    D.secondFundForm nabla X τ p = 0 := by
  obtain ⟨f, hf, hfp, hfτ⟩ := exists_smul_eq_self_of_eventuallyEq_zero hτ
  have h := D.secondFundForm_smul_right nabla hf X hτt
  rw [hfτ] at h
  have h' := congrArg (fun F : SmoothVectorField I M => F p) h
  simp only [SmoothVectorField.smul_apply, hfp, zero_smul] at h'
  exact h'

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `B(X, ·)` annihilates, at `p`, (pointwise) sums `Σᵢ fᵢ Wᵢ` of
smooth multiples of *tangent* fields with all scalars vanishing at `p`. -/
theorem secondFundForm_apply_eq_zero_of_forall_eq_sum
    (X : SmoothVectorField I M) {ι : Type*} (s : Finset ι)
    {f : ι → M → ℝ} (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
    {W : ι → SmoothVectorField I M} (hW : ∀ i, D.IsTangentField (W i)) {p : M}
    (hfp : ∀ i ∈ s, f i p = 0) {σ : SmoothVectorField I M}
    (hσ : ∀ q, σ q = ∑ i ∈ s, f i q • W i q) :
    D.secondFundForm nabla X σ p = 0 := by
  classical
  induction s using Finset.induction_on generalizing σ with
  | empty =>
    have hσ0 : σ = 0 := SmoothVectorField.ext fun q => by simpa using hσ q
    rw [hσ0]
    exact D.secondFundForm_zero_right nabla X p
  | @insert a s ha ih =>
    have key : ∀ q, (σ - SmoothVectorField.smul (f a) (hf a) (W a)) q
        = ∑ i ∈ s, f i q • W i q := by
      intro q
      rw [SmoothVectorField.sub_apply, SmoothVectorField.smul_apply, hσ q,
        Finset.sum_insert ha]
      abel
    have hzero := ih (fun i hi => hfp i (Finset.mem_insert_of_mem hi)) key
    have hsub := congrArg (fun F : SmoothVectorField I M => F p)
      (D.secondFundForm_sub_right nabla X σ (SmoothVectorField.smul (f a) (hf a) (W a)))
    have hsm := congrArg (fun F : SmoothVectorField I M => F p)
      (D.secondFundForm_smul_right nabla (hf a) X (hW a))
    simp only [SmoothVectorField.sub_apply, SmoothVectorField.smul_apply] at hsub hsm
    rw [hsub, hsm, hfp a (Finset.mem_insert_self a s), zero_smul, sub_zero] at hzero
    exact hzero

omit [CompleteSpace E] in
/-- **Math.** **Tangent bump-frame decomposition.** A *tangent* field `σ` with
`σ(p) = 0` decomposes as `σ = Σᵢ fᵢ Wᵢ + τ` (pointwise) with globally smooth
scalars `fᵢ` vanishing at `p`, global *tangent* fields `Wᵢ`, and a *tangent*
remainder `τ` vanishing near `p` — push the ambient decomposition through the
tangential projection: the discrepancy is a sum of normal vectors, hence zero by
directness of the splitting. -/
theorem exists_tangent_decomposition_of_apply_eq_zero
    {σ : SmoothVectorField I M} (hσt : D.IsTangentField σ) {p : M}
    (hσ : σ p = 0) :
    ∃ (k : ℕ) (f : Fin k → M → ℝ) (_ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
      (W : Fin k → SmoothVectorField I M) (τ : SmoothVectorField I M),
      (∀ i, D.IsTangentField (W i)) ∧ D.IsTangentField τ ∧ (∀ i, f i p = 0) ∧
        (∀ᶠ q in nhds p, τ q = 0) ∧ ∀ q, σ q = (∑ i, f i q • W i q) + τ q := by
  obtain ⟨k, f, hf, W, τ, hfp, hτ0, hdecomp⟩ :=
    exists_decomposition_of_apply_eq_zero σ hσ
  refine ⟨k, f, hf, fun i => D.tangentProj (W i), D.tangentProj τ,
    fun i => D.isTangentField_tangentProj (W i), D.isTangentField_tangentProj τ,
    hfp, ?_, ?_⟩
  · -- the projected remainder still vanishes near `p`
    filter_upwards [hτ0] with q hq
    have h0 : D.tangentProj τ q = D.tangentProj (0 : SmoothVectorField I M) q :=
      D.tangentProj_congr_apply (by rw [hq, SmoothVectorField.zero_apply])
    rw [h0, D.tangentProj_zero, SmoothVectorField.zero_apply]
  · -- the projected decomposition still represents `σ`
    intro q
    have hcalc : σ q - ((∑ i, f i q • D.tangentProj (W i) q) + D.tangentProj τ q)
        = (∑ i, f i q • D.normalProj (W i) q) + D.normalProj τ q := by
      simp only [normalProj_apply, smul_sub, Finset.sum_sub_distrib, hdecomp q]
      abel
    have hmem_n : σ q - ((∑ i, f i q • D.tangentProj (W i) q) + D.tangentProj τ q)
        ∈ D.normalSpace q := by
      rw [hcalc]
      exact add_mem
        (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (D.normalProj_mem (W i) q))
        (D.normalProj_mem τ q)
    have hmem_t : σ q - ((∑ i, f i q • D.tangentProj (W i) q) + D.tangentProj τ q)
        ∈ D.tang q :=
      sub_mem (hσt q)
        (add_mem
          (Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (D.tangentProj_mem (W i) q))
          (D.tangentProj_mem τ q))
    exact sub_eq_zero.mp (D.eq_zero_of_mem_tang_of_mem_normalSpace hmem_t hmem_n)

/-! ### Pointwise locality of the second fundamental form
(do Carmo Ch. 6 §2, after Prop. 2.1) -/

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6 §2: "Because `B` is bilinear, we conclude that
`B(X, Y)(p)` depends only on `X(p)` and `Y(p)`" — for `Y, Y'` *tangent* fields
(the second slot of `B` is tensorial only on tangent fields). -/
theorem secondFundForm_congr_apply {X X' Y Y' : SmoothVectorField I M}
    (hY : D.IsTangentField Y) (hY' : D.IsTangentField Y') {p : M}
    (hX : X p = X' p) (hYp : Y p = Y' p) :
    D.secondFundForm nabla X Y p = D.secondFundForm nabla X' Y' p := by
  -- direction slot: locality of the ambient connection plus pointwise
  -- determination of the projection
  have h1 : D.secondFundForm nabla X Y p = D.secondFundForm nabla X' Y p := by
    have hcov := nabla.cov_congr_apply_left Y hX
    simp only [secondFundForm, normalProj_apply, hcov,
      D.tangentProj_congr_apply hcov]
  -- second slot: decompose the tangent field `Y − Y'` vanishing at `p`
  have hσt : D.IsTangentField (Y - Y') := fun q => by
    rw [SmoothVectorField.sub_apply]
    exact sub_mem (hY q) (hY' q)
  have hσp : (Y - Y') p = 0 := by
    rw [SmoothVectorField.sub_apply, hYp, sub_self]
  obtain ⟨k, f, hf, W, τ, hWt, hτt, hfp, hτ0, hdecomp⟩ :=
    D.exists_tangent_decomposition_of_apply_eq_zero hσt hσp
  have hkey : ∀ q, ((Y - Y') - τ) q = ∑ i, f i q • W i q := by
    intro q
    rw [SmoothVectorField.sub_apply, hdecomp q]
    abel
  have hzero1 : D.secondFundForm nabla X' ((Y - Y') - τ) p = 0 :=
    D.secondFundForm_apply_eq_zero_of_forall_eq_sum nabla X' Finset.univ hf hWt
      (fun i _ => hfp i) hkey
  have hzero2 : D.secondFundForm nabla X' τ p = 0 :=
    D.secondFundForm_apply_eq_zero_of_eventuallyEq_zero_right nabla X' hτt hτ0
  have hsub1 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.secondFundForm_sub_right nabla X' (Y - Y') τ)
  have hsub2 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.secondFundForm_sub_right nabla X' Y Y')
  simp only [SmoothVectorField.sub_apply] at hsub1 hsub2
  rw [hzero1, hzero2, sub_zero] at hsub1
  rw [← hsub1] at hsub2
  rw [h1]
  exact sub_eq_zero.mp hsub2.symm

/-! ### Locality of the derived operators in the direction slot -/

omit [CompleteSpace E] in
/-- **Math.** Pointwise locality of the induced connection `∇` in the direction
slot: `(∇_X Z)(p)` depends only on `X(p)`. -/
theorem inducedCov_congr_apply_left {X X' : SmoothVectorField I M}
    (Z : SmoothVectorField I M) {p : M} (h : X p = X' p) :
    D.inducedCov nabla X Z p = D.inducedCov nabla X' Z p := by
  have hcov := nabla.cov_congr_apply_left Z h
  simp only [inducedCov]
  exact D.tangentProj_congr_apply hcov

omit [CompleteSpace E] in
/-- **Math.** Pointwise locality of the shape operator in its direction slot:
`S_η(X)(p)` depends only on `X(p)` (do Carmo Ch. 6 §2, Prop. 2.3 makes sense
pointwise). -/
theorem shapeOperator_congr_apply (η : SmoothVectorField I M)
    {X X' : SmoothVectorField I M} {p : M} (h : X p = X' p) :
    D.shapeOperator nabla η X p = D.shapeOperator nabla η X' p := by
  have hcov := nabla.cov_congr_apply_left η h
  simp only [shapeOperator, SmoothVectorField.neg_apply,
    D.tangentProj_congr_apply hcov]

omit [CompleteSpace E] in
/-- **Math.** Pointwise locality of the normal connection in its direction slot:
`(∇^⊥_X η)(p)` depends only on `X(p)`. -/
theorem normalCov_congr_apply (η : SmoothVectorField I M)
    {X X' : SmoothVectorField I M} {p : M} (h : X p = X' p) :
    D.normalCov nabla X η p = D.normalCov nabla X' η p := by
  have hcov := nabla.cov_congr_apply_left η h
  simp only [normalCov, normalProj_apply, hcov, D.tangentProj_congr_apply hcov]

end DCImmersedPatch

end Riemannian
