/-
Chapter 2, "Riemannian Metrics", Problem 2-16: the fibre metric on `Λ^k T^*M`.

Lee asks for the unique fibre metric `⟨·,·⟩_g` on `Λ^k T^*M` satisfying

  `⟨ω^1 ∧ ⋯ ∧ ω^k, η^1 ∧ ⋯ ∧ η^k⟩_g = det (⟨ω^i, η^j⟩_g)`                              (2.26)

for covectors `ω^i, η^j` at a point.  This file builds the fibrewise algebra: the inner product on
`V [⋀^ι]→L[ℝ] ℝ` for an inner product space `V`, its characterization (2.26), positive
definiteness, uniqueness, and independence of the orthonormal basis used to define it.  The
remaining step -- assembling the pointwise family into a smooth fibre metric on the bundle
`LeeLib.AppendixA.AlternatingBundle` builds over `M` -- is not done here.

Nothing upstream helps.  Mathlib has no inner product on `exteriorPower`, `AlternatingMap`,
`ContinuousAlternatingMap`, `MultilinearMap` or `PiTensorProduct` (only on the *binary*
`TensorProduct`, in `Analysis/InnerProductSpace/TensorProduct.lean`), and no Hodge star; nor does
any sibling project in this workspace.  `exteriorPower.pairingDual` is a duality pairing between
`⋀^k (V^*)` and `(⋀^k V)^*`, needs no metric, and is not a self-pairing.

## The route

Lee's hint is to *declare* `{e^{i_1} ∧ ⋯ ∧ e^{i_k} : i_1 < ⋯ < i_k}` orthonormal for an
orthonormal coframe `(e^i)`, then check (2.26) and independence of the frame.  Formalizing that
literally means carrying strictly-increasing multi-indices through every computation.  This file
avoids them entirely by summing over **all** maps `s : ι → ι'` instead, with a `1/k!` correction:

  `innerForms e w θ = (∑_{s : ι → ι'} w (e ∘ s) · θ (e ∘ s)) / k!`.

The terms where `s` is not injective are not discarded by hand -- they simply do not contribute,
because `w` is alternating -- and each increasing multi-index is counted `k!` times with the two
sign changes cancelling.  Bilinearity, symmetry and positive definiteness are then immediate from
the shape of the definition (`innerForms e w w` is a sum of squares), which is the main reason to
prefer it: in the increasing-multi-index formulation none of these is immediate.

Everything else follows from one identity, `AlternatingMap.sum_det_submatrix_smul_apply` in
`LeeLib.AppendixB.CauchyBinet` (Cauchy-Binet with one determinant replaced by an arbitrary
alternating map), applied twice with different matrices:

* with `A_{i m} = ω^i (e_m)` it gives **(2.26)** (`innerForms_wedgeCovectors`);
* with `A_{i m} = ⟪e_{v(i)}, e_m⟫` it gives the **expansion of an arbitrary `k`-covector** in
  wedges of the dual coframe (`factorial_smul_eq_sum_wedgeCovectors`), hence that the wedges span
  (`span_range_wedgeCovectors`), hence **uniqueness** (`eq_innerForms_of_wedgeCovectors`).

Frame independence (`innerForms_eq_innerForms`) is then a *corollary of uniqueness* rather than a
separate change-of-basis computation: `innerForms e` and `innerForms f` both satisfy (2.26), which
determines a bilinear form on a spanning set.  This is why (2.26) is proved for an arbitrary
orthonormal basis rather than a fixed one.
-/
import LeeLib.Ch02.VolumeForm
import LeeLib.AppendixB.CauchyBinet

namespace LeeLib.Ch02

open Finset Matrix Module InnerProductSpace
open scoped InnerProductSpace Matrix

noncomputable section

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ι' : Type*} [Fintype ι'] [DecidableEq ι']
  {ι'' : Type*} [Fintype ι''] [DecidableEq ι'']

/-! ### The musical isomorphisms on an abstract inner product space

`LeeLib.Ch02.RiemannianMetric.flat`/`sharp` are the same maps for a metric on a tangent space;
these are their counterparts for a bare inner product space, which is the setting the fibrewise
algebra below lives in. -/

/-- The covector `v^♭ = ⟪v, ·⟫`. -/
def flatL (v : V) : V →L[ℝ] ℝ := InnerProductSpace.toDual ℝ V v

/-- The vector `a^♯`, characterized by `⟪a^♯, ·⟫ = a` (`inner_sharpL`). -/
def sharpL (a : V →L[ℝ] ℝ) : V := (InnerProductSpace.toDual ℝ V).symm a

@[simp] theorem flatL_apply (v w : V) : flatL v w = ⟪v, w⟫_ℝ := rfl

@[simp] theorem inner_sharpL (a : V →L[ℝ] ℝ) (w : V) : ⟪sharpL a, w⟫_ℝ = a w :=
  InnerProductSpace.toDual_symm_apply

omit [DecidableEq ι'] in
/-- The Riesz representative expanded in an orthonormal basis: `a^♯ = ∑_m a(e_m) e_m`. -/
theorem sharpL_eq_sum (e : OrthonormalBasis ι' ℝ V) (a : V →L[ℝ] ℝ) :
    sharpL a = ∑ m, a (e m) • e m := by
  conv_lhs => rw [← e.sum_repr (sharpL a)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [e.repr_apply_apply, real_inner_comm, inner_sharpL]

/-- **The inner product induced on covectors**, Lee's `⟨ω, η⟩_g`: transport the inner product of
`V` along `♯`.  In coordinates this is his `g^{ij} ω_i η_j`. -/
def innerDual (a b : V →L[ℝ] ℝ) : ℝ := ⟪sharpL a, sharpL b⟫_ℝ

theorem innerDual_comm (a b : V →L[ℝ] ℝ) : innerDual a b = innerDual b a :=
  real_inner_comm _ _

omit [DecidableEq ι'] in
/-- Against an orthonormal basis the dual inner product is the plain dot product of the
coefficient vectors -- Parseval. -/
theorem innerDual_eq_sum (e : OrthonormalBasis ι' ℝ V) (a b : V →L[ℝ] ℝ) :
    innerDual a b = ∑ m, a (e m) * b (e m) := by
  rw [innerDual, ← e.sum_inner_mul_inner (sharpL a) (sharpL b)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_sharpL, real_inner_comm, inner_sharpL]

/-- Evaluating a covector on another covector's sharp is the dual inner product. -/
theorem apply_sharpL (a b : V →L[ℝ] ℝ) : a (sharpL b) = innerDual a b := by
  rw [innerDual, ← inner_sharpL a (sharpL b)]

/-! ### Two facts about orthonormal bases -/

omit [FiniteDimensional ℝ V] [DecidableEq ι] [DecidableEq ι'] in
/-- Two continuous alternating maps agreeing on every tuple of basis vectors are equal.

`ContinuousAlternatingMap.ext` demands agreement on *all* tuples; this cuts the test set down to
basis tuples, via `Module.Basis.ext_multilinear` on the underlying multilinear maps.  It is what
turns "`w` vanishes on all `e ∘ s`" into "`w = 0`", used for positive definiteness and for the
basis expansion. -/
theorem ext_of_orthonormalBasis (e : OrthonormalBasis ι' ℝ V) {f g : V [⋀^ι]→L[ℝ] ℝ}
    (h : ∀ v : ι → ι', f (fun i => e (v i)) = g (fun i => e (v i))) : f = g := by
  refine ContinuousAlternatingMap.ext fun x => ?_
  have hm : f.toAlternatingMap.toMultilinearMap = g.toAlternatingMap.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ => e.toBasis) (fun v => h v)
  exact DFunLike.congr_fun hm x

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
/-- `∑_m ⟪x, e_m⟫ e_m = x`: the expansion of a vector in an orthonormal basis, in the form the
master identity of `CauchyBinet` consumes. -/
theorem sum_inner_smul_orthonormalBasis (e : OrthonormalBasis ι' ℝ V) (x : V) :
    ∑ m, ⟪x, e m⟫_ℝ • e m = x := by
  conv_rhs => rw [← e.sum_repr x]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [e.repr_apply_apply, real_inner_comm]

/-! ### The inner product on `k`-covectors -/

/-- **The inner product on `k`-covectors** determined by an orthonormal basis `e` of `V`
(Lee, Problem 2-16).

Summing over *all* index maps `s : ι → ι'` rather than over increasing multi-indices, and dividing
by `k!`, gives the same form -- see the module docstring -- while keeping symmetry, bilinearity and
positive definiteness immediate.  `innerForms_eq_innerForms` shows the choice of `e` does not
matter, so this deserves the name. -/
def innerForms (e : OrthonormalBasis ι' ℝ V) (w θ : V [⋀^ι]→L[ℝ] ℝ) : ℝ :=
  (∑ s : ι → ι', w (fun i => e (s i)) * θ (fun i => e (s i))) / (Fintype.card ι).factorial

omit [DecidableEq ι'] in
/-- **Lee's (2.26)**: `⟨ω^1 ∧ ⋯ ∧ ω^k, η^1 ∧ ⋯ ∧ η^k⟩ = det (⟨ω^i, η^j⟩)`.

This is the master identity of `LeeLib.AppendixB.CauchyBinet` with `θ` the wedge `η^1 ∧ ⋯ ∧ η^k`
and `A_{i m} = ω^i (e_m)` the coefficient matrix of the `ω`'s: the left-hand side of that identity
is `∑_s (ω^1 ∧ ⋯ ∧ ω^k)(e ∘ s) · (η^1 ∧ ⋯ ∧ η^k)(e ∘ s)`, because `det (A[·, s])` is by definition
the wedge evaluated on `e ∘ s`; and its right-hand side is `k! · (η^1 ∧ ⋯ ∧ η^k)((ω^i)^♯)`,
because `∑_m ω^i(e_m) e_m` is the Riesz representative `(ω^i)^♯`.  The determinant that comes out
is the transpose of the one wanted, whence the `det_transpose`. -/
theorem innerForms_wedgeCovectors (e : OrthonormalBasis ι' ℝ V) (a b : ι → (V →L[ℝ] ℝ)) :
    innerForms e (wedgeCovectors a) (wedgeCovectors b)
      = (Matrix.of fun i j => innerDual (a i) (b j)).det := by
  have hmaster := AlternatingMap.sum_det_submatrix_smul_apply
    (wedgeCovectors b).toAlternatingMap (e : ι' → V) (Matrix.of fun (i : ι) (m : ι') => a i (e m))
  simp only [smul_eq_mul, ContinuousAlternatingMap.coe_toAlternatingMap] at hmaster
  have hsub : ∀ s : ι → ι',
      ((Matrix.of fun (i : ι) (m : ι') => a i (e m)).submatrix id s).det
        = wedgeCovectors a (fun i => e (s i)) := by
    intro s
    rw [wedgeCovectors_apply]
    rfl
  have hrhs :
      ((wedgeCovectors b) fun i => ∑ m, (Matrix.of fun (i : ι) (m : ι') => a i (e m)) i m • e m)
        = (Matrix.of fun i j => innerDual (a i) (b j)).det := by
    have hsharp : ∀ i : ι,
        (∑ m, (Matrix.of fun (i : ι) (m : ι') => a i (e m)) i m • e m) = sharpL (a i) :=
      fun i => (sharpL_eq_sum e (a i)).symm
    simp only [hsharp, wedgeCovectors_apply]
    rw [← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [apply_sharpL, innerDual_comm]
  rw [Finset.sum_congr rfl fun s _ => congrArg (· * _) (hsub s), hrhs] at hmaster
  rw [innerForms, hmaster, nsmul_eq_mul]
  have hfac : ((Fintype.card ι).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp

omit [DecidableEq ι'] in
/-- **Every `k`-covector is a combination of wedges of the dual coframe**:

  `k! · w = ∑_{u : ι → ι'} w(e ∘ u) · (e_{u(1)}^♭ ∧ ⋯ ∧ e_{u(k)}^♭)`.

Stated with `k! • w` on the left rather than a `1/k!` on the right so that it holds over any
`ℝ`-module without a division.  Together with `ext_of_orthonormalBasis` this is the master identity
of `CauchyBinet` with the "selection" matrix `A_{i m} = ⟪e_{v(i)}, e_m⟫`, for which
`∑_m A_{i m} e_m = e_{v(i)}` collapses the right-hand side to `k! · w(e ∘ v)`. -/
theorem factorial_smul_eq_sum_wedgeCovectors (e : OrthonormalBasis ι' ℝ V)
    (w : V [⋀^ι]→L[ℝ] ℝ) :
    ((Fintype.card ι).factorial : ℝ) • w
      = ∑ u : ι → ι', w (fun i => e (u i)) • wedgeCovectors (fun i => flatL (e (u i))) := by
  refine ext_of_orthonormalBasis e fun v => ?_
  have hmaster := AlternatingMap.sum_det_submatrix_smul_apply
    w.toAlternatingMap (e : ι' → V) (Matrix.of fun (i : ι) (m : ι') => ⟪e (v i), e m⟫_ℝ)
  simp only [smul_eq_mul, ContinuousAlternatingMap.coe_toAlternatingMap] at hmaster
  have hcollapse : ∀ i : ι,
      (∑ m, (Matrix.of fun (i : ι) (m : ι') => ⟪e (v i), e m⟫_ℝ) i m • e m) = e (v i) :=
    fun i => sum_inner_smul_orthonormalBasis e (e (v i))
  simp only [hcollapse] at hmaster
  rw [nsmul_eq_mul] at hmaster
  rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply, smul_eq_mul,
    ← hmaster]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, wedgeCovectors_apply, mul_comm]
  congr 1
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.submatrix_apply, id_eq, flatL_apply]
  exact real_inner_comm _ _

/-! ### `innerForms` is an inner product

Each of these is immediate from the shape of the definition; that is the payoff of summing over
all index maps rather than over increasing multi-indices. -/

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
theorem innerForms_comm (e : OrthonormalBasis ι' ℝ V) (w θ : V [⋀^ι]→L[ℝ] ℝ) :
    innerForms e w θ = innerForms e θ w := by
  simp only [innerForms]
  congr 1
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
theorem innerForms_add_left (e : OrthonormalBasis ι' ℝ V) (w₁ w₂ θ : V [⋀^ι]→L[ℝ] ℝ) :
    innerForms e (w₁ + w₂) θ = innerForms e w₁ θ + innerForms e w₂ θ := by
  simp only [innerForms, ContinuousAlternatingMap.add_apply, add_mul]
  rw [Finset.sum_add_distrib, add_div]

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
theorem innerForms_smul_left (e : OrthonormalBasis ι' ℝ V) (c : ℝ) (w θ : V [⋀^ι]→L[ℝ] ℝ) :
    innerForms e (c • w) θ = c * innerForms e w θ := by
  simp only [innerForms, ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum]
  rw [mul_div_assoc]

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
/-- `⟨w, w⟩ ≥ 0`: the numerator is a sum of squares. -/
theorem innerForms_self_nonneg (e : OrthonormalBasis ι' ℝ V) (w : V [⋀^ι]→L[ℝ] ℝ) :
    0 ≤ innerForms e w w :=
  div_nonneg (Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (Nat.cast_nonneg _)

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
/-- `⟨w, w⟩ > 0` for `w ≠ 0`: a nonzero alternating map is nonzero on some tuple of basis
vectors (`ext_of_orthonormalBasis`), so one square in the sum is positive. -/
theorem innerForms_self_pos (e : OrthonormalBasis ι' ℝ V) {w : V [⋀^ι]→L[ℝ] ℝ} (hw : w ≠ 0) :
    0 < innerForms e w w := by
  obtain ⟨v, hv⟩ : ∃ v : ι → ι', w (fun i => e (v i)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (ext_of_orthonormalBasis e fun v => by simp [h v])
  refine div_pos ?_ (by exact_mod_cast Nat.factorial_pos _)
  exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _)
    ⟨v, Finset.mem_univ v, mul_self_pos.2 hv⟩

/-- `innerForms` as a bundled bilinear form -- the shape uniqueness is stated against. -/
def innerFormsₗ (e : OrthonormalBasis ι' ℝ V) :
    (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (innerForms e) (innerForms_add_left e)
    (fun c w θ => by rw [innerForms_smul_left, smul_eq_mul])
    (fun w θ₁ θ₂ => by
      rw [innerForms_comm, innerForms_add_left, innerForms_comm e θ₁, innerForms_comm e θ₂])
    (fun c w θ => by
      rw [innerForms_comm, innerForms_smul_left, innerForms_comm e θ, smul_eq_mul])

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
@[simp] theorem innerFormsₗ_apply (e : OrthonormalBasis ι' ℝ V) (w θ : V [⋀^ι]→L[ℝ] ℝ) :
    innerFormsₗ e w θ = innerForms e w θ := rfl

/-! ### Uniqueness and frame independence (Lee, Problem 2-16) -/

omit [DecidableEq ι'] in
/-- **The wedges of covectors span the `k`-covectors.**  Immediate from
`factorial_smul_eq_sum_wedgeCovectors`, since `k! ≠ 0` in `ℝ`.

This is the only place characteristic zero is used, and it is used essentially: over a field of
characteristic `p ≤ k` the `1/k!` normalization -- and with it this whole route -- breaks down. -/
theorem span_range_wedgeCovectors (e : OrthonormalBasis ι' ℝ V) :
    Submodule.span ℝ (Set.range fun a : ι → (V →L[ℝ] ℝ) => wedgeCovectors a) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro w
  have hfac : ((Fintype.card ι).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hw : w = ((Fintype.card ι).factorial : ℝ)⁻¹ •
      ∑ u : ι → ι', w (fun i => e (u i)) • wedgeCovectors (fun i => flatL (e (u i))) := by
    rw [← factorial_smul_eq_sum_wedgeCovectors e w, inv_smul_smul₀ hfac]
  rw [hw]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨_, rfl⟩

omit [DecidableEq ι'] in
/-- **Uniqueness in Lee's Problem 2-16**: a bilinear form on `k`-covectors satisfying (2.26) *is*
`innerForms`.  A bilinear form is determined by its values on a spanning set, and the wedges span
(`span_range_wedgeCovectors`), while (2.26) prescribes exactly those values. -/
theorem eq_innerForms_of_wedgeCovectors (e : OrthonormalBasis ι' ℝ V)
    (B : (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hB : ∀ a b : ι → (V →L[ℝ] ℝ),
      B (wedgeCovectors a) (wedgeCovectors b) = (Matrix.of fun i j => innerDual (a i) (b j)).det) :
    B = innerFormsₗ e := by
  refine LinearMap.ext_on (span_range_wedgeCovectors (ι := ι) e) ?_
  rintro _ ⟨a, rfl⟩
  refine LinearMap.ext_on (span_range_wedgeCovectors (ι := ι) e) ?_
  rintro _ ⟨b, rfl⟩
  rw [hB a b, innerFormsₗ_apply, innerForms_wedgeCovectors]

omit [DecidableEq ι'] [DecidableEq ι''] in
/-- **Frame independence**: `innerForms` does not depend on the orthonormal basis defining it --
not even on its index type.

Lee's Problem 2-16 asks for this directly, as a change-of-frame computation.  Here it is a
corollary of uniqueness: both `innerForms e` and `innerForms f` satisfy (2.26)
(`innerForms_wedgeCovectors` is proved for an *arbitrary* orthonormal basis), and (2.26) pins a
bilinear form down. -/
theorem innerForms_eq_innerForms (e : OrthonormalBasis ι' ℝ V) (f : OrthonormalBasis ι'' ℝ V) :
    innerForms (ι := ι) e = innerForms (ι := ι) f := by
  have h : innerFormsₗ (ι := ι) e = innerFormsₗ (ι := ι) f :=
    eq_innerForms_of_wedgeCovectors f _ (fun a b => innerForms_wedgeCovectors e a b)
  funext w θ
  simpa using DFunLike.congr_fun (DFunLike.congr_fun h w) θ

end Pointwise

end

end LeeLib.Ch02
