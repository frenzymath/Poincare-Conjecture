/-
Chapter 2, "Riemannian Metrics", §"Inner Products of Tensors": Exercises 2.38 and 2.39.

Two short exercises about the interaction of a Riemannian metric with a local frame `(E_i)`,
its `frameMatrix` `(g_ij)`, and the dual coframe `(e^i)`.

* **Exercise 2.38.**  Lee points out a potential ambiguity in the symbol `(g^{ij})`: it could
  mean the *inverse matrix* of `(g_ij)`, or the components of the contravariant tensor obtained
  by raising both indices of `g`.  These agree.  Formally, the "raise both indices" reading is the
  induced inner product on covectors, `LeeLib.Ch02.innerDual`, evaluated on the dual coframe; the
  statement `innerDual_dualCoframe` shows it equals the inverse of the `frameMatrix`.

* **Exercise 2.39.**  For a local frame `(E_i)` with dual coframe `(e^i)`, the following are
  equivalent: `(E_i)` is `g`-orthonormal; `(e^i)` is orthonormal in the induced cotangent inner
  product; and `(e^i)^♯ = E_i` for every `i`.  All three are packaged as
  `List.TFAE` in `tfae_orthonormal_frame_coframe`; each is equivalent to the frame matrix being the
  identity, which is the pivot of the proof.

Everything is pointwise, at a chosen `x` in the domain of the frame, and lives under the fibrewise
inner product `mathlib`'s `RiemannianBundle` installs on the tangent spaces from `g` — the same
setup as `MusicalIsomorphism`, `InnerForms` and `VolumeForm`.  The three pieces of machinery reused
are the sharp/flat maps `LeeLib.Ch02.sharp`/`flat`, the covector inner product
`LeeLib.Ch02.innerDual`, and the frame data `RiemannianMetric.frameMatrix`/`dualCoframe`.
-/
import LeeLib.Ch02.VolumeForm
import LeeLib.Ch02.InnerForms
import LeeLib.Ch02.MusicalIsomorphism

namespace LeeLib.Ch02

open Bundle Manifold Matrix Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace Matrix

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianMetric

variable {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} {u : Set M} {x : M}

/-! ### The sharp of a dual-coframe covector -/

/-- **The raised dual coframe** `(e^i)^♯ = ∑_k g^{ik} E_k`.

The Riesz representative of the dual covector `e^i = g^{il} g(E_l, ·)` is `∑_k g^{ik} E_k`, obtained
by pairing against the flat map: applying `♭` to the claimed right-hand side reproduces `e^i`.  This
is Lee's basis formula (2.13) for `♯` specialized to the dual coframe, and it is the computational
core of both exercises below. -/
theorem sharpL_dualCoframe (g : RiemannianMetric I M) (j : Fin (finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    sharpL (g.dualCoframe Y x j) = ∑ k, (g.frameMatrix Y x)⁻¹ j k • Y k x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hsf : sharpL (flatL (∑ k, (g.frameMatrix Y x)⁻¹ j k • Y k x))
      = ∑ k, (g.frameMatrix Y x)⁻¹ j k • Y k x :=
    (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm_apply_apply _
  rw [← hsf]
  congr 1
  ext w
  rw [flatL_apply, sum_inner]
  simp only [RiemannianMetric.dualCoframe, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, real_inner_smul_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/-! ### Lee, Exercise 2.38 -/

/-- **Lee, Exercise 2.38.**  The two readings of `(g^{ij})` agree.

The "inverse matrix" reading is `(g.frameMatrix Y x)⁻¹`; the "raise both indices" reading is the
induced inner product on covectors `innerDual`, evaluated on the dual coframe `(e^i)`.  They are
equal:
`⟨e^i, e^j⟩_g = g^{ij}`.

The proof unwinds `⟨e^i, e^j⟩_g = e^i((e^j)^♯)` via the sharp of the dual coframe
(`sharpL_dualCoframe`) and the duality `e^i(E_k) = δ^i_k` (`dualCoframe_apply_frame`), collapsing to
`g^{ji}`, which equals `g^{ij}` because the frame matrix — hence its inverse — is symmetric. -/
theorem innerDual_dualCoframe (g : RiemannianMetric I M)
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u) (i j : Fin (finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    innerDual (g.dualCoframe Y x i) (g.dualCoframe Y x j) = (g.frameMatrix Y x)⁻¹ i j := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [← apply_sharpL, sharpL_dualCoframe g j, map_sum]
  simp only [map_smul, smul_eq_mul, dualCoframe_apply_frame g hY hx i, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- remaining goal: `g^{j i} = g^{i j}`, i.e. symmetry of the inverse frame matrix
  have hGsymm : (g.frameMatrix Y x)ᵀ = g.frameMatrix Y x := by
    ext a b
    simp only [Matrix.transpose_apply, RiemannianMetric.frameMatrix, Matrix.of_apply]
    exact g.symm x (Y b x) (Y a x)
  have h1 : (g.frameMatrix Y x)⁻¹ᵀ = (g.frameMatrix Y x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hGsymm]
  calc (g.frameMatrix Y x)⁻¹ j i
      = (g.frameMatrix Y x)⁻¹ᵀ i j := (Matrix.transpose_apply _ i j).symm
    _ = (g.frameMatrix Y x)⁻¹ i j := by rw [h1]

/-! ### Lee, Exercise 2.39 -/

/-- **Lee, Exercise 2.39.**  For a local frame `(E_i)` with dual coframe `(e^i)`, at a point `x` in
the frame's domain the following are equivalent:

* `(a)` `(E_i)` is `g`-orthonormal: `⟨E_i, E_j⟩_g = δ_{ij}`;
* `(b)` `(e^i)` is orthonormal for the induced cotangent inner product: `⟨e^i, e^j⟩_g = δ^{ij}`;
* `(c)` `(e^i)^♯ = E_i` for every `i`.

Each is equivalent to the frame matrix `(g_ij)` being the identity, which is the hinge of the
argument: `(a)` says so directly; `(b)` says so of the inverse (via Exercise 2.38), and a matrix
equals `1` iff its inverse does; `(c)` says `♭` sends `E_i` to `e^i`, which pairs against the frame
back to `(a)`. -/
theorem tfae_orthonormal_frame_coframe (g : RiemannianMetric I M)
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    List.TFAE
      [ ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0,
        ∀ i j, innerDual (g.dualCoframe Y x i) (g.dualCoframe Y x j) = if i = j then 1 else 0,
        ∀ i, sharp g x (g.dualCoframe Y x i) = Y i x ] := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  -- `⟨E_i, E_j⟩ = δ_{ij}` for all `i, j` is exactly `frameMatrix = 1`; likewise for the inverse.
  have hone : ∀ N : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ,
      (∀ i j, N i j = if i = j then (1 : ℝ) else 0) ↔ N = 1 := fun N => by
    constructor
    · intro h; ext i j; rw [Matrix.one_apply]; exact h i j
    · intro h i j; rw [h, Matrix.one_apply]
  -- `frameMatrix = 1 ↔ frameMatrix⁻¹ = 1`, using that the frame matrix is invertible.
  have hdet : (g.frameMatrix Y x).det ≠ 0 := g.frameMatrix_det_ne_zero hY hx
  have hinv : g.frameMatrix Y x = 1 ↔ (g.frameMatrix Y x)⁻¹ = 1 := by
    constructor
    · intro h; rw [h, inv_one]
    · intro h
      have hmul := Matrix.mul_nonsing_inv (g.frameMatrix Y x) (Ne.isUnit hdet)
      rwa [h, Matrix.mul_one] at hmul
  have ha1 : (∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0)
      ↔ g.frameMatrix Y x = 1 := hone (g.frameMatrix Y x)
  have hb1 : (∀ i j, innerDual (g.dualCoframe Y x i) (g.dualCoframe Y x j) = if i = j then 1 else 0)
      ↔ (g.frameMatrix Y x)⁻¹ = 1 := by
    rw [← hone ((g.frameMatrix Y x)⁻¹)]
    exact forall_congr' fun i => forall_congr' fun j => by rw [innerDual_dualCoframe g hY hx i j]
  tfae_have 1 ↔ 2 := ha1.trans (hinv.trans hb1.symm)
  tfae_have 3 → 1 := by
    intro hc i j
    rw [← hc i, ← RiemannianMetric.innerAt_apply, innerAt_sharp, dualCoframe_apply_frame g hY hx i j]
  tfae_have 1 → 3 := by
    intro ha i
    refine flat_injective g x ?_
    rw [flat_sharp]
    show g.dualCoframe Y x i = g.inner x (Y i x)
    refine ContinuousLinearMap.coe_injective (Basis.ext (hY.toBasisAt hx) fun k => ?_)
    simp only [ContinuousLinearMap.coe_coe, hY.toBasisAt_coe hx k,
      dualCoframe_apply_frame g hY hx i k]
    exact (ha i k).symm
  tfae_finish

end RiemannianMetric

end

end LeeLib.Ch02
