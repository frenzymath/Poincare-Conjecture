/- Vendored from DoCarmo `OpenGALib/Riemannian/TensorBundle/SmoothOrthoFrame.lean` (identical shared OpenGA infra).
   Namespace `Riemannian` mapped to `PetersenLib`; `AffineConnection` renamed
   `DCAffineConnection` to keep the Petersen blueprint anchor name free.
   Engineering infrastructure only — not a blueprint node. -/
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import PetersenLib.Vendored.OpenGA.Auxiliary.OrthonormalBasisDiagonal
import PetersenLib.Foundations.RiemannianMetric
import PetersenLib.Vendored.OpenGA.TangentBundle.TangentSmooth
import PetersenLib.Vendored.OpenGA.TensorBundle.SmoothOrthoFrame.ChartBasis
import PetersenLib.Vendored.OpenGA.TensorBundle.SmoothOrthoFrame.Orthonormality

/-!
# Smooth orthonormal local frame from the chart frame

For a Riemannian manifold $(M, g)$ and a base point $\alpha : M$:

* `chartBasisVecFiber α i b` — the $i$-th tangent vector at $b$ obtained
  by transporting the $i$-th model-space basis vector through the
  inverse of the tangent trivialization centred at $\alpha$ (smooth on
  the trivialization base set, junk off it).
* `chartFrameNormFiber g α b i` — fiberwise $g$-Gram-Schmidt
  orthonormalisation of `chartBasisVecFiber α · b`.
* `smoothOrthoFrame g α i` — globally-smooth tangent-bundle section
  obtained by multiplying `chartFrameNorm g α i` by a smooth bump
  function whose support lies in the chart source; identically zero off
  the chart source, equal to the un-bumped Gram-Schmidt frame on
  `smoothOrthoFrameNbhd α`.

Used downstream by the heart-of-Bochner sum identity, where the smooth
orthonormal frame is the basis along which $\nabla^2(\nabla f)$'s trace
becomes $\Delta_g f$.

**Ground truth**: do Carmo §1 (chart-frame trivialization); Lee §3
(smooth bump functions); Petersen §1 (Gram-Schmidt). The construction
follows an external `differential-geometry` lib analog.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle

namespace PetersenLib
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


/-! ## Stage 3: bump-cutoff to produce a global section

The chart-frame normalised Gram-Schmidt is $C^\infty$ only on the chart
source. To produce a globally smooth tangent-bundle section, we
multiply by a smooth bump function centred at $\alpha$ whose support
lies inside the chart source. -/

/-- **Math.** A canonical smooth bump function centred at $\alpha$. It is $1$ on
a neighbourhood of $\alpha$ and supported in `(chartAt H α).source`
(the trivialization base set at $\alpha$). The existence is guaranteed
by `SmoothBumpFunction.instNonempty`. -/
noncomputable def chartBumpAt (α : M) : SmoothBumpFunction I α :=
  Classical.arbitrary (SmoothBumpFunction I α)

/-- **Math.** **Smooth orthonormal frame**. The $i$-th tangent-bundle section of a
smooth $g$-orthonormal local frame attached to the base point $\alpha$.
On the neighbourhood of $\alpha$ where the chart bump function
`chartBumpAt α` equals $1$, this section equals the $g$-Gram-Schmidt
orthonormalisation of the chart basis frame. Off the support of the
bump (which is contained in the chart source), the section is zero.

The fiber-by-fiber definition uses the chart bump function multiplied
by the chart-frame normalised Gram-Schmidt step. -/
noncomputable def smoothOrthoFrame
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    VectorFieldSection I M :=
  fun b => (chartBumpAt (I := I) (M := M) α : M → ℝ) b •
    chartFrameNorm (I := I) g α i b

/-- **Math.** The open subset of $M$ on which `smoothOrthoFrame g α` is guaranteed
to be a $g$-orthonormal smooth basis: the (open) set where the chart
bump function equals $1$. -/
noncomputable def smoothOrthoFrameNbhd (α : M) : Set M :=
  {b : M | (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1}

/-- **Math.** The neighbourhood `smoothOrthoFrameNbhd α` is in `𝓝 α`. -/
lemma smoothOrthoFrameNbhd_mem_nhds (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ∈ 𝓝 α := by
  classical
  exact (chartBumpAt (I := I) (M := M) α).eventuallyEq_one

/-- **Math.** The centre $\alpha$ belongs to `smoothOrthoFrameNbhd α`. -/
lemma mem_smoothOrthoFrameNbhd_self (α : M) :
    α ∈ smoothOrthoFrameNbhd (I := I) (M := M) α := by
  classical
  change (chartBumpAt (I := I) (M := M) α : M → ℝ) α = 1
  exact (chartBumpAt (I := I) (M := M) α).eq_one

/-- **Math.** On `smoothOrthoFrameNbhd α`, the smooth orthonormal
frame agrees with the un-bumped Gram-Schmidt step. -/
lemma smoothOrthoFrame_eq_on_nbhd
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    smoothOrthoFrame (I := I) g α i b =
      chartFrameNorm (I := I) g α i b := by
  classical
  unfold smoothOrthoFrame
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  rw [hb1, one_smul]

/-- **Eng.** `smoothOrthoFrameNbhd α` is contained in the chart
source `(chartAt H α).source`. -/
lemma smoothOrthoFrameNbhd_subset_chartAt_source (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆ (chartAt H α).source := by
  classical
  intro b hb
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  have hsupp : b ∈ Function.support (chartBumpAt (I := I) (M := M) α : M → ℝ) := by
    change (chartBumpAt (I := I) (M := M) α : M → ℝ) b ≠ 0
    rw [hb1]; exact one_ne_zero
  exact (chartBumpAt (I := I) (M := M) α).support_subset_source hsupp

/-- **Eng.** `smoothOrthoFrameNbhd α` is contained in the
trivialization base set
`(trivializationAt E (TangentSpace I) α).baseSet`. -/
lemma smoothOrthoFrameNbhd_subset_baseSet (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro b hb
  rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
  exact smoothOrthoFrameNbhd_subset_chartAt_source (I := I) (M := M) α hb

/-! ## Stage 5: orthonormality of `smoothOrthoFrame`

On the neighbourhood `smoothOrthoFrameNbhd α`, the smooth orthonormal
frame agrees with the un-bumped Gram-Schmidt frame, which is
$g$-orthonormal at every base-set point (Stage 3a). Combining the two
yields orthonormality of `smoothOrthoFrame g α` on
`smoothOrthoFrameNbhd α`, and (via $\alpha \in \mathrm{Nbhd}\,\alpha$)
at the centre $\alpha$ itself. -/

/-- **Math.** **Orthonormality of `smoothOrthoFrame` on the bump-equals-1
neighbourhood.** For $b \in \mathrm{smoothOrthoFrameNbhd}\,\alpha$,
the smooth orthonormal frame at $b$ is $g$-orthonormal. -/
theorem smoothOrthoFrame_orthonormal
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (smoothOrthoFrame (I := I) g α i b)
        (smoothOrthoFrame (I := I) g α j b) =
      if i = j then 1 else 0 := by
  rw [smoothOrthoFrame_eq_on_nbhd (I := I) g α i hb,
      smoothOrthoFrame_eq_on_nbhd (I := I) g α j hb]
  exact chartFrameNorm_orthonormal (I := I) g α
    (smoothOrthoFrameNbhd_subset_baseSet (I := I) (M := M) α hb) i j

/-- **Math.** **Orthonormality of `smoothOrthoFrame` at the centre.** The frame
`smoothOrthoFrame g α` is $g_\alpha$-orthonormal. Direct corollary of
`smoothOrthoFrame_orthonormal` at $\alpha$, since
$\alpha \in \mathrm{smoothOrthoFrameNbhd}\,\alpha$. -/
theorem smoothOrthoFrame_orthonormal_at_center
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner α
        (smoothOrthoFrame (I := I) g α i α)
        (smoothOrthoFrame (I := I) g α j α) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal (I := I) g α
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) α) i j


/-! ## Stage 7: smoothOrthoFrame as an `OrthonormalBasis` at $\alpha$,
and the basis-invariance bridge

For the heart-of-Bochner closure, we need to compare diagonal sums
indexed by the smooth orthonormal frame (smooth-section-friendly) with
diagonal sums indexed by `stdOrthonormalBasis ℝ (TangentSpace I α)`
(the basis used in the existing `connectionLaplacian` /
`scalarLaplacian` API). The values $b_i = \mathrm{smoothOrthoFrame}\,
\mathrm{hm.metric}\,\alpha\,i\,\alpha \in T_\alpha M$ form an
orthonormal family at $\alpha$ (in the InnerProductSpace sense, via the
`HasMetric I M` typeclass bridge), and so can be packaged as an
`OrthonormalBasis`. Combined with
`OrthonormalBasis.sum_apply_diagonal_invariant`, this gives
basis-invariance of $\sum_i B(b_i)(b_i)$ for any bilinear
$B : T_\alpha M \to_\ell T_\alpha M \to_\ell W$.

This stage uses `[HasMetric I M]` and instantiates the construction at
the canonical metric `hm.metric`; the InnerProductSpace inner product
`⟪·, ·⟫_ℝ` on `TangentSpace I α` is then definitionally
`hm.metric.inner α`. -/

variable [hm : HasMetric I M]

open scoped InnerProductSpace

/-- **Math.** Orthonormality of `smoothOrthoFrame hm.metric α · α` in the
`InnerProductSpace ℝ` sense (via `⟪·, ·⟫_ℝ` rather than
`hm.metric.inner α`). Direct from
`smoothOrthoFrame_orthonormal_at_center` and the def-eq
`⟪v, w⟫_ℝ = hm.metric.inner α v w` via the `RiemannianBundle` routing
from `instRiemannianBundleOfHasMetric`. -/
theorem smoothOrthoFrame_inner_at_center (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ⟪smoothOrthoFrame (I := I) hm.metric α i α,
        smoothOrthoFrame (I := I) hm.metric α j α⟫_ℝ =
      if i = j then 1 else 0 := by
  -- The InnerProductSpace inner product on `TangentSpace I α` (via `HasMetric I M` →
  -- `RiemannianBundle (TangentSpace I)`) is definitionally `hm.metric.inner α`.
  show hm.metric.inner α _ _ = _
  exact smoothOrthoFrame_orthonormal_at_center (I := I) hm.metric α i j

/-- **Math.** `smoothOrthoFrame hm.metric α · α` is an `Orthonormal` family in
`TangentSpace I α`. -/
theorem smoothOrthoFrame_orthonormal_family (α : M) :
    Orthonormal ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        smoothOrthoFrame (I := I) hm.metric α i α) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  exact smoothOrthoFrame_inner_at_center (I := I) α i j

/-- **Math.** **`smoothOrthoFrame` packaged as an `OrthonormalBasis` at $\alpha$**.
The smooth orthonormal frame evaluated at the centre $\alpha$, indexed
by `Fin (Module.finrank ℝ E)`, with the canonical orthonormality from
`smoothOrthoFrame_orthonormal_family`. Constructed via
`basisOfOrthonormalOfCardEqFinrank` (orthonormal family of correct
cardinality is a basis) and `Basis.toOrthonormalBasis` (upgrade to
`OrthonormalBasis` given the orthonormality witness, which transfers
through `coe_basisOfOrthonormalOfCardEqFinrank`). -/
noncomputable def smoothOrthoFrameOrthonormalBasis (α : M) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I α) := by
  classical
  have hOrth := smoothOrthoFrame_orthonormal_family (I := I) α
  -- `TangentSpace I α` reduces to `E` via Mathlib's `@[reducible] def TangentSpace`.
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I α) := Fintype.card_fin _
  refine (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis ?_
  rw [coe_basisOfOrthonormalOfCardEqFinrank]
  exact hOrth

@[simp] theorem smoothOrthoFrameOrthonormalBasis_apply (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    smoothOrthoFrameOrthonormalBasis (I := I) α i =
      smoothOrthoFrame (I := I) hm.metric α i α := by
  unfold smoothOrthoFrameOrthonormalBasis
  rw [Module.Basis.coe_toOrthonormalBasis]
  exact congrFun
    (coe_basisOfOrthonormalOfCardEqFinrank
      (smoothOrthoFrame_orthonormal_family (I := I) α) _) i

/-- **Math.** **Basis-change bridge at $\alpha$**: for any bilinear
$B : T_\alpha M \to_\ell T_\alpha M \to_\ell W$ and any
`OrthonormalBasis b` of `TangentSpace I α`, the diagonal sum over
the smooth orthonormal frame equals the diagonal sum over $b$.

Applied with $b = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,
(T_\alpha M)$, this bridges the heart-of-Bochner formulation against
`smoothOrthoFrame` (which is smoothness-friendly for the algebraic
chain) to the existing API formulation against `stdOrthonormalBasis`
(used in `connectionLaplacian` / `scalarLaplacian`). -/
theorem sum_diagonal_smoothOrthoFrame_eq_orthonormalBasis
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (α : M)
    (B : TangentSpace I α →ₗ[ℝ] TangentSpace I α →ₗ[ℝ] W)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I α)) :
    ∑ i, B (smoothOrthoFrame (I := I) hm.metric α i α)
            (smoothOrthoFrame (I := I) hm.metric α i α) =
      ∑ i, B (b i) (b i) := by
  have h := OrthonormalBasis.sum_apply_diagonal_invariant
    (smoothOrthoFrameOrthonormalBasis (I := I) α) b B
  -- Rewrite LHS sum via the simp lemma for smoothOrthoFrameOrthonormalBasis.
  simp only [smoothOrthoFrameOrthonormalBasis_apply] at h
  exact h

/-- **Math.** **Basis-change bridge to `stdOrthonormalBasis`**: specialization of
`sum_diagonal_smoothOrthoFrame_eq_orthonormalBasis` with
$b = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,(T_\alpha M)$ — the
basis used by `connectionLaplacian` / `scalarLaplacian` / the
heart-of-Bochner statement. -/
theorem sum_diagonal_smoothOrthoFrame_eq_std
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (α : M)
    (B : TangentSpace I α →ₗ[ℝ] TangentSpace I α →ₗ[ℝ] W) :
    ∑ i, B (smoothOrthoFrame (I := I) hm.metric α i α)
            (smoothOrthoFrame (I := I) hm.metric α i α) =
      ∑ i, B ((stdOrthonormalBasis ℝ (TangentSpace I α)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I α)) i) :=
  sum_diagonal_smoothOrthoFrame_eq_orthonormalBasis (I := I) α B
    (stdOrthonormalBasis ℝ (TangentSpace I α))

/-! ### `smoothOrthoFrame` as `OrthonormalBasis` at any point in the nbhd

At any `b ∈ smoothOrthoFrameNbhd α`, the frame `(smoothOrthoFrame hm.metric α i b)_i`
forms a `g_b`-orthonormal basis of `T_bM`. Same construction as
`smoothOrthoFrameOrthonormalBasis α` but parameterised by the nbhd point. -/

/-- **Math.** `InnerProductSpace` form of `smoothOrthoFrame_orthonormal` at `b ∈ nbhd α`,
routed through `HasMetric I M` → `InnerProductSpace ℝ (TangentSpace I b)`. -/
theorem smoothOrthoFrame_inner_at_nbhd (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    ⟪smoothOrthoFrame (I := I) hm.metric α i b,
        smoothOrthoFrame (I := I) hm.metric α j b⟫_ℝ =
      if i = j then 1 else 0 := by
  show hm.metric.inner b _ _ = _
  exact smoothOrthoFrame_orthonormal (I := I) hm.metric α hb i j

/-- **Math.** `smoothOrthoFrame hm.metric α · b` is an `Orthonormal` family in `T_bM`. -/
theorem smoothOrthoFrame_orthonormal_family_at_nbhd (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    Orthonormal ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        smoothOrthoFrame (I := I) hm.metric α i b) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  exact smoothOrthoFrame_inner_at_nbhd (I := I) α hb i j

/-- **Math.** **`smoothOrthoFrame` packaged as an `OrthonormalBasis` at `b ∈ nbhd α`**.
Parametric in the nbhd point. -/
noncomputable def smoothOrthoFrameOrthonormalBasis_at_nbhd (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) := by
  classical
  have hOrth := smoothOrthoFrame_orthonormal_family_at_nbhd (I := I) α hb
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I b) := Fintype.card_fin _
  refine (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis ?_
  rw [coe_basisOfOrthonormalOfCardEqFinrank]
  exact hOrth

@[simp] theorem smoothOrthoFrameOrthonormalBasis_at_nbhd_apply
    (α : M) {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    smoothOrthoFrameOrthonormalBasis_at_nbhd (I := I) α hb i =
      smoothOrthoFrame (I := I) hm.metric α i b := by
  unfold smoothOrthoFrameOrthonormalBasis_at_nbhd
  rw [Module.Basis.coe_toOrthonormalBasis]
  exact congrFun
    (coe_basisOfOrthonormalOfCardEqFinrank
      (smoothOrthoFrame_orthonormal_family_at_nbhd (I := I) α hb) _) i

/-- **Math.** **Basis-change bridge at `b ∈ nbhd α` (to `stdOrthonormalBasis`)**:
the diagonal sum over the smooth orthonormal frame at any nbhd point `b`
equals the diagonal sum over `stdOrthonormalBasis ℝ (T_bM)`. Parametric
version of `sum_diagonal_smoothOrthoFrame_eq_std`. -/
theorem sum_diagonal_smoothOrthoFrame_at_nbhd_eq_std
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (α : M) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (B : TangentSpace I b →ₗ[ℝ] TangentSpace I b →ₗ[ℝ] W) :
    ∑ i, B (smoothOrthoFrame (I := I) hm.metric α i b)
            (smoothOrthoFrame (I := I) hm.metric α i b) =
      ∑ i, B ((stdOrthonormalBasis ℝ (TangentSpace I b)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I b)) i) := by
  have h := OrthonormalBasis.sum_apply_diagonal_invariant
    (smoothOrthoFrameOrthonormalBasis_at_nbhd (I := I) α hb)
    (stdOrthonormalBasis ℝ (TangentSpace I b)) B
  simp only [smoothOrthoFrameOrthonormalBasis_at_nbhd_apply] at h
  exact h

end Tensor
end PetersenLib

end
