import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Chart-basis tangent sections and the un-normalised $g$-Gram-Schmidt

Construction-only Foundation for `Tensor/SmoothOrthoFrame.lean`:

* **Stage 1** — `chartBasisVecFiber α i b` transports the $i$-th
  model-space basis vector through the inverse of the tangent
  trivialization centred at $\alpha$, smooth on the base set and junk
  off it; `chartBasisVec`, `chartBasisFamily`, plus the linear-
  independence of the chart-basis family.
* **Stage 2** — fiberwise $g$-Gram-Schmidt: `chartFrameRawFiber` (the
  un-normalised vector), `chartFrameNormFiber` (the normalised vector),
  `chartFrameNorm` (the section-form package). Includes the basic
  recurrence identities (`chartFrameNormFiber_eq`,
  `chartFrameRawFiber_at_zero`, `chartFrameNormFiber_at_zero`,
  `g_inner_normalised`, `chartFrameNormFiber_at_zero_norm`).

Stage 3a's orthonormality proof lives in
`Tensor/SmoothOrthoFrame/Orthonormality.lean`; Stage 6's smoothness
chain lives in `Tensor/SmoothOrthoFrame/Smoothness.lean`. Anchor
`Tensor/SmoothOrthoFrame.lean` imports both and packages the public
`smoothOrthoFrame` + `OrthonormalBasis` API.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 1: chart-basis tangent sections -/

/-- **Math.** The $i$-th pointwise tangent vector of the chart-local
frame attached to $\alpha$: image of the $i$-th model-space basis vector
under `(trivializationAt E (TangentSpace I) α).symm b` on the base set,
junk off it. Smooth on `(chartAt H α).source`. -/
def chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    TangentSpace I b :=
  (trivializationAt E (TangentSpace I) α).symm b ((Module.finBasis ℝ E) i)

/-- **Math.** Section-form packaging of `chartBasisVecFiber α i` as
`M → TotalSpace E _`. -/
def chartBasisVec (α : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun b => TotalSpace.mk' E b (chartBasisVecFiber (I := I) α i b)

@[simp] lemma chartBasisVec_proj
    (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    (chartBasisVec (I := I) α i b).proj = b := rfl

@[simp] lemma chartBasisVec_snd
    (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    (chartBasisVec (I := I) α i b).2 = chartBasisVecFiber (I := I) α i b := rfl

/-- **Eng.** On the base set, the trivialization sends the chart-basis
vector to the constant model-basis vector. -/
lemma trivializationAt_chartBasisVec_snd
    (α : M) (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (trivializationAt E (TangentSpace I) α
        ⟨b, chartBasisVecFiber (I := I) α i b⟩).2
      = (Module.finBasis ℝ E) i := by
  have h := (trivializationAt E (TangentSpace I) α).apply_mk_symm hb
    ((Module.finBasis ℝ E) i)
  simpa [chartBasisVecFiber] using congrArg Prod.snd h

/-- **Math.** The chart-basis tangent-bundle section is smooth on the
base set of the trivialization at $\alpha$. -/
lemma chartBasisVec_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) α i)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) α)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun b => chartBasisVecFiber (I := I) α i b)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (Module.finBasis ℝ E) i)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro b hb
  exact (trivializationAt_chartBasisVec_snd (I := I) α i hb)

/-- **Math.** The chart-basis family at $b \in \mathrm{baseSet}$ is a
basis of `TangentSpace I b`, obtained by transporting the fixed
model-space basis through the trivialization. -/
def chartBasisFamily (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
  (Module.finBasis ℝ E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb).symm)

lemma chartBasisFamily_apply (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) α hb i =
      chartBasisVecFiber (I := I) α i b := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

/-- **Math.** The chart-basis family is linearly independent at each
base-set point. -/
lemma chartBasisFamily_linearIndependent (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) := by
  have h := (chartBasisFamily (I := I) α hb).linearIndependent
  have hcongr :
      (chartBasisFamily (I := I) α hb : Fin (Module.finrank ℝ E) → TangentSpace I b)
        = fun i => chartBasisVecFiber (I := I) α i b := by
    funext i
    exact chartBasisFamily_apply (I := I) α hb i
  rw [← hcongr]
  exact h

/-! ## Stage 2: hand-rolled $g$-Gram-Schmidt of the chart frame, fiberwise

For a fixed point $b : M$, we recursively build the orthonormalised
basis `chartFrameNormFiber g α b i ∈ T_bM`, with
$i : \mathrm{Fin}\,(\mathrm{Module.finrank}\,\mathbb{R}\,E)$.

The recursion uses Lean's well-founded recursion on `i.val`: each step
references earlier fiber-values, and termination is by strict decrease
of the index. -/

/-- **Math.** The normalised Gram-Schmidt vector for the chart frame, in a fixed
fiber $b$. Defined by well-founded recursion on `i.val`. -/
noncomputable def chartFrameNormFiber
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  let v : TangentSpace I b := chartBasisVecFiber (I := I) α i b
  let raw : TangentSpace I b :=
    v - ∑ j : Fin i.val,
      (g.inner b v
          (chartFrameNormFiber g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        chartFrameNormFiber g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩
  (Real.sqrt (g.inner b raw raw))⁻¹ • raw
termination_by i.val
decreasing_by exact j.isLt

/-- **Math.** Section-form packaging of `chartFrameNormFiber`
in $b$: `chartFrameNorm g α i b ∈ T_bM`. -/
noncomputable def chartFrameNorm
    (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) : TangentSpace I b :=
  chartFrameNormFiber (I := I) g α b i

/-- **Math.** The unnormalised Gram-Schmidt vector at index $i$, in a fixed fiber
$b$:
$$\mathrm{raw}_i(b) := v_i(b) - \sum_{j < i} \langle v_i(b), e_j(b)\rangle_g \, e_j(b),$$
where $v_i(b) = \mathrm{chartBasisVecFiber}\,\alpha\,i\,b$ and
$e_j(b) = \mathrm{chartFrameNormFiber}\,g\,\alpha\,b\,j$. -/
noncomputable def chartFrameRawFiber
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  chartBasisVecFiber (I := I) α i b -
    ∑ j : Fin i.val,
      (g.inner b (chartBasisVecFiber (I := I) α i b)
          (chartFrameNormFiber (I := I) g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        chartFrameNormFiber (I := I) g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- **Eng.** Recursive expansion of `chartFrameNormFiber` at index $i$.
normalised vector is `(Real.sqrt (g.inner b raw raw))⁻¹ • raw`. -/
lemma chartFrameNormFiber_eq
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartFrameNormFiber (I := I) g α b i =
      (Real.sqrt (g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
        chartFrameRawFiber (I := I) g α b i := by
  unfold chartFrameNormFiber chartFrameRawFiber
  rfl

/-- **Eng.** At the zeroth index, the unnormalised Gram-Schmidt vector reduces to
the chart-basis vector itself (the empty sum vanishes). -/
lemma chartFrameRawFiber_at_zero
    (g : RiemannianMetric I M) (α : M) (b : M) :
    chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  unfold chartFrameRawFiber
  simp

/-- **Eng.** At the zeroth index, the normalised Gram-Schmidt vector is the
chart-basis vector divided by its $g$-norm. -/
lemma chartFrameNormFiber_at_zero
    (g : RiemannianMetric I M) (α : M) (b : M) :
    chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      (Real.sqrt
          (g.inner b
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
        chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  rw [chartFrameNormFiber_eq, chartFrameRawFiber_at_zero]

/-- **Eng.** Generic normalisation calculation: for a vector $v$ in a fiber
with positive $g$-self-inner-product $N$, scaling $v$ by
$(\sqrt N)^{-1}$ gives a unit-norm vector. Pure continuous linear map/ring algebra in
the inner-product slot; isolated as a helper to keep
`chartFrameNormFiber_at_zero_norm` from re-elaborating continuous linear map types
inside `set`-chains. -/
lemma g_inner_normalised
    (g : RiemannianMetric I M) (b : M) (v : TangentSpace I b)
    (hpos : 0 < g.inner b v v) :
    g.inner b ((Real.sqrt (g.inner b v v))⁻¹ • v)
              ((Real.sqrt (g.inner b v v))⁻¹ • v) = 1 := by
  set s : ℝ := Real.sqrt (g.inner b v v) with hs_def
  have hs_sq : s * s = g.inner b v v := Real.mul_self_sqrt hpos.le
  -- Bilinearity of `g.inner b`: pull `s⁻¹` out of each slot via `map_smul`
  -- on the appropriate continuous linear map. The first-slot pull yields a continuous linear map equality
  -- (smul of continuous linear maps); evaluating at `s⁻¹ • v` then re-applies smul to extract
  -- the second factor. Final shape: `s⁻¹ * (s⁻¹ * g.inner b v v)`.
  have h_left : g.inner b (s⁻¹ • v) = s⁻¹ • g.inner b v := map_smul _ _ _
  have h_right : g.inner b v (s⁻¹ • v) = s⁻¹ * g.inner b v v := by
    rw [map_smul]; rfl
  calc g.inner b (s⁻¹ • v) (s⁻¹ • v)
      = (s⁻¹ • g.inner b v) (s⁻¹ • v) := by rw [h_left]
    _ = s⁻¹ * g.inner b v (s⁻¹ • v) := by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = s⁻¹ * (s⁻¹ * g.inner b v v) := by rw [h_right]
    _ = (s * s)⁻¹ * g.inner b v v := by rw [mul_inv]; ring
    _ = (g.inner b v v)⁻¹ * g.inner b v v := by rw [hs_sq]
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- **Math.** At a base-set point and at the zeroth index, the normalised
Gram-Schmidt vector is $g$-unit-norm. -/
lemma chartFrameNormFiber_at_zero_norm
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    g.inner b
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩) = 1 := by
  rw [chartFrameNormFiber_at_zero]
  have hv_ne :
      chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b ≠ 0 :=
    (chartBasisFamily_linearIndependent (I := I) α hb).ne_zero _
  exact g_inner_normalised (I := I) g b _ (g.pos b _ hv_ne)

end Tensor
end Riemannian
