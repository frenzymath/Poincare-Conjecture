import PoincareLib.Ch01.PointwiseCurvature
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame

/-!
# Morgan–Tian Ch. 2 — smooth local orthonormal frames

Every point of a Riemannian manifold admits a **smooth local orthonormal
frame**: global smooth vector fields `F₁, …, F_n` that are `g`-orthonormal at
every point of a neighbourhood of `p`. Morgan–Tian use such frames implicitly
whenever they compute a metric trace "in an orthonormal frame at `p`" and then
differentiate the resulting identity — the step that turns the pointwise trace
`Δf = Σᵢ Hess(f)(Fᵢ, Fᵢ)` into the trace-commutation identity of the Bochner
formula (blueprint `lem:function-bochner-formula`).

The construction is the `g`-Gram–Schmidt orthonormalisation of the chart frame
(`Riemannian.Tensor.chartFrameNormFiber`, from OpenGALib), whose orthonormality
on the trivialization base set is already known
(`chartFrameNormFiber_orthonormal`). This file supplies the missing analytic
ingredient and the packaging:

* `contMDiffOn_metricInner_sections` — the metric pairing of two smooth
  sections is smooth on a set (setwise form of
  `RiemannianMetric.metricInner_contMDiffWithinAt`);
* `chartFrameNorm_section_contMDiffOn` — **smoothness of the Gram–Schmidt
  frame** on the trivialization base set: the recursion only involves the
  chart frame, metric pairings, and inversion of the positive square norm of
  the (nowhere-vanishing) raw vectors, so it preserves smoothness by strong
  induction on the index;
* `exists_orthonormalFrame` — the frame globalized to bundled
  `SmoothVectorField`s agreeing with the Gram–Schmidt frame near `p`
  (via `Riemannian.exists_smoothVectorField_eventuallyEq`), `g`-orthonormal
  on a neighbourhood of `p`;
* `orthonormalBasisOfMetricInner` (+ `_apply`) — a family of tangent vectors
  that is `g_q`-orthonormal, packaged as an `OrthonormalBasis` of
  `(T_qM, g_q)`, ready for the trace lemmas `laplacianAt_eq_sum` /
  `hessianNormSqAt_eq_sum`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:function-bochner-formula`); do Carmo, *Riemannian Geometry*,
Ch. 3 (orthonormal frames).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian Riemannian.Tensor Filter

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Smoothness of the Gram–Schmidt chart frame -/

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** The metric pairing of two smooth sections is smooth on a set:
setwise form of `RiemannianMetric.metricInner_contMDiffWithinAt`.
Blueprint: `lem:function-bochner-formula` (frame infrastructure). -/
theorem contMDiffOn_metricInner_sections (g : RiemannianMetric I M)
    {σ τ : Π q : M, TangentSpace I q} {s : Set M}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, σ q⟩ : TangentBundle I M)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, τ q⟩ : TangentBundle I M)) s) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => g.metricInner q (σ q) (τ q)) s :=
  fun b hb => g.metricInner_contMDiffWithinAt (hσ b hb) (hτ b hb)

omit [CompleteSpace E] in
/-- Strong-induction auxiliary for `chartFrameNorm_section_contMDiffOn`:
smoothness of the Gram–Schmidt frame section at every index `i` with
`i.val < n`, by induction on `n`. -/
private theorem chartFrameNorm_section_contMDiffOn_aux
    (g : RiemannianMetric I M) (α : M) (n : ℕ) :
    ∀ i : Fin (Module.finrank ℝ E), i.val < n →
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b => (⟨b, chartFrameNormFiber (I := I) g α b i⟩ : TangentBundle I M))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  induction n with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ n IH =>
    intro i hi
    -- the previous frame vectors are smooth sections (induction hypothesis)
    have hprev : ∀ j : Fin i.val,
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (fun b => (⟨b, chartFrameNormFiber (I := I) g α b
              ⟨j.val, lt_trans j.isLt i.isLt⟩⟩ : TangentBundle I M))
          (trivializationAt E (TangentSpace I) α).baseSet :=
      fun j => IH ⟨j.val, lt_trans j.isLt i.isLt⟩
        (lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp hi))
    -- the chart-basis section is smooth
    have hchart : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b => (⟨b, chartBasisVecFiber (I := I) α i b⟩ : TangentBundle I M))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α i
    -- the Gram–Schmidt coefficients are smooth
    have hcoef : ∀ j : Fin i.val,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b => g.inner b (chartBasisVecFiber (I := I) α i b)
            (chartFrameNormFiber (I := I) g α b ⟨j.val, lt_trans j.isLt i.isLt⟩))
          (trivializationAt E (TangentSpace I) α).baseSet :=
      fun j => contMDiffOn_metricInner_sections g hchart (hprev j)
    -- the projection sum is a smooth section
    have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b => (⟨b, ∑ j : Fin i.val,
            (g.inner b (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
              chartFrameNormFiber (I := I) g α b
                ⟨j.val, lt_trans j.isLt i.isLt⟩⟩ : TangentBundle I M))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.sum_section fun j _ => (hcoef j).smul_section (hprev j)
    -- the raw Gram–Schmidt section is smooth
    have hraw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b => (⟨b, chartFrameRawFiber (I := I) g α b i⟩ : TangentBundle I M))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      hchart.sub_section hsum
    -- the g-square-norm of the raw vector is positive and smooth on the base set
    have hpos : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
        0 < g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) := fun b hb =>
      g.pos b _ (chartFrameRawFiber_ne_zero (I := I) g α hb i)
    have hpair : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b => g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      contMDiffOn_metricInner_sections g hraw hraw
    -- the normalisation factor is smooth
    have hfactor : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b => (Real.sqrt (g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)))⁻¹)
        (trivializationAt E (TangentSpace I) α).baseSet := by
      intro b hb
      have hsq : ContDiffAt ℝ ∞ (fun t : ℝ => (Real.sqrt t)⁻¹)
          (g.inner b (chartFrameRawFiber (I := I) g α b i)
            (chartFrameRawFiber (I := I) g α b i)) :=
        (Real.contDiffAt_sqrt (hpos b hb).ne').inv
          (Real.sqrt_pos.mpr (hpos b hb)).ne'
      exact hsq.comp_contMDiffWithinAt
        (f := fun b => g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)) (hpair b hb)
    -- assemble: the normalised vector is `factor • raw`
    refine (hfactor.smul_section hraw).congr fun b hb => ?_
    show (⟨b, chartFrameNormFiber (I := I) g α b i⟩ : TangentBundle I M)
      = ⟨b, (Real.sqrt (g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
          chartFrameRawFiber (I := I) g α b i⟩
    rw [chartFrameNormFiber_eq]

-- `[CompleteSpace E]` is unused by the proof; the linter is silenced instead
-- of `omit`ting it, to keep the declaration's signature unchanged.
set_option linter.unusedSectionVars false in
/-- **Math.** **Smoothness of the `g`-Gram–Schmidt chart frame** on the
trivialization base set at `α`. By strong induction on the index: the raw
vector `rawᵢ = ∂ᵢ − Σ_{j<i} ⟨∂ᵢ, eⱼ⟩ eⱼ` is a linear combination, with smooth
metric-pairing coefficients, of the smooth chart frame and the (inductively
smooth) previous frame vectors; it is nowhere zero on the base set
(`chartFrameRawFiber_ne_zero`), so its square norm is smooth and positive,
and the normalisation `eᵢ = (√⟨rawᵢ, rawᵢ⟩)⁻¹ • rawᵢ` is smooth as well.
Blueprint: `lem:function-bochner-formula` (frame infrastructure). -/
theorem chartFrameNorm_section_contMDiffOn (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b => (⟨b, chartFrameNormFiber (I := I) g α b i⟩ : TangentBundle I M))
      (trivializationAt E (TangentSpace I) α).baseSet :=
  chartFrameNorm_section_contMDiffOn_aux g α (i.val + 1) i (Nat.lt_succ_self _)

/-! ### The local orthonormal frame, globalized -/

variable [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Existence of a smooth local orthonormal frame**: for every
point `p` there are global smooth vector fields `F₁, …, F_n`
(`n = dim M`) that form a `g`-orthonormal basis of the tangent space at
every point of some neighbourhood of `p`. The Gram–Schmidt chart frame is
smooth on the trivialization base set
(`chartFrameNorm_section_contMDiffOn`) and `g`-orthonormal there
(`chartFrameNormFiber_orthonormal`); extend it to global smooth fields
agreeing with it near `p` (`exists_smoothVectorField_eventuallyEq`).
Blueprint: `lem:function-bochner-formula` (frame infrastructure). -/
theorem exists_orthonormalFrame (g : RiemannianMetric I M) (p : M) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
        = if i = j then 1 else 0 := by
  classical
  have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  choose F hF using fun i : Fin (Module.finrank ℝ E) =>
    exists_smoothVectorField_eventuallyEq (I := I)
      (σ := fun q => chartFrameNormFiber (I := I) g p q i)
      (s := (trivializationAt E (TangentSpace I) p).baseSet) hopen
      (chartFrameNorm_section_contMDiffOn g p i) hbase
  refine ⟨F, fun i j => ?_⟩
  filter_upwards [hF i, hF j, hopen.mem_nhds hbase] with q hqi hqj hqbase
  rw [hqi, hqj]
  exact chartFrameNormFiber_orthonormal (I := I) g p hqbase i j

/-! ### Orthonormal families as orthonormal bases of the tangent fibre -/

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A family of tangent vectors at `q` that is `g_q`-orthonormal
(`⟨vᵢ, vⱼ⟩_g = δᵢⱼ`) and of cardinality `dim M`, packaged as an
**orthonormal basis** of `(T_qM, g_q)` — the form consumed by the metric
trace lemmas (`laplacianAt_eq_sum`, `hessianNormSqAt_eq_sum`).
Blueprint: `lem:function-bochner-formula` (frame infrastructure). -/
def orthonormalBasisOfMetricInner (g : RiemannianMetric I M) {q : M}
    {v : Fin (Module.finrank ℝ E) → TangentSpace I q}
    (hv : ∀ i j, g.metricInner q (v i) (v j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I q) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hOrth : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_tangentSpace_eq_metricInner g q (v i) (v j)]
    exact hv i j
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I q) := Fintype.card_fin _
  refine (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis ?_
  rw [coe_basisOfOrthonormalOfCardEqFinrank]
  exact hOrth

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The orthonormal basis `orthonormalBasisOfMetricInner` has the
given family as its vectors. Blueprint: `lem:function-bochner-formula`
(frame infrastructure). -/
@[simp] theorem orthonormalBasisOfMetricInner_apply (g : RiemannianMetric I M)
    {q : M} {v : Fin (Module.finrank ℝ E) → TangentSpace I q}
    (hv : ∀ i j, g.metricInner q (v i) (v j) = if i = j then 1 else 0)
    (i : Fin (Module.finrank ℝ E)) :
    orthonormalBasisOfMetricInner g hv i = v i := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold orthonormalBasisOfMetricInner
  rw [Module.Basis.coe_toOrthonormalBasis]
  exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank _ _) i

end PoincareLib

end
