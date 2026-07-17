import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame
import OpenGALib.Riemannian.TangentBundle.TangentSmooth

/-!
# Morgan–Tian Ch. 1 — smoothness of the local orthonormal frame

OpenGALib's `Riemannian.Tensor.smoothOrthoFrame g α` is a fiberwise
$g$-Gram–Schmidt orthonormalisation of the chart frame at `α`, cut off by a
smooth bump function. Its *orthonormality* on the bump-equals-one
neighbourhood is proved upstream (`smoothOrthoFrame_orthonormal`), but its
*smoothness* — the planned upstream `SmoothOrthoFrame/Smoothness.lean` stage —
was never proved. This file supplies that missing stage:

* `contMDiffOn_chartFrameNorm_section` — the normalised Gram–Schmidt frame
  `chartFrameNorm g α i` is a `C^∞` section of the tangent bundle on the
  trivialization base set at `α`, by strong induction along the Gram–Schmidt
  recursion (the coefficients are metric inner products of smooth sections,
  and the normalising factor `(√⟨raw, raw⟩)⁻¹` is smooth because `raw ≠ 0`
  on the base set);
* `contMDiff_smoothOrthoFrame_section` — the bump-cutoff frame
  `smoothOrthoFrame g α i` is a *globally* smooth section;
* `orthoFrameField g α i : SmoothVectorField I M` — the frame bundled as a
  smooth vector field;
* `orthoFrameSet α` — an *open* neighbourhood of `α` (the interior of the
  bump-equals-one set) on which the bundled frame is `g`-orthonormal at every
  point (`orthoFrameField_orthonormal`) and hence an orthonormal basis of
  each tangent space, with the expansion
  `v = ∑ i ⟨v, Eᵢ(q)⟩ Eᵢ(q)` (`orthoFrameField_expansion`).

This is the analytic backbone for differentiating metric traces (scalar
curvature, Ricci contractions) in the divergence lemma
`lem:div-ricci-scalar-curvature` and later Bochner-type identities: a metric
trace is locally a finite sum over this frame, so its directional derivatives
can be computed term by term.

Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure).
-/

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle

noncomputable section

set_option linter.unusedSectionVars false

namespace PoincareLib

open Riemannian Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-! ### Smoothness of the Gram–Schmidt frame on the base set -/

/-- **Math.** The metric inner product of two tangent-bundle sections that are
`C^∞` on a set is `C^∞` on that set: the `ContMDiffOn` form of
`Riemannian.RiemannianMetric.metricInner_contMDiffWithinAt`, phrased with
`g.inner`. Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem contMDiffOn_inner_sections (g : RiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x} {s : Set M}
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b => TotalSpace.mk' E b (v b)) s)
    (hw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b => TotalSpace.mk' E b (w b)) s) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b => g.inner b (v b) (w b)) s := by
  intro x hx
  exact RiemannianMetric.metricInner_contMDiffWithinAt g (hv x hx) (hw x hx)

/-- **Math.** **Smoothness of the fiberwise Gram–Schmidt frame.** The
normalised `g`-Gram–Schmidt orthonormalisation `chartFrameNorm g α i` of the
chart frame at `α` is a `C^∞` section of the tangent bundle on the
trivialization base set at `α`.

Proof: strong induction on `i`. The unnormalised vector
`raw i = v i − ∑_{j<i} ⟨v i, e j⟩ e j` is smooth because the chart-basis
section `v i` is smooth on the base set (`chartBasisVec_contMDiffOn`), the
previous frame vectors `e j` are smooth by induction, and the Gram–Schmidt
coefficients are metric inner products of smooth sections. The normalising
factor `(√⟨raw i, raw i⟩)⁻¹` is smooth because `raw i ≠ 0` on the base set
(`chartFrameRawFiber_ne_zero`) and `g` is positive definite, so the radicand
is positive and both `Real.sqrt` and the inverse are smooth there.

This is the missing upstream `SmoothOrthoFrame/Smoothness.lean` stage.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem contMDiffOn_chartFrameNorm_section (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b => TotalSpace.mk' E b (chartFrameNorm (I := I) g α i b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  -- strong induction on the index value
  suffices main : ∀ (n : ℕ) (i : Fin (Module.finrank ℝ E)), i.val < n →
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b => TotalSpace.mk' E b (chartFrameNormFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet from
    main (i.val + 1) i (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ n IH =>
    intro i hi
    -- smoothness of the unnormalised Gram–Schmidt vector
    have hraw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b => TotalSpace.mk' E b (chartFrameRawFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet := by
      -- the subtracted sum, as a pointwise section
      set w : ∀ b : M, TangentSpace I b := fun b =>
        ∑ j : Fin i.val,
          (g.inner b (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
            chartFrameNormFiber (I := I) g α b
              ⟨j.val, lt_trans j.isLt i.isLt⟩ with hw_def
      have hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (fun b => TotalSpace.mk' E b (chartBasisVecFiber (I := I) α i b))
          (trivializationAt E (TangentSpace I) α).baseSet :=
        chartBasisVec_contMDiffOn (I := I) α i
      have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (fun b => TotalSpace.mk' E b (w b))
          (trivializationAt E (TangentSpace I) α).baseSet := by
        have hterm : ∀ j : Fin i.val,
            ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
              (fun b => TotalSpace.mk' E b
                ((g.inner b (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
                  chartFrameNormFiber (I := I) g α b
                    ⟨j.val, lt_trans j.isLt i.isLt⟩))
              (trivializationAt E (TangentSpace I) α).baseSet := by
          intro j
          have hprev : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
              (fun b => TotalSpace.mk' E b
                (chartFrameNormFiber (I := I) g α b
                  ⟨j.val, lt_trans j.isLt i.isLt⟩))
              (trivializationAt E (TangentSpace I) α).baseSet :=
            IH ⟨j.val, lt_trans j.isLt i.isLt⟩
              (lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp hi))
          have hcoeff : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
              (fun b => g.inner b (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j.val, lt_trans j.isLt i.isLt⟩))
              (trivializationAt E (TangentSpace I) α).baseSet :=
            contMDiffOn_inner_sections g hv hprev
          exact fun x hx => (hcoeff x hx).smul_section (hprev x hx)
        have := ContMDiffOn.sum_section (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (∞ : ℕ∞ω))
          (s := (Finset.univ : Finset (Fin i.val)))
          (t := fun j (b : M) =>
            (g.inner b (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
              chartFrameNormFiber (I := I) g α b
                ⟨j.val, lt_trans j.isLt i.isLt⟩)
          (u := (trivializationAt E (TangentSpace I) α).baseSet)
          (fun j _ => hterm j)
        simpa [hw_def] using this
      have hsub := ContMDiffOn.sub_section (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (n := (∞ : ℕ∞ω))
        (s := fun b => chartBasisVecFiber (I := I) α i b) (t := w)
        (u := (trivializationAt E (TangentSpace I) α).baseSet) hv hsum
      refine hsub.congr fun b _ => ?_
      simp only [chartFrameRawFiber, Pi.sub_apply, hw_def]
    -- the normalising scalar is smooth on the base set
    have hradicand : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b => g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      contMDiffOn_inner_sections g hraw hraw
    have hpos : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
        0 < g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) := fun b hb =>
      g.pos b _ (chartFrameRawFiber_ne_zero (I := I) g α hb i)
    have hscalar : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b => (Real.sqrt (g.inner b (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)))⁻¹)
        (trivializationAt E (TangentSpace I) α).baseSet := by
      have hsqrt : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b => Real.sqrt (g.inner b (chartFrameRawFiber (I := I) g α b i)
            (chartFrameRawFiber (I := I) g α b i)))
          (trivializationAt E (TangentSpace I) α).baseSet := by
        intro x hx
        exact (Real.contDiffAt_sqrt (hpos x hx).ne').contMDiffAt.comp_contMDiffWithinAt
          x (hradicand x hx)
      exact hsqrt.inv₀ fun x hx => (Real.sqrt_pos.mpr (hpos x hx)).ne'
    -- assemble via the recursion identity
    have hres := ContMDiffOn.smul_section (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (∞ : ℕ∞ω))
      (f := fun b => (Real.sqrt (g.inner b (chartFrameRawFiber (I := I) g α b i)
        (chartFrameRawFiber (I := I) g α b i)))⁻¹)
      (s := fun b => chartFrameRawFiber (I := I) g α b i)
      (u := (trivializationAt E (TangentSpace I) α).baseSet) hscalar hraw
    refine hres.congr fun b _ => ?_
    rw [chartFrameNormFiber_eq (I := I) g α b i]
    rfl

/-! ### Global smoothness of the bump-cutoff frame -/

/-- **Math.** **Global smoothness of the bump-cutoff orthonormal frame.** The
section `smoothOrthoFrame g α i` (the Gram–Schmidt frame multiplied by the
chart bump function at `α`) is `C^∞` on all of `M`: on the base set it is a
product of smooth data, and off the (closed) support of the bump it vanishes
identically. Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem contMDiff_smoothOrthoFrame_section (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b => TotalSpace.mk' E b (smoothOrthoFrame (I := I) g α i b)) := by
  classical
  have hψ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      ((chartBumpAt (I := I) (M := M) α : M → ℝ))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    (chartBumpAt (I := I) (M := M) α).contMDiff.contMDiffOn
  have hts : tsupport ((chartBumpAt (I := I) (M := M) α : M → ℝ)) ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact (chartBumpAt (I := I) (M := M) α).tsupport_subset_chartAt_source
  have hglob := ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (∞ : ℕ∞ω))
    (ψ := (chartBumpAt (I := I) (M := M) α : M → ℝ))
    (s := fun b => chartFrameNorm (I := I) g α i b)
    hψ (trivializationAt E (TangentSpace I) α).open_baseSet hts
    (contMDiffOn_chartFrameNorm_section g α i)
  refine hglob.congr fun b => ?_
  simp only [smoothOrthoFrame, Pi.smul_apply']

/-- **Math.** The `i`-th vector of the local orthonormal frame at `α`, bundled
as a smooth vector field on `M`. It vanishes off the chart source at `α` and
is `g`-orthonormal at every point of `orthoFrameSet α`
(`orthoFrameField_orthonormal`).
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
def orthoFrameField (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) : SmoothVectorField I M where
  toFun := fun b => smoothOrthoFrame (I := I) g α i b
  smooth := contMDiff_smoothOrthoFrame_section g α i

@[simp] theorem orthoFrameField_apply (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    orthoFrameField g α i b = smoothOrthoFrame (I := I) g α i b := rfl

/-! ### The open orthonormality neighbourhood -/

/-- **Math.** An **open** neighbourhood of `α` on which the frame
`orthoFrameField g α` is `g`-orthonormal at every point: the interior of the
bump-equals-one set `smoothOrthoFrameNbhd α`. (The bump-equals-one set itself
is generally not open; its interior still contains `α` because the bump is
`1` near its centre.)
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
def orthoFrameSet (α : M) : Set M :=
  interior (smoothOrthoFrameNbhd (I := I) (M := M) α)

theorem isOpen_orthoFrameSet (α : M) :
    IsOpen (orthoFrameSet (I := I) (M := M) α) := isOpen_interior

theorem orthoFrameSet_mem_nhds (α : M) :
    orthoFrameSet (I := I) (M := M) α ∈ 𝓝 α :=
  interior_mem_nhds.mpr (smoothOrthoFrameNbhd_mem_nhds (I := I) α)

theorem mem_orthoFrameSet_self (α : M) :
    α ∈ orthoFrameSet (I := I) (M := M) α :=
  mem_of_mem_nhds (orthoFrameSet_mem_nhds (I := I) α)

theorem orthoFrameSet_subset_nbhd (α : M) :
    orthoFrameSet (I := I) (M := M) α ⊆
      smoothOrthoFrameNbhd (I := I) (M := M) α := interior_subset

/-- **Math.** On `orthoFrameSet α` the bundled frame is `g`-orthonormal:
`⟨Eᵢ(q), Eⱼ(q)⟩_g = δᵢⱼ`.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem orthoFrameField_orthonormal (g : RiemannianMetric I M) (α : M)
    {q : M} (hq : q ∈ orthoFrameSet (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.metricInner q (orthoFrameField g α i q) (orthoFrameField g α j q)
      = if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal (I := I) g α (orthoFrameSet_subset_nbhd α hq) i j

/-- **Math.** At each point of `orthoFrameSet α` the frame values form an
`Orthonormal` family in `(T_qM, g_q)` (with the fibre inner product installed
via `Bundle.RiemannianBundle ⟨g.toRiemannianMetric⟩`, definitionally
`g.metricInner q`).
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem orthoFrameField_orthonormal_family (g : RiemannianMetric I M) (α : M)
    {q : M} (hq : q ∈ orthoFrameSet (I := I) (M := M) α) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Orthonormal ℝ (fun i : Fin (Module.finrank ℝ E) => orthoFrameField g α i q) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [orthonormal_iff_ite]
  intro i j
  exact orthoFrameField_orthonormal g α hq i j

/-- **Math.** The frame values at a point of `orthoFrameSet α`, packaged as an
`OrthonormalBasis` of the tangent space. This is what feeds the algebraic
trace layer (`Riemannian.ricciForm_eq_sum`, `Riemannian.scalarCurvature_eq_sum`).
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
def orthoFrameBasis (g : RiemannianMetric I M) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I q) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hOrth := orthoFrameField_orthonormal_family g α hq
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I q) := Fintype.card_fin _
  refine (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis ?_
  rw [coe_basisOfOrthonormalOfCardEqFinrank]
  exact hOrth

@[simp] theorem orthoFrameBasis_apply (g : RiemannianMetric I M) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (i : Fin (Module.finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    orthoFrameBasis g α hq i = orthoFrameField g α i q := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold orthoFrameBasis
  rw [Module.Basis.coe_toOrthonormalBasis]
  exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank
    (orthoFrameField_orthonormal_family g α hq) _) i

/-- **Math.** **Orthonormal expansion in the frame**: at `q ∈ orthoFrameSet α`,
every tangent vector expands as `v = ∑ i ⟨v, Eᵢ(q)⟩_g • Eᵢ(q)`.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem orthoFrameField_expansion (g : RiemannianMetric I M) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (v : TangentSpace I q) :
    v = ∑ i, g.metricInner q v (orthoFrameField g α i q) • orthoFrameField g α i q := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := (orthoFrameBasis g α hq).sum_repr' v
  simp only [orthoFrameBasis_apply g α hq] at h
  refine h.symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  show inner ℝ (orthoFrameField g α i q) v = g.metricInner q v (orthoFrameField g α i q)
  exact g.symm q _ _

end PoincareLib
