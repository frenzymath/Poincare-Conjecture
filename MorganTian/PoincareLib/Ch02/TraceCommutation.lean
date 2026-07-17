import PoincareLib.Ch01.SecondCov
import PoincareLib.Ch02.OrthoFrame
import PoincareLib.Ch02.GradientNormSq

/-!
# Morgan–Tian Ch. 2 — the trace-commutation identity for the Bochner formula

The **trace-commutation pillar** of the Bochner formula for functions
(blueprint `lem:function-bochner-formula`): for the Levi-Civita connection
and the gradient field `G = (∇f)^*` of a smooth `f`,

`Σᵢ ⟨∇²G(G, Eᵢ), Eᵢ⟩(p) = G(Δf)(p) = ⟨(∇Δf)^*, G⟩(p)`,

i.e. the metric trace of the second covariant derivative of the gradient,
with the *outer* derivative along `G`, is the derivative of the trace
`Δf = tr_g Hess f` along `G` ("derivative of trace = trace of derivative",
valid because the metric is parallel).

The proof differentiates the orthonormal-frame formula for the Laplacian.
Let `F₁, …, F_n` be a smooth local orthonormal frame at `p`
(`PoincareLib.exists_orthonormalFrame`). Then near `p`

`Δf = Σᵢ ⟨∇_{Fᵢ} G, Fᵢ⟩` (`laplacianAt_eventuallyEq_sum_frame`),

so, differentiating along `G` at `p` and using metric compatibility,

`G(Δf) = Σᵢ ⟨∇_G ∇_{Fᵢ} G, Fᵢ⟩ + Σᵢ ⟨∇_{Fᵢ} G, ∇_G Fᵢ⟩`.

Meanwhile `∇²G(G, Fᵢ) = ∇_G ∇_{Fᵢ} G − ∇_{∇_G Fᵢ} G` by definition, so the
difference of the two sides is
`Σᵢ [⟨∇_{Fᵢ} G, ∇_G Fᵢ⟩ + ⟨∇_{∇_G Fᵢ} G, Fᵢ⟩]`; by the gradient formula for
the Hessian both summands are Hessian values,
`Hess(f)_p(Fᵢ, ∇_G Fᵢ) + Hess(f)_p(∇_G Fᵢ, Fᵢ)`, and expanding `∇_G Fᵢ(p)`
over the orthonormal basis `{Fⱼ(p)}` with coefficients
`aᵢⱼ = ⟨∇_G Fᵢ, Fⱼ⟩(p)` — **antisymmetric** in `(i,j)` since the frame inner
products `⟨Fᵢ, Fⱼ⟩ = δᵢⱼ` are constant near `p` — the difference becomes a
full contraction of an antisymmetric matrix against the symmetric Hessian,
which vanishes. No derivatives of the metric coefficients or Christoffel
symbols are needed.

Main results:

* `contMDiff_laplacianAt` — the Laplacian of a smooth function is smooth
  (near every point `Δf` agrees with the manifestly smooth frame sum);
* `sum_metricInner_secondCov_frame_eq_dir_laplacianAt` — the identity in
  local-orthonormal-frame form;
* `sum_metricInner_secondCov_gradientField_eq_dir_laplacianAt` — the identity
  in the `stdOrthonormalBasis`/`extendVector` form consumed by the Bochner
  assembly (matching `sum_metricInner_cov_cov_gradientField_eq_hessianNormSqAt`
  and `sum_metricInner_riemannCurvature_self_eq_ricciAt`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:function-bochner-formula`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian Filter

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Scalar calculus helpers -/

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [IsManifold I ∞ M] in
/-- **Math.** A finite sum of smooth functions is smooth.
Blueprint: `lem:function-bochner-formula` (trace-commutation step). -/
theorem contMDiff_fun_sum {ι : Type*} {s : Finset ι} {h : ι → M → ℝ}
    (hs : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (h i)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => ∑ i ∈ s, h i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contMDiff_const (c := (0 : ℝ))
  | insert a t ha IH =>
      have hfun : (fun q => ∑ i ∈ insert a t, h i q)
          = fun q => h a q + ∑ i ∈ t, h i q := by
        funext q
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact (hs a (Finset.mem_insert_self a t)).add
        (IH fun i hi => hs i (Finset.mem_insert_of_mem hi))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] in
/-- **Math.** The directional derivative of a finite sum of smooth functions
is the sum of the directional derivatives.
Blueprint: `lem:function-bochner-formula` (trace-commutation step). -/
theorem dir_sum (X : SmoothVectorField I M) {ι : Type*} {s : Finset ι}
    {h : ι → M → ℝ} (hs : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (h i)) (p : M) :
    X.dir (fun q => ∑ i ∈ s, h i q) p = ∑ i ∈ s, X.dir (h i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      show mfderiv I 𝓘(ℝ, ℝ) (fun _ => (0 : ℝ)) p (X p) = 0
      rw [mfderiv_const]
      rfl
  | insert a t ha IH =>
      have hfun : (fun q => ∑ i ∈ insert a t, h i q)
          = fun q => h a q + ∑ i ∈ t, h i q := by
        funext q
        rw [Finset.sum_insert ha]
      have hta : ContMDiff I 𝓘(ℝ, ℝ) ∞ (h a) :=
        hs a (Finset.mem_insert_self a t)
      have htsum : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => ∑ i ∈ t, h i q) :=
        contMDiff_fun_sum fun i hi => hs i (Finset.mem_insert_of_mem hi)
      rw [hfun, X.dir_add p (hta.mdifferentiableAt (by simp))
          (htsum.mdifferentiableAt (by simp)),
        IH fun i hi => hs i (Finset.mem_insert_of_mem hi),
        Finset.sum_insert ha]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] in
/-- **Math.** The metric pairing of two smooth vector fields is a smooth
scalar function (two-field form of `contMDiff_metricNormSq`).
Blueprint: `lem:function-bochner-formula` (trace-commutation step). -/
theorem contMDiff_metricInner_fields (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => g.metricInner q (X q) (Y q)) := by
  intro x
  have h := g.metricInner_contMDiffWithinAt (v := fun y => X y)
    (w := fun y => Y y) (s := Set.univ) (x := x)
    ((X.smooth x).contMDiffWithinAt) ((Y.smooth x).contMDiffWithinAt)
  rw [contMDiffWithinAt_univ] at h
  exact h

/-! ### Middle-slot pointwise locality of the paired second covariant
derivative -/

variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** **Pointwise locality of `⟨∇²Z(X, ·), w⟩` in the middle slot**:
the scalar `⟨∇²Z(X, Y)(p), w⟩` depends on `Y` only through `Y(p)`. The map
`Y ↦ ⟨∇²Z(X, Y), W⟩` is `𝒟(M)`-linear in `Y` (`secondCov_add_middle`,
`secondCov_smul_middle`), so the scalar locality engine
`tensorial_congr_apply` applies. Blueprint: `lem:function-bochner-formula`
(trace-commutation step). -/
theorem metricInner_secondCov_middle_congr (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (X Z : SmoothVectorField I M)
    {Y Y' : SmoothVectorField I M} {p : M} (w : TangentSpace I p)
    (h : Y p = Y' p) :
    g.metricInner p ((secondCov nabla X Y Z) p) w
      = g.metricInner p ((secondCov nabla X Y' Z) p) w := by
  have hloc := tensorial_congr_apply
    (fun A q => g.metricInner q ((secondCov nabla X A Z) q) ((extendVector p w) q))
    (fun A B q => by
      dsimp only
      rw [secondCov_add_middle, SmoothVectorField.add_apply,
        g.metricInner_add_left])
    (fun φ hφ A q => by
      dsimp only
      rw [secondCov_smul_middle, SmoothVectorField.smul_apply,
        g.metricInner_smul_left])
    h
  dsimp only at hloc
  rwa [extendVector_apply] at hloc

/-! ### The Laplacian as a frame sum near a point -/

variable [I.Boundaryless]

omit [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** **The Laplacian is the orthonormal-frame trace of the Hessian
near `p`**: if `F₁, …, F_n` are smooth vector fields that are `g`-orthonormal
on a neighbourhood of `p`, then near `p`
`Δf = Σᵢ ⟨∇_{Fᵢ} (∇f)^*, Fᵢ⟩`.
At each nearby point `q` the values `{Fᵢ(q)}` form an orthonormal basis of
`(T_qM, g_q)`, so the basis-independence of the metric trace
(`laplacianAt_eq_sum`) applies, and the Hessian entries read as covariant
derivatives of the gradient by the gradient formula for the Hessian.
Blueprint: `lem:function-bochner-formula` (trace-commutation step). -/
theorem laplacianAt_eventuallyEq_sum_frame (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hON : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0) :
    laplacianAt g nabla f =ᶠ[𝓝 p]
      fun q => ∑ i, g.metricInner q
        ((nabla.cov (F i) (gradientField g f hf)) q) (F i q) := by
  have hall : ∀ᶠ q in 𝓝 p, ∀ i j, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0 :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hON i j
  filter_upwards [hall] with q hq
  rw [laplacianAt_eq_sum g nabla hf q
    (orthonormalBasisOfMetricInner g (v := fun i => F i q) fun i j => hq i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orthonormalBasisOfMetricInner_apply, hessianAt_eq nabla hf (F i) (F i) q]
  exact hessian_eq_metricInner_cov_gradientField g nabla hLC.2 hf (F i) (F i) q

omit [I.Boundaryless] in
/-- **Math.** **The Laplacian of a smooth function is smooth**: near every
point, `Δf` agrees with the frame sum `Σᵢ ⟨∇_{Fᵢ} (∇f)^*, Fᵢ⟩` of a smooth
local orthonormal frame (`laplacianAt_eventuallyEq_sum_frame`), which is a
finite sum of metric pairings of smooth vector fields.
Blueprint: `lem:function-bochner-formula` (trace-commutation step). -/
theorem contMDiff_laplacianAt (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacianAt g nabla f) := by
  intro p
  obtain ⟨F, hON⟩ := exists_orthonormalFrame g p
  have hev := laplacianAt_eventuallyEq_sum_frame g hLC hf hON
  have hsum : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun q => ∑ i, g.metricInner q
        ((nabla.cov (F i) (gradientField g f hf)) q) (F i q)) :=
    contMDiff_fun_sum fun i _ =>
      contMDiff_metricInner_fields g (nabla.cov (F i) (gradientField g f hf)) (F i)
  exact (hsum p).congr_of_eventuallyEq hev

/-! ### The trace-commutation identity -/

/-- **Math.** **Trace commutation in a local orthonormal frame**: for the
Levi-Civita connection, `G = (∇f)^*`, and a smooth local orthonormal frame
`F₁, …, F_n` at `p`,
`Σᵢ ⟨∇²G(G, Fᵢ), Fᵢ⟩(p) = G(Δf)(p)`.
Differentiating the frame formula `Δf = Σᵢ ⟨∇_{Fᵢ}G, Fᵢ⟩` along `G` and using
metric compatibility produces the sum `Σᵢ ⟨∇_G ∇_{Fᵢ}G, Fᵢ⟩` plus correction
terms; the corrections `Σᵢ [⟨∇_{Fᵢ}G, ∇_G Fᵢ⟩ + ⟨∇_{∇_G Fᵢ}G, Fᵢ⟩]` are a
full contraction of the coefficient matrix `aᵢⱼ = ⟨∇_G Fᵢ, Fⱼ⟩(p)` —
antisymmetric, because the frame inner products are constant near `p` —
against the symmetric Hessian, hence vanish.
Blueprint: `lem:function-bochner-formula` (trace-commutation step). -/
theorem sum_metricInner_secondCov_frame_eq_dir_laplacianAt
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hON : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0) :
    ∑ i, g.metricInner p
        ((secondCov nabla (gradientField g f hf) (F i) (gradientField g f hf)) p)
        (F i p)
      = (gradientField g f hf).dir (laplacianAt g nabla f) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hONp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0 :=
    fun i j => (hON i j).self_of_nhds
  set G := gradientField g f hf with hGdef
  -- (1) differentiate the frame formula for `Δf` along `G`
  have hev : laplacianAt g nabla f =ᶠ[𝓝 p]
      fun q => ∑ i, g.metricInner q ((nabla.cov (F i) G) q) (F i q) :=
    laplacianAt_eventuallyEq_sum_frame g hLC hf hON
  have hdirΔ : G.dir (laplacianAt g nabla f) p
      = ∑ i, G.dir
          (fun q => g.metricInner q ((nabla.cov (F i) G) q) (F i q)) p := by
    have h1 : G.dir (laplacianAt g nabla f) p
        = G.dir (fun q => ∑ i, g.metricInner q
            ((nabla.cov (F i) G) q) (F i q)) p := by
      show mfderiv I 𝓘(ℝ, ℝ) (laplacianAt g nabla f) p (G p)
        = mfderiv I 𝓘(ℝ, ℝ)
            (fun q => ∑ i, g.metricInner q ((nabla.cov (F i) G) q) (F i q))
            p (G p)
      rw [hev.mfderiv_eq]
      rfl
    rw [h1]
    exact dir_sum G
      (fun i _ => contMDiff_metricInner_fields g (nabla.cov (F i) G) (F i)) p
  -- (2) metric compatibility on each summand
  have hcompat : ∀ i, G.dir
        (fun q => g.metricInner q ((nabla.cov (F i) G) q) (F i q)) p
      = g.metricInner p ((nabla.cov G (nabla.cov (F i) G)) p) (F i p)
        + g.metricInner p ((nabla.cov (F i) G) p) ((nabla.cov G (F i)) p) :=
    fun i => hLC.2 G (nabla.cov (F i) G) (F i) p
  -- (3) expand the second covariant derivative
  have hsecond : ∀ i, g.metricInner p ((secondCov nabla G (F i) G) p) (F i p)
      = g.metricInner p ((nabla.cov G (nabla.cov (F i) G)) p) (F i p)
        - g.metricInner p ((nabla.cov (nabla.cov G (F i)) G) p) (F i p) := by
    intro i
    rw [secondCov_apply, g.metricInner_sub_left]
  -- (4) the two correction sums are Hessian contractions
  have hriesz1 : ∀ i,
      g.metricInner p ((nabla.cov (nabla.cov G (F i)) G) p) (F i p)
        = hessianAt nabla f p ((nabla.cov G (F i)) p) (F i p) := fun i =>
    metricInner_cov_gradientField_eq_hessianAt g hLC.2 hf
      (nabla.cov G (F i)) p (F i p)
  have hriesz2 : ∀ i,
      g.metricInner p ((nabla.cov (F i) G) p) ((nabla.cov G (F i)) p)
        = hessianAt nabla f p (F i p) ((nabla.cov G (F i)) p) := fun i =>
    metricInner_cov_gradientField_eq_hessianAt g hLC.2 hf
      (F i) p ((nabla.cov G (F i)) p)
  -- (5) antisymmetry of the connection coefficients of the frame
  have hanti : ∀ i j,
      g.metricInner p ((nabla.cov G (F i)) p) (F j p)
        + g.metricInner p ((nabla.cov G (F j)) p) (F i p) = 0 := by
    intro i j
    have hdir0 : G.dir (fun q => g.metricInner q (F i q) (F j q)) p = 0 := by
      have hconst : (fun q => g.metricInner q (F i q) (F j q))
          =ᶠ[𝓝 p] fun _ => if i = j then (1 : ℝ) else 0 := hON i j
      show mfderiv I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (F i q) (F j q)) p (G p)
        = 0
      rw [hconst.mfderiv_eq, mfderiv_const]
      rfl
    have hc := hLC.2 G (F i) (F j) p
    rw [hdir0] at hc
    have hcm := g.metricInner_comm p ((nabla.cov G (F j)) p) (F i p)
    linarith
  -- (6) expand `∇_G Fᵢ(p)` over the orthonormal basis `{Fⱼ(p)}`
  set e := orthonormalBasisOfMetricInner g hONp with hedef
  have happ : ∀ i, e i = F i p := fun i =>
    orthonormalBasisOfMetricInner_apply g hONp i
  have hexpand : ∀ i, hessianAt nabla f p (F i p) ((nabla.cov G (F i)) p)
      = ∑ j, g.metricInner p ((nabla.cov G (F i)) p) (F j p)
          * hessianAt nabla f p (F i p) (F j p) := by
    intro i
    set W := (nabla.cov G (F i)) p with hWdef
    have hrepr : W = ∑ j, inner ℝ (e j) W • e j := (e.sum_repr' W).symm
    let L : TangentSpace I p →ₗ[ℝ] ℝ :=
      { toFun := fun w => hessianAt nabla f p (F i p) w
        map_add' := fun w₁ w₂ => hessianAt_add_right nabla hf p (F i p) w₁ w₂
        map_smul' := fun c w => hessianAt_smul_right nabla hf p c (F i p) w }
    have hcoef : ∀ j, inner ℝ (e j) W = g.metricInner p W (F j p) := by
      intro j
      rw [inner_tangentSpace_eq_metricInner g p, g.metricInner_comm, happ j]
    calc hessianAt nabla f p (F i p) W
        = L (∑ j, inner ℝ (e j) W • e j) := by rw [← hrepr]; rfl
      _ = ∑ j, inner ℝ (e j) W * L (e j) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
      _ = ∑ j, g.metricInner p W (F j p)
            * hessianAt nabla f p (F i p) (F j p) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hcoef j, happ j]
          rfl
  -- (7) the antisymmetric–symmetric contraction vanishes
  have hS : ∑ i, hessianAt nabla f p (F i p) ((nabla.cov G (F i)) p) = 0 := by
    set S := ∑ i, hessianAt nabla f p (F i p) ((nabla.cov G (F i)) p) with hSdef
    have hSsum : S = ∑ i, ∑ j,
        g.metricInner p ((nabla.cov G (F i)) p) (F j p)
          * hessianAt nabla f p (F i p) (F j p) := by
      rw [hSdef]
      exact Finset.sum_congr rfl fun i _ => hexpand i
    have hneg : S = -S := by
      calc S = ∑ i, ∑ j,
            g.metricInner p ((nabla.cov G (F i)) p) (F j p)
              * hessianAt nabla f p (F i p) (F j p) := hSsum
        _ = ∑ j, ∑ i,
            g.metricInner p ((nabla.cov G (F i)) p) (F j p)
              * hessianAt nabla f p (F i p) (F j p) := Finset.sum_comm
        _ = ∑ i, ∑ j,
            -(g.metricInner p ((nabla.cov G (F i)) p) (F j p))
              * hessianAt nabla f p (F i p) (F j p) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            have h1 : g.metricInner p ((nabla.cov G (F j)) p) (F i p)
                = -(g.metricInner p ((nabla.cov G (F i)) p) (F j p)) := by
              have := hanti i j
              linarith
            rw [h1, hessianAt_symm nabla hLC.1 hf p (F j p) (F i p)]
        _ = -S := by
            rw [hSsum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  -- (8) assemble
  have hgoal : ∑ i, g.metricInner p ((secondCov nabla G (F i) G) p) (F i p)
      = ∑ i, (g.metricInner p ((nabla.cov G (nabla.cov (F i) G)) p) (F i p)
          - hessianAt nabla f p ((nabla.cov G (F i)) p) (F i p)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsecond i, hriesz1 i]
  have hrhs : G.dir (laplacianAt g nabla f) p
      = ∑ i, (g.metricInner p ((nabla.cov G (nabla.cov (F i) G)) p) (F i p)
          + hessianAt nabla f p (F i p) ((nabla.cov G (F i)) p)) := by
    rw [hdirΔ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcompat i, hriesz2 i]
  rw [hgoal, hrhs, Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, add_zero]
  have hsymm_sum : ∑ i, hessianAt nabla f p ((nabla.cov G (F i)) p) (F i p)
      = ∑ i, hessianAt nabla f p (F i p) ((nabla.cov G (F i)) p) :=
    Finset.sum_congr rfl fun i _ =>
      hessianAt_symm nabla hLC.1 hf p ((nabla.cov G (F i)) p) (F i p)
  rw [hsymm_sum, hS, sub_zero]

/-- **Math.** **The trace-commutation identity** (the last pillar of the
Bochner formula): for the Levi-Civita connection, `G = (∇f)^*`, and the chosen
orthonormal basis `{eᵢ}` of `(T_pM, g_p)` with global extensions
`Eᵢ = extendVector p eᵢ`,
`Σᵢ ⟨∇²G(G, Eᵢ), Eᵢ⟩(p) = G(Δf)(p)`
— the metric trace of `∇²G` with outer derivative along `G` is the derivative
of the trace `Δf = tr_g Hess f` along `G`. Proved by transporting
`sum_metricInner_secondCov_frame_eq_dir_laplacianAt` from a smooth local
orthonormal frame to the chosen basis: the summand is, by middle-slot
locality of `∇²`, the diagonal value of a bilinear form on `T_pM`, and
diagonal sums of bilinear forms agree over all orthonormal bases.
Blueprint: `lem:function-bochner-formula` (trace-commutation step). -/
theorem sum_metricInner_secondCov_gradientField_eq_dir_laplacianAt
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, g.metricInner p
        ((secondCov nabla (gradientField g f hf)
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (gradientField g f hf)) p)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      = (gradientField g f hf).dir (laplacianAt g nabla f) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨F, hON⟩ := exists_orthonormalFrame g p
  have hONp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0 :=
    fun i j => (hON i j).self_of_nhds
  set G := gradientField g f hf with hGdef
  -- the summand as a bilinear form on `T_pM`
  let B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v w => g.metricInner p ((secondCov nabla G (extendVector p v) G) p) w)
      (fun v₁ v₂ w => by
        dsimp only
        have h := metricInner_secondCov_middle_congr g nabla G G
          (Y := extendVector p (v₁ + v₂))
          (Y' := extendVector p v₁ + extendVector p v₂) w
          (by rw [extendVector_apply, SmoothVectorField.add_apply,
            extendVector_apply, extendVector_apply])
        rw [h, secondCov_add_middle, SmoothVectorField.add_apply,
          g.metricInner_add_left])
      (fun c v w => by
        dsimp only
        have h := metricInner_secondCov_middle_congr g nabla G G
          (Y := extendVector p (c • v))
          (Y' := SmoothVectorField.smul (fun _ => c) contMDiff_const
            (extendVector p v)) w
          (by rw [extendVector_apply, SmoothVectorField.smul_apply,
            extendVector_apply])
        rw [h, secondCov_smul_middle, SmoothVectorField.smul_apply,
          g.metricInner_smul_left]
        rfl)
      (fun v w₁ w₂ => g.metricInner_add_right p _ w₁ w₂)
      (fun c v w => g.metricInner_smul_right p c _ w)
  have hB : ∀ v w, B v w
      = g.metricInner p ((secondCov nabla G (extendVector p v) G) p) w :=
    fun _ _ => rfl
  set e := orthonormalBasisOfMetricInner g hONp with hedef
  have happ : ∀ i, e i = F i p := fun i =>
    orthonormalBasisOfMetricInner_apply g hONp i
  have hinv := OrthonormalBasis.sum_apply_diagonal_invariant
    (stdOrthonormalBasis ℝ (TangentSpace I p)) e B
  calc ∑ i, g.metricInner p
        ((secondCov nabla G
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) G) p)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      = ∑ i, B (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
        simp only [hB]
    _ = ∑ i, B (e i) (e i) := hinv
    _ = ∑ i, g.metricInner p ((secondCov nabla G (F i) G) p) (F i p) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hB, happ i]
        exact metricInner_secondCov_middle_congr g nabla G G
          (Y := extendVector p (F i p)) (Y' := F i) (F i p)
          (extendVector_apply p (F i p))
    _ = G.dir (laplacianAt g nabla f) p :=
        sum_metricInner_secondCov_frame_eq_dir_laplacianAt g hLC hf hON

end PoincareLib

end
