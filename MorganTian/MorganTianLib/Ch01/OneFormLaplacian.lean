import MorganTianLib.Ch01.SecondCov
import MorganTianLib.Ch01.PointwiseCurvature
import MorganTianLib.Ch02.TraceCommutation

/-!
# Morgan–Tian Ch. 1 — the Laplacian of the differential of a function

Morgan–Tian's **Laplacian-of-a-one-form lemma** (blueprint
`lem:laplacian-one-form`, eq. `lapformula`): for a smooth function `f` on a
Riemannian manifold,

`Δ(df) = d(Δf) + Ric((∇f)^*, ·)`.

Throughout, one-forms are handled through their metric-dual vector fields
(the reading Morgan–Tian themselves use via `(∇f)^*`): since `∇g = 0`, the
musical isomorphism commutes with covariant differentiation, so with
`G = (∇f)^*` and `H = Hess f` the two-tensor `∇_W H` is
`(∇_W H)(A, B) = ⟨∇²G(W, A), B⟩` (the display opening the blueprint proof),
and

* `Δ(df)(z) = Σᵢ (∇_{Eᵢ} H)(Eᵢ, z) = Σᵢ ⟨∇²G(Eᵢ, Eᵢ), z⟩` — the trace of
  `∇(df)` over an orthonormal basis (`oneFormLaplacianAt`, defined for the
  dual field of an arbitrary one-form, i.e. for any smooth vector field);
* `d(Δf)(z) = z(Δf)` — the differential of the trace (`dirTangent`).

The proof is the blueprint proof read through this duality:

1. `⟨∇²G(W, A), B⟩ = (∇_W H)(A, B)` is **symmetric in `(A, B)`** because `H`
   is symmetric near `p` (`lem:hessian-symmetric` differentiated;
   `metricInner_secondCov_gradientField_symm`), so the trace over the
   `(middle, pairing)` slots equals the trace over the `(middle, middle)`
   slots;
2. the **Ricci commutation identity** `∇²G(X,Y) − ∇²G(Y,X) = ℛ_MT(X,Y)G`
   (`secondCov_sub_swap`, the vector-field mirror of the blueprint's
   one-form commutation formula `oneformcomm` — the two agree by the
   second-pair antisymmetry of the curvature tensor) swaps the outer slot
   with the middle slot at the cost of a curvature term;
3. the resulting `Σᵢ ⟨∇²G(z, Eᵢ), Eᵢ⟩` is `z(Δf)` — **differentiating the
   trace commutes with the contraction** because `∇g = 0`
   (`sum_metricInner_secondCov_along_frame_eq_dir_laplacianAt`, the
   arbitrary-direction form of the Ch. 2 trace-commutation identity);
4. the curvature term contracts to the Ricci term: by the pair-swap symmetry
   and the two pair antisymmetries of the curvature tensor
   (`claim:curvature-symmetries-bianchi`),
   `Σᵢ ⟨ℛ_MT(Eᵢ, z)G, Eᵢ⟩ = Ric(G, z)`
   (`sum_metricInner_riemannCurvature_frame_eq_ricciAt`; this is the
   blueprint's contraction `−g^{jk} df(ℛ(∂_k, ∂_i)∂_j) = Ric((∇f)^*, ∂_i)`,
   with the `g^{jk} ℛ(∂_j,∂_k)`-antisymmetry cancellation performed by the
   symmetry step 1 instead).

Main statements:

* `oneFormLaplacianAt` — the Laplacian `Δ(X^♭)(z)` of the one-form dual to a
  smooth vector field `X`, as a basis-independent metric trace;
* `oneFormLaplacianAt_eq_sum_frame` — evaluation over any pointwise
  orthonormal family of smooth fields;
* `oneFormLaplacianAt_gradientField_eq_dirTangent_laplacianAt_add_ricciAt` —
  the blueprint formula `Δ(df)(z) = d(Δf)(z) + Ric((∇f)^*, z)`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1
(blueprint `lem:laplacian-one-form`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian Filter

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-! ### The Laplacian of a one-form, through its dual vector field -/

/-- **Math.** The **Laplacian of the one-form `X^♭` dual to a smooth vector
field `X`**, evaluated at `z ∈ T_pM`:
`Δ(X^♭)(z) = Σᵢ ⟨∇²X(eᵢ, eᵢ), z⟩`,
the metric trace over the two direction slots of the second covariant
derivative, computed from the chosen orthonormal basis `{eᵢ}` of `(T_pM, g_p)`
with global extensions `Eᵢ = extendVector p eᵢ`. Since `∇g = 0`, this is
Morgan–Tian's `Δω(Z) = g^{jk}(∇_{∂_j}(∇ω))(∂_k, Z)` for `ω = X^♭`; by
`oneFormLaplacianAt_eq_sum_frame` the value does not depend on the choice of
basis or extensions. Blueprint: `lem:laplacian-one-form`. -/
noncomputable def oneFormLaplacianAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (X : SmoothVectorField I M) (p : M)
    (z : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, g.metricInner p
    ((secondCov nabla
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) X) p)
    z

omit [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** **Evaluation of the one-form Laplacian over any pointwise
orthonormal family of smooth fields**: if `F₁, …, F_n` are smooth vector
fields whose values at `p` are `g_p`-orthonormal, then
`Δ(X^♭)(z) = Σᵢ ⟨∇²X(Fᵢ, Fᵢ)(p), z⟩`.
The summand is the diagonal value of a bilinear form on `T_pM` (by the
tensoriality of `∇²X` in both direction slots), and diagonal sums of bilinear
forms agree over all orthonormal bases. In particular `oneFormLaplacianAt` is
independent of the basis and extensions chosen in its definition.
Blueprint: `lem:laplacian-one-form`. -/
theorem oneFormLaplacianAt_eq_sum_frame (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (X : SmoothVectorField I M) {p : M}
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hONp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0)
    (z : TangentSpace I p) :
    oneFormLaplacianAt g nabla X p z
      = ∑ i, g.metricInner p ((secondCov nabla (F i) (F i) X) p) z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v w => g.metricInner p
        ((secondCov nabla (extendVector p v) (extendVector p w) X) p) z)
      (fun v₁ v₂ w => by
        dsimp only
        have h : (secondCov nabla (extendVector p (v₁ + v₂))
              (extendVector p w) X) p
            = (secondCov nabla (extendVector p v₁ + extendVector p v₂)
                (extendVector p w) X) p :=
          secondCov_congr_left nabla _ _ (by
            rw [extendVector_apply, SmoothVectorField.add_apply,
              extendVector_apply, extendVector_apply])
        rw [h, secondCov_add_left, SmoothVectorField.add_apply,
          g.metricInner_add_left])
      (fun c v w => by
        dsimp only
        have h : (secondCov nabla (extendVector p (c • v))
              (extendVector p w) X) p
            = (secondCov nabla (SmoothVectorField.smul (fun _ => c)
                contMDiff_const (extendVector p v)) (extendVector p w) X) p :=
          secondCov_congr_left nabla _ _ (by
            rw [extendVector_apply, SmoothVectorField.smul_apply,
              extendVector_apply])
        rw [h, secondCov_smul_left, SmoothVectorField.smul_apply,
          g.metricInner_smul_left]
        rfl)
      (fun v w₁ w₂ => by
        dsimp only
        have h := metricInner_secondCov_middle_congr g nabla
          (extendVector p v) X
          (Y := extendVector p (w₁ + w₂))
          (Y' := extendVector p w₁ + extendVector p w₂) z
          (by rw [extendVector_apply, SmoothVectorField.add_apply,
            extendVector_apply, extendVector_apply])
        rw [h, secondCov_add_middle, SmoothVectorField.add_apply,
          g.metricInner_add_left])
      (fun c v w => by
        dsimp only
        have h := metricInner_secondCov_middle_congr g nabla
          (extendVector p v) X
          (Y := extendVector p (c • w))
          (Y' := SmoothVectorField.smul (fun _ => c) contMDiff_const
            (extendVector p w)) z
          (by rw [extendVector_apply, SmoothVectorField.smul_apply,
            extendVector_apply])
        rw [h, secondCov_smul_middle, SmoothVectorField.smul_apply,
          g.metricInner_smul_left]
        rfl)
  have hB : ∀ v w, B v w
      = g.metricInner p
          ((secondCov nabla (extendVector p v) (extendVector p w) X) p) z :=
    fun _ _ => rfl
  set e := orthonormalBasisOfMetricInner g hONp with hedef
  have happ : ∀ i, e i = F i p := fun i =>
    orthonormalBasisOfMetricInner_apply g hONp i
  have hinv := OrthonormalBasis.sum_apply_diagonal_invariant
    (stdOrthonormalBasis ℝ (TangentSpace I p)) e B
  calc oneFormLaplacianAt g nabla X p z
      = ∑ i, B (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
        simp only [oneFormLaplacianAt, hB]
    _ = ∑ i, B (e i) (e i) := hinv
    _ = ∑ i, g.metricInner p ((secondCov nabla (F i) (F i) X) p) z := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hB, happ i]
        have h1 : (secondCov nabla (extendVector p (F i p))
              (extendVector p (F i p)) X) p
            = (secondCov nabla (F i) (extendVector p (F i p)) X) p :=
          secondCov_congr_left nabla _ _ (extendVector_apply p (F i p))
        rw [h1]
        exact metricInner_secondCov_middle_congr g nabla (F i) X
          (Y := extendVector p (F i p)) (Y' := F i) z
          (extendVector_apply p (F i p))

/-! ### The differentiated symmetry of the Hessian -/

/-- **Math.** **The differentiated Hessian symmetry**: for the Levi-Civita
connection, `G = (∇f)^*`, and smooth vector fields `W, X, Y`,
`⟨∇²G(W, X), Y⟩(p) = ⟨∇²G(W, Y), X⟩(p)`,
i.e. the two-tensor `∇_W(Hess f)` is symmetric. Expanding with metric
compatibility,
`⟨∇²G(W, X), Y⟩ = W(Hess(f)(X, Y)) − Hess(f)(X, ∇_W Y) − Hess(f)(∇_W X, Y)`,
which is symmetric under `X ↔ Y` by the symmetry of the Hessian
(`lem:hessian-symmetric`). This is the blueprint's identification
`(∇²_{X,Y} df)(Z) = (∇_X H)(Y, Z)` combined with the symmetry of `H`.
Blueprint: `lem:laplacian-one-form`. -/
theorem metricInner_secondCov_gradientField_symm (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (W X Y : SmoothVectorField I M) (p : M) :
    g.metricInner p ((secondCov nabla W X (gradientField g f hf)) p) (Y p)
      = g.metricInner p ((secondCov nabla W Y (gradientField g f hf)) p)
          (X p) := by
  have key : ∀ A B : SmoothVectorField I M,
      g.metricInner p ((secondCov nabla W A (gradientField g f hf)) p) (B p)
        = W.dir (hessian nabla f A B) p
          - hessian nabla f A (nabla.cov W B) p
          - hessian nabla f (nabla.cov W A) B p := by
    intro A B
    have hc := hLC.2 W (nabla.cov A (gradientField g f hf)) B p
    have hfun : (fun q => g.metricInner q
          ((nabla.cov A (gradientField g f hf)) q) (B q))
        = hessian nabla f A B := by
      funext q
      exact (hessian_eq_metricInner_cov_gradientField g nabla hLC.2 hf
        A B q).symm
    rw [hfun] at hc
    have h2 : g.metricInner p ((nabla.cov A (gradientField g f hf)) p)
          ((nabla.cov W B) p)
        = hessian nabla f A (nabla.cov W B) p :=
      (hessian_eq_metricInner_cov_gradientField g nabla hLC.2 hf
        A (nabla.cov W B) p).symm
    have h3 : g.metricInner p
          ((nabla.cov (nabla.cov W A) (gradientField g f hf)) p) (B p)
        = hessian nabla f (nabla.cov W A) B p :=
      (hessian_eq_metricInner_cov_gradientField g nabla hLC.2 hf
        (nabla.cov W A) B p).symm
    rw [secondCov_apply, g.metricInner_sub_left, h3]
    linarith [hc, h2]
  rw [key X Y, key Y X]
  have hsymm_fun : hessian nabla f X Y = hessian nabla f Y X :=
    funext fun q => hessian_symm nabla hLC.1 hf X Y q
  rw [hsymm_fun]
  have h1 : hessian nabla f X (nabla.cov W Y) p
      = hessian nabla f (nabla.cov W Y) X p :=
    hessian_symm nabla hLC.1 hf X (nabla.cov W Y) p
  have h2 : hessian nabla f (nabla.cov W X) Y p
      = hessian nabla f Y (nabla.cov W X) p :=
    hessian_symm nabla hLC.1 hf (nabla.cov W X) Y p
  linarith

/-! ### Trace commutation along an arbitrary direction -/

/-- **Math.** **Trace commutation along an arbitrary direction, in a local
orthonormal frame**: for the Levi-Civita connection, `G = (∇f)^*`, a smooth
vector field `X`, and a smooth local orthonormal frame `F₁, …, F_n` at `p`,
`Σᵢ ⟨∇²G(X, Fᵢ), Fᵢ⟩(p) = X(Δf)(p)`
— differentiating the trace `Δf = tr_g Hess f` commutes with the contraction
because `∇g = 0`. This generalizes the direction slot of
`sum_metricInner_secondCov_frame_eq_dir_laplacianAt` from `G` itself to an
arbitrary field `X`; the proof is identical: differentiate the frame formula
`Δf = Σᵢ ⟨∇_{Fᵢ}G, Fᵢ⟩` along `X`, and the correction terms are a full
contraction of the antisymmetric coefficient matrix `⟨∇_X Fᵢ, Fⱼ⟩(p)` against
the symmetric Hessian, hence vanish. Blueprint: `lem:laplacian-one-form`
(the display `d(Δf)(Z) = g^{jk}(∇_Z H)(∂_j, ∂_k)`). -/
theorem sum_metricInner_secondCov_along_frame_eq_dir_laplacianAt
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X : SmoothVectorField I M) {p : M}
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hON : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0) :
    ∑ i, g.metricInner p
        ((secondCov nabla X (F i) (gradientField g f hf)) p)
        (F i p)
      = X.dir (laplacianAt g nabla f) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hONp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0 :=
    fun i j => (hON i j).self_of_nhds
  set G := gradientField g f hf with hGdef
  -- (1) differentiate the frame formula for `Δf` along `X`
  have hev : laplacianAt g nabla f =ᶠ[𝓝 p]
      fun q => ∑ i, g.metricInner q ((nabla.cov (F i) G) q) (F i q) :=
    laplacianAt_eventuallyEq_sum_frame g hLC hf hON
  have hdirΔ : X.dir (laplacianAt g nabla f) p
      = ∑ i, X.dir
          (fun q => g.metricInner q ((nabla.cov (F i) G) q) (F i q)) p := by
    have h1 : X.dir (laplacianAt g nabla f) p
        = X.dir (fun q => ∑ i, g.metricInner q
            ((nabla.cov (F i) G) q) (F i q)) p := by
      show mfderiv I 𝓘(ℝ, ℝ) (laplacianAt g nabla f) p (X p)
        = mfderiv I 𝓘(ℝ, ℝ)
            (fun q => ∑ i, g.metricInner q ((nabla.cov (F i) G) q) (F i q))
            p (X p)
      rw [hev.mfderiv_eq]
      rfl
    rw [h1]
    exact dir_sum X
      (fun i _ => contMDiff_metricInner_fields g (nabla.cov (F i) G) (F i)) p
  -- (2) metric compatibility on each summand
  have hcompat : ∀ i, X.dir
        (fun q => g.metricInner q ((nabla.cov (F i) G) q) (F i q)) p
      = g.metricInner p ((nabla.cov X (nabla.cov (F i) G)) p) (F i p)
        + g.metricInner p ((nabla.cov (F i) G) p) ((nabla.cov X (F i)) p) :=
    fun i => hLC.2 X (nabla.cov (F i) G) (F i) p
  -- (3) expand the second covariant derivative
  have hsecond : ∀ i, g.metricInner p ((secondCov nabla X (F i) G) p) (F i p)
      = g.metricInner p ((nabla.cov X (nabla.cov (F i) G)) p) (F i p)
        - g.metricInner p ((nabla.cov (nabla.cov X (F i)) G) p) (F i p) := by
    intro i
    rw [secondCov_apply, g.metricInner_sub_left]
  -- (4) the two correction sums are Hessian contractions
  have hriesz1 : ∀ i,
      g.metricInner p ((nabla.cov (nabla.cov X (F i)) G) p) (F i p)
        = hessianAt nabla f p ((nabla.cov X (F i)) p) (F i p) := fun i =>
    metricInner_cov_gradientField_eq_hessianAt g hLC.2 hf
      (nabla.cov X (F i)) p (F i p)
  have hriesz2 : ∀ i,
      g.metricInner p ((nabla.cov (F i) G) p) ((nabla.cov X (F i)) p)
        = hessianAt nabla f p (F i p) ((nabla.cov X (F i)) p) := fun i =>
    metricInner_cov_gradientField_eq_hessianAt g hLC.2 hf
      (F i) p ((nabla.cov X (F i)) p)
  -- (5) antisymmetry of the connection coefficients of the frame
  have hanti : ∀ i j,
      g.metricInner p ((nabla.cov X (F i)) p) (F j p)
        + g.metricInner p ((nabla.cov X (F j)) p) (F i p) = 0 := by
    intro i j
    have hdir0 : X.dir (fun q => g.metricInner q (F i q) (F j q)) p = 0 := by
      have hconst : (fun q => g.metricInner q (F i q) (F j q))
          =ᶠ[𝓝 p] fun _ => if i = j then (1 : ℝ) else 0 := hON i j
      show mfderiv I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (F i q) (F j q)) p (X p)
        = 0
      rw [hconst.mfderiv_eq, mfderiv_const]
      rfl
    have hc := hLC.2 X (F i) (F j) p
    rw [hdir0] at hc
    have hcm := g.metricInner_comm p ((nabla.cov X (F j)) p) (F i p)
    linarith
  -- (6) expand `∇_X Fᵢ(p)` over the orthonormal basis `{Fⱼ(p)}`
  set e := orthonormalBasisOfMetricInner g hONp with hedef
  have happ : ∀ i, e i = F i p := fun i =>
    orthonormalBasisOfMetricInner_apply g hONp i
  have hexpand : ∀ i, hessianAt nabla f p (F i p) ((nabla.cov X (F i)) p)
      = ∑ j, g.metricInner p ((nabla.cov X (F i)) p) (F j p)
          * hessianAt nabla f p (F i p) (F j p) := by
    intro i
    set W := (nabla.cov X (F i)) p with hWdef
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
  have hS : ∑ i, hessianAt nabla f p (F i p) ((nabla.cov X (F i)) p) = 0 := by
    set S := ∑ i, hessianAt nabla f p (F i p) ((nabla.cov X (F i)) p) with hSdef
    have hSsum : S = ∑ i, ∑ j,
        g.metricInner p ((nabla.cov X (F i)) p) (F j p)
          * hessianAt nabla f p (F i p) (F j p) := by
      rw [hSdef]
      exact Finset.sum_congr rfl fun i _ => hexpand i
    have hneg : S = -S := by
      calc S = ∑ i, ∑ j,
            g.metricInner p ((nabla.cov X (F i)) p) (F j p)
              * hessianAt nabla f p (F i p) (F j p) := hSsum
        _ = ∑ j, ∑ i,
            g.metricInner p ((nabla.cov X (F i)) p) (F j p)
              * hessianAt nabla f p (F i p) (F j p) := Finset.sum_comm
        _ = ∑ i, ∑ j,
            -(g.metricInner p ((nabla.cov X (F i)) p) (F j p))
              * hessianAt nabla f p (F i p) (F j p) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            have h1 : g.metricInner p ((nabla.cov X (F j)) p) (F i p)
                = -(g.metricInner p ((nabla.cov X (F i)) p) (F j p)) := by
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
  have hgoal : ∑ i, g.metricInner p ((secondCov nabla X (F i) G) p) (F i p)
      = ∑ i, (g.metricInner p ((nabla.cov X (nabla.cov (F i) G)) p) (F i p)
          - hessianAt nabla f p ((nabla.cov X (F i)) p) (F i p)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsecond i, hriesz1 i]
  have hrhs : X.dir (laplacianAt g nabla f) p
      = ∑ i, (g.metricInner p ((nabla.cov X (nabla.cov (F i) G)) p) (F i p)
          + hessianAt nabla f p (F i p) ((nabla.cov X (F i)) p)) := by
    rw [hdirΔ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcompat i, hriesz2 i]
  rw [hgoal, hrhs, Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, add_zero]
  have hsymm_sum : ∑ i, hessianAt nabla f p ((nabla.cov X (F i)) p) (F i p)
      = ∑ i, hessianAt nabla f p (F i p) ((nabla.cov X (F i)) p) :=
    Finset.sum_congr rfl fun i _ =>
      hessianAt_symm nabla hLC.1 hf p ((nabla.cov X (F i)) p) (F i p)
  rw [hsymm_sum, hS, sub_zero]

/-! ### The Ricci trace of the curvature term -/

/-- **Math.** **The off-diagonal Ricci trace**: for the Levi-Civita
connection, smooth vector fields `V, W`, and smooth fields `F₁, …, F_n` whose
values at `p` are `g_p`-orthonormal,
`Σᵢ ⟨ℛ_MT(Fᵢ, V)W, Fᵢ⟩(p) = Ric_p(W(p), V(p))`.
Each summand is the curvature-tensor value `ℛ(Fᵢ, V, Fᵢ, W)(p)`, which by the
pair-swap symmetry and the two pair antisymmetries
(`claim:curvature-symmetries-bianchi`) equals `ℛ(W, Fᵢ, V, Fᵢ)(p)`; summing
gives the orthonormal-basis formula for the Ricci tensor. This generalizes
the diagonal case `sum_metricInner_riemannCurvature_self_eq_ricciAt` and is
the blueprint's contraction
`−g^{jk} df(ℛ(∂_k, ∂_i)∂_j) = Ric((∇f)^*, ∂_i)`.
Blueprint: `lem:laplacian-one-form`. -/
theorem sum_metricInner_riemannCurvature_frame_eq_ricciAt
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) (V W : SmoothVectorField I M) {p : M}
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hONp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0) :
    ∑ i, g.metricInner p ((riemannCurvature nabla (F i) V W) p) (F i p)
      = ricciAt g nabla hLC p (W p) (V p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hAlg := isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  set e := orthonormalBasisOfMetricInner g hONp with hedef
  have happ : ∀ i, e i = F i p := fun i =>
    orthonormalBasisOfMetricInner_apply g hONp i
  have hsummand : ∀ i,
      g.metricInner p ((riemannCurvature nabla (F i) V W) p) (F i p)
        = curvatureFormAt g nabla p (W p) (F i p) (V p) (F i p) := by
    intro i
    have h0 : g.metricInner p ((riemannCurvature nabla (F i) V W) p) (F i p)
        = curvatureForm g nabla (F i) V (F i) W p := rfl
    have h1 : curvatureForm g nabla (F i) V (F i) W p
        = curvatureFormAt g nabla p (F i p) (V p) (F i p) (W p) := by
      rw [curvatureForm_eq g nabla hLC.2 (F i) V (F i) W p]
      exact (curvatureFormAt_eq g nabla (F i) V (F i) W p).symm
    have h2 : curvatureFormAt g nabla p (F i p) (V p) (F i p) (W p)
        = curvatureFormAt g nabla p (W p) (F i p) (V p) (F i p) := by
      rw [hAlg.pairSwap]
      rw [curvatureFormAt_antisymm_left g nabla p,
        curvatureFormAt_antisymm_right g nabla hLC.2 p, neg_neg]
    rw [h0, h1, h2]
  rw [Finset.sum_congr rfl fun i _ => hsummand i]
  calc ∑ i, curvatureFormAt g nabla p (W p) (F i p) (V p) (F i p)
      = ∑ i, curvatureFormAt g nabla p (W p) (e i) (V p) (e i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [happ i]
    _ = ricciAt g nabla hLC p (W p) (V p) :=
        (ricciForm_eq_sum hAlg (W p) (V p) e).symm

/-! ### The Laplacian of a differential -/

/-- **Math.** **Morgan–Tian's Laplacian-of-a-one-form formula**
(`lem:laplacian-one-form`, eq. `lapformula`): for a smooth function `f` on a
Riemannian manifold, at every `p` and `z ∈ T_pM`,
`Δ(df)(z) = d(Δf)(z) + Ric_p((∇f)^*(p), z)`.
Here `Δ(df)` is the trace of `∇(df)` (`oneFormLaplacianAt` of the gradient
field), `d(Δf)(z) = z(Δf)` is the differential of the Laplacian
(`dirTangent`; `Δf` is smooth by `contMDiff_laplacianAt`), and `Ric` is the
Ricci tensor. Proof: evaluate the trace in a smooth local orthonormal frame,
swap the pairing slot into the middle slot by the differentiated Hessian
symmetry, commute the outer and middle slots by the Ricci commutation
identity, and identify the two resulting traces as `z(Δf)` (trace
commutation) and `Ric((∇f)^*, z)` (Ricci trace of the curvature term).
Blueprint: `lem:laplacian-one-form`. -/
theorem oneFormLaplacianAt_gradientField_eq_dirTangent_laplacianAt_add_ricciAt
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (z : TangentSpace I p) :
    oneFormLaplacianAt g nabla (gradientField g f hf) p z
      = dirTangent (laplacianAt g nabla f) z
        + ricciAt g nabla hLC p (gradientAt g f p) z := by
  classical
  obtain ⟨F, hON⟩ := exists_orthonormalFrame g p
  have hONp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0 :=
    fun i j => (hON i j).self_of_nhds
  rw [oneFormLaplacianAt_eq_sum_frame g nabla (gradientField g f hf) hONp z]
  have hsym : ∀ i, g.metricInner p
        ((secondCov nabla (F i) (F i) (gradientField g f hf)) p) z
      = g.metricInner p
          ((secondCov nabla (F i) (extendVector p z) (gradientField g f hf)) p)
          (F i p) := by
    intro i
    have h := metricInner_secondCov_gradientField_symm g hLC hf
      (F i) (F i) (extendVector p z) p
    rwa [extendVector_apply] at h
  have hcomm : ∀ i, g.metricInner p
        ((secondCov nabla (F i) (extendVector p z) (gradientField g f hf)) p)
        (F i p)
      = g.metricInner p
          ((secondCov nabla (extendVector p z) (F i) (gradientField g f hf)) p)
          (F i p)
        + g.metricInner p
            ((riemannCurvature nabla (F i) (extendVector p z)
              (gradientField g f hf)) p)
            (F i p) := by
    intro i
    have h := secondCov_sub_swap_apply hLC.1 (F i) (extendVector p z)
      (gradientField g f hf) p
    have h2 : (secondCov nabla (F i) (extendVector p z)
          (gradientField g f hf)) p
        = (secondCov nabla (extendVector p z) (F i) (gradientField g f hf)) p
          + (riemannCurvature nabla (F i) (extendVector p z)
              (gradientField g f hf)) p := by
      rw [← h]
      abel
    rw [h2, g.metricInner_add_left]
  calc ∑ i, g.metricInner p
        ((secondCov nabla (F i) (F i) (gradientField g f hf)) p) z
      = ∑ i, (g.metricInner p
          ((secondCov nabla (extendVector p z) (F i) (gradientField g f hf)) p)
          (F i p)
        + g.metricInner p
            ((riemannCurvature nabla (F i) (extendVector p z)
              (gradientField g f hf)) p)
            (F i p)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsym i, hcomm i]
    _ = (∑ i, g.metricInner p
          ((secondCov nabla (extendVector p z) (F i) (gradientField g f hf)) p)
          (F i p))
        + ∑ i, g.metricInner p
            ((riemannCurvature nabla (F i) (extendVector p z)
              (gradientField g f hf)) p)
            (F i p) := Finset.sum_add_distrib
    _ = dirTangent (laplacianAt g nabla f) z
        + ricciAt g nabla hLC p (gradientAt g f p) z := by
        have h1 := sum_metricInner_secondCov_along_frame_eq_dir_laplacianAt
          g hLC hf (extendVector p z) hON
        have h1' : (extendVector p z).dir (laplacianAt g nabla f) p
            = dirTangent (laplacianAt g nabla f) z := by
          show mfderiv I 𝓘(ℝ, ℝ) (laplacianAt g nabla f) p
              ((extendVector p z) p)
            = mfderiv I 𝓘(ℝ, ℝ) (laplacianAt g nabla f) p z
          rw [extendVector_apply]
        have h2 := sum_metricInner_riemannCurvature_frame_eq_ricciAt
          g hLC (extendVector p z) (gradientField g f hf) hONp
        rw [h1, h1', h2, gradientField_apply, extendVector_apply]

/-- **Math.** The Laplacian-of-a-one-form formula with the differential term
as the gradient pairing: `Δ(df)(z) = ⟨(∇Δf)^*(p), z⟩ + Ric_p((∇f)^*(p), z)`.
Blueprint: `lem:laplacian-one-form`. -/
theorem oneFormLaplacianAt_gradientField_eq_metricInner_gradientAt_add_ricciAt
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (z : TangentSpace I p) :
    oneFormLaplacianAt g nabla (gradientField g f hf) p z
      = g.metricInner p (gradientAt g (laplacianAt g nabla f) p) z
        + ricciAt g nabla hLC p (gradientAt g f p) z := by
  rw [oneFormLaplacianAt_gradientField_eq_dirTangent_laplacianAt_add_ricciAt
    g hLC hf p z]
  congr 1
  exact (metricInner_gradientAt g (laplacianAt g nabla f) p z).symm

end MorganTianLib

end
