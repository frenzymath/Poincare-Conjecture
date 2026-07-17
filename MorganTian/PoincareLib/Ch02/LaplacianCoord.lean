import PoincareLib.Ch01.InvGramTrace
import PoincareLib.Ch02.Laplacian
import OpenGALib.Riemannian.Connection.ChartFrameBridge

/-!
# Morgan–Tian Ch. 1 — the Laplacian in local coordinates (Christoffel form)

Blueprint `lem:laplacian-local-formula`: in a coordinate chart at `α`, writing
`F = f ∘ φ⁻¹` for the coordinate representation of a smooth `f : M → ℝ`
(`φ = extChartAt I α`), `G_{ij}` for the chart Gram matrix of the metric,
`g^{ij}` for its inverse, and `Γ^k_{ij}` for the chart Christoffel symbols
(all from `OpenGALib.Riemannian.Connection.ChartChristoffel`), this file
establishes at every chart-source point:

* `df(∂_i) = ∂_i F` — the first-derivative bridge
  (`mfderiv_apply_chartBasisVecFiber`);
* `Hess(f)(∂_i, ∂_j) = ∂_i ∂_j F − Σ_k Γ^k_{ij} ∂_k F` — the Hessian in
  local coordinates, the coordinate clause of Ch. 1's `lem:hessian-symmetric`
  (`hessianAt_chartBasisVecFiber`);
* `Δf = Σ_{ij} g^{ij} (∂_i ∂_j F − Σ_k Γ^k_{ij} ∂_k F)` — the Laplacian in
  local coordinates, blueprint `lem:laplacian-christoffel-formula`
  (`laplacianAt_eq_chart_formula`), the first display of the blueprint proof
  of `lem:laplacian-local-formula` and the exact elliptic-operator form
  `Δf = g^{ij}∂_i∂_j f + b^j ∂_j f` consumed by the Hopf strong maximum
  principle (`lem:hopf-strong-maximum`) and the maximum-principle cluster of
  Ch. 2.

The Christoffel term is produced by do Carmo's chart-Christoffel bridge
(`christoffel_bridge_vector` fed with the germ-local chart frame,
strengthened here to `exists_chartFrame_nhds_leviCivita_christoffel`); the
second-derivative term comes from differentiating the coordinate
representation twice through `mfderiv_extChartAt_chartBasisVecFiber`; the
trace over an orthonormal basis is converted to the `g^{ij}`-weighted chart
sum by `PoincareLib.sum_orthonormalBasis_diagonal_eq_invGram`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1
(blueprint `lem:laplacian-local-formula`).
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
  [I.Boundaryless]

/-! ### The first-derivative bridge -/

omit [CompleteSpace E] in
/-- **Math.** **The differential on the chart frame is the coordinate partial
derivative**: for `f` smooth at `q` and `q` in the chart source at `α`,
`df_q(∂_i|_q) = ∂_i (f ∘ φ⁻¹)(φ(q))` where `φ = extChartAt I α`. This is the
chain rule through the chart: `f = (f ∘ φ⁻¹) ∘ φ` near `q`, and `dφ_q` sends
`∂_i|_q` to the `i`-th model basis vector
(`mfderiv_extChartAt_chartBasisVecFiber`).
Blueprint: `lem:laplacian-local-formula` (first-order term). -/
theorem mfderiv_apply_chartBasisVecFiber {f : M → ℝ} {q : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f q) (α : M)
    (hq : q ∈ (chartAt H α).source) (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) f q (chartBasisVecFiber (I := I) α i q)
      = partialDeriv (E := E) i (f ∘ (extChartAt I α).symm) (extChartAt I α q) := by
  have hqe : q ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hyt : extChartAt I α q ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hqe
  have hleft : (extChartAt I α).symm (extChartAt I α q) = q :=
    (extChartAt I α).left_inv hqe
  -- the coordinate representation is smooth at `φ q`
  have hFm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f ∘ (extChartAt I α).symm)
      (extChartAt I α q) := by
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α q) :=
      (contMDiffOn_extChartAt_symm α _ hyt).contMDiffAt
        (extChartAt_target_mem_nhds' hyt)
    exact ContMDiffAt.comp _ (by rwa [hleft]) hsymm
  -- `f` agrees near `q` with its coordinate representation composed with `φ`
  have hfeq : f =ᶠ[𝓝 q] (f ∘ (extChartAt I α).symm) ∘ (extChartAt I α) := by
    filter_upwards [(chartAt H α).open_source.mem_nhds hq] with r hr
    have hre : r ∈ (extChartAt I α).source := by rwa [extChartAt_source]
    simp only [Function.comp_apply, (extChartAt I α).left_inv hre]
  have hcomp : mfderiv I 𝓘(ℝ, ℝ)
        ((f ∘ (extChartAt I α).symm) ∘ (extChartAt I α)) q
      = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ (extChartAt I α).symm)
          (extChartAt I α q)).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I α) q) :=
    mfderiv_comp q (hFm.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
      ((contMDiffAt_extChartAt' hq).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  rw [hfeq.mfderiv_eq, hcomp]
  show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ (extChartAt I α).symm) (extChartAt I α q)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) q (chartBasisVecFiber (I := I) α i q))
    = _
  rw [mfderiv_extChartAt_chartBasisVecFiber (I := I) α i hq, mfderiv_eq_fderiv]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** Locality of the coordinate partial derivative: functions that
agree near `y` have the same partial derivatives at `y`.
Blueprint: `lem:laplacian-local-formula`. -/
theorem partialDeriv_congr_of_eventuallyEq {u v : E → ℝ} {y : E}
    (h : u =ᶠ[𝓝 y] v) (i : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) i u y = partialDeriv (E := E) i v y := by
  unfold partialDeriv
  rw [h.fderiv_eq]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** The coordinate partial derivative of a smooth function, read back
on the manifold: `q ↦ ∂_j(f ∘ φ⁻¹)(φ(q))` is smooth at every chart-source
point. Blueprint: `lem:laplacian-local-formula` (smoothness of the
coefficient functions). -/
theorem contMDiffAt_partialDeriv_extChartAt {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : M) {p : M}
    (hp : p ∈ (chartAt H α).source) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q => partialDeriv (E := E) j (f ∘ (extChartAt I α).symm)
        (extChartAt I α q)) p := by
  have hpe : p ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hyt : extChartAt I α p ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hpe
  have hleft : (extChartAt I α).symm (extChartAt I α p) = p :=
    (extChartAt I α).left_inv hpe
  -- the coordinate representation is `C^∞` at `φ p`
  have hFm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f ∘ (extChartAt I α).symm)
      (extChartAt I α p) := by
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α p) :=
      (contMDiffOn_extChartAt_symm α _ hyt).contMDiffAt
        (extChartAt_target_mem_nhds' hyt)
    exact ContMDiffAt.comp _ (by rw [hleft]; exact hf p) hsymm
  have hFd : ContDiffAt ℝ ∞ (f ∘ (extChartAt I α).symm) (extChartAt I α p) :=
    contMDiffAt_iff_contDiffAt.mp hFm
  -- hence so is its derivative, and the evaluation against the basis vector
  have hdF : ContDiffAt ℝ ∞ (fderiv ℝ (f ∘ (extChartAt I α).symm))
      (extChartAt I α p) := hFd.fderiv_right (by simp)
  have hPj : ContDiffAt ℝ ∞
      (fun y => partialDeriv (E := E) j (f ∘ (extChartAt I α).symm) y)
      (extChartAt I α p) := hdF.clm_apply contDiffAt_const
  exact ContMDiffAt.comp p (contMDiffAt_iff_contDiffAt.mpr hPj)
    (contMDiffAt_extChartAt' hp)

omit [CompleteSpace E] in
/-- **Math.** The directional derivative along a field that agrees with the
chart frame near `p` is, near `p`, the coordinate partial derivative:
`Z(f) = ∂_j(f ∘ φ⁻¹) ∘ φ` on a neighbourhood of `p`.
Blueprint: `lem:laplacian-local-formula` (first-order term). -/
theorem dir_eventuallyEq_partialDeriv
    {Z : SmoothVectorField I M} {α p : M}
    (hp : p ∈ (chartAt H α).source) (j : Fin (Module.finrank ℝ E))
    (hZ : ∀ᶠ q in 𝓝 p, Z q = chartBasisVecFiber (I := I) α j q)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Z.dir f =ᶠ[𝓝 p]
      fun q => partialDeriv (E := E) j (f ∘ (extChartAt I α).symm)
        (extChartAt I α q) := by
  filter_upwards [hZ, (chartAt H α).open_source.mem_nhds hp] with q hq hqs
  show mfderiv I 𝓘(ℝ, ℝ) f q (Z q) = _
  rw [hq]
  exact mfderiv_apply_chartBasisVecFiber (hf q) α hqs j

variable [SigmaCompactSpace M] [T2Space M]

/-! ### The chart frame near a point, with its Levi-Civita Christoffel data

This strengthens `Riemannian.exists_chartFrame_leviCivita_christoffel` (which
only records the frame values *at* `p`) to a frame agreeing with the chart
basis *near* `p` — the form needed to differentiate `X_j(f)` once more — with
the covariant-derivative identity for **all** index pairs simultaneously. The
construction is that of the original proof. -/

/-- **Math.** do Carmo Ch. 2, eq. (10), germ-local form: at any chart-source
point `p` there are global smooth fields `X₁, …, X_n` agreeing with the chart
frame **near** `p` such that `∇_{X_i} X_j(p) = Σ_m Γ^m_{ij}(φ(p)) X_m(p)` for
all `i, j`, where `∇` is the Levi-Civita connection of `g` and `Γ` the chart
Christoffel symbols. Blueprint: `lem:laplacian-local-formula` (Christoffel
term). -/
theorem exists_chartFrame_nhds_leviCivita_christoffel
    (g : RiemannianMetric I M) {α p : M} (hp : p ∈ (chartAt H α).source) :
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ a, ∀ᶠ q in 𝓝 p, X a q = chartBasisVecFiber (I := I) α a q) ∧
        ∀ i j, (g.leviCivitaConnection.cov (X i) (X j)) p
          = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α p)
              • X m p := by
  classical
  have hbase : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := hp
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  -- Extend the chart frame to global smooth vector fields agreeing near `p`.
  choose Z hZ using fun a : Fin (Module.finrank ℝ E) =>
    exists_smoothVectorField_eventuallyEq (I := I)
      (σ := fun q => chartBasisVecFiber (I := I) α a q)
      (s := (trivializationAt E (TangentSpace I) α).baseSet) hbaseopen
      (chartBasisVec_contMDiffOn (I := I) α a) hbase
  have hval : ∀ a, Z a p = chartBasisVecFiber (I := I) α a p := fun a =>
    (hZ a).self_of_nhds
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hpe : (extChartAt I α).symm (extChartAt I α p) = p :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  -- `hbr`: the frame brackets vanish (germ-local reduction to the chart frame).
  have hbr : ∀ a b, DCLieBracket (Z a) (Z b) p = 0 := by
    intro a b
    show VectorField.mlieBracket I (Z a).toFun (Z b).toFun p = 0
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hZ a) (hZ b)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α a b hp
  -- `hdir`: the directional derivative is the partial derivative of the Gram
  -- matrix.
  have hdir : ∀ r a b, (Z r).dir (fun q => g.metricInner q (Z a q) (Z b q)) p
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b)
          (extChartAt I α p) := by
    intro r a b
    have hfeq : (fun q => g.metricInner q (Z a q) (Z b q))
        =ᶠ[nhds p] (fun q => chartGramMatrix (I := I) g α q a b) := by
      filter_upwards [hZ a, hZ b] with q hqa hqb
      rw [hqa, hqb]
      exact (chartGramMatrix_apply (I := I) g α q a b).symm
    show mfderiv I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (Z a q) (Z b q)) p (Z r p)
      = _
    rw [hfeq.mfderiv_eq, hval r]
    exact mfderiv_chartGramMatrix_eq_partialDeriv (I := I) g α a b r hp
  exact ⟨Z, hZ, fun i j => christoffel_bridge_vector (I := I) g
    g.leviCivitaConnection hLC α p Z hbr hdir hbase hpe hval i j⟩

/-! ### The Hessian in local coordinates -/

/-- **Math.** **The Hessian in local coordinates**: at a chart-source point
`p`, with `F = f ∘ φ⁻¹` the coordinate representation of a smooth `f`,
`Hess(f)_p(∂_i, ∂_j) = ∂_i ∂_j F(φ(p)) − Σ_k Γ^k_{ij}(φ(p)) ∂_k F(φ(p))`,
where `∇` is the Levi-Civita connection of `g`. This is the local-coordinate
clause of Ch. 1's `lem:hessian-symmetric` and the pointwise heart of
`lem:laplacian-local-formula`. -/
theorem hessianAt_chartBasisVecFiber
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {α p : M}
    (hp : p ∈ (chartAt H α).source) (i j : Fin (Module.finrank ℝ E)) :
    hessianAt g.leviCivitaConnection f p
        (chartBasisVecFiber (I := I) α i p)
        (chartBasisVecFiber (I := I) α j p)
      = partialDeriv (E := E) i
          (fun y => partialDeriv (E := E) j (f ∘ (extChartAt I α).symm) y)
          (extChartAt I α p)
        - ∑ k, chartChristoffel (I := I) g α i j k (extChartAt I α p)
            * partialDeriv (E := E) k (f ∘ (extChartAt I α).symm)
                (extChartAt I α p) := by
  obtain ⟨X, hXev, hXcov⟩ := exists_chartFrame_nhds_leviCivita_christoffel g hp
  have hval : ∀ a, X a p = chartBasisVecFiber (I := I) α a p := fun a =>
    (hXev a).self_of_nhds
  have hpe : p ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hyt : extChartAt I α p ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hpe
  -- the Hessian evaluates the frame
  have h1 : hessianAt g.leviCivitaConnection f p
      (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p)
      = hessian g.leviCivitaConnection f (X i) (X j) p := by
    rw [← hval i, ← hval j]
    exact hessianAt_eq g.leviCivitaConnection hf (X i) (X j) p
  -- first term: `X_i(X_j(f))(p) = ∂_i ∂_j F(φ(p))`
  have h2 : (X i).dir ((X j).dir f) p
      = partialDeriv (E := E) i
          (fun y => partialDeriv (E := E) j (f ∘ (extChartAt I α).symm) y)
          (extChartAt I α p) := by
    have hdirEq := dir_eventuallyEq_partialDeriv hp j (hXev j) hf
    have hstep : (X i).dir ((X j).dir f) p
        = mfderiv I 𝓘(ℝ, ℝ)
            (fun q => partialDeriv (E := E) j (f ∘ (extChartAt I α).symm)
              (extChartAt I α q)) p (X i p) := by
      show mfderiv I 𝓘(ℝ, ℝ) ((X j).dir f) p (X i p) = _
      rw [hdirEq.mfderiv_eq]
      rfl
    rw [hstep, hval i, mfderiv_apply_chartBasisVecFiber
      (contMDiffAt_partialDeriv_extChartAt hf α hp j) α hp i]
    -- collapse `(∂_j F ∘ φ) ∘ φ⁻¹` to `∂_j F` near `φ(p)`
    have hcongr : ((fun q => partialDeriv (E := E) j
          (f ∘ (extChartAt I α).symm) (extChartAt I α q))
            ∘ (extChartAt I α).symm)
        =ᶠ[𝓝 (extChartAt I α p)]
          fun y => partialDeriv (E := E) j (f ∘ (extChartAt I α).symm) y := by
      filter_upwards [extChartAt_target_mem_nhds' hyt] with y hy
      simp only [Function.comp_apply]
      rw [(extChartAt I α).right_inv hy]
    exact partialDeriv_congr_of_eventuallyEq hcongr i
  -- second term: the covariant derivative contracts to the Christoffel sum
  have h3 : (g.leviCivitaConnection.cov (X i) (X j)).dir f p
      = ∑ k, chartChristoffel (I := I) g α i j k (extChartAt I α p)
          * partialDeriv (E := E) k (f ∘ (extChartAt I α).symm)
              (extChartAt I α p) := by
    show mfderiv I 𝓘(ℝ, ℝ) f p ((g.leviCivitaConnection.cov (X i) (X j)) p) = _
    rw [hXcov i j, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hval k,
      mfderiv_apply_chartBasisVecFiber (hf p) α hp k]
    rfl
  rw [h1]
  show (X i).dir ((X j).dir f) p
      - (g.leviCivitaConnection.cov (X i) (X j)).dir f p = _
  rw [h2, h3]

/-! ### The Laplacian in local coordinates -/

omit [I.Boundaryless] in
/-- **Math.** **The Laplacian is the inverse-Gram-weighted chart sum of the
Hessian**: at a chart-source point `p`,
`Δf(p) = Σ_{ab} g^{ab}(p) Hess(f)_p(∂_a, ∂_b)`, where `g^{ab}` is the inverse
of the chart Gram matrix. This converts the orthonormal-basis trace defining
`laplacianAt` into the coordinate-frame sum, via
`sum_orthonormalBasis_diagonal_eq_invGram`.
Blueprint: `lem:laplacian-local-formula` (the trace step `tr_g = g^{ij}·`). -/
theorem laplacianAt_eq_invGram_sum (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {α p : M}
    (hp : p ∈ (chartAt H α).source) :
    laplacianAt g g.leviCivitaConnection f p
      = ∑ a, ∑ b, chartInvGramMatrix (I := I) g α p a b
          * hessianAt g.leviCivitaConnection f p
              (chartBasisVecFiber (I := I) α a p)
              (chartBasisVecFiber (I := I) α b p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hbase : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := hp
  -- the Hessian at `p` as a bilinear map
  let B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (hessianAt g.leviCivitaConnection f p)
      (fun v₁ v₂ w => hessianAt_add_left _ f p v₁ v₂ w)
      (fun a v w => hessianAt_smul_left _ f p a v w)
      (fun v w₁ w₂ => hessianAt_add_right _ hf p v w₁ w₂)
      (fun a v w => hessianAt_smul_right _ hf p a v w)
  have hB : ∀ (v w : TangentSpace I p),
      B v w = hessianAt g.leviCivitaConnection f p v w := fun v w => rfl
  -- the chart Gram matrix is the Gram matrix of the chart basis family
  have hG : ∀ a b, chartGramMatrix (I := I) g α p a b
      = inner ℝ (chartBasisFamily (I := I) α hbase a)
          (chartBasisFamily (I := I) α hbase b) := by
    intro a b
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    rfl
  have h := sum_orthonormalBasis_diagonal_eq_invGram
    (stdOrthonormalBasis ℝ (TangentSpace I p))
    (chartBasisFamily (I := I) α hbase) B hG
    (chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase)
  calc laplacianAt g g.leviCivitaConnection f p
      = ∑ i, B (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
        simp only [laplacianAt, hB]
    _ = ∑ a, ∑ b, chartInvGramMatrix (I := I) g α p a b
          • B (chartBasisFamily (I := I) α hbase a)
              (chartBasisFamily (I := I) α hbase b) := h
    _ = ∑ a, ∑ b, chartInvGramMatrix (I := I) g α p a b
          * hessianAt g.leviCivitaConnection f p
              (chartBasisVecFiber (I := I) α a p)
              (chartBasisVecFiber (I := I) α b p) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hB, chartBasisFamily_apply, chartBasisFamily_apply, smul_eq_mul]

/-- **Math.** **The Laplacian in local coordinates** (Christoffel form,
blueprint `lem:laplacian-christoffel-formula`): at a chart-source point `p`,
with `F = f ∘ φ⁻¹` the coordinate representation of a smooth `f : M → ℝ`,
`g^{ab}` the inverse chart Gram matrix and `Γ^k_{ab}` the chart Christoffel
symbols of the metric `g`,

`Δf(p) = Σ_{ab} g^{ab}(p) (∂_a ∂_b F(φ(p)) − Σ_k Γ^k_{ab}(φ(p)) ∂_k F(φ(p)))`.

Expanding the inner bracket, this is the elliptic-operator form
`Δf = g^{ab} ∂_a ∂_b F + b^k ∂_k F` (with `b^k = −g^{ab}Γ^k_{ab}` smooth)
consumed by the Hopf strong maximum principle (`lem:hopf-strong-maximum`) and
the weak-Laplacian material of Ch. 2. It is the first display of the
blueprint proof of `lem:laplacian-local-formula`; the divergence form
`Δ = (det g)^{-1/2} ∂_a (g^{ab} (det g)^{1/2} ∂_b)` follows from it by the
product rule and is not yet formalized. -/
theorem laplacianAt_eq_chart_formula (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {α p : M}
    (hp : p ∈ (chartAt H α).source) :
    laplacianAt g g.leviCivitaConnection f p
      = ∑ a, ∑ b, chartInvGramMatrix (I := I) g α p a b
          * (partialDeriv (E := E) a
              (fun y => partialDeriv (E := E) b (f ∘ (extChartAt I α).symm) y)
              (extChartAt I α p)
            - ∑ k, chartChristoffel (I := I) g α a b k (extChartAt I α p)
                * partialDeriv (E := E) k (f ∘ (extChartAt I α).symm)
                    (extChartAt I α p)) := by
  rw [laplacianAt_eq_invGram_sum g hf hp]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hessianAt_chartBasisVecFiber g hf hp a b]

end PoincareLib

end
