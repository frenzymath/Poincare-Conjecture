import OpenGALib.Riemannian.Connection.ChartCurvature
import OpenGALib.Riemannian.Connection.CurvaturePointwise

/-!
# The Riemann curvature tensor in a **fixed chart at a moving point**

`ChartCurvature.lean` computes the intrinsic curvature `R(∂_i,∂_j)∂_k` of the
Levi-Civita connection in the chart frame `∂ = chartBasisVecFiber p ·`, but only
**at the chart's own centre `p`** (`leviCivita_curvature_chartFrame_expansion`):
the global smooth field `chartFrameField p m` agrees with `∂_m` only near `p`,
so that formula is base-point-only.

do Carmo's Jacobi-field computation (Ch. 5) and the curvature-commutation lemma
(Ch. 4, `lem:dc-ch4-4-1`) need the curvature **at a moving point `q` read in one
fixed chart at a base point `α`**: along a geodesic `γ` with `α = γ(0)`, the
coefficients `a_{ij}(t) = ⟨R(γ',e_i)γ', e_j⟩` are the curvature evaluated at the
moving point `γ(t)`, in the single chart at `α`. This is the "chart-curvature
bridge" flagged as the missing step in
`OpenGALib/Riemannian/Jacobi/FrameReduction.lean`.

This file supplies it. Working with an **arbitrary** smooth frame `Y` agreeing
with the coordinate frame `chartBasisVecFiber α ·` near a point `q ∈` chart
source (not necessarily the centre `α`), we prove the moving-point analogues of
the three `ChartCurvature.lean` steps:

* `leviCivita_cov_frame_expansion` — `(∇_{Y_i} Y_j)(q) = Σ_m Γ^m_{ij}(q) ∂_m(q)`;
* `leviCivita_cov_cov_frame_expansion` — the double covariant derivative;
* `leviCivita_curvature_frame_expansion` — `R(Y_i,Y_j)Y_k(q) = Σ_l R^l_{ijk}(q) ∂_l(q)`.

Building a `q`-centred frame from `exists_smoothVectorField_eventuallyEq` then
gives the intrinsic, frame-free consequence

* `curvatureOperatorAt_chartBasis_expansion` —
  `R(∂_i, ∂_j)∂_k` at any `q` in the chart at `α`, with the coordinate curvature
  coefficients `R^l_{ijk}` of the **fixed** chart at `α` evaluated at
  `extChartAt I α q`.

Here `Γ = chartChristoffel g α · · ·` and the coordinate curvature coefficient is
`R^l_{ijk}(y) = ∂_jΓ^l_{ik}(y) − ∂_iΓ^l_{jk}(y) + Σ_s(Γ^s_{ik}(y)Γ^l_{js}(y) −
Γ^s_{jk}(y)Γ^l_{is}(y))`, matching `leviCivita_curvature_chartFrame_expansion` at
`y = extChartAt I α α`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ## The moving-point frame expansion for an arbitrary agreeing frame -/

/-- **Math.** The **moving-point frame expansion** for an arbitrary smooth frame
`Y` agreeing with the coordinate frame near `q`: if `Y m =ᶠ[nhds q] ∂_m`
(`∂_m = chartBasisVecFiber α m`) for every `m`, and `q` lies in the chart at `α`,
then `(∇_{Y_i} Y_j)(q) = Σ_m Γ^m_{ij}(q) ∂_m(q)` with `Γ^m_{ij}(q) =
chartChristoffel g α i j m (extChartAt I α q)` the coordinate Christoffel symbols
of the **fixed** chart at `α`. This is `leviCivita_cov_chartFrameField_expansion`
freed from the `chartFrameField α` witness (so it applies at any `q`, with the
witness a frame agreeing near `q`, not near `α`). -/
theorem leviCivita_cov_frame_expansion (g : RiemannianMetric I M) (α : M)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (i j : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H α).source)
    (hev : ∀ m, ⇑(Y m) =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) α m x) :
    (g.leviCivitaConnection.cov (Y i) (Y j)) q
      = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α q) •
          chartBasisVecFiber (I := I) α m q := by
  classical
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  have hbr : ∀ a b, DCLieBracket (Y a) (Y b) q = 0 := by
    intro a b
    show VectorField.mlieBracket I (Y a).toFun (Y b).toFun q = 0
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hev a) (hev b)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α a b hq
  have hdir : ∀ r a b, (Y r).dir
      (fun q' => g.metricInner q' (Y a q') (Y b q')) q
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) (extChartAt I α q) := by
    intro r a b
    have hfeq : (fun q' => g.metricInner q' (Y a q') (Y b q'))
        =ᶠ[nhds q] (fun q' => chartGramMatrix (I := I) g α q' a b) := by
      filter_upwards [hev a, hev b] with q' hqa hqb
      rw [hqa, hqb]
      exact (chartGramMatrix_apply (I := I) g α q' a b).symm
    show mfderiv I 𝓘(ℝ, ℝ) (fun q' => g.metricInner q' (Y a q') (Y b q')) q ((Y r) q) = _
    rw [hfeq.mfderiv_eq, (hev r).self_of_nhds]
    exact mfderiv_chartGramMatrix_eq_partialDeriv (I := I) g α a b r hq
  have hpe : (extChartAt I α).symm (extChartAt I α q) = q :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  have hval : ∀ a, Y a q = chartBasisVecFiber (I := I) α a q :=
    fun a => (hev a).self_of_nhds
  rw [christoffel_bridge_vector (I := I) g g.leviCivitaConnection hLC α q Y hbr hdir hq hpe hval
    i j]
  exact Finset.sum_congr rfl fun m _ => by rw [hval m]

/-! ## The moving-point double covariant derivative for an agreeing frame -/

/-- **Math.** The **double covariant derivative at a moving point `q`** for an
agreeing frame `Y`: `(∇_{Y_i}∇_{Y_j} Y_k)(q) = Σ_l (∂_iΓ^l_{jk}(q) + Σ_s
Γ^s_{jk}(q)Γ^l_{is}(q)) ∂_l(q)`, all Christoffel symbols read in the fixed chart
at `α` and evaluated at `extChartAt I α q`. Moving-point analogue of
`leviCivita_cov_cov_chartFrameField` (which fixes `q = α`). -/
theorem leviCivita_cov_cov_frame_expansion (g : RiemannianMetric I M) (α : M)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (i j k : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H α).source)
    (hev : ∀ m, ⇑(Y m) =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) α m x) :
    (g.leviCivitaConnection.cov (Y i)
        (g.leviCivitaConnection.cov (Y j) (Y k))) q
      = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
              (extChartAt I α q)
            + ∑ s, chartChristoffel (I := I) g α j k s (extChartAt I α q)
                * chartChristoffel (I := I) g α i s l (extChartAt I α q))
          • chartBasisVecFiber (I := I) α l q := by
  classical
  set nabla := g.leviCivitaConnection with hnabla
  -- the moving Christoffel functions are smooth on the chart source
  have hΓsmooth : ∀ m, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x => chartChristoffel (I := I) g α j k m (extChartAt I α x))
      (chartAt H α).source := by
    intro m
    have hΓE : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chartChristoffel (I := I) g α j k m)
        (interior (extChartAt I α).target) :=
      (chartChristoffel_contDiffOn_interior (I := I) g α j k m).contMDiffOn
    have hsub : (chartAt H α).source ⊆
        extChartAt I α ⁻¹' (interior (extChartAt I α).target) := by
      intro q' hq'
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source (by rwa [extChartAt_source]))
    exact hΓE.comp (contMDiffOn_extChartAt (I := I) (x := α) (n := ∞)) hsub
  -- global smooth functions agreeing with them near `q`
  choose γ hγsmooth hγev using fun m =>
    exists_contMDiff_eventuallyEq (I := I) ((chartAt H α).open_source)
      (hΓsmooth m) hq
  -- the frame combination field, as a single bundled smooth field
  have hWsmooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun q' => (⟨q', ∑ m, γ m q' • Y m q'⟩ : TangentBundle I M)) :=
    ContMDiff.sum_section fun m _ =>
      ContMDiff.smul_section (hγsmooth m) (Y m).smooth
  set W : SmoothVectorField I M :=
    ⟨fun q' => ∑ m, γ m q' • Y m q', hWsmooth⟩ with hWeq
  have hWdef : ∀ q', W q' = ∑ m, γ m q' • Y m q' := fun q' => rfl
  -- open neighborhood of `q` where the frame agrees and `γ = Γ`
  obtain ⟨U, hU, hUopen, hqU⟩ := eventually_nhds_iff.mp
    (((eventually_all.mpr fun m => hev m).and
      (eventually_all.mpr fun m => hγev m)).and
      ((chartAt H α).open_source.eventually_mem hq))
  have hUsub : U ⊆ (chartAt H α).source := fun q' hq' => (hU q' hq').2
  have hUframe : ∀ m, ∀ q' ∈ U,
      Y m q' = chartBasisVecFiber (I := I) α m q' :=
    fun m q' hq' => (hU q' hq').1.1 m
  have hUγ : ∀ m, ∀ q' ∈ U,
      γ m q' = chartChristoffel (I := I) g α j k m (extChartAt I α q') :=
    fun m q' hq' => (hU q' hq').1.2 m
  -- `∇_{Y_j} Y_k = W` on `U`
  have hEqOn : Set.EqOn ⇑(nabla.cov (Y j) (Y k)) ⇑W U := by
    intro q' hq'
    have hq'src : q' ∈ (chartAt H α).source := hUsub hq'
    have hev' : ∀ m, ⇑(Y m)
        =ᶠ[nhds q'] fun x => chartBasisVecFiber (I := I) α m x := fun m =>
      eventuallyEq_of_mem (hUopen.mem_nhds hq') fun x hx => hUframe m x hx
    show (nabla.cov (Y j) (Y k)) q' = ∑ m, γ m q' • Y m q'
    rw [leviCivita_cov_frame_expansion (I := I) g α Y j k hq'src hev']
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hUγ m q' hq', hUframe m q' hq']
  have hEvW : ⇑(nabla.cov (Y j) (Y k)) =ᶠ[nhds q] ⇑W :=
    eventuallyEq_of_mem (hUopen.mem_nhds hqU) hEqOn
  rw [nabla.cov_congr_apply_eventuallyEq_right (Y i) hEvW,
    nabla.cov_smulSum_apply (Y i) q Finset.univ γ hγsmooth
      (fun m => Y m) W hWdef]
  -- rewrite each summand
  have hstep : ∀ m : Fin (Module.finrank ℝ E),
      (Y i).dir (γ m) q • (Y m) q
        + γ m q • (nabla.cov (Y i) (Y m)) q
      = partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m) (extChartAt I α q)
            • chartBasisVecFiber (I := I) α m q
        + chartChristoffel (I := I) g α j k m (extChartAt I α q) •
            ∑ l, chartChristoffel (I := I) g α i m l (extChartAt I α q) •
              chartBasisVecFiber (I := I) α l q := by
    intro m
    have hd : (Y i).dir (γ m) q
        = partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m) (extChartAt I α q) := by
      show mfderiv I 𝓘(ℝ, ℝ) (γ m) q ((Y i) q) = _
      rw [(hev i).self_of_nhds, (hγev m).mfderiv_eq]
      exact mfderiv_chartChristoffel_eq_partialDeriv (I := I) g α j k m i hq
    have hγval : γ m q = chartChristoffel (I := I) g α j k m (extChartAt I α q) :=
      (hγev m).self_of_nhds
    have hYval : Y m q = chartBasisVecFiber (I := I) α m q := (hev m).self_of_nhds
    have hcov : (nabla.cov (Y i) (Y m)) q
        = ∑ l, chartChristoffel (I := I) g α i m l (extChartAt I α q) •
            chartBasisVecFiber (I := I) α l q :=
      leviCivita_cov_frame_expansion (I := I) g α Y i m hq hev
    rw [hd, hγval, hcov, hYval]
  rw [Finset.sum_congr rfl fun m _ => hstep m]
  -- reorganize the finite sums
  calc ∑ m, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m)
            (extChartAt I α q) • chartBasisVecFiber (I := I) α m q
          + chartChristoffel (I := I) g α j k m (extChartAt I α q) •
              ∑ l, chartChristoffel (I := I) g α i m l (extChartAt I α q) •
                chartBasisVecFiber (I := I) α l q)
      = ∑ m, partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m)
            (extChartAt I α q) • chartBasisVecFiber (I := I) α m q
        + ∑ m, ∑ l, (chartChristoffel (I := I) g α j k m (extChartAt I α q) *
              chartChristoffel (I := I) g α i m l (extChartAt I α q)) •
            chartBasisVecFiber (I := I) α l q := by
        rw [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun l _ => smul_smul ..
    _ = ∑ l, partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
            (extChartAt I α q) • chartBasisVecFiber (I := I) α l q
        + ∑ l, (∑ s, chartChristoffel (I := I) g α j k s (extChartAt I α q) *
              chartChristoffel (I := I) g α i s l (extChartAt I α q)) •
            chartBasisVecFiber (I := I) α l q := by
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
    _ = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
            (extChartAt I α q)
          + ∑ s, chartChristoffel (I := I) g α j k s (extChartAt I α q) *
              chartChristoffel (I := I) g α i s l (extChartAt I α q))
          • chartBasisVecFiber (I := I) α l q := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => (add_smul ..).symm

/-! ## The moving-point curvature coordinate formula for an agreeing frame -/

/-- **Math.** The **Riemann curvature in the fixed chart at `α`, at a moving point
`q`**, for an agreeing frame `Y`: `R(Y_i,Y_j)Y_k(q) = Σ_l R^l_{ijk}(q) ∂_l(q)`,
with `R^l_{ijk}(q) = ∂_jΓ^l_{ik} − ∂_iΓ^l_{jk} + Σ_s(Γ^s_{ik}Γ^l_{js} −
Γ^s_{jk}Γ^l_{is})` evaluated at `extChartAt I α q` (Christoffel symbols of the
fixed chart at `α`). Moving-point analogue of
`leviCivita_curvature_chartFrame_expansion`; the bracket term vanishes because the
frame agrees with a coordinate frame near `q`. -/
theorem leviCivita_curvature_frame_expansion (g : RiemannianMetric I M) (α : M)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (i j k : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H α).source)
    (hev : ∀ m, ⇑(Y m) =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) α m x) :
    (g.leviCivitaConnection.curvature (Y i) (Y j) (Y k)) q
      = ∑ l, (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)
              (extChartAt I α q)
            - partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
              (extChartAt I α q)
            + ∑ s, (chartChristoffel (I := I) g α i k s (extChartAt I α q)
                  * chartChristoffel (I := I) g α j s l (extChartAt I α q)
                - chartChristoffel (I := I) g α j k s (extChartAt I α q)
                  * chartChristoffel (I := I) g α i s l (extChartAt I α q)))
          • chartBasisVecFiber (I := I) α l q := by
  classical
  set nabla := g.leviCivitaConnection with hnabla
  rw [nabla.curvature_apply]
  -- the bracket term vanishes: `[Y_i, Y_j]|_q = 0`
  have hbrq : bracketField (Y i) (Y j) q = (0 : SmoothVectorField I M) q := by
    rw [bracketField_apply, SmoothVectorField.zero_apply]
    show VectorField.mlieBracket I (Y i).toFun (Y j).toFun q = 0
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hev i) (hev j)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α i j hq
  have hbr0 : (nabla.cov (bracketField (Y i) (Y j)) (Y k)) q = 0 := by
    rw [nabla.cov_congr_apply_left (Y k) hbrq, nabla.cov_zero_left]
  rw [hbr0, add_zero,
    leviCivita_cov_cov_frame_expansion (I := I) g α Y i j k hq hev,
    leviCivita_cov_cov_frame_expansion (I := I) g α Y j i k hq hev,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← sub_smul]
  congr 1
  rw [Finset.sum_sub_distrib]
  ring

/-! ## Multilinearity of the pointwise curvature operator

`curvatureOperatorAt` is `ℝ`-multilinear in each of its three tangent-vector
slots — the pointwise shadow of the field-level linearity
`curvature_add_left/middle/right`, `curvature_smul_left/middle/right`, lifted
through `curvatureOperatorAt_eq` and the smooth extensions `extendField`. These
let an arbitrary tangent vector be expanded in the chart basis, turning
`curvatureOperatorAt_chartBasis_expansion` (basis vectors) into the curvature at
*arbitrary* chart-read vectors, e.g. `a_{ij} = ⟨R(γ',e_i)γ',e_j⟩` of the Ch. 5
Jacobi equation. -/

namespace AffineConnection

variable (nabla : AffineConnection I M)

/-- **Math.** Additivity of `R(·,v)w` in the first slot. -/
theorem curvatureOperatorAt_add_left (p : M) (u₁ u₂ v w : TangentSpace I p) :
    nabla.curvatureOperatorAt p (u₁ + u₂) v w
      = nabla.curvatureOperatorAt p u₁ v w + nabla.curvatureOperatorAt p u₂ v w := by
  rw [nabla.curvatureOperatorAt_eq p (X := extendField p u₁ + extendField p u₂)
        (Y := extendField p v) (Z := extendField p w)
        (by rw [SmoothVectorField.add_apply, extendField_apply, extendField_apply])
        (extendField_apply p v) (extendField_apply p w),
      nabla.curvature_add_left,
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u₁) (extendField_apply p v)
        (extendField_apply p w),
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u₂) (extendField_apply p v)
        (extendField_apply p w)]

/-- **Math.** Additivity of `R(u,·)w` in the second slot. -/
theorem curvatureOperatorAt_add_middle (p : M) (u v₁ v₂ w : TangentSpace I p) :
    nabla.curvatureOperatorAt p u (v₁ + v₂) w
      = nabla.curvatureOperatorAt p u v₁ w + nabla.curvatureOperatorAt p u v₂ w := by
  rw [nabla.curvatureOperatorAt_eq p (X := extendField p u)
        (Y := extendField p v₁ + extendField p v₂) (Z := extendField p w)
        (extendField_apply p u)
        (by rw [SmoothVectorField.add_apply, extendField_apply, extendField_apply])
        (extendField_apply p w),
      nabla.curvature_add_middle,
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u) (extendField_apply p v₁)
        (extendField_apply p w),
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u) (extendField_apply p v₂)
        (extendField_apply p w)]

/-- **Math.** Additivity of `R(u,v)·` in the third slot. -/
theorem curvatureOperatorAt_add_right (p : M) (u v w₁ w₂ : TangentSpace I p) :
    nabla.curvatureOperatorAt p u v (w₁ + w₂)
      = nabla.curvatureOperatorAt p u v w₁ + nabla.curvatureOperatorAt p u v w₂ := by
  rw [nabla.curvatureOperatorAt_eq p (X := extendField p u)
        (Y := extendField p v) (Z := extendField p w₁ + extendField p w₂)
        (extendField_apply p u) (extendField_apply p v)
        (by rw [SmoothVectorField.add_apply, extendField_apply, extendField_apply]),
      nabla.curvature_add_right,
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u) (extendField_apply p v)
        (extendField_apply p w₁),
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u) (extendField_apply p v)
        (extendField_apply p w₂)]

/-- **Math.** Homogeneity of `R(·,v)w` in the first slot. -/
theorem curvatureOperatorAt_smul_left (p : M) (c : ℝ) (u v w : TangentSpace I p) :
    nabla.curvatureOperatorAt p (c • u) v w = c • nabla.curvatureOperatorAt p u v w := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  rw [nabla.curvatureOperatorAt_eq p (X := SmoothVectorField.smul (fun _ => c) hf (extendField p u))
        (Y := extendField p v) (Z := extendField p w)
        (by rw [SmoothVectorField.smul_apply, extendField_apply])
        (extendField_apply p v) (extendField_apply p w),
      nabla.curvature_smul_left hf,
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u) (extendField_apply p v)
        (extendField_apply p w)]

/-- **Math.** Homogeneity of `R(u,·)w` in the second slot. -/
theorem curvatureOperatorAt_smul_middle (p : M) (c : ℝ) (u v w : TangentSpace I p) :
    nabla.curvatureOperatorAt p u (c • v) w = c • nabla.curvatureOperatorAt p u v w := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  rw [nabla.curvatureOperatorAt_eq p (X := extendField p u)
        (Y := SmoothVectorField.smul (fun _ => c) hf (extendField p v)) (Z := extendField p w)
        (extendField_apply p u)
        (by rw [SmoothVectorField.smul_apply, extendField_apply])
        (extendField_apply p w),
      nabla.curvature_smul_middle hf,
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u) (extendField_apply p v)
        (extendField_apply p w)]

/-- **Math.** Homogeneity of `R(u,v)·` in the third slot (`R` is a tensor). -/
theorem curvatureOperatorAt_smul_right (p : M) (c : ℝ) (u v w : TangentSpace I p) :
    nabla.curvatureOperatorAt p u v (c • w) = c • nabla.curvatureOperatorAt p u v w := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  rw [nabla.curvatureOperatorAt_eq p (X := extendField p u)
        (Y := extendField p v) (Z := SmoothVectorField.smul (fun _ => c) hf (extendField p w))
        (extendField_apply p u) (extendField_apply p v)
        (by rw [SmoothVectorField.smul_apply, extendField_apply]),
      nabla.curvature_smul_right hf,
      ← nabla.curvatureOperatorAt_eq p (extendField_apply p u) (extendField_apply p v)
        (extendField_apply p w)]

end AffineConnection

/-! ## The intrinsic curvature operator in the fixed chart at a moving point -/

/-- **Math.** **The chart-curvature bridge.** For any `q` in the chart at `α`, the
intrinsic pointwise curvature operator `curvatureOperatorAt` applied to the
coordinate frame vectors `∂_i = chartBasisVecFiber α i` at `q` is the coordinate
curvature formula `R^l_{ijk}` of the **fixed** chart at `α`, evaluated at
`extChartAt I α q`:
`R(∂_i,∂_j)∂_k|_q = Σ_l (∂_jΓ^l_{ik} − ∂_iΓ^l_{jk} + Σ_s(Γ^s_{ik}Γ^l_{js} −
Γ^s_{jk}Γ^l_{is}))(extChartAt I α q) · ∂_l|_q`.

This is the frame-free, moving-point curvature identity feeding do Carmo Ch. 4
`lem:dc-ch4-4-1` and the Ch. 5 Jacobi equation `a_{ij}(t) = ⟨R(γ',e_i)γ',e_j⟩`
(`FrameReduction.lean`). -/
theorem curvatureOperatorAt_chartBasis_expansion (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H α).source) :
    g.leviCivitaConnection.curvatureOperatorAt q
        (chartBasisVecFiber (I := I) α i q) (chartBasisVecFiber (I := I) α j q)
        (chartBasisVecFiber (I := I) α k q)
      = ∑ l, (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)
              (extChartAt I α q)
            - partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
              (extChartAt I α q)
            + ∑ s, (chartChristoffel (I := I) g α i k s (extChartAt I α q)
                  * chartChristoffel (I := I) g α j s l (extChartAt I α q)
                - chartChristoffel (I := I) g α j k s (extChartAt I α q)
                  * chartChristoffel (I := I) g α i s l (extChartAt I α q)))
          • chartBasisVecFiber (I := I) α l q := by
  classical
  have hqbase : q ∈ (trivializationAt E (TangentSpace I) α).baseSet := hq
  -- a global smooth frame agreeing with the coordinate frame near `q`
  choose Y hYev using fun m =>
    exists_smoothVectorField_eventuallyEq (I := I)
      (σ := fun q' => chartBasisVecFiber (I := I) α m q')
      (trivializationAt E (TangentSpace I) α).open_baseSet
      (chartBasisVec_contMDiffOn (I := I) α m) hqbase
  have hev : ∀ m, ⇑(Y m) =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) α m x :=
    fun m => hYev m
  have hval : ∀ m, Y m q = chartBasisVecFiber (I := I) α m q :=
    fun m => (hev m).self_of_nhds
  rw [g.leviCivitaConnection.curvatureOperatorAt_eq q (hval i) (hval j) (hval k),
    leviCivita_curvature_frame_expansion (I := I) g α Y i j k hq hev]

end Riemannian

end
