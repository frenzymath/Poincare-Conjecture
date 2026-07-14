import OpenGALib.Riemannian.Connection.ChartFrameBridge
import OpenGALib.Riemannian.Manifold.DoCarmoCh6Locality

/-!
# The Riemann curvature tensor in chart coordinates (`R = ∂Γ − ∂Γ + ΓΓ`)

do Carmo Ch. 8 §3 computes the curvature of the hyperbolic metric through the
**coordinate curvature coefficients** `R^s_{ijk} = ∂_jΓ^s_{ik} − ∂_iΓ^s_{jk} +
Σ_m(Γ^m_{ik}Γ^s_{jm} − Γ^m_{jk}Γ^s_{im})`. This file supplies the general bridge
tying those coordinate coefficients to the **intrinsic** curvature operator
`AffineConnection.curvature` of the metric's own Levi-Civita connection
(`prop:dc-ch8-3-const-curv`, and reusable well beyond Ch. 8 — Ch. 5 Jacobi
fields, Ch. 10 Rauch, etc.).

The main result `leviCivita_curvature_chartFrame_expansion` states, in the chart
frame `∂_i = chartBasisVecFiber p i` at `p`, that
`R(∂_i, ∂_j)∂_k = Σ_l (∂_jΓ^l_{ik} − ∂_iΓ^l_{jk} + Σ_s(Γ^s_{ik}Γ^l_{js} −
Γ^s_{jk}Γ^l_{is})) ∂_l` with `Γ = chartChristoffel g p · · ·` the coordinate
Christoffel symbols and `∂` the chart partial derivative `partialDeriv`. The sign
matches do Carmo's `Rcoeff` (`R(X,Y)Z = ∇_Y∇_X Z − ∇_X∇_Y Z + ∇_{[X,Y]}Z`).

## Method

The proof is Petersen's direct expansion (adapted to do Carmo's *field*-valued
connection `cov : 𝒳(M) → 𝒳(M) → 𝒳(M)`):

* the chart frame `∂_j` is fed to `∇` through a global smooth field
  `chartFrameField p j` agreeing with it near `p`
  (`exists_smoothVectorField_eventuallyEq`);
* the moving-point identity `∇_{∂_i}∂_j = Σ_m Γ^m_{ij} ∂_m` holds at every chart
  point (`leviCivita_cov_chartFrameField_expansion`), which for do Carmo is just
  `christoffel_bridge_vector` applied at the moving point;
* near `p` the field `∇_{∂_j}∂_k` equals the frame combination `Σ_m Γ^m_{jk} ∂_m`,
  so (by *right-slot* locality of `∇`, proved here from `cov_smul_right`) the
  Leibniz rule differentiates it along `∂_i` (`leviCivita_cov_cov_chartFrameField`);
* `[∂_i, ∂_j] = 0` kills the bracket term.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §3; Petersen, *Riemannian
Geometry* (3rd ed.), §3.1.6.
-/

set_option linter.unusedSectionVars false

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

/-! ## Local-to-global extension of germs of smooth functions -/

/-- **Math.** A function smooth on an open set `s` agrees near any `x ∈ s` with a
globally smooth function: cut off by a bump that is `1` near `x` and supported in
`s`. Function counterpart of `exists_smoothVectorField_eventuallyEq`. -/
theorem exists_contMDiff_eventuallyEq {f : M → ℝ} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f s) {x : M} (hx : x ∈ s) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[nhds x] f := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K, hK_nhds, hK_closed, hK_sub⟩ :=
    exists_mem_nhds_isClosed_subset (hs.mem_nhds hx)
  obtain ⟨K', hK'_nhds, hK'_closed, hK'_sub⟩ :=
    exists_mem_nhds_isClosed_subset
      (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hK_nhds))
  obtain ⟨lam, hlam0, hlam1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed I
      (isClosed_compl_iff.mpr isOpen_interior) hK'_closed
      (by rw [Set.disjoint_compl_left_iff_subset]; exact hK'_sub)
  refine ⟨fun q => if q ∈ s then (lam : M → ℝ) q * f q else 0, ?_, ?_⟩
  · intro q
    by_cases hq : q ∈ s
    · have hsmul : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q' => (lam : M → ℝ) q' * f q') s :=
        (lam.contMDiff.contMDiffOn).mul hf
      have hcongr : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun q' => if q' ∈ s then (lam : M → ℝ) q' * f q' else 0) s :=
        hsmul.congr fun q' hq' => if_pos hq'
      exact (hcongr q hq).contMDiffAt (hs.mem_nhds hq)
    · have hqK : q ∉ K := fun h => hq (hK_sub h)
      have hzero : ∀ q' ∈ (Kᶜ : Set M),
          (if q' ∈ s then (lam : M → ℝ) q' * f q' else 0) = 0 := by
        intro q' hq'
        by_cases hq's : q' ∈ s
        · rw [if_pos hq's]
          have hlamq' : (lam : M → ℝ) q' = 0 := by
            have hq'int : q' ∉ interior K := fun h => hq' (interior_subset h)
            simpa using hlam0 (Set.mem_compl hq'int)
          rw [hlamq', zero_mul]
        · rw [if_neg hq's]
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hK_closed.isOpen_compl.mem_nhds hqK) hzero)
  · filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hK'_nhds)]
      with q hq
    have hqK' : q ∈ K' := interior_subset hq
    have hqs : q ∈ s := hK_sub (interior_subset (hK'_sub hqK'))
    rw [if_pos hqs, show (lam : M → ℝ) q = 1 from by simpa using hlam1 hqK', one_mul]

/-! ## The chart frame as global smooth fields -/

/-- **Math.** A global smooth vector field agreeing with the coordinate frame
field `∂_j = chartBasisVecFiber α j` on a neighborhood of `α`
(`exists_smoothVectorField_eventuallyEq`). The choice is irrelevant near `α` by
locality of the connection. -/
def chartFrameField (α : M) (j : Fin (Module.finrank ℝ E)) :
    SmoothVectorField I M :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) α j q)
    (trivializationAt E (TangentSpace I) α).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) α j)
    (FiberBundle.mem_baseSet_trivializationAt' α)).choose

/-- **Math.** The defining property of `chartFrameField`: it agrees with the
coordinate frame field near `α`. -/
theorem chartFrameField_eventuallyEq (α : M) (j : Fin (Module.finrank ℝ E)) :
    ⇑(chartFrameField (I := I) α j)
      =ᶠ[nhds α] fun q => chartBasisVecFiber (I := I) α j q :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) α j q)
    (trivializationAt E (TangentSpace I) α).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) α j)
    (FiberBundle.mem_baseSet_trivializationAt' α)).choose_spec

theorem chartFrameField_apply_self (α : M) (j : Fin (Module.finrank ℝ E)) :
    chartFrameField (I := I) α j α = chartBasisVecFiber (I := I) α j α :=
  (chartFrameField_eventuallyEq (I := I) α j).self_of_nhds

/-! ## Right-slot locality of the covariant derivative -/

namespace AffineConnection

variable (nabla : AffineConnection I M)

/-- **Math.** `∇` annihilates, at `p`, *field-slot* arguments vanishing near `p`:
if `τ =ᶠ 0` near `p` then `(∇_X τ)(p) = 0`. Companion of
`cov_apply_eq_zero_of_eventuallyEq_zero_left`, proved from the Leibniz rule
`cov_smul_right`. -/
theorem cov_apply_eq_zero_of_eventuallyEq_zero_right (X : SmoothVectorField I M)
    {τ : SmoothVectorField I M} {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) :
    nabla.cov X τ p = 0 := by
  obtain ⟨f, hf, hfp, hfτ⟩ := exists_smul_eq_self_of_eventuallyEq_zero hτ
  have h := nabla.cov_smul_right hf X τ
  rw [hfτ] at h
  have h' := congrArg (fun F : SmoothVectorField I M => F p) h
  simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply] at h'
  rw [hfp, zero_smul, hτ.self_of_nhds, smul_zero, add_zero] at h'
  exact h'

/-- **Math.** **Right-slot locality of `∇`**: if `Y =ᶠ Y'` near `p` then
`(∇_X Y)(p) = (∇_X Y')(p)`. -/
theorem cov_congr_apply_eventuallyEq_right (X : SmoothVectorField I M)
    {Y Y' : SmoothVectorField I M} {p : M} (h : ⇑Y =ᶠ[nhds p] ⇑Y') :
    nabla.cov X Y p = nabla.cov X Y' p := by
  have hτ : ∀ᶠ q in nhds p, (Y - Y') q = 0 := by
    filter_upwards [h] with q hq
    rw [SmoothVectorField.sub_apply, hq, sub_self]
  have h0 := nabla.cov_apply_eq_zero_of_eventuallyEq_zero_right X hτ
  have hsub := nabla.cov_sub_right X Y Y' p
  rw [h0] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- **Math.** The covariant derivative of a field `W` that is (pointwise) a finite
combination `Σ_m f_m • V_m` of function-scaled smooth fields, evaluated at `p`:
`(∇_X W)(p) = Σ_m (X(f_m)(p) • V_m(p) + f_m(p) • (∇_X V_m)(p))` — additivity plus
the Leibniz rule. `W` is passed bundled and characterised pointwise by `hWdef`,
so no `AddCommMonoid` structure on `SmoothVectorField` is needed. -/
theorem cov_smulSum_apply (X : SmoothVectorField I M) (p : M)
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ m, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f m)) (V : ι → SmoothVectorField I M)
    (W : SmoothVectorField I M) (hWdef : ∀ q, W q = ∑ m ∈ s, f m q • V m q) :
    (nabla.cov X W) p = ∑ m ∈ s, (X.dir (f m) p • V m p + f m p • (nabla.cov X (V m)) p) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
      have hW0 : W = 0 := SmoothVectorField.ext fun q => by simpa using hWdef q
      rw [hW0, Finset.sum_empty]
      exact nabla.cov_zero_right X p
  | insert a s ha ih =>
      set Wtail : SmoothVectorField I M :=
        W - SmoothVectorField.smul (f a) (hf a) (V a) with hWtail
      have hWtaildef : ∀ q, Wtail q = ∑ m ∈ s, f m q • V m q := by
        intro q
        rw [hWtail, SmoothVectorField.sub_apply, SmoothVectorField.smul_apply, hWdef q,
          Finset.sum_insert ha]
        abel
      have hWsplit : W = SmoothVectorField.smul (f a) (hf a) (V a) + Wtail := by
        rw [hWtail]
        ext q
        rw [SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
        abel
      rw [hWsplit, nabla.add_right, SmoothVectorField.add_apply,
        nabla.leibniz (f a) (hf a) X (V a) p, ih Wtail hWtaildef, Finset.sum_insert ha]
      abel

end AffineConnection

/-! ## The chart partial derivative of the moving Christoffel symbols -/

/-- **Math.** The manifold derivative of the moving Christoffel symbol
`q ↦ Γ^c_{ab}(q)` (the fixed-chart function `chartChristoffel g α a b c` composed
with the chart) along the frame vector `∂_r` is the chart partial derivative
`∂_r Γ^c_{ab}` — the chart chain rule through
`mfderiv_extChartAt_chartBasisVecFiber`, using smoothness of the coordinate
Christoffel symbols (`chartChristoffel_contDiffOn_interior`). -/
theorem mfderiv_chartChristoffel_eq_partialDeriv (g : RiemannianMetric I M)
    (α : M) (a b c r : Fin (Module.finrank ℝ E)) {q : M}
    (hq : q ∈ (chartAt H α).source) :
    mfderiv I 𝓘(ℝ, ℝ) (fun x => chartChristoffel (I := I) g α a b c (extChartAt I α x)) q
        (chartBasisVecFiber (I := I) α r q)
      = partialDeriv (E := E) r (chartChristoffel (I := I) g α a b c)
          (extChartAt I α q) := by
  have hqsrc : q ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hy : extChartAt I α q ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hqsrc
  have hΓdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (chartChristoffel (I := I) g α a b c) (extChartAt I α q) := by
    have hnb : interior (extChartAt I α).target ∈ nhds (extChartAt I α q) :=
      Filter.mem_of_superset (extChartAt_target_mem_nhds' (I := I) hy)
        (extChartAt_target_subset_interior_of_boundaryless (I := I) α)
    have hcd : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α a b c)
        (extChartAt I α q) :=
      (chartChristoffel_contDiffOn_interior (I := I) g α a b c).contDiffAt hnb
    exact hcd.contMDiffAt.mdifferentiableAt (by decide)
  have hφdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) q :=
    mdifferentiableAt_extChartAt hq
  rw [show (fun x => chartChristoffel (I := I) g α a b c (extChartAt I α x))
      = (chartChristoffel (I := I) g α a b c) ∘ (extChartAt I α) from rfl,
    mfderiv_comp q hΓdiff hφdiff]
  show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (chartChristoffel (I := I) g α a b c) (extChartAt I α q))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) q (chartBasisVecFiber (I := I) α r q))
    = partialDeriv (E := E) r (chartChristoffel (I := I) g α a b c) (extChartAt I α q)
  rw [mfderiv_extChartAt_chartBasisVecFiber (I := I) α r hq, mfderiv_eq_fderiv]
  rfl

/-! ## The moving-point frame expansion `∇_{∂_i}∂_j = Γ^m_{ij} ∂_m` -/

/-- **Math.** The **moving-point frame expansion of the Levi-Civita connection**:
at any `q` in the chart at `α` where the global frame fields `chartFrameField α ·`
agree with the chart frame `∂ = chartBasisVecFiber α ·`,
`(∇_{∂_i} chartFrameField α j)(q) = Σ_m Γ^m_{ij}(q) ∂_m(q)`, with
`Γ^m_{ij}(q) = chartChristoffel g α i j m (extChartAt I α q)` the coordinate
Christoffel symbols of the **fixed** chart at `α`. This is do Carmo's
`christoffel_bridge_vector` applied at the moving point `q`. -/
theorem leviCivita_cov_chartFrameField_expansion (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {q : M} (hq : q ∈ (chartAt H α).source)
    (hev : ∀ m, ⇑(chartFrameField (I := I) α m)
      =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) α m x) :
    (g.leviCivitaConnection.cov (chartFrameField (I := I) α i)
        (chartFrameField (I := I) α j)) q
      = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α q) •
          chartBasisVecFiber (I := I) α m q := by
  classical
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  have hbr : ∀ a b, DCLieBracket (chartFrameField (I := I) α a)
      (chartFrameField (I := I) α b) q = 0 := by
    intro a b
    show VectorField.mlieBracket I (chartFrameField (I := I) α a).toFun
      (chartFrameField (I := I) α b).toFun q = 0
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hev a) (hev b)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α a b hq
  have hdir : ∀ r a b, (chartFrameField (I := I) α r).dir
      (fun q' => g.metricInner q' (chartFrameField (I := I) α a q')
        (chartFrameField (I := I) α b q')) q
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) (extChartAt I α q) := by
    intro r a b
    have hfeq : (fun q' => g.metricInner q' (chartFrameField (I := I) α a q')
        (chartFrameField (I := I) α b q'))
        =ᶠ[nhds q] (fun q' => chartGramMatrix (I := I) g α q' a b) := by
      filter_upwards [hev a, hev b] with q' hqa hqb
      rw [hqa, hqb]
      exact (chartGramMatrix_apply (I := I) g α q' a b).symm
    show mfderiv I 𝓘(ℝ, ℝ) (fun q' => g.metricInner q' (chartFrameField (I := I) α a q')
        (chartFrameField (I := I) α b q')) q ((chartFrameField (I := I) α r) q) = _
    rw [hfeq.mfderiv_eq, (hev r).self_of_nhds]
    exact mfderiv_chartGramMatrix_eq_partialDeriv (I := I) g α a b r hq
  have hpe : (extChartAt I α).symm (extChartAt I α q) = q :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  have hval : ∀ a, chartFrameField (I := I) α a q = chartBasisVecFiber (I := I) α a q :=
    fun a => (hev a).self_of_nhds
  rw [christoffel_bridge_vector (I := I) g g.leviCivitaConnection hLC α q
    (chartFrameField (I := I) α) hbr hdir hq hpe hval i j]
  exact Finset.sum_congr rfl fun m _ => by rw [hval m]

/-! ## The double covariant derivative of the frame -/

/-- **Math.** The double covariant derivative of the frame at `p`:
`(∇_{∂_i}∇_{∂_j}∂_k)(p) = Σ_l (∂_iΓ^l_{jk} + Σ_s Γ^s_{jk}Γ^l_{is}) ∂_l(p)`.
Leibniz expansion of `∇_{∂_i}(Γ^s_{jk} ∂_s)` at `p`, after replacing the smooth
field `∇_{∂_j}∂_k` near `p` by the frame combination `Σ_s Γ^s_{jk}(·) ∂_s`
through right-slot locality of the connection. -/
private theorem leviCivita_cov_cov_chartFrameField (g : RiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    (g.leviCivitaConnection.cov (chartFrameField (I := I) p i)
        (g.leviCivitaConnection.cov (chartFrameField (I := I) p j)
          (chartFrameField (I := I) p k))) p
      = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
              (extChartAt I p p)
            + ∑ s, chartChristoffel (I := I) g p j k s (extChartAt I p p)
                * chartChristoffel (I := I) g p i s l (extChartAt I p p))
          • chartBasisVecFiber (I := I) p l p := by
  classical
  set nabla := g.leviCivitaConnection with hnabla
  -- the moving Christoffel functions are smooth on the chart source
  have hΓsmooth : ∀ m, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x => chartChristoffel (I := I) g p j k m (extChartAt I p x))
      (chartAt H p).source := by
    intro m
    have hΓE : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chartChristoffel (I := I) g p j k m)
        (interior (extChartAt I p).target) :=
      (chartChristoffel_contDiffOn_interior (I := I) g p j k m).contMDiffOn
    have hsub : (chartAt H p).source ⊆
        extChartAt I p ⁻¹' (interior (extChartAt I p).target) := by
      intro q hq
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) p
        ((extChartAt I p).map_source (by rwa [extChartAt_source]))
    exact hΓE.comp (contMDiffOn_extChartAt (I := I) (x := p) (n := ∞)) hsub
  -- global smooth functions agreeing with them near `p`
  choose γ hγsmooth hγev using fun m =>
    exists_contMDiff_eventuallyEq (I := I) ((chartAt H p).open_source)
      (hΓsmooth m) (mem_chart_source H p)
  -- the frame combination field, as a single bundled smooth field
  have hWsmooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, ∑ m, γ m q • chartFrameField (I := I) p m q⟩ : TangentBundle I M)) :=
    ContMDiff.sum_section fun m _ =>
      ContMDiff.smul_section (hγsmooth m) (chartFrameField (I := I) p m).smooth
  set W : SmoothVectorField I M :=
    ⟨fun q => ∑ m, γ m q • chartFrameField (I := I) p m q, hWsmooth⟩ with hWeq
  have hWdef : ∀ q, W q = ∑ m, γ m q • chartFrameField (I := I) p m q := fun q => rfl
  -- open neighborhood of `p` where the frame agrees and `γ = Γ`
  obtain ⟨U, hU, hUopen, hpU⟩ := eventually_nhds_iff.mp
    (((eventually_all.mpr fun m => chartFrameField_eventuallyEq (I := I) p m).and
      (eventually_all.mpr fun m => hγev m)).and
      ((chartAt H p).open_source.eventually_mem (mem_chart_source H p)))
  have hUsub : U ⊆ (chartAt H p).source := fun q hq => (hU q hq).2
  have hUframe : ∀ m, ∀ q ∈ U,
      chartFrameField (I := I) p m q = chartBasisVecFiber (I := I) p m q :=
    fun m q hq => (hU q hq).1.1 m
  have hUγ : ∀ m, ∀ q ∈ U,
      γ m q = chartChristoffel (I := I) g p j k m (extChartAt I p q) :=
    fun m q hq => (hU q hq).1.2 m
  -- `∇_{∂_j}∂_k = W` on `U`
  have hEqOn : Set.EqOn
      ⇑(nabla.cov (chartFrameField (I := I) p j) (chartFrameField (I := I) p k)) ⇑W U := by
    intro q hq
    have hqsrc : q ∈ (chartAt H p).source := hUsub hq
    have hev : ∀ m, ⇑(chartFrameField (I := I) p m)
        =ᶠ[nhds q] fun x => chartBasisVecFiber (I := I) p m x := fun m =>
      eventuallyEq_of_mem (hUopen.mem_nhds hq) fun x hx => hUframe m x hx
    show (nabla.cov (chartFrameField (I := I) p j) (chartFrameField (I := I) p k)) q
        = ∑ m, γ m q • chartFrameField (I := I) p m q
    rw [leviCivita_cov_chartFrameField_expansion (I := I) g p j k hqsrc hev]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hUγ m q hq, hUframe m q hq]
  have hEvW : ⇑(nabla.cov (chartFrameField (I := I) p j) (chartFrameField (I := I) p k))
      =ᶠ[nhds p] ⇑W := eventuallyEq_of_mem (hUopen.mem_nhds hpU) hEqOn
  rw [nabla.cov_congr_apply_eventuallyEq_right (chartFrameField (I := I) p i) hEvW,
    nabla.cov_smulSum_apply (chartFrameField (I := I) p i) p Finset.univ γ hγsmooth
      (fun m => chartFrameField (I := I) p m) W hWdef]
  -- rewrite each summand
  have hstep : ∀ m : Fin (Module.finrank ℝ E),
      (chartFrameField (I := I) p i).dir (γ m) p • (chartFrameField (I := I) p m) p
        + γ m p • (nabla.cov (chartFrameField (I := I) p i)
            (chartFrameField (I := I) p m)) p
      = partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m) (extChartAt I p p)
            • chartBasisVecFiber (I := I) p m p
        + chartChristoffel (I := I) g p j k m (extChartAt I p p) •
            ∑ l, chartChristoffel (I := I) g p i m l (extChartAt I p p) •
              chartBasisVecFiber (I := I) p l p := by
    intro m
    have hd : (chartFrameField (I := I) p i).dir (γ m) p
        = partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m) (extChartAt I p p) := by
      show mfderiv I 𝓘(ℝ, ℝ) (γ m) p ((chartFrameField (I := I) p i) p) = _
      rw [chartFrameField_apply_self, (hγev m).mfderiv_eq]
      exact mfderiv_chartChristoffel_eq_partialDeriv (I := I) g p j k m i
        (mem_chart_source H p)
    have hval : γ m p = chartChristoffel (I := I) g p j k m (extChartAt I p p) :=
      (hγev m).self_of_nhds
    have hcov : (nabla.cov (chartFrameField (I := I) p i)
          (chartFrameField (I := I) p m)) p
        = ∑ l, chartChristoffel (I := I) g p i m l (extChartAt I p p) •
            chartBasisVecFiber (I := I) p l p :=
      leviCivita_cov_chartFrameField_expansion (I := I) g p i m (mem_chart_source H p)
        (fun b => chartFrameField_eventuallyEq (I := I) p b)
    rw [hd, hval, hcov, chartFrameField_apply_self]
  rw [Finset.sum_congr rfl fun m _ => hstep m]
  -- reorganize the finite sums
  calc ∑ m, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m)
            (extChartAt I p p) • chartBasisVecFiber (I := I) p m p
          + chartChristoffel (I := I) g p j k m (extChartAt I p p) •
              ∑ l, chartChristoffel (I := I) g p i m l (extChartAt I p p) •
                chartBasisVecFiber (I := I) p l p)
      = ∑ m, partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m)
            (extChartAt I p p) • chartBasisVecFiber (I := I) p m p
        + ∑ m, ∑ l, (chartChristoffel (I := I) g p j k m (extChartAt I p p) *
              chartChristoffel (I := I) g p i m l (extChartAt I p p)) •
            chartBasisVecFiber (I := I) p l p := by
        rw [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun l _ => smul_smul ..
    _ = ∑ l, partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
            (extChartAt I p p) • chartBasisVecFiber (I := I) p l p
        + ∑ l, (∑ s, chartChristoffel (I := I) g p j k s (extChartAt I p p) *
              chartChristoffel (I := I) g p i s l (extChartAt I p p)) •
            chartBasisVecFiber (I := I) p l p := by
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
    _ = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
            (extChartAt I p p)
          + ∑ s, chartChristoffel (I := I) g p j k s (extChartAt I p p) *
              chartChristoffel (I := I) g p i s l (extChartAt I p p))
          • chartBasisVecFiber (I := I) p l p := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => (add_smul ..).symm

/-! ## The curvature coordinate formula -/

/-- **Math.** **The Riemann curvature tensor in chart coordinates** (do Carmo
Ch. 8 §3, eq. (2); the general bridge for `prop:dc-ch8-3-const-curv`). In the
chart frame `∂_i = chartBasisVecFiber p i` at `p`, the intrinsic curvature of the
metric's Levi-Civita connection is
`R(∂_i, ∂_j)∂_k = Σ_l R^l_{ijk} ∂_l` with
`R^l_{ijk} = ∂_jΓ^l_{ik} − ∂_iΓ^l_{jk} + Σ_s(Γ^s_{ik}Γ^l_{js} − Γ^s_{jk}Γ^l_{is})`,
where `Γ^k_{ij} = chartChristoffel g p i j k (extChartAt I p p)` and `∂_j Γ^l_{ik}`
is the chart partial derivative `partialDeriv j (chartChristoffel g p i k l)` at
the chart image of `p`. The sign convention is do Carmo's
(`R(X,Y)Z = ∇_Y∇_X Z − ∇_X∇_Y Z + ∇_{[X,Y]}Z`), matching `Rcoeff`.

Proof (Petersen's expansion adapted to do Carmo's field-valued connection):
`[∂_i, ∂_j] = 0` kills the bracket term; the two double covariant derivatives are
`leviCivita_cov_cov_chartFrameField`, and their difference collapses to the
displayed coefficient. -/
theorem leviCivita_curvature_chartFrame_expansion (g : RiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    (g.leviCivitaConnection.curvature (chartFrameField (I := I) p i)
        (chartFrameField (I := I) p j) (chartFrameField (I := I) p k)) p
      = ∑ l, (partialDeriv (E := E) j (chartChristoffel (I := I) g p i k l)
              (extChartAt I p p)
            - partialDeriv (E := E) i (chartChristoffel (I := I) g p j k l)
              (extChartAt I p p)
            + ∑ s, (chartChristoffel (I := I) g p i k s (extChartAt I p p)
                  * chartChristoffel (I := I) g p j s l (extChartAt I p p)
                - chartChristoffel (I := I) g p j k s (extChartAt I p p)
                  * chartChristoffel (I := I) g p i s l (extChartAt I p p)))
          • chartBasisVecFiber (I := I) p l p := by
  classical
  set nabla := g.leviCivitaConnection with hnabla
  rw [nabla.curvature_apply]
  -- the bracket term vanishes: `[∂_i, ∂_j]|_p = 0`
  have hbrp : bracketField (chartFrameField (I := I) p i) (chartFrameField (I := I) p j) p
      = (0 : SmoothVectorField I M) p := by
    rw [bracketField_apply, SmoothVectorField.zero_apply]
    show VectorField.mlieBracket I (chartFrameField (I := I) p i).toFun
      (chartFrameField (I := I) p j).toFun p = 0
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq
        (chartFrameField_eventuallyEq (I := I) p i)
        (chartFrameField_eventuallyEq (I := I) p j)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) p i j (mem_chart_source H p)
  have hbr0 : (nabla.cov (bracketField (chartFrameField (I := I) p i)
      (chartFrameField (I := I) p j)) (chartFrameField (I := I) p k)) p = 0 := by
    rw [nabla.cov_congr_apply_left (chartFrameField (I := I) p k) hbrp, nabla.cov_zero_left]
  rw [hbr0, add_zero,
    leviCivita_cov_cov_chartFrameField (I := I) g p i j k,
    leviCivita_cov_cov_chartFrameField (I := I) g p j i k,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← sub_smul]
  congr 1
  rw [Finset.sum_sub_distrib]
  ring

end Riemannian

end
