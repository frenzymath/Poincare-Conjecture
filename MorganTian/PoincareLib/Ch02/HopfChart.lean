import PoincareLib.Ch02.LaplacianCoord
import OpenGALib.Riemannian.Connection.ChartChristoffelSmooth
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Morgan–Tian Ch. 2 §2.2 — the chart elliptic operator for the Hopf argument

Blueprint `lem:hopf-strong-maximum` works in a fixed coordinate chart, where
by `lem:laplacian-christoffel-formula` the Laplacian is the second-order
elliptic operator `L u = g^{ac} ∂_a∂_c u + b^k ∂_k u` with
`b^k = −g^{ac}Γ^k_{ac}`, acting on coordinate representations `u = f ∘ φ⁻¹`.
This file packages that operator on the chart target and the facts the Hopf
proof consumes:

* `chartLaplaceB`, `chartLaplaceOp` — the drift coefficients and the operator
  `L` on `E`;
* `laplacianAt_eq_chartLaplaceOp` — `Δf(p) = L(f ∘ φ⁻¹)(φ(p))` at
  chart-source points (a rearrangement of `laplacianAt_eq_chart_formula`);
* `chartLaplaceOp_congr` — `L` only sees the germ of `u` at `y`;
* `chartLaplaceOp_add_smul` — `L(u + ε(w − C)) = L(u) + ε L(w)` for `u`
  smooth on an open set and `w` globally smooth;
* `chartInvGramOnE_continuousOn` / `chartLaplaceB_continuousOn` /
  `chartInvGramOnE_quadratic_pos` — continuity of the coefficients on the
  chart target and pointwise positive definiteness of the leading part;
* `exists_contMDiff_eqOn_open_of_contMDiffOn` — a function smooth on an open
  set `U` agrees with a globally smooth function on a neighbourhood of any
  compact `K ⊆ U` (smooth cutoff), the localization used to feed local data
  into the globally-stated Laplacian lemmas.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2 §2.2
(blueprint `lem:hopf-strong-maximum`).
-/

open scoped ContDiff Manifold Topology Bundle Matrix
open Riemannian Riemannian.Tensor Filter Set

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The chart elliptic operator -/

/-- **Math.** The drift coefficients of the Laplacian in a chart:
`b^k = −g^{ac} Γ^k_{ac}`, as functions on the chart target.
Blueprint: `lem:laplacian-christoffel-formula`. -/
def chartLaplaceB (g : RiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  -∑ a, ∑ c, chartInvGramOnE (I := I) g α a c y
    * chartChristoffel (I := I) g α a c k y

/-- **Math.** The Laplacian read in a chart, as a second-order operator on
functions on the chart target: `L u = g^{ac} ∂_a∂_c u + b^k ∂_k u` with
`b^k = −g^{ac}Γ^k_{ac}`. By `laplacianAt_eq_chartLaplaceOp`, `Δf` at
chart-source points is `L(f ∘ φ⁻¹)` at the coordinate image.
Blueprint: `lem:laplacian-christoffel-formula` / `lem:hopf-strong-maximum`. -/
def chartLaplaceOp (g : RiemannianMetric I M) (α : M) (u : E → ℝ) (y : E) : ℝ :=
  (∑ a, ∑ c, chartInvGramOnE (I := I) g α a c y
      * fderiv ℝ (fun z => fderiv ℝ u z ((Module.finBasis ℝ E) c)) y
          ((Module.finBasis ℝ E) a))
    + ∑ k, chartLaplaceB (I := I) g α k y
        * fderiv ℝ u y ((Module.finBasis ℝ E) k)

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The Laplacian is the chart elliptic operator on coordinate
representations**: at a chart-source point `p`,
`Δf(p) = L(f ∘ φ⁻¹)(φ(p))`. Rearrangement of
`laplacianAt_eq_chart_formula`. Blueprint:
`lem:laplacian-christoffel-formula`. -/
theorem laplacianAt_eq_chartLaplaceOp (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {α p : M}
    (hp : p ∈ (chartAt H α).source) :
    laplacianAt g g.leviCivitaConnection f p
      = chartLaplaceOp (I := I) g α (f ∘ (extChartAt I α).symm)
          (extChartAt I α p) := by
  have hpe : (extChartAt I α).symm (extChartAt I α p) = p :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  rw [laplacianAt_eq_chart_formula g hf hp]
  unfold chartLaplaceOp chartLaplaceB chartInvGramOnE
  rw [hpe]
  unfold Riemannian.partialDeriv
  have expand : ∀ a c : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α p a c
          * (fderiv ℝ (fun y => fderiv ℝ (f ∘ (extChartAt I α).symm) y
                ((Module.finBasis ℝ E) c)) (extChartAt I α p)
                ((Module.finBasis ℝ E) a)
            - ∑ k, chartChristoffel (I := I) g α a c k (extChartAt I α p)
                * fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α p)
                    ((Module.finBasis ℝ E) k))
        = chartInvGramMatrix (I := I) g α p a c
            * fderiv ℝ (fun y => fderiv ℝ (f ∘ (extChartAt I α).symm) y
                ((Module.finBasis ℝ E) c)) (extChartAt I α p)
                ((Module.finBasis ℝ E) a)
          - ∑ k, chartInvGramMatrix (I := I) g α p a c
              * chartChristoffel (I := I) g α a c k (extChartAt I α p)
              * fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α p)
                  ((Module.finBasis ℝ E) k) := by
    intro a c
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [expand, Finset.sum_sub_distrib]
  have swap : ∑ a, ∑ c, ∑ k, chartInvGramMatrix (I := I) g α p a c
        * chartChristoffel (I := I) g α a c k (extChartAt I α p)
        * fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α p)
            ((Module.finBasis ℝ E) k)
      = ∑ k, (∑ a, ∑ c, chartInvGramMatrix (I := I) g α p a c
          * chartChristoffel (I := I) g α a c k (extChartAt I α p))
          * fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α p)
              ((Module.finBasis ℝ E) k) := by
    calc ∑ a, ∑ c, ∑ k, _ * _ * _
        = ∑ a, ∑ k, ∑ c, chartInvGramMatrix (I := I) g α p a c
            * chartChristoffel (I := I) g α a c k (extChartAt I α p)
            * fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α p)
                ((Module.finBasis ℝ E) k) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ c, chartInvGramMatrix (I := I) g α p a c
            * chartChristoffel (I := I) g α a c k (extChartAt I α p)
            * fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α p)
                ((Module.finBasis ℝ E) k) := Finset.sum_comm
      _ = ∑ k, (∑ a, ∑ c, chartInvGramMatrix (I := I) g α p a c
            * chartChristoffel (I := I) g α a c k (extChartAt I α p))
            * fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α p)
                ((Module.finBasis ℝ E) k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
  rw [swap, sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => (neg_mul _ _).symm

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The chart elliptic operator only sees the germ of `u` at `y`.
Blueprint: `lem:hopf-strong-maximum`. -/
theorem chartLaplaceOp_congr (g : RiemannianMetric I M) (α : M)
    {u u' : E → ℝ} {y : E} (h : u =ᶠ[𝓝 y] u') :
    chartLaplaceOp (I := I) g α u y = chartLaplaceOp (I := I) g α u' y := by
  unfold chartLaplaceOp
  have h1 : ∀ k, fderiv ℝ u y ((Module.finBasis ℝ E) k)
      = fderiv ℝ u' y ((Module.finBasis ℝ E) k) := fun k => by
    rw [h.fderiv_eq]
  have h2 : ∀ a c, fderiv ℝ (fun z => fderiv ℝ u z ((Module.finBasis ℝ E) c)) y
        ((Module.finBasis ℝ E) a)
      = fderiv ℝ (fun z => fderiv ℝ u' z ((Module.finBasis ℝ E) c)) y
        ((Module.finBasis ℝ E) a) := fun a c => by
    have hev : (fun z => fderiv ℝ u z ((Module.finBasis ℝ E) c))
        =ᶠ[𝓝 y] fun z => fderiv ℝ u' z ((Module.finBasis ℝ E) c) := by
      filter_upwards [h.eventually_nhds] with z hz
      rw [Filter.EventuallyEq.fderiv_eq hz]
    rw [hev.fderiv_eq]
  simp only [h1, h2]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Linearity of the chart elliptic operator on the sum of a
function smooth on an open set and a global smooth function (shifted by a
constant): `L(u + ε(w − C)) = L(u) + ε L(w)` at points of the open set.
Blueprint: `lem:hopf-strong-maximum` (the barrier perturbation `v = h + εw`). -/
theorem chartLaplaceOp_add_smul (g : RiemannianMetric I M) (α : M)
    {u w : E → ℝ} {T : Set E} (hT : IsOpen T) {y : E} (hy : y ∈ T)
    (hu : ContDiffOn ℝ ∞ u T) (hw : ContDiff ℝ ∞ w) (ε C : ℝ) :
    chartLaplaceOp (I := I) g α (fun z => u z + ε * (w z - C)) y
      = chartLaplaceOp (I := I) g α u y
        + ε * chartLaplaceOp (I := I) g α w y := by
  -- first-order: on `T`, the derivative splits pointwise
  have hd1 : ∀ z ∈ T, ∀ d : E,
      fderiv ℝ (fun z' => u z' + ε * (w z' - C)) z d
        = fderiv ℝ u z d + ε * fderiv ℝ w z d := by
    intro z hz d
    have hud : DifferentiableAt ℝ u z :=
      (hu.contDiffAt (hT.mem_nhds hz)).differentiableAt (by simp)
    have hwd : DifferentiableAt ℝ w z := hw.differentiable (by simp) z
    have hcalc : HasFDerivAt (fun z' => u z' + ε * (w z' - C))
        (fderiv ℝ u z + ε • fderiv ℝ w z) z := by
      have h1 : HasFDerivAt (fun z' => ε * (w z' - C)) (ε • fderiv ℝ w z) z :=
        (hwd.hasFDerivAt.sub_const C).const_mul ε
      exact hud.hasFDerivAt.add h1
    rw [hcalc.fderiv]
    simp
  -- second-order: differentiate the split first derivative
  have hd2 : ∀ a c : Fin (Module.finrank ℝ E),
      fderiv ℝ (fun z => fderiv ℝ (fun z' => u z' + ε * (w z' - C)) z
          ((Module.finBasis ℝ E) c)) y ((Module.finBasis ℝ E) a)
        = fderiv ℝ (fun z => fderiv ℝ u z ((Module.finBasis ℝ E) c)) y
            ((Module.finBasis ℝ E) a)
          + ε * fderiv ℝ (fun z => fderiv ℝ w z ((Module.finBasis ℝ E) c)) y
              ((Module.finBasis ℝ E) a) := by
    intro a c
    have hev : (fun z => fderiv ℝ (fun z' => u z' + ε * (w z' - C)) z
          ((Module.finBasis ℝ E) c))
        =ᶠ[𝓝 y] fun z => fderiv ℝ u z ((Module.finBasis ℝ E) c)
          + ε * fderiv ℝ w z ((Module.finBasis ℝ E) c) := by
      filter_upwards [hT.mem_nhds hy] with z hz
      exact hd1 z hz _
    rw [hev.fderiv_eq]
    -- differentiate the sum
    have hdu : DifferentiableAt ℝ
        (fun z => fderiv ℝ u z ((Module.finBasis ℝ E) c)) y := by
      have : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z ((Module.finBasis ℝ E) c)) T := by
        exact (hu.fderiv_of_isOpen hT (by simp)).clm_apply contDiffOn_const
      exact (this.contDiffAt (hT.mem_nhds hy)).differentiableAt (by simp)
    have hdw : DifferentiableAt ℝ
        (fun z => fderiv ℝ w z ((Module.finBasis ℝ E) c)) y := by
      have : ContDiffAt ℝ ∞ (fun z => fderiv ℝ w z ((Module.finBasis ℝ E) c)) y :=
        ((hw.contDiffAt.fderiv_right (by simp)).clm_apply contDiffAt_const)
      exact this.differentiableAt (by simp)
    rw [fderiv_fun_add hdu (hdw.const_mul ε)]
    simp only [ContinuousLinearMap.add_apply]
    congr 1
    rw [fderiv_const_mul hdw ε]
    simp
  -- first-order at `y` itself
  have hd1y : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ (fun z' => u z' + ε * (w z' - C)) y ((Module.finBasis ℝ E) k)
        = fderiv ℝ u y ((Module.finBasis ℝ E) k)
          + ε * fderiv ℝ w y ((Module.finBasis ℝ E) k) := fun k =>
    hd1 y hy _
  unfold chartLaplaceOp
  simp only [hd2, hd1y, mul_add, Finset.sum_add_distrib]
  have eA : ∑ a, ∑ c, chartInvGramOnE (I := I) g α a c y
        * (ε * fderiv ℝ (fun z => fderiv ℝ w z ((Module.finBasis ℝ E) c)) y
            ((Module.finBasis ℝ E) a))
      = ε * ∑ a, ∑ c, chartInvGramOnE (I := I) g α a c y
          * fderiv ℝ (fun z => fderiv ℝ w z ((Module.finBasis ℝ E) c)) y
              ((Module.finBasis ℝ E) a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have eB : ∑ k, chartLaplaceB (I := I) g α k y
        * (ε * fderiv ℝ w y ((Module.finBasis ℝ E) k))
      = ε * ∑ k, chartLaplaceB (I := I) g α k y
          * fderiv ℝ w y ((Module.finBasis ℝ E) k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [eA, eB]
  ring

/-! ### Continuity and positivity of the coefficients -/

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The leading coefficients `g^{ac}` are continuous on the chart
target. Blueprint: `lem:laplacian-christoffel-formula` (smooth coefficients). -/
theorem chartInvGramOnE_continuousOn (g : RiemannianMetric I M) (α : M)
    (a c : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartInvGramOnE (I := I) g α a c) (extChartAt I α).target :=
  (chartInvGramOnE_contDiffOn (I := I) g α a c).continuousOn

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The drift coefficients `b^k = −g^{ac}Γ^k_{ac}` are continuous on
the chart target (boundaryless model, so the target is open and equals its
interior). Blueprint: `lem:laplacian-christoffel-formula` (smooth
coefficients). -/
theorem chartLaplaceB_continuousOn (g : RiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartLaplaceB (I := I) g α k) (extChartAt I α).target := by
  have hΓ : ∀ a c, ContinuousOn (chartChristoffel (I := I) g α a c k)
      (extChartAt I α).target := by
    intro a c
    have := (chartChristoffel_contDiffOn_interior (I := I) g α a c k).continuousOn
    rwa [(isOpen_extChartAt_target (I := I) α).interior_eq] at this
  unfold chartLaplaceB
  exact (continuousOn_finset_sum _ fun a _ =>
    continuousOn_finset_sum _ fun c _ =>
      (chartInvGramOnE_continuousOn g α a c).mul (hΓ a c)).neg

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Pointwise positive definiteness of the leading part: for `y` in
the chart target and `ξ ≠ 0`, `Σ_{ac} g^{ac}(y) ξ_a ξ_c > 0` — the inverse of
the positive definite Gram matrix is positive definite.
Blueprint: `lem:laplacian-christoffel-formula` (ellipticity). -/
theorem chartInvGramOnE_quadratic_pos (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target)
    {ξ : Fin (Module.finrank ℝ E) → ℝ} (hξ : ξ ≠ 0) :
    0 < ∑ a, ∑ c, chartInvGramOnE (I := I) g α a c y * ξ a * ξ c := by
  have hx : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source] at hsource
    exact hsource
  have hposdef : (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).PosDef :=
    chartGramMatrix_posDef (I := I) g α hx
  have hinv : (chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y)).PosDef := by
    have := hposdef.inv
    rwa [chartInvGramMatrix]
  have hq := hinv.dotProduct_mulVec_pos hξ
  calc (0 : ℝ) < star ξ ⬝ᵥ (chartInvGramMatrix (I := I) g α
        ((extChartAt I α).symm y)) *ᵥ ξ := hq
    _ = ∑ a, ∑ c, chartInvGramOnE (I := I) g α a c y * ξ a * ξ c := by
        simp only [dotProduct, Matrix.mulVec, chartInvGramOnE_def,
          Pi.star_apply, star_trivial]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring

/-! ### Smooth extension agreeing on a neighbourhood of a compact set -/

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** A function smooth on an open set `U` agrees, on a neighbourhood
`W` of any compact `K ⊆ U`, with a globally smooth function: multiply by a
smooth cutoff that is `1` near `K` and supported in `U`. This strengthens the
single-point germ extension `exists_contMDiff_eventuallyEq_of_contMDiffOn` to
a uniform open neighbourhood. Blueprint: `lem:hopf-strong-maximum`
(localization). -/
theorem exists_contMDiff_eqOn_open_of_contMDiffOn
    {U : Set M} (hU : IsOpen U) {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ∃ f' : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f' ∧
      ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ EqOn f' f W := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- interpose `K ⊆ W ⊆ closure W ⊆ V ⊆ closure V ⊆ U`
  obtain ⟨V, hVopen, hKV, hVU, -⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hWopen, hKW, hWV, -⟩ :=
    exists_open_between_and_isCompact_closure hK hVopen hKV
  -- smooth cutoff: `0` exactly off `V`, `1` on `closure W`
  obtain ⟨χ, hχ, -, hχ0, hχ1⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (I := I) (n := (⊤ : ℕ∞))
      (isClosed_compl_iff.mpr hVopen) isClosed_closure
      (disjoint_compl_left_iff_subset.mpr hWV)
  have hχsupp : Function.support χ = V := by
    ext x
    simp only [Function.mem_support, ne_eq, ← hχ0 x, mem_compl_iff, not_not]
  have hWU : W ⊆ U := fun x hx =>
    hVU (subset_closure (hWV (subset_closure hx)))
  refine ⟨fun x => χ x * f x, ?_, W, hWopen, hKW, hWU, ?_⟩
  · -- smoothness: the product is supported in `closure V ⊆ U`, where both
    -- factors are smooth
    refine contMDiff_of_tsupport fun x hx => ?_
    have hxU : x ∈ U := by
      have h1 : tsupport (fun x => χ x * f x) ⊆ tsupport χ :=
        tsupport_mul_subset_left
      have h2 : tsupport χ ⊆ closure V := by
        rw [tsupport, hχsupp]
      exact hVU (h2 (h1 hx))
    exact (hχ.contMDiffAt).mul (hf.contMDiffAt (hU.mem_nhds hxU))
  · intro x hx
    have h1 : χ x = 1 := (hχ1 x).mp (subset_closure hx)
    simp [h1]

end PoincareLib

end
