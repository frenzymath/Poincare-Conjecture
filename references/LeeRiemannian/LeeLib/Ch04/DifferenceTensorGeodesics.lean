/-
Chapter 4, "Connections", Problem 4-9(b): two connections determine the same
geodesics iff their difference tensor is *antisymmetric*.

For two connections `∇⁰, ∇¹` in `TM` with difference tensor
`D(X, Y) = ∇¹_X Y − ∇⁰_X Y` (Proposition 4.13, `differenceTensor`), Lee's
Problem 4-9(b) is the counterpart of 4-9(a) (`sameTorsion_iff_differenceTensor_symm`):

  `∇⁰` and `∇¹` determine the same geodesics  ⟺  `D` is antisymmetric,
  `D(X, Y) = −D(Y, X)`.

The geodesic of a connection is read in a chart through the acceleration
`chartAcceleration cov e b u c = ü + Γ(u̇, u̇)(c)` of `LeeLib.Ch04.Geodesic`.
Two connections produce the *same acceleration on every curve* iff their chart
Christoffel contractions agree on the diagonal `Γ¹(v, v) = Γ⁰(v, v)`, and — since
`Γ¹ − Γ⁰` is bilinear — that diagonal agreement is exactly antisymmetry of the
difference `Γ¹ − Γ⁰` (the polarization identity
`biadditive_diag_eq_zero_iff_antisymm`).  This is Problem 4-9(b) read at the
level of the geodesic equation; the equivalence with the same *solution set*
is the standard geodesic existence/uniqueness theory (the chapter's spray
development), so the acceleration-operator form is the one proved here in full.

The final step bridges the chart Christoffel difference `Γ¹ − Γ⁰` to the abstract
`differenceTensor ∇¹ ∇⁰` (`chartGamma_sub_eq_differenceTensor`), so the statement
is phrased in Lee's difference tensor, matching Problem 4-9(a).
-/
import LeeLib.Ch04.Geodesic
import LeeLib.Ch04.DifferenceTensor

namespace LeeLib.Ch04

open Bundle Module
open scoped Manifold ContDiff Topology
open Set

set_option linter.unusedSectionVars false

noncomputable section

/-- **Polarization identity.**  A biadditive map `F : V × V → G` into a real
vector space vanishes on the diagonal (`F v v = 0` for all `v`) iff it is
antisymmetric (`F v w = −F w v`).  This is the algebraic core of Problem 4-9(b):
"the symmetric part vanishes" ⟺ "the map is antisymmetric". -/
theorem biadditive_diag_eq_zero_iff_antisymm
    {V G : Type*} [AddCommGroup V] [AddCommGroup G] [Module ℝ G]
    (F : V → V → G)
    (hl : ∀ v v' w, F (v + v') w = F v w + F v' w)
    (hr : ∀ v w w', F v (w + w') = F v w + F v w') :
    (∀ v, F v v = 0) ↔ ∀ v w, F v w = - F w v := by
  constructor
  · intro h v w
    have hvw := h (v + w)
    rw [hl, hr, hr, h v, h w] at hvw
    -- hvw : 0 + F v w + (F w v + 0) = 0
    have hsum : F v w + F w v = 0 := by
      rw [zero_add, add_zero] at hvw; exact hvw
    exact eq_neg_of_add_eq_zero_left hsum
  · intro h v
    have hself : F v v = - F v v := h v v
    have hsum : F v v + F v v = 0 := by
      nth_rewrite 1 [hself]; exact neg_add_cancel _
    have h2 : (2 : ℝ) • F v v = 0 := by rw [two_smul]; exact hsum
    rcases smul_eq_zero.mp h2 with h0 | h0
    · norm_num at h0
    · exact h0

section Chart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]
  {e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)}
  [MemTrivializationAtlas e] {b : Basis ι ℝ E}

/-- The chart Christoffel *difference* `Γ¹(v, w)(y) − Γ⁰(v, w)(y)` of two
connections, at a fixed base point `y`, is biadditive in each of its two vector
slots (immediate from the bilinearity of each `chartGamma`). -/
theorem chartGamma_sub_add_left (cov cov' : Connection I E (TangentSpace I : M → Type _))
    (v v' w : E) (y : M) :
    chartGamma cov e b (v + v') w y - chartGamma cov' e b (v + v') w y
      = (chartGamma cov e b v w y - chartGamma cov' e b v w y)
        + (chartGamma cov e b v' w y - chartGamma cov' e b v' w y) := by
  rw [chartGamma_add_left, chartGamma_add_left]; abel

theorem chartGamma_sub_add_right (cov cov' : Connection I E (TangentSpace I : M → Type _))
    (v w w' : E) (y : M) :
    chartGamma cov e b v (w + w') y - chartGamma cov' e b v (w + w') y
      = (chartGamma cov e b v w y - chartGamma cov' e b v w y)
        + (chartGamma cov e b v w' y - chartGamma cov' e b v w' y) := by
  rw [chartGamma_add_right, chartGamma_add_right]; abel

/-- **The chart Christoffel difference is antisymmetric iff it vanishes on the
diagonal.**  Polarization applied to `F v w = Γ¹(v, w)(y) − Γ⁰(v, w)(y)`: the two
connections have equal Christoffel contractions on the diagonal at `y`
(`Γ¹(v, v)(y) = Γ⁰(v, v)(y)` for all `v`) iff the difference `Γ¹ − Γ⁰` is
antisymmetric at `y`. -/
theorem chartGamma_diag_eq_iff_diff_antisymm
    (cov cov' : Connection I E (TangentSpace I : M → Type _)) (y : M) :
    (∀ v : E, chartGamma cov e b v v y = chartGamma cov' e b v v y)
      ↔ ∀ v w : E, chartGamma cov e b v w y - chartGamma cov' e b v w y
          = - (chartGamma cov e b w v y - chartGamma cov' e b w v y) := by
  have hiff := biadditive_diag_eq_zero_iff_antisymm
    (F := fun v w => chartGamma cov e b v w y - chartGamma cov' e b v w y)
    (fun v v' w => chartGamma_sub_add_left cov cov' v v' w y)
    (fun v w w' => chartGamma_sub_add_right cov cov' v w w' y)
  simp only [sub_eq_zero] at hiff
  exact hiff

/-- The acceleration of the **straight-line chart curve** `u(s) = s • v` over the
constant base curve `c ≡ y` is exactly the diagonal Christoffel contraction
`Γ(v, v)(y)`: the second derivative `ü` vanishes and `u̇ ≡ v`, so
`chartAcceleration = ü + Γ(u̇, u̇)(c) = Γ(v, v)(y)`.  These test curves realise
every `(v, y)` as an acceleration, which is what makes the acceleration operator
determine the diagonal of `Γ`. -/
theorem chartAcceleration_line (cov : Connection I E (TangentSpace I : M → Type _))
    (v : E) (y : M) (t : ℝ) :
    chartAcceleration cov e b (fun s => s • v) (fun _ => y) t = chartGamma cov e b v v y := by
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => r • v) v s := fun s => by
    simpa using (hasDerivAt_id s).smul_const v
  have hderiv : deriv (fun r : ℝ => r • v) = fun _ => v := funext fun s => (hd s).deriv
  rw [chartAcceleration_def, hderiv]
  simp

/-- **Two connections produce the same acceleration on every chart curve iff their
Christoffel contractions agree on the diagonal.**  The forward direction tests the
acceleration operator on the straight-line curves `chartAcceleration_line`; the
backward direction is immediate from the acceleration formula `ü + Γ(u̇, u̇)(c)`
(the `ü` terms coincide, and the `Γ`-diagonal terms agree by hypothesis). -/
theorem sameChartAcceleration_iff_chartGamma_diag_eq
    (cov cov' : Connection I E (TangentSpace I : M → Type _)) :
    (∀ (u : ℝ → E) (c : ℝ → M) (t : ℝ),
        chartAcceleration cov e b u c t = chartAcceleration cov' e b u c t)
      ↔ ∀ (v : E) (y : M), chartGamma cov e b v v y = chartGamma cov' e b v v y := by
  constructor
  · intro h v y
    have h0 := h (fun s => s • v) (fun _ => y) 0
    rwa [chartAcceleration_line, chartAcceleration_line] at h0
  · intro h u c t
    rw [chartAcceleration_def, chartAcceleration_def, h (deriv u t) (c t)]

/-- **Lee's Problem 4-9(b), chart-Christoffel form.**  Two connections `∇⁰, ∇¹`
induce the same acceleration on every curve (equivalently, the same geodesic
equation in every chart) iff the difference `Γ¹ − Γ⁰` of their chart Christoffel
contractions is antisymmetric — the coordinate form of "the difference tensor `D`
is antisymmetric".  (The bridge to the abstract `differenceTensor` is
`chartGamma_diag_eq_iff_diff_antisymm` composed with the coefficient identity;
the equivalence with the same geodesic *solution set* is the standard geodesic
existence/uniqueness theory.) -/
theorem sameChartAcceleration_iff_chartGamma_diff_antisymm
    (cov cov' : Connection I E (TangentSpace I : M → Type _)) :
    (∀ (u : ℝ → E) (c : ℝ → M) (t : ℝ),
        chartAcceleration cov e b u c t = chartAcceleration cov' e b u c t)
      ↔ ∀ (v w : E) (y : M),
          chartGamma cov e b v w y - chartGamma cov' e b v w y
            = - (chartGamma cov e b w v y - chartGamma cov' e b w v y) := by
  rw [sameChartAcceleration_iff_chartGamma_diag_eq]
  constructor
  · intro h v w y
    exact (chartGamma_diag_eq_iff_diff_antisymm cov cov' y).mp (fun v' => h v' y) v w
  · intro h v y
    exact (chartGamma_diag_eq_iff_diff_antisymm cov cov' y).mpr (fun v' w => h v' w y) v

/-- **Antisymmetric difference tensor ⟹ same geodesics** (Lee, Problem 4-9(b), the
elementary direction).  If the chart Christoffel difference is antisymmetric, the
two connections induce equal accelerations on every curve, hence exactly the same
chart geodesics: `γ` is a `∇⁰`-geodesic iff it is a `∇¹`-geodesic. -/
theorem isGeodesicInChart_congr_of_diff_antisymm
    (cov cov' : Connection I E (TangentSpace I : M → Type _))
    (h : ∀ (v w : E) (y : M),
        chartGamma cov e b v w y - chartGamma cov' e b v w y
          = - (chartGamma cov e b w v y - chartGamma cov' e b w v y))
    (u : ℝ → E) (c : ℝ → M) :
    IsGeodesicInChart cov e b u c ↔ IsGeodesicInChart cov' e b u c := by
  have hacc := (sameChartAcceleration_iff_chartGamma_diff_antisymm cov cov').mpr h
  constructor
  · intro hg t; rw [← hacc u c t]; exact hg t
  · intro hg t; rw [hacc u c t]; exact hg t

/-- **The abstract difference tensor's chart components are the Christoffel
coefficient differences.**  Evaluated on the chart frame vectors `∂_i, ∂_j`
(direction `∂_i`, section `∂_j`), the difference tensor `D = ∇ − ∇'`
(`differenceTensor`, Proposition 4.13) reads
`D(∂_j, ∂_i)(y) = ∑_k (Γ^k_{ij}(y) − Γ'^k_{ij}(y)) ∂_k(y)` on the chart domain,
where `Γ^k_{ij} = chartConnectionCoeff`.  This is the coordinate identity linking
Lee's abstract difference tensor to the chart Christoffel data used in the
geodesic form of Problem 4-9(b); it is the difference-tensor analogue of the
connection's own frame identity
`covariantDeriv_chartFrame_eq_sum_chartConnectionCoeff` (Lee, equation (4.8)). -/
theorem differenceTensor_chartFrame_eq_sum
    (cov cov' : Connection I E (TangentSpace I : M → Type _)) (i j : ι) {y : M}
    (hy : y ∈ e.baseSet) :
    differenceTensor cov cov' y (e.localFrame b j y) (e.localFrame b i y)
      = ∑ k, (chartConnectionCoeff cov e b i j k y - chartConnectionCoeff cov' e b i j k y)
          • e.localFrame b k y := by
  have hj : MDiffAt (T% (e.localFrame b j)) y :=
    ((chartFrame_isLocalFrameOn e b).contMDiffAt e.open_baseSet hy j).mdifferentiableAt (by norm_num)
  rw [differenceTensor_apply cov cov' (e.localFrame b i) hj,
    covariantDeriv_chartFrame_eq_sum_chartConnectionCoeff cov i j hy,
    covariantDeriv_chartFrame_eq_sum_chartConnectionCoeff cov' i j hy,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (sub_smul _ _ _).symm

/-- Coordinate extraction for a finite basis: `∑ c_k • β_k = ∑ d_k • β_k` forces
`c = d`, via injectivity of `β.equivFun.symm`. -/
theorem basis_coeff_ext {W : Type*} [AddCommGroup W] [Module ℝ W]
    (β : Basis ι ℝ W) {c d : ι → ℝ}
    (h : ∑ k, c k • β k = ∑ k, d k • β k) : c = d := by
  apply β.equivFun.symm.injective
  simpa only [Basis.equivFun_symm_apply] using h

/-- `chartGamma` evaluated on the basis directions `(b i, b j)` selects the single
Christoffel contraction `Γ(b_i, b_j)(y) = ∑_k Γ^k_{ij}(y) • b_k`. -/
theorem chartGamma_basis (cov : Connection I E (TangentSpace I : M → Type _))
    (i j : ι) (y : M) :
    chartGamma cov e b (b i) (b j) y
      = ∑ k, chartConnectionCoeff cov e b i j k y • b k := by
  classical
  simp only [chartGamma_def, Basis.repr_self_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp [mul_ite, Finset.sum_ite_eq]

/-- Combine the two Christoffel sums for `chartGamma cov (b i) (b j) − chartGamma cov' (b i) (b j)`
into a single sum over the coefficient differences. -/
private theorem chartGamma_basis_sub (cov cov' : Connection I E (TangentSpace I : M → Type _))
    (i j : ι) (y : M) :
    chartGamma cov e b (b i) (b j) y - chartGamma cov' e b (b i) (b j) y
      = ∑ k, (chartConnectionCoeff cov e b i j k y - chartConnectionCoeff cov' e b i j k y) • b k := by
  rw [chartGamma_basis, chartGamma_basis, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (sub_smul _ _ _).symm

/-- **`chartGamma`-difference antisymmetry ⟺ Christoffel-coefficient antisymmetry.**
The difference `Γ¹ − Γ⁰` of the chart Christoffel contractions is antisymmetric at
`y` iff the coefficient differences `Γ¹^k_{ij} − Γ⁰^k_{ij}` are antisymmetric in
`(i, j)` (the coordinate form of "the difference tensor `D` is antisymmetric"). -/
theorem chartGamma_diff_antisymm_iff_coeff
    (cov cov' : Connection I E (TangentSpace I : M → Type _)) (y : M) :
    (∀ v w : E, chartGamma cov e b v w y - chartGamma cov' e b v w y
        = - (chartGamma cov e b w v y - chartGamma cov' e b w v y))
      ↔ ∀ i j k : ι,
          chartConnectionCoeff cov e b i j k y - chartConnectionCoeff cov' e b i j k y
            = - (chartConnectionCoeff cov e b j i k y - chartConnectionCoeff cov' e b j i k y) := by
  classical
  constructor
  · intro h i j k
    have hij := h (b i) (b j)
    rw [chartGamma_basis_sub, chartGamma_basis_sub, ← Finset.sum_neg_distrib] at hij
    have hcoe := basis_coeff_ext b (c := fun k =>
        chartConnectionCoeff cov e b i j k y - chartConnectionCoeff cov' e b i j k y)
      (d := fun k =>
        -(chartConnectionCoeff cov e b j i k y - chartConnectionCoeff cov' e b j i k y))
      (by simpa only [neg_smul] using hij)
    exact congrFun hcoe k
  · intro h v w
    -- Reduce the vector identity to the per-`k` scalar antisymmetry `hscalar`.
    have hscalar : ∀ k : ι,
        (∑ i, ∑ j, chartConnectionCoeff cov e b i j k y * b.repr v i * b.repr w j)
          - (∑ i, ∑ j, chartConnectionCoeff cov' e b i j k y * b.repr v i * b.repr w j)
        = -((∑ i, ∑ j, chartConnectionCoeff cov e b i j k y * b.repr w i * b.repr v j)
          - (∑ i, ∑ j, chartConnectionCoeff cov' e b i j k y * b.repr w i * b.repr v j)) := by
      intro k
      set Δ : ι → ι → ℝ :=
        fun i j => chartConnectionCoeff cov e b i j k y - chartConnectionCoeff cov' e b i j k y
        with hΔ
      have step1 :
          (∑ i, ∑ j, chartConnectionCoeff cov e b i j k y * b.repr v i * b.repr w j)
            - (∑ i, ∑ j, chartConnectionCoeff cov' e b i j k y * b.repr v i * b.repr w j)
          = ∑ i, ∑ j, Δ i j * b.repr v i * b.repr w j := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hΔ]; ring
      have step2 :
          (∑ i, ∑ j, chartConnectionCoeff cov e b i j k y * b.repr w i * b.repr v j)
            - (∑ i, ∑ j, chartConnectionCoeff cov' e b i j k y * b.repr w i * b.repr v j)
          = ∑ i, ∑ j, Δ i j * b.repr w i * b.repr v j := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hΔ]; ring
      have hswap : (∑ i, ∑ j, Δ i j * b.repr w i * b.repr v j)
          = ∑ i, ∑ j, Δ j i * b.repr w j * b.repr v i := Finset.sum_comm
      have hanti : (∑ i, ∑ j, Δ j i * b.repr w j * b.repr v i)
          = -(∑ i, ∑ j, Δ i j * b.repr v i * b.repr w j) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hji : Δ j i = -(Δ i j) := by rw [hΔ]; exact h j i k
        rw [hji]; ring
      rw [step1, step2, hswap, hanti, neg_neg]
    -- Lift `hscalar` to the vector identity.
    simp only [chartGamma_def]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul, ← sub_smul, ← neg_smul]
    congr 1
    exact hscalar k

/-- **Abstract difference tensor antisymmetric on the chart frame ⟺ Christoffel
coefficients antisymmetric.**  On the chart domain, the difference tensor `D`
(`differenceTensor`) is antisymmetric on the frame vectors,
`D(∂_j, ∂_i)(y) = −D(∂_i, ∂_j)(y)`, iff the coefficient differences
`Γ¹^k_{ij} − Γ⁰^k_{ij}` are antisymmetric in `(i, j)` — via the frame identity
`differenceTensor_chartFrame_eq_sum` and coordinate extraction in the frame
basis at `y`. -/
theorem differenceTensor_frame_antisymm_iff_coeff
    (cov cov' : Connection I E (TangentSpace I : M → Type _)) {y : M} (hy : y ∈ e.baseSet) :
    (∀ i j : ι, differenceTensor cov cov' y (e.localFrame b j y) (e.localFrame b i y)
        = - differenceTensor cov cov' y (e.localFrame b i y) (e.localFrame b j y))
      ↔ ∀ i j k : ι,
          chartConnectionCoeff cov e b i j k y - chartConnectionCoeff cov' e b i j k y
            = - (chartConnectionCoeff cov e b j i k y - chartConnectionCoeff cov' e b j i k y) := by
  classical
  have hfr := chartFrame_isLocalFrameOn (I := I) e b
  have hcoe : ∀ k, hfr.toBasisAt hy k = e.localFrame b k y := fun k => hfr.toBasisAt_coe hy k
  constructor
  · intro h i j
    have hij := h i j
    rw [differenceTensor_chartFrame_eq_sum cov cov' i j hy,
        differenceTensor_chartFrame_eq_sum cov cov' j i hy, ← Finset.sum_neg_distrib] at hij
    have hfun := basis_coeff_ext (hfr.toBasisAt hy)
      (c := fun k => chartConnectionCoeff cov e b i j k y - chartConnectionCoeff cov' e b i j k y)
      (d := fun k => -(chartConnectionCoeff cov e b j i k y - chartConnectionCoeff cov' e b j i k y))
      (by simp only [hcoe, neg_smul]; exact hij)
    exact fun k => congrFun hfun k
  · intro h i j
    rw [differenceTensor_chartFrame_eq_sum cov cov' i j hy,
        differenceTensor_chartFrame_eq_sum cov cov' j i hy, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_smul]
    congr 1
    exact h i j k

/-- **Lee's Problem 4-9(b), the abstract–chart bridge.**  At a point `y` of the chart
domain, the chart Christoffel difference `Γ¹ − Γ⁰` is antisymmetric — equivalently
(`sameChartAcceleration_iff_chartGamma_diff_antisymm`) the two connections induce the
same acceleration on every chart curve — iff Lee's abstract difference tensor
`D = ∇¹ − ∇⁰` (`differenceTensor`, Proposition 4.13) is antisymmetric on the chart
frame, `D(∂_j, ∂_i)(y) = −D(∂_i, ∂_j)(y)`.  This is the counterpart of Problem 4-9(a)
(`sameTorsion_iff_differenceTensor_symm`), phrased in the same abstract difference
tensor, for the geodesic condition instead of the torsion. -/
theorem chartGamma_diff_antisymm_iff_differenceTensor_frame_antisymm
    (cov cov' : Connection I E (TangentSpace I : M → Type _)) {y : M} (hy : y ∈ e.baseSet) :
    (∀ v w : E, chartGamma cov e b v w y - chartGamma cov' e b v w y
        = - (chartGamma cov e b w v y - chartGamma cov' e b w v y))
      ↔ ∀ i j : ι, differenceTensor cov cov' y (e.localFrame b j y) (e.localFrame b i y)
          = - differenceTensor cov cov' y (e.localFrame b i y) (e.localFrame b j y) :=
  (chartGamma_diff_antisymm_iff_coeff cov cov' y).trans
    (differenceTensor_frame_antisymm_iff_coeff cov cov' hy).symm

end Chart

end

end LeeLib.Ch04
