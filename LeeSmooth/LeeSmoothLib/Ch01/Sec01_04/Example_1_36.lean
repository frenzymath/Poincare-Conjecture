import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic search note: no `lean_leansearch` tool was available in this environment.
-- The statement surface below was checked against mathlib's `LinearMap.graph`,
-- `Submodule.prodEquivOfIsCompl`, `Submodule.projectionOnto`, and
-- `Mathlib/RingTheory/Grassmannian.lean`; the latter uses the algebraic-geometry quotient
-- convention rather than Lee's `k`-plane convention, so this file keeps the source-faithful
-- `Submodule`-based owner.

open scoped BigOperators

universe u

/-- The Grassmannian of `k`-planes in a real vector space `V`, in the sense of Lee's text: its
points are the `k`-dimensional linear subspaces of `V`. -/
def grassmannian (V : Type u) [AddCommGroup V] [Module ℝ V] (k : ℕ) :=
  { S : Submodule ℝ V // Module.finrank ℝ S = k }

namespace grassmannian

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {k : ℕ}
variable {P Q P' Q' : Submodule ℝ V}

/-- For a fixed complementary subspace `Q`, the corresponding Grassmannian chart domain consists
of the `k`-planes meeting `Q` trivially. -/
def chart_domain (Q : Submodule ℝ V) : Set (grassmannian V k) :=
  { S | Disjoint S.1 Q }

/-- The graph of a linear map `X : P → Q`, transported across a decomposition `V = P ⊕ Q`, has the
same dimension as `P`. -/
theorem graph_finrank
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) (X : P →ₗ[ℝ] Q) :
    Module.finrank ℝ
        ((LinearMap.graph X).map (P.prodEquivOfIsCompl Q hPQ).toLinearMap) = k := by
  -- Transport the graph across the complementary decomposition and identify it as a range.
  rw [LinearEquiv.finrank_map_eq]
  rw [LinearMap.graph_eq_range_prod]
  refine (LinearMap.finrank_range_of_inj ?_).trans hP
  -- Injectivity is read off from the first coordinate.
  intro x y hxy
  exact congrArg Prod.fst hxy

/-- The graph of a linear map `X : P → Q`, viewed as a `k`-plane in `V` through a complementary
decomposition `V = P ⊕ Q`. -/
def graph (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) (X : P →ₗ[ℝ] Q) :
    grassmannian V k :=
  ⟨(LinearMap.graph X).map (P.prodEquivOfIsCompl Q hPQ).toLinearMap,
    graph_finrank hPQ hP X⟩

/-- The graph of a linear map `X : P → Q` meets the complementary subspace `Q` trivially, so it
lies in the chart domain determined by `Q`. -/
theorem graph_mem_chart_domain
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) (X : P →ₗ[ℝ] Q) :
    graph hPQ hP X ∈ chart_domain Q := by
  -- Move an intersection point back to `P × Q` and inspect its coordinates.
  change Disjoint (graph hPQ hP X).1 Q
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  rcases hx with ⟨hxGraph, hxQ⟩
  rcases hxGraph with ⟨y, hy, rfl⟩
  have hy1 : y.1 = 0 := by
    have : ((P.prodEquivOfIsCompl Q hPQ).symm ((P.prodEquivOfIsCompl Q hPQ) y)).1 = 0 :=
      (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero (p := P) (q := Q) hPQ).2 hxQ
    simpa using this
  have hy2 : y.2 = 0 := by
    simpa [hy1] using hy
  -- A graph point with both coordinates zero is the zero vector in `V`.
  simp [hy1, hy2]

/-- If `S` is a `k`-plane whose intersection with `Q` is trivial, then projection onto `P` along
`Q` restricts to a linear isomorphism from `S` to `P`. -/
theorem chart_projection_bijective
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) :
    Function.Bijective (((P.projectionOnto Q hPQ).comp S.1.subtype)) := by
  let f : S.1 →ₗ[ℝ] P := (P.projectionOnto Q hPQ).comp S.1.subtype
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hdiffS : ((x : V) - (y : V)) ∈ S.1 := S.1.sub_mem x.2 y.2
    have hdiffQ : ((x : V) - (y : V)) ∈ Q := by
      rw [← Submodule.projectionOnto_apply_eq_zero_iff hPQ]
      simpa [f, LinearMap.map_sub] using sub_eq_zero.mpr hxy
    have hdiff0 : (x : V) - (y : V) = 0 := by
      have hmem : ((x : V) - (y : V)) ∈ (S.1 ⊓ Q : Submodule ℝ V) := ⟨hdiffS, hdiffQ⟩
      have : ((x : V) - (y : V)) ∈ (⊥ : Submodule ℝ V) := by
        rw [hS.eq_bot] at hmem
        exact hmem
      simpa using this
    exact sub_eq_zero.mp hdiff0
  have hdim : Module.finrank ℝ S.1 = Module.finrank ℝ P := by
    calc
      Module.finrank ℝ S.1 = k := S.2
      _ = Module.finrank ℝ P := hP.symm
  -- Equal dimensions promote injectivity of the restricted projection to surjectivity.
  exact ⟨hf_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf_inj⟩

/-- The inverse to the restricted projection `S → P` for a `k`-plane `S` in the chart domain of
`Q`. -/
noncomputable def chart_linear_equiv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) :
    S.1 ≃ₗ[ℝ] P :=
  LinearEquiv.ofBijective (((P.projectionOnto Q hPQ).comp S.1.subtype))
    (chart_projection_bijective hPQ hP S hS)

/-- The coordinate of a `k`-plane `S` in the chart determined by `V = P ⊕ Q`, obtained by writing
`S` as the graph of a linear map `P → Q`. -/
noncomputable def chart_fun
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) :
    P →ₗ[ℝ] Q :=
  (Q.projectionOnto P hPQ.symm).comp
    (S.1.subtype.comp (chart_linear_equiv hPQ hP S hS).symm.toLinearMap)

/-- Helper for Example 1.36: the inverse restricted projection reconstructs a vector in `S` from
its `P`-coordinate together with its chart value in `Q`. -/
theorem chartLinearEquivSymm_apply_eq_chartPoint
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) (p : P) :
    (((chart_linear_equiv hPQ hP S hS).symm p : S.1) : V) =
      (P.prodEquivOfIsCompl Q hPQ) (p, chart_fun hPQ hP S hS p) := by
  let v : V := (((chart_linear_equiv hPQ hP S hS).symm p : S.1) : V)
  have hv1 : ((P.prodEquivOfIsCompl Q hPQ).symm v).1 = p := by
    -- The `P`-coordinate is exactly the restricted projection defining `chart_linear_equiv`.
    change (P.projectionOnto Q hPQ) v = p
    change (P.projectionOnto Q hPQ) ((((chart_linear_equiv hPQ hP S hS).symm p : S.1) : V)) = p
    exact (chart_linear_equiv hPQ hP S hS).apply_symm_apply p
  have hv2 : ((P.prodEquivOfIsCompl Q hPQ).symm v).2 = chart_fun hPQ hP S hS p := by
    -- The `Q`-coordinate is the chart value by definition.
    simp [v, chart_fun, LinearMap.comp_apply, Submodule.prodEquivOfIsCompl_symm_apply]
  -- Reassemble the vector from its two complementary coordinates.
  calc
    v = (P.prodEquivOfIsCompl Q hPQ) ((P.prodEquivOfIsCompl Q hPQ).symm v) := by
      simpa using ((P.prodEquivOfIsCompl Q hPQ).apply_symm_apply v).symm
    _ = (P.prodEquivOfIsCompl Q hPQ) (p, chart_fun hPQ hP S hS p) := by
      exact congrArg (P.prodEquivOfIsCompl Q hPQ) (Prod.ext hv1 hv2)

/-- Helper for Example 1.36: on an actual graph, the inverse restricted projection sends `p : P`
back to the graph point `(p, X p)`. -/
theorem chartLinearEquivSymm_apply_eq_graphPoint
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) (X : P →ₗ[ℝ] Q) (p : P) :
    (((chart_linear_equiv hPQ hP (graph hPQ hP X)
          (graph_mem_chart_domain hPQ hP X)).symm p :
        (graph hPQ hP X).1) : V) =
      (P.prodEquivOfIsCompl Q hPQ) (p, X p) := by
  let y0 : (graph hPQ hP X).1 :=
    (chart_linear_equiv hPQ hP (graph hPQ hP X)
      (graph_mem_chart_domain hPQ hP X)).symm p
  have hy0 :
      ((y0 : (graph hPQ hP X).1) : V) ∈
        ((LinearMap.graph X).map (P.prodEquivOfIsCompl Q hPQ).toLinearMap) := by
    change ((y0 : (graph hPQ hP X).1) : V) ∈ (graph hPQ hP X).1
    exact y0.2
  -- Unpack the mapped-graph membership of the inverse image.
  rcases hy0 with ⟨y, hy, hyEq⟩
  have hy1 : y.1 = p := by
    have hproj :
        (P.projectionOnto Q hPQ) (((y0 : (graph hPQ hP X).1) : V)) = p := by
      change (P.projectionOnto Q hPQ) ((((chart_linear_equiv hPQ hP (graph hPQ hP X)
        (graph_mem_chart_domain hPQ hP X)).symm p : (graph hPQ hP X).1) : V)) = p
      exact (chart_linear_equiv hPQ hP (graph hPQ hP X)
        (graph_mem_chart_domain hPQ hP X)).apply_symm_apply p
    have hy1' : (P.projectionOnto Q hPQ) ((P.prodEquivOfIsCompl Q hPQ) y) = p := by
      rw [← hyEq] at hproj
      exact hproj
    have hy1'' : (P.projectionOnto Q hPQ) ((P.prodEquivOfIsCompl Q hPQ) y) = y.1 := by
      change (P.projectionOnto Q hPQ) ((y.1 : V) + (y.2 : V)) = y.1
      simp
    exact hy1''.symm.trans hy1'
  have hy2 : y.2 = X p := by
    simpa [hy1] using hy
  have hyPair : y = (p, X p) := by
    ext <;> simp [hy1, hy2]
  -- The point in the mapped graph is therefore the expected graph vector.
  simpa [y0, hyPair] using hyEq.symm

/-- Helper for Example 1.36: applying the graph construction to the chart coordinate of `S`
recovers the original `k`-plane. -/
theorem graph_chartFun_eq
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k)
    (S : grassmannian V k) (hS : S ∈ chart_domain Q) :
    graph hPQ hP (chart_fun hPQ hP S hS) = S := by
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyGraph : y.2 = chart_fun hPQ hP S hS y.1 := by
      simpa using hy
    have hyPair : y = (y.1, chart_fun hPQ hP S hS y.1) := by
      ext
      · rfl
      · simpa using congrArg (fun z : Q => (z : V)) hyGraph
    -- Rewrite the graph point using the inverse of the restricted projection.
    have hpoint := chartLinearEquivSymm_apply_eq_chartPoint hPQ hP S hS y.1
    rw [← hyPair] at hpoint
    simpa [hpoint] using (((chart_linear_equiv hPQ hP S hS).symm y.1).2)
  · intro hx
    let p : P := chart_linear_equiv hPQ hP S hS ⟨x, hx⟩
    -- Write `x` in graph coordinates using its `P`-component.
    have hxEq : x = (P.prodEquivOfIsCompl Q hPQ) (p, chart_fun hPQ hP S hS p) := by
      have hback : (((chart_linear_equiv hPQ hP S hS).symm p : S.1) : V) = x := by
        simpa [p] using
          congrArg (fun z : S.1 => (z : V))
            ((chart_linear_equiv hPQ hP S hS).symm_apply_apply ⟨x, hx⟩)
      exact hback.symm.trans (chartLinearEquivSymm_apply_eq_chartPoint hPQ hP S hS p)
    change x ∈ ((LinearMap.graph (chart_fun hPQ hP S hS)).map
      (P.prodEquivOfIsCompl Q hPQ).toLinearMap)
    refine ⟨(p, chart_fun hPQ hP S hS p), ?_, hxEq.symm⟩
    simp

/-- Applying the graph construction to the coordinate map of a plane in the `Q`-chart recovers
that plane. -/
theorem chart_equiv_left_inv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    Function.LeftInverse
      (fun S : { S : grassmannian V k // S ∈ chart_domain Q } ↦
        chart_fun hPQ hP S.1 S.2)
      (fun X : P →ₗ[ℝ] Q ↦
        ⟨graph hPQ hP X, graph_mem_chart_domain hPQ hP X⟩) := by
  intro X
  ext p
  -- Project the recovered graph point to the complementary summand `Q`.
  simpa [chart_fun, LinearMap.comp_apply, Submodule.coe_prodEquivOfIsCompl'] using
    congrArg (Q.projection P hPQ.symm)
      (chartLinearEquivSymm_apply_eq_graphPoint hPQ hP X p)

/-- Applying the coordinate map to the graph of `X : P → Q` recovers the original linear map. -/
theorem chart_equiv_right_inv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    Function.RightInverse
      (fun S : { S : grassmannian V k // S ∈ chart_domain Q } ↦
        chart_fun hPQ hP S.1 S.2)
      (fun X : P →ₗ[ℝ] Q ↦
        ⟨graph hPQ hP X, graph_mem_chart_domain hPQ hP X⟩) := by
  intro S
  apply Subtype.ext
  -- The structural graph reconstruction lemma closes the inverse law.
  exact graph_chartFun_eq hPQ hP S.1 S.2

/-- Example 1.36: if `V = P ⊕ Q` with `P` a `k`-plane, then the `k`-planes in `V` that intersect
`Q` trivially are in canonical bijection with the linear maps `P → Q`, via the graph
construction. -/
noncomputable def chart_equiv
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    { S : grassmannian V k // S ∈ chart_domain Q } ≃ (P →ₗ[ℝ] Q) where
  toFun := fun S ↦ chart_fun hPQ hP S.1 S.2
  invFun := fun X ↦ ⟨graph hPQ hP X, graph_mem_chart_domain hPQ hP X⟩
  left_inv := chart_equiv_right_inv hPQ hP
  right_inv := chart_equiv_left_inv hPQ hP

/-- The linear model space of the `Q`-chart has the expected dimension `k (n - k)`, where
`n = dim V`. -/
theorem chart_model_finrank
    (hPQ : IsCompl P Q) (hP : Module.finrank ℝ P = k) :
    Module.finrank ℝ (P →ₗ[ℝ] Q) = k * (Module.finrank ℝ V - k) := by
  have hQ : Module.finrank ℝ Q = Module.finrank ℝ V - k := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hPQ
    omega
  -- Compute the dimension of the linear-map space and rewrite the complementary dimension.
  calc
    Module.finrank ℝ (P →ₗ[ℝ] Q) = Module.finrank ℝ P * Module.finrank ℝ Q :=
      by simpa using (Module.finrank_linearMap (R := ℝ) (S := ℝ) (M := P) (N := Q))
    _ = k * (Module.finrank ℝ V - k) := by rw [hP, hQ]

end grassmannian

end
