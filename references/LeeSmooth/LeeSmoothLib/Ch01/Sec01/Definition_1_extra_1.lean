import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Manifold

/-- Definition 1-extra-1: A topological manifold of dimension `n` is a topological space that is
Hausdorff, second-countable, and equipped with charts to open subsets of `ℝ^n`. -/
class TopologicalManifold (n : ℕ) (M : Type u) [TopologicalSpace M] extends T2Space M,
    SecondCountableTopology M, ChartedSpace (EuclideanSpace ℝ (Fin n)) M

/-- A Hausdorff second-countable charted space modelled on `ℝ^n` carries the chapter's canonical
topological-manifold structure. -/
@[reducible] def topologicalManifoldOfChartedSpace (n : ℕ) (M : Type u) [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    TopologicalManifold n M where
  toT2Space := inferInstance
  toSecondCountableTopology := inferInstance
  toChartedSpace := inferInstance

/-- Euclidean space is a topological manifold of its own dimension. -/
instance euclideanSpace_topologicalManifold (n : ℕ) :
    TopologicalManifold n (EuclideanSpace ℝ (Fin n)) :=
  topologicalManifoldOfChartedSpace n (EuclideanSpace ℝ (Fin n))

noncomputable section

namespace TopologicalManifold

open ChartedSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [TopologicalManifold n M]

/-- A homeomorphism transports a topological manifold structure across the source. -/
@[reducible] noncomputable def of_homeomorph (n : ℕ) {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalManifold n N]
    (h : M ≃ₜ N) : TopologicalManifold n M := by
  let _ : T2Space M := h.symm.t2Space
  let _ : SecondCountableTopology M := h.secondCountableTopology
  let hs := h.symm.isLocalHomeomorph
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
    hs.chartedSpace h.symm.surjective
  exact topologicalManifoldOfChartedSpace n M

theorem locallyCompactSpace_of_topologicalManifold (n : ℕ) (M : Type u) [TopologicalSpace M]
    [TopologicalManifold n M] : LocallyCompactSpace M := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  infer_instance

-- Proof sketch: use the preferred chart at `p`; by definition its source contains `p`.
/-- A topological manifold has, at each point, a chart to `ℝ^n`, i.e. an open partial
homeomorphism whose source contains that point. -/
theorem exists_open_homeomorph (p : M) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), p ∈ e.source :=
  ⟨chartAt (EuclideanSpace ℝ (Fin n)) p, mem_chart_source _ p⟩

/-- Helper for Definition 1-extra-1: one can choose charts from both manifold structures whose
sources contain the same point. -/
lemma commonChartIntersectionAtPoint (n m : ℕ) (M : Type u) [TopologicalSpace M]
    [TopologicalManifold n M] [TopologicalManifold m M] (p : M) :
    ∃ eN : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      ∃ eM : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)),
        p ∈ eN.source ∩ eM.source := by
  -- Choose one chart from each manifold structure through the fixed point `p`.
  rcases TopologicalManifold.exists_open_homeomorph (n := n) (M := M) p with ⟨eN, hpN⟩
  rcases TopologicalManifold.exists_open_homeomorph (n := m) (M := M) p with ⟨eM, hpM⟩
  exact ⟨eN, eM, ⟨hpN, hpM⟩⟩

/-- Helper for Definition 1-extra-1: restricting two charts to their common source neighborhood
produces homeomorphic nonempty open subsets of the Euclidean models. -/
lemma euclideanOpenHomeomorphAtPoint (n m : ℕ) (M : Type u) [TopologicalSpace M]
    [TopologicalManifold n M] [TopologicalManifold m M] (p : M) :
    ∃ Vn : Set (EuclideanSpace ℝ (Fin n)), ∃ Vm : Set (EuclideanSpace ℝ (Fin m)),
      IsOpen Vn ∧ IsOpen Vm ∧ Vn.Nonempty ∧ Vm.Nonempty ∧ Nonempty ((↑Vn) ≃ₜ ↑Vm) := by
  rcases commonChartIntersectionAtPoint (n := n) (m := m) (M := M) p with ⟨eN, eM, hp⟩
  let common : Set M := eN.source ∩ eM.source
  have hCommonOpen : IsOpen common := eN.open_source.inter eM.open_source
  have hpN : p ∈ (eN.restr common).source := by
    -- On the common open set, the restricted chart source is exactly the common neighborhood.
    rw [eN.restr_source' common hCommonOpen]
    exact ⟨hp.1, hp⟩
  have hpM : p ∈ (eM.restr common).source := by
    -- The same normalization holds for the second restricted chart.
    rw [eM.restr_source' common hCommonOpen]
    exact ⟨hp.2, hp⟩
  have hSourceEq : (eN.restr common).source = (eM.restr common).source := by
    -- Both restricted sources reduce to the same common open neighborhood.
    rw [eN.restr_source' common hCommonOpen, eM.restr_source' common hCommonOpen]
    ext x
    simp [common, and_left_comm]
  refine ⟨(eN.restr common).target, (eM.restr common).target, ?_, ?_, ?_, ?_, ?_⟩
  · -- The target of an open partial homeomorphism is open by definition.
    exact (eN.restr common).open_target
  · -- The same openness statement holds for the second restricted chart.
    exact (eM.restr common).open_target
  · -- The image of `p` under the restricted first chart witnesses nonemptiness.
    exact ⟨(eN.restr common) p, (eN.restr common).map_source hpN⟩
  · -- The image of `p` under the restricted second chart witnesses nonemptiness.
    exact ⟨(eM.restr common) p, (eM.restr common).map_source hpM⟩
  · -- Both restricted charts identify the same open neighborhood with Euclidean open subsets.
    exact ⟨((eN.restr common).toHomeomorphSourceTarget).symm.trans
      ((Homeomorph.setCongr hSourceEq).trans (eM.restr common).toHomeomorphSourceTarget)⟩

/-- Helper for Definition 1-extra-1: an open chart target contains a genuine Euclidean ball around
the image of any source point. -/
private theorem ballSubsetTargetAroundPoint
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {p : M}
    (hp : p ∈ e.source) :
    ∃ r > 0, Metric.ball (e p) r ⊆ e.target := by
  -- The image point lies in the open target, so some metric ball stays inside that target.
  have hep : e p ∈ e.target := e.map_source hp
  rcases Metric.isOpen_iff.mp e.open_target (e p) hep with ⟨r, hr, hball⟩
  exact ⟨r, hr, hball⟩

/-- Helper for Definition 1-extra-1: shrinking a chart target to a Euclidean ball preserves the
chosen source point and makes the new target exactly that ball. -/
private theorem chartRestrictTargetToBall
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {p : M} {r : ℝ}
    (hp : p ∈ e.source) (hr : 0 < r) (hball : Metric.ball (e p) r ⊆ e.target) :
    ∃ e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      p ∈ e'.source ∧ e'.target = Metric.ball (e p) r := by
  let e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    e.trans (OpenPartialHomeomorph.ofSet (Metric.ball (e p) r) Metric.isOpen_ball)
  have hp_source : p ∈ e'.source := by
    -- The center point stays in the restricted source because its image lies in the smaller ball.
    simp [e', hp, hr]
  have htarget : e'.target = Metric.ball (e p) r := by
    -- The restricted target is exactly the chosen ball because the ball lies inside `e.target`.
    ext y
    simp [e', Set.inter_eq_left.mpr hball]
  exact ⟨e', hp_source, htarget⟩

/-- Helper for Definition 1-extra-1: a chart with ball target can be straightened to a chart whose
target is all of the Euclidean model space. -/
private theorem chartStraightenBallTarget
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 < r) (hball : e.target = Metric.ball c r) :
    ∃ e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      e'.source = e.source ∧ e'.target = Set.univ := by
  have hsource :
      e.target = (OpenPartialHomeomorph.univBall c r).symm.source := by
    -- Route correction: use the canonical `univBall` chart to normalize a Euclidean ball target.
    simp [OpenPartialHomeomorph.univBall_target, hr, hball]
  let e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    OpenPartialHomeomorph.trans' e (OpenPartialHomeomorph.univBall c r).symm hsource
  have hsource_eq : e'.source = e.source := by
    -- Exact composition with the inverse ball chart does not change the source.
    simp [e', OpenPartialHomeomorph.trans']
  have htarget_eq : e'.target = Set.univ := by
    -- The inverse ball chart lands in the whole Euclidean model.
    simp [e', OpenPartialHomeomorph.trans', OpenPartialHomeomorph.univBall_source]
  exact ⟨e', hsource_eq, htarget_eq⟩

/-- Helper for Definition 1-extra-1: a homeomorphism between nonempty open subsets of Euclidean
spaces should force equality of the Euclidean dimensions. -/
@[reducible] def topologicalManifoldSubtypeOfIsOpen {n : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V) :
    TopologicalManifold n ↥V := by
  -- Package the subtype as the canonical `Opens` object and reuse the existing instance there.
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  exact (show TopologicalManifold n U from topologicalManifoldOfChartedSpace n U)

/-- Helper for Definition 1-extra-1: an open subset of a finite-dimensional real normed space
inherits the canonical topological-manifold structure of the ambient finrank. -/
@[reducible] noncomputable def topologicalManifoldSubtypeOfFiniteDimensionalIsOpen {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsOpen s) :
    TopologicalManifold (Module.finrank ℝ E) ↥s :=
  let e : E ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ)
      (E := E) (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      (by simp)).toHomeomorph
  let t : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := e '' s
  let ht : IsOpen t := (e.isOpen_image).2 hs
  letI : TopologicalManifold (Module.finrank ℝ E) ↥t := topologicalManifoldSubtypeOfIsOpen ht
  -- Transfer the Euclidean open-subset manifold structure back along the ambient homeomorphism.
  of_homeomorph (Module.finrank ℝ E) (e.image s)

/-- Helper for Definition 1-extra-1: a `0`-dimensional topological manifold has the discrete
topology. -/
private theorem topologicalManifoldZeroDiscreteTopology (M : Type u) [TopologicalSpace M]
    [TopologicalManifold 0 M] : DiscreteTopology M := by
  -- A `0`-chart has subsingleton source, so every point is itself an open chart neighborhood.
  refine ⟨eq_bot_of_singletons_open fun p ↦ ?_⟩
  let e := chartAt (EuclideanSpace ℝ (Fin 0)) p
  have hsource : Set.Subsingleton e.source := by
    have hsub : Subsingleton e.source := by
      let h := e.toHomeomorphSourceTarget.toEquiv
      let _ : Subsingleton e.target := inferInstance
      exact h.subsingleton
    intro x hx y hy
    exact congrArg Subtype.val (show (⟨x, hx⟩ : e.source) = ⟨y, hy⟩ from Subsingleton.elim _ _)
  have hsource_eq : e.source = {p} :=
    hsource.eq_singleton_of_mem (mem_chart_source _ p)
  simpa [e, hsource_eq] using e.open_source

/-- Helper for Definition 1-extra-1: positive-dimensional Euclidean space has no open
singletons. -/
private theorem notIsOpenSingletonEuclideanSpace {n : ℕ}
    (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    ¬ IsOpen ({x} : Set (EuclideanSpace ℝ (Fin n))) := by
  -- Positive-dimensional Euclidean space has nontrivial punctured neighborhoods at every point.
  letI : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by simpa using hn)
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  letI : Filter.NeBot (nhdsWithin x ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :=
    Module.punctured_nhds_neBot ℝ (EuclideanSpace ℝ (Fin n)) x
  intro hx
  have hsingleton : ({x} : Set (EuclideanSpace ℝ (Fin n))) ∈ nhds x := hx.mem_nhds (by simp)
  have hinfinite : Set.Infinite ({x} : Set (EuclideanSpace ℝ (Fin n))) :=
    infinite_of_mem_nhds x hsingleton
  exact (Set.finite_singleton x).not_infinite hinfinite

/-- Helper for Definition 1-extra-1: an open singleton in Euclidean space forces dimension `0`.
-/
private theorem euclideanDimensionEqZeroOfOpenSingleton {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsOpen ({x} : Set (EuclideanSpace ℝ (Fin n)))) :
    n = 0 := by
  -- A positive-dimensional Euclidean model would contradict the previous non-isolation lemma.
  by_contra hne
  exact notIsOpenSingletonEuclideanSpace (Nat.pos_iff_ne_zero.mpr hne) x hx

/-- Helper for Definition 1-extra-1: an open partial homeomorphism with singleton source has
singleton target. -/
private theorem targetEqSingletonOfSourceEqSingleton {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {x : X}
    (hsource : e.source = ({x} : Set X)) :
    e.target = {e x} := by
  -- Homeomorphic source and target inherit the same subsingleton behavior.
  have hsourceSubsingleton : e.source.Subsingleton := by
    rw [hsource]
    exact Set.subsingleton_singleton
  have hsourceSubtype : Subsingleton e.source := by
    refine ⟨fun y z ↦ Subtype.ext (hsourceSubsingleton y.2 z.2)⟩
  let _ : Subsingleton e.source := hsourceSubtype
  have htargetSubsingleton : e.target.Subsingleton := by
    let _ : Subsingleton e.target := e.toHomeomorphSourceTarget.toEquiv.symm.subsingleton
    intro y hy z hz
    exact congrArg Subtype.val (show (⟨y, hy⟩ : e.target) = ⟨z, hz⟩ from Subsingleton.elim _ _)
  have hx : e x ∈ e.target := by
    have hxsource : x ∈ e.source := by simp [hsource]
    exact e.map_source hxsource
  exact htargetSubsingleton.eq_singleton_of_mem hx

/-- Helper for Definition 1-extra-1: a nonempty discrete topological manifold must have dimension
`0`. -/
private theorem topologicalManifoldDimensionEqZeroOfDiscrete (n : ℕ) (M : Type u)
    [TopologicalSpace M] [Nonempty M] [DiscreteTopology M] [TopologicalManifold n M] :
    n = 0 := by
  obtain ⟨p⟩ := ‹Nonempty M›
  rcases TopologicalManifold.exists_open_homeomorph (n := n) (M := M) p with ⟨e, hp⟩
  let e' := e.restr ({p} : Set M)
  have hsource : e'.source = ({p} : Set M) := by
    -- Restricting a chart to the open singleton isolates a singleton Euclidean target.
    rw [show e' = e.restr ({p} : Set M) by rfl]
    rw [e.restr_source' ({p} : Set M) (isOpen_discrete _)]
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      refine ⟨?_, hx⟩
      rcases hx with rfl
      exact hp
  have htarget : e'.target = {e' p} :=
    targetEqSingletonOfSourceEqSingleton e' hsource
  have hopen : IsOpen ({e' p} : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [htarget] using e'.open_target
  -- The restricted chart target is an open singleton in the Euclidean model, so `n = 0`.
  exact euclideanDimensionEqZeroOfOpenSingleton hopen

/-- Helper for Definition 1-extra-1: a homeomorphism between nonempty open subsets of Euclidean
spaces should force equality of the Euclidean dimensions. -/
private noncomputable def ambientOpenPartialHomeomorphOfOpenHomeomorph {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} {Vm : Set (EuclideanSpace ℝ (Fin m))}
    (hVn : IsOpen Vn) (hVm : IsOpen Vm) (hn : Vn.Nonempty) (hm : Vm.Nonempty)
    (hhomeo : ↥Vn ≃ₜ ↥Vm) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)) :=
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨Vn, hVn⟩
  let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)) := ⟨Vm, hVm⟩
  ((U.openPartialHomeomorphSubtypeCoe hn.to_subtype).symm.transHomeomorph hhomeo).trans
    (V.openPartialHomeomorphSubtypeCoe hm.to_subtype)

/-- Helper for Definition 1-extra-1: the ambient partial homeomorphism associated to a
homeomorphism of open Euclidean subtypes has source `Vn`. -/
private theorem ambientOpenPartialHomeomorphOfOpenHomeomorph_source {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} {Vm : Set (EuclideanSpace ℝ (Fin m))}
    (hVn : IsOpen Vn) (hVm : IsOpen Vm) (hn : Vn.Nonempty) (hm : Vm.Nonempty)
    (hhomeo : ↥Vn ≃ₜ ↥Vm) :
    (ambientOpenPartialHomeomorphOfOpenHomeomorph hVn hVm hn hm hhomeo).source = Vn := by
  -- Unfold the subtype wrapper to expose the original open subset as the source.
  simp [ambientOpenPartialHomeomorphOfOpenHomeomorph]

/-- Helper for Definition 1-extra-1: the ambient partial homeomorphism associated to a
homeomorphism of open Euclidean subtypes has target `Vm`. -/
private theorem ambientOpenPartialHomeomorphOfOpenHomeomorph_target {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} {Vm : Set (EuclideanSpace ℝ (Fin m))}
    (hVn : IsOpen Vn) (hVm : IsOpen Vm) (hn : Vn.Nonempty) (hm : Vm.Nonempty)
    (hhomeo : ↥Vn ≃ₜ ↥Vm) :
    (ambientOpenPartialHomeomorphOfOpenHomeomorph hVn hVm hn hm hhomeo).target = Vm := by
  -- The same subtype wrapper identifies the target with the original target open set.
  simp [ambientOpenPartialHomeomorphOfOpenHomeomorph]

/-- Helper for Definition 1-extra-1: deleting one point from a standard sphere leaves a space
homeomorphic to Euclidean space of the expected lower dimension. -/
private theorem sphereComplementHomeomorphEuclidean {n : ℕ}
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty ((({x}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) ≃ₜ
      EuclideanSpace ℝ (Fin n)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk (by simpa using (finrank_euclideanSpace_fin (𝕜 := ℝ) (ι := Fin (n + 1))))
  -- The stereographic chart at `x` already identifies its complement with the Euclidean model.
  refine ⟨(Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    (((stereographic' n x).toHomeomorphSourceTarget.trans
      (Homeomorph.setCongr (stereographic'_target (n := n) x))).trans
      (Homeomorph.Set.univ _))⟩

/-- Helper for Definition 1-extra-1: deleting two antipodal points from the standard sphere leaves
the punctured Euclidean model. -/
private theorem sphereComplementTwoPointsHomeomorphPuncturedEuclidean {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Nonempty ((({v, -v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) :=
    Fact.mk (by
      simpa [Nat.add_assoc] using
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (ι := Fin (n + 2))))
  let e :
      OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
        (EuclideanSpace ℝ (Fin (n + 1))) :=
    stereographic' (n + 1) (-v)
  have hv_source : v ∈ e.source := by
    -- The stereographic chart from `-v` is defined at the opposite pole `v`.
    simp [e, stereographic'_source, ne_neg_of_mem_unit_sphere ℝ v]
  have hv_zero : e v = 0 := by
    -- In this normalization, the opposite pole `v` is exactly the deleted Euclidean origin.
    dsimp [e, stereographic']
    exact
      (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1)
          (ne_zero_of_mem_unit_sphere (-v))).repr.map_eq_zero_iff.mpr
        (stereographic_neg_apply v)
  have hs :
      ({v, -v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) ⊆ e.source := by
    -- Deleting both poles certainly stays inside the chart source, which only deletes `-v`.
    intro x hx
    simp [e, stereographic'_source] at hx ⊢
    exact hx.2
  have himage :
      e '' ({v, -v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) =
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    -- The only deleted source point besides `-v` is `v`, and it maps exactly to `0`.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx_source : x ∈ e.source := hs hx
      simp at hx ⊢
      intro hy
      have hxeq : x = v := e.injOn hx_source hv_source (by simpa [hv_zero, hy])
      exact hx.1 hxeq
    · intro hy
      have hy_ne_zero : y ≠ 0 := by
        simpa using hy
      have hy_target : y ∈ e.target := by
        simpa [e, stereographic'_target]
      refine ⟨e.symm y, ?_, e.right_inv hy_target⟩
      have hy_source : e.symm y ∈ e.source := e.map_target hy_target
      have hy_not_neg : e.symm y ≠ -v := by
        simpa [e, stereographic'_source] using hy_source
      have hy_not_v : e.symm y ≠ v := by
        intro hEq
        have : y = 0 := by
          rw [← e.right_inv hy_target, hEq, hv_zero]
        exact hy_ne_zero this
      simp [hy_not_v, hy_not_neg]
  -- Restrict the stereographic chart to the complement of both poles.
  exact ⟨e.homeomorphOfImageSubsetSource hs himage⟩

/-- Helper for Definition 1-extra-1: the normalized punctured Euclidean model is homeomorphic to
the complement of two antipodal points on the next standard sphere. -/
private theorem sphereProdIoiHomeomorphSphereComplementTwoPoints {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Nonempty (((Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) × Set.Ioi (0 : ℝ)) ≃ₜ
      (({v, -v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)))) := by
  rcases sphereComplementTwoPointsHomeomorphPuncturedEuclidean (n := n) v with ⟨hSphere⟩
  -- Compose the radial decomposition of punctured Euclidean space with the two-pole sphere model.
  exact ⟨(homeomorphSphereProd (EuclideanSpace ℝ (Fin (n + 1))) 1 one_pos).symm.trans
    hSphere.symm⟩

/-- Helper for Definition 1-extra-1: a homeomorphism between nonempty open Euclidean subsets can
be normalized on the source to a nonempty open subset homeomorphic to the full target Euclidean
model. -/
private theorem sourceOpenHomeomorphToEuclideanOfOpenHomeomorph {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} {Vm : Set (EuclideanSpace ℝ (Fin m))}
    (hVn : IsOpen Vn) (hVm : IsOpen Vm) (hn : Vn.Nonempty) (hm : Vm.Nonempty)
    (hhomeo : Nonempty ((↑Vn) ≃ₜ ↑Vm)) :
    ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ U.Nonempty ∧ Nonempty (↑U ≃ₜ EuclideanSpace ℝ (Fin m)) := by
  rcases hhomeo with ⟨hhomeo⟩
  have hn' : Vn.Nonempty := hn
  rcases hn with ⟨x, hx⟩
  let e₀ := ambientOpenPartialHomeomorphOfOpenHomeomorph hVn hVm hn' hm hhomeo
  have hx₀ : x ∈ e₀.source := by
    -- The ambient partial homeomorphism has source exactly the original open subset `Vn`.
    change x ∈
      (ambientOpenPartialHomeomorphOfOpenHomeomorph hVn hVm hn' hm hhomeo).source
    rw [ambientOpenPartialHomeomorphOfOpenHomeomorph_source]
    exact hx
  rcases ballSubsetTargetAroundPoint e₀ hx₀ with ⟨r, hr, hball⟩
  rcases chartRestrictTargetToBall e₀ hx₀ hr hball with ⟨e₁, hx₁, htarget₁⟩
  rcases chartStraightenBallTarget (e := e₁) (c := e₀ x) (r := r) hr htarget₁ with
    ⟨e₂, hsource₂, htarget₂⟩
  have hx₂ : x ∈ e₂.source := by
    -- Straightening the target ball does not change the source neighborhood.
    rw [hsource₂]
    exact hx₁
  refine ⟨e₂.source, e₂.open_source, ⟨x, hx₂⟩, ?_⟩
  -- After normalizing the target to `univ`, the source is homeomorphic to the ambient target space.
  refine ⟨e₂.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr htarget₂).trans (Homeomorph.Set.univ _))⟩

/-- Helper for Definition 1-extra-1: if a nonempty open subset of `ℝ^n` is homeomorphic to the
full Euclidean model `ℝ^m`, then `m = n`. -/
private theorem globalEuclideanChartOfHomeomorph {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))}
    (hhomeo : Nonempty ((↑Vn) ≃ₜ EuclideanSpace ℝ (Fin m))) :
    ∃ e : OpenPartialHomeomorph ↥Vn (EuclideanSpace ℝ (Fin m)),
      e.source = Set.univ ∧ e.target = Set.univ := by
  rcases hhomeo with ⟨h⟩
  -- Package the global homeomorphism as a full chart on the open subtype.
  refine ⟨h.toOpenPartialHomeomorph, ?_, ?_⟩
  · simp
  · simp

/-- Helper for Definition 1-extra-1: after choosing a point in an open Euclidean subset, one can
shrink to a genuine Euclidean ball whose image is an open subset of the target Euclidean model. -/
private theorem restrictHomeomorphToOpenBallImage {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} (hVn : IsOpen Vn)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Vn)
    (h : ↥Vn ≃ₜ EuclideanSpace ℝ (Fin m)) :
    ∃ r > 0, ∃ W : Set (EuclideanSpace ℝ (Fin m)),
      IsOpen W ∧ Nonempty ((↑(Metric.ball x r)) ≃ₜ ↑W) := by
  rcases Metric.isOpen_iff.mp hVn x hx with ⟨r, hr, hball⟩
  let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)) :=
    ambientOpenPartialHomeomorphOfOpenHomeomorph hVn isOpen_univ ⟨x, hx⟩ Set.univ_nonempty
      (h.trans (Homeomorph.Set.univ _).symm)
  let W : Set (EuclideanSpace ℝ (Fin m)) := e '' Metric.ball x r
  have hsource : e.source = Vn := by
    -- The ambient partial homeomorphism remembers the original open source subset.
    simpa [e] using ambientOpenPartialHomeomorphOfOpenHomeomorph_source hVn isOpen_univ
      ⟨x, hx⟩ Set.univ_nonempty (h.trans (Homeomorph.Set.univ _).symm)
  have hballSource : Metric.ball x r ⊆ e.source := by
    -- The small Euclidean ball stays inside the source because it was chosen from openness.
    rw [hsource]
    exact hball
  have hW : IsOpen W := by
    -- Open partial homeomorphisms send open subsets of the source to open subsets of the target.
    dsimp [W]
    exact e.isOpen_image_of_subset_source Metric.isOpen_ball hballSource
  refine ⟨r, hr, W, hW, ?_⟩
  -- Restrict the ambient partial homeomorphism to the chosen source ball.
  exact ⟨e.homeomorphOfImageSubsetSource hballSource rfl⟩

/-- Helper for Definition 1-extra-1: puncturing a ball homeomorphism at a chosen center yields a
homeomorphism to the punctured target open subset. -/
private theorem puncturedBallHomeomorphOpenPuncture {n m : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    {W : Set (EuclideanSpace ℝ (Fin m))} (hW : IsOpen W)
    (hhomeo : Nonempty ((↑(Metric.ball x r)) ≃ₜ ↑W)) :
    ∃ y ∈ W, Nonempty ((↑((Metric.ball x r) \ {x})) ≃ₜ ↑(W \ {y})) := by
  rcases hhomeo with ⟨h⟩
  let xb : ↥(Metric.ball x r) := ⟨x, Metric.mem_ball_self hr⟩
  let yb : ↥W := h xb
  let y : EuclideanSpace ℝ (Fin m) := yb
  have hy : y ∈ W := yb.2
  have hpreimage :
      h ⁻¹' ({yb}ᶜ : Set ↥W) = ({xb}ᶜ : Set ↥(Metric.ball x r)) := by
    -- A homeomorphism sends the complement of a chosen point to the complement of its image.
    ext z
    simp [xb, yb, h.injective.eq_iff]
  let hSubtypePuncture :
      ({xb}ᶜ : Set ↥(Metric.ball x r)) ≃ₜ ({yb}ᶜ : Set ↥W) :=
    (Homeomorph.setCongr hpreimage.symm).trans
      (h.isEmbedding.homeomorphOfSubsetRange (s := ({yb}ᶜ : Set ↥W)) <| by
        simpa [h.range_coe])
  have hsourceEq :
      (((↑) : ↥(Metric.ball x r) → EuclideanSpace ℝ (Fin n)) ⁻¹'
        ((Metric.ball x r) \ ({x} : Set (EuclideanSpace ℝ (Fin n)))) :
          Set ↥(Metric.ball x r)) = ({xb}ᶜ : Set ↥(Metric.ball x r)) := by
    -- The ambient punctured ball is exactly the complement of the center inside the ball subtype.
    ext z
    constructor
    · intro hz hEq
      apply hz.2
      simpa [xb] using congrArg Subtype.val hEq
    · intro hz
      refine ⟨z.2, ?_⟩
      intro hEq
      apply hz
      exact Subtype.ext hEq
  let hSourcePuncture :
      ({xb}ᶜ : Set ↥(Metric.ball x r)) ≃ₜ
        ↑((Metric.ball x r) \ ({x} : Set (EuclideanSpace ℝ (Fin n)))) :=
    (Homeomorph.setCongr hsourceEq.symm).trans
      (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.homeomorphOfSubsetRange
        (s := ((Metric.ball x r) \ ({x} : Set (EuclideanSpace ℝ (Fin n)))) ) <| by
          intro z hz
          exact ⟨⟨z, hz.1⟩, rfl⟩)
  have htargetEq :
      (((↑) : ↥W → EuclideanSpace ℝ (Fin m)) ⁻¹'
        (W \ ({y} : Set (EuclideanSpace ℝ (Fin m)))) : Set ↥W) = ({yb}ᶜ : Set ↥W) := by
    -- The same complement normalization holds on the target open subset.
    ext z
    constructor
    · intro hz hEq
      apply hz.2
      simpa [y, yb] using congrArg Subtype.val hEq
    · intro hz
      refine ⟨z.2, ?_⟩
      intro hEq
      apply hz
      exact Subtype.ext hEq
  let hTargetPuncture :
      ({yb}ᶜ : Set ↥W) ≃ₜ ↑(W \ ({y} : Set (EuclideanSpace ℝ (Fin m)))) :=
    (Homeomorph.setCongr htargetEq.symm).trans
      (hW.isOpenEmbedding_subtypeVal.homeomorphOfSubsetRange
        (s := (W \ ({y} : Set (EuclideanSpace ℝ (Fin m))))) <| by
        intro z hz
        exact ⟨⟨z, hz.1⟩, rfl⟩)
  refine ⟨y, hy, ?_⟩
  -- Compare the ambient punctured subsets by passing through the subtype complements.
  exact ⟨hSourcePuncture.symm.trans (hSubtypePuncture.trans hTargetPuncture)⟩

/-- Helper for Definition 1-extra-1: a punctured Euclidean ball is homeomorphic to the canonical
punctured Euclidean model. -/
private theorem puncturedBallHomeomorphPuncturedEuclidean {n : ℕ}
    {x : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 < r) :
    Nonempty ((↑((Metric.ball x r) \ {x})) ≃ₜ
      ↑(({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))))) := by
  let hBall : ↑(Metric.ball x r) ≃ₜ ↑(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target x hr)).symm.trans
      ((OpenPartialHomeomorph.univBall x r).toHomeomorphSourceTarget.symm.trans
        (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source x r)))
  let xb : ↥(Metric.ball x r) := ⟨x, Metric.mem_ball_self hr⟩
  let zeroUniv : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := ⟨0, by simp⟩
  have hBall_zero : hBall xb = zeroUniv := by
    -- The inverse ball chart sends the puncture center to the Euclidean origin.
    dsimp [hBall, xb, zeroUniv, Homeomorph.setCongr]
    ext
    simp [OpenPartialHomeomorph.univBall_symm_apply_center]
  have hpreimage :
      hBall ⁻¹' ({zeroUniv}ᶜ : Set ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1))))) =
        ({xb}ᶜ : Set ↥(Metric.ball x r)) := by
    -- Removing the center in the source matches removing the origin in the normalized target.
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hz hEq
      apply hz
      rw [hEq, hBall_zero]
    · intro hz hEq
      apply hz
      exact hBall.injective (hEq.trans hBall_zero.symm)
  let hSubtypePuncture :
      ({xb}ᶜ : Set ↥(Metric.ball x r)) ≃ₜ
        ({zeroUniv}ᶜ : Set ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Homeomorph.setCongr hpreimage.symm).trans
      (hBall.isEmbedding.homeomorphOfSubsetRange
        (s := ({zeroUniv}ᶜ : Set ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1)))))) <| by
          simpa [hBall.range_coe])
  have hsourceEq :
      (((↑) : ↥(Metric.ball x r) → EuclideanSpace ℝ (Fin (n + 1))) ⁻¹'
        ((Metric.ball x r) \ ({x} : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
          Set ↥(Metric.ball x r)) = ({xb}ᶜ : Set ↥(Metric.ball x r)) := by
    -- The ambient punctured ball is the complement of the center inside the ball subtype.
    ext z
    constructor
    · intro hz hEq
      apply hz.2
      simpa [xb] using congrArg Subtype.val hEq
    · intro hz
      refine ⟨z.2, ?_⟩
      intro hEq
      apply hz
      exact Subtype.ext hEq
  let hSourcePuncture :
      ({xb}ᶜ : Set ↥(Metric.ball x r)) ≃ₜ
        ↑((Metric.ball x r) \ ({x} : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Homeomorph.setCongr hsourceEq.symm).trans
      (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.homeomorphOfSubsetRange
        (s := ((Metric.ball x r) \ ({x} : Set (EuclideanSpace ℝ (Fin (n + 1))))) ) <| by
          intro z hz
          exact ⟨⟨z, hz.1⟩, rfl⟩)
  have htargetEq :
      (((↑) : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
          EuclideanSpace ℝ (Fin (n + 1))) ⁻¹'
        (({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
          Set ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1))))) =
        ({zeroUniv}ᶜ : Set ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    -- Inside the universal subtype, puncturing at the origin is just taking the complement of `0`.
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hz hEq
      apply hz
      simpa [zeroUniv] using congrArg Subtype.val hEq
    · intro hz
      intro hEq
      apply hz
      exact Subtype.ext hEq
  let hTargetPuncture :
      ({zeroUniv}ᶜ : Set ↥(Set.univ : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≃ₜ
        ↑(({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Homeomorph.setCongr htargetEq.symm).trans
      (isOpen_univ.isOpenEmbedding_subtypeVal.homeomorphOfSubsetRange
        (s := (({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))))) <| by
          intro z hz
          exact ⟨⟨z, by simp⟩, rfl⟩)
  -- Pass from the punctured ball subtype to the punctured Euclidean complement via the normalized
  -- ball homeomorphism.
  exact ⟨hSourcePuncture.symm.trans (hSubtypePuncture.trans hTargetPuncture)⟩

/-- Helper for Definition 1-extra-1: removing one point from an open Euclidean subset preserves
openness. -/
private theorem isOpen_diff_singleton_euclidean {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    (y : EuclideanSpace ℝ (Fin (k + 1))) :
    IsOpen (W \ ({y} : Set (EuclideanSpace ℝ (Fin (k + 1))))) := by
  -- Intersect the ambient open set with the open complement of the deleted point.
  simpa [Set.diff_eq] using hW.inter isClosed_singleton.isOpen_compl

/-- Helper for Definition 1-extra-1: punctured Euclidean space is a nonempty open subset of the
ambient Euclidean space. -/
private theorem puncturedEuclideanNonempty {k : ℕ} :
    (({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 1))))).Nonempty := by
  -- The first basis vector stays away from the deleted origin.
  refine ⟨EuclideanSpace.single 0 1, ?_⟩
  simp

/-- Helper for Definition 1-extra-1: the canonical punctured Euclidean model is open. -/
private theorem isOpen_puncturedEuclidean {k : ℕ} :
    IsOpen (({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 1))))) := by
  -- In a Hausdorff Euclidean space, complements of singletons are open.
  simpa [Set.diff_eq] using
    (isOpen_diff_singleton_euclidean (k := k) isOpen_univ (0 : EuclideanSpace ℝ (Fin (k + 1))))

/-- Helper for Definition 1-extra-1: any space homeomorphic to punctured Euclidean space is
nonempty. -/
private theorem nonemptyOfHomeomorphPuncturedEuclidean {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hhomeo : Nonempty (↑U ≃ₜ ↑(({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))))) :
    U.Nonempty := by
  rcases hhomeo with ⟨e⟩
  rcases puncturedEuclideanNonempty (k := n) with ⟨z, hz⟩
  exact ⟨e.symm ⟨z, hz⟩, (e.symm ⟨z, hz⟩).property⟩

/-- Helper for Definition 1-extra-1: a homeomorphism to the canonical punctured Euclidean model
transports its manifold structure onto the source carrier. -/
@[reducible] private noncomputable def topologicalManifoldOfPuncturedEuclideanHomeomorph {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hhomeo : ↑U ≃ₜ ↑(({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    TopologicalManifold (n + 1) ↥U := by
  letI :
      TopologicalManifold (n + 1) ↑(({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    topologicalManifoldSubtypeOfIsOpen (isOpen_puncturedEuclidean (k := n))
  -- Pull back the canonical punctured-Euclidean manifold structure along the given homeomorphism.
  exact of_homeomorph (n + 1) hhomeo

/-- Helper for Definition 1-extra-1: the remaining positive-dimensional core is uniqueness of the
Euclidean manifold model on one common nonempty carrier. -/
private theorem sameCarrierPositiveEuclideanModelDimensionEq {n m : ℕ}
    (M : Type u) [TopologicalSpace M] [Nonempty M]
    [TopologicalManifold (n + 1) M] [TopologicalManifold (m + 1) M] :
    m = n := by
  -- Route correction: all punctured/open-subset normalization has been pushed upstream.
  -- The only unresolved step is now the same-carrier uniqueness theorem for positive dimensions.
  sorry

/-- Helper for Definition 1-extra-1: the positive-dimensional owner theorem is the ambient
dimension invariant for an ambient-open subset homeomorphic to punctured Euclidean space. -/
private theorem puncturedEuclideanAmbientDimensionEqOfOpenHomeomorph {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hU : IsOpen U)
    (hhomeo : Nonempty (↑U ≃ₜ ↑(({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))))) :
    m = n := by
  have hSourceNe : U.Nonempty := nonemptyOfHomeomorphPuncturedEuclidean (n := n) (m := m) hhomeo
  letI : TopologicalManifold (m + 1) ↥U := topologicalManifoldSubtypeOfIsOpen hU
  letI : Nonempty ↥U := hSourceNe.to_subtype
  rcases hhomeo with ⟨e⟩
  letI : TopologicalManifold (n + 1) ↥U :=
    topologicalManifoldOfPuncturedEuclideanHomeomorph (n := n) (m := m) e
  -- Route correction: the punctured/open-subset normalization is finished.
  -- The owner theorem now reduces exactly to same-carrier uniqueness on the nonempty subtype `↥U`.
  simpa using sameCarrierPositiveEuclideanModelDimensionEq (n := n) (m := m) ↥U

/-- Helper for Definition 1-extra-1: the remaining positive-dimensional owner theorem is the
ambient-dimension invariant for an open punctured Euclidean subset. -/
private theorem puncturedOpenEuclideanDimensionEq {n m : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hW : IsOpen W)
    {y : EuclideanSpace ℝ (Fin (m + 1))} (hy : y ∈ W)
    (hhomeo : Nonempty ((↑(W \ {y})) ≃ₜ
      ↑(({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))))) :
    m = n := by
  have hWpunctured : IsOpen (W \ ({y} : Set (EuclideanSpace ℝ (Fin (m + 1))))) :=
    isOpen_diff_singleton_euclidean (k := m) hW y
  -- Route correction: this theorem is now only the deleted-point wrapper around the normalized
  -- owner theorem on an ambient-open Euclidean subset.
  let _ := hy
  simpa using
    puncturedEuclideanAmbientDimensionEqOfOpenHomeomorph (n := n) (m := m)
      (U := W \ ({y} : Set (EuclideanSpace ℝ (Fin (m + 1))))) hWpunctured hhomeo

/-- Helper for Definition 1-extra-1: the genuine positive-dimensional frontier is the punctured
Euclidean invariant for an open target puncture. -/
private theorem puncturedBallDimensionEqOfOpenPuncture {n m : ℕ}
    {x : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 < r)
    {W : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hW : IsOpen W)
    {y : EuclideanSpace ℝ (Fin (m + 1))} (hy : y ∈ W)
    (hhomeo : Nonempty ((↑((Metric.ball x r) \ {x})) ≃ₜ ↑(W \ {y}))) :
    m = n := by
  rcases puncturedBallHomeomorphPuncturedEuclidean (n := n) (x := x) hr with ⟨hBall⟩
  rcases hhomeo with ⟨hhomeo⟩
  have hWpunctured : IsOpen (W \ ({y} : Set (EuclideanSpace ℝ (Fin (m + 1))))) :=
    isOpen_diff_singleton_euclidean (k := m) hW y
  -- Route correction: the ball-specific geometry is finished; only the normalized punctured-owner
  -- theorem remains.
  let _ := hy
  exact puncturedEuclideanAmbientDimensionEqOfOpenHomeomorph (n := n) (m := m)
    (U := W \ ({y} : Set (EuclideanSpace ℝ (Fin (m + 1))))) hWpunctured
    ⟨hhomeo.symm.trans hBall⟩

/-- Helper for Definition 1-extra-1: if a nonempty open subset of `ℝ^n` is homeomorphic to the
full Euclidean model `ℝ^m`, then `m = n`. -/
private theorem euclideanModelDimensionEqOfOpenHomeomorphToUniv {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))}
    (hVn : IsOpen Vn) (hn : Vn.Nonempty)
    (hhomeo : Nonempty ((↑Vn) ≃ₜ EuclideanSpace ℝ (Fin m))) :
    m = n := by
  by_cases hzeroN : n = 0
  · subst hzeroN
    have hsub : Subsingleton ↥Vn := by
      -- In the `0`-dimensional Euclidean model, every nonempty open subset is subsingleton.
      refine ⟨fun x y ↦ Subtype.ext (Subsingleton.elim x.1 y.1)⟩
    letI : DiscreteTopology ↥Vn := inferInstance
    rcases hhomeo with ⟨h⟩
    letI : DiscreteTopology (EuclideanSpace ℝ (Fin m)) := h.discreteTopology
    -- Route correction: discharge the zero-dimensional source branch before entering the punctured
    -- comparison, so the positive-dimensional frontier is isolated cleanly.
    exact topologicalManifoldDimensionEqZeroOfDiscrete (n := m) (M := EuclideanSpace ℝ (Fin m))
  by_cases hzeroM : m = 0
  · subst hzeroM
    rcases hhomeo with ⟨h⟩
    letI : TopologicalManifold n ↥Vn := topologicalManifoldSubtypeOfIsOpen hVn
    letI : Nonempty ↥Vn := hn.to_subtype
    letI : DiscreteTopology (EuclideanSpace ℝ (Fin 0)) := inferInstance
    letI : DiscreteTopology ↥Vn := (Homeomorph.discreteTopology_iff h).2 inferInstance
    -- The symmetric zero-dimensional target branch also collapses the ambient source dimension.
    simpa using
      (topologicalManifoldDimensionEqZeroOfDiscrete (n := n) (M := ↥Vn)).symm
  rcases Nat.exists_eq_succ_of_ne_zero hzeroN with ⟨n', rfl⟩
  rcases Nat.exists_eq_succ_of_ne_zero hzeroM with ⟨m', rfl⟩
  rcases hhomeo with ⟨h⟩
  rcases hn with ⟨x, hx⟩
  rcases restrictHomeomorphToOpenBallImage (n := n' + 1) (m := m' + 1) hVn hx h with
    ⟨r, hr, W, hW, hWhomeo⟩
  rcases puncturedBallHomeomorphOpenPuncture (n := n' + 1) (m := m' + 1) hr hW hWhomeo with
    ⟨y, hy, hpunctured⟩
  rcases hpunctured with ⟨hpunctured⟩
  rcases puncturedBallHomeomorphPuncturedEuclidean (n := n') (x := x) hr with ⟨hBall⟩
  have hWpunctured : IsOpen (W \ ({y} : Set (EuclideanSpace ℝ (Fin (m' + 1))))) :=
    isOpen_diff_singleton_euclidean (k := m') hW y
  -- Route correction: the positive-dimensional branch now calls the normalized punctured-owner
  -- theorem directly instead of cycling through the deleted-point wrapper.
  let _ := hy
  simpa using
    puncturedEuclideanAmbientDimensionEqOfOpenHomeomorph (n := n') (m := m')
      (U := W \ ({y} : Set (EuclideanSpace ℝ (Fin (m' + 1))))) hWpunctured
      ⟨hpunctured.symm.trans hBall⟩

/-- Helper for Definition 1-extra-1: a homeomorphism between nonempty open subsets of Euclidean
spaces should force equality of the Euclidean dimensions. -/
private theorem euclideanModelDimensionEqOfOpenHomeomorph {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} {Vm : Set (EuclideanSpace ℝ (Fin m))}
    (hVn : IsOpen Vn) (hVm : IsOpen Vm) (hn : Vn.Nonempty) (hm : Vm.Nonempty)
    (hhomeo : Nonempty ((↑Vn) ≃ₜ ↑Vm)) :
    m = n := by
  by_cases hzeroN : n = 0
  · subst hzeroN
    letI : TopologicalManifold m ↥Vm := topologicalManifoldSubtypeOfIsOpen hVm
    letI : Nonempty ↥Vm := hm.to_subtype
    have hsub : Subsingleton ↥Vn := by
      -- Any nonempty open subset of the `0`-dimensional Euclidean model is subsingleton.
      refine ⟨fun x y ↦ Subtype.ext (Subsingleton.elim x.1 y.1)⟩
    letI : DiscreteTopology ↥Vn := inferInstance
    rcases hhomeo with ⟨h⟩
    letI : DiscreteTopology ↥Vm := h.discreteTopology
    -- Transport discreteness across the homeomorphism, then apply the solved zero-dimensional case.
    have hzeroM : m = 0 := topologicalManifoldDimensionEqZeroOfDiscrete (n := m) (M := ↥Vm)
    simp [hzeroM]
  by_cases hzeroM : m = 0
  · subst hzeroM
    letI : TopologicalManifold n ↥Vn := topologicalManifoldSubtypeOfIsOpen hVn
    letI : Nonempty ↥Vn := hn.to_subtype
    have hsub : Subsingleton ↥Vm := by
      -- The symmetric `0`-dimensional target branch is also subsingleton.
      refine ⟨fun x y ↦ Subtype.ext (Subsingleton.elim x.1 y.1)⟩
    letI : DiscreteTopology ↥Vm := inferInstance
    rcases hhomeo with ⟨h⟩
    letI : DiscreteTopology ↥Vn := h.symm.discreteTopology
    -- Route correction: discharge the zero-dimensional branches before the punctured-neighborhood
    -- comparison, so the remaining frontier is genuinely positive-dimensional.
    have hzeroN' : n = 0 := topologicalManifoldDimensionEqZeroOfDiscrete (n := n) (M := ↥Vn)
    simp [hzeroN']
  rcases sourceOpenHomeomorphToEuclideanOfOpenHomeomorph hVn hVm hn hm hhomeo with
    ⟨U, hU, hUne, hUhomeo⟩
  -- Route correction: normalize only one side to the ambient Euclidean model first.
  -- The remaining blocker is now the one-sided ambient invariant for open Euclidean subsets.
  exact euclideanModelDimensionEqOfOpenHomeomorphToUniv hU hUne hUhomeo

/-- Helper for Definition 1-extra-1: equality of Euclidean model dimensions gives an ambient
homeomorphism by transport along the index equality. -/
private theorem euclideanHomeomorphOfEq {n m : ℕ} (h : m = n) :
    Nonempty ((EuclideanSpace ℝ (Fin n)) ≃ₜ (EuclideanSpace ℝ (Fin m))) := by
  -- Once the indices agree, the ambient Euclidean spaces are definitionally the same.
  cases h
  exact ⟨Homeomorph.refl _⟩

/-- Helper for Definition 1-extra-1: a homeomorphism between Euclidean spaces is the special case
of the open-subset invariant with both subsets equal to `univ`. -/
private theorem euclideanDimensionEq_of_homeomorph {n m : ℕ}
    (hhomeo : Nonempty ((EuclideanSpace ℝ (Fin n)) ≃ₜ (EuclideanSpace ℝ (Fin m)))) :
    m = n := by
  rcases hhomeo with ⟨hhomeo⟩
  let hunivN : (↑(Set.univ : Set (EuclideanSpace ℝ (Fin n)))) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    Homeomorph.Set.univ _
  let hunivM : (↑(Set.univ : Set (EuclideanSpace ℝ (Fin m)))) ≃ₜ EuclideanSpace ℝ (Fin m) :=
    Homeomorph.Set.univ _
  -- Reinterpret both ambient Euclidean spaces as nonempty open subsets of themselves.
  exact euclideanModelDimensionEqOfOpenHomeomorph (n := n) (m := m)
    (Vn := Set.univ) (Vm := Set.univ) isOpen_univ isOpen_univ Set.univ_nonempty
    Set.univ_nonempty ⟨hunivN.trans (hhomeo.trans hunivM.symm)⟩

/-- Helper for Definition 1-extra-1: a homeomorphism between standard spheres forces equality of
their Euclidean model dimensions. -/
private theorem sphereDimensionEq_of_homeomorph {n m : ℕ}
    (hhomeo : Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ₜ
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))) :
    m = n := by
  rcases hhomeo with ⟨hhomeo⟩
  let xn : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let xm : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := hhomeo xn
  have hpreimage :
      hhomeo ⁻¹' ({xm}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) =
        ({xn}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
    -- A homeomorphism sends the complement of one point to the complement of its image.
    ext z
    simp [xm, xn, hhomeo.injective.eq_iff]
  let hcompl :
      (({xn}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) ≃ₜ
        ({xm}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) :=
    (Homeomorph.setCongr hpreimage.symm).trans
      (hhomeo.isEmbedding.homeomorphOfSubsetRange (s := ({xm}ᶜ : Set
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))) <| by
        simpa [hhomeo.range_coe])
  rcases sphereComplementHomeomorphEuclidean (n := n) xn with ⟨hnc⟩
  rcases sphereComplementHomeomorphEuclidean (n := m) xm with ⟨hmc⟩
  -- After deleting corresponding points, both spheres become Euclidean spaces.
  exact euclideanDimensionEq_of_homeomorph ⟨hnc.symm.trans (hcompl.trans hmc)⟩

/-- Helper for Definition 1-extra-1: once the open-subset invariant gives equality of dimensions,
the corresponding ambient Euclidean spaces are homeomorphic. -/
private theorem euclideanHomeomorphOfOpenHomeomorph {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} {Vm : Set (EuclideanSpace ℝ (Fin m))}
    (hVn : IsOpen Vn) (hVm : IsOpen Vm) (hn : Vn.Nonempty) (hm : Vm.Nonempty)
    (hhomeo : Nonempty ((↑Vn) ≃ₜ ↑Vm)) :
    Nonempty ((EuclideanSpace ℝ (Fin n)) ≃ₜ (EuclideanSpace ℝ (Fin m))) := by
  -- After the dimension invariant is known, the ambient models agree and can be identified.
  exact euclideanHomeomorphOfEq
    (euclideanModelDimensionEqOfOpenHomeomorph hVn hVm hn hm hhomeo)

/-- Helper for Definition 1-extra-1: a homeomorphism between nonempty open subsets of Euclidean
spaces should force equality of the Euclidean dimensions. -/
lemma modelFinrank_eq_of_twoTopologicalManifolds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : Type u} [TopologicalSpace M] [Nonempty M]
    [TopologicalManifold (Module.finrank ℝ E) M]
    [TopologicalManifold (Module.finrank ℝ F) M] :
    Module.finrank ℝ F = Module.finrank ℝ E := by
  by_cases hE0 : Module.finrank ℝ E = 0
  · have hTopE0 : TopologicalManifold 0 M := by
      -- Normalize the first manifold structure to the already-solvable zero-dimensional branch.
      simpa [hE0] using
        (inferInstance : TopologicalManifold (Module.finrank ℝ E) M)
    letI : TopologicalManifold 0 M := hTopE0
    letI : DiscreteTopology M := topologicalManifoldZeroDiscreteTopology M
    have hF0 : Module.finrank ℝ F = 0 := by
      -- Once the carrier is discrete, the second manifold structure must also be zero-dimensional.
      exact topologicalManifoldDimensionEqZeroOfDiscrete (n := Module.finrank ℝ F) (M := M)
    simp [hE0, hF0]
  by_cases hF0 : Module.finrank ℝ F = 0
  · have hTopF0 : TopologicalManifold 0 M := by
      -- Symmetrically, a zero-dimensional second model makes the common carrier discrete.
      simpa [hF0] using
        (inferInstance : TopologicalManifold (Module.finrank ℝ F) M)
    letI : TopologicalManifold 0 M := hTopF0
    letI : DiscreteTopology M := topologicalManifoldZeroDiscreteTopology M
    have hE0' : Module.finrank ℝ E = 0 := by
      -- The first manifold structure collapses to the same zero-dimensional discrete case.
      exact topologicalManifoldDimensionEqZeroOfDiscrete (n := Module.finrank ℝ E) (M := M)
    simp [hF0, hE0']
  · obtain ⟨p⟩ := ‹Nonempty M›
    -- After the zero-dimensional branches, compare the two manifold structures through one point.
    rcases euclideanOpenHomeomorphAtPoint
        (n := Module.finrank ℝ E) (m := Module.finrank ℝ F) (M := M) p with
      ⟨Vn, Vm, hVn, hVm, hn, hm, hhomeo⟩
    -- The remaining work is exactly the Euclidean open-subset dimension invariant.
    exact euclideanModelDimensionEqOfOpenHomeomorph hVn hVm hn hm hhomeo

/-- Helper for Definition 1-extra-1: a homeomorphism between topological manifolds is a `C^0`
diffeomorphism for the corresponding Euclidean models. -/
noncomputable def homeomorphToZeroDiffeomorph
    {n m : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalManifold n M]
    [TopologicalSpace N] [TopologicalManifold m N]
    (h : M ≃ₜ N) :
    M ≃ₘ^0⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N where
  toEquiv := h.toEquiv
  contMDiff_toFun := by
    -- At smoothness level `0`, manifold differentiability is exactly continuity.
    rw [contMDiff_zero_iff]
    exact h.continuous
  contMDiff_invFun := by
    -- The inverse direction is handled by the same continuity-to-`C^0` bridge.
    rw [contMDiff_zero_iff]
    exact h.symm.continuous

/-- Helper for Definition 1-extra-1: transport the canonical open-subtype manifold structure of a
finite-dimensional real normed space across a homeomorphism of subtypes. -/
@[reducible] noncomputable def topologicalManifoldSubtypeOfFiniteDimensionalIsOpen_of_homeomorph
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s : Set E} {t : Set F} (ht : IsOpen t) (h : ↥s ≃ₜ ↥t) :
    TopologicalManifold (Module.finrank ℝ F) ↥s := by
  letI : TopologicalManifold (Module.finrank ℝ F) ↥t :=
    topologicalManifoldSubtypeOfFiniteDimensionalIsOpen ht
  -- Pull back the target open-subset manifold structure along the given homeomorphism.
  exact of_homeomorph (Module.finrank ℝ F) h

/-- Helper for Definition 1-extra-1: a homeomorphism between nonempty open subsets of Euclidean
spaces should force equality of the Euclidean dimensions. -/
lemma finiteDimensionalAmbient_eq_of_open_homeomorph {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s : Set E} {t : Set F} (hs : IsOpen s) (ht : IsOpen t) (hsne : s.Nonempty)
    (_htne : t.Nonempty)
    (hhomeo : Nonempty ((↑s) ≃ₜ ↑t)) :
    Module.finrank ℝ F = Module.finrank ℝ E := by
  let n := Module.finrank ℝ E
  let m := Module.finrank ℝ F
  letI : TopologicalManifold n ↥s := topologicalManifoldSubtypeOfFiniteDimensionalIsOpen hs
  letI : Nonempty ↥s := hsne.to_subtype
  rcases hhomeo with ⟨h⟩
  letI : TopologicalManifold m ↥s :=
    topologicalManifoldSubtypeOfFiniteDimensionalIsOpen_of_homeomorph (F := F) ht h
  -- Once both manifold structures live on the same nonempty subtype, the generic owner theorem
  -- closes the ambient finrank comparison.
  simpa [m, n] using
    (modelFinrank_eq_of_twoTopologicalManifolds (E := E) (F := F) (M := ↥s))

/-- Helper for Definition 1-extra-1: a homeomorphism between nonempty open subsets of Euclidean
spaces should force equality of the Euclidean dimensions. -/
lemma openEuclideanDimension_eq_of_homeomorph {n m : ℕ}
    {Vn : Set (EuclideanSpace ℝ (Fin n))} {Vm : Set (EuclideanSpace ℝ (Fin m))}
    (hVn : IsOpen Vn) (hVm : IsOpen Vm) (hn : Vn.Nonempty) (hm : Vm.Nonempty)
    (hhomeo : Nonempty ((↑Vn) ≃ₜ ↑Vm)) :
    m = n := by
  -- Reuse the isolated Euclidean-model uniqueness step directly.
  exact euclideanModelDimensionEqOfOpenHomeomorph hVn hVm hn hm hhomeo

/-- A nonempty space cannot carry topological manifold structures of two different dimensions. -/
theorem dimension_eq (n m : ℕ) (M : Type u) [TopologicalSpace M] [Nonempty M]
    [TopologicalManifold n M] [TopologicalManifold m M] :
    m = n := by
  letI : TopologicalManifold (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) M := by
    -- Normalize the `n`-manifold instance to the generic finrank-indexed owner theorem.
    simpa [finrank_euclideanSpace_fin] using (inferInstance : TopologicalManifold n M)
  letI : TopologicalManifold (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))) M := by
    -- Repeat the same normalization for the `m`-manifold structure.
    simpa [finrank_euclideanSpace_fin] using (inferInstance : TopologicalManifold m M)
  -- Normalize the custom manifold dimensions to Euclidean model finranks on the same space.
  simpa [finrank_euclideanSpace_fin] using
    (modelFinrank_eq_of_twoTopologicalManifolds
      (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin m)) (M := M))

/-- Homeomorphic nonempty topological manifolds have the same dimension. -/
theorem dimension_eq_of_homeomorph (n m : ℕ) (M : Type u) (N : Type v)
    [TopologicalSpace M] [Nonempty M] [TopologicalManifold n M]
    [TopologicalSpace N] [TopologicalManifold m N] (h : M ≃ₜ N) :
    m = n := by
  letI : TopologicalManifold m M := of_homeomorph m h
  simpa using dimension_eq n m M

end TopologicalManifold

namespace TopologicalSpace.Opens

open ChartedSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [TopologicalManifold n M] (U : Opens M)

/-- An open subset of a topological manifold is canonically a topological manifold of the same
dimension. -/
noncomputable instance topologicalManifold : TopologicalManifold n U :=
  topologicalManifoldOfChartedSpace n U

end TopologicalSpace.Opens

end
