import PoincareConjecture.Topology.FiniteQuotient
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth quotient charts and their projection

The quotient charted-space instance in the pinned Mathlib does not yet prove
that a smooth free action gives a smooth quotient or a smooth projection.
We construct those bridges using the actual quotient atlas: a local branch
of the projection agrees near each point with one group translate. This
supplies smooth chart transitions and smooth local inverse maps.

The model is a real normed vector space without boundary. No assertion about
an arbitrary topological three-manifold admitting a smooth structure is
used or proved here.
-/

open Function Set Filter Topology ChartedSpace IsManifold
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

section LocalBranches

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {E : Type*} [TopologicalSpace E] [ChartedSpace V E]
  {X : Type*} [TopologicalSpace X]
  {G : Type*} [Group G] [MulAction G E]
  {n : ℕ∞ω} [IsManifold 𝓘(ℝ, V) n E]
  {p : E → X} (hp : IsQuotientCoveringMap p G)
  (hsmul : ∀ g : G, ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) n (fun x : E => g • x))

include hp hsmul

omit [IsManifold 𝓘(ℝ, V) n E] in
/-- A local inverse branch followed by the quotient projection is locally a
group translate. Smoothness follows from the action, not from an assumed
smooth quotient projection. -/
theorem contMDiffAt_localBranch_comp_projection
    (s : OpenPartialHomeomorph X E) (hs : (s.symm : E → X) = p)
    {x : E} (hx : p x ∈ s.source) :
    ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V) n (fun z => s (p z)) x := by
  have hproj : p (s (p x)) = p x := by
    simpa only [hs] using s.left_inv hx
  obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.mp hproj
  change g • x = s (p x) at hg
  have htarget : g • x ∈ s.target := by rw [hg]; exact s.map_source hx
  have hnear : ∀ᶠ z in 𝓝 x, g • z ∈ s.target :=
    (hsmul g x).continuousAt (s.open_target.mem_nhds htarget)
  apply (hsmul g x).congr_of_eventuallyEq
  filter_upwards [hnear] with z hz
  rw [← hp.map_smul g (e := z), ← hs]
  exact s.right_inv hz

/-- The atlas constructed from local inverses of a quotient covering is a
smooth manifold atlas when every group translate is smooth. This supplies
the smooth-quotient bridge missing from the pinned charted-space instance. -/
theorem isManifold_quotientChartedSpace {r : X → E} (hr : RightInverse r p) :
    letI := hp.isCoveringMap.isLocalHomeomorph.chartedSpaceOfRightInverse (H := V) hr
    IsManifold 𝓘(ℝ, V) n X := by
  let hf := hp.isCoveringMap.isLocalHomeomorph
  letI := hf.chartedSpaceOfRightInverse (H := V) hr
  apply isManifold_of_contDiffOn 𝓘(ℝ, V) n X
  intro e e' he he'
  change ∃ a : X, (hf.localInverseAt (r a)).trans (chartAt V (r a)) = e at he
  change ∃ b : X, (hf.localInverseAt (r b)).trans (chartAt V (r b)) = e' at he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    id_comp, comp_id, range_id, inter_univ]
  apply ContMDiffOn.contDiffOn
  intro v hv
  let ca := chartAt V (r a)
  let cb := chartAt V (r b)
  let sa := hf.localInverseAt (r a)
  let sb := hf.localInverseAt (r b)
  have hsap (w : V) : (sa.trans ca).symm w = p (ca.symm w) := by
    change sa.symm (ca.symm w) = p (ca.symm w)
    exact congrFun (hf.localInverseAt_symm (r a)) _
  have hca : v ∈ ca.target := hv.1.1
  have hsb : p (ca.symm v) ∈ sb.source := by
    have h : (sa.trans ca).symm v ∈ sb.source := hv.2.1
    rwa [hsap] at h
  have hcb : sb (p (ca.symm v)) ∈ cb.source := by
    have h : sb ((sa.trans ca).symm v) ∈ cb.source := hv.2.2
    rwa [hsap] at h
  have hbranch := contMDiffAt_localBranch_comp_projection hp hsmul sb
    (hf.localInverseAt_symm (r b)) hsb
  have hinner := hbranch.comp v
    (contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (r a)) hca)
  have hout := (contMDiffAt_of_mem_maximalAtlas
    (chart_mem_maximalAtlas (r b)) hcb).comp v hinner
  convert! hout.contMDiffWithinAt using 1
  ext w
  change cb (sb ((sa.trans ca).symm w)) = cb (sb (p (ca.symm w)))
  rw [hsap]

/-- The quotient projection is smooth for the atlas built from its local
inverse branches. Its smoothness is a conclusion, not an input. -/
theorem contMDiff_quotientProjection {r : X → E} (hr : RightInverse r p) :
    letI := hp.isCoveringMap.isLocalHomeomorph.chartedSpaceOfRightInverse (H := V) hr
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) n p := by
  let hf := hp.isCoveringMap.isLocalHomeomorph
  letI := hf.chartedSpaceOfRightInverse (H := V) hr
  intro x
  apply contMDiffAt_iff_target.mpr
  refine ⟨hp.continuous.continuousAt, ?_⟩
  let s := hf.localInverseAt (r (p x))
  let c := chartAt V (r (p x))
  have hx : p x ∈ s.source := by
    rw [← hr (p x)]
    exact hf.apply_self_mem_localInverseAt_source
  have hbase : s (p x) = r (p x) := by
    change hf.localInverseAt (r (p x)) (p x) = r (p x)
    nth_rw 2 [← hr (p x)]
    exact hf.localInverseAt_apply_self
  have hc : s (p x) ∈ c.source := by
    rw [hbase]
    exact mem_chart_source V (r (p x))
  have hbranch := contMDiffAt_localBranch_comp_projection hp hsmul s
    (hf.localInverseAt_symm (r (p x))) hx
  change ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V) n (fun z => c (s (p z))) x
  exact (contMDiffAt_of_mem_maximalAtlas
    (chart_mem_maximalAtlas (r (p x))) hc).comp x hbranch

/-- Every local inverse of the quotient projection is smooth on its source
for the constructed quotient atlas. -/
theorem contMDiffOn_quotientLocalInverse {r : X → E} (hr : RightInverse r p)
    (s : OpenPartialHomeomorph X E) (hs : (s.symm : E → X) = p) :
    letI := hp.isCoveringMap.isLocalHomeomorph.chartedSpaceOfRightInverse (H := V) hr
    ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) n s s.source := by
  let hf := hp.isCoveringMap.isLocalHomeomorph
  letI := hf.chartedSpaceOfRightInverse (H := V) hr
  intro z hz
  suffices ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V) n s z from this.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  let c := chartAt V (r z)
  let v := c (r z)
  have hv : v ∈ c.target := c.map_source (mem_chart_source V (r z))
  have hcv : c.symm v = r z := c.left_inv (mem_chart_source V (r z))
  have hbase : extChartAt 𝓘(ℝ, V) z z = v := by
    change c (hf.localInverseAt (r z) z) = c (r z)
    nth_rw 2 [← hr z]
    rw [hf.localInverseAt_apply_self]
  have hps : p (c.symm v) ∈ s.source := by simpa only [hcv, hr z] using hz
  have hbranch := contMDiffAt_localBranch_comp_projection hp hsmul s hs hps
  have hcomp := hbranch.comp v
    (contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (r z)) hv)
  rw [hbase]
  convert! hcomp.contMDiffWithinAt using 1
  ext w
  change s ((hf.localInverseAt (r z)).symm (c.symm w)) = s (p (c.symm w))
  rw [hf.localInverseAt_symm]

/-- The smooth quotient projection is locally a diffeomorphism, with its
actual topological local inverse as the smooth inverse. -/
theorem isLocalDiffeomorph_quotientProjection {r : X → E} (hr : RightInverse r p) :
    letI := hp.isCoveringMap.isLocalHomeomorph.chartedSpaceOfRightInverse (H := V) hr
    IsLocalDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, V) n p := by
  let hf := hp.isCoveringMap.isLocalHomeomorph
  letI := hf.chartedSpaceOfRightInverse (H := V) hr
  have hpSmooth := contMDiff_quotientProjection hp hsmul hr
  intro x
  let s := hf.localInverseAt x
  refine ⟨{
    toPartialEquiv := s.symm.toPartialEquiv
    open_source := s.open_target
    open_target := s.open_source
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_
  }, hf.self_mem_localInverseAt_target, ?_⟩
  · change ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) n (s.symm : E → X) s.target
    rw [hf.localInverseAt_symm]
    exact hpSmooth.contMDiffOn
  · exact contMDiffOn_quotientLocalInverse hp hsmul hr s (hf.localInverseAt_symm x)
  · intro y _
    exact (congrFun (hf.localInverseAt_symm x) y).symm

end LocalBranches

section FiniteSmoothAction

variable (G : Type*) [Group G] [Finite G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {E : Type*} [TopologicalSpace E] [ChartedSpace V E]
  [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  [LocallyCompactSpace E] [T2Space E]
  {n : ℕ∞ω} [IsManifold 𝓘(ℝ, V) n E]
  (hsmul : ∀ g : G, ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) n (fun x : E => g • x))

include hsmul

/-- The existing orbit-quotient charted-space instance is a smooth manifold
for a finite free smooth action. -/
theorem finiteSmoothAction_isManifold :
    IsManifold 𝓘(ℝ, V) n (MulAction.orbitRel.Quotient G E) :=
  isManifold_quotientChartedSpace
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := E))
    hsmul (Quotient.mk_surjective.hasRightInverse.choose_spec)

/-- The actual orbit projection is a local diffeomorphism. -/
theorem finiteSmoothAction_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, V) n (Quotient.mk (MulAction.orbitRel G E)) :=
  isLocalDiffeomorph_quotientProjection
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := E))
    hsmul (Quotient.mk_surjective.hasRightInverse.choose_spec)

/-- The projection onto a simply connected finite free smooth quotient of a
path-connected manifold is a diffeomorphism for its canonical quotient atlas. -/
noncomputable def finiteSmoothActionQuotientDiffeomorph [PathConnectedSpace E]
    [SimplyConnectedSpace (MulAction.orbitRel.Quotient G E)] :
    E ≃ₘ^n⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ MulAction.orbitRel.Quotient G E :=
  (finiteSmoothAction_isLocalDiffeomorph G hsmul).diffeomorphOfBijective
    (quotientCovering_bijective
      (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := E)))

end FiniteSmoothAction

section Sphere

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

/-- A simply connected spherical space form is diffeomorphic to the standard
three-sphere. The group is proved trivial before smoothness is invoked, so
even continuity (rather than a supplied smoothness witness) of the action is
sufficient. The quotient has Mathlib's canonical orbit atlas. -/
noncomputable def sphere3QuotientDiffeomorph
    (G : Type*) [Group G] [Finite G] [MulAction G Sphere3]
    [ContinuousConstSMul G Sphere3] [IsCancelSMul G Sphere3]
    [SimplyConnectedSpace (MulAction.orbitRel.Quotient G Sphere3)] :
    MulAction.orbitRel.Quotient G Sphere3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3 := by
  letI := finiteAction_group_subsingleton G Sphere3
  have hsmul : ∀ g : G, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : Sphere3 => g • x) := by
    intro g
    have hg : g = 1 := Subsingleton.elim _ _
    have hid : (fun x : Sphere3 => g • x) = id := by
      funext x
      simp only [hg, one_smul, id_eq]
    rw [hid]
    exact contMDiff_id
  exact (finiteSmoothActionQuotientDiffeomorph G hsmul).symm

/-- Presentation-independent spherical-space-form elimination, with a smooth
presentation into the actual finite free orbit quotient. -/
theorem diffeomorph_sphere3_of_finite_quotient
    (G : Type*) [Group G] [Finite G] [MulAction G Sphere3]
    [ContinuousConstSMul G Sphere3] [IsCancelSMul G Sphere3]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M]
    (e : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ MulAction.orbitRel.Quotient G Sphere3) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3) := by
  letI : SimplyConnectedSpace (MulAction.orbitRel.Quotient G Sphere3) :=
    e.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  exact ⟨e.trans (sphere3QuotientDiffeomorph G)⟩

end Sphere

end PoincareConjecture
