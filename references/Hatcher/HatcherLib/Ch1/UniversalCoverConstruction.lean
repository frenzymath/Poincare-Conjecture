import HatcherLib.Ch1.CoveringClassification
import HatcherLib.Ch1.Contractible
import Mathlib.Topology.Subpath
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Chapter 1: construction of the universal covering space

For a basepoint `x₀`, the fiber over `x` consists of endpoint-preserving
homotopy classes of paths from `x₀` to `x`. Semilocal simple connectedness and
local path connectedness provide trivializing neighborhoods on which these
classes vary discretely. The resulting fiber prebundle equips the path-class
total space with a topology whose endpoint projection is a covering map.

Simple connectedness of the total space is proved separately from this
covering-space construction.
-/

namespace HatcherLib

namespace UniversalCoverConstruction

noncomputable section

open CategoryTheory
open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The path-homotopy classes from the chosen basepoint to a varying endpoint. -/
abbrev Fiber (x₀ x : X) := Path.Homotopic.Quotient x₀ x

/-- The discrete topology used on path-class fibers while building the cover. -/
@[implicit_reducible]
def fiberTopology (x₀ x : X) : TopologicalSpace (Fiber x₀ x) := ⊥

local instance fiberTopologicalSpace (x₀ x : X) : TopologicalSpace (Fiber x₀ x) :=
  fiberTopology x₀ x

local instance fiberDiscreteTopology (x₀ x : X) : DiscreteTopology (Fiber x₀ x) :=
  discreteTopology_bot _

/-- The total space of endpoint-indexed path-homotopy classes. -/
abbrev Space (x₀ : X) := Bundle.TotalSpace (Fiber x₀ x₀) (Fiber x₀)

/-- The endpoint projection from the path-class total space. -/
def endpoint {x₀ : X} : Space x₀ → X := Bundle.TotalSpace.proj

def pathInSet {U : Set X} (hU : IsPathConnected U) (a b : U) : Path a b where
  toFun t := ⟨(hU.joinedIn a a.2 b b.2).somePath t,
    (hU.joinedIn a a.2 b b.2).somePath_mem t⟩
  continuous_toFun := (hU.joinedIn a a.2 b b.2).somePath.continuous.subtype_mk _
  source' := Subtype.ext (hU.joinedIn a a.2 b b.2).somePath.source
  target' := Subtype.ext (hU.joinedIn a a.2 b b.2).somePath.target

def pathInSetVal {U : Set X} (hU : IsPathConnected U) (a b : U) : Path a.1 b.1 :=
  (pathInSet hU a b).map continuous_subtype_val

def chartPath [PathConnectedSpace X] {U : Set X} (hU : IsPathConnected U)
    (a : U) (y : X) : Path a.1 y := by
  classical
  exact if hy : y ∈ U then pathInSetVal hU a ⟨y, hy⟩
    else PathConnectedSpace.somePath a.1 y

def globalPath [PathConnectedSpace X] (x₀ x : X) : Path x₀ x :=
  PathConnectedSpace.somePath x₀ x

def chartToFun [PathConnectedSpace X] {x₀ : X} {U : Set X}
    (hU : IsPathConnected U) (a : U) (z : Space x₀) : X × Fiber x₀ x₀ :=
  (z.1, (z.2.trans (.mk (chartPath hU a z.1).symm)).trans
    (.mk (globalPath x₀ a.1).symm))

def chartInvFun [PathConnectedSpace X] {x₀ : X} {U : Set X}
    (hU : IsPathConnected U) (a : U) (z : X × Fiber x₀ x₀) : Space x₀ :=
  ⟨z.1, (z.2.trans (.mk (globalPath x₀ a.1))).trans (.mk (chartPath hU a z.1))⟩

def chartPartialEquiv [PathConnectedSpace X] {x₀ : X} {U : Set X}
    (hU : IsPathConnected U) (a : U) : PartialEquiv (Space x₀) (X × Fiber x₀ x₀) where
  toFun := chartToFun hU a
  invFun := chartInvFun hU a
  source := endpoint ⁻¹' U
  target := U ×ˢ (Set.univ : Set (Fiber x₀ x₀))
  map_source' z hz := by exact ⟨hz, Set.mem_univ _⟩
  map_target' z hz := by exact hz.1
  left_inv' z hz := by
    apply Bundle.TotalSpace.ext
    · rfl
    have hz' : z.1 ∈ U := hz
    apply heq_of_eq
    obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective z.snd
    simp [chartInvFun, chartToFun, chartPath, hz']
  right_inv' z hz := by
    apply Prod.ext
    · rfl
    · simp only [chartInvFun, chartToFun]
      simp

def chartPretrivialization [PathConnectedSpace X] {x₀ : X} {U : Set X}
    (hUo : IsOpen U) (hU : IsPathConnected U) (a : U) :
    Bundle.Pretrivialization (Fiber x₀ x₀) (endpoint (x₀ := x₀)) where
  toPartialEquiv := chartPartialEquiv hU a
  open_target := hUo.prod isOpen_univ
  baseSet := U
  open_baseSet := hUo
  source_eq := rfl
  target_eq := rfl
  proj_toFun := by
    intro z hz
    by_cases h : z ∈ endpoint ⁻¹' U
    · rfl
    · exact (h hz).elim

theorem cancel_conjugated_loop {C : Type*} [Groupoid C] {a b c : C}
    (r : a ⟶ b) (p q : b ⟶ c)
    (h : ((r ≫ p) ≫ Groupoid.inv q) ≫ Groupoid.inv r = 𝟙 a) : p = q := by
  apply (cancel_epi r).1
  apply (cancel_mono (Groupoid.inv q)).1
  have h' := congrArg (fun k ↦ k ≫ r) h
  simpa only [Category.assoc, Groupoid.inv_comp, Groupoid.comp_inv, Category.comp_id,
    Category.id_comp] using h'

/-- An open path-connected set on which all paths with fixed endpoints are
homotopic after inclusion into the base. -/
def IsTrivializing (U : Set X) : Prop :=
  IsOpen U ∧ IsPathConnected U ∧
    ∀ (a b : U) (p q : Path a b),
      Path.Homotopic.Quotient.mk (p.map continuous_subtype_val) =
        Path.Homotopic.Quotient.mk (q.map continuous_subtype_val)

theorem isTrivializing_of_range_eq_bot {U : Set X} (hUo : IsOpen U)
    (hU : IsPathConnected U) (a : U)
    (hπ : (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) a).range = ⊥) :
    IsTrivializing U := by
  refine ⟨hUo, hU, ?_⟩
  intro b c p q
  let r : Path a b := pathInSet hU a b
  let loop : Path a a := ((r.trans p).trans q.symm).trans r.symm
  have hmem : FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) a
        (FundamentalGroup.fromPath (.mk loop)) ∈
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) a).range :=
    ⟨_, rfl⟩
  rw [hπ] at hmem
  have hmem' : FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) a
        (FundamentalGroup.fromPath (.mk loop)) = 1 := by
    simpa only [Subgroup.mem_bot] using hmem
  have hloop :
      Path.Homotopic.Quotient.mk (loop.map continuous_subtype_val) =
        Path.Homotopic.Quotient.refl a.1 := by
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map] at hmem'
    exact hmem'
  let R : Path.Homotopic.Quotient a.1 b.1 :=
    .mk (r.map continuous_subtype_val)
  let P : Path.Homotopic.Quotient b.1 c.1 :=
    .mk (p.map continuous_subtype_val)
  let Q : Path.Homotopic.Quotient b.1 c.1 :=
    .mk (q.map continuous_subtype_val)
  have hQsymm : Path.Homotopic.Quotient.mk
      (q.symm.map continuous_subtype_val) = Q.symm := by
    rw [← Path.map_symm]
    rfl
  have hRsymm : Path.Homotopic.Quotient.mk
      (r.symm.map continuous_subtype_val) = R.symm := by
    rw [← Path.map_symm]
    rfl
  have hloop' : ((R.trans P).trans Q.symm).trans R.symm =
      Path.Homotopic.Quotient.refl a.1 := by
    simpa only [loop, Path.map_trans, Path.Homotopic.Quotient.mk_trans,
      hQsymm, hRsymm] using hloop
  let R' : FundamentalGroupoid.mk a.1 ⟶ FundamentalGroupoid.mk b.1 := R
  let P' : FundamentalGroupoid.mk b.1 ⟶ FundamentalGroupoid.mk c.1 := P
  let Q' : FundamentalGroupoid.mk b.1 ⟶ FundamentalGroupoid.mk c.1 := Q
  have hloop'' : ((R' ≫ P') ≫ Groupoid.inv Q') ≫ Groupoid.inv R' = 𝟙 _ := hloop'
  exact cancel_conjugated_loop R' P' Q' hloop''

theorem inclusion_range_eq_bot_mono {U V : Set X} (hUV : U ⊆ V)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V)
    (hV : (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) ⟨x, hxV⟩).range = ⊥) :
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hxU⟩).range = ⊥ := by
  apply le_antisymm
  · rintro z ⟨g, rfl⟩
    let iUV : C(U, V) :=
      ⟨fun y ↦ ⟨y.1, hUV y.2⟩, continuous_subtype_val.subtype_mk _⟩
    have hzV : FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hxU⟩ g ∈
        (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) ⟨x, hxV⟩).range := by
      refine ⟨FundamentalGroup.map iUV ⟨x, hxU⟩ g, ?_⟩
      obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective
        (FundamentalGroup.toPath g)
      have hg : g = FundamentalGroup.fromPath (.mk γ) := hγ.symm
      rw [hg]
      rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply,
        FundamentalGroup.map_apply,
        ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_map]
      rfl
    rw [hV] at hzV
    exact hzV
  · exact bot_le

theorem exists_isTrivializing_subset [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x : X)
    {S : Set X} (hS : S ∈ nhds x) :
    ∃ U : Set X, x ∈ U ∧ IsTrivializing U ∧ U ⊆ S := by
  rcases hsemi x with ⟨V, hVnhds, hxV, hVπ⟩
  rcases (isOpen_isPathConnected_basis x).mem_iff.mp (Filter.inter_mem hVnhds hS) with
    ⟨U, ⟨hUo, hxU, hUpc⟩, hUVS⟩
  refine ⟨U, hxU, ?_, hUVS.trans Set.inter_subset_right⟩
  apply isTrivializing_of_range_eq_bot hUo hUpc ⟨x, hxU⟩
  exact inclusion_range_eq_bot_mono
    (hUVS.trans Set.inter_subset_left) hxU hxV hVπ

theorem chartPathClass_trans [PathConnectedSpace X] {U : Set X} (hU : IsTrivializing U) (a : U)
    {y z : X} (hy : y ∈ U) (hz : z ∈ U)
    (d : Path (⟨y, hy⟩ : U) ⟨z, hz⟩) :
    Path.Homotopic.Quotient.mk (chartPath hU.2.1 a z) =
      (Path.Homotopic.Quotient.mk (chartPath hU.2.1 a y)).trans
        (.mk (d.map continuous_subtype_val)) := by
  have h := hU.2.2 a ⟨z, hz⟩ (pathInSet hU.2.1 a ⟨z, hz⟩)
    ((pathInSet hU.2.1 a ⟨y, hy⟩).trans d)
  simpa [chartPath, hy, hz, pathInSetVal, Path.map_trans] using h

theorem transition_const_of_path {C : Type*} [Groupoid C]
    {o a b y z : C} (g : o ⟶ o) (ab : o ⟶ a) (aa : o ⟶ b)
    (By : a ⟶ y) (Bz : a ⟶ z) (Ay : b ⟶ y) (Az : b ⟶ z) (D : y ⟶ z)
    (hB : Bz = By ≫ D) (hA : Az = Ay ≫ D) :
    (((g ≫ ab) ≫ Bz) ≫ Groupoid.inv Az) ≫ Groupoid.inv aa =
      (((g ≫ ab) ≫ By) ≫ Groupoid.inv Ay) ≫ Groupoid.inv aa := by
  rw [hB, hA]
  simp only [Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_comp,
    IsIso.hom_inv_id_assoc]

theorem quotient_symm_eq_groupoid_inv {x y : X}
    (p : Path.Homotopic.Quotient x y) :
    p.symm = (Groupoid.inv p : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk x) := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk q => rfl

/-- Chart data for the path-class covering over a trivializing neighborhood. -/
structure Chart (x₀ : X) [PathConnectedSpace X] where
  U : Set X
  hU : IsTrivializing U
  a : U

def transitionFiber [PathConnectedSpace X] {x₀ : X}
    (i j : Chart x₀) (x : X) (g : Fiber x₀ x₀) : Fiber x₀ x₀ :=
  (chartToFun i.hU.2.1 i.a (chartInvFun j.hU.2.1 j.a (x, g))).2

theorem transitionFiber_eq_formula [PathConnectedSpace X] {x₀ : X}
    (i j : Chart x₀) {x : X} (hxi : x ∈ i.U) (hxj : x ∈ j.U) (g : Fiber x₀ x₀) :
    transitionFiber i j x g =
      (((g.trans (.mk (globalPath x₀ j.a.1))).trans
        (.mk (chartPath j.hU.2.1 j.a x))).trans
        (.mk (chartPath i.hU.2.1 i.a x).symm)).trans
          (.mk (globalPath x₀ i.a.1).symm) := by
  simp [transitionFiber, chartToFun, chartInvFun, chartPath, hxi, hxj]

theorem transitionFiber_const_of_path [PathConnectedSpace X] {x₀ : X}
    (i j : Chart x₀) {W : Set X}
    (hWi : W ⊆ i.U) (hWj : W ⊆ j.U) {y z : X}
    (hy : y ∈ W) (hz : z ∈ W) (d : Path (⟨y, hy⟩ : W) ⟨z, hz⟩)
    (g : Fiber x₀ x₀) : transitionFiber i j y g = transitionFiber i j z g := by
  let d_i : Path (⟨y, hWi hy⟩ : i.U) ⟨z, hWi hz⟩ := by
    let m : C(W, i.U) := ⟨fun q ↦ ⟨q.1, hWi q.2⟩, continuous_subtype_val.subtype_mk _⟩
    exact d.map m.continuous
  let d_j : Path (⟨y, hWj hy⟩ : j.U) ⟨z, hWj hz⟩ := by
    let m : C(W, j.U) := ⟨fun q ↦ ⟨q.1, hWj q.2⟩, continuous_subtype_val.subtype_mk _⟩
    exact d.map m.continuous
  have hi := chartPathClass_trans i.hU i.a (hWi hy) (hWi hz) d_i
  have hj := chartPathClass_trans j.hU j.a (hWj hy) (hWj hz) d_j
  rw [transitionFiber_eq_formula i j (hWi hy) (hWj hy) g,
    transitionFiber_eq_formula i j (hWi hz) (hWj hz) g]
  let R : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk j.a.1 :=
    .mk (globalPath x₀ j.a.1)
  let A : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₀ := g
  let B : FundamentalGroupoid.mk j.a.1 ⟶ FundamentalGroupoid.mk y :=
    .mk (chartPath j.hU.2.1 j.a y)
  let Bz : FundamentalGroupoid.mk j.a.1 ⟶ FundamentalGroupoid.mk z :=
    .mk (chartPath j.hU.2.1 j.a z)
  let C : FundamentalGroupoid.mk i.a.1 ⟶ FundamentalGroupoid.mk y :=
    .mk (chartPath i.hU.2.1 i.a y)
  let Cz : FundamentalGroupoid.mk i.a.1 ⟶ FundamentalGroupoid.mk z :=
    .mk (chartPath i.hU.2.1 i.a z)
  let S : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z :=
    .mk (d.map continuous_subtype_val)
  let AA : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk i.a.1 :=
    .mk (globalPath x₀ i.a.1)
  have hdjPath : d_j.map continuous_subtype_val = d.map continuous_subtype_val := by
    ext t
    change (d_j t : X) = d t
    rfl
  have hdiPath : d_i.map continuous_subtype_val = d.map continuous_subtype_val := by
    ext t
    change (d_i t : X) = d t
    rfl
  have hdj : Path.Homotopic.Quotient.mk (d_j.map continuous_subtype_val) =
      Path.Homotopic.Quotient.mk (d.map continuous_subtype_val) := congrArg _ hdjPath
  have hdi : Path.Homotopic.Quotient.mk (d_i.map continuous_subtype_val) =
      Path.Homotopic.Quotient.mk (d.map continuous_subtype_val) := congrArg _ hdiPath
  have hj' : Bz = B ≫ S := by
    change Bz = B.trans S
    simpa only [Bz, B, S, hdj] using hj
  have hi' : Cz = C ≫ S := by
    change Cz = C.trans S
    simpa only [Cz, C, S, hdi] using hi
  simp only [Path.Homotopic.Quotient.mk_symm, quotient_symm_eq_groupoid_inv]
  exact (transition_const_of_path A R AA B Bz C Cz S hj' hi').symm

def chartPretriv [PathConnectedSpace X] {x₀ : X} (i : Chart x₀) :
    Bundle.Pretrivialization (Fiber x₀ x₀) (endpoint (x₀ := x₀)) :=
  chartPretrivialization i.hU.1 i.hU.2.1 i.a

def chartTransition [PathConnectedSpace X] {x₀ : X} (i j : Chart x₀) :
    (X × Fiber x₀ x₀) → (X × Fiber x₀ x₀) :=
  chartPretriv i ∘ (chartPretriv j).toPartialEquiv.symm

theorem chartTransition_continuousOn [PathConnectedSpace X] [LocallyPathConnectedSpace X] {x₀ : X}
    (i j : Chart x₀) :
    ContinuousOn (chartTransition i j)
      ((chartPretriv j).target ∩ (chartPretriv j).toPartialEquiv.symm ⁻¹'
        (chartPretriv i).source) := by
  rw [continuousOn_prod_of_discrete_right]
  intro g
  simp only [chartTransition, Function.comp_apply]
  have hfun : (fun x ↦ (chartPretriv i)
      ((chartPretriv j).toPartialEquiv.symm (x, g))) =
      (fun x ↦ (x, transitionFiber i j x g)) := by
    funext x
    apply Prod.ext
    · rfl
    · rfl
  have hset : {a | (a, g) ∈ (chartPretriv j).target ∩
      (chartPretriv j).toPartialEquiv.symm ⁻¹' (chartPretriv i).source} =
      i.U ∩ j.U := by
    ext x
    simp [chartPretriv, chartPretrivialization, chartPartialEquiv,
      endpoint, chartInvFun, and_comm]
  rw [hfun, hset]
  refine continuous_id.continuousOn.prodMk ?_
  rw [continuousOn_iff_continuous_restrict]
  apply (IsLocallyConstant.iff_continuous _).1
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  rcases (isOpen_isPathConnected_basis y.1).mem_iff.mp
      ((i.hU.1.inter j.hU.1).mem_nhds y.2) with ⟨T, ⟨hTo, hyT, hTpc⟩, hTij⟩
  refine ⟨Subtype.val ⁻¹' T, hTo.preimage continuous_subtype_val, hyT, ?_⟩
  intro z hz
  exact (transitionFiber_const_of_path i j
    (hTij.trans Set.inter_subset_left) (hTij.trans Set.inter_subset_right)
    hyT hz (pathInSet hTpc ⟨y.1, hyT⟩ ⟨z.1, hz⟩) g).symm

def chooseChart [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsemi : HatcherLib.SemilocallySimplyConnected X) (x₀ x : X) : Chart x₀ := by
  classical
  let U := Classical.choose (exists_isTrivializing_subset hsemi x (Filter.univ_mem))
  have hU := (Classical.choose_spec
    (exists_isTrivializing_subset hsemi x (Filter.univ_mem))).2.1
  have hxU : x ∈ U := (Classical.choose_spec
    (exists_isTrivializing_subset hsemi x (Filter.univ_mem))).1
  exact ⟨U, hU, ⟨x, hxU⟩⟩

/-- The path-class fiber prebundle assembled from chosen trivializing
neighborhoods. -/
def universalPrebundle [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {x₀ : X} (hsemi : HatcherLib.SemilocallySimplyConnected X) :
    FiberPrebundle (Fiber x₀ x₀) (Fiber x₀) where
  pretrivializationAtlas := Set.range chartPretriv
  pretrivializationAt := fun x ↦ chartPretriv (chooseChart hsemi x₀ x)
  mem_base_pretrivializationAt := by
    intro x
    exact (chooseChart hsemi x₀ x).a.2
  pretrivialization_mem_atlas := fun x ↦ ⟨chooseChart hsemi x₀ x, rfl⟩
  continuous_trivChange := by
    intro e he e' he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    exact chartTransition_continuousOn i j
  totalSpaceMk_isInducing := by
    intro b
    let i := chooseChart hsemi x₀ b
    let f : Fiber x₀ b → X × Fiber x₀ x₀ :=
      chartPretriv i ∘ Bundle.TotalSpace.mk b
    let inv : X × Fiber x₀ x₀ → Fiber x₀ b := fun z =>
      (chartInvFun i.hU.2.1 i.a (b, z.2)).2
    have hinv : Function.LeftInverse inv f := by
      intro g
      have hba : i.a.1 = b := by rfl
      have hb : b ∈ i.U := hba ▸ i.a.2
      have hsource : Bundle.TotalSpace.mk b g ∈ (chartPretriv i).source := by
        change b ∈ i.U
        exact hb
      have hleft := (chartPretriv i).toPartialEquiv.left_inv hsource
      change (chartInvFun i.hU.2.1 i.a (b, (f g).2)).2 = g
      rw [show f g = (chartPretriv i) (Bundle.TotalSpace.mk b g) by rfl]
      exact Bundle.TotalSpace.mk_inj.mp hleft
    have hf : Continuous f := continuous_of_discreteTopology
    have hinv_cont : Continuous inv := by
      let phi : Fiber x₀ x₀ → Fiber x₀ b := fun g =>
        (chartInvFun i.hU.2.1 i.a (b, g)).2
      have hphi : Continuous phi := continuous_of_discreteTopology
      change Continuous (fun z : X × Fiber x₀ x₀ => phi z.2)
      exact hphi.comp continuous_snd
    exact (hinv.isEmbedding hinv_cont hf).isInducing

/-- The topology on the path-class total space generated by its local product
charts. -/
@[implicit_reducible]
def universalCoverTopology [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {x₀ : X} (hsemi : HatcherLib.SemilocallySimplyConnected X) :
    TopologicalSpace (Space x₀) :=
  (universalPrebundle hsemi).totalSpaceTopology

/-- The endpoint projection of the path-class construction is a covering map. -/
theorem universalCoverEndpoint_isCoveringMap [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] {x₀ : X}
    (hsemi : HatcherLib.SemilocallySimplyConnected X) :
    @CoveringMap (Space x₀) X (universalCoverTopology hsemi) inferInstance endpoint := by
  let a : FiberPrebundle (Fiber x₀ x₀) (Fiber x₀) := universalPrebundle (x₀ := x₀) hsemi
  letI : TopologicalSpace (Space x₀) := a.totalSpaceTopology
  letI : FiberBundle (Fiber x₀ x₀) (Fiber x₀) := a.toFiberBundle
  exact FiberBundle.isCoveringMap

/-! ## Canonical lifts in the path-class cover -/

/-- The straight path in the parameter interval from `s` to `t`. -/
def intervalSegment (s t : unitInterval) : Path s t where
  toFun := Set.Icc.convexComb s t
  continuous_toFun := Set.Icc.continuous_convexComb s t
  source' := Set.Icc.convexComb_zero s t
  target' := Set.Icc.convexComb_one s t

/-- The class of the initial segment of a path, with its source transported to
the declared source of the path. -/
def prefixPathClass {x y : X} (γ : Path x y) (t : unitInterval) :
    Path.Homotopic.Quotient x (γ t) :=
  (Path.Homotopic.Quotient.mk (γ.subpath 0 t)).cast γ.source.symm rfl

/-- Appending initial segments of `γ` to a path class gives the canonical lift
of `γ` to the path-class total space. -/
def pathClassLift {x₀ x y : X} (g : Fiber x₀ x) (γ : Path x y)
    (t : unitInterval) : Space x₀ :=
  ⟨γ t, g.trans (prefixPathClass γ t)⟩

private theorem quotient_cast_trans_left {a a' b c : X}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c)
    (h : a' = a) :
    (p.trans q).cast h rfl = (p.cast h rfl).trans q := by
  subst a'
  simp

/-- Initial path classes compose according to subdivision of the interval. -/
theorem prefixPathClass_trans {x y : X} (γ : Path x y) (s t : unitInterval) :
    prefixPathClass γ t =
      (prefixPathClass γ s).trans (.mk (γ.subpath s t)) := by
  have hraw : Path.Homotopic.Quotient.mk (γ.subpath 0 t) =
      (Path.Homotopic.Quotient.mk (γ.subpath 0 s)).trans
        (.mk (γ.subpath s t)) := by
    rw [← Path.Homotopic.Quotient.mk_trans]
    apply Quotient.sound
    exact ⟨(Path.Homotopy.subpathTransSubpath γ 0 s t).symm⟩
  unfold prefixPathClass
  rw [hraw, quotient_cast_trans_left]

private theorem quotient_trans_assoc {a b c d : X}
    (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c)
    (r : Path.Homotopic.Quotient c d) :
    p.trans (q.trans r) = (p.trans q).trans r := by
  let P : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := p
  let Q : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk c := q
  let R : FundamentalGroupoid.mk c ⟶ FundamentalGroupoid.mk d := r
  change P ≫ (Q ≫ R) = (P ≫ Q) ≫ R
  simp

/-- Any path in the parameter interval gives the same subpath class after
mapping through `γ` as the straight parameter segment. -/
theorem subpathClass_eq_of_path {x y : X} (γ : Path x y)
    {W : Set unitInterval} {s t : unitInterval} (hs : s ∈ W) (ht : t ∈ W)
    (d : Path (⟨s, hs⟩ : W) ⟨t, ht⟩) :
    Path.Homotopic.Quotient.mk (γ.subpath s t) =
      Path.Homotopic.Quotient.mk
        ((d.map continuous_subtype_val).map γ.continuous) := by
  have hseg : Path.Homotopic (intervalSegment s t)
      (d.map continuous_subtype_val) :=
    convex_paths_homotopic (convex_Icc (0 : ℝ) 1)
      (Set.nonempty_Icc.mpr zero_le_one) _ _
  apply Quotient.sound
  have hmap := hseg.map (⟨γ, γ.continuous⟩ : C(unitInterval, X))
  change Path.Homotopic (γ.subpath s t)
    ((d.map continuous_subtype_val).map γ.continuous)
  have hsubpath : γ.subpath s t =
      (intervalSegment s t).map γ.continuous := by
    rfl
  rw [hsubpath]
  exact hmap

/-- In one covering chart, the fiber coordinate of the canonical lift is
constant along every parameter path that stays in the chart. -/
theorem pathClassLift_chartFiber_eq [PathConnectedSpace X]
    {x₀ x y : X} (i : Chart x₀) (g : Fiber x₀ x) (γ : Path x y)
    {s t : unitInterval} (hs : γ s ∈ i.U) (ht : γ t ∈ i.U)
    (d : Path (⟨γ s, hs⟩ : i.U) ⟨γ t, ht⟩)
    (hsub : Path.Homotopic.Quotient.mk (γ.subpath s t) =
      Path.Homotopic.Quotient.mk (d.map continuous_subtype_val)) :
    (chartToFun i.hU.2.1 i.a (pathClassLift g γ t)).2 =
      (chartToFun i.hU.2.1 i.a (pathClassLift g γ s)).2 := by
  have hprefix : prefixPathClass γ t =
      (prefixPathClass γ s).trans
        (.mk (d.map continuous_subtype_val)) := by
    rw [prefixPathClass_trans, hsub]
  have hchart := chartPathClass_trans i.hU i.a hs ht d
  simp only [chartToFun, pathClassLift, Path.Homotopic.Quotient.mk_symm]
  rw [hprefix, hchart, quotient_trans_assoc]
  let P' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk (γ s) :=
    g.trans (prefixPathClass γ s)
  let D' : FundamentalGroupoid.mk (γ s) ⟶ FundamentalGroupoid.mk (γ t) :=
    .mk (d.map continuous_subtype_val)
  let C' : FundamentalGroupoid.mk i.a.1 ⟶ FundamentalGroupoid.mk (γ s) :=
    .mk (chartPath i.hU.2.1 i.a (γ s))
  let A' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk i.a.1 :=
    .mk (globalPath x₀ i.a.1)
  change ((P' ≫ D') ≫ Groupoid.inv (C' ≫ D')) ≫ Groupoid.inv A' =
    (P' ≫ Groupoid.inv C') ≫ Groupoid.inv A'
  simp

/-- The canonical path-class lift is continuous for the topology assembled
from the path-class covering charts. -/
theorem pathClassLift_continuous [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {x₀ x y : X} (hsemi : HatcherLib.SemilocallySimplyConnected X)
    (g : Fiber x₀ x) (γ : Path x y) :
    @Continuous unitInterval (Space x₀) inferInstance
      (universalCoverTopology hsemi) (pathClassLift g γ) := by
  letI fiberTS (z : X) : TopologicalSpace (Fiber x₀ z) := fiberTopology x₀ z
  letI fiberDiscrete (z : X) : DiscreteTopology (Fiber x₀ z) := discreteTopology_bot _
  let a : FiberPrebundle (Fiber x₀ x₀) (Fiber x₀) :=
    universalPrebundle (x₀ := x₀) hsemi
  change @Continuous unitInterval (Space x₀) inferInstance
    a.totalSpaceTopology (pathClassLift g γ)
  letI : TopologicalSpace (Space x₀) := a.totalSpaceTopology
  letI : FiberBundle (Fiber x₀ x₀) (Fiber x₀) := a.toFiberBundle
  apply continuous_iff_continuousAt.2
  intro t
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨γ.continuous.continuousAt, ?_⟩
  let i : Chart x₀ := chooseChart hsemi x₀ (γ t)
  change ContinuousAt (fun s =>
    (chartToFun i.hU.2.1 i.a (pathClassLift g γ s)).2) t
  have htU : γ t ∈ i.U := by
    change γ t ∈ (chooseChart hsemi x₀ (γ t)).U
    exact (chooseChart hsemi x₀ (γ t)).a.2
  have hpreopen : IsOpen (γ ⁻¹' i.U) := i.hU.1.preimage γ.continuous
  letI : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  rcases (isOpen_isPathConnected_basis t).mem_iff.mp
      (hpreopen.mem_nhds htU) with ⟨W, ⟨hWo, htW, hWpc⟩, hWsub⟩
  apply Filter.EventuallyEq.continuousAt
  filter_upwards [hWo.mem_nhds htW] with r hr
  have htU' : γ t ∈ i.U := hWsub htW
  have hrU : γ r ∈ i.U := hWsub hr
  let dW : Path (⟨t, htW⟩ : W) ⟨r, hr⟩ :=
    pathInSet hWpc ⟨t, htW⟩ ⟨r, hr⟩
  let m : C(W, i.U) :=
    ⟨fun z => ⟨γ z.1, hWsub z.2⟩,
      (γ.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let dU : Path (⟨γ t, htU'⟩ : i.U) ⟨γ r, hrU⟩ :=
    dW.map m.continuous
  apply pathClassLift_chartFiber_eq i g γ htU' hrU dU
  have hsub := subpathClass_eq_of_path γ htW hr dW
  rw [hsub]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  rfl

private theorem quotient_trans_cast_refl_heq {x₀ x x' : X}
    (g : Path.Homotopic.Quotient x₀ x) (h : x = x') :
    g.trans ((Path.Homotopic.Quotient.refl x').cast h rfl) ≍ g := by
  subst x'
  simp

private theorem quotient_trans_cast_heq {x₀ x y y' : X}
    (g : Path.Homotopic.Quotient x₀ x)
    (q : Path.Homotopic.Quotient x y) (hx : x = x) (hy : y' = y) :
    g.trans (q.cast hx hy) ≍ g.trans q := by
  subst y'
  simp

/-- The canonical lift starts at its specified path class. -/
theorem pathClassLift_zero {x₀ x y : X} (g : Fiber x₀ x) (γ : Path x y) :
    pathClassLift g γ 0 = ⟨x, g⟩ := by
  apply Bundle.TotalSpace.ext
  · exact γ.source
  · simp only [pathClassLift, prefixPathClass, Path.subpath_self,
      Path.Homotopic.Quotient.mk_refl]
    exact quotient_trans_cast_refl_heq g γ.source.symm

/-- The canonical lift ends at the class obtained by appending the lifted
path. -/
theorem pathClassLift_one {x₀ x y : X} (g : Fiber x₀ x) (γ : Path x y) :
    pathClassLift g γ 1 = ⟨y, g.trans (.mk γ)⟩ := by
  apply Bundle.TotalSpace.ext
  · exact γ.target
  · simp only [pathClassLift, prefixPathClass, Path.subpath_zero_one,
      Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.cast_cast]
    exact quotient_trans_cast_heq g (.mk γ) _ _

/-- Monodromy in the path-class covering appends the traversed path class. -/
theorem universalCoverEndpoint_monodromy [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] {x₀ x y : X}
    (hsemi : HatcherLib.SemilocallySimplyConnected X)
    (g : Fiber x₀ x) (q : Path.Homotopic.Quotient x y) :
    letI : TopologicalSpace (Space x₀) := universalCoverTopology hsemi
    (universalCoverEndpoint_isCoveringMap hsemi).monodromy q
        ⟨⟨x, g⟩, rfl⟩ =
      ⟨⟨y, g.trans q⟩, rfl⟩ := by
  letI : TopologicalSpace (Space x₀) := universalCoverTopology hsemi
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ =>
    let cov := universalCoverEndpoint_isCoveringMap (x₀ := x₀) hsemi
    let L : C(unitInterval, Space x₀) :=
      ⟨pathClassLift g γ, pathClassLift_continuous hsemi g γ⟩
    have hL : L = cov.liftPath γ ⟨x, g⟩ γ.source := by
      apply (cov.eq_liftPath_iff' γ.source).2
      refine ⟨?_, pathClassLift_zero g γ⟩
      funext t
      rfl
    apply Subtype.ext
    change cov.liftPath γ ⟨x, g⟩ γ.source 1 =
      ⟨y, g.trans (.mk γ)⟩
    rw [← hL]
    exact pathClassLift_one g γ

/-! ## Connectedness and the universal-cover theorem -/

/-- The path-class total space is locally path-connected because its endpoint
projection is a covering of a locally path-connected base. -/
theorem universalCover_locPathConnectedSpace [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] {x₀ : X}
    (hsemi : HatcherLib.SemilocallySimplyConnected X) :
    @LocallyPathConnectedSpace (Space x₀) (universalCoverTopology hsemi) := by
  letI : TopologicalSpace (Space x₀) := universalCoverTopology hsemi
  exact CoveringMap.locPathConnectedSpace (p := endpoint)
    (universalCoverEndpoint_isCoveringMap hsemi)

/-- The path-class total space is path-connected: a representative of each
point is itself a path from the constant-path class to that point. -/
theorem universalCover_pathConnectedSpace [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] {x₀ : X}
    (hsemi : HatcherLib.SemilocallySimplyConnected X) :
    @PathConnectedSpace (Space x₀) (universalCoverTopology hsemi) := by
  letI : TopologicalSpace (Space x₀) := universalCoverTopology hsemi
  let base : Space x₀ := ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩
  have fromBase (z : Space x₀) : Joined base z := by
    obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective z.2
    let p : Path base z :=
      { toFun := pathClassLift (Path.Homotopic.Quotient.refl x₀) γ
        continuous_toFun := pathClassLift_continuous hsemi _ γ
        source' := by
          simpa [base] using pathClassLift_zero
            (Path.Homotopic.Quotient.refl x₀) γ
        target' := by
          rw [pathClassLift_one, Path.Homotopic.Quotient.refl_trans, hγ] }
    exact ⟨p⟩
  rw [pathConnectedSpace_iff]
  refine ⟨⟨base⟩, ?_⟩
  intro z w
  exact (fromBase z).symm.trans (fromBase w)

/-- The path-class total space is simply connected. A loop projects to a class
`q` satisfying `g · q = g`; cancellation in the fundamental groupoid gives
`q = 1`, and injectivity for covering maps lifts the nullhomotopy. -/
theorem universalCover_simplyConnectedSpace [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] {x₀ : X}
    (hsemi : HatcherLib.SemilocallySimplyConnected X) :
    @SimplyConnectedSpace (Space x₀) (universalCoverTopology hsemi) := by
  letI : TopologicalSpace (Space x₀) := universalCoverTopology hsemi
  letI : PathConnectedSpace (Space x₀) := universalCover_pathConnectedSpace hsemi
  let cov := universalCoverEndpoint_isCoveringMap (x₀ := x₀) hsemi
  apply simply_connected_iff_loops_nullhomotopic.2
  refine ⟨inferInstance, ?_⟩
  rintro ⟨x, g⟩ γ
  rw [← Path.Homotopic.Quotient.eq]
  apply cov.injective_path_homotopic_map
  let projected : Path x x := γ.map cov.continuous
  let q : Path.Homotopic.Quotient x x := .mk projected
  have hqmap :
      (Path.Homotopic.Quotient.mk γ).map ⟨endpoint, cov.continuous⟩ = q := by
    rw [← Path.Homotopic.Quotient.mk_map]
    rfl
  have hm := universalCoverEndpoint_monodromy hsemi g q
  have hmap := cov.monodromy_map (Path.Homotopic.Quotient.mk γ)
  rw [hqmap] at hmap
  have htotal := congrArg Subtype.val (hm.symm.trans hmap)
  have htrans : g.trans q = g := Bundle.TotalSpace.mk_inj.mp htotal
  have hq : q = Path.Homotopic.Quotient.refl x := by
    let G : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := g
    let Q : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x := q
    apply (cancel_epi G).1
    change g.trans q = g.trans (Path.Homotopic.Quotient.refl x)
    rw [htrans]
    change G = G ≫ 𝟙 _
    simp
  change (Path.Homotopic.Quotient.mk γ).map ⟨endpoint, cov.continuous⟩ =
    (Path.Homotopic.Quotient.mk (Path.refl _)).map ⟨endpoint, cov.continuous⟩
  rw [hqmap, hq]
  rfl

/-- The endpoint projection is onto whenever the base is path-connected. -/
theorem universalCoverEndpoint_surjective [PathConnectedSpace X] (x₀ : X) :
    Function.Surjective (endpoint (x₀ := x₀)) := by
  intro x
  exact ⟨⟨x, Path.Homotopic.Quotient.mk (globalPath x₀ x)⟩, rfl⟩

/-- The path-class construction is a universal covering map. -/
theorem universalCoverEndpoint_isUniversalCoveringMap [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] {x₀ : X}
    (hsemi : HatcherLib.SemilocallySimplyConnected X) :
    @IsUniversalCoveringMap (Space x₀) X (universalCoverTopology hsemi)
      inferInstance endpoint := by
  letI : TopologicalSpace (Space x₀) := universalCoverTopology hsemi
  refine ⟨universalCoverEndpoint_isCoveringMap hsemi,
    universalCoverEndpoint_surjective x₀, inferInstance, inferInstance, ?_⟩
  exact universalCover_simplyConnectedSpace hsemi

end

end UniversalCoverConstruction

end HatcherLib
