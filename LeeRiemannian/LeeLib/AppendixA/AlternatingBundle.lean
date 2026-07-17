import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import LeeLib.AppendixA.AlternatingSmooth

/-!
# The vector bundle of continuous alternating maps

Given a vector bundle `E : B → Type*` with model fibre `F` and a fixed normed space `G`, we build
the vector bundle whose fibre at `x` is `(E x) [⋀^ι]→L[𝕜] G`, the continuous alternating `ι`-linear
maps out of `E x`. For `E = TangentSpace I` and `G = 𝕜` this is the bundle of differential
`ι`-forms.

Mathlib has no such construction: `Mathlib/Topology/VectorBundle/Hom.lean` builds the bundle of
continuous *linear* maps and its docstring notes that the analogous constructions "for tensor
products of topological vector bundles, exterior algebras, and so on" are "yet to be formalized",
while `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` records bundled forms on manifolds as
an explicit TODO.

The construction follows `Hom.lean`, with one genuine simplification and one genuine complication.

* Simplification: the target `G` is a fixed normed space rather than a second bundle, so only one
  trivialization family is involved and the coordinate change is a single `compContinuousLinearMap`
  rather than a two-sided `arrowCongrSL`.
* Complication: the coordinate change is homogeneous of degree `card ι` in the transition function,
  not bilinear. Continuity is `ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM`
  (mathlib), but smoothness is not in mathlib; it is
  `ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM`, proved in
  `LeeLib.AppendixA.AlternatingSmooth`.

## Main definitions

* `Bundle.Pretrivialization.continuousAlternatingMap`: the induced pretrivialization.
* `Bundle.ContinuousAlternatingMap.vectorPrebundle`: the prebundle, hence the topology, the
  `FiberBundle` and the `VectorBundle` instances on `fun x ↦ (E x) [⋀^ι]→L[𝕜] G`.
* `Bundle.ContinuousAlternatingMap.vectorPrebundle.isContMDiff`: the smooth structure, giving the
  `ContMDiffVectorBundle` instance.
-/

noncomputable section

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (E : B → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {E}
variable [TopologicalSpace B] (e e' : Trivialization F (π F E))

namespace Bundle.Pretrivialization

/-- The coordinate change between the two pretrivializations of the bundle of continuous
alternating maps induced by trivializations `e`, `e'` of `E`: pull back along the transition
function of `E`. -/
def continuousAlternatingMapCoordChange (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [∀ x, Module 𝕜 (E x)] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] (b : B) :
    (F [⋀^ι]→L[𝕜] G) →L[𝕜] (F [⋀^ι]→L[𝕜] G) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM
    ((e'.coordChangeL 𝕜 e b : F ≃L[𝕜] F) : F →L[𝕜] F)

variable {e e'}
variable [FiberBundle F E]

theorem continuousOn_continuousAlternatingMapCoordChange [VectorBundle 𝕜 F E]
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (continuousAlternatingMapCoordChange (E := E) 𝕜 (G := G) (ι := ι) e e')
      (e.baseSet ∩ e'.baseSet) := by
  have h := continuousOn_coordChange 𝕜 e' e
  exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM).comp_continuousOn
    (h.mono (by mfld_set_tac))

variable (e e')
variable [e.IsLinear 𝕜] [e'.IsLinear 𝕜]

/-- Given a trivialization `e` for a vector bundle `E`, `continuousAlternatingMap 𝕜 e` is the
induced pretrivialization for the bundle of continuous alternating maps out of `E`. -/
def continuousAlternatingMap (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [∀ x, Module 𝕜 (E x)] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    Pretrivialization (F [⋀^ι]→L[𝕜] G) (π (F [⋀^ι]→L[𝕜] G) fun x ↦ (E x) [⋀^ι]→L[𝕜] G) where
  toFun p := ⟨p.1, p.2.compContinuousLinearMap (e.symmL 𝕜 p.1)⟩
  invFun p := ⟨p.1, p.2.compContinuousLinearMap (e.continuousLinearMapAt 𝕜 p.1)⟩
  source := Bundle.TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := fun ⟨x, ω⟩ h ↦ by
    simp only [TotalSpace.mk_inj]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
    congr 1
    ext i
    exact e.symmL_continuousLinearMapAt (R := 𝕜) h (v i)
  right_inv' := fun ⟨x, θ⟩ ⟨h, _⟩ ↦ by
    simp only [Prod.mk_right_inj]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
    congr 1
    ext i
    exact e.continuousLinearMapAt_symmL (R := 𝕜) h (v i)
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance continuousAlternatingMap.isLinear :
    (continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) e).IsLinear 𝕜 where
  linear x _ :=
    { map_add ω ω' := by ext v; rfl
      map_smul c ω := by ext v; rfl }

theorem continuousAlternatingMap_apply
    (p : TotalSpace (F [⋀^ι]→L[𝕜] G) fun x ↦ (E x) [⋀^ι]→L[𝕜] G) :
    (continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) e) p
      = ⟨p.1, p.2.compContinuousLinearMap (e.symmL 𝕜 p.1)⟩ := rfl

theorem continuousAlternatingMap_symm_apply (b : B) (θ : F [⋀^ι]→L[𝕜] G) :
    (continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) e).toPartialEquiv.symm (b, θ)
      = ⟨b, θ.compContinuousLinearMap (e.continuousLinearMapAt 𝕜 b)⟩ := rfl

theorem continuousAlternatingMap_symm_apply' {b : B} (hb : b ∈ e.baseSet) (θ : F [⋀^ι]→L[𝕜] G) :
    (continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) e).symm b θ
      = θ.compContinuousLinearMap (e.continuousLinearMapAt 𝕜 b) := by
  rw [symm_apply]
  · rfl
  · exact hb

variable {e e'}

theorem continuousAlternatingMapCoordChange_apply [VectorBundle 𝕜 F E]
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] (b : B)
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (θ : F [⋀^ι]→L[𝕜] G) :
    continuousAlternatingMapCoordChange (E := E) 𝕜 e e' b θ
      = (continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) e' ⟨b,
          (continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) e).symm b θ⟩).2 := by
  rw [continuousAlternatingMap_symm_apply' e hb.1]
  ext v
  simp only [continuousAlternatingMapCoordChange,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, continuousAlternatingMap,
    Pretrivialization.toFun', Function.comp_def]
  congr 1
  ext i
  rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply (R := 𝕜) e' e hb.symm,
    Trivialization.symmL_apply]
  exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e hb.1 _).symm

end Bundle.Pretrivialization

namespace Bundle.ContinuousAlternatingMap

variable [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The prebundle of continuous alternating maps out of a vector bundle. -/
def vectorPrebundle :
    VectorPrebundle 𝕜 (F [⋀^ι]→L[𝕜] G) fun x ↦ (E x) [⋀^ι]→L[𝕜] G where
  pretrivializationAtlas :=
    {e | ∃ (e₀ : Trivialization F (π F E)) (_ : MemTrivializationAtlas e₀),
      e = Pretrivialization.continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) e₀}
  pretrivialization_linear' := by
    rintro _ ⟨e₀, he₀, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.continuousAlternatingMap (E := E) 𝕜 (G := G) (ι := ι) (trivializationAt F E x)
  mem_base_pretrivializationAt := mem_baseSet_trivializationAt F E
  pretrivialization_mem_atlas x := ⟨trivializationAt F E x, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₀, he₀, rfl⟩ _ ⟨e₀', he₀', rfl⟩
    exact ⟨Pretrivialization.continuousAlternatingMapCoordChange (E := E) 𝕜 (G := G) (ι := ι) e₀ e₀',
      Pretrivialization.continuousOn_continuousAlternatingMapCoordChange,
      fun b hb θ => Pretrivialization.continuousAlternatingMapCoordChange_apply b hb θ⟩
  totalSpaceMk_isInducing := by
    intro b
    let L : (E b) ≃L[𝕜] F :=
      (trivializationAt F E b).continuousLinearEquivAt 𝕜 b (mem_baseSet_trivializationAt _ _ _)
    let φ : ((E b) [⋀^ι]→L[𝕜] G) ≃L[𝕜] (F [⋀^ι]→L[𝕜] G) :=
      L.continuousAlternatingMapCongrLeft
    have h : IsInducing fun x : (E b) [⋀^ι]→L[𝕜] G ↦ (b, φ x) :=
      isInducing_const_prod.mpr φ.toHomeomorph.isInducing
    convert h


/-- Topology on the total space of the bundle of continuous alternating maps. -/
instance topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (F [⋀^ι]→L[𝕜] G) fun x ↦ (E x) [⋀^ι]→L[𝕜] G) :=
  (vectorPrebundle (E := E) (𝕜 := 𝕜) (F := F) (G := G) (ι := ι)).totalSpaceTopology

/-- The continuous alternating maps out of a vector bundle form a fiber bundle. -/
instance fiberBundle : FiberBundle (F [⋀^ι]→L[𝕜] G) fun x ↦ (E x) [⋀^ι]→L[𝕜] G :=
  (vectorPrebundle (E := E) (𝕜 := 𝕜) (F := F) (G := G) (ι := ι)).toFiberBundle

/-- The continuous alternating maps out of a vector bundle form a vector bundle. -/
instance vectorBundle : VectorBundle 𝕜 (F [⋀^ι]→L[𝕜] G) fun x ↦ (E x) [⋀^ι]→L[𝕜] G :=
  (vectorPrebundle (E := E) (𝕜 := 𝕜) (F := F) (G := G) (ι := ι)).toVectorBundle

end Bundle.ContinuousAlternatingMap

section Smooth

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {n : WithTop ℕ∞}
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

namespace Bundle.Pretrivialization

/-- The coordinate change of the bundle of continuous alternating maps is `C^n`.

This is the smooth counterpart of `continuousOn_continuousAlternatingMapCoordChange`. Unlike the
hom-bundle case, it is not a consequence of any mathlib lemma: the coordinate change is homogeneous
of degree `card ι` in the transition function of `E`, and its smoothness is
`ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM`. -/
theorem contMDiffOn_continuousAlternatingMapCoordChange [CharZero 𝕜]
    [ContMDiffVectorBundle n F E IB]
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffOn IB 𝓘(𝕜, (F [⋀^ι]→L[𝕜] G) →L[𝕜] (F [⋀^ι]→L[𝕜] G)) n
      (continuousAlternatingMapCoordChange (E := E) 𝕜 (G := G) (ι := ι) e e')
      (e.baseSet ∩ e'.baseSet) := by
  have h := contMDiffOn_coordChangeL (IB := IB) (n := n) e' e
  have hs : ContMDiff 𝓘(𝕜, F →L[𝕜] F) 𝓘(𝕜, (F [⋀^ι]→L[𝕜] G) →L[𝕜] (F [⋀^ι]→L[𝕜] G)) n
      (fun f : F →L[𝕜] F =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (F [⋀^ι]→L[𝕜] G) →L[𝕜] (F [⋀^ι]→L[𝕜] G))) :=
    contMDiff_iff_contDiff.mpr
      (ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
        (𝕜 := 𝕜) (E := F) (F := F) (G := G) (ι := ι) (n := n))
  exact hs.comp_contMDiffOn (h.mono (by mfld_set_tac))

end Bundle.Pretrivialization

namespace Bundle.ContinuousAlternatingMap

/-- The prebundle of continuous alternating maps is a `C^n` prebundle. -/
instance vectorPrebundle.isContMDiff [CharZero 𝕜] [ContMDiffVectorBundle n F E IB] :
    (vectorPrebundle (E := E) (𝕜 := 𝕜) (F := F) (G := G) (ι := ι)).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₀, he₀, rfl⟩ _ ⟨e₀', he₀', rfl⟩
    exact ⟨Pretrivialization.continuousAlternatingMapCoordChange (E := E) 𝕜 (G := G) (ι := ι)
        e₀ e₀',
      Pretrivialization.contMDiffOn_continuousAlternatingMapCoordChange e₀ e₀',
      fun b hb θ => Pretrivialization.continuousAlternatingMapCoordChange_apply b hb θ⟩

/-- The continuous alternating maps out of a `C^n` vector bundle form a `C^n` vector bundle.

For `E = TangentSpace I` and `G = 𝕜` this is the bundle of differential `ι`-forms on a manifold,
which mathlib records as a TODO. -/
instance contMDiffVectorBundle [CharZero 𝕜] [ContMDiffVectorBundle n F E IB] :
    ContMDiffVectorBundle n (F [⋀^ι]→L[𝕜] G) (fun x ↦ (E x) [⋀^ι]→L[𝕜] G) IB :=
  (vectorPrebundle (E := E) (𝕜 := 𝕜) (F := F) (G := G) (ι := ι)).contMDiffVectorBundle IB

end Bundle.ContinuousAlternatingMap

end Smooth
