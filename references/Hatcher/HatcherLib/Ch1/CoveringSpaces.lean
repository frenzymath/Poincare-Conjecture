import HatcherLib.Ch1.BasicConstructions
import Mathlib.Topology.Homotopy.Lifting

/-!
# Chapter 1: covering spaces

The covering-map and lifting infrastructure in mathlib matches the elementary
covering-space arguments in Hatcher.  This module exposes that infrastructure
under chapter-local names and packages the uniqueness statements in the form
used by the blueprint.
-/

namespace HatcherLib

noncomputable section

open scoped unitInterval

universe u v w

variable {E : Type u} {X : Type v} {A : Type w}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
variable {p : E → X}

/-- A covering map in the sense of Hatcher. -/
abbrev CoveringMap (p : E → X) : Prop := IsCoveringMap p

/-- The evenly-covered-neighborhood condition at a point. -/
abbrev EvenlyCovered (p : E → X) (x : X) : Prop :=
  IsEvenlyCovered p x (p ⁻¹' {x})

/-- A covering map from a pointed total space onto a path-connected base is
surjective. -/
theorem CoveringMap.surjective_of_pathConnectedSpace
    (cov : CoveringMap p) [PathConnectedSpace X] (e₀ : E) :
    Function.Surjective p := by
  intro x
  let γ : Path (p e₀) x := PathConnectedSpace.somePath (p e₀) x
  refine ⟨cov.liftPath γ e₀ (by simp) 1, ?_⟩
  exact (congrFun (cov.liftPath_lifts γ e₀ (by simp)) 1).trans γ.target

private def localSectionPathBasis (p : E → X) : Set (Set E) :=
  {U | ∃ V : Set X, IsOpen V ∧ IsPathConnected V ∧
    ∃ s : C(V, E), p ∘ (s : V → E) = (Subtype.val : V → X) ∧
      Set.range s = U}

/-- The domain of a local homeomorphism into a locally path-connected space
is locally path-connected. -/
theorem locPathConnectedSpace_of_isLocalHomeomorph
    (hp : IsLocalHomeomorph p) [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace E := by
  let B := localSectionPathBasis p
  have hB : TopologicalSpace.IsTopologicalBasis B := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      rcases hU with ⟨V, hVo, hVp, s, hs, hrange⟩
      rw [← hrange]
      exact (hp.isOpenEmbedding_of_comp
        (by rw [hs]; exact hVo.isOpenEmbedding_subtypeVal)
        s.continuous).isOpen_range
    · intro e U heU hUo
      obtain ⟨C, hC, heC, hCU⟩ :=
        hp.isTopologicalBasis.exists_subset_of_mem_open heU hUo
      obtain ⟨V, hVo, s, hs, hrange⟩ := hC
      rw [← hrange] at heC hCU
      obtain ⟨v, hvse⟩ := heC
      have hvpe : v.1 = p e := by
        calc
          v.1 = p (s v) := (congrFun hs v).symm
          _ = p e := congrArg p hvse
      have hpeV : p e ∈ V := hvpe ▸ v.2
      obtain ⟨W, ⟨hWo, hpW, hWp⟩, hWV⟩ :=
        (isOpen_isPathConnected_basis (p e)).mem_iff.mp
          (hVo.mem_nhds hpeV)
      let iWV : C(W, V) :=
        ⟨fun w => ⟨w.1, hWV w.2⟩,
          continuous_subtype_val.subtype_mk _⟩
      let sW : C(W, E) := s.comp iWV
      have hsW : p ∘ (sW : W → E) = (Subtype.val : W → X) := by
        ext w
        simpa [sW, iWV, Function.comp_def] using congrFun hs (iWV w)
      have heW : e ∈ Set.range sW := by
        have hvEq : iWV ⟨p e, hpW⟩ = v := by
          apply Subtype.ext
          exact hvpe.symm
        refine ⟨⟨p e, hpW⟩, ?_⟩
        simpa [sW, iWV, hvEq] using hvse
      refine ⟨Set.range sW, ?_, heW, ?_⟩
      · exact ⟨W, hWo, hWp, sW, hsW, rfl⟩
      · intro z hz
        obtain ⟨w, rfl⟩ := hz
        exact hCU ⟨iWV w, by simp [sW, iWV]⟩
  refine LocallyPathConnectedSpace.of_bases (ι := Set E)
    (p := fun e U => U ∈ B ∧ e ∈ U)
    (s := fun _ U => U) (fun _ => hB.nhds_hasBasis) ?_
  intro e U hU
  obtain ⟨V, hVo, hVp, s, hs, hrange⟩ := hU.1
  rw [← hrange]
  letI : PathConnectedSpace V :=
    isPathConnected_iff_pathConnectedSpace.mp hVp
  simpa only [Set.image_univ] using
    (isPathConnected_univ.image s.continuous)

/-- The domain of a covering map over a locally path-connected base is locally
path-connected. -/
theorem CoveringMap.locPathConnectedSpace (cov : CoveringMap p)
    [LocallyPathConnectedSpace X] : LocallyPathConnectedSpace E :=
  locPathConnectedSpace_of_isLocalHomeomorph cov.isLocalHomeomorph

/-- A continuous map `f'` is a lift of `f` through `p`. -/
def IsLift (p : E → X) (f : C(A, X)) (f' : C(A, E)) : Prop :=
  p ∘ (f' : A → E) = f

/-- The canonical lift supplied by the covering homotopy theorem. -/
noncomputable def liftHomotopy (cov : CoveringMap p)
    (H : C(↑unitInterval × A, X)) (f : C(A, E))
    (h₀ : ∀ a, H (0, a) = p (f a)) : C(↑unitInterval × A, E) :=
  cov.liftHomotopy H f h₀

/-- Homotopy lifting, including uniqueness for the prescribed initial lift. -/
theorem existsUnique_liftHomotopy (cov : CoveringMap p)
    (H : C(↑unitInterval × A, X)) (f : C(A, E))
    (h₀ : ∀ a, H (0, a) = p (f a)) :
    ∃! H' : C(↑unitInterval × A, E),
      IsLift p H H' ∧ ∀ a, H' (0, a) = f a := by
  refine ⟨cov.liftHomotopy H f h₀,
    ⟨cov.liftHomotopy_lifts H f h₀, cov.liftHomotopy_zero H f h₀⟩, ?_⟩
  intro H' hH'
  exact (cov.eq_liftHomotopy_iff' h₀ H').2 hH'

/-- Every path admits a lift after choosing a point above its initial point. -/
theorem exists_path_lift (cov : CoveringMap p) (γ : C(↑unitInterval, X))
    (e : E) (h₀ : γ 0 = p e) :
    ∃ Γ : C(↑unitInterval, E), IsLift p γ Γ ∧ Γ 0 = e := by
  obtain ⟨Γ, hΓ, hΓ₀⟩ := cov.exists_path_lifts γ e h₀
  exact ⟨Γ, hΓ, hΓ₀⟩

/-- The map on path homotopy classes induced by a covering map is injective. -/
theorem coveringPathClassMap_injective (cov : CoveringMap p) (e₀ e₁ : E) :
    Function.Injective fun γ : _root_.Path.Homotopic.Quotient e₀ e₁ =>
      γ.map ⟨p, cov.continuous⟩ :=
  cov.injective_path_homotopic_map e₀ e₁

/-- A covering map is injective on mathlib's raw fundamental group. -/
theorem coveringFundamentalGroupMap_injective (cov : CoveringMap p) (e : E) :
    Function.Injective (FundamentalGroup.map ⟨p, cov.continuous⟩ e) := by
  exact cov.injective_path_homotopic_map e e

/-- In particular, a covering map is injective on Hatcher's fundamental group,
with its path-product multiplication convention. -/
theorem coveringPiOneMap_injective (cov : CoveringMap p) (e : E) :
    Function.Injective (inducedPiOne ⟨p, cov.continuous⟩ e) := by
  intro a b hab
  apply MulOpposite.unop_injective
  apply coveringFundamentalGroupMap_injective cov e
  exact congrArg MulOpposite.unop hab

/-- The subgroup lifting criterion for a path-connected, locally path-connected source. -/
theorem existsUnique_lift_of_piOne_range_le (cov : CoveringMap p)
    [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (hle : (FundamentalGroup.map f a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range) :
    ∃! f' : C(A, E), f' a₀ = e₀ ∧ IsLift p f f' :=
  cov.existsUnique_continuousMap_lifts_of_range_le he hle

/-- The image of the fundamental group of a based lift is contained in the
image subgroup of the covering map, with both maps transported to a specified
basepoint of the codomain. -/
theorem piOne_mapOfEq_range_le_of_lift (cov : CoveringMap p)
    {f : C(A, X)} {f' : C(A, E)} {a₀ : A} {e₀ : E} {x₀ : X}
    (hf : f a₀ = x₀) (he : p e₀ = x₀) (hbase : f' a₀ = e₀)
    (hlift : IsLift p f f') :
    (FundamentalGroup.mapOfEq f hf).range ≤
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  rintro z ⟨u, rfl⟩
  obtain ⟨γ, rfl⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath u)
  refine ⟨FundamentalGroup.mapOfEq f' hbase
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  apply Quotient.sound
  have hpath : ((((γ.map f'.continuous).cast hbase.symm hbase.symm).map
      cov.continuous).cast he.symm he.symm) =
      (γ.map f.continuous).cast hf.symm hf.symm := by
    apply Path.ext
    funext t
    simpa [Path.cast_coe, Path.map_coe, IsLift] using congrFun hlift (γ t)
  change Path.Homotopic
    ((((γ.map f'.continuous).cast hbase.symm hbase.symm).map
      cov.continuous).cast he.symm he.symm)
    ((γ.map f.continuous).cast hf.symm hf.symm)
  rw [hpath]

/-- The image of the fundamental group of a based lift is contained in the
image subgroup of the covering map. -/
theorem piOne_range_le_of_lift (cov : CoveringMap p)
    {f : C(A, X)} {f' : C(A, E)} {a₀ : A} {e₀ : E}
    (he : p e₀ = f a₀) (hbase : f' a₀ = e₀)
    (hlift : IsLift p f f') :
    (FundamentalGroup.map f a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  rintro z ⟨u, rfl⟩
  obtain ⟨γ, rfl⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath u)
  refine ⟨FundamentalGroup.mapOfEq f' hbase
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.map_apply]
  apply Quotient.sound
  have hpath : ((((γ.map f'.continuous).cast hbase.symm hbase.symm).map
      cov.continuous).cast he.symm he.symm) = γ.map f.continuous := by
    apply Path.ext
    funext t
    simpa [Path.cast_coe, Path.map_coe, IsLift] using congrFun hlift (γ t)
  change Path.Homotopic
    ((((γ.map f'.continuous).cast hbase.symm hbase.symm).map
      cov.continuous).cast he.symm he.symm)
    (γ.map f.continuous)
  rw [hpath]

/-- The exact subgroup lifting criterion: a based lift exists if and only if
the induced fundamental-group image lies in the covering image subgroup. -/
theorem exists_lift_iff_piOne_range_le (cov : CoveringMap p)
    [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀) :
    (∃ f' : C(A, E), f' a₀ = e₀ ∧ IsLift p f f') ↔
      (FundamentalGroup.map f a₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  constructor
  · rintro ⟨f', hbase, hlift⟩
    exact piOne_range_le_of_lift cov he hbase hlift
  · intro hle
    obtain ⟨f', hf', -⟩ := existsUnique_lift_of_piOne_range_le cov he hle
    exact ⟨f', hf'⟩

/-- Two lifts over a preconnected source that agree once agree everywhere. -/
theorem lifts_eq_of_eq_at (cov : CoveringMap p) [PreconnectedSpace A]
    {f₁ f₂ : C(A, E)}
    (hcomp : p ∘ (f₁ : A → E) = p ∘ (f₂ : A → E))
    (a : A) (ha : f₁ a = f₂ a) : f₁ = f₂ := by
  ext z
  exact congrFun (cov.eq_of_comp_eq f₁.continuous f₂.continuous hcomp a ha) z

/-- A neighborhood has trivial image in the fundamental group. -/
def SemilocallySimplyConnected (X : Type v) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, U ∈ nhds x ∧
    ∃ hx : x ∈ U,
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩).range = ⊥

end
end HatcherLib
