import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_29.Theorem_5_8
import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_33
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch02.Sec02_09.Example_2_14
import LeeSmoothLib.Ch07.Sec07_46.Definition_7_46_extra_3
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_11
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_50.Theorem_7_25
import LeeSmoothLib.Ch07.Sec07_50.Definition_7_50_extra_4
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Manifold ContDiff

universe u𝕜 uE uH uG uE' uH' uM uQ

section OrbitSubmanifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H} [LieGroup I ∞ G]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

namespace LieSubgroup

omit [LieGroup I ∞ G] in
/-- Helper: the inclusion of a Lie subgroup carrier into the ambient
group is continuous because the stored immersion witness is pointwise continuous. -/
theorem subtypeVal_continuous (S : LieSubgroup I) :
    Continuous (Subtype.val : S.carrier → G) := by
  -- Exercise 4.16 upgrades each pointwise immersion witness for the subgroup inclusion to
  -- continuity at that point, so continuity follows pointwise.
  rw [continuous_iff_continuousAt]
  intro x
  let hImm :
      Manifold.IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) :=
    S.subtype_val_isImmersion
  exact (hImm.isImmersionAt x).continuousAt

/-- Helper: a closed Lie subgroup carrier determines the canonical closed
subgroup owner with the same underlying subgroup. -/
def closedCarrierOwner (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) : ClosedSubgroup G :=
  { toSubgroup := S.carrier
    isClosed' := hS_closed }

/-- Helper: the subgroup inclusion factors through the canonical closed
subgroup with the same carrier. -/
def toClosedCarrierHom (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    S.carrier →* closedCarrierOwner S hS_closed :=
  { toFun := fun x ↦ ⟨x.1, x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }

omit [LieGroup I ∞ G] in
/-- Helper: the factor map into the canonical closed subgroup is
continuous because it is the subgroup inclusion with the codomain repackaged as a subtype. -/
theorem toClosedCarrierHom_continuous (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Continuous (toClosedCarrierHom S hS_closed) := by
  -- Repackage continuity of the subgroup inclusion through the closed-subgroup subtype owner.
  exact
    (subtypeVal_continuous S).subtype_mk fun x ↦ by
      exact x.2

omit [LieGroup I ∞ G] in
/-- Helper: the factor map onto the canonical closed subgroup is
surjective because both domain and codomain encode the same subgroup elements. -/
theorem toClosedCarrierHom_surjective (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Function.Surjective (toClosedCarrierHom S hS_closed) := by
  rintro ⟨x, hx⟩
  -- Lift the closed-subgroup point back to the original Lie-subgroup carrier without changing the
  -- ambient group element.
  refine ⟨⟨x, hx⟩, rfl⟩

omit [LieGroup I ∞ G] in
/-- Helper: the canonical factor map into the closed-subgroup owner still
records the same ambient group element as the original subgroup inclusion. -/
theorem subtypeVal_factor_through_closedCarrierOwner (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    (Subtype.val : S.carrier → G) =
      (Subtype.val : closedCarrierOwner S hS_closed → G) ∘ toClosedCarrierHom S hS_closed := by
  -- Both sides are definitionally the same subgroup inclusion; only the codomain owner changes.
  rfl

omit [LieGroup I ∞ G] in
/-- Helper: the factor map into the canonical closed subgroup owner is
injective because both source and target remember the same ambient group element. -/
theorem toClosedCarrierHom_injective (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Function.Injective (toClosedCarrierHom S hS_closed) := by
  intro x y hxy
  -- Forgetting the codomain packaging reduces equality to equality of ambient group elements.
  apply Subtype.ext
  exact congrArg Subtype.val hxy

omit [LieGroup I ∞ G] in
/-- Helper: the canonical factor map to the closed-subgroup owner is a
bijection of underlying subgroup elements. -/
theorem toClosedCarrierHom_bijective (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Function.Bijective (toClosedCarrierHom S hS_closed) := by
  -- Combine the explicit injective and surjective carrier-transport lemmas.
  exact ⟨toClosedCarrierHom_injective S hS_closed, toClosedCarrierHom_surjective S hS_closed⟩

end LieSubgroup

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the canonical map from `G ⧸ MulAction.stabilizer G p` onto
the orbit of `p` has image exactly `MulAction.orbit G p`. -/
theorem range_ofQuotientStabilizer_eq_orbit (p : M) :
    Set.range (MulAction.ofQuotientStabilizer G p) = MulAction.orbit G p := by
  -- Compare the range pointwise so that the forward and reverse directions use the canonical
  -- quotient-stabilizer orbit API directly.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    -- Every point produced by the descended quotient map lies in the orbit by construction.
    exact MulAction.ofQuotientStabilizer_mem_orbit G p q
  · intro hy
    refine ⟨MulAction.orbitEquivQuotientStabilizer G p ⟨y, hy⟩, ?_⟩
    -- The orbit-stabilizer equivalence sends the chosen orbit point back to a quotient class
    -- whose image under the descended map is exactly that point.
    change
      (((MulAction.orbitEquivQuotientStabilizer G p).symm
          ((MulAction.orbitEquivQuotientStabilizer G p) ⟨y, hy⟩) : MulAction.orbit G p) : M) = y
    exact congrArg Subtype.val
      (Equiv.symm_apply_apply (MulAction.orbitEquivQuotientStabilizer G p) ⟨y, hy⟩)

omit [IsManifold J ∞ M] in
/-- Helper: once the descended map
`MulAction.ofQuotientStabilizer G p` is available as an injective immersion from a boundaryless
manifold structure on `G ⧸ MulAction.stabilizer G p`, its image gives the required immersed
submanifold structure on the orbit of `p`. -/
theorem orbitImmersedSubmanifold_fromQuotient
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    (p : M)
    [ChartedSpace EQ (G ⧸ MulAction.stabilizer G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ MulAction.stabilizer G p)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p)) :
    ∃ S : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      S.carrier = MulAction.orbit G p := by
  -- Package the injective descended quotient map as an immersed submanifold of `M`.
  refine ⟨hImm.toImmersedSubmanifold (MulAction.injective_ofQuotientStabilizer G p), ?_⟩
  -- The carrier of that immersed submanifold is exactly the orbit identified by the quotient API.
  exact range_ofQuotientStabilizer_eq_orbit p

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: transporting the stabilizer quotient along a subgroup equality
does not change the image of the descended orbit map. -/
theorem range_ofQuotientStabilizer_comp_quotientEquivOfEq_eq_orbit
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) :
    Set.range (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS) =
      MulAction.orbit G p := by
  -- The transported quotient map still lands in the orbit because `ofQuotientStabilizer` does.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact MulAction.ofQuotientStabilizer_mem_orbit G p _
  · intro hy
    -- Use the canonical stabilizer quotient parametrization and pull the witness back across the
    -- quotient equivalence coming from `hS`.
    rw [← range_ofQuotientStabilizer_eq_orbit p] at hy
    rcases hy with ⟨q, rfl⟩
    refine ⟨(Subgroup.quotientEquivOfEq hS).symm q, ?_⟩
    simp

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: after transporting a subgroup quotient to the stabilizer
quotient, evaluating the descended orbit map on quotient classes recovers the original orbit map
on representatives. -/
theorem descendedOrbitMap_comp_quotientEquivOfEq_mk
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) :
    MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS ∘ QuotientGroup.mk =
      orbit_map G p := by
  -- Collapse the quotient transport on representatives so the quotient route rewrites back to
  -- the original orbit map without further `quotientEquivOfEq` normalization.
  funext g
  rw [Function.comp_apply, Function.comp_apply, Subgroup.quotientEquivOfEq_mk,
    MulAction.ofQuotientStabilizer_mk, orbit_map]

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: if a subgroup quotient is identified with the stabilizer
quotient by `hS`, the resulting quotient type is canonically equivalent to the orbit subtype. -/
noncomputable def orbitEquivQuotientOfStabilizerEq
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) :
    G ⧸ S ≃ MulAction.orbit G p :=
  (Subgroup.quotientEquivOfEq hS).trans (MulAction.orbitEquivQuotientStabilizer G p).symm

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the ambient-valued map underlying
`orbitEquivQuotientOfStabilizerEq` is exactly the descended orbit map. -/
theorem orbitEquivQuotientOfStabilizerEq_apply
    (p : M) {S : Subgroup G} (hS : S = MulAction.stabilizer G p) (q : G ⧸ S) :
    ((orbitEquivQuotientOfStabilizerEq p hS q : MulAction.orbit G p) : M) =
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS) q := by
  refine Quotient.inductionOn q ?_
  intro g
  -- Collapse both quotient parametrizations to the common representative-level action `g • p`.
  change
    (((MulAction.orbitEquivQuotientStabilizer G p).symm
        (Subgroup.quotientEquivOfEq hS (QuotientGroup.mk g)) : MulAction.orbit G p) : M) =
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS) (QuotientGroup.mk g)
  rw [Function.comp_apply, Subgroup.quotientEquivOfEq_mk, MulAction.ofQuotientStabilizer_mk]
  -- The canonical orbit-stabilizer equivalence sends the transported quotient class to `g • p`.
  simpa using
    (MulAction.orbitEquivQuotientStabilizer_symm_apply p (QuotientGroup.mk g))

omit [IsManifold J ∞ M] in
/-- Helper: if a quotient by a subgroup whose carrier is the stabilizer
immerses into `M` through the transported descended orbit map, its image is the orbit of `p`. -/
theorem orbitImmersedSubmanifold_fromCarrierEqQuotient
    {S : Subgroup G} {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    (p : M) (hS : S = MulAction.stabilizer G p)
    [ChartedSpace EQ (G ⧸ S)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ S)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS)) :
    ∃ T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      T.carrier = MulAction.orbit G p := by
  -- Package the transported quotient map as an immersed submanifold using injectivity of both
  -- the stabilizer quotient map and the carrier-transport equivalence.
  refine ⟨hImm.toImmersedSubmanifold ?_, ?_⟩
  · intro q₁ q₂ hq
    apply (Subgroup.quotientEquivOfEq hS).injective
    exact MulAction.injective_ofQuotientStabilizer G p hq
  -- The carrier is still the orbit because the transported quotient map has the same range.
  exact range_ofQuotientStabilizer_comp_quotientEquivOfEq_eq_orbit p hS

omit [LieGroup I ∞ G] [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- Helper: once the stabilizer is realized as a Lie subgroup owner `S`,
the remaining quotient-manifold and immersion package on `G ⧸ S.carrier` is enough to finish the
orbit statement. -/
theorem orbitImmersedSubmanifold_fromLieSubgroupQuotient
    (p : M) (S : LieSubgroup I) (hS : S.carrier = MulAction.stabilizer G p)
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    [ChartedSpace EQ (G ⧸ S.carrier)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞) (G ⧸ S.carrier)]
    (hImm : IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p ∘ Subgroup.quotientEquivOfEq hS)) :
    ∃ T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uG} J M,
      T.carrier = MulAction.orbit G p := by
  -- Once the stabilizer carrier is owned by `S`, the earlier carrier-equality quotient assembly
  -- closes the orbit statement without any additional transport work in the final theorem.
  exact orbitImmersedSubmanifold_fromCarrierEqQuotient p hS hImm

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the descended orbit map is `G`-equivariant with respect to
the quotient action on `G ⧸ MulAction.stabilizer G p`. -/
theorem ofQuotientStabilizer_map_smul (p : M) (g : G)
    (q : G ⧸ MulAction.stabilizer G p) :
    MulAction.ofQuotientStabilizer G p (g • q) = g • MulAction.ofQuotientStabilizer G p q := by
  -- Evaluate the quotient map on a representative so the equivariance reduces to associativity of
  -- the action.
  refine Quotient.inductionOn q ?_
  intro x
  simp [MulAction.ofQuotientStabilizer_mk, smul_smul]

/-- Helper: package the descended orbit map as the canonical equivariant
map from `G ⧸ MulAction.stabilizer G p` to `M`. -/
def ofQuotientStabilizerMulActionHom (p : M) :
    (G ⧸ MulAction.stabilizer G p) →[G] M where
  toFun := MulAction.ofQuotientStabilizer G p
  map_smul' := ofQuotientStabilizer_map_smul p

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the orbit map intertwines left multiplication on `G` with the
given action on `M`, so it is a bundled equivariant map. -/
theorem orbitMap_map_smul (p : M) (g x : G) :
    orbit_map G p (g • x) = g • orbit_map G p x := by
  -- Expand the orbit map and use associativity of the action.
  simp [orbit_map, smul_smul]

/-- Helper: package the orbit map at `p` as the canonical equivariant map
from `G` with its left-regular action to `M`. -/
def orbitMapMulActionHom (p : M) : G →[G] M where
  toFun := orbit_map G p
  map_smul' := orbitMap_map_smul p

/-- Helper: the orbit map has constant rank by the equivariant rank
transport argument already used earlier in the chapter. -/
theorem orbitMapHasConstantRank [FiniteDimensional 𝕜 E'] (p : M) :
    ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r := by
  -- Repackage the orbit map as an equivariant map so Theorem 7.25 applies directly.
  let F : G →[G] M := orbitMapMulActionHom p
  have hF : ContMDiff I J ∞ F := orbitMap_contMDiff p
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank I J F r := by
    exact
      @MulActionHom.hasConstantRank 𝕜 _ E _ _ H _ G _ _ _ I _
        E _ _ H _ G _ _ I _ _ _
        E' _ _ _ H' _ M _ _ J _ _ _ _
        F hF
  simpa [orbitMapMulActionHom] using hConstRank

/-- Helper: the constant-rank level-set theorem equips the stabilizer of
`p` with the embedded-submanifold structure inherited from the fiber `orbit_map G p ⁻¹' {p}`. -/
theorem stabilizerEmbeddedData
    {r : ℕ} (J' : ModelWithCorners 𝕜 E' H')
    [IsManifold J' ∞ M] [ContMDiffSMul I J' ∞ G M]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (p : M) (hRank : Manifold.HasConstantRank I J' (orbit_map G p) r) :
    let k : ℕ := Module.finrank 𝕜 E - r
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)),
      ∃ hs : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)),
        let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k))
            ((MulAction.stabilizer G p : Set G)) := cs
        let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
        ∃ hEmb : IsEmbeddedSubmanifold I K ((MulAction.stabilizer G p : Set G)),
          hEmb.codimension = r := by
  -- Rewrite the level-set owner to the stabilizer subtype before unpacking the theorem output.
  simpa [preimage_singleton_orbit_map_eq_stabilizer] using
    (constant_rank_level_set_has_embedded_submanifold_structure
      (orbitMap_contMDiff p) hRank p)

include I J in
/-- Helper: the stabilizer is a closed subset because it is the fiber
over `p` of the continuous orbit map. -/
theorem stabilizerClosed
    [T2Space M] (p : M) :
    IsClosed ((MulAction.stabilizer G p : Set G)) := by
  -- Rewrite the stabilizer as the singleton fiber of the continuous orbit map.
  have hSmooth : ContMDiff I J ∞ (orbit_map G p) := by
    simpa [orbit_map] using
      ((contMDiff_id : ContMDiff I I ∞ fun g : G ↦ g).smul
        (contMDiff_const : ContMDiff I J ∞ fun _ : G ↦ p))
  rw [← preimage_singleton_orbit_map_eq_stabilizer]
  exact isClosed_singleton.preimage hSmooth.continuous

/-- Helper: in a Hausdorff target manifold, the stabilizer of `p` carries
the canonical closed-subgroup owner coming from its closedness in `G`. -/
def stabilizerClosedSubgroup
    [T2Space M] (p : M) : ClosedSubgroup G :=
  { toSubgroup := MulAction.stabilizer G p
    isClosed' := by
      have hSmooth : ContMDiff I J ∞ (orbit_map G p) := by
        simpa [orbit_map] using
          ((contMDiff_id : ContMDiff I I ∞ fun g : G ↦ g).smul
            (contMDiff_const : ContMDiff I J ∞ fun _ : G ↦ p))
      simpa [preimage_singleton_orbit_map_eq_stabilizer] using
        (isClosed_singleton.preimage hSmooth.continuous :
          IsClosed ((orbit_map G p) ⁻¹' ({p} : Set M))) }

/-- Helper: once the stabilizer is known to be closed, the quotient
`G ⧸ MulAction.stabilizer G p` is Hausdorff in the canonical quotient topology. -/
theorem stabilizerQuotient_t2Space
    {J' : ModelWithCorners 𝕜 E' H'} [IsManifold J' ∞ M] [ContMDiffSMul I J' ∞ G M]
    [T2Space G] [T2Space M] (p : M) :
    T2Space (G ⧸ MulAction.stabilizer G p) := by
  -- The quotient by a closed subgroup of a topological group is Hausdorff.
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : IsClosed ((MulAction.stabilizer G p : Set G)) :=
    by
      have hSmooth : ContMDiff I J' ∞ (orbit_map G p) := by
        simpa [orbit_map] using
          ((contMDiff_id : ContMDiff I I ∞ fun g : G ↦ g).smul
            (contMDiff_const : ContMDiff I J' ∞ fun _ : G ↦ p))
      simpa [preimage_singleton_orbit_map_eq_stabilizer] using
        (isClosed_singleton.preimage hSmooth.continuous :
          IsClosed ((orbit_map G p) ⁻¹' ({p} : Set M)))
  infer_instance

section

include I J

/-- Helper for Remark 7.50-extra-5: before the missing `LieSubgroup` owner step, the stabilizer of
`p` already has a closed finite-dimensional embedded-submanifold package at regularity `∞`. -/
theorem stabilizerEmbeddedClosedData
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] [T2Space M] (p : M) :
    ∃ k : ℕ,
      ∃ K : ModelWithCorners 𝕜 (EuclideanSpace 𝕜 (Fin k)) (EuclideanSpace 𝕜 (Fin k)),
        ∃ _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)),
          ∃ _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)),
            IsEmbeddedSubmanifold I K ((MulAction.stabilizer G p : Set G)) ∧
              IsClosed ((MulAction.stabilizer G p : Set G)) := by
  -- First package the stabilizer fiber of the orbit map as an embedded subgroup.
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    orbitMapHasConstantRank p
  rcases hConstRank with ⟨r, hRank⟩
  let k : ℕ := Module.finrank 𝕜 E - r
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
  rcases stabilizerEmbeddedData J p hRank with ⟨cs, hs, hEmb, _⟩
  refine ⟨k, K, cs, hs, ?_⟩
  constructor
  · -- The constant-rank level-set package already gives the embedded subgroup structure.
    exact hEmb
  · -- Closedness comes from identifying the stabilizer with the orbit-map fiber over `p`.
    have hSmooth : ContMDiff I J ∞ (orbit_map G p) := by
      simpa [orbit_map] using
        ((contMDiff_id : ContMDiff I I ∞ fun g : G ↦ g).smul
          (contMDiff_const : ContMDiff I J ∞ fun _ : G ↦ p))
    simpa [preimage_singleton_orbit_map_eq_stabilizer] using
      (isClosed_singleton.preimage hSmooth.continuous :
        IsClosed ((orbit_map G p) ⁻¹' ({p} : Set M)))

end

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: quotient classes for `MulAction.stabilizer G p` agree exactly
when the corresponding orbit-map values agree. -/
theorem quotientMk_eq_iff_orbitMap_eq (p : M) (g₁ g₂ : G) :
    (QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂ ↔
      orbit_map G p g₁ = orbit_map G p g₂ := by
  constructor
  · intro hq
    have hmem : g₁⁻¹ * g₂ ∈ MulAction.stabilizer G p := QuotientGroup.eq.mp hq
    have hfix : (g₁⁻¹ * g₂) • p = p := by
      simpa [MulAction.mem_stabilizer_iff] using hmem
    -- Rewrite quotient equality into a stabilizer element fixing `p`, then reassociate the action.
    calc
      orbit_map G p g₁ = g₁ • p := rfl
      _ = g₁ • ((g₁⁻¹ * g₂) • p) := by rw [hfix]
      _ = (g₁ * (g₁⁻¹ * g₂)) • p := by simp [smul_smul]
      _ = orbit_map G p g₂ := by simp [orbit_map]
  · intro hOrbit
    apply QuotientGroup.eq.mpr
    -- Equality in the orbit rewrites back to the stabilizer relation defining the quotient.
    rw [MulAction.mem_stabilizer_iff]
    calc
      (g₁⁻¹ * g₂) • p = g₁⁻¹ • (g₂ • p) := by simp [smul_smul]
      _ = g₁⁻¹ • (g₁ • p) := by
          simpa [orbit_map] using congrArg (fun x : M ↦ g₁⁻¹ • x) hOrbit.symm
      _ = p := by simp

/-- Helper: in Euclidean manifold models, the constant-rank theorem gives
the orbit map a centered local normal form at `1 : G`. -/
theorem orbitMapLocalNormalFormAtOne
    {m n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) :
    ∃ r : ℕ,
      ∃ _ : LocalNormalFormAPI.LocalCoordinateNormalFormAt
        (orbit_map G p) (1 : G)
        (LocalNormalFormAPI.rank_normal_form m n r),
        True := by
  -- Combine constant rank for the equivariant orbit map with the chapter's rank theorem.
  let IG : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  let JM : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let _ : LieGroup IG ∞ G := by
    simpa [IG] using (inferInstance : LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G)
  let _ : IsManifold JM ∞ M := by
    simpa [JM] using
      (inferInstance : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M)
  let _ : ContMDiffSMul IG JM ∞ G M := by
    simpa [IG, JM] using
      (inferInstance :
        ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M)
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank IG JM (orbit_map G p) r :=
    orbitMapHasConstantRank p
  rcases hConstRank with ⟨r, hRank⟩
  rcases constant_rank_local_coordinate_normal_form
      (orbitMap_contMDiff p) hRank (1 : G) with ⟨hNF, _⟩
  exact ⟨r, hNF, trivial⟩

/-- Helper for Remark 7.50-extra-5: the Euclidean first-coordinate projection is a smooth
submersion. -/
def orbitHeadProjection {m r : ℕ} (hr : r ≤ m) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin r) :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x (Fin.castLE hr i)

/-- Helper for Remark 7.50-extra-5: the first-coordinate projection on Euclidean space is
continuous. -/
theorem continuous_orbitHeadProjection
    {m r : ℕ} (hr : r ≤ m) :
    Continuous (orbitHeadProjection hr) := by
  -- The first-coordinate projection is coordinatewise continuous on Euclidean space.
  have hcoord :
      Continuous fun x : EuclideanSpace ℝ (Fin m) ↦
        fun i : Fin r ↦ x (Fin.castLE hr i) :=
    continuous_pi fun i ↦
      PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) (Fin.castLE hr i)
  simpa [orbitHeadProjection] using
    (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp hcoord

/-- Helper for Remark 7.50-extra-5: the standard rank-`r` inclusion is a right inverse to the
first-coordinate projection. -/
theorem orbitHeadProjection_rankNormalForm
    {m r : ℕ} (hr : r ≤ m) (x : EuclideanSpace ℝ (Fin r)) :
    orbitHeadProjection hr (LocalNormalFormAPI.rank_normal_form r m r x) = x := by
  -- On the first `r` target coordinates, the rank normal form is literally the identity.
  ext i
  change LocalNormalFormAPI.rank_normal_form r m r x (Fin.castLE hr i) = x i
  exact LocalNormalFormAPI.rank_normal_form_apply_of_lt i.2 i.2 x

/-- Helper for Remark 7.50-extra-5: the Euclidean first-coordinate projection is a smooth
submersion. -/
theorem orbitHeadProjection_isSmoothSubmersion
    {m r : ℕ} (hr : r ≤ m) :
    IsSmoothSubmersion (𝓡 m) (𝓡 r) (orbitHeadProjection hr) := by
  -- Package the coordinate projection as a continuous linear map so smoothness and derivative
  -- surjectivity are both reduced to linear algebra on Euclidean space.
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    { toFun := orbitHeadProjection hr
      map_add' := by
        intro x y
        ext i
        simp [orbitHeadProjection]
      map_smul' := by
        intro c x
        ext i
        simp [orbitHeadProjection]
      cont := continuous_orbitHeadProjection hr }
  refine ⟨?_, ?_⟩
  · -- Linear maps between Euclidean model spaces are smooth.
    simpa [L] using
      (L.contMDiff : ContMDiff (𝓡 m) (𝓡 r) ∞ L)
  · intro x
    rw [mfderiv_eq_fderiv]
    have hderiv :
        fderiv ℝ (orbitHeadProjection hr) x = L := by
      simpa [L, orbitHeadProjection] using (L.hasFDerivAt).fderiv
    rw [hderiv]
    -- Surjectivity comes from the standard zero-tail inclusion right inverse.
    intro y
    refine ⟨LocalNormalFormAPI.rank_normal_form r m r y, ?_⟩
    exact orbitHeadProjection_rankNormalForm hr y

/-- Helper for Remark 7.50-extra-5: the Euclidean first-coordinate projection is an open map. -/
theorem orbitHeadProjection_isOpenMap
    {m r : ℕ} (hr : r ≤ m) :
    IsOpenMap (orbitHeadProjection hr) := by
  -- Package the coordinate projection as a continuous linear map and apply the Banach open
  -- mapping theorem using the explicit zero-tail right inverse.
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    { toFun := orbitHeadProjection hr
      map_add' := by
        intro x y
        ext i
        simp [orbitHeadProjection]
      map_smul' := by
        intro c x
        ext i
        simp [orbitHeadProjection]
      cont := continuous_orbitHeadProjection hr }
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨LocalNormalFormAPI.rank_normal_form r m r y, ?_⟩
    exact orbitHeadProjection_rankNormalForm hr y
  -- The projection is the underlying map of this surjective continuous linear map.
  simpa [L] using L.isOpenMap hsurj

/-- Helper for Remark 7.50-extra-5: applying the target head projection to the rank normal form
recovers the source head projection. -/
theorem headProjection_rankNormalForm
    {m n r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n)
    (x : EuclideanSpace ℝ (Fin m)) :
    orbitHeadProjection hrn (LocalNormalFormAPI.rank_normal_form m n r x) =
      orbitHeadProjection hrm x := by
  -- On the first `r` target coordinates, the rank normal form literally returns the matching
  -- source coordinate.
  ext i
  change LocalNormalFormAPI.rank_normal_form m n r x (Fin.castLE hrn i) = x (Fin.castLE hrm i)
  exact LocalNormalFormAPI.rank_normal_form_apply_of_lt i.2 (lt_of_lt_of_le i.2 hrm) x

/-- Helper for Remark 7.50-extra-5: the rank normal form depends only on the first `r` source
coordinates. -/
theorem rankNormalForm_eq_iff_headProjection_eq
    {m n r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n)
    {x y : EuclideanSpace ℝ (Fin m)} :
    LocalNormalFormAPI.rank_normal_form m n r x =
      LocalNormalFormAPI.rank_normal_form m n r y ↔
      orbitHeadProjection hrm x = orbitHeadProjection hrm y := by
  constructor
  · intro hEq
    -- Compare the first `r` target coordinates of the two equal normal-form values.
    calc
      orbitHeadProjection hrm x =
          orbitHeadProjection hrn (LocalNormalFormAPI.rank_normal_form m n r x) := by
            symm
            exact headProjection_rankNormalForm hrm hrn x
      _ = orbitHeadProjection hrn (LocalNormalFormAPI.rank_normal_form m n r y) := by
            rw [hEq]
      _ = orbitHeadProjection hrm y := headProjection_rankNormalForm hrm hrn y
  · intro hHead
    -- Split target coordinates into the first `r` slots and the zero tail forced by the normal
    -- form.
    ext i
    rcases lt_or_ge i.1 r with hi | hi
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin r) ↦ v ⟨i.1, hi⟩) hHead
      rw [LocalNormalFormAPI.rank_normal_form_apply_of_lt hi (lt_of_lt_of_le hi hrm) x,
        LocalNormalFormAPI.rank_normal_form_apply_of_lt hi (lt_of_lt_of_le hi hrm) y]
      simpa [orbitHeadProjection] using hcoord
    · have hnot : ¬ i.1 < r := Nat.not_lt_of_ge hi
      simpa [_root_.rank_normal_form, hnot]

/-- Helper: on a neighborhood where the orbit map is in local normal
form, quotient classes are detected by equality of the normal-form coordinates. -/
theorem quotientMk_eq_iff_rankNormalForm_eqOnOrbitNormalFormNeighborhood
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    {g₁ g₂ : G}
    (hg₁ : g₁ ∈ hNF.domChart.source)
    (hg₂ : g₂ ∈ hNF.domChart.source) :
    ((QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂) ↔
      LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₁) =
        LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₂) := by
  have hOrbit1 : orbit_map G p g₁ ∈ hNF.codChart.source := hNF.mapsTo hg₁
  have hOrbit2 : orbit_map G p g₂ ∈ hNF.codChart.source := hNF.mapsTo hg₂
  have hChart1 :
      hNF.codChart (orbit_map G p g₁) =
        LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₁) := by
    -- Evaluate the local normal-form equation on the image of `g₁` under the source chart.
    have hEq := hNF.eqOn (hNF.domChart.map_source hg₁)
    simpa [Function.comp, OpenPartialHomeomorph.left_inv hNF.domChart hg₁] using hEq
  have hChart2 :
      hNF.codChart (orbit_map G p g₂) =
        LocalNormalFormAPI.rank_normal_form m n r (hNF.domChart g₂) := by
    -- The same chart computation identifies the orbit-map value of `g₂`.
    have hEq := hNF.eqOn (hNF.domChart.map_source hg₂)
    simpa [Function.comp, OpenPartialHomeomorph.left_inv hNF.domChart hg₂] using hEq
  constructor
  · intro hq
    -- Quotient equality first gives equality in the orbit, then the normal-form chart rewrites it.
    have hOrbitEq : orbit_map G p g₁ = orbit_map G p g₂ :=
      (quotientMk_eq_iff_orbitMap_eq p g₁ g₂).mp hq
    rw [← hChart1, ← hChart2, hOrbitEq]
  · intro hRankEq
    -- Equality of the normal-form coordinates pulls back through the target chart to the orbit.
    have hOrbitChartEq :
        hNF.codChart (orbit_map G p g₁) = hNF.codChart (orbit_map G p g₂) := by
      rw [hChart1, hChart2, hRankEq]
    have hOrbitEq : orbit_map G p g₁ = orbit_map G p g₂ := by
      calc
        orbit_map G p g₁ =
            hNF.codChart.symm (hNF.codChart (orbit_map G p g₁)) := by
              symm
              exact OpenPartialHomeomorph.left_inv hNF.codChart hOrbit1
        _ = hNF.codChart.symm (hNF.codChart (orbit_map G p g₂)) := by rw [hOrbitChartEq]
        _ = orbit_map G p g₂ := OpenPartialHomeomorph.left_inv hNF.codChart hOrbit2
    exact (quotientMk_eq_iff_orbitMap_eq p g₁ g₂).mpr hOrbitEq

/-- Helper for Remark 7.50-extra-5: on a normal-form neighborhood for the orbit map, quotient
classes are already detected by equality of the first `r` source coordinates. -/
theorem quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n)
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    {g₁ g₂ : G}
    (hg₁ : g₁ ∈ hNF.domChart.source)
    (hg₂ : g₂ ∈ hNF.domChart.source) :
    ((QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂) ↔
      orbitHeadProjection hrm (hNF.domChart g₁) =
        orbitHeadProjection hrm (hNF.domChart g₂) := by
  -- First convert quotient equality into equality of the local normal-form values, then normalize
  -- that equality to the first `r` source coordinates.
  rw [← rankNormalForm_eq_iff_headProjection_eq hrm hrn]
  exact
    quotientMk_eq_iff_rankNormalForm_eqOnOrbitNormalFormNeighborhood
      p hNF hg₁ hg₂

/-- Helper for Remark 7.50-extra-5: the quotient image of the source patch in the orbit-map
normal form is open in the stabilizer quotient. -/
theorem orbitQuotientPatchImage_open
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpen (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) := by
  letI : IsTopologicalGroup G :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
  -- The quotient projection is open, so it carries the open source patch to an open quotient
  -- patch.
  simpa using
    (QuotientGroup.isOpenMap_coe _ hNF.domChart.open_source)

/-- Helper for Remark 7.50-extra-5: restricting the quotient projection to the source patch
produces the open-quotient map onto the quotient patch used for descending coordinates. -/
theorem orbitQuotientPatchProjection_isOpenQuotientMap
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpenQuotientMap (fun g : hNF.domChart.source ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  letI : IsTopologicalGroup G :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
  let Uq : Set (G ⧸ MulAction.stabilizer G p) :=
    ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source
  have hUq_open : IsOpen Uq := orbitQuotientPatchImage_open p hNF
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rcases q.2 with ⟨g, hg, hgq⟩
    -- Every quotient-patch point has a representative inside the chosen source patch.
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    simpa using hgq
  · -- The restricted quotient projection is continuous because the ambient quotient map is.
    exact
      (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk
          (fun g ↦ by
            exact ⟨(g : G), g.2, rfl⟩)
  · intro s hs
    -- Open subsets of the source patch stay open after first forgetting the subtype and then
    -- applying the ambient open quotient map.
    have hUqEmbedding :
        Topology.IsOpenEmbedding (Subtype.val : Uq → G ⧸ MulAction.stabilizer G p) :=
      hUq_open.isOpenEmbedding_subtypeVal
    rw [hUqEmbedding.isOpen_iff_image_isOpen]
    have hDomChartOpenSource : IsOpen hNF.domChart.source := hNF.domChart.open_source
    have hSourceEmbedding :
        Topology.IsOpenEmbedding (Subtype.val : hNF.domChart.source → G) :=
      hDomChartOpenSource.isOpenEmbedding_subtypeVal
    have hSourceOpenMap : IsOpenMap (Subtype.val : hNF.domChart.source → G) :=
      hSourceEmbedding.isOpenMap
    have hsAmbient : IsOpen ((Subtype.val : hNF.domChart.source → G) '' s) := by
      exact hSourceOpenMap s hs
    simpa [Uq, Set.image_image] using
      (QuotientGroup.isOpenMap_coe
        ((Subtype.val : hNF.domChart.source → G) '' s) hsAmbient)

/-- Helper for Remark 7.50-extra-5: the head projection carries the target patch of the source
chart to an open subset of `EuclideanSpace ℝ (Fin r)`. -/
theorem orbitHeadProjection_targetPatchImage_open
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpen (orbitHeadProjection hrm '' hNF.domChart.target) := by
  -- The target chart is open, and the Euclidean head projection is an open map.
  exact orbitHeadProjection_isOpenMap hrm _ hNF.domChart.open_target

/-- Helper for Remark 7.50-extra-5: restricting the Euclidean head projection to the target patch
produces the open-quotient map onto its image. -/
theorem orbitHeadProjection_targetPatch_isOpenQuotientMap
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpenQuotientMap (fun x : hNF.domChart.target ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)) := by
  let W : Set (EuclideanSpace ℝ (Fin r)) := orbitHeadProjection hrm '' hNF.domChart.target
  have hW_open : IsOpen W := orbitHeadProjection_targetPatchImage_open hrm p hNF
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rcases y.2 with ⟨x, hx, hxy⟩
    -- By construction, every point in the image patch comes from a target-patch point.
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa using hxy
  · -- Restrict the continuous Euclidean projection to the open target patch.
    exact ((continuous_orbitHeadProjection hrm).comp continuous_subtype_val).subtype_mk
      (fun x ↦ by
        exact ⟨(x : EuclideanSpace ℝ (Fin m)), x.2, rfl⟩)
  · intro s hs
    -- Open subsets of the target patch stay open after forgetting the subtype and applying the
    -- ambient open projection.
    have hWEmbedding :
        Topology.IsOpenEmbedding (Subtype.val : W → EuclideanSpace ℝ (Fin r)) :=
      hW_open.isOpenEmbedding_subtypeVal
    rw [hWEmbedding.isOpen_iff_image_isOpen]
    have hDomChartOpenTarget : IsOpen hNF.domChart.target := hNF.domChart.open_target
    have hTargetEmbedding :
        Topology.IsOpenEmbedding
          (Subtype.val : hNF.domChart.target → EuclideanSpace ℝ (Fin m)) :=
      hDomChartOpenTarget.isOpenEmbedding_subtypeVal
    have hTargetOpenMap :
        IsOpenMap (Subtype.val : hNF.domChart.target → EuclideanSpace ℝ (Fin m)) :=
      hTargetEmbedding.isOpenMap
    have hsAmbient :
        IsOpen ((Subtype.val : hNF.domChart.target → EuclideanSpace ℝ (Fin m)) '' s) := by
      exact hTargetOpenMap s hs
    simpa [W, Set.image_image] using orbitHeadProjection_isOpenMap hrm _ hsAmbient

/-- Helper for Remark 7.50-extra-5: the quotient patch at the identity coset carries the forward
local coordinate obtained by descending the head projection through the quotient patch map. -/
noncomputable def orbitQuotientPatchForward
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source),
      orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      refine ⟨orbitHeadProjection hrm (hNF.domChart g), ?_⟩
      exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩
    · -- Restrict the chart to its source patch, then compose with the Euclidean head projection.
      have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦
            orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            show orbitHeadProjection hrm (hNF.domChart g) ∈
                orbitHeadProjection hrm '' hNF.domChart.target
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  -- Descend the representative-level coordinate through the open quotient map on the source patch.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        -- Fiberwise quotient equality is exactly the normal-form head-projection criterion.
        exact
          (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
            hrm hrn p hNF a.2 b.2).mp
            (by simpa [proj] using congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: the identity-coset quotient patch also carries the inverse
local coordinate obtained by descending the inverse source chart through the head-projection patch
map. -/
noncomputable def orbitQuotientPatchInverse
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((orbitHeadProjection hrm '' hNF.domChart.target),
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p), ?_⟩
      exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩
    · -- Restrict the inverse chart to the target patch, then compose with the quotient projection.
      have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            show (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) ∈
                ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  -- Descend the representative-level inverse coordinate through the head-projection quotient map.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        -- Equal head projections on the target patch lift back to the same quotient class.
        refine
          (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
            hrm hrn p hNF
            (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
        simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
          OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
          (congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: on the canonical quotient-patch representative, the descended
forward coordinate map agrees with the source-chart head projection used to define it. -/
theorem orbitQuotientPatchForward_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchForward hrm hrn p hNF :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) →
          orbitHeadProjection hrm '' hNF.domChart.target) ∘
      (fun g : hNF.domChart.source ↦
        (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)))) =
      fun g : hNF.domChart.source ↦
        (⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
          rfl⟩⟩ : orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMap p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      exact ⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
        rfl⟩⟩
    · have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦ orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    exact
      (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
        hrm hrn p hNF a.2 b.2).mp
        (by simpa [proj] using congrArg Subtype.val hab)
  -- Compare the descended continuous map with its representative-level model before evaluation.
  funext g
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) g = raw g
  exact congrArg (fun f ↦ f g) hcomp

/-- Helper for Remark 7.50-extra-5: on the canonical head-projection representative, the descended
inverse coordinate map agrees with the inverse source chart used to define it. -/
theorem orbitQuotientPatchInverse_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchInverse hrm hrn p hNF :
        orbitHeadProjection hrm '' hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) ∘
      (fun x : hNF.domChart.target ↦
        (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
          orbitHeadProjection hrm '' hNF.domChart.target))) =
      fun x : hNF.domChart.target ↦
        (⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
          ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
        ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩
    · have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    refine
      (quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
        hrm hrn p hNF
        (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
    simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
      OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
      (congrArg Subtype.val hab)
  -- Compare the descended inverse with the representative-level inverse before evaluation.
  funext x
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) x = raw x
  exact congrArg (fun f ↦ f x) hcomp

/-- Helper for Remark 7.50-extra-5: after projecting to the first `r` source coordinates, the
rank normal form depends only on those coordinates. -/
theorem rankNormalForm_factor_through_headProjection
    {m n r : ℕ} (hrm : r ≤ m)
    (x : EuclideanSpace ℝ (Fin m)) :
    LocalNormalFormAPI.rank_normal_form m n r x =
      LocalNormalFormAPI.rank_normal_form r n r (orbitHeadProjection hrm x) := by
  -- Compare target coordinates directly: both normal forms have the same leading `r` coordinates
  -- and the same zero tail.
  ext i
  rcases lt_or_ge i.1 r with hi | hi
  · rw [LocalNormalFormAPI.rank_normal_form_apply_of_lt hi (lt_of_lt_of_le hi hrm) x]
    rw [LocalNormalFormAPI.rank_normal_form_apply_of_lt hi hi (orbitHeadProjection hrm x)]
    simp [orbitHeadProjection]
  · have hnot : ¬ i.1 < r := Nat.not_lt_of_ge hi
    simp [_root_.rank_normal_form, hnot]

/-- Helper for Remark 7.50-extra-5: the descended forward and inverse patch coordinates at the
identity coset package into a genuine homeomorphism between the quotient patch owner and the open
head-projection image patch. -/
noncomputable def orbitQuotientPatchAtOneHomeomorph
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) ≃ₜ
      orbitHeadProjection hrm '' hNF.domChart.target where
  toEquiv :=
    { toFun := orbitQuotientPatchForward hrm hrn p hNF
      invFun := orbitQuotientPatchInverse hrm hrn p hNF
      left_inv := by
        rintro ⟨q, hq⟩
        rcases hq with ⟨g, hg, rfl⟩
        let gU : hNF.domChart.source := ⟨g, hg⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨g, hg, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm (hNF.domChart gU), ⟨hNF.domChart gU, hNF.domChart.map_source hg, rfl⟩⟩
        apply Subtype.ext
        -- Compare both descended patch maps with their representative-level formulas before the
        -- chart inverse collapses back to the original source-patch point.
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target => f gU)
            (orbitQuotientPatchForward_comp_projection
              hrm hrn p hNF)
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f ⟨hNF.domChart gU, hNF.domChart.map_source hg⟩)
            (orbitQuotientPatchInverse_comp_projection
              hrm hrn p hNF)
        have hForwardEval :
            orbitQuotientPatchForward hrm hrn p hNF qU = xW := by
          simpa [gU, qU, xW] using hForward
        have hInverseEval :
            orbitQuotientPatchInverse hrm hrn p hNF xW = qU := by
          simpa [gU, qU, xW, OpenPartialHomeomorph.left_inv hNF.domChart hg] using hInverse
        rw [hForwardEval, hInverseEval]
      right_inv := by
        rintro ⟨x, hx⟩
        rcases hx with ⟨y, hy, rfl⟩
        let yV : hNF.domChart.target := ⟨y, hy⟩
        let gU : hNF.domChart.source := ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨(QuotientGroup.mk (hNF.domChart.symm yV) : G ⧸ MulAction.stabilizer G p),
            ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm y, ⟨y, hy, rfl⟩⟩
        apply Subtype.ext
        -- Route correction: prove the inverse law on the target owner through the canonical
        -- target-patch representative, not by reopening quotient representatives.
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f yV)
            (orbitQuotientPatchInverse_comp_projection
              hrm hrn p hNF)
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target =>
              f gU)
            (orbitQuotientPatchForward_comp_projection
              hrm hrn p hNF)
        have hInverseEval :
            orbitQuotientPatchInverse hrm hrn p hNF xW = qU := by
          simpa [yV, gU, qU, xW] using hInverse
        have hForwardEval :
            orbitQuotientPatchForward hrm hrn p hNF qU = xW := by
          simpa [yV, gU, qU, xW, OpenPartialHomeomorph.right_inv hNF.domChart hy] using hForward
        rw [hInverseEval, hForwardEval] }
  continuous_toFun :=
    (orbitQuotientPatchForward hrm hrn p hNF).continuous
  continuous_invFun :=
    (orbitQuotientPatchInverse hrm hrn p hNF).continuous


/-- Helper for Remark 7.50-extra-5: the left action of `G` on the stabilizer quotient is a
homeomorphism with inverse given by left multiplication by `g⁻¹`. -/
noncomputable def quotientLeftTranslationHomeomorph
    [LieGroup I ∞ G] (p : M) (g : G) :
    (G ⧸ MulAction.stabilizer G p) ≃ₜ (G ⧸ MulAction.stabilizer G p) where
  toEquiv :=
    { toFun := fun q ↦ g • q
      invFun := fun q ↦ g⁻¹ • q
      left_inv := by
        intro q
        -- Cancel the two left actions in the quotient action.
        simp [smul_smul]
      right_inv := by
        intro q
        -- The inverse action is again left multiplication, now by `g⁻¹`.
        simp [smul_smul] }
  continuous_toFun := by
    -- The quotient inherits the continuous left action from the topological group structure on `G`.
    letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    simpa using (continuous_const_smul g :
      Continuous fun q : G ⧸ MulAction.stabilizer G p ↦ g • q)
  continuous_invFun := by
    -- Apply the same continuity statement to the inverse group element.
    letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    simpa using (continuous_const_smul g⁻¹ :
      Continuous fun q : G ⧸ MulAction.stabilizer G p ↦ g⁻¹ • q)

/-- Helper for Remark 7.50-extra-5: an ambient Euclidean chart transports its target-side
self-modeled atlas back to the chart-source subtype. -/
noncomputable abbrev transportedSelfModeledPatchChartedSpace
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {N : Type*} [TopologicalSpace N] [ChartedSpace ES N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    ChartedSpace ES S := by
  let _ : ChartedSpace N S :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Transport the self-modeled source charts explicitly through the singleton-chart homeomorphism.
  exact ChartedSpace.comp ES N S

/-- Helper for Remark 7.50-extra-5: transporting a self-modeled atlas across a homeomorphism
preserves the smooth manifold structure. -/
lemma transportedSelfModeledPatchIsManifold
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace ES N]
    [IsManifold (modelWithCornersSelf 𝕜 ES) n N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace ES S := by
      let _ : ChartedSpace N S := (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
        ext x
        simp)
      exact ChartedSpace.comp ES N S
    IsManifold (modelWithCornersSelf 𝕜 ES) n S := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace ES S := by
    let _ : ChartedSpace N S := eS.singletonChartedSpace (by
      ext x
      simp [eS])
    exact ChartedSpace.comp ES N S
  have hGroupoid :
      HasGroupoid S (contDiffGroupoid n (modelWithCornersSelf 𝕜 ES)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- After normalizing the singleton-chart transport, compatibility reduces to the source atlas.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
          contDiffGroupoid n (modelWithCornersSelf 𝕜 ES) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported atlas therefore defines the desired smooth manifold structure.
  exact IsManifold.mk' (modelWithCornersSelf 𝕜 ES) n S

/-- Helper for Remark 7.50-extra-5: an ambient Euclidean chart transports its target-side
self-modeled atlas back to the chart-source subtype. -/
noncomputable abbrev chartSourceEuclideanOwner
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace 𝕜 (Fin n)))
    (h : Nonempty e.target) :
    ChartedSpace (EuclideanSpace 𝕜 (Fin n)) e.source :=
  -- Route correction: transport the self-modeled Euclidean patch owner along the chart
  -- homeomorphism, instead of postulating a global auxiliary target owner on all of `M`.
  let U : TopologicalSpace.Opens (EuclideanSpace 𝕜 (Fin n)) := ⟨e.target, e.open_target⟩
  let eU : OpenPartialHomeomorph U (EuclideanSpace 𝕜 (Fin n)) :=
    U.openPartialHomeomorphSubtypeCoe h
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U :=
    eU.singletonChartedSpace (by
      simpa [eU] using U.openPartialHomeomorphSubtypeCoe_source h)
  let _ :
      ChartedSpace (EuclideanSpace 𝕜 (Fin n))
        (e.target : Set (EuclideanSpace 𝕜 (Fin n))) := by
    change ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U
    infer_instance
  let eST : (e.target : Set (EuclideanSpace 𝕜 (Fin n))) ≃ₜ e.source :=
    e.toHomeomorphSourceTarget.symm
  let _ : ChartedSpace (e.target : Set (EuclideanSpace 𝕜 (Fin n))) e.source :=
    (eST.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp [eST])
  ChartedSpace.comp (EuclideanSpace 𝕜 (Fin n))
    (e.target : Set (EuclideanSpace 𝕜 (Fin n))) e.source

/-- Helper for Remark 7.50-extra-5: the chart-source subtype transported from an ambient Euclidean
chart is itself a smooth boundaryless manifold in the self-modeled Euclidean owner. -/
lemma chartSourceEuclideanOwner_isManifold
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace 𝕜 (Fin n)))
    (h : Nonempty e.target) :
    let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) e.source := chartSourceEuclideanOwner e h
    IsManifold
      (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin n)))
      (⊤ : WithTop ℕ∞) e.source := by
  -- The transported singleton-chart atlas inherits the standard Euclidean manifold structure from
  -- the open target patch.
  let U : TopologicalSpace.Opens (EuclideanSpace 𝕜 (Fin n)) := ⟨e.target, e.open_target⟩
  let eU : OpenPartialHomeomorph U (EuclideanSpace 𝕜 (Fin n)) :=
    U.openPartialHomeomorphSubtypeCoe h
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U :=
    eU.singletonChartedSpace (by
      simpa [eU] using U.openPartialHomeomorphSubtypeCoe_source h)
  let _ :
      ChartedSpace (EuclideanSpace 𝕜 (Fin n))
        (e.target : Set (EuclideanSpace 𝕜 (Fin n))) := by
      change ChartedSpace (EuclideanSpace 𝕜 (Fin n)) U
      infer_instance
  let _ :
      IsManifold
        (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin n)))
        (⊤ : WithTop ℕ∞)
        (e.target : Set (EuclideanSpace 𝕜 (Fin n))) := by
      change IsManifold
          (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin n)))
          (⊤ : WithTop ℕ∞) U
      exact eU.isManifold_singleton (by
        simpa [eU] using U.openPartialHomeomorphSubtypeCoe_source h)
  exact
    transportedSelfModeledPatchIsManifold
      (e.toHomeomorphSourceTarget.symm)

/-- Helper for Remark 7.50-extra-5: the inverse branch of a maximal-atlas Euclidean chart is an
immersion from the open target patch back into the ambient manifold. -/
lemma euclideanChartInverse_isImmersion
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h : Nonempty e.target)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) e.target]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) e.target]
    (he : e ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M)
    (heU :
      let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.target, e.open_target⟩
      U.openPartialHomeomorphSubtypeCoe h ∈
        IsManifold.maximalAtlas
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (⊤ : WithTop ℕ∞) e.target) :
    IsImmersion
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞)
      (fun x : e.target ↦ e.symm x) := by
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.target, e.open_target⟩
  let eU : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin n)) :=
    U.openPartialHomeomorphSubtypeCoe h
  -- In the canonical target-patch chart and the ambient chart `e`, the inverse branch is the
  -- identity on Euclidean coordinates.
  refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    (.prodUnique ℝ (EuclideanSpace ℝ (Fin n)) PUnit) eU e ?_ ?_ ?_ ?_ ?_ ?_
  · -- The canonical open-subtype chart is defined on all of the target patch.
    simpa [eU] using (show x ∈ eU.source from by simp [eU])
  · -- The ambient chart inverse sends each target-patch point back to the source patch.
    exact e.map_target x.2
  · -- The canonical target-patch chart is the preferred maximal-atlas chart on the open subtype.
    simpa [U, eU] using heU
  · -- The ambient chart was assumed to lie in the original maximal atlas.
    exact he
  · intro y hy
    -- Every point in the target-patch chart source already lies in `e.target`.
    exact e.map_target y.2
  · intro u hu
    have hu_target : u ∈ eU.target := by
      simpa [eU, OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hu
    have hInversePatch :
        (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
          EuclideanSpace ℝ (Fin n)) = u := by
      simpa [eU, OpenPartialHomeomorph.extend_coe_symm] using eU.right_inv hu_target
    have hAmbientRightInv :
        e
            (e.symm
              (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
                EuclideanSpace ℝ (Fin n))) =
          (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
            EuclideanSpace ℝ (Fin n)) := by
      exact e.right_inv (((eU.extend
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U).2)
    -- After normalizing the open-subtype inverse, the chart inverse followed by `e` is the
    -- identity on the Euclidean target coordinate.
    calc
      ((e.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))) ∘
          (fun x : e.target ↦ e.symm x) ∘
            (eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm) u
          =
        e
          (e.symm
            (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
              EuclideanSpace ℝ (Fin n))) := by
              simp [Function.comp, OpenPartialHomeomorph.extend_coe,
                OpenPartialHomeomorph.extend_coe_symm]
      _ = (((eU.extend (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))).symm u : U) :
            EuclideanSpace ℝ (Fin n)) := hAmbientRightInv
      _ = u := hInversePatch

/-- Helper for Remark 7.50-extra-5: the inverse branch of a maximal-atlas Euclidean chart is an
immersion from the open target patch back into the ambient manifold for the Euclidean self owner.
-/
lemma ambientChartInverse_isImmersion
    {n : ℕ} (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h : Nonempty e.target)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) e.target]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) e.target]
    (he : e ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞) M)
    (heU :
      let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.target, e.open_target⟩
      U.openPartialHomeomorphSubtypeCoe h ∈
        IsManifold.maximalAtlas
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (⊤ : WithTop ℕ∞) e.target) :
    IsImmersion
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞)
      (fun x : e.target ↦ e.symm x) := by
  -- Route correction: the earlier `J`-owner version was ill-typed because `e` is a Euclidean
  -- chart, so maximal-atlas membership can only be asked for the Euclidean self owner here.
  exact euclideanChartInverse_isImmersion e h he heU

/-- Helper for Remark 7.50-extra-5: the orbit map has one fixed rank `r`, and at every
representative `g : G` the constant-rank theorem gives local coordinates with normal form
`rank_normal_form m n r`. -/
theorem orbitMapLocalNormalFormAtRepresentative
    {m n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) :
    ∃ r : ℕ,
      ∀ g : G,
        ∃ h : LocalNormalFormAPI.LocalCoordinateNormalFormAt
          (orbit_map G p) g (LocalNormalFormAPI.rank_normal_form m n r),
          True := by
  -- First pin down the global constant rank of the orbit map.
  let IG : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  let JM : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let _ : LieGroup IG ∞ G := by
    simpa [IG] using (inferInstance : LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G)
  let _ : IsManifold JM ∞ M := by
    simpa [JM] using
      (inferInstance : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M)
  let _ : ContMDiffSMul IG JM ∞ G M := by
    simpa [IG, JM] using
      (inferInstance :
        ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M)
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank IG JM (orbit_map G p) r :=
    orbitMapHasConstantRank p
  rcases hConstRank with ⟨r, hRank⟩
  refine ⟨r, ?_⟩
  intro g
  -- Then apply the constant-rank local normal form theorem at the chosen representative.
  rcases constant_rank_local_coordinate_normal_form
      (orbitMap_contMDiff p) hRank g with ⟨hNF, _⟩
  exact ⟨hNF, trivial⟩

/-- Helper for Remark 7.50-extra-5: once the orbit-map normal form is centered at a representative
`g₀`, equality of quotient classes on that source patch is still detected by the Euclidean head
projection. -/
theorem quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ g₁ g₂ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (hg₁ : g₁ ∈ hNF.domChart.source)
    (hg₂ : g₂ ∈ hNF.domChart.source) :
    ((QuotientGroup.mk g₁ : G ⧸ MulAction.stabilizer G p) = QuotientGroup.mk g₂) ↔
      orbitHeadProjection hrm (hNF.domChart g₁) =
        orbitHeadProjection hrm (hNF.domChart g₂) := by
  -- Route correction: the quotient-detection argument only uses the representative-local normal
  -- form itself, so it works unchanged away from the identity patch.
  exact
    quotientMk_eq_iff_headProjection_eqOnOrbitNormalFormNeighborhood
      hrm hrn p hNF hg₁ hg₂

/-- Helper for Remark 7.50-extra-5: the quotient image of a representative-local normal-form
source patch is open in the stabilizer quotient. -/
theorem orbitQuotientPatchImage_openAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpen (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) := by
  -- The open-image descent never used that the normal form was centered at `1`.
  exact orbitQuotientPatchImage_open p hNF

/-- Helper for Remark 7.50-extra-5: the restricted quotient projection on a representative-local
normal-form source patch is an open quotient map. -/
theorem orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    IsOpenQuotientMap (fun g : hNF.domChart.source ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  -- The quotient-descent map is again identical to the identity-centered version; only the chosen
  -- local normal form has changed.
  exact orbitQuotientPatchProjection_isOpenQuotientMap p hNF

/-- Helper for Remark 7.50-extra-5: the representative-local quotient patch carries the forward
local coordinate obtained by descending the head projection through the quotient patch map. -/
noncomputable def orbitQuotientPatchForwardAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source),
      orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      refine ⟨orbitHeadProjection hrm (hNF.domChart g), ?_⟩
      exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩
    · -- Restrict the representative chart to its source patch before projecting to the shared
      -- Euclidean head coordinates.
      have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦
            orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            show orbitHeadProjection hrm (hNF.domChart g) ∈
                orbitHeadProjection hrm '' hNF.domChart.target
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  -- Route correction: the quotient descent only depends on the representative-local normal form,
  -- not on the center being `1`, so the same quotient-map lift works unchanged here.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        exact
          (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
            hrm hrn p hNF a.2 b.2).mp
            (by simpa [proj] using congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: the representative-local quotient patch also carries the
inverse local coordinate obtained by descending the inverse source chart through the head-projection
patch map. -/
noncomputable def orbitQuotientPatchInverseAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    C((orbitHeadProjection hrm '' hNF.domChart.target),
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p), ?_⟩
      exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩
    · -- Restrict the representative inverse chart to the target patch before quotienting the
      -- representative back to the stabilizer quotient.
      have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            show (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) ∈
                ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  -- Equal head projections on the representative-local target patch still lift to the same
  -- stabilizer quotient class.
  exact
    hproj.lift raw
      (fun a b hab ↦ by
        apply Subtype.ext
        refine
          (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
            hrm hrn p hNF
            (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
        simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
          OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
          (congrArg Subtype.val hab))

/-- Helper for Remark 7.50-extra-5: on the canonical representative-local quotient-patch
representative, the descended forward coordinate map agrees with the source-chart head projection
used to define it. -/
theorem orbitQuotientPatchForwardAtRepresentative_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) →
          orbitHeadProjection hrm '' hNF.domChart.target) ∘
      (fun g : hNF.domChart.source ↦
        (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)))) =
      fun g : hNF.domChart.source ↦
        (⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
          rfl⟩⟩ : orbitHeadProjection hrm '' hNF.domChart.target) := by
  let proj :
      C(hNF.domChart.source,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨(fun g ↦
      (⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨(g : G), g.2, rfl⟩⟩ :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source))), ?_⟩
    simpa using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitQuotientPatchProjection_isOpenQuotientMapAtRepresentative p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.source, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨?_, ?_⟩
    · intro g
      exact ⟨orbitHeadProjection hrm (hNF.domChart g), ⟨hNF.domChart g, hNF.domChart.map_source g.2,
        rfl⟩⟩
    · have hChartOn := hNF.domChart.continuousOn_toFun
      have hChart : Continuous fun g : hNF.domChart.source ↦ hNF.domChart g :=
        hChartOn.restrict
      have hHead :
          Continuous fun g : hNF.domChart.source ↦ orbitHeadProjection hrm (hNF.domChart g) :=
        (continuous_orbitHeadProjection hrm).comp hChart
      exact
        Continuous.subtype_mk hHead
          (fun g ↦ by
            exact ⟨hNF.domChart g, hNF.domChart.map_source g.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    exact
      (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
        hrm hrn p hNF a.2 b.2).mp
        (by simpa [proj] using congrArg Subtype.val hab)
  -- Compare the descended representative-local forward map with its model before evaluation.
  funext g
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) g = raw g
  exact congrArg (fun f ↦ f g) hcomp

/-- Helper for Remark 7.50-extra-5: on the canonical representative-local head-projection
representative, the descended inverse coordinate map agrees with the inverse source chart used to
define it. -/
theorem orbitQuotientPatchInverseAtRepresentative_comp_projection
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ((orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF :
        orbitHeadProjection hrm '' hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) ∘
      (fun x : hNF.domChart.target ↦
        (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
          orbitHeadProjection hrm '' hNF.domChart.target))) =
      fun x : hNF.domChart.target ↦
        (⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
          ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
  let proj :
      C(hNF.domChart.target, orbitHeadProjection hrm '' hNF.domChart.target) := by
    refine ⟨(fun x ↦
      (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
        orbitHeadProjection hrm '' hNF.domChart.target)), ?_⟩
    simpa using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).continuous
  have hproj : Topology.IsQuotientMap proj := by
    simpa [proj] using
      (orbitHeadProjection_targetPatch_isOpenQuotientMap hrm p hNF).isQuotientMap
  let raw :
      C(hNF.domChart.target,
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact ⟨(QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p),
        ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩
    · have hSymmOn := hNF.domChart.continuousOn_invFun
      have hSymm : Continuous fun x : hNF.domChart.target ↦ hNF.domChart.symm x :=
        hSymmOn.restrict
      have hMk :
          Continuous fun x : hNF.domChart.target ↦
            (QuotientGroup.mk (hNF.domChart.symm x) : G ⧸ MulAction.stabilizer G p) :=
        QuotientGroup.continuous_mk.comp hSymm
      exact
        Continuous.subtype_mk hMk
          (fun x ↦ by
            exact ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩)
  have hfactor : Function.FactorsThrough raw proj := by
    intro a b hab
    apply Subtype.ext
    refine
      (quotientMk_eq_iff_headProjection_eqOnRepresentativeNeighborhood
        hrm hrn p hNF
        (hNF.domChart.map_target a.2) (hNF.domChart.map_target b.2)).mpr ?_
    simpa [OpenPartialHomeomorph.right_inv hNF.domChart a.2,
      OpenPartialHomeomorph.right_inv hNF.domChart b.2, proj] using
      (congrArg Subtype.val hab)
  -- Compare the descended representative-local inverse with the inverse-chart model before
  -- evaluation.
  funext x
  have hcomp :
      (hproj.lift raw hfactor).comp proj = raw :=
    Topology.IsQuotientMap.lift_comp hproj raw hfactor
  change ((hproj.lift raw hfactor).comp proj) x = raw x
  exact congrArg (fun f ↦ f x) hcomp

/-- Helper for Remark 7.50-extra-5: the descended forward and inverse patch coordinates at an
arbitrary representative package into a genuine homeomorphism between the quotient patch owner and
the open head-projection image patch. -/
noncomputable def orbitQuotientPatchAtRepresentativeHomeomorph
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) ≃ₜ
      orbitHeadProjection hrm '' hNF.domChart.target where
  toEquiv :=
    { toFun := orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF
      invFun := orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF
      left_inv := by
        rintro ⟨q, hq⟩
        rcases hq with ⟨g, hg, rfl⟩
        let gU : hNF.domChart.source := ⟨g, hg⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨((g : G) : G ⧸ MulAction.stabilizer G p), ⟨g, hg, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm (hNF.domChart gU),
            ⟨hNF.domChart gU, hNF.domChart.map_source hg, rfl⟩⟩
        apply Subtype.ext
        -- Reduce both descended representative-local patch maps to their representative formulas
        -- before cancelling the chart inverse.
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target => f gU)
            (orbitQuotientPatchForwardAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f ⟨hNF.domChart gU, hNF.domChart.map_source hg⟩)
            (orbitQuotientPatchInverseAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hForwardEval :
            orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU = xW := by
          simpa [gU, qU, xW] using hForward
        have hInverseEval :
            orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW = qU := by
          simpa [gU, qU, xW, OpenPartialHomeomorph.left_inv hNF.domChart hg] using hInverse
        rw [hForwardEval, hInverseEval]
      right_inv := by
        rintro ⟨x, hx⟩
        rcases hx with ⟨y, hy, rfl⟩
        let yV : hNF.domChart.target := ⟨y, hy⟩
        let gU : hNF.domChart.source := ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy⟩
        let qU :
            (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
          ⟨(QuotientGroup.mk (hNF.domChart.symm yV) : G ⧸ MulAction.stabilizer G p),
            ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy, rfl⟩⟩
        let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
          ⟨orbitHeadProjection hrm y, ⟨y, hy, rfl⟩⟩
        apply Subtype.ext
        -- Route correction: use the canonical target-patch representative on the arbitrary patch
        -- as well, so the inverse law stays in the same spelling world as the identity patch.
        have hInverse :=
          congrArg
            (fun f : hNF.domChart.target →
                (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
              f yV)
            (orbitQuotientPatchInverseAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hForward :=
          congrArg
            (fun f : hNF.domChart.source →
                orbitHeadProjection hrm '' hNF.domChart.target =>
              f gU)
            (orbitQuotientPatchForwardAtRepresentative_comp_projection
              hrm hrn p hNF)
        have hInverseEval :
            orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW = qU := by
          simpa [yV, gU, qU, xW] using hInverse
        have hForwardEval :
            orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU = xW := by
          simpa [yV, gU, qU, xW, OpenPartialHomeomorph.right_inv hNF.domChart hy] using hForward
        rw [hInverseEval, hForwardEval] }
  continuous_toFun :=
    (orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF).continuous
  continuous_invFun :=
    (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF).continuous

/-- Helper for Remark 7.50-extra-5: in representative-local quotient coordinates, the descended
orbit map is written by the canonical rank-`r` inclusion. -/
theorem ofQuotientStabilizer_writtenInRepresentativePatch
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    hNF.codChart ∘ MulAction.ofQuotientStabilizer G p ∘ Subtype.val ∘
        orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF =
      fun x : orbitHeadProjection hrm '' hNF.domChart.target ↦
        LocalNormalFormAPI.rank_normal_form r n r x.1 := by
  funext x
  rcases x.2 with ⟨y, hy, hxy⟩
  let yV : hNF.domChart.target := ⟨y, hy⟩
  let qU :
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
    ⟨(QuotientGroup.mk (hNF.domChart.symm yV) : G ⧸ MulAction.stabilizer G p),
      ⟨hNF.domChart.symm yV, hNF.domChart.map_target hy, rfl⟩⟩
  let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
    ⟨orbitHeadProjection hrm y, ⟨y, hy, rfl⟩⟩
  have hxW : x = xW := by
    -- Identify the arbitrary point in the image patch with its canonical representative.
    apply Subtype.ext
    exact hxy.symm
  have hInverse :=
    congrArg
      (fun f : hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) =>
        f yV)
      (orbitQuotientPatchInverseAtRepresentative_comp_projection
        hrm hrn p hNF)
  have hInverseEval :
      orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW = qU := by
    -- Evaluate the descended inverse on the canonical target-patch representative.
    simpa [yV, qU, xW] using hInverse
  have hChartEq :
      hNF.codChart (MulAction.ofQuotientStabilizer G p qU) =
        LocalNormalFormAPI.rank_normal_form m n r y := by
    -- The representative chosen by the inverse patch map lies on the normal-form branch of `hNF`.
    simpa [Function.comp, yV, qU, orbit_map, MulAction.ofQuotientStabilizer_mk,
      OpenPartialHomeomorph.right_inv hNF.domChart hy] using hNF.eqOn hy
  -- Compare the written-in-charts expression first with the representative-level inverse, then
  -- collapse the remaining `m`-coordinate normal form through the head projection.
  calc
    hNF.codChart
        (MulAction.ofQuotientStabilizer G p
          (Subtype.val (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF x)))
        = hNF.codChart
            (MulAction.ofQuotientStabilizer G p
              (Subtype.val (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW))) := by
                rw [hxW]
    hNF.codChart
        (MulAction.ofQuotientStabilizer G p
          (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW))
        = hNF.codChart (MulAction.ofQuotientStabilizer G p qU) := by
            rw [hInverseEval]
    _ = LocalNormalFormAPI.rank_normal_form m n r y := hChartEq
    _ = LocalNormalFormAPI.rank_normal_form r n r (orbitHeadProjection hrm y) := by
          exact rankNormalForm_factor_through_headProjection (n := n) hrm y
    _ = LocalNormalFormAPI.rank_normal_form r n r x.1 := by
          rw [hxW]

/-- Helper for Remark 7.50-extra-5: the constant rank of the orbit map cannot exceed the source
dimension of the Lie group. -/
theorem orbitMapConstantRank_le_sourceFinrank
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] (p : M)
    {r : ℕ} (hRank : Manifold.HasConstantRank I J (orbit_map G p) r) :
    r ≤ Module.finrank 𝕜 E := by
  let _ : FiniteDimensional 𝕜 (TangentSpace I (1 : G)) := by
    simpa using (inferInstance : FiniteDimensional 𝕜 E)
  have hRankAt :
      rankAt I J (orbit_map G p) (1 : G) =
        Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) :=
    rankAt_eq_finrank_range_mfderiv (orbit_map G p) (1 : G)
  have hRankOne :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) = r := by
    -- Evaluate the constant-rank witness at the identity and rewrite the rank through `mfderiv`.
    simpa [hRank.2 (1 : G)] using hRankAt.symm
  have hRangeLe :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) ≤
        Module.finrank 𝕜 E := by
    -- The image of the derivative is the range of a linear map out of the source tangent space.
    simpa using
      (LinearMap.finrank_range_le
        ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap))
  omega

/-- Helper for Remark 7.50-extra-5: the constant rank of the orbit map cannot exceed the target
dimension of the ambient manifold. -/
theorem orbitMapConstantRank_le_targetFinrank
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] (p : M)
    {r : ℕ} (hRank : Manifold.HasConstantRank I J (orbit_map G p) r) :
    r ≤ Module.finrank 𝕜 E' := by
  let _ : FiniteDimensional 𝕜 (TangentSpace J (orbit_map G p (1 : G))) := by
    simpa [orbit_map] using (inferInstance : FiniteDimensional 𝕜 E')
  have hRankAt :
      rankAt I J (orbit_map G p) (1 : G) =
        Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) :=
    rankAt_eq_finrank_range_mfderiv (orbit_map G p) (1 : G)
  have hRankOne :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) = r := by
    -- The constant-rank witness still reads off the derivative rank at the identity.
    simpa [hRank.2 (1 : G)] using hRankAt.symm
  have hRangeLe :
      Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) ≤
        Module.finrank 𝕜 E' := by
    -- The derivative image is a submodule of the target tangent space at `p = orbit_map G p 1`.
    simpa [orbit_map] using
      (Submodule.finrank_le
        ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range))
  omega

/-- Helper for Remark 7.50-extra-5: the constant-rank route packages a single global rank together
with both ambient finiteness bounds needed by the quotient-patch normal form. -/
theorem orbitMapConstantRankBounds
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] (p : M) :
    ∃ r : ℕ, ∃ hRank : Manifold.HasConstantRank I J (orbit_map G p) r,
      r ≤ Module.finrank 𝕜 E ∧ r ≤ Module.finrank 𝕜 E' := by
  rcases orbitMapHasConstantRank (I := I) (J := J) (G := G) (M := M) p with ⟨r, hRank⟩
  refine ⟨r, hRank, ?_⟩
  constructor
  · -- The source-dimension bound is the first half of the constant-rank package used later.
    exact orbitMapConstantRank_le_sourceFinrank (I := I) (J := J) p hRank
  · -- The target-dimension bound is the second half of the same package.
    exact orbitMapConstantRank_le_targetFinrank (I := I) (J := J) p hRank

/-- Helper for Remark 7.50-extra-5: transporting a self-modeled source patch across a
homeomorphism preserves immersions into the fixed ambient target `M`. -/
lemma transportedAmbientMapIsImmersionPatch
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace ES N]
    [IsManifold (modelWithCornersSelf 𝕜 ES) n N]
    {S : Type*} [TopologicalSpace S] {g : N → M} {ι : S → M}
    (hg : IsImmersion (modelWithCornersSelf 𝕜 ES) J n g)
    (e : N ≃ₜ S) (he : ∀ x, ι (e x) = g x) :
    let _ : ChartedSpace ES S := transportedSelfModeledPatchChartedSpace (𝕜 := 𝕜) e
    let _ : IsManifold (modelWithCornersSelf 𝕜 ES) n S :=
      transportedSelfModeledPatchIsManifold (𝕜 := 𝕜) e
    IsImmersion (modelWithCornersSelf 𝕜 ES) J n ι := by
  let instCharted : ChartedSpace ES S := transportedSelfModeledPatchChartedSpace (𝕜 := 𝕜) e
  let _ : ChartedSpace ES S := instCharted
  let instManifold : IsManifold (modelWithCornersSelf 𝕜 ES) n S :=
    transportedSelfModeledPatchIsManifold (𝕜 := 𝕜) e
  let _ : IsManifold (modelWithCornersSelf 𝕜 ES) n S := instManifold
  let hCompImm := hg.isImmersionOfComplement_complement
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  -- Route correction: move the homeomorphism transport entirely to the source side, so the
  -- codomain chart data from the original immersion proof is reused without any new target owner.
  refine ⟨hg.complement, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm (e.symm x)
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (eS.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · -- The transported source chart still contains the chosen point.
    simpa [eS, OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · -- The codomain chart condition is exactly the old pointwise condition for `g`.
    have hxe : g (e.symm x) = ι x := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · -- Maximal-atlas membership on the transported source reduces to the original source chart.
    intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext z
        simp [eS]) f hf
    subst f
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
            contDiffGroupoid n (modelWithCornersSelf 𝕜 ES) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid n (modelWithCornersSelf 𝕜 ES) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · -- Source points in the transported chart map into the codomain chart source because
    -- `ι ∘ e = g`.
    intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [eS, OpenPartialHomeomorph.trans_source] using hz
    have hze : g (e.symm z) = ι z := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · -- After normalizing the transported source chart, the written-in-charts formula is exactly
    -- the old one for `g`.
    intro u hu
    have hu' : u ∈ (hx.domChart.extend (modelWithCornersSelf 𝕜 ES)).target := by
      simpa [eS, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint : ι (e (hx.domChart.symm u)) = g (hx.domChart.symm u) := by
      exact he (hx.domChart.symm u)
    simpa
      [eS, OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, hpoint] using
      hx.writtenInCharts hu'

/-- Helper for Remark 7.50-extra-5: the Euclidean rank-`r` normal form
`rank_normal_form r n r` is an immersion. -/
theorem rankNormalFormSelf_isImmersion
    {n r : ℕ} (hr : r ≤ n) :
    IsImmersion (𝓡 r) (𝓡 n) ∞
      (LocalNormalFormAPI.rank_normal_form r n r) := by
  change IsImmersion (𝓡 r) (𝓡 n) ∞ (_root_.rank_normal_form r n r)
  let L : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := _root_.rank_normal_form r n r
      map_add' := by
        intro x y
        ext i
        by_cases hi : i.1 < r
        · simp [_root_.rank_normal_form, hi]
        · simp [_root_.rank_normal_form, hi]
      map_smul' := by
        intro c x
        ext i
        by_cases hi : i.1 < r
        · simp [_root_.rank_normal_form, hi]
        · simp [_root_.rank_normal_form, hi]
      cont := by
        -- The normal form is coordinatewise continuous on Euclidean space.
        have hcoord :
            Continuous fun x : EuclideanSpace ℝ (Fin r) ↦
              fun i : Fin n ↦
                if hri : i.1 < r then x ⟨i.1, hri⟩ else 0 := by
          refine continuous_pi ?_
          intro i
          by_cases hi : i.1 < r
          · simpa [hi] using
              (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℝ) ⟨i.1, hi⟩)
          · simpa [hi] using
              (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin r) ↦ (0 : ℝ))
        have hEq :
            (_root_.rank_normal_form r n r) =
              (WithLp.toLp 2 ∘
                fun x : EuclideanSpace ℝ (Fin r) ↦
                  fun i : Fin n ↦
                    if hri : i.1 < r then x ⟨i.1, hri⟩ else 0) := by
          funext x
          ext i
          by_cases hi : i.1 < r
          · simp [_root_.rank_normal_form, hi]
          · simp [_root_.rank_normal_form, hi]
        rw [hEq]
        simpa [Function.comp] using
          (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp hcoord }
  have hCont :
      ContMDiff (𝓡 r) (𝓡 n) ∞
        (_root_.rank_normal_form r n r) := by
    -- Rewrite the normal form as a continuous linear map to obtain smoothness.
    simpa [L] using (L.contMDiff : ContMDiff (𝓡 r) (𝓡 n) ∞ L)
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hCont).2 ?_
  intro x
  rw [mfderiv_eq_fderiv]
  have hDeriv :
      fderiv ℝ (_root_.rank_normal_form r n r) x = L := by
    simpa [L] using (L.hasFDerivAt : HasFDerivAt L L x).fderiv
  rw [hDeriv]
  intro v w hvw
  -- Apply the left-inverse projection to compare source vectors coordinatewise.
  have hproj := congrArg (orbitHeadProjection hr) hvw
  have hproj' : orbitHeadProjection hr (L v) = orbitHeadProjection hr (L w) := hproj
  have hv : v = orbitHeadProjection hr (L v) := by
    -- The head projection is a left inverse for the zero-tail inclusion.
    symm
    simpa [L] using orbitHeadProjection_rankNormalForm hr v
  have hw : orbitHeadProjection hr (L w) = w := by
    -- Apply the same left-inverse identity on the second source vector.
    simpa [L] using orbitHeadProjection_rankNormalForm hr w
  -- Transport equality through the left inverse of `L`.
  exact hv.trans (hproj'.trans hw)

/-- Helper for Remark 7.50-extra-5: every representative-local quotient source
patch contains the quotient class of its chosen representative. -/
theorem orbitQuotientPatch_nonemptyAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    Nonempty (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) := by
  refine ⟨⟨(QuotientGroup.mk g₀ : G ⧸ MulAction.stabilizer G p), ?_⟩⟩
  exact ⟨g₀, hNF.domChart_centered.1, rfl⟩

/-- Helper for Remark 7.50-extra-5: the Euclidean target patch for a representative-local
quotient chart is nonempty because it contains the projected source center. -/
theorem orbitHeadProjection_targetPatch_nonemptyAtRepresentative
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    Nonempty (orbitHeadProjection hrm '' hNF.domChart.target) := by
  refine ⟨⟨orbitHeadProjection hrm (hNF.domChart g₀), ?_⟩⟩
  exact ⟨hNF.domChart g₀, hNF.domChart.map_source hNF.domChart_centered.1, rfl⟩

/-- Helper for Remark 7.50-extra-5: package a representative-local quotient patch as an actual
Euclidean chart on the ambient quotient. -/
noncomputable def quotientRepresentativeChart
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    OpenPartialHomeomorph (G ⧸ MulAction.stabilizer G p)
      (EuclideanSpace ℝ (Fin r)) :=
  let Uq : TopologicalSpace.Opens (G ⧸ MulAction.stabilizer G p) :=
    ⟨((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source,
      orbitQuotientPatchImage_openAtRepresentative p hNF⟩
  let W : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin r)) :=
    ⟨orbitHeadProjection hrm '' hNF.domChart.target,
      orbitHeadProjection_targetPatchImage_open hrm p hNF⟩
  let eU : OpenPartialHomeomorph Uq W :=
    (orbitQuotientPatchAtRepresentativeHomeomorph hrm hrn p hNF).toOpenPartialHomeomorph
  let eW : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin r)) :=
    W.openPartialHomeomorphSubtypeCoe
      (orbitHeadProjection_targetPatch_nonemptyAtRepresentative hrm p hNF)
  let eUW : OpenPartialHomeomorph Uq (EuclideanSpace ℝ (Fin r)) := eU.trans eW
  eUW.lift_openEmbedding Uq.2.isOpenEmbedding_subtypeVal

/-- Helper for Remark 7.50-extra-5: the representative-local quotient chart is defined exactly on
the quotient image of the chosen source patch. -/
theorem quotientRepresentativeChart_source
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M) {g₀ : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    (quotientRepresentativeChart hrm hrn p hNF).source =
      ((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source := by
  -- Normalize the lifted source explicitly so later atlas packaging can read chart membership from
  -- the chosen representative patch data.
  ext q
  simp [quotientRepresentativeChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.trans_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source]

/-- Helper for Remark 7.50-extra-5: fixing the constant-rank witness and a quotient point `q`,
the representative `q.out` determines one local quotient chart whose source already contains `q`. -/
theorem existsRepresentativeLocalQuotientChartAt
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    ∃ hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
        (orbit_map G p) q.out
        (LocalNormalFormAPI.rank_normal_form m n r),
      q ∈ (quotientRepresentativeChart hrm hrn p hNF).source := by
  rcases constant_rank_local_coordinate_normal_form
      (orbitMap_contMDiff p) hRank q.out with ⟨hNF, _⟩
  refine ⟨hNF, ?_⟩
  -- The chosen quotient point is literally the quotient class of its stored representative `q.out`.
  rw [quotientRepresentativeChart_source hrm hrn p hNF]
  exact ⟨q.out, hNF.domChart_centered.1, QuotientGroup.out_eq' q⟩

/-- Helper for Remark 7.50-extra-5: choose one representative-local quotient chart at each quotient
point using the fixed constant-rank witness. -/
noncomputable def representativeLocalQuotientChartAt
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    OpenPartialHomeomorph (G ⧸ MulAction.stabilizer G p) (EuclideanSpace ℝ (Fin r)) :=
  quotientRepresentativeChart hrm hrn p
    (Classical.choose (existsRepresentativeLocalQuotientChartAt p hRank hrm hrn q))

/-- Helper for Remark 7.50-extra-5: the chosen representative-local quotient chart at `q` is
indeed centered on `q` in the sense required by `ChartedSpace.mem_chart_source`. -/
theorem representativeLocalQuotientChartAt_mem_source
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    q ∈ (representativeLocalQuotientChartAt p hRank hrm hrn q).source := by
  -- Unfold the chosen chart once and read the stored source-membership witness from the choice
  -- theorem so later charted-space packaging avoids replaying the representative choice.
  simpa [representativeLocalQuotientChartAt] using
    (Classical.choose_spec (existsRepresentativeLocalQuotientChartAt p hRank hrm hrn q))

/-- Helper for Remark 7.50-extra-5: the chosen representative-local quotient chart belongs to the
atlas generated by the chart selector itself. -/
theorem representativeLocalQuotientChartAt_mem_atlas
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n)
    (q : G ⧸ MulAction.stabilizer G p) :
    representativeLocalQuotientChartAt p hRank hrm hrn q ∈
      Set.range (representativeLocalQuotientChartAt p hRank hrm hrn) := by
  -- The chart selector is its own atlas generator, so membership is immediate from the witness
  -- point `q`.
  exact ⟨q, rfl⟩

/-- Helper for Remark 7.50-extra-5: once the Euclidean constant-rank witness is fixed, the chosen
representative-local quotient charts already define the underlying `ChartedSpace` data on the
stabilizer quotient. -/
@[reducible] noncomputable def representativeLocalQuotientChartedSpace
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (p : M)
    (hRank : Manifold.HasConstantRank
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (orbit_map G p) r)
    (hrm : r ≤ m) (hrn : r ≤ n) :
    ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) where
  atlas := Set.range (representativeLocalQuotientChartAt p hRank hrm hrn)
  chartAt := representativeLocalQuotientChartAt p hRank hrm hrn
  mem_chart_source := representativeLocalQuotientChartAt_mem_source p hRank hrm hrn
  chart_mem_atlas := representativeLocalQuotientChartAt_mem_atlas p hRank hrm hrn

/-- Helper for Remark 7.50-extra-5: fix one identity-centered normal form and generate every
quotient chart by translating that single chart along quotient left multiplication. -/
noncomputable def translatedIdentityQuotientChartAt
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q : G ⧸ MulAction.stabilizer G p) :
    OpenPartialHomeomorph (G ⧸ MulAction.stabilizer G p) (EuclideanSpace ℝ (Fin r)) :=
  -- Route correction: use one fixed identity chart and transport it by quotient left
  -- translations, instead of comparing unrelated `Classical.choose` normal forms.
  (quotientLeftTranslationHomeomorph
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm.toOpenPartialHomeomorph.trans
    (quotientRepresentativeChart hrm hrn p hNF)

/-- Helper for Remark 7.50-extra-5: the translated identity chart at `q` is centered on `q`. -/
theorem translatedIdentityQuotientChartAt_mem_source
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q : G ⧸ MulAction.stabilizer G p) :
    q ∈ (translatedIdentityQuotientChartAt hrm hrn p hNF q).source := by
  have hBase :
      (QuotientGroup.mk (1 : G) : G ⧸ MulAction.stabilizer G p) ∈
        (quotientRepresentativeChart hrm hrn p hNF).source := by
    -- The fixed identity patch contains the identity coset because the normal form is centered at
    -- `1 : G`.
    rw [quotientRepresentativeChart_source hrm hrn p hNF]
    exact ⟨1, hNF.domChart_centered.1, rfl⟩
  have hTranslate :
      ((quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm q :
        G ⧸ MulAction.stabilizer G p) =
        QuotientGroup.mk (1 : G) := by
    -- Moving `q` back by its chosen representative lands at the identity coset.
    have hOut :
        (QuotientGroup.mk q.out : G ⧸ MulAction.stabilizer G p) = q :=
      QuotientGroup.out_eq' q
    have hSmul :
        q.out⁻¹ • q =
          q.out⁻¹ • (QuotientGroup.mk q.out : G ⧸ MulAction.stabilizer G p) := by
      simpa using congrArg
        (fun q' : G ⧸ MulAction.stabilizer G p ↦ q.out⁻¹ • q') hOut.symm
    calc
      ((quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm q :
          G ⧸ MulAction.stabilizer G p)
          = q.out⁻¹ • q := by
            rfl
      _ = q.out⁻¹ • (QuotientGroup.mk q.out : G ⧸ MulAction.stabilizer G p) := hSmul
      _ = QuotientGroup.mk (1 : G) := by
            change (QuotientGroup.mk (q.out⁻¹ * q.out) : G ⧸ MulAction.stabilizer G p) =
              QuotientGroup.mk (1 : G)
            simp
  have hPulled :
      ((quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm q :
        G ⧸ MulAction.stabilizer G p) ∈
        (quotientRepresentativeChart hrm hrn p hNF).source := by
    simpa [hTranslate] using hBase
  -- Unfold one transport layer: membership in the translated chart source is exactly membership of
  -- the pulled-back point in the fixed identity chart source.
  simpa [translatedIdentityQuotientChartAt, OpenPartialHomeomorph.trans_source] using hPulled

/-- Helper for Remark 7.50-extra-5: every translated identity chart lies in the atlas generated by
the translated chart selector itself. -/
theorem translatedIdentityQuotientChartAt_mem_atlas
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q : G ⧸ MulAction.stabilizer G p) :
    translatedIdentityQuotientChartAt hrm hrn p hNF q ∈
      Set.range (translatedIdentityQuotientChartAt hrm hrn p hNF) := by
  -- The translated-chart selector is its own atlas generator.
  exact ⟨q, rfl⟩

/-- Helper for Remark 7.50-extra-5: the translated identity chart family already determines the
underlying `ChartedSpace` data on the stabilizer quotient. -/
@[reducible] noncomputable def translatedIdentityQuotientChartedSpace
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) where
  atlas := Set.range (translatedIdentityQuotientChartAt hrm hrn p hNF)
  chartAt := translatedIdentityQuotientChartAt hrm hrn p hNF
  mem_chart_source := translatedIdentityQuotientChartAt_mem_source hrm hrn p hNF
  chart_mem_atlas := translatedIdentityQuotientChartAt_mem_atlas hrm hrn p hNF

/-- Helper for Remark 7.50-extra-5: composing one quotient left translation with the inverse of
another collapses to the single left translation by the relative group element. -/
theorem quotientLeftTranslationHomeomorph_trans_symm
    {m : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    (p : M) (g h : G) :
    (quotientLeftTranslationHomeomorph
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p g).trans
      (quotientLeftTranslationHomeomorph
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p h).symm =
      quotientLeftTranslationHomeomorph
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p (h⁻¹ * g) := by
  -- Compare both homeomorphisms pointwise: each side acts by the same left multiplication on the
  -- quotient.
  ext q <;> simp [quotientLeftTranslationHomeomorph, smul_smul, mul_assoc]

/-- Helper for Remark 7.50-extra-5: every translated-chart overlap is the fixed identity chart
conjugating the single quotient left translation by `q'.out⁻¹ * q.out`. -/
theorem translatedIdentityChartTransition_eq_fixedLeftTranslation
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q q' : G ⧸ MulAction.stabilizer G p) :
    ((translatedIdentityQuotientChartAt hrm hrn p hNF q).symm.trans
      (translatedIdentityQuotientChartAt hrm hrn p hNF q')) =
      (quotientRepresentativeChart hrm hrn p hNF).symm.trans
        ((quotientLeftTranslationHomeomorph
            (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p (q'.out⁻¹ * q.out)).toOpenPartialHomeomorph.trans
          (quotientRepresentativeChart hrm hrn p hNF)) := by
  -- Route correction: expand both translated charts back to the fixed identity chart before
  -- comparing overlaps, so the representative-choice seam disappears.
  rw [translatedIdentityQuotientChartAt, translatedIdentityQuotientChartAt]
  -- The transition is the fixed chart on both ends with only the middle source translation left.
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  -- Collapse the two translated source symmetries to one left translation before reattaching the
  -- fixed chart on both sides.
  have hmiddle :
      (quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm.toOpenPartialHomeomorph.symm.trans
        (quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q'.out).symm.toOpenPartialHomeomorph =
        (quotientLeftTranslationHomeomorph
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p (q'.out⁻¹ * q.out)).toOpenPartialHomeomorph := by
    -- The inverse of the inverse translated chart is the original left translation.
    rw [show
        (quotientLeftTranslationHomeomorph
            (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).symm.toOpenPartialHomeomorph.symm =
          (quotientLeftTranslationHomeomorph
            (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) p q.out).toOpenPartialHomeomorph by
          rfl]
    rw [← Homeomorph.trans_toOpenPartialHomeomorph]
    rw [quotientLeftTranslationHomeomorph_trans_symm]
  -- After the middle normalization, both sides are the same fixed-chart conjugation.
  simpa [OpenPartialHomeomorph.trans_assoc] using
    congrArg
      (fun e ↦
        (quotientRepresentativeChart hrm hrn p hNF).symm.trans
          (e.trans (quotientRepresentativeChart hrm hrn p hNF)))
      hmiddle

/-- Helper for Remark 7.50-extra-5: on the canonical target-patch representative, the fixed
left-translation conjugation of the quotient patch is written by the explicit head-projection
formula coming from the translated representative. -/
theorem fixedLeftTranslation_patch_formula
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    {g₀ g : G}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) g₀
      (LocalNormalFormAPI.rank_normal_form m n r))
    (x : hNF.domChart.target)
    (hxg : g * hNF.domChart.symm x ∈ hNF.domChart.source) :
    ∃ qU :
        (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source),
      Subtype.val qU =
          g •
            Subtype.val
              (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF
                (⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩ :
                  orbitHeadProjection hrm '' hNF.domChart.target)) ∧
        orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU =
          (⟨orbitHeadProjection hrm (hNF.domChart (g * hNF.domChart.symm x)),
            ⟨hNF.domChart (g * hNF.domChart.symm x),
              hNF.domChart.map_source hxg, rfl⟩⟩ :
            orbitHeadProjection hrm '' hNF.domChart.target) := by
  let xW : orbitHeadProjection hrm '' hNF.domChart.target :=
    ⟨orbitHeadProjection hrm x.1, ⟨x.1, x.2, rfl⟩⟩
  let gxU : hNF.domChart.source := ⟨g * hNF.domChart.symm x, hxg⟩
  let qU :
      (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) :=
    ⟨(QuotientGroup.mk (g * hNF.domChart.symm x) :
        G ⧸ MulAction.stabilizer G p),
      ⟨g * hNF.domChart.symm x, hxg, rfl⟩⟩
  let yW : orbitHeadProjection hrm '' hNF.domChart.target :=
    ⟨orbitHeadProjection hrm (hNF.domChart gxU),
      ⟨hNF.domChart gxU, hNF.domChart.map_source hxg, rfl⟩⟩
  have hForward :=
    congrArg
      (fun f : hNF.domChart.source →
          orbitHeadProjection hrm '' hNF.domChart.target =>
        f gxU)
      (orbitQuotientPatchForwardAtRepresentative_comp_projection
        hrm hrn p hNF)
  have hForwardEval :
      orbitQuotientPatchForwardAtRepresentative hrm hrn p hNF qU = yW := by
    simpa [gxU, qU, yW] using hForward
  have hInverse :=
    congrArg
      (fun f : hNF.domChart.target →
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source) ↦
        f x)
      (orbitQuotientPatchInverseAtRepresentative_comp_projection
        hrm hrn p hNF)
  have hInverseEval :
      orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW =
        (⟨(QuotientGroup.mk (hNF.domChart.symm x) :
            G ⧸ MulAction.stabilizer G p),
          ⟨hNF.domChart.symm x, hNF.domChart.map_target x.2, rfl⟩⟩ :
          (((↑) : G → G ⧸ MulAction.stabilizer G p) '' hNF.domChart.source)) := by
    simpa [xW] using hInverse
  have hqVal :
      Subtype.val qU =
        g •
          Subtype.val
            (orbitQuotientPatchInverseAtRepresentative hrm hrn p hNF xW) := by
    -- The inverse patch chooses the representative `hNF.domChart.symm x`, and left translation
    -- by `g` carries its quotient class to the class of `g * hNF.domChart.symm x`.
    rw [hInverseEval]
    change
      (QuotientGroup.mk (g * hNF.domChart.symm x) :
        G ⧸ MulAction.stabilizer G p) =
        g • (QuotientGroup.mk (hNF.domChart.symm x) :
          G ⧸ MulAction.stabilizer G p)
    rfl
  refine ⟨qU, hqVal, ?_⟩
  simpa [yW] using hForwardEval

/-- Helper for Remark 7.50-extra-5: on the actual representative-patch overlap, the explicit
translated head-projection formula is `C^∞`. -/
theorem fixedLeftTranslation_headProjectionPatch_contDiffOn
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (g : G) :
    ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin r)))
      ∞
      (fun y : EuclideanSpace ℝ (Fin m) ↦
        orbitHeadProjection hrm (hNF.domChart (g * hNF.domChart.symm y)))
      {y | y ∈ hNF.domChart.target ∧ g * hNF.domChart.symm y ∈ hNF.domChart.source} := by
  have hChartInv :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        hNF.domChart.symm hNF.domChart.target := by
    -- The inverse branch of the normal-form chart is smooth on its target because the chart lies
    -- in the maximal atlas.
    simpa using contMDiffOn_symm_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
  have hLeftMul :
      ContMDiff
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        (fun x : G ↦ g * x) := by
    -- Fixed left multiplication is the ambient action of `G` on itself, hence smooth.
    simpa using
      (MulActionHom.contMDiff_const_smul
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (IX := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (X := G) g)
  have hTranslated :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦ g * hNF.domChart.symm y)
        hNF.domChart.target := by
    -- Compose the smooth chart inverse with fixed left multiplication.
    simpa [Function.comp] using hLeftMul.comp_contMDiffOn hChartInv
  have hChart :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        hNF.domChart hNF.domChart.source := by
    -- The forward branch of the normal-form chart is smooth on its source for the same atlas
    -- reason.
    simpa using contMDiffOn_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
  have hWritten :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        ∞
        (fun y : EuclideanSpace ℝ (Fin m) ↦ hNF.domChart (g * hNF.domChart.symm y))
        {y | y ∈ hNF.domChart.target ∧ g * hNF.domChart.symm y ∈ hNF.domChart.source} := by
    -- Restrict the translated chart inverse to the actual overlap where the forward chart is
    -- defined.
    refine hChart.comp (hTranslated.mono ?_) ?_
    · intro y hy
      exact hy.1
    intro y hy
    exact hy.2
  -- Finish by composing with the smooth linear head projection.
  simpa [Function.comp] using
    (orbitHeadProjection_isSmoothSubmersion hrm).contMDiff.comp_contMDiffOn hWritten

/-- Helper for Remark 7.50-extra-5: every overlap of the translated identity quotient charts is
`C^∞` on its source. -/
theorem translatedIdentityChartTransition_contDiffOn
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r))
    (q q' : G ⧸ MulAction.stabilizer G p) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (((translatedIdentityQuotientChartAt hrm hrn p hNF q).symm.trans
        (translatedIdentityQuotientChartAt hrm hrn p hNF q')) :
          OpenPartialHomeomorph
            (EuclideanSpace ℝ (Fin r))
            (EuclideanSpace ℝ (Fin r)))
      (((translatedIdentityQuotientChartAt hrm hrn p hNF q).symm.trans
        (translatedIdentityQuotientChartAt hrm hrn p hNF q')).source) := by
  -- Route correction: the overlap itself has already been normalized to one fixed-chart
  -- conjugation of a quotient left translation, so the remaining task is exactly that smoothness
  -- bridge and nothing else from the quotient atlas package.
  -- TODO: combine `fixedLeftTranslation_patch_formula` with `ContDiffOn.comp` for the explicit map
  -- `y ↦ orbitHeadProjection hrm (hNF.domChart ((q'.out⁻¹ * q.out) * hNF.domChart.symm y))` on the
  -- actual overlap source, then rewrite back through
  -- `translatedIdentityChartTransition_eq_fixedLeftTranslation`.
  sorry

/-- Helper for Remark 7.50-extra-5: the translated identity quotient atlas defines a smooth
boundaryless manifold structure on `G ⧸ MulAction.stabilizer G p`. -/
theorem translatedIdentityQuotientChartedSpace_isManifold
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) :=
      translatedIdentityQuotientChartedSpace hrm hrn p hNF
    IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin r))) (⊤ : WithTop ℕ∞)
      (G ⧸ MulAction.stabilizer G p) := by
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) :=
    translatedIdentityQuotientChartedSpace hrm hrn p hNF
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) := cs
  -- The translated charts generate the whole atlas, so smooth compatibility reduces to the
  -- single transition lemma proved above for arbitrary `q` and `q'`.
  refine isManifold_of_contDiffOn (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin r)))
    (n := (⊤ : WithTop ℕ∞)) (M := G ⧸ MulAction.stabilizer G p) ?_
  intro e e' he he'
  rcases he with ⟨q, rfl⟩
  rcases he' with ⟨q', rfl⟩
  simpa using translatedIdentityChartTransition_contDiffOn hrm hrn p hNF q q'

/-- Helper for Remark 7.50-extra-5: once the translated identity quotient atlas is installed, the
descended orbit map `MulAction.ofQuotientStabilizer G p` is a global immersion into the Euclidean
target owner coming from the fixed normal-form chart. -/
theorem translatedIdentityQuotientMap_isImmersion
    {m n r : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
    [ContMDiffSMul (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]
    (hrm : r ≤ m) (hrn : r ≤ n) (p : M)
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (orbit_map G p) (1 : G)
      (LocalNormalFormAPI.rank_normal_form m n r)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin r)) (G ⧸ MulAction.stabilizer G p) :=
      translatedIdentityQuotientChartedSpace hrm hrn p hNF
    let _ : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin r))) (⊤ : WithTop ℕ∞)
        (G ⧸ MulAction.stabilizer G p) :=
      translatedIdentityQuotientChartedSpace_isManifold hrm hrn p hNF
    IsImmersion
      (𝓘(ℝ, EuclideanSpace ℝ (Fin r)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p) := by
  -- Route correction: the global immersion should now be assembled from the identity-patch normal
  -- form and equivariant transport along quotient left translations, with no return to the older
  -- stabilizer-owner bridge.
  -- TODO: first prove immersion on the fixed identity patch using
  -- `ofQuotientStabilizer_writtenInRepresentativePatch`, `rankNormalFormSelf_isImmersion`, and
  -- `euclideanChartInverse_isImmersion`, then transport that local result to every translated
  -- chart via `ofQuotientStabilizer_map_smul` and fixed-smul smoothness on `M`.
  sorry

/-- Helper for Remark 7.50-extra-5: once the descended quotient map is an immersion into an
auxiliary target owner on the same carrier `M`, composing with the identity immersion back to the
original target model `J` upgrades it to the required original-model immersion. -/
theorem ofQuotientStabilizer_isImmersion_originalModel
    {EM'' : Type uE'} [NormedAddCommGroup EM''] [NormedSpace 𝕜 EM'']
    [ChartedSpace EM'' M]
    [IsManifold (modelWithCornersSelf 𝕜 EM'') (⊤ : WithTop ℕ∞) M]
    (p : M)
    (hIdImm : IsImmersion (modelWithCornersSelf 𝕜 EM'') J (⊤ : WithTop ℕ∞)
      (fun x : M ↦ x))
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    [ChartedSpace EQ (G ⧸ MulAction.stabilizer G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞)
      (G ⧸ MulAction.stabilizer G p)]
    (hQuotImm : IsImmersion (modelWithCornersSelf 𝕜 EQ)
      (modelWithCornersSelf 𝕜 EM'') (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p)) :
    IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p) := by
  -- Compose the auxiliary-target immersion with the identity immersion back to the original model.
  simpa [Function.comp] using
    Manifold.IsImmersion.ex416_comp hIdImm hQuotImm

/-- Helper for Remark 7.50-extra-5: an auxiliary target owner on `M` is enough for the quotient
bridge once the identity map back to `J` is known to be an immersion. -/
theorem stabilizerQuotientManifoldBridge_of_auxiliaryTargetModel
    {EM'' : Type uE'} [NormedAddCommGroup EM''] [NormedSpace 𝕜 EM'']
    [ChartedSpace EM'' M]
    [IsManifold (modelWithCornersSelf 𝕜 EM'') (⊤ : WithTop ℕ∞) M]
    (p : M)
    (hIdImm : IsImmersion (modelWithCornersSelf 𝕜 EM'') J (⊤ : WithTop ℕ∞)
      (fun x : M ↦ x))
    {EQ : Type uQ} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
    [ChartedSpace EQ (G ⧸ MulAction.stabilizer G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞)
      (G ⧸ MulAction.stabilizer G p)]
    (hQuotImm : IsImmersion (modelWithCornersSelf 𝕜 EQ)
      (modelWithCornersSelf 𝕜 EM'') (⊤ : WithTop ℕ∞)
      (MulAction.ofQuotientStabilizer G p)) :
    ∃ (EQ : Type uQ), ∃ _ : NormedAddCommGroup EQ, ∃ _ : NormedSpace 𝕜 EQ,
      ∃ _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p),
        ∃ _ : IsManifold (modelWithCornersSelf 𝕜 EQ) (⊤ : WithTop ℕ∞)
            (G ⧸ MulAction.stabilizer G p),
          IsImmersion (modelWithCornersSelf 𝕜 EQ) J (⊤ : WithTop ℕ∞)
            (MulAction.ofQuotientStabilizer G p) := by
  -- Package the quotient charted-space owner together with the transported original-model
  -- immersion.
  refine ⟨EQ, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ofQuotientStabilizer_isImmersion_originalModel p hIdImm hQuotImm

omit [LieGroup I ∞ G] [IsManifold J ∞ M] [ContMDiffSMul I J ∞ G M] in
/-- Helper: the orbit map corestricts to a canonical map onto the literal
orbit subtype. -/
def orbitMapToOrbit (p : M) : G → MulAction.orbit G p :=
  fun g ↦ ⟨orbit_map G p g, ⟨g, rfl⟩⟩

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: forgetting the orbit subtype on `orbitMapToOrbit` recovers the
original orbit map. -/
theorem orbitMapToOrbit_coe_apply (p : M) (g : G) :
    ((orbitMapToOrbit p g : MulAction.orbit G p) : M) = orbit_map G p g := rfl

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: every orbit point is represented by some group element under
the corestricted orbit map. -/
theorem orbitMapToOrbit_surjective (p : M) :
    Function.Surjective (fun g : G ↦ orbitMapToOrbit p g) := by
  intro q
  rcases q.2 with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  -- Compare the subtype-valued orbit map at the representative furnished by orbit membership.
  apply Subtype.ext
  simpa [orbitMapToOrbit, orbit_map] using hg

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper: the subtype inclusion of the literal orbit subtype has image
exactly the orbit subset in `M`. -/
theorem range_subtypeVal_orbit (p : M) :
    Set.range (Subtype.val : MulAction.orbit G p → M) = MulAction.orbit G p := by
  -- Compare the subtype-inclusion range pointwise so the carrier normalization is purely
  -- set-theoretic and independent of any manifold structure placed on the orbit subtype.
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

omit [IsManifold J ∞ M] in
/-- Helper: a local-slice condition on the literal orbit subtype would
already force an embedded-submanifold structure in the ambient subspace topology. -/
theorem orbitLocalSliceCondition_givesEmbeddedSubtype
    {n r : ℕ}
    [TopologicalManifold n M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    (p : M)
    (hSlice : Set.SatisfiesLocalSliceCondition n (MulAction.orbit G p) r) :
    ∃ tm : TopologicalManifold r (MulAction.orbit G p),
      let _ : TopologicalManifold r (MulAction.orbit G p) := tm
      ∃ hs : IsManifold (𝓡 r) (⊤ : WithTop ℕ∞) (MulAction.orbit G p),
        let _ : IsManifold (𝓡 r) (⊤ : WithTop ℕ∞) (MulAction.orbit G p) := hs
        IsEmbeddedSubmanifold (𝓡 n) (𝓡 r) (MulAction.orbit G p) := by
  -- Theorem 5.8 identifies a local-slice atlas on the literal orbit subtype with an embedded
  -- submanifold structure for the same subtype topology.
  exact
    local_slice_condition_has_embedded_submanifold_structure
      (MulAction.orbit G p) hSlice

omit [TopologicalSpace G] [IsManifold J ∞ M] in
/-- Helper: once the literal orbit subtype carries a weakly embedded
boundaryless manifold structure, the Chapter 5 embedded-to-immersed bridge packages it as an
immersed submanifold with carrier exactly that orbit. -/
theorem orbitSubtype_toImmersedSubmanifold
    {EO : Type uQ} [NormedAddCommGroup EO] [NormedSpace 𝕜 EO]
    (p : M)
    [IsManifold J ω M]
    [ChartedSpace EO (MulAction.orbit G p)]
    [IsManifold (modelWithCornersSelf 𝕜 EO) (⊤ : WithTop ℕ∞) (MulAction.orbit G p)]
    [IsWeaklyEmbeddedSubmanifold J (modelWithCornersSelf 𝕜 EO) (MulAction.orbit G p)] :
    ∃ S : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uM} J M,
      S.carrier = MulAction.orbit G p := by
  letI : IsEmbeddedSubmanifold J (modelWithCornersSelf 𝕜 EO) (MulAction.orbit G p) :=
    inferInstance
  let hOrbitEmb : IsEmbeddedSubmanifold J (modelWithCornersSelf 𝕜 EO) (MulAction.orbit G p) :=
    inferInstance
  let T : ImmersedSubmanifold.{u𝕜, uE', uH', uQ, uM, uM} J M :=
    hOrbitEmb.toImmersedSubmanifold
  -- The weakly embedded orbit subtype is already embedded, so the standard Chapter 5 bridge turns
  -- its subtype inclusion into an immersed submanifold of the ambient manifold.
  refine ⟨T, ?_⟩
  -- The resulting carrier is the image of `Subtype.val`, which is exactly the orbit subset.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Helper for Remark 7.50-extra-5: in the real theorem context, once the constant-rank witness
for the orbit map is fixed, the only missing work is the representative-local quotient atlas and
its written-in-charts immersion formula for `MulAction.ofQuotientStabilizer G p`. -/
theorem stabilizerQuotientManifoldBridge
    {EG : Type uE} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace EG G]
    {EM : Type uE'} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type uH'} [TopologicalSpace HM]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
    {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M]
    [MulAction G M]
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ G]
    [ContMDiffSMul (modelWithCornersSelf ℝ EG) J ∞ G M]
    (p : M) :
    ∃ (EQ : Type uQ), ∃ _ : NormedAddCommGroup EQ, ∃ _ : NormedSpace ℝ EQ,
      ∃ _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p),
        ∃ _ : IsManifold (modelWithCornersSelf ℝ EQ) (⊤ : WithTop ℕ∞)
            (G ⧸ MulAction.stabilizer G p),
          IsImmersion (modelWithCornersSelf ℝ EQ) J (⊤ : WithTop ℕ∞)
            (MulAction.ofQuotientStabilizer G p) := by
  let I : ModelWithCorners ℝ EG EG := modelWithCornersSelf ℝ EG
  let _ : LieGroup I ∞ G := by
    simpa [I] using (inferInstance : LieGroup (modelWithCornersSelf ℝ EG) ∞ G)
  let _ : ContMDiffSMul I J ∞ G M := by
    simpa [I] using
      (inferInstance : ContMDiffSMul (modelWithCornersSelf ℝ EG) J ∞ G M)
  rcases orbitMapConstantRankBounds (I := I) (J := J) (G := G) (M := M) p with
    ⟨r, hRank, hr_source, hr_target⟩
  -- Route correction: the atlas pivot now uses one fixed identity normal form and the translated
  -- chart family `translatedIdentityQuotientChartAt`, so the representative-choice seam is gone.
  -- The Euclidean translated-atlas helpers above now isolate the local quotient-manifold owner and
  -- the Euclidean-target immersion route. The remaining blocker is owner transport:
  -- this theorem still works over arbitrary finite-dimensional model spaces `EG` and `EM`, so it
  -- needs a bridge from those ambient models to the Euclidean source/target owners consumed by the
  -- translated-atlas package.
  -- TODO: choose Euclidean models for `G` and `M`, transport the constant-rank witness to those
  -- owners, apply `translatedIdentityQuotientChartedSpace_isManifold` and
  -- `translatedIdentityQuotientMap_isImmersion`, then compose with the identity immersion back to
  -- the original target model via `stabilizerQuotientManifoldBridge_of_auxiliaryTargetModel`.
  have _ : r ≤ Module.finrank ℝ EG := hr_source
  have _ : r ≤ Module.finrank ℝ EM := hr_target
  sorry

-- Domain sampling summary: the Chapter 5 owner for this remark is `ImmersedSubmanifold`, while
-- §7.50 contributes the orbit-map vocabulary `orbit_map` and the canonical orbit subset
-- `MulAction.orbit G p`. This item stays source-facing: it asserts existence of an immersed
-- submanifold structure on that orbit subset, without introducing any new wrapper API.
-- Semantic recall: the canonical mathlib orbit/quotient API used here is
-- `MulAction.ofQuotientStabilizer` together with `MulAction.orbitEquivQuotientStabilizer`.
/-- Remark 7.50-extra-5: in the book's real-manifold setting, every orbit of a smooth Lie-group
action is an immersed submanifold of `M`, even when the isotropy group is nontrivial. -/
theorem orbit_is_immersed_submanifold
    {EG : Type uE} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace EG G]
    {EM : Type uE'} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type uH'} [TopologicalSpace HM]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
    {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M]
    [MulAction G M]
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ G]
    [ContMDiffSMul (modelWithCornersSelf ℝ EG) J ∞ G M]
    (p : M) :
    ∃ S : ImmersedSubmanifold.{0, uE', uH', uQ, uM, uG} J M,
      S.carrier = MulAction.orbit G p := by
  -- Reduce the final statement to the real quotient-manifold bridge isolated just above.
  have hBridge :
      ∃ (EQ : Type uQ), ∃ _ : NormedAddCommGroup EQ, ∃ _ : NormedSpace ℝ EQ,
        ∃ _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p),
          ∃ _ : IsManifold (modelWithCornersSelf ℝ EQ) (⊤ : WithTop ℕ∞)
              (G ⧸ MulAction.stabilizer G p),
            IsImmersion (modelWithCornersSelf ℝ EQ) J (⊤ : WithTop ℕ∞)
              (MulAction.ofQuotientStabilizer G p) :=
    stabilizerQuotientManifoldBridge
      (EG := EG) (G := G) (EM := EM) (HM := HM) (M := M) (J := J) p
  rcases
      hBridge with
    ⟨EQ, instNormedAddCommGroupEQ, instNormedSpaceEQ,
      instChartedSpaceQuotient, instIsManifoldQuotient, hImm⟩
  let _ : NormedAddCommGroup EQ := instNormedAddCommGroupEQ
  let _ : NormedSpace ℝ EQ := instNormedSpaceEQ
  let _ : ChartedSpace EQ (G ⧸ MulAction.stabilizer G p) := instChartedSpaceQuotient
  let _ : IsManifold (modelWithCornersSelf ℝ EQ) (⊤ : WithTop ℕ∞)
      (G ⧸ MulAction.stabilizer G p) := instIsManifoldQuotient
  -- Package the descended quotient map as the required immersed submanifold.
  rcases
      orbitImmersedSubmanifold_fromQuotient p hImm with
    ⟨S, hS⟩
  exact ⟨S, hS⟩

end OrbitSubmanifold
