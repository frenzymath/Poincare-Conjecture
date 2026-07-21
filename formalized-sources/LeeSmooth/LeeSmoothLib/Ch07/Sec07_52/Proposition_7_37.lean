import LeeSmoothLib.Ch07.Sec07_52.Definition_7_52_extra_2
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uH uE uG uV

-- Semantic recall note: `lean_leansearch` confirms the finite-dimensional completeness bridge via
-- `FiniteDimensional.complete` together with `RCLike.toCompleteSpace`, so Proposition 7.37 can
-- keep the source-facing assumptions while still using `LieGroupRepresentation I G V`.

section

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]

/-- The smooth general linear group of a complete normed space is the units manifold inside the
ambient ring of continuous endomorphisms. -/
noncomputable instance continuousLinearMapUnitsChartedSpace :
    ChartedSpace (V →L[𝕜] V) (V →L[𝕜] V)ˣ :=
  @Units.instChartedSpace (V →L[𝕜] V) inferInstance inferInstance

/-- A smooth representation of a Lie group `G` on the normed vector space `V`, viewed as a smooth
group homomorphism into the smooth general linear group `(V →L[𝕜] V)ˣ`. -/
abbrev LieGroupRepresentation
    (I : ModelWithCorners 𝕜 E H)
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] :
    Type _ :=
  ContMDiffMonoidMorphism I 𝓘(𝕜, V →L[𝕜] V) ∞ G (V →L[𝕜] V)ˣ

local notation "LieRep" => LieGroupRepresentation I G V

namespace LieGroupRepresentation

/-- The underlying algebraic representation of a smooth Lie-group representation. -/
noncomputable def toRepresentation (ρ : LieRep) : Representation 𝕜 G V where
  toFun g := (ρ g : V →L[𝕜] V).toLinearMap
  map_one' := by
    ext v
    simpa using congrArg
      (fun u : (V →L[𝕜] V)ˣ ↦ ((u : V →L[𝕜] V) v))
      ρ.map_one
  map_mul' g h := by
    ext v
    simpa using congrArg
      (fun u : (V →L[𝕜] V)ˣ ↦ ((u : V →L[𝕜] V) v))
      (ρ.map_mul g h)

@[simp] theorem toRepresentation_apply (ρ : LieRep) (g : G) (v : V) :
    ρ.toRepresentation g v = (ρ g : V →L[𝕜] V) v :=
  rfl

end LieGroupRepresentation

variable [MulAction G V] [ContMDiffSMul I 𝓘(𝕜, V) ∞ G V] [FiniteDimensional 𝕜 V]

/-- Helper for Proposition 7.37: a nontrivial complete finite-dimensional normed `𝕜`-space forces
`𝕜` itself to be complete. -/
lemma completeSpaceFieldOfCompleteFiniteDimensional
    (V' : Type uV) [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [CompleteSpace V']
    [FiniteDimensional 𝕜 V'] [Nontrivial V'] : CompleteSpace 𝕜 :=
  by
    -- `RCLike` fields are already complete, so no extra bridge through `V'` is needed here.
    infer_instance

/-- Helper for Proposition 7.37: smoothness into `Rˣ` is detected after forgetting the unit
structure. -/
theorem contMDiffUnitsOfVal
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {R : Type*} [NormedRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]
    {f : M → Rˣ}
    (h : ContMDiff I (𝓘(𝕜, R)) ∞ fun x ↦ ((f x : Rˣ) : R)) :
    ContMDiff I (𝓘(𝕜, R)) ∞ f := by
  -- The units manifold is an open submanifold of the ambient normed algebra.
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  simpa using h

/-- Helper for Proposition 7.37: smoothness of a `ContinuousLinearMap`-valued map is equivalent to
smoothness of all evaluation maps when the source vector space is finite-dimensional. -/
theorem contMDiffContinuousLinearMap_iff_forall_apply
    [CompleteSpace 𝕜]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [FiniteDimensional 𝕜 V₁]
    {W : Type*}
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] {f : M → V₁ →L[𝕜] W} :
    ContMDiff I 𝓘(𝕜, V₁ →L[𝕜] W) ∞ f ↔
      ∀ y : V₁, ContMDiff I 𝓘(𝕜, W) ∞ (fun x ↦ f x y) :=
  -- Route correction: the smoothness step is handled in finite coordinates for `V₁ →L[𝕜] W`,
  -- rather than by expanding the main theorem around the field-completeness detour.
  let d := Module.finrank 𝕜 V₁
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := by
    simpa [d] using (finrank_fin_fun 𝕜).symm
  let e₁ : V₁ ≃L[𝕜] Fin d → 𝕜 :=
    ContinuousLinearEquiv.ofFinrankEq hd
  let e : (V₁ →L[𝕜] W) ≃L[𝕜] Fin d → W :=
    (e₁.arrowCongr (1 : W ≃L[𝕜] W)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
  ⟨fun hf y ↦ by
      -- Evaluate the smooth operator-valued map at the fixed vector `y`.
      exact hf.clm_apply
        (contMDiff_const : ContMDiff I 𝓘(𝕜, V₁) ∞ (fun _ : M ↦ y)),
    fun h ↦ by
      have hpi : ContMDiff I 𝓘(𝕜, Fin d → W) ∞
          (fun x ↦ e (f x)) := by
        -- The coordinate normal form is smooth once each fixed evaluation map is smooth.
        refine contMDiff_pi_space.2 ?_
        intro i
        let y : V₁ := e₁.symm (Pi.single i 1)
        have hy := h y
        simpa [e, e₁, y] using hy
      -- Return from coordinates by composing with the inverse equivalence.
      let eSymm : (Fin d → W) →L[𝕜] (V₁ →L[𝕜] W) := e.symm.toContinuousLinearMap
      have hSymm : ContMDiff 𝓘(𝕜, Fin d → W) 𝓘(𝕜, V₁ →L[𝕜] W) ∞ eSymm :=
        eSymm.contMDiff
      refine (hSymm.comp hpi).congr ?_
      intro x
      simp [eSymm] ⟩

/-- Helper for Proposition 7.37: the algebraic representation attached to a linear action, viewed
inside the units of continuous endomorphisms. -/
noncomputable def linearActionContinuousUnits [CompleteSpace 𝕜] (h : IsLinearAction 𝕜 G V) :
    G →* (V →L[𝕜] V)ˣ :=
  ((Units.mapEquiv (Module.End.toContinuousLinearMap V).toMulEquiv).toMonoidHom).comp
    h.toRepresentation.asGroupHom

/-- Helper for Proposition 7.37: the transported continuous-endomorphism representation acts by the
original group action. -/
@[simp] theorem linearActionContinuousUnits_apply [CompleteSpace 𝕜]
    (h : IsLinearAction 𝕜 G V) (g : G) (v : V) :
    (linearActionContinuousUnits h g : V →L[𝕜] V) v = g • v := by
  -- This collapses the transport from algebraic units to continuous units.
  simp [linearActionContinuousUnits, Representation.asGroupHom_apply,
    Module.End.toContinuousLinearMap, LinearMap.coe_toContinuousLinearMap',
    IsLinearAction.toRepresentation_apply]

/-- Helper for Proposition 7.37: the operator-valued map extracted from a smooth linear action is
smooth. -/
theorem linearActionContinuousUnits_contMDiff [CompleteSpace 𝕜] (h : IsLinearAction 𝕜 G V) :
    ContMDiff I 𝓘(𝕜, V →L[𝕜] V) ∞
      (fun g ↦ (linearActionContinuousUnits h g : V →L[𝕜] V)) := by
  rw [contMDiffContinuousLinearMap_iff_forall_apply]
  intro v
  -- For each fixed vector, the evaluation map is the smooth orbit map.
  simpa using
    (contMDiff_id.smul (contMDiff_const : ContMDiff I 𝓘(𝕜, V) ∞ fun _ : G ↦ v))

/-- Helper for Proposition 7.37: a smooth linear action packages into a smooth representation. -/
noncomputable def lieGroupRepresentationOfIsLinearAction (h : IsLinearAction 𝕜 G V) :
    LieGroupRepresentation I G V where
  toMonoidHom := linearActionContinuousUnits h
  -- Smoothness into the units group follows from the ambient operator-valued smoothness.
  contMDiff_toFun := contMDiffUnitsOfVal (linearActionContinuousUnits_contMDiff h)

/-- Helper for Proposition 7.37: if a smooth action is given pointwise by a Lie-group
representation, then each action map is linear. -/
theorem isLinearActionOfLieGroupRepresentation
    (ρ : LieGroupRepresentation I G V)
    (hρ : ∀ g : G, ∀ v : V, g • v = (ρ g : V →L[𝕜] V) v) :
    IsLinearAction 𝕜 G V where
  map_add g x y := by
    -- Rewrite the action through the representing operator and use additivity of that operator.
    rw [hρ g (x + y), hρ g x, hρ g y]
    simpa using (ρ g : V →L[𝕜] V).map_add x y
  map_smul g a x := by
    -- Rewrite the action through the representing operator and use `𝕜`-linearity.
    rw [hρ g (a • x), hρ g x]
    simpa using (ρ g : V →L[𝕜] V).map_smul a x

end

section

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [MulAction G V] [ContMDiffSMul I 𝓘(𝕜, V) ∞ G V] [FiniteDimensional 𝕜 V]

/-- Helper for Proposition 7.37: finite-dimensional normed spaces over an `RCLike` field are
complete. This supplies the smooth general linear group used in the theorem statement. -/
local instance completeSpaceFiniteDimensional : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

/-- Proposition 7.37. For a smooth left action of a Lie group `G` on a finite-dimensional vector
space `V`, the action is linear, in the sense that each action map `v ↦ g • v` is given by a
linear endomorphism of `V`, if and only if it is induced by some smooth representation
`ρ : G → (V →L[𝕜] V)ˣ`, in the sense that `g • v = ρ g • v` for all `g : G` and `v : V`. -/
theorem isLinearAction_iff_exists_lieGroupRepresentation :
    IsLinearAction 𝕜 G V ↔
      ∃ ρ : LieGroupRepresentation I G V, ∀ g : G, ∀ v : V,
        g • v = (ρ g : V →L[𝕜] V) v :=
  by
    constructor
    · intro h
      -- The linear action packages directly into a smooth units-valued representation.
      refine ⟨lieGroupRepresentationOfIsLinearAction h, ?_⟩
      intro g v
      -- The bundled representation acts by the original action.
      calc
        g • v = (linearActionContinuousUnits h g : V →L[𝕜] V) v :=
          (linearActionContinuousUnits_apply h g v).symm
        _ = (lieGroupRepresentationOfIsLinearAction h g : V →L[𝕜] V) v := rfl
    · rintro ⟨ρ, hρ⟩
      -- The representing operators are linear, so the action maps are linear as well.
      exact isLinearActionOfLieGroupRepresentation ρ hρ

end
