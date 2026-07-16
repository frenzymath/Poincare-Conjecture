/-
Chapter 2, "Riemannian Metrics", §"Riemannian Coverings", **Proposition 2.31**.

Lee: *let `π : M̃ → M` be a smooth normal covering map, and `g̃` any metric on `M̃`
that is invariant under all covering automorphisms.  Then there is a unique metric
`g` on `M` such that `π` is a Riemannian covering.*

## The route

Lee's proof is a short reduction to Theorem 2.28
(`existsUnique_isRiemannianSubmersion_metric`), and that is exactly how it is
formalized here.  The group acting on `M̃` is the covering automorphism group
`Aut_π(M̃)` (`CoveringAut`), and 2.28's four hypotheses are supplied by:

* **submersion** — a smooth covering map is a local diffeomorphism (Lee A.49(a)),
  so every `dπ_x` is a linear equivalence, in particular surjective;
* **vertical** — `π ∘ φ = π` is the defining property of a covering automorphism;
* **fibre-transitive** — this is exactly what normality buys (Lee C.21);
* **isometric** — the invariance hypothesis on `g̃`.

Theorem 2.28 then yields a unique `g` making `π` a Riemannian *submersion*, and the
last step upgrades that to a *local isometry*: `dπ_x` is not merely surjective but
bijective, so `V_x = ker dπ_x = 0`, hence `H_x = T_x M̃` and every tangent vector is
horizontal, which collapses the definition of a Riemannian submersion onto that of a
metric-preserving map.  `isRiemannianSubmersion_iff_isMetricPreserving` is that step.
It is stated as an *iff* precisely so that 2.28's *uniqueness* transfers as well:
without the converse direction one would obtain existence of `g` but could not rule
out a second metric making `π` a local isometry without making it a submersion.

## Two modelling decisions, and why they are faithful

**Smooth covering maps.**  Lee defines a smooth covering map by evenly covered
neighbourhoods whose sheets map *diffeomorphically* onto the base.  Mathlib has
`IsCoveringMap` (the topological notion) but nothing smooth — `IsCoveringMap` does
not occur anywhere under `Mathlib/Geometry/`.  Rather than rebuild the sheet-wise
definition, `IsSmoothCoveringMap` is spelled as "topological covering map *and*
local diffeomorphism", which is Lee's own Proposition A.49(c): *a topological
covering map is a smooth covering map if and only if it is a local diffeomorphism*.
Surjectivity is a separate field because Lee builds it into the definition of a
covering map while mathlib deliberately does not: `IsCoveringMap`'s docstring allows
empty fibres, and `IsCoveringMap.of_isEmpty` makes the empty map a covering map.

**Normality.**  Lee defines a normal covering by a condition on `π_*` of fundamental
groups, and Proposition C.21 says this holds *iff* `Aut_π(M̃)` acts transitively on
each fibre.  Proposition 2.31 uses normality only through that conclusion, and the
fundamental group of a manifold is not available here (Appendix C is unformalized),
so `IsNormalCovering` is spelled as the fibre-transitivity characterization.  This
is the C.21-equivalent of Lee's definition, not a weakening of the theorem.
-/
import LeeLib.Ch02.SubmersionMetric
import LeeLib.Ch02.Isometry
import LeeLib.Ch02.LocalIsometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic

namespace LeeLib.Ch02

open scoped Manifold ContDiff Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## Smooth covering maps -/

/-- **A smooth covering map** (Lee, Appendix A): a surjective smooth map that is a
topological covering map and a local diffeomorphism.

By Lee's Proposition A.49(c) a topological covering map is a smooth covering map
exactly when it is a local diffeomorphism, so this is Lee's notion and not a
convenient approximation to it.  `surjective` is a field of its own because Lee's
covering maps are surjective by definition whereas mathlib's `IsCoveringMap` permits
empty fibres. -/
structure IsSmoothCoveringMap (π : C^∞⟮I, M; I', M'⟯) : Prop where
  /-- A covering map is surjective (part of Lee's definition). -/
  surjective : Function.Surjective π
  /-- The underlying map is a topological covering map. -/
  isCoveringMap : IsCoveringMap (π : M → M')
  /-- The sheets map diffeomorphically, in the form given by Lee's A.49(c). -/
  isLocalDiffeomorph : IsLocalDiffeomorph I I' ∞ (π : M → M')

namespace IsSmoothCoveringMap

variable {π : C^∞⟮I, M; I', M'⟯}

/-- Each `dπ_x` is a linear equivalence, `π` being a local diffeomorphism. -/
noncomputable def mfderivEquiv (hπ : IsSmoothCoveringMap π) (x : M) :
    TangentSpace I x ≃L[ℝ] TangentSpace I' (π x) :=
  hπ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- **Lee A.49(a), the half that Proposition 2.31 needs**: a smooth covering map is a
smooth submersion. -/
theorem isSubmersion (hπ : IsSmoothCoveringMap π) : IsSubmersion π := fun x => by
  rw [← hπ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe (by simp) x]
  exact (hπ.mfderivEquiv x).surjective

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- A smooth covering map is an immersion: the differentials are injective.  This is
what distinguishes it from a general submersion, and it is what makes the induced
Riemannian submersion a local isometry. -/
theorem injective_mfderiv (hπ : IsSmoothCoveringMap π) (x : M) :
    Function.Injective (mfderiv I I' π x) := by
  rw [← hπ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe (by simp) x]
  exact (hπ.mfderivEquiv x).injective

end IsSmoothCoveringMap

/-! ## Covering automorphisms

Lee's `Aut_π(M̃)`: the diffeomorphisms of the total space that commute with the
projection.  Mathlib has no deck transformation group — neither `Deck` nor an
automorphism group of a covering map occurs anywhere in it — so the group and its
action are built here. -/

/-- **A covering automorphism** of `π` (Lee: an element of `Aut_π(M̃)`): a
diffeomorphism `φ` of the total space with `π ∘ φ = π`. -/
structure CoveringAut (π : C^∞⟮I, M; I', M'⟯) where
  /-- The underlying diffeomorphism of the total space. -/
  toDiffeomorph : Diffeomorph I I M M ∞
  /-- It commutes with the projection: `π ∘ φ = π`. -/
  proj_comp : ∀ x : M, π (toDiffeomorph x) = π x

namespace CoveringAut

variable {π : C^∞⟮I, M; I', M'⟯}

noncomputable instance : FunLike (CoveringAut π) M M where
  coe φ := φ.toDiffeomorph
  coe_injective' φ ψ h := by
    cases φ; cases ψ
    simpa using DFunLike.coe_injective h

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
@[simp] theorem coe_toDiffeomorph (φ : CoveringAut π) : (φ.toDiffeomorph : M → M) = φ := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
@[ext] theorem ext {φ ψ : CoveringAut π} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext _ _ h

/-- `Aut_π(M̃)` is a group under composition.  Only the inverse needs an argument:
applying `π ∘ φ = π` at `φ⁻¹ x` gives `π x = π (φ⁻¹ x)`. -/
noncomputable instance : Group (CoveringAut π) where
  mul φ ψ := ⟨ψ.toDiffeomorph.trans φ.toDiffeomorph, fun x => by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, φ.proj_comp, ψ.proj_comp]⟩
  one := ⟨Diffeomorph.refl I M ∞, fun _ => rfl⟩
  inv φ := ⟨φ.toDiffeomorph.symm, fun x => by
    conv_rhs => rw [← φ.toDiffeomorph.apply_symm_apply x]
    exact (φ.proj_comp _).symm⟩
  mul_assoc _ _ _ := by ext x; rfl
  one_mul _ := by ext x; rfl
  mul_one _ := by ext x; rfl
  inv_mul_cancel φ := by
    ext x
    exact φ.toDiffeomorph.symm_apply_apply x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
@[simp] theorem mul_apply (φ ψ : CoveringAut π) (x : M) : (φ * ψ) x = φ (ψ x) := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
@[simp] theorem one_apply (x : M) : (1 : CoveringAut π) x = x := rfl

/-- `Aut_π(M̃)` acts on the total space by evaluation. -/
noncomputable instance : MulAction (CoveringAut π) M where
  smul φ x := φ x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
@[simp] theorem smul_def (φ : CoveringAut π) (x : M) : φ • x = φ x := rfl

end CoveringAut

/-! ## Normal coverings and Riemannian coverings -/

/-- **A normal covering** (Lee, via Proposition C.21): one whose automorphism group
acts transitively on each fibre.

Lee's definition asks that `π_*(π₁(M̃))` be a normal subgroup of `π₁(M)`, and C.21
identifies that with the condition below; 2.31 uses normality only through C.21, and
fundamental groups of manifolds are not available here. -/
def IsNormalCovering (π : C^∞⟮I, M; I', M'⟯) : Prop :=
  IsFibreTransitiveAction (G := CoveringAut π) π

/-- **`g` is invariant under all covering automorphisms** (Lee's hypothesis on `g̃` in
Proposition 2.31): every `φ ∈ Aut_π(M̃)` pulls `g` back to `g`. -/
def IsCoveringAutInvariant (g : RiemannianMetric I M) (π : C^∞⟮I, M; I', M'⟯) : Prop :=
  ∀ φ : CoveringAut π, IsMetricPreserving g g (φ : M → M)

/-- **A Riemannian covering** (Lee, §"Riemannian Coverings"): a smooth covering map
that is a local isometry.

Lee's "local isometry" is spelled here as `IsMetricPreserving`, i.e. `π^* g = g̃`.
The two agree for a covering map, which is in particular a local diffeomorphism, and
`IsRiemannianCovering.isLocalIsometry` below proves it — so this really is Lee's
definition and not a weakening of it. -/
def IsRiemannianCovering (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (π : C^∞⟮I, M; I', M'⟯) : Prop :=
  IsSmoothCoveringMap π ∧ IsMetricPreserving g g' (π : M → M')

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **A Riemannian covering is a local isometry**, which is how Lee states the
definition.

This discharges the reading of `IsRiemannianCovering` given above: a smooth covering
map is a local diffeomorphism by definition, so adjoining `π^* g' = g` to it is
exactly `IsLocalIsometry`.  No hypothesis on dimensions is needed here — unlike in
Lee's Exercise 2.7, the local diffeomorphism is given rather than deduced, so the
inverse function theorem does not enter. -/
theorem IsRiemannianCovering.isLocalIsometry
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {π : C^∞⟮I, M; I', M'⟯}
    (h : IsRiemannianCovering g g' π) : IsLocalIsometry g g' (π : M → M') :=
  ⟨h.1.isLocalDiffeomorph, h.2⟩

/-! ## An equidimensional Riemannian submersion is a local isometry -/

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {π : C^∞⟮I, M; I', M'⟯}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **A Riemannian submersion whose differentials are injective is exactly a local
isometry**, and conversely.  This is the last step of Lee's proof of Proposition 2.31
("a Riemannian submersion between manifolds of the same dimension is a local
isometry"), stated as an equivalence so that uniqueness transfers along it.

Forwards: injectivity of `dπ_x` makes every tangent vector horizontal
(`horizontalSpace_eq_top`), so the defining condition of a Riemannian submersion —
which only constrains horizontal vectors — becomes the definition of `π^* g' = g`.
Backwards: `π^* g' = g` constrains *all* vectors, so it implies the horizontal
condition without any hypothesis on `dπ_x` beyond surjectivity. -/
theorem isRiemannianSubmersion_iff_isMetricPreserving (hπ : IsSubmersion π)
    (hinj : ∀ x : M, Function.Injective (mfderiv I I' π x)) :
    IsRiemannianSubmersion g g' π ↔ IsMetricPreserving g g' (π : M → M') := by
  refine ⟨fun h p => ?_, fun h => ⟨hπ, fun x v w _ _ => ?_⟩⟩
  · ext v w
    rw [pullbackForm_apply]
    exact h.2 p v w (by rw [horizontalSpace_eq_top g π (hinj p)]; trivial)
      (by rw [horizontalSpace_eq_top g π (hinj p)]; trivial)
  · exact h.inner_mfderiv x v w

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The forward direction of `isRiemannianSubmersion_iff_isMetricPreserving`, in the
shape Lee states it. -/
theorem IsRiemannianSubmersion.isMetricPreserving
    (h : IsRiemannianSubmersion g g' π)
    (hinj : ∀ x : M, Function.Injective (mfderiv I I' π x)) :
    IsMetricPreserving g g' (π : M → M') :=
  (isRiemannianSubmersion_iff_isMetricPreserving h.1 hinj).mp h

end

/-! ## Proposition 2.31 -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {g : RiemannianMetric I M} {π : C^∞⟮I, M; I', M'⟯}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- The covering automorphism group acts vertically: this *is* `π ∘ φ = π`. -/
theorem isVerticalAction_coveringAut : IsVerticalAction (G := CoveringAut π) π :=
  fun φ x => φ.proj_comp x

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- An `Aut_π`-invariant metric makes the action of `Aut_π` an isometric action, in
the sense Theorem 2.28 requires. -/
theorem isIsometricAction_coveringAut (hinv : IsCoveringAutInvariant g π) :
    IsIsometricAction (G := CoveringAut π) g where
  contMDiff φ := φ.toDiffeomorph.contMDiff
  inner_smul φ x v w := (hinv φ).inner_mfderiv x v w

/-- **Lee, Proposition 2.31**: *if `π : M̃ → M` is a smooth normal covering map and
`g̃` is a metric on `M̃` invariant under all covering automorphisms, then there is a
unique metric `g` on `M` such that `π` is a Riemannian covering.*

The proof is Lee's.  `Aut_π(M̃)` acts on `M̃` isometrically (invariance), vertically
(`π ∘ φ = π`), and transitively on fibres (normality, via C.21); `π` is a surjective
submersion (A.49); so Theorem 2.28 gives a unique metric making `π` a Riemannian
submersion, and `isRiemannianSubmersion_iff_isMetricPreserving` identifies those
metrics with the ones making `π` a local isometry. -/
theorem existsUnique_isRiemannianCovering_metric (hπ : IsSmoothCoveringMap π)
    (hnormal : IsNormalCovering π) (hinv : IsCoveringAutInvariant g π) :
    ∃! g' : RiemannianMetric I' M', IsRiemannianCovering g g' π := by
  have hsub : IsSubmersion π := hπ.isSubmersion
  have hbridge : ∀ g' : RiemannianMetric I' M',
      IsRiemannianSubmersion g g' π ↔ IsRiemannianCovering g g' π := fun g' =>
    (isRiemannianSubmersion_iff_isMetricPreserving hsub hπ.injective_mfderiv).trans
      ⟨fun h => ⟨hπ, h⟩, fun h => h.2⟩
  obtain ⟨g', hg', huniq⟩ := existsUnique_isRiemannianSubmersion_metric (G := CoveringAut π)
    hsub (isIsometricAction_coveringAut hinv) isVerticalAction_coveringAut hnormal hπ.surjective
  exact ⟨g', (hbridge g').mp hg', fun g'' h => huniq g'' ((hbridge g'').mpr h)⟩

end

end LeeLib.Ch02
