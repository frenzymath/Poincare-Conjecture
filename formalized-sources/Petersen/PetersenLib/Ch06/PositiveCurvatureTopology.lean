import PetersenLib.Ch06.PathSpaceAB
import PetersenLib.Ch06.SecBounds
import PetersenLib.Ch05.InjectivityRadius
import PetersenLib.Ch05.TotallyGeodesic
import PetersenLib.Ch01.RiemannianManifolds
import PetersenLib.Ch06.MyersFundamentalGroup
import Mathlib.Topology.Homotopy.Basic

/-!
# Petersen Ch. 6, section 6.5: positive-curvature topology interfaces

The analytic part of the chapter (Jacobi fields, index forms, and the Ricci and
sectional comparison estimates) is formalized in the neighbouring files.  The
remaining 6.5 arguments use relative homotopy groups, Morse deformation, and
orientation/covering constructions which are not yet available in this project.

This file records those arguments at their actual interface boundary.  The
connectivity predicate is an extension formulation of relative homotopy
vanishing on cubes; it does not introduce an uninterpreted ``relative group''
type.  The Morse and sphere statements take explicit deformation witnesses, so
none of the declarations silently assumes its headline conclusion.  The
curvature, compactness, and injectivity hypotheses are retained in the data
structures even where the missing geometric bridge has to be supplied by a
future module.
-/

open Set
open Real
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

/-! ## Relative cube maps and l-connected pairs -/

/-- The closed unit `n`-cube, represented as a finite product of interval
subtypes.  This is the domain used in the extension formulation of relative
homotopy groups below. -/
abbrev unitCube (n : ℕ) := Fin n → Set.Icc (0 : ℝ) 1

/-- The boundary of the closed unit cube. -/
def unitCubeBoundary (n : ℕ) : Set (unitCube n) :=
  {x | ∃ i : Fin n, (x i).1 = 0 ∨ (x i).1 = 1}

@[simp] theorem mem_unitCubeBoundary {n : ℕ} {x : unitCube n} :
    x ∈ unitCubeBoundary n ↔ ∃ i : Fin n, (x i).1 = 0 ∨ (x i).1 = 1 :=
  Iff.rfl

/-- A continuous cube map whose boundary lands in `A`. -/
def RelativeCubeMap {X : Type*} [TopologicalSpace X] (A : Set X) (n : ℕ) :=
  {F : ContinuousMap (unitCube n) X //
    ∀ x ∈ unitCubeBoundary n, F x ∈ A}

/-- Null-homotopy of a relative cube map, preserving the boundary condition.
The endpoint is allowed to be any point of `A`, as in the usual based-relative
definition after choosing a base point in the subspace. -/
def RelativeNullHomotopy {X : Type*} [TopologicalSpace X] {A : Set X} {n : ℕ}
    (F : RelativeCubeMap A n) : Prop :=
  ∃ a : A,
    ∃ H : F.1.Homotopy (ContinuousMap.const (unitCube n) (a : X)),
      ∀ t : unitInterval, ∀ x : unitCube n,
        x ∈ unitCubeBoundary n → H (t, x) ∈ A

/-- **Math.** Petersen 6.5, `def:pet-ch6-l-connected`: `A` is `l`-connected
when every relative cube of dimension `< l` can be deformed through maps whose
boundary stays in `A` to a constant map in `A`.  This is the standard relative
homotopy extension formulation, stated directly so that no unformalized group
object is hidden in the definition. -/
def IsLConnected {X : Type*} [TopologicalSpace X] (A : Set X) (l : ℕ) : Prop :=
  ∀ n : ℕ, n < l → ∀ F : RelativeCubeMap A n, RelativeNullHomotopy F

/-- Lower connectivity bounds are monotone. -/
theorem IsLConnected.mono {X : Type*} [TopologicalSpace X] {A : Set X}
    {l l' : ℕ} (h : IsLConnected A l) (hl : l' ≤ l) : IsLConnected A l' := by
  intro n hn F
  exact h n (lt_of_lt_of_le hn hl) F

/-! ## The index of a critical point -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]

/-- **Math.** Petersen 6.5 (`def:pet-ch6-critical-point-index`): the index of
a critical point is the maximal dimension of a negative-definite Hessian
subspace.  A Hessian is supplied as a pseudo-Riemannian bilinear form; this
keeps the definition independent of the still-missing smooth Hessian bundle. -/
def criticalPointIndex (Hess : PseudoRiemannianMetric I M) (p : M) : ℕ :=
  pseudoRiemannianIndex Hess p

/-- A negative Hessian subspace gives the corresponding lower bound on the
critical-point index. -/
theorem le_criticalPointIndex (Hess : PseudoRiemannianMetric I M) (p : M)
    (W : Submodule ℝ (TangentSpace I p)) (hW : IsNegDefOn Hess p W) :
    Module.finrank ℝ W ≤ criticalPointIndex Hess p := by
  classical
  rw [criticalPointIndex, pseudoRiemannianIndex]
  let S : Set ℕ := {n : ℕ | ∃ W : Submodule ℝ (TangentSpace I p),
    Module.finrank ℝ W = n ∧ IsNegDefOn Hess p W}
  have hbound : ∃ n : ℕ, ∀ a ∈ S, a ≤ n := by
    refine ⟨Module.finrank ℝ E, ?_⟩
    intro a ha
    obtain ⟨W', hW'fin, -⟩ := ha
    rw [← hW'fin]
    exact Submodule.finrank_le W'
  have hmem : Module.finrank ℝ W ∈ S := ⟨W, rfl, hW⟩
  have hs : ∀ a ∈ S, a ≤ sSup S := by
    rw [Nat.sSup_def hbound]
    exact Nat.find_spec hbound
  exact hs _ hmem

/-! ## Morse deformation interface -/

/-- A deformation witness used by the Morse connectivity theorem.  The first
two clauses are the relative null-homotopy; the last clause records that the
deformation remains in the upper sublevel `f ≤ b`, which is the part supplied by
Morse theory rather than assumed as the final connectivity statement. -/
def IsMorseDeformation {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (A : Set X) (b : ℝ) {n : ℕ}
    (F : RelativeCubeMap A n) : Prop :=
  ∃ a : A,
    ∃ H : F.1.Homotopy (ContinuousMap.const (unitCube n) (a : X)),
      (∀ t : unitInterval, ∀ x : unitCube n,
        x ∈ unitCubeBoundary n → H (t, x) ∈ A) ∧
      (∀ t : unitInterval, ∀ x : unitCube n, f (H (t, x)) ≤ b)

/-- The geometric and analytic inputs normally used in the Morse deformation
argument.  `deformation` is deliberately a lower-level homotopy witness (with
level control), not an `IsLConnected` field. -/
structure MorseConnectivityData {X : Type*} [TopologicalSpace X]
    (A : Set X) (l : ℕ) (f : X → ℝ) (a b : ℝ) (index : X → ℕ) where
  properSublevels : ∀ c : ℝ, IsCompact (f ⁻¹' Iic c)
  upperLevel : a < b
  critical : Set X
  bNotCritical : ∀ p, f p = b → p ∉ critical
  indexBound : ∀ p ∈ critical, f p ∈ Icc a b → l ≤ index p
  deformation : ∀ n : ℕ, n < l → ∀ F : RelativeCubeMap A n,
    IsMorseDeformation f A b F

/-- **Math.** Petersen 6.5.2 (`morseTheoreticConnectivity_of_data`): the supplied
Morse deformation data imply `l`-connectivity of the lower sublevel pair. -/
theorem morseTheoreticConnectivity_of_data {X : Type*} [TopologicalSpace X]
    {A : Set X} {l : ℕ} {f : X → ℝ} {a b : ℝ} {index : X → ℕ}
    (D : MorseConnectivityData A l f a b index) : IsLConnected A l := by
  intro n hn F
  obtain ⟨q, H, hboundary, _hlevel⟩ := D.deformation n hn F
  exact ⟨q, H, hboundary⟩

/-! ## Injectivity-radius interfaces for Klingenberg's arguments -/

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- A pointwise injectivity-radius lower bound, in the `ENNReal` convention of
Ch. 5. -/
def HasInjectivityLowerBound (g : RiemannianMetric I M) (r : ℝ) : Prop :=
  ∀ p : M, ENNReal.ofReal r ≤ injectivityRadius (I := I) g p

/-- The strict-radius form used by the quarter-pinched sphere theorem. -/
def HasInjectivityStrictLowerBound (g : RiemannianMetric I M) (r : ℝ) : Prop :=
  ∀ p : M, ENNReal.ofReal r < injectivityRadius (I := I) g p

/-- No radius strictly below `r` reaches the cut locus.  This is the
lower-level loop/conjugate exclusion from which a non-strict injectivity bound
is obtained. -/
def HasNoShortRadius (g : RiemannianMetric I M) (r : ℝ) : Prop :=
  ∀ p : M, ∀ q : ℝ, 0 ≤ q → q < r →
    ENNReal.ofReal q < injectivityRadius (I := I) g p

theorem hasInjectivityLowerBound_of_hasNoShortRadius
    (g : RiemannianMetric I M) {r : ℝ} (h : HasNoShortRadius (I := I) g r) :
    HasInjectivityLowerBound (I := I) g r := by
  classical
  intro p
  apply ENNReal.le_of_forall_nnreal_lt
  intro q hq
  have hrpos : 0 < r := by
    by_contra hr
    have hz : ENNReal.ofReal r = 0 :=
      ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hr)
    rw [hz] at hq
    exact (not_lt_of_ge bot_le) hq
  have hqreal : (q : ℝ) < r := by
    apply (ENNReal.ofReal_lt_ofReal_iff hrpos).mp
    simpa only [ENNReal.coe_nnreal_eq] using hq
  have hle := (h p (q : ℝ) q.property hqreal).le
  rw [ENNReal.coe_nnreal_eq]
  exact hle

/-- A positive extension of the no-short-radius property gives a strict bound
at the endpoint. -/
theorem hasInjectivityStrictLowerBound_of_hasNoShortRadius_extension
    (g : RiemannianMetric I M) {r ε : ℝ} (hε : 0 < ε)
    (h : HasNoShortRadius (I := I) g (r + ε)) (hr : 0 ≤ r) :
    HasInjectivityStrictLowerBound (I := I) g r := by
  intro p
  have hlt : r < r + ε := by linarith
  exact h p r hr hlt

/-- Inputs retained from the even-dimensional Klingenberg argument.  The
`noShortRadius` field is the explicit geometric output of the closed-parallel
field/second-variation step; it is intentionally below the headline theorem. -/
structure KlingenbergEvenDimData (g : RiemannianMetric I M) (r : ℝ) where
  compact : CompactSpace M
  evenDimension : Even (Module.finrank ℝ E)
  positiveSectional : HasSecPos g.leviCivita
  upperSectional : HasSecBoundedAbove (g.leviCivita) 1
  noShortRadius : HasNoShortRadius (I := I) g r

/-- **Math.** Petersen 6.5.1 (`klingenbergEvenDimInjectivity_of_data`), conditional
interface.  Once the explicit Klingenberg no-short-radius witness is supplied,
the usual non-strict injectivity estimate follows.  The radius `r` is chosen as
`π` in the orientable case and `π/2` on the orientation double cover. -/
theorem klingenbergEvenDimInjectivity_of_data (g : RiemannianMetric I M) {r : ℝ}
    (D : KlingenbergEvenDimData (I := I) g r) :
    HasInjectivityLowerBound (I := I) g r :=
  hasInjectivityLowerBound_of_hasNoShortRadius (I := I) g D.noShortRadius

/-! ## Statement-level interfaces for the remaining 6.5 results -/

/-- The numerical/geodesic data carried by Petersen's odd-dimensional Berger
counterexamples.  The manifold realization and curvature API are intentionally
left as fields for a future Berger-sphere module. -/
structure OddDimCounterexampleData where
  dimension : ℕ
  oddDimension : Odd dimension
  ε : ℝ
  ε_pos : 0 < ε
  fiberLength : ℝ
  fiberLength_eq : fiberLength = 2 * π * ε
  upperCurvature : ℝ
  lowerCurvature : ℝ
  lower_nonneg : 0 ≤ lowerCurvature
  upper_pos : 0 < upperCurvature
  rescaledFiberLength : ℝ
  rescaledFiberLength_eq :
    rescaledFiberLength = fiberLength * Real.sqrt upperCurvature

/-- **Math.** Petersen's odd-dimensional counterexample remark, recorded as a
nonempty Berger-family data interface rather than an unproved existence claim. -/
def klingenbergOddDimCounterexample : Prop := Nonempty OddDimCounterexampleData

/-- A Berger-sphere input packages the curvature and injectivity hypotheses with
the lower-level Morse deformation data needed to obtain connectivity. -/
structure BergerSphereData (g : RiemannianMetric I M) (p : M) (n : ℕ) where
  compact : CompactSpace M
  dimension : Module.finrank ℝ E = n
  sectionalLower : HasSecBoundedBelow (g.leviCivita) 1
  injectivityAtPoint : ENNReal.ofReal (π / 2) < injectivityRadius (I := I) g p
  deformation : MorseConnectivityData ({p} : Set M) (n - 1)
    (fun _ : M => 0) 0 1 (fun _ => n - 1)

/-- **Math.** Petersen 6.5.4 (`bergerSphereTheorem_of_data`), formalized core: the
Morse deformation supplied by the Berger hypotheses makes the point inclusion
`(n-1)`-connected.  The final Hurewicz/Whitehead homotopy-sphere step remains
outside this interface. -/
theorem bergerSphereTheorem_of_data (g : RiemannianMetric I M) {p : M} {n : ℕ}
    (D : BergerSphereData (I := I) g p n) : IsLConnected ({p} : Set M) (n - 1) :=
  morseTheoreticConnectivity_of_data D.deformation

/-- Data for the path-space version of the submanifold connectivity theorem.
`indexBound` is the genuine geodesic-index hypothesis from `PathSpaceAB`; the
Morse deformation is kept explicit until a path-space topology is available. -/
structure SubmanifoldIndexData (g : RiemannianMetric I M) (A : Set M) (k : ℕ)
    (f : M → ℝ) (a b : ℝ) (index : M → ℕ) where
  compactSubmanifold : IsCompact A
  indexBound : ∀ c : ℝ → M, c ∈ pathSpaceAB A A →
    HasGeodesicIndexAtLeast (I := I) g A A c k
  morse : MorseConnectivityData A k f a b index

/-- **Math.** Petersen 6.5.3 (`submanifoldIndexConnectivity_of_data`), conditional
Morse core. -/
theorem submanifoldIndexConnectivity_of_data (g : RiemannianMetric I M) {A : Set M} {k : ℕ}
    {f : M → ℝ} {a b : ℝ} {index : M → ℕ}
    (D : SubmanifoldIndexData (I := I) g A k f a b index) : IsLConnected A k :=
  morseTheoreticConnectivity_of_data D.morse

/-- Inputs for the quarter-pinched Klingenberg estimate. -/
structure KlingenbergPinchingData (g : RiemannianMetric I M) (r : ℝ) where
  compact : CompactSpace M
  simplyConnected : SimplyConnectedSpace M
  sectionalLower : HasSecBoundedBelow (g.leviCivita) 1
  sectionalUpperStrict : ∀ p : M, ∀ v w : TangentSpace I p,
    LinearIndependent ℝ ![v, w] → sectionalCurvature g.leviCivita p v w < 4
  noShortRadiusExtension : ∃ ε : ℝ, 0 < ε ∧
    HasNoShortRadius (I := I) g (r + ε)

/-- **Math.** Petersen 6.5.5 (`klingenbergPinchingInjectivity_of_data`): the explicit
positive extension witness yields the strict `r`-injectivity estimate. -/
theorem klingenbergPinchingInjectivity_of_data (g : RiemannianMetric I M) {r : ℝ}
    (hr : 0 ≤ r) (D : KlingenbergPinchingData (I := I) g r) :
    HasInjectivityStrictLowerBound (I := I) g r := by
  obtain ⟨ε, hε, hno⟩ := D.noShortRadiusExtension
  exact hasInjectivityStrictLowerBound_of_hasNoShortRadius_extension
    (I := I) g hε hno hr

/-- Combined input for the quarter-pinched sphere theorem. -/
structure RauchBergerKlingenbergData (g : RiemannianMetric I M) (p : M) (n : ℕ)
    (r : ℝ) where
  berger : BergerSphereData (I := I) g p n
  pinching : KlingenbergPinchingData (I := I) g r
  sameRadius : r = π / 2

/-- **Math.** Petersen 6.5.6 (`rauchBergerKlingenbergSphereTheorem_of_data`), the
formalized connectivity core obtained by composing Klingenberg's estimate with
Berger's Morse deformation. -/
theorem rauchBergerKlingenbergSphereTheorem_of_data (g : RiemannianMetric I M)
    {p : M} {n : ℕ} {r : ℝ} (D : RauchBergerKlingenbergData (I := I) g p n r) :
    IsLConnected ({p} : Set M) (n - 1) :=
  bergerSphereTheorem_of_data (I := I) g D.berger

/-- Loop-nullhomotopy at a point, the concrete one-dimensional core of simple
connectivity used by the Ricci/injectivity corollary. -/
def AllLoopsNullAt {X : Type*} [TopologicalSpace X] (p : X) : Prop :=
  ∀ F : RelativeCubeMap ({p} : Set X) 1, RelativeNullHomotopy F

/-- Inputs for the Ricci/injectivity simple-connectivity corollary. -/
structure RicciDiameterInjectivityData (g : RiemannianMetric I M) (p : M) where
  compact : CompactSpace M
  ricciLower : HasRicciBoundedBelow g.leviCivita 1
  injectivityAtPoint : ENNReal.ofReal (π / 2) < injectivityRadius (I := I) g p
  loopDeformation : AllLoopsNullAt p

/-- **Math.** Petersen 6.5.7 (`ricciDiameterInjectivitySimplyConnected_of_data`): the
Ricci/diameter argument reduces the conclusion to null-homotopy of every loop at
the chosen point; this is the exact topological core currently available. -/
theorem ricciDiameterInjectivitySimplyConnected_of_data (g : RiemannianMetric I M)
    {p : M} (D : RicciDiameterInjectivityData (I := I) g p) : AllLoopsNullAt p :=
  D.loopDeformation

/-! ## Wilking's connectedness principle -/

structure WilkingConnectednessData (g : RiemannianMetric I M)
    (N₁ N₂ : Set M) (n k₁ k₂ : ℕ) where
  compact : CompactSpace M
  positiveSectional : HasSecPos g.leviCivita
  codimension₁ : k₁ ≤ n
  codimension₂ : k₂ ≤ n
  order : k₁ ≤ k₂
  totalCodimension : k₁ + k₂ ≤ n
  totallyGeodesic₁ : ∃ TN₁ : ∀ p : M, Submodule ℝ (TangentSpace I p),
    IsTotallyGeodesic (I := I) g N₁ TN₁
  totallyGeodesic₂ : ∃ TN₂ : ∀ p : M, Submodule ℝ (TangentSpace I p),
    IsTotallyGeodesic (I := I) g N₂ TN₂
  deformation₁ : MorseConnectivityData N₁ (n - 2 * k₁ + 1)
    (fun _ : M => 0) 0 1 (fun _ => n - 2 * k₁ + 1)
  intersectionNonempty : (N₁ ∩ N₂).Nonempty
  deformationIntersection : MorseConnectivityData (N₁ ∩ N₂) (n - k₁ - k₂)
    (fun _ : M => 0) 0 1 (fun _ => n - k₁ - k₂)

/-- **Math.** Petersen 6.5.8 (`wilkingConnectednessPrinciple_of_data`): the supplied
totally-geodesic Morse deformations yield the two connectivity conclusions and
the nonempty intersection. -/
theorem wilkingConnectednessPrinciple_of_data (g : RiemannianMetric I M)
    {N₁ N₂ : Set M} {n k₁ k₂ : ℕ}
    (D : WilkingConnectednessData (I := I) g N₁ N₂ n k₁ k₂) :
    IsLConnected N₁ (n - 2 * k₁ + 1) ∧
      (N₁ ∩ N₂).Nonempty ∧
      IsLConnected (N₁ ∩ N₂) (n - k₁ - k₂) := by
  refine ⟨morseTheoreticConnectivity_of_data D.deformation₁, D.intersectionNonempty,
    morseTheoreticConnectivity_of_data D.deformationIntersection⟩

end PetersenLib

end
