import MorganTianLib.Ch04.HamiltonMaximumCore
import MorganTianLib.Ch04.ODEInvariant

/-!
# Morgan--Tian Ch. 4 - transported and local maximum principles

The source records a maximum principle for genuinely moving convex carriers and
for compact domains with boundary.  The compact constant-fiber theorem in
HamiltonMaximumCore does not by itself provide either transport or
localisation.  This file therefore proves two explicit consequences:

* a translated carrier, with the translated reaction field and operator;
* the compact-closure/boundary iff, obtained by applying the global theorem to
  the compact closure.

The translation data are concrete (not a preservation certificate): an
integral curve is subtracted from the prescribed translation and the existing
convex ODE theorem is applied to the resulting autonomous curve.  General
parallel transport in a tensor bundle, arbitrary time-dependent convex slices,
and the smooth codimension-zero localisation argument remain separate
producers.
-/

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

section TranslatedFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ### Concrete translated families -/

/-- The time-t translate of a fixed carrier. -/
def translatedCarrier (Z : Set E) (c : ℝ → E) (t : ℝ) : Set E :=
  (fun z => z + c t) '' Z

/-- Reaction field obtained by transporting an autonomous field through the
time-dependent translation c.  The second argument is the prescribed
derivative of c; its regularity is an explicit hypothesis of the transport
lemmas below. -/
def translatedReaction (ψ : E → E) (c c' : ℝ → E) : ℝ → E → E :=
  fun t v => ψ (v - c t) + c' t

/-! ### Integral-curve preservation for the moving carrier -/

/--
An integral curve of the transported reaction field stays in the translated
carrier whenever its initial value does.  This is the integral-curve form of
Hamilton's moving-set hypothesis for the concrete translation family.
-/
theorem integralCurve_mem_translatedCarrier
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    (hψ : LipschitzWith K ψ)
    (c c' : ℝ → E) (hc : ∀ s : ℝ, HasDerivAt c (c' s) s)
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : IsIntegralCurveOn γ (translatedReaction ψ c c') (Icc a b))
    (hinit : γ a ∈ translatedCarrier Z c a) :
    ∀ t ∈ Icc a b, γ t ∈ translatedCarrier Z c t := by
  let δ : ℝ → E := fun s => γ s - c s
  have hδ : IsIntegralCurveOn δ (fun _ : ℝ => ψ) (Icc a b) := by
    intro s hs
    have hγs := hγ s hs
    have hcs : HasDerivWithinAt c (c' s) (Icc a b) s :=
      (hc s).hasDerivWithinAt
    have hsub := hγs.sub hcs
    change HasDerivWithinAt (γ - c) (ψ (γ s - c s)) (Icc a b) s
    rw [translatedReaction] at hsub
    convert hsub using 1
    abel
  obtain ⟨z, hz, hza⟩ := hinit
  have hδa : δ a ∈ Z := by
    have hza' : γ a = z + c a := hza.symm
    dsimp [δ]
    rw [hza']
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
  have hδmem := integralCurve_mem_of_vectorFieldPreservesConvexSet
    hZne hZclosed hZconv hψ hpres hab hδ hδa
  intro t ht
  refine ⟨δ t, hδmem t ht, ?_⟩
  dsimp [δ]
  abel

/-! ### PDE transport -/

/--
The operator transported through a time-dependent translation.  It is defined
by subtracting the translation from every spatial value before applying the
fixed-fiber operator.  This makes the reduction to the compact core
definitional once u = v + c is supplied.
-/
def translatedOperator {X : Type*} (L : ℝ → (X → E) → X → E)
    (c : ℝ → E) : ℝ → (X → E) → X → E :=
  fun t f x => L t (fun y => f y - c t) x

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

/--
Maximum principle for a compact carrier translated in time.  The unknown v is
the field in fixed coordinates and u = v + c is the transported field.
The PDE hypothesis is stated for the concrete translated operator/reaction;
the proof differentiates u-c and invokes the checked compact constant-fiber
theorem.  Thus no support or preservation property is assumed as a target
shaped certificate.
-/
theorem hamilton_tensor_maximum_principle_varying_translation
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) (hZcompact : IsCompact Z)
    {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    (hψ : LipschitzWith K ψ)
    (c c' : ℝ → E) (hc : ∀ s : ℝ, HasDerivAt c (c' s) s)
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u v : X → ℝ → E)
    (huv : ∀ x s, u x s = v x s + c s)
    {a b : ℝ}
    (hF : Continuous ↿(hamiltonSupportValueFamily Z v))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamily Z v L ψ))
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x)
        (translatedOperator L c s (fun y : X => u y s) x +
          translatedReaction ψ c c' s (u x s)) s)
    (hinit : ∀ x : X, v x a ∈ Z) :
    ∀ x : X, ∀ t ∈ Icc a b, u x t ∈ translatedCarrier Z c t := by
  have hvpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (v x) (L s (fun y : X => v y s) x + ψ (v x s)) s := by
    intro x s
    have hu := hpde x s
    have hsub := hu.sub (hc s)
    have hfun : v x = fun r : ℝ => u x r - c r := by
      funext r
      rw [huv x r]
      abel_nf
    have hLtrans : translatedOperator L c s (fun y : X => u y s) x =
        L s (fun y : X => v y s) x := by
      simp only [translatedOperator]
      congr 2
      funext y
      rw [huv y s]
      abel
    have hR : translatedReaction ψ c c' s (u x s) = ψ (v x s) + c' s := by
      simp only [translatedReaction]
      rw [huv x s]
      congr 1
      abel_nf
    have hsub' : HasDerivAt (u x - c)
        (L s (fun y : X => v y s) x + ψ (v x s)) s := by
      rw [hLtrans, hR] at hsub
      convert hsub using 1
      abel
    have hsubLambda : HasDerivAt (fun r : ℝ => u x r - c r)
        (L s (fun y : X => v y s) x + ψ (v x s)) s := by
      have heq : (fun r : ℝ => u x r - c r) =ᶠ[𝓝 s] (u x - c) := by
        filter_upwards [] with r
        rfl
      exact hsub'.congr_of_eventuallyEq heq
    have heqv : v x =ᶠ[𝓝 s] (fun r : ℝ => u x r - c r) :=
      Filter.Eventually.of_forall (fun r => congrFun hfun r)
    exact hsubLambda.congr_of_eventuallyEq heqv
  have hv := hamilton_tensor_maximum_principle_compact
    (X := X) (a := a) (b := b) hZne hZclosed hZconv hZcompact hpres hψ L hL v
      hF hF' hvpde hinit
  intro x t ht
  refine ⟨v x t, hv x t ht, ?_⟩
  exact (huv x t).symm

end TranslatedFamily

section LocalPrinciple

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
The compact type X below represents the compact closure of U in the source
theorem.  U and B record the interior and boundary pieces; the cover
assumption is the only topological fact needed for the boundary iff.
Smoothness, connectedness, and codimension-zero localisation are deliberately
not inferred from this abstract compact-domain interface.
-/

/--
Compact-closure local maximum principle with persistent boundary values.  The
forward implication is the global compact theorem applied to the closure; the
reverse implication simply restricts its conclusion to the initial and
boundary subsets.  This is an honest local consequence, while the geometric
codimension-zero localisation and boundary extension remain explicit inputs
for a later producer.
-/
theorem hamilton_tensor_maximum_principle_local_iff
    (U B : Set X) (hcover : U ∪ B = (univ : Set X))
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) (hZcompact : IsCompact Z)
    {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    (hψ : LipschitzWith K ψ)
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u : X → ℝ → E)
    {a b : ℝ} (hab : a ≤ b)
    (hF : Continuous ↿(hamiltonSupportValueFamily Z u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamily Z u L ψ))
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s) :
    ((∀ x ∈ U, u x a ∈ Z) ∧
      (∀ x ∈ B, ∀ t ∈ Icc a b, u x t ∈ Z)) ↔
      (∀ x : X, ∀ t ∈ Icc a b, u x t ∈ Z) := by
  constructor
  · rintro ⟨hUinit, hB⟩
    have hinit : ∀ x : X, u x a ∈ Z := by
      intro x
      have hx' : x ∈ U ∪ B := by
        rw [hcover]
        exact mem_univ x
      have hx : x ∈ U ∨ x ∈ B := mem_or_mem_of_mem_union hx'
      cases hx with
      | inl hxU => exact hUinit x hxU
      | inr hxB => exact hB x hxB a ⟨le_rfl, hab⟩
    exact hamilton_tensor_maximum_principle_compact
      (X := X) hZne hZclosed hZconv hZcompact hpres hψ L hL u hF hF' hpde hinit
  · intro hall
    constructor
    · intro x hx
      exact hall x a ⟨le_rfl, hab⟩
    · intro x hx t ht
      exact hall x t ht

end LocalPrinciple

end MorganTianLib
