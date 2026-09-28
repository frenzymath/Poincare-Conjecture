import MorganTianLib.Ch04.HamiltonMaximumCore

/-!
# Morgan--Tian Ch. 4 - a moving convex-carrier maximum principle

This file supplies the time-dependent carrier step left open by the fixed
carrier theorem in `HamiltonMaximumCore`.  A compact parameter space indexes
support pairs for every time slice.  The point and normal components of a
support pair are allowed to move; their velocities therefore occur explicitly
in the scalar support derivative and in the reaction viability condition.

The geometric construction of these data from a tensor bundle and a connection
is a separate producer.  Here all analytic inputs are visible: closedness,
convexity and nonemptiness of the slices, support-pair attainment, continuity,
the PDE, support-point/normal derivatives, the spatial maximum inequality, a
reaction viability bound, and a reach bound for the trajectory.
-/

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

section MovingCarrier

variable {X E P : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Time-dependent support scalarizations -/

/-- A support-pair family for a time-dependent carrier. -/
abbrev MovingSupportFamily (Z : ℝ → Set E) :=
  ∀ t : ℝ, P → ConvexSupportPair (Z t)

/-- The scalar support value, with a zero competitor indexed by `Unit`. -/
def movingSupportValue (Z : ℝ → Set E) (support : MovingSupportFamily (P := P) Z)
    (u : X → ℝ → E) (x : X) (q : Unit ⊕ P) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr p =>
      ⟪(support t p).1.2, u x t - (support t p).1.1⟫_ℝ

/-- The derivative of a moving support value.  `pointVelocity` and
`normalVelocity` are the explicitly supplied velocities of the support point
and normal. -/
def movingSupportDerivative (Z : ℝ → Set E)
    (support : MovingSupportFamily (P := P) Z)
    (pointVelocity normalVelocity : P → ℝ → E)
    (u : X → ℝ → E) (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (x : X) (q : Unit ⊕ P) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr p =>
      ⟪normalVelocity p t, u x t - (support t p).1.1⟫_ℝ +
        ⟪(support t p).1.2,
          L t (fun y : X => u y t) x + ψ (u x t) - pointVelocity p t⟫_ℝ

/-- Product-parameter form of `movingSupportValue`. -/
def movingSupportValueFamily (Z : ℝ → Set E)
    (support : MovingSupportFamily (P := P) Z) (u : X → ℝ → E)
    (xp : X × (Unit ⊕ P)) (t : ℝ) : ℝ :=
  movingSupportValue Z support u xp.1 xp.2 t

/-- Product-parameter form of `movingSupportDerivative`. -/
def movingSupportDerivativeFamily (Z : ℝ → Set E)
    (support : MovingSupportFamily (P := P) Z)
    (pointVelocity normalVelocity : P → ℝ → E)
    (u : X → ℝ → E) (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (xp : X × (Unit ⊕ P)) (t : ℝ) : ℝ :=
  movingSupportDerivative Z support pointVelocity normalVelocity u L ψ xp.1 xp.2 t

/-! ### Explicit reaction viability for a moving slice -/

/-- Support-level viability of the reaction for a moving carrier.

At a reachable point and an attained support pair, the normal component of the
reaction together with the motion of the support is bounded by the supplied
constant times the distance to the carrier.  This is an explicit
support-functional viability interface; a geometric bridge from an
integral-curve preservation statement for the time-dependent family is a
separate producer.
-/
def movingCarrierReactionPreserves
    (Z : ℝ → Set E) (support : MovingSupportFamily (P := P) Z)
    (pointVelocity normalVelocity : P → ℝ → E) (ψ : E → E)
    (Reach : ℝ → E → Prop) (K : ℝ≥0) : Prop :=
  ∀ t : ℝ, ∀ v : E, Reach t v →
    ∀ p : P,
      ⟪(support t p).1.2, v - (support t p).1.1⟫_ℝ = Metric.infDist v (Z t) →
      ⟪normalVelocity p t, v - (support t p).1.1⟫_ℝ +
          ⟪(support t p).1.2, ψ v - pointVelocity p t⟫_ℝ ≤
        (K : ℝ) * Metric.infDist v (Z t)

/-! ### Derivative of a moving support scalar -/

omit [TopologicalSpace X] [CompactSpace X] [Nonempty X] [TopologicalSpace P]
  [CompactSpace P] [FiniteDimensional ℝ E] in
theorem hasDerivAt_movingSupportValue
    {Z : ℝ → Set E} (support : MovingSupportFamily (P := P) Z)
    (pointVelocity normalVelocity : P → ℝ → E)
    {u : X → ℝ → E} {L : ℝ → (X → E) → X → E} {ψ : E → E}
    (hpoint : ∀ p : P, ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => (support r p).1.1) (pointVelocity p s) s)
    (hnormal : ∀ p : P, ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => (support r p).1.2) (normalVelocity p s) s)
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (x : X) (q : Unit ⊕ P) (s : ℝ) :
    HasDerivAt (movingSupportValue Z support u x q)
      (movingSupportDerivative Z support pointVelocity normalVelocity u L ψ x q s) s := by
  cases q with
  | inl _ =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) s
      exact hasDerivAt_const (x := s) (c := (0 : ℝ))
  | inr p =>
      have hsub : HasDerivAt
          (fun r : ℝ => u x r - (support r p).1.1)
          (L s (fun y : X => u y s) x + ψ (u x s) - pointVelocity p s) s := by
        have hsub' := (hpde x s).sub (hpoint p s)
        have heq : (u x - fun r : ℝ => (support r p).1.1) =ᶠ[𝓝 s]
            (fun r : ℝ => u x r - (support r p).1.1) := by
          filter_upwards [] with r
          rfl
        exact hsub'.congr_of_eventuallyEq heq
      change HasDerivAt
        (fun r : ℝ => ⟪(support r p).1.2,
          u x r - (support r p).1.1⟫_ℝ)
        (⟪normalVelocity p s, u x s - (support s p).1.1⟫_ℝ +
          ⟪(support s p).1.2,
            L s (fun y : X => u y s) x + ψ (u x s) - pointVelocity p s⟫_ℝ) s
      simpa [movingSupportDerivative, add_comm] using (hnormal p s).inner ℝ hsub

/-!
### The time-dependent compact-support tensor maximum principle

The proof is the same scalar barrier used by
`hamilton_tensor_maximum_principle_compact_support`, but the support point and
normal are now time dependent.  The moving support derivative and reaction
viability hypotheses are kept separate so a geometric bundle producer can
discharge them without changing this theorem.
-/
theorem hamilton_tensor_maximum_principle_moving_support
    {Z : ℝ → Set E}
    (hZne : ∀ t : ℝ, (Z t).Nonempty)
    (hZclosed : ∀ t : ℝ, IsClosed (Z t))
    (hZconv : ∀ t : ℝ, Convex ℝ (Z t))
    (support : MovingSupportFamily (P := P) Z)
    {Reach : ℝ → E → Prop}
    (hattain : ∀ t : ℝ, ∀ v : E, Reach t v → v ∉ Z t → ∃ p : P,
      ⟪(support t p).1.2, v - (support t p).1.1⟫_ℝ = Metric.infDist v (Z t))
    {ψ : E → E} {K : ℝ≥0}
    (pointVelocity normalVelocity : P → ℝ → E)
    (hpres : movingCarrierReactionPreserves Z support pointVelocity normalVelocity
      ψ Reach K)
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u : X → ℝ → E) {a b : ℝ}
    (hF : Continuous ↿(movingSupportValueFamily Z support u))
    (hF' : Continuous ↿(movingSupportDerivativeFamily Z support pointVelocity
      normalVelocity u L ψ))
    (hpoint : ∀ p : P, ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => (support r p).1.1) (pointVelocity p s) s)
    (hnormal : ∀ p : P, ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => (support r p).1.2) (normalVelocity p s) s)
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (hinit : ∀ x : X, u x a ∈ Z a)
    (hreach_u : ∀ x : X, ∀ t : ℝ, t ∈ Icc a b → Reach t (u x t)) :
    ∀ x : X, ∀ t ∈ Icc a b, u x t ∈ Z t := by
  let A := X × (Unit ⊕ P)
  letI : TopologicalSpace A :=
    inferInstanceAs (TopologicalSpace (X × (Unit ⊕ P)))
  letI : CompactSpace A :=
    inferInstanceAs (CompactSpace (X × (Unit ⊕ P)))
  letI : Nonempty A :=
    inferInstanceAs (Nonempty (X × (Unit ⊕ P)))
  let F : A → ℝ → ℝ := movingSupportValueFamily Z support u
  let F' : A → ℝ → ℝ := movingSupportDerivativeFamily Z support pointVelocity
    normalVelocity u L ψ
  have hderiv : ∀ q : A, ∀ s ∈ Ioo a b,
      HasDerivAt (F q) (F' q s) s := by
    intro q s hs
    change HasDerivAt (movingSupportValue Z support u q.1 q.2)
      (movingSupportDerivative Z support pointVelocity normalVelocity u L ψ
        q.1 q.2 s) s
    exact hasDerivAt_movingSupportValue support pointVelocity normalVelocity
      hpoint hnormal hpde q.1 q.2 s
  have hinitF : (⨆ q : A, F q a) ≤ 0 := by
    apply ciSup_le
    rintro ⟨x, o⟩
    cases ho : o with
    | inl _ => simp [F, movingSupportValueFamily, movingSupportValue]
    | inr p =>
        have hnonpos := convexSupportPair_eval_nonpos (Z a) (support a p)
          (u x a) (hinit x)
        simpa [F, movingSupportValueFamily, movingSupportValue] using hnonpos
  have hmax : ∀ t ∈ Ico a b, ∀ q : A,
      F q t = (⨆ r : A, F r t) →
        F' q t ≤ (K : ℝ) * (⨆ r : A, F r t) := by
    intro t ht q hqmax
    rcases q with ⟨x, o⟩
    cases ho : o with
    | inl z =>
        have hqmax' : F (x, Sum.inl z) t = (⨆ r : A, F r t) := by
          simpa [ho] using hqmax
        have hzero' : F (x, Sum.inl z) t = 0 := by
          simp [F, movingSupportValueFamily, movingSupportValue]
        have hUzero : (⨆ r : A, F r t) = 0 := by
          rw [hzero'] at hqmax'
          exact hqmax'.symm
        change (0 : ℝ) ≤ (K : ℝ) * (⨆ r : A, F r t)
        rw [hUzero]
        simp
    | inr p =>
        let v := u x t
        let q' : ConvexSupportPair (Z t) := support t p
        have hqmax' : F (x, Sum.inr p) t = (⨆ r : A, F r t) := by
          simpa [ho] using hqmax
        have hq_le_dist : F (x, Sum.inr p) t ≤ Metric.infDist v (Z t) := by
          have hpval := convexSupportPair_eval_le_infDist (Z t) (hZne t)
            (hZclosed t) (hZconv t) q' v
          simpa [F, movingSupportValueFamily, movingSupportValue, q', v] using hpval
        have hUle_dist : (⨆ r : A, F r t) ≤ Metric.infDist v (Z t) := by
          rw [← hqmax']
          exact hq_le_dist
        have hUge0 : (0 : ℝ) ≤ (⨆ r : A, F r t) := by
          have hzero : F (x, Sum.inl ()) t ≤ (⨆ r : A, F r t) :=
            le_ciSup (bddAbove_range_family hF t) (x, Sum.inl ())
          simpa [F, movingSupportValueFamily, movingSupportValue] using hzero
        have hUeq : (⨆ r : A, F r t) = Metric.infDist v (Z t) := by
          by_cases hv : v ∈ Z t
          · have hz : Metric.infDist v (Z t) = 0 := Metric.infDist_zero_of_mem hv
            linarith
          · obtain ⟨pe, hpe⟩ := hattain t v (hreach_u x t
                ⟨ht.1, le_of_lt ht.2⟩) hv
            have hpeval : F (x, Sum.inr pe) t = Metric.infDist v (Z t) := by
              simpa [F, movingSupportValueFamily, movingSupportValue, v] using hpe
            have hle : F (x, Sum.inr pe) t ≤ (⨆ r : A, F r t) :=
              le_ciSup (bddAbove_range_family hF t) (x, Sum.inr pe)
            linarith
        have hpactive :
            ⟪q'.1.2, v - q'.1.1⟫_ℝ = Metric.infDist v (Z t) := by
          rw [hUeq] at hqmax'
          simpa [F, movingSupportValueFamily, movingSupportValue, q', v] using hqmax'
        have hreac := hpres t v (hreach_u x t
          ⟨ht.1, le_of_lt ht.2⟩) p hpactive
        have hspatial : IsMaxOn (fun y : X => ⟪q'.1.2, u y t⟫_ℝ)
            (univ : Set X) x := by
          intro y hy
          have hle : F (y, Sum.inr p) t ≤ (⨆ r : A, F r t) :=
            le_ciSup (bddAbove_range_family hF t) (y, Sum.inr p)
          have hactive : F (x, Sum.inr p) t = (⨆ r : A, F r t) := by
            simpa [ho] using hqmax
          change ⟪q'.1.2, u x t - q'.1.1⟫_ℝ = (⨆ r : A, F r t) at hactive
          change ⟪q'.1.2, u y t - q'.1.1⟫_ℝ ≤ (⨆ r : A, F r t) at hle
          rw [inner_sub_right] at hactive hle
          have hxy :
              ⟪q'.1.2, u y t⟫_ℝ - ⟪q'.1.2, q'.1.1⟫_ℝ ≤
                ⟪q'.1.2, u x t⟫_ℝ - ⟪q'.1.2, q'.1.1⟫_ℝ :=
            hle.trans_eq hactive.symm
          exact (sub_le_sub_iff_right _).mp hxy
        have hdiff := hL t (fun y : X => u y t) q'.1.2 x hspatial
        have hsum := add_le_add hdiff hreac
        change
          (⟪normalVelocity p t, v - q'.1.1⟫_ℝ +
            ⟪q'.1.2, L t (fun y : X => u y t) x + ψ v - pointVelocity p t⟫_ℝ) ≤
            (K : ℝ) * (⨆ r : A, F r t)
        have hsplit :
            ⟪q'.1.2, L t (fun y : X => u y t) x + ψ v - pointVelocity p t⟫_ℝ =
                ⟪q'.1.2, L t (fun y : X => u y t) x⟫_ℝ +
                ⟪q'.1.2, ψ v - pointVelocity p t⟫_ℝ := by
          simp only [inner_sub_right, inner_add_right]
          ring
        rw [hsplit]
        rw [inner_sub_right] at hsum
        simpa [q', hUeq, inner_sub_right, add_assoc, add_left_comm, add_comm] using hsum
  have henv : ∀ t ∈ Icc a b, (⨆ q : A, F q t) ≤ 0 :=
    hamilton_envelope_nonpositive hF hF' hderiv hmax hinitF
  intro x t ht
  by_contra hv
  obtain ⟨pe, hpe⟩ := hattain t (u x t) (hreach_u x t ht) hv
  have hpos : 0 < F (x, Sum.inr pe) t := by
    have hd : 0 < Metric.infDist (u x t) (Z t) :=
      ((hZclosed t).notMem_iff_infDist_pos (hZne t)).mp hv
    have heq' : F (x, Sum.inr pe) t = Metric.infDist (u x t) (Z t) := by
      simpa [F, movingSupportValueFamily, movingSupportValue] using hpe
    rw [heq']
    exact hd
  have hle : F (x, Sum.inr pe) t ≤ (⨆ q : A, F q t) :=
    le_ciSup (bddAbove_range_family hF t) (x, Sum.inr pe)
  have hUpos : 0 < (⨆ q : A, F q t) := lt_of_lt_of_le hpos hle
  exact (not_lt_of_ge (henv t ht)) hUpos

end MovingCarrier

end MorganTianLib
