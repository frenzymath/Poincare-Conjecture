import MorganTianLib.Ch02.ForwardDifference
import MorganTianLib.Ch04.HamiltonPositiveEnvelope
import MorganTianLib.Ch04.ConvexInvariant
import MorganTianLib.Ch04.ConvexSupport
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Constructions.SumProd

/-!
# Morgan--Tian Ch. 4 - Hamilton's tensor maximum-principle core

This file proves the compact, constant-fiber part of Hamilton's argument.  The
parabolic input is deliberately an operator-level positive-maximum property:
for a scalarization by a fixed normal, the diffusion operator is nonpositive
at a spatial maximum.  The reaction estimate is obtained from the supporting
functional theorem and a nearest-point projection; it is not postulated as a
certificate about the chosen solution.

The public theorem below is the finite-dimensional compact-carrier version.
The unbounded cone case and the bundle/parallel-transport step remain explicit
producers for the later tensor-bundle theorem.
-/

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

/-! ### The scalar comparison engine -/

section Envelope

variable {A : Type*} [TopologicalSpace A] [CompactSpace A] [Nonempty A]

/-- A compact-family forward-difference maximum principle with zero barrier.

This is the scalar envelope step in Hamilton's proof.  The derivative bound is
assumed only at actual maximizers; all analytic regularity and the comparison
ODE are explicit hypotheses.
-/
theorem hamilton_envelope_nonpositive
    {F F' : A → ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ q : A, ∀ s ∈ Ioo a b,
      HasDerivAt (F q) (F' q s) s)
    (hmax : ∀ t ∈ Ico a b, ∀ q : A,
      F q t = (⨆ r : A, F r t) →
        F' q t ≤ (K : ℝ) * (⨆ r : A, F r t))
    (hinit : (⨆ q : A, F q a) ≤ 0) :
    ∀ t ∈ Icc a b, (⨆ q : A, F q t) ≤ 0 := by
  exact hamilton_envelope_nonpositive_of_positive_max hF hF' hderiv
    (fun t ht _ q hq => hmax t ht q hq) hinit

end Envelope

/-! ### Reaction estimate from a support pair -/

section Reaction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- At an active support pair, the reaction is bounded by the Lipschitz
constant times the distance to the carrier.

The proof compares the solution value with the nearest point `p` of `Z`.
Equality of the active support value with the distance forces the given normal
also to support `Z` at `p`; this is the point that prevents the common,
incorrect replacement of `‖v-k‖` by the envelope value for an arbitrary active
pair.
-/
theorem convexSupportPair_reaction_bound
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    (hψ : LipschitzWith K ψ) (v : E) (q : ConvexSupportPair Z)
    (hvalue : ⟪q.1.2, v - q.1.1⟫_ℝ = Metric.infDist v Z) :
    ⟪q.1.2, ψ v⟫_ℝ ≤ (K : ℝ) * Metric.infDist v Z := by
  let p : E := convexProjection Z hZne hZclosed hZconv v
  have hp : p ∈ Z := by
    exact convexProjection_mem Z hZne hZclosed hZconv v
  have hpdist : ‖v - p‖ = Metric.infDist v Z := by
    rw [← dist_eq_norm]
    exact convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v
  have hnorm : ‖q.1.2‖ = 1 := convexSupportPair_normal_unit Z q
  have hqps : ⟪q.1.2, p - q.1.1⟫_ℝ ≤ 0 :=
    convexSupportPair_support Z q p hp
  have hinner_le : ⟪q.1.2, v - p⟫_ℝ ≤ ‖v - p‖ := by
    calc
      ⟪q.1.2, v - p⟫_ℝ ≤ ‖q.1.2‖ * ‖v - p‖ :=
        real_inner_le_norm _ _
      _ = ‖v - p‖ := by rw [hnorm, one_mul]
  have hdecomp : v - q.1.1 = (v - p) + (p - q.1.1) := by abel
  have hsum : Metric.infDist v Z =
      ⟪q.1.2, v - p⟫_ℝ + ⟪q.1.2, p - q.1.1⟫_ℝ := by
    rw [← hvalue, hdecomp, inner_add_right]
  have hinner_ge : Metric.infDist v Z ≤ ⟪q.1.2, v - p⟫_ℝ := by
    linarith
  have hinner_le_dist : ⟪q.1.2, v - p⟫_ℝ ≤ Metric.infDist v Z := by
    rw [← hpdist]
    exact hinner_le
  have hqpeq : ⟪q.1.2, p - q.1.1⟫_ℝ = 0 := by
    linarith
  have hsupport_p : ∀ z : E, z ∈ Z →
      ⟪q.1.2, z - p⟫_ℝ ≤ 0 := by
    intro z hz
    have hqz := convexSupportPair_support Z q z hz
    rw [inner_sub_right] at hqz ⊢
    rw [inner_sub_right] at hqpeq
    linarith
  have hψp : ⟪q.1.2, ψ p⟫_ℝ ≤ 0 := by
    have hφ := support_functional_nonpos_of_vectorFieldPreservesConvexSet
      hpres hp (innerSL ℝ q.1.2) (by
        intro z hz
        have hz' := hsupport_p z hz
        have hz'' : ⟪q.1.2, z⟫_ℝ - ⟪q.1.2, p⟫_ℝ ≤ 0 := by
          simpa [inner_sub_right] using hz'
        have hz''' : ⟪q.1.2, z⟫_ℝ ≤ ⟪q.1.2, p⟫_ℝ :=
          sub_nonpos.mp hz''
        simpa [innerSL_apply_apply] using hz''')
    simpa [innerSL_apply_apply] using hφ
  have hdistψ := hψ.dist_le_mul v p
  have hnormψ : ‖ψ v - ψ p‖ ≤ (K : ℝ) * Metric.infDist v Z := by
    simpa [dist_eq_norm, hpdist] using hdistψ
  have hinnerψ : ⟪q.1.2, ψ v - ψ p⟫_ℝ ≤ ‖ψ v - ψ p‖ := by
    calc
      ⟪q.1.2, ψ v - ψ p⟫_ℝ ≤ ‖q.1.2‖ * ‖ψ v - ψ p‖ :=
        real_inner_le_norm _ _
      _ = ‖ψ v - ψ p‖ := by rw [hnorm, one_mul]
  rw [inner_sub_right] at hinnerψ
  linarith

end Reaction

/-! ### The compact constant-fiber tensor principle -/

section TensorPrinciple

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- `ConvexSupportPair` is a reducible alias for a subtype, but its carrier
-- predicate is opaque to typeclass search at a theorem binder.  Register the
-- canonical subtype topology once so the regularity hypotheses below use the
-- same topology as `compactSpace_convexSupportPair`.
local instance supportPairTopology (Z : Set E) : TopologicalSpace (ConvexSupportPair Z) :=
  inferInstanceAs (TopologicalSpace {q : E × E // q ∈ convexSupportPairSet Z})

/-- Scalarization of a field by a support pair.  The `none` parameter is the
constant-zero competitor; it makes the envelope nonnegative at every time and
handles first contact with the carrier without a nonsmooth positive-part
operation.
-/
def hamiltonSupportValue (Z : Set E) (u : X → ℝ → E)
    (x : X) (q : Unit ⊕ ConvexSupportPair Z) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr q => ⟪q.1.2, u x t - q.1.1⟫_ℝ

/-- Time derivative of `hamiltonSupportValue` supplied by a reaction-diffusion
operator `L` and reaction field `ψ`.
-/
def hamiltonSupportDerivative (Z : Set E) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (x : X) (q : Unit ⊕ ConvexSupportPair Z) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr q =>
      ⟪q.1.2, L t (fun y : X => u y t) x + ψ (u x t)⟫_ℝ

/-- Product-parameter form of `hamiltonSupportValue`, with the spatial point
and support parameter grouped as the compact-family index. -/
def hamiltonSupportValueFamily (Z : Set E) (u : X → ℝ → E)
    (xp : X × (Unit ⊕ ConvexSupportPair Z)) (t : ℝ) : ℝ :=
  hamiltonSupportValue Z u xp.1 xp.2 t

/-- Product-parameter form of `hamiltonSupportDerivative`. -/
def hamiltonSupportDerivativeFamily (Z : Set E) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (xp : X × (Unit ⊕ ConvexSupportPair Z)) (t : ℝ) : ℝ :=
  hamiltonSupportDerivative Z u L ψ xp.1 xp.2 t

/-- The scalarized support value has the derivative dictated by the vector
reaction-diffusion equation. -/
theorem hasDerivAt_hamiltonSupportValue
    {Z : Set E} {u : X → ℝ → E}
    {L : ℝ → (X → E) → X → E} {ψ : E → E}
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (x : X) (q : Unit ⊕ ConvexSupportPair Z) (s : ℝ) :
    HasDerivAt (hamiltonSupportValue Z u x q)
      (hamiltonSupportDerivative Z u L ψ x q s) s := by
  cases q with
  | inl _ =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) s
      exact hasDerivAt_const (x := s) (c := (0 : ℝ))
  | inr q =>
      have hconst : HasDerivAt (fun _ : ℝ => q.1.2) 0 s :=
        hasDerivAt_const (x := s) (c := q.1.2)
      have hsub : HasDerivAt (fun r : ℝ => u x r - q.1.1)
          (L s (fun y : X => u y s) x + ψ (u x s)) s := by
        simpa using (hpde x s).sub_const q.1.1
      change HasDerivAt (fun r : ℝ => ⟪q.1.2, u x r - q.1.1⟫_ℝ)
        ⟪q.1.2, L s (fun y : X => u y s) x + ψ (u x s)⟫_ℝ s
      simpa using hconst.inner ℝ hsub

/-!
The theorem below is the source-faithful compact-carrier global maximum
principle.  `hF` and `hF'` expose the joint regularity needed by the scalar
envelope lemma; in a geometric application they come from the smooth field,
the support-pair projections, and the chosen connection chart.  The diffusion
condition itself is stated for every spatial field and every normal, rather
than being tailored to this particular solution.
-/
theorem hamilton_tensor_maximum_principle_compact
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
    {a b : ℝ}
    (hF : Continuous ↿(hamiltonSupportValueFamily Z u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamily Z u L ψ))
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (hinit : ∀ x : X, u x a ∈ Z) :
    ∀ x : X, ∀ t ∈ Icc a b, u x t ∈ Z := by
  -- The support-pair type is compact because the carrier is compact.  The
  -- option type adds the zero competitor and is compact/nonempty outright.
  letI : CompactSpace (ConvexSupportPair Z) :=
    compactSpace_convexSupportPair Z hZcompact
  let A := X × (Unit ⊕ ConvexSupportPair Z)
  letI : TopologicalSpace A :=
    inferInstanceAs (TopologicalSpace (X × (Unit ⊕ ConvexSupportPair Z)))
  letI : CompactSpace A :=
    inferInstanceAs (CompactSpace (X × (Unit ⊕ ConvexSupportPair Z)))
  letI : Nonempty A :=
    inferInstanceAs (Nonempty (X × (Unit ⊕ ConvexSupportPair Z)))
  let F : A → ℝ → ℝ := hamiltonSupportValueFamily Z u
  let F' : A → ℝ → ℝ := hamiltonSupportDerivativeFamily Z u L ψ
  have hderiv : ∀ q : A, ∀ s ∈ Ioo a b,
      HasDerivAt (F q) (F' q s) s := by
    intro q s hs
    change HasDerivAt (hamiltonSupportValue Z u q.1 q.2)
      (hamiltonSupportDerivative Z u L ψ q.1 q.2 s) s
    exact hasDerivAt_hamiltonSupportValue hpde q.1 q.2 s
  have hinitF : (⨆ q : A, F q a) ≤ 0 := by
    apply ciSup_le
    rintro ⟨x, o⟩
    cases ho : o with
    | inl _ => simp [F, hamiltonSupportValueFamily, hamiltonSupportValue, ho]
    | inr p =>
        have hmem := hinit x
        have hnonpos := convexSupportPair_eval_nonpos Z p (u x a) hmem
        simpa [F, hamiltonSupportValueFamily, hamiltonSupportValue, ho] using hnonpos
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
          simp [F, hamiltonSupportValueFamily, hamiltonSupportValue]
        have hUzero : (⨆ r : A, F r t) = 0 := by
          rw [hzero'] at hqmax'
          exact hqmax'.symm
        change (0 : ℝ) ≤ (K : ℝ) * (⨆ r : A, F r t)
        rw [hUzero]
        simp
    | inr p =>
        let v := u x t
        have hqmax' : F (x, Sum.inr p) t = (⨆ r : A, F r t) := by
          simpa [ho] using hqmax
        have hq_le_dist : F (x, Sum.inr p) t ≤ Metric.infDist v Z := by
          have hpval := convexSupportPair_eval_le_infDist Z hZne hZclosed hZconv p v
          simpa [F, hamiltonSupportValueFamily, hamiltonSupportValue, v] using hpval
        have hUle_dist : (⨆ r : A, F r t) ≤ Metric.infDist v Z := by
          rw [← hqmax']
          exact hq_le_dist
        have hUge0 : (0 : ℝ) ≤ (⨆ r : A, F r t) := by
          have hzero : F (x, Sum.inl ()) t ≤ (⨆ r : A, F r t) :=
            le_ciSup (bddAbove_range_family hF t) (x, Sum.inl ())
          simpa [F, hamiltonSupportValueFamily, hamiltonSupportValue] using hzero
        have hUeq : (⨆ r : A, F r t) = Metric.infDist v Z := by
          by_cases hv : v ∈ Z
          · have hz : Metric.infDist v Z = 0 := Metric.infDist_zero_of_mem hv
            linarith
          · let pe := exteriorSupportPair Z hZne hZclosed hZconv v hv
            have hpeval : F (x, Sum.inr pe) t = Metric.infDist v Z := by
              simpa [F, hamiltonSupportValueFamily, hamiltonSupportValue, v] using
                exteriorSupportPair_eval_eq_infDist Z hZne hZclosed hZconv v hv
            have hle : F (x, Sum.inr pe) t ≤ (⨆ r : A, F r t) :=
              le_ciSup (bddAbove_range_family hF t) (x, Sum.inr pe)
            linarith
        have hpactive :
            ⟪p.1.2, v - p.1.1⟫_ℝ = Metric.infDist v Z := by
          rw [hUeq] at hqmax'
          simpa [F, hamiltonSupportValueFamily, hamiltonSupportValue, v] using hqmax'
        have hreac := convexSupportPair_reaction_bound hZne hZclosed hZconv
          hpres hψ v p hpactive
        have hspatial : IsMaxOn (fun y : X => ⟪p.1.2, u y t⟫_ℝ)
            (univ : Set X) x := by
          intro y hy
          have hle : F (y, Sum.inr p) t ≤ (⨆ r : A, F r t) :=
            le_ciSup (bddAbove_range_family hF t) (y, Sum.inr p)
          have hactive : F (x, Sum.inr p) t = (⨆ r : A, F r t) := by
            simpa [ho] using hqmax
          change ⟪p.1.2, u x t - p.1.1⟫_ℝ = (⨆ r : A, F r t) at hactive
          change ⟪p.1.2, u y t - p.1.1⟫_ℝ ≤ (⨆ r : A, F r t) at hle
          rw [inner_sub_right] at hactive hle
          have hxy :
              ⟪p.1.2, u y t⟫_ℝ - ⟪p.1.2, p.1.1⟫_ℝ ≤
                ⟪p.1.2, u x t⟫_ℝ - ⟪p.1.2, p.1.1⟫_ℝ :=
            hle.trans_eq hactive.symm
          exact (sub_le_sub_iff_right _).mp hxy
        have hdiff := hL t (fun y : X => u y t) p.1.2 x hspatial
        have hsum := add_le_add hdiff hreac
        change (⟪p.1.2, L t (fun y : X => u y t) x + ψ (u x t)⟫_ℝ) ≤
          (K : ℝ) * (⨆ r : A, F r t)
        rw [inner_add_right]
        simpa [hUeq] using hsum
  have henv : ∀ t ∈ Icc a b, (⨆ q : A, F q t) ≤ 0 :=
    hamilton_envelope_nonpositive hF hF' hderiv hmax hinitF
  intro x t ht
  by_contra hv
  let p := exteriorSupportPair Z hZne hZclosed hZconv (u x t) hv
  have hpos : 0 < F (x, Sum.inr p) t := by
    have hd : 0 < Metric.infDist (u x t) Z :=
      (hZclosed.notMem_iff_infDist_pos hZne).mp hv
    have heq := exteriorSupportPair_eval_eq_infDist Z hZne hZclosed hZconv
      (u x t) hv
    have heq' : F (x, Sum.inr p) t = Metric.infDist (u x t) Z := by
      simpa [F, hamiltonSupportValueFamily, hamiltonSupportValue, p] using heq
    rw [heq']
    exact hd
  have hle : F (x, Sum.inr p) t ≤ (⨆ q : A, F q t) :=
    le_ciSup (bddAbove_range_family hF t) (x, Sum.inr p)
  have hUpos : 0 < (⨆ q : A, F q t) := lt_of_lt_of_le hpos hle
  exact (not_lt_of_ge (henv t ht)) hUpos

end TensorPrinciple

/-! ### Compact support families (the unbounded-carrier adapter) -/

section CompactSupportFamily

variable {X E P : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Scalarization by a compact family of support pairs.  The `Unit` branch is
the constant-zero competitor used to detect first contact with the carrier. -/
def hamiltonSupportValueOn (Z : Set E) (support : P → ConvexSupportPair Z)
    (u : X → ℝ → E) (x : X) (q : Unit ⊕ P) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr p =>
      ⟪(support p).1.2, u x t - (support p).1.1⟫_ℝ

/-- Time derivative of the compact-support scalarization. -/
def hamiltonSupportDerivativeOn (Z : Set E) (support : P → ConvexSupportPair Z)
    (u : X → ℝ → E) (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (x : X) (q : Unit ⊕ P) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr p =>
      ⟪(support p).1.2,
        L t (fun y : X => u y t) x + ψ (u x t)⟫_ℝ

def hamiltonSupportValueOnFamily (Z : Set E) (support : P → ConvexSupportPair Z)
    (u : X → ℝ → E) (xp : X × (Unit ⊕ P)) (t : ℝ) : ℝ :=
  hamiltonSupportValueOn Z support u xp.1 xp.2 t

def hamiltonSupportDerivativeOnFamily (Z : Set E)
    (support : P → ConvexSupportPair Z) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (xp : X × (Unit ⊕ P)) (t : ℝ) : ℝ :=
  hamiltonSupportDerivativeOn Z support u L ψ xp.1 xp.2 t

theorem hasDerivAt_hamiltonSupportValueOn
    {Z : Set E} (support : P → ConvexSupportPair Z)
    {u : X → ℝ → E} {L : ℝ → (X → E) → X → E} {ψ : E → E}
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (x : X) (q : Unit ⊕ P) (s : ℝ) :
    HasDerivAt (hamiltonSupportValueOn Z support u x q)
      (hamiltonSupportDerivativeOn Z support u L ψ x q s) s := by
  cases q with
  | inl _ =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) s
      exact hasDerivAt_const (x := s) (c := (0 : ℝ))
  | inr p =>
      let q' : ConvexSupportPair Z := support p
      have hconst : HasDerivAt (fun _ : ℝ => q'.1.2) 0 s :=
        hasDerivAt_const (x := s) (c := q'.1.2)
      have hsub : HasDerivAt (fun r : ℝ => u x r - q'.1.1)
          (L s (fun y : X => u y s) x + ψ (u x s)) s := by
        simpa using (hpde x s).sub_const q'.1.1
      change HasDerivAt (fun r : ℝ => ⟪q'.1.2, u x r - q'.1.1⟫_ℝ)
        ⟪q'.1.2, L s (fun y : X => u y s) x + ψ (u x s)⟫_ℝ s
      simpa [q'] using hconst.inner ℝ hsub

/-!
The support-family theorem is the precise finite-dimensional barrier statement
used by the unbounded-carrier wrapper.  It requires only compactness of the
chosen support parameters and an attainment witness for every exterior point;
the carrier itself need not be compact.  The predicate `Reach` is an explicit
externally established side condition for the trajectory; this lemma does not
derive it from the conclusion it proves.
-/
theorem hamilton_tensor_maximum_principle_compact_support
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z)
    (support : P → ConvexSupportPair Z)
    {Reach : E → Prop}
    (hattain : ∀ v : E, Reach v → v ∉ Z → ∃ p : P,
      ⟪(support p).1.2, v - (support p).1.1⟫_ℝ = Metric.infDist v Z)
    {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    (hψ : LipschitzWith K ψ)
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u : X → ℝ → E) {a b : ℝ}
    (hF : Continuous ↿(hamiltonSupportValueOnFamily Z support u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeOnFamily Z support u L ψ))
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (hinit : ∀ x : X, u x a ∈ Z)
    (hreach_u : ∀ x : X, ∀ t : ℝ, t ∈ Icc a b → Reach (u x t)) :
    ∀ x : X, ∀ t ∈ Icc a b, u x t ∈ Z := by
  let A := X × (Unit ⊕ P)
  letI : TopologicalSpace A :=
    inferInstanceAs (TopologicalSpace (X × (Unit ⊕ P)))
  letI : CompactSpace A :=
    inferInstanceAs (CompactSpace (X × (Unit ⊕ P)))
  letI : Nonempty A :=
    inferInstanceAs (Nonempty (X × (Unit ⊕ P)))
  let F : A → ℝ → ℝ := hamiltonSupportValueOnFamily Z support u
  let F' : A → ℝ → ℝ := hamiltonSupportDerivativeOnFamily Z support u L ψ
  have hderiv : ∀ q : A, ∀ s ∈ Ioo a b,
      HasDerivAt (F q) (F' q s) s := by
    intro q s hs
    change HasDerivAt (hamiltonSupportValueOn Z support u q.1 q.2)
      (hamiltonSupportDerivativeOn Z support u L ψ q.1 q.2 s) s
    exact hasDerivAt_hamiltonSupportValueOn support hpde q.1 q.2 s
  have hinitF : (⨆ q : A, F q a) ≤ 0 := by
    apply ciSup_le
    rintro ⟨x, o⟩
    cases ho : o with
    | inl _ => simp [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn]
    | inr p =>
        have hnonpos := convexSupportPair_eval_nonpos Z (support p) (u x a) (hinit x)
        simpa [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn] using hnonpos
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
          simp [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn]
        have hUzero : (⨆ r : A, F r t) = 0 := by
          rw [hzero'] at hqmax'
          exact hqmax'.symm
        change (0 : ℝ) ≤ (K : ℝ) * (⨆ r : A, F r t)
        rw [hUzero]
        simp
    | inr p =>
        let v := u x t
        let q' : ConvexSupportPair Z := support p
        have hqmax' : F (x, Sum.inr p) t = (⨆ r : A, F r t) := by
          simpa [ho] using hqmax
        have hq_le_dist : F (x, Sum.inr p) t ≤ Metric.infDist v Z := by
          have hpval := convexSupportPair_eval_le_infDist Z hZne hZclosed hZconv q' v
          simpa [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn, q', v] using hpval
        have hUle_dist : (⨆ r : A, F r t) ≤ Metric.infDist v Z := by
          rw [← hqmax']
          exact hq_le_dist
        have hUge0 : (0 : ℝ) ≤ (⨆ r : A, F r t) := by
          have hzero : F (x, Sum.inl ()) t ≤ (⨆ r : A, F r t) :=
            le_ciSup (bddAbove_range_family hF t) (x, Sum.inl ())
          simpa [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn] using hzero
        have hUeq : (⨆ r : A, F r t) = Metric.infDist v Z := by
          by_cases hv : v ∈ Z
          · have hz : Metric.infDist v Z = 0 := Metric.infDist_zero_of_mem hv
            linarith
          · have hreach : Reach v := hreach_u x t ⟨ht.1, le_of_lt ht.2⟩
            obtain ⟨pe, hpe⟩ := hattain v hreach hv
            have hpeval : F (x, Sum.inr pe) t = Metric.infDist v Z := by
              simpa [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn, v] using hpe
            have hle : F (x, Sum.inr pe) t ≤ (⨆ r : A, F r t) :=
              le_ciSup (bddAbove_range_family hF t) (x, Sum.inr pe)
            linarith
        have hpactive :
            ⟪q'.1.2, v - q'.1.1⟫_ℝ = Metric.infDist v Z := by
          rw [hUeq] at hqmax'
          simpa [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn, q', v] using hqmax'
        have hreac := convexSupportPair_reaction_bound hZne hZclosed hZconv
          hpres hψ v q' hpactive
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
        change (⟪q'.1.2,
          L t (fun y : X => u y t) x + ψ (u x t)⟫_ℝ) ≤
          (K : ℝ) * (⨆ r : A, F r t)
        rw [inner_add_right]
        simpa [hUeq] using hsum
  have henv : ∀ t ∈ Icc a b, (⨆ q : A, F q t) ≤ 0 :=
    hamilton_envelope_nonpositive hF hF' hderiv hmax hinitF
  intro x t ht
  by_contra hv
  obtain ⟨pe, hpe⟩ := hattain (u x t) (hreach_u x t ht) hv
  have hpos : 0 < F (x, Sum.inr pe) t := by
    have hd : 0 < Metric.infDist (u x t) Z :=
      (hZclosed.notMem_iff_infDist_pos hZne).mp hv
    have heq' : F (x, Sum.inr pe) t = Metric.infDist (u x t) Z := by
      simpa [F, hamiltonSupportValueOnFamily, hamiltonSupportValueOn] using hpe
    rw [heq']
    exact hd
  have hle : F (x, Sum.inr pe) t ≤ (⨆ q : A, F q t) :=
    le_ciSup (bddAbove_range_family hF t) (x, Sum.inr pe)
  have hUpos : 0 < (⨆ q : A, F q t) := lt_of_lt_of_le hpos hle
  exact (not_lt_of_ge (henv t ht)) hUpos

end CompactSupportFamily

end MorganTianLib
