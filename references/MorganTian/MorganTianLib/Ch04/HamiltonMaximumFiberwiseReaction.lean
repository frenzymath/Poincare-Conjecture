import MorganTianLib.Ch04.HamiltonMaximumBounded

/-!
# Morgan--Tian Ch. 4 - Hamilton maximum principle with a spatial reaction

This module extends the finite-dimensional compact-support and bounded-carrier
barriers to a reaction field `psi x : E -> E` that may vary with the spatial
parameter.  The preservation and Lipschitz hypotheses are pointwise in `x`,
with one common Lipschitz constant.  The scalarized regularity and the
reaction-diffusion equation remain explicit hypotheses, so this file does not
assert a missing bundle or parallel-frame construction.
-/

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

section FiberwiseReaction

variable {X E P : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! Direct support-pair notation (without a compact parameter type). -/

/-- Time derivative scalarization on all support pairs for a spatial reaction. -/
def hamiltonSupportDerivativeFiberwise (Z : Set E) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : X → E → E)
    (x : X) (q : Unit ⊕ ConvexSupportPair Z) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr q =>
      ⟪q.1.2, L t (fun y : X => u y t) x + ψ x (u x t)⟫_ℝ

/-- Product-parameter form of the direct fiberwise derivative scalarization. -/
def hamiltonSupportDerivativeFamilyFiberwise (Z : Set E) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : X → E → E)
    (xp : X × (Unit ⊕ ConvexSupportPair Z)) (t : ℝ) : ℝ :=
  hamiltonSupportDerivativeFiberwise Z u L ψ xp.1 xp.2 t

theorem hasDerivAt_hamiltonSupportValueFiberwise
    {Z : Set E} {u : X → ℝ → E} {L : ℝ → (X → E) → X → E}
    {ψ : X → E → E}
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ x (u x s)) s)
    (x : X) (q : Unit ⊕ ConvexSupportPair Z) (s : ℝ) :
    HasDerivAt (hamiltonSupportValue Z u x q)
      (hamiltonSupportDerivativeFiberwise Z u L ψ x q s) s := by
  cases q with
  | inl _ =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) s
      exact hasDerivAt_const (x := s) (c := (0 : ℝ))
  | inr q =>
      change HasDerivAt (fun r : ℝ => ⟪q.1.2, u x r - q.1.1⟫_ℝ)
        ⟪q.1.2, L s (fun y : X => u y s) x + ψ x (u x s)⟫_ℝ s
      have hsub := (hpde x s).sub_const q.1.1
      simpa using (hasDerivAt_const (x := s) (c := q.1.2)).inner ℝ hsub

/-! The compact-support scalarization with a reaction depending on `x`. -/

/-- Time derivative scalarization for a spatially varying reaction. -/
def hamiltonSupportDerivativeOnFiberwise (Z : Set E)
    (support : P → ConvexSupportPair Z) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : X → E → E)
    (x : X) (q : Unit ⊕ P) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr p =>
      ⟪(support p).1.2,
        L t (fun y : X => u y t) x + ψ x (u x t)⟫_ℝ

/-- Product-parameter form of the fiberwise derivative scalarization. -/
def hamiltonSupportDerivativeOnFamilyFiberwise (Z : Set E)
    (support : P → ConvexSupportPair Z) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : X → E → E)
    (xp : X × (Unit ⊕ P)) (t : ℝ) : ℝ :=
  hamiltonSupportDerivativeOnFiberwise Z support u L ψ xp.1 xp.2 t

theorem hasDerivAt_hamiltonSupportValueOnFiberwise
    {Z : Set E} (support : P → ConvexSupportPair Z)
    {u : X → ℝ → E} {L : ℝ → (X → E) → X → E} {ψ : X → E → E}
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ x (u x s)) s)
    (x : X) (q : Unit ⊕ P) (s : ℝ) :
    HasDerivAt (hamiltonSupportValueOn Z support u x q)
      (hamiltonSupportDerivativeOnFiberwise Z support u L ψ x q s) s := by
  cases q with
  | inl _ =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) s
      exact hasDerivAt_const (x := s) (c := (0 : ℝ))
  | inr p =>
      let q' : ConvexSupportPair Z := support p
      have hconst : HasDerivAt (fun _ : ℝ => q'.1.2) 0 s :=
        hasDerivAt_const (x := s) (c := q'.1.2)
      have hsub : HasDerivAt (fun r : ℝ => u x r - q'.1.1)
          (L s (fun y : X => u y s) x + ψ x (u x s)) s := by
        simpa using (hpde x s).sub_const q'.1.1
      change HasDerivAt (fun r : ℝ => ⟪q'.1.2, u x r - q'.1.1⟫_ℝ)
        ⟪q'.1.2, L s (fun y : X => u y s) x + ψ x (u x s)⟫_ℝ s
      simpa [q'] using hconst.inner ℝ hsub

/-!
The compact-support theorem below is the same finite-dimensional barrier as
`hamilton_tensor_maximum_principle_compact_support`, with the reaction estimate
applied to `ψ x` at the spatial maximizer.  `Reach` is an explicit trajectory
side condition, as in the single-reaction theorem.
-/
theorem hamilton_tensor_maximum_principle_compact_support_fiberwise
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z)
    (support : P → ConvexSupportPair Z)
    {Reach : E → Prop}
    (hattain : ∀ v : E, Reach v → v ∉ Z → ∃ p : P,
      ⟪(support p).1.2, v - (support p).1.1⟫_ℝ = Metric.infDist v Z)
    {ψ : X → E → E} {K : ℝ≥0}
    (hpres : ∀ x : X, vectorFieldPreservesConvexSet Z (ψ x))
    (hψ : ∀ x : X, LipschitzWith K (ψ x))
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u : X → ℝ → E) {a b : ℝ}
    (hF : Continuous ↿(hamiltonSupportValueOnFamily Z support u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeOnFamilyFiberwise
      Z support u L ψ))
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ x (u x s)) s)
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
  let F' : A → ℝ → ℝ := hamiltonSupportDerivativeOnFamilyFiberwise Z support u L ψ
  have hderiv : ∀ q : A, ∀ s ∈ Ioo a b,
      HasDerivAt (F q) (F' q s) s := by
    intro q s hs
    change HasDerivAt (hamiltonSupportValueOn Z support u q.1 q.2)
      (hamiltonSupportDerivativeOnFiberwise Z support u L ψ q.1 q.2 s) s
    exact hasDerivAt_hamiltonSupportValueOnFiberwise support hpde q.1 q.2 s
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
          (hpres x) (hψ x) v q' hpactive
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
          L t (fun y : X => u y t) x + ψ x (u x t)⟫_ℝ) ≤
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

end FiberwiseReaction

section BoundedFiberwiseReaction

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! Bounded-carrier adapter for the spatial reaction theorem. -/

theorem hamilton_tensor_maximum_principle_bounded_fiberwise
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : X → E → E} {K : ℝ≥0}
    (hpres : ∀ x : X, vectorFieldPreservesConvexSet Z (ψ x))
    (hψ : ∀ x : X, LipschitzWith K (ψ x))
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u : X → ℝ → E) {a b : ℝ}
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ x (u x s)) s)
    {B : ℝ} (hbound : ∀ x t, t ∈ Icc a b → ‖u x t‖ ≤ B) (hB0 : 0 ≤ B)
    (hF : Continuous ↿(hamiltonSupportValueFamily Z u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamilyFiberwise Z u L ψ))
    (hinit : ∀ x : X, u x a ∈ Z) :
    ∀ x : X, ∀ t ∈ Icc a b, u x t ∈ Z := by
  let z₀ : E := Classical.choose hZne
  have hz₀ : z₀ ∈ Z := Classical.choose_spec hZne
  let R : ℝ := ‖z₀‖ + 2 * B
  letI : CompactSpace (BoundedConvexSupportPair Z R) :=
    compactSpace_boundedConvexSupportPair Z R hZclosed
  let support : BoundedConvexSupportPair Z R → ConvexSupportPair Z :=
    boundedPairSupport Z R
  have hattain : ∀ v : E, ‖v‖ ≤ B → v ∉ Z →
      ∃ p : BoundedConvexSupportPair Z R,
        ⟪(support p).1.2, v - (support p).1.1⟫_ℝ = Metric.infDist v Z := by
    intro v hvnorm hv
    let pe := exteriorSupportPair Z hZne hZclosed hZconv v hv
    have hpbound : ‖pe.1.1‖ ≤ R := by
      have hproj := convexProjection_norm_le_of_norm_le hZne hZclosed hZconv
        z₀ hz₀ hB0 v hvnorm
      have heq : pe.1.1 = convexProjection Z hZne hZclosed hZconv v := by
        simp [pe, exteriorSupportPair, convexProjection_unit_support]
      rw [heq]
      exact hproj
    let pb : BoundedConvexSupportPair Z R := ⟨pe.1, ⟨pe.2, hpbound⟩⟩
    refine ⟨pb, ?_⟩
    simpa [support, pb, boundedPairSupport] using
      exteriorSupportPair_eval_eq_infDist Z hZne hZclosed hZconv v hv
  let A := X × (Unit ⊕ BoundedConvexSupportPair Z R)
  let mapA : A → X × (Unit ⊕ ConvexSupportPair Z) := fun xp =>
    (xp.1, Sum.elim (fun z => Sum.inl z)
      (fun q => Sum.inr (support q)) xp.2)
  have hmapA : Continuous mapA := by
    have hs : Continuous (Sum.elim (fun z : Unit => Sum.inl z)
        (fun q : BoundedConvexSupportPair Z R => Sum.inr (support q))) :=
      continuous_inl.sumElim (continuous_inr.comp
        ((continuous_subtype_val : Continuous
          (fun q : BoundedConvexSupportPair Z R => q.1)).subtype_mk
            (fun q => q.2.1)))
    exact continuous_fst.prodMk (hs.comp continuous_snd)
  have hFb : Continuous ↿(hamiltonSupportValueOnFamily Z support u) := by
    have hmp : Continuous (fun pt : A × ℝ => (mapA pt.1, pt.2)) :=
      (hmapA.comp continuous_fst).prodMk continuous_snd
    have hh := hF.comp hmp
    convert hh using 1
    funext pt
    rcases pt with ⟨⟨x, o⟩, t⟩
    cases o <;> rfl
  have hFb' : Continuous ↿(hamiltonSupportDerivativeOnFamilyFiberwise
      Z support u L ψ) := by
    have hmp : Continuous (fun pt : A × ℝ => (mapA pt.1, pt.2)) :=
      (hmapA.comp continuous_fst).prodMk continuous_snd
    have hh := hF'.comp hmp
    convert hh using 1
    funext pt
    rcases pt with ⟨⟨x, o⟩, t⟩
    cases o <;> rfl
  apply hamilton_tensor_maximum_principle_compact_support_fiberwise
    (P := BoundedConvexSupportPair Z R) (Reach := fun v => ‖v‖ ≤ B)
    hZne hZclosed hZconv support hattain hpres hψ L hL u
  · exact hFb
  · exact hFb'
  · exact hpde
  · exact hinit
  · intro x t ht
    exact hbound x t ht

end BoundedFiberwiseReaction

end MorganTianLib
