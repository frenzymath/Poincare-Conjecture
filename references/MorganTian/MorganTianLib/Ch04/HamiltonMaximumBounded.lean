import MorganTianLib.Ch04.HamiltonMaximumCore
import Mathlib.Topology.Constructions.SumProd

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {X : Type*}

/-! A compact truncation of the support-pair carrier. -/

def boundedConvexSupportPairSet (Z : Set E) (R : ℝ) : Set (E × E) :=
  convexSupportPairSet Z ∩ {q | ‖q.1‖ ≤ R}

abbrev BoundedConvexSupportPair (Z : Set E) (R : ℝ) :=
  {q : E × E // q ∈ boundedConvexSupportPairSet Z R}

def boundedPairSupport (Z : Set E) (R : ℝ)
    (q : BoundedConvexSupportPair Z R) : ConvexSupportPair Z :=
  ⟨q.1, q.2.1⟩

@[simp] theorem boundedPairSupport_val (Z : Set E) (R : ℝ)
    (q : BoundedConvexSupportPair Z R) : (boundedPairSupport Z R q).1 = q.1 := rfl

theorem boundedPairSupport_norm_le (Z : Set E) (R : ℝ)
    (q : BoundedConvexSupportPair Z R) : ‖(boundedPairSupport Z R q).1.1‖ ≤ R :=
  q.2.2

omit [FiniteDimensional ℝ E] in
/-- The inclusion of bounded support pairs into all convex support pairs is continuous. -/
theorem continuous_boundedPairSupport (Z : Set E) (R : ℝ) :
    Continuous (boundedPairSupport Z R) :=
  continuous_subtype_val.subtype_mk (fun q => q.2.1)

theorem isCompact_boundedConvexSupportPairSet (Z : Set E) (R : ℝ)
    (hZclosed : IsClosed Z) : IsCompact (boundedConvexSupportPairSet Z R) := by
  have hZball : IsCompact (Z ∩ Metric.closedBall (0 : E) R) := by
    apply (isCompact_closedBall (0 : E) R).of_isClosed_subset
      (hZclosed.inter Metric.isClosed_closedBall)
    intro z hz
    exact hz.2
  have hprod : IsCompact
      ((Z ∩ Metric.closedBall (0 : E) R) ×ˢ Metric.closedBall (0 : E) 1) :=
    hZball.prod (isCompact_closedBall (0 : E) 1)
  apply hprod.of_isClosed_subset
    ((isClosed_convexSupportPairSet Z hZclosed).inter
      (isClosed_le (continuous_norm.comp continuous_fst) continuous_const))
  intro q hq
  refine ⟨⟨hq.1.1, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hq.2
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq hq.1.2.1

theorem compactSpace_boundedConvexSupportPair (Z : Set E) (R : ℝ)
    (hZclosed : IsClosed Z) : CompactSpace (BoundedConvexSupportPair Z R) :=
  isCompact_iff_compactSpace.mp (isCompact_boundedConvexSupportPairSet Z R hZclosed)

/-! Bounded scalarization families. -/

def hamiltonSupportValueBounded (Z : Set E) (R : ℝ) (u : X → ℝ → E)
    (x : X) (q : Unit ⊕ BoundedConvexSupportPair Z R) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr q => ⟪q.1.2, u x t - q.1.1⟫_ℝ

def hamiltonSupportDerivativeBounded (Z : Set E) (R : ℝ) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (x : X) (q : Unit ⊕ BoundedConvexSupportPair Z R) (t : ℝ) : ℝ :=
  match q with
  | Sum.inl _ => 0
  | Sum.inr q => ⟪q.1.2, L t (fun y : X => u y t) x + ψ (u x t)⟫_ℝ

def hamiltonSupportValueFamilyBounded (Z : Set E) (R : ℝ) (u : X → ℝ → E)
    (xp : X × (Unit ⊕ BoundedConvexSupportPair Z R)) (t : ℝ) : ℝ :=
  hamiltonSupportValueBounded Z R u xp.1 xp.2 t

def hamiltonSupportDerivativeFamilyBounded (Z : Set E) (R : ℝ) (u : X → ℝ → E)
    (L : ℝ → (X → E) → X → E) (ψ : E → E)
    (xp : X × (Unit ⊕ BoundedConvexSupportPair Z R)) (t : ℝ) : ℝ :=
  hamiltonSupportDerivativeBounded Z R u L ψ xp.1 xp.2 t

theorem hasDerivAt_hamiltonSupportValueBounded
    {X : Type*} [TopologicalSpace X]
    {Z : Set E} {R : ℝ} {u : X → ℝ → E}
    {L : ℝ → (X → E) → X → E} {ψ : E → E}
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (x : X) (q : Unit ⊕ BoundedConvexSupportPair Z R) (s : ℝ) :
    HasDerivAt (hamiltonSupportValueBounded Z R u x q)
      (hamiltonSupportDerivativeBounded Z R u L ψ x q s) s := by
  cases q with
  | inl _ =>
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) s
      exact hasDerivAt_const (x := s) (c := (0 : ℝ))
  | inr q =>
      change HasDerivAt (fun r : ℝ => ⟪q.1.2, u x r - q.1.1⟫_ℝ)
        ⟪q.1.2, L s (fun y : X => u y s) x + ψ (u x s)⟫_ℝ s
      have hsub := (hpde x s).sub_const q.1.1
      simpa using (hasDerivAt_const (x := s) (c := q.1.2)).inner ℝ hsub

section Principle

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

theorem convexProjection_norm_le_of_norm_le
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) (z₀ : E) (hz₀ : z₀ ∈ Z)
    {B : ℝ} (hB0 : 0 ≤ B) (v : E) (hv : ‖v‖ ≤ B) :
    ‖convexProjection Z hZne hZclosed hZconv v‖ ≤ ‖z₀‖ + 2 * B := by
  let p := convexProjection Z hZne hZclosed hZconv v
  have hdist : dist v p = Metric.infDist v Z :=
    convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v
  calc
    ‖p‖ = ‖(p - v) + v‖ := by rw [sub_add_cancel]
    _ ≤ ‖p - v‖ + ‖v‖ := norm_add_le _ _
    _ = dist v p + ‖v‖ := by simpa [dist_eq_norm, norm_sub_rev]
    _ = Metric.infDist v Z + ‖v‖ := by rw [hdist]
    _ ≤ dist v z₀ + ‖v‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right (Metric.infDist_le_dist_of_mem (s := Z) (x := v) hz₀) ‖v‖)
    _ ≤ (‖v‖ + ‖z₀‖) + ‖v‖ := by
      gcongr
      simpa [dist_eq_norm] using (norm_sub_le v z₀)
    _ ≤ ‖z₀‖ + 2 * B := by nlinarith [norm_nonneg v]

/-- An exterior point of norm at most `B` has a supporting pair attaining its distance
to a closed convex set, with support point of norm at most `‖z₀‖ + 2 * B`. -/
theorem exists_boundedConvexSupportPair_eval_eq_infDist
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) (z₀ : E) (hz₀ : z₀ ∈ Z)
    {B : ℝ} (hB0 : 0 ≤ B) (v : E) (hvnorm : ‖v‖ ≤ B) (hv : v ∉ Z) :
    ∃ q : BoundedConvexSupportPair Z (‖z₀‖ + 2 * B),
      ⟪q.1.2, v - q.1.1⟫_ℝ = Metric.infDist v Z := by
  let pe := exteriorSupportPair Z hZne hZclosed hZconv v hv
  have hpbound : ‖pe.1.1‖ ≤ ‖z₀‖ + 2 * B := by
    have hproj := convexProjection_norm_le_of_norm_le hZne hZclosed hZconv z₀ hz₀ hB0 v hvnorm
    have heq : pe.1.1 = convexProjection Z hZne hZclosed hZconv v := by
      simp [pe, exteriorSupportPair, convexProjection_unit_support]
    rw [heq]
    exact hproj
  refine ⟨⟨pe.1, ⟨pe.2, hpbound⟩⟩, ?_⟩
  exact exteriorSupportPair_eval_eq_infDist Z hZne hZclosed hZconv v hv

theorem hamilton_tensor_maximum_principle_bounded
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ) (hψ : LipschitzWith K ψ)
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u : X → ℝ → E) {a b : ℝ}
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    {B : ℝ} (hbound : ∀ x t, t ∈ Icc a b → ‖u x t‖ ≤ B) (hB0 : 0 ≤ B)
    (hF : Continuous ↿(hamiltonSupportValueFamily Z u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamily Z u L ψ))
    (hinit : ∀ x : X, u x a ∈ Z) :
    ∀ x : X, ∀ t ∈ Icc a b, u x t ∈ Z := by
  let z₀ : E := Classical.choose hZne
  have hz₀ : z₀ ∈ Z := Classical.choose_spec hZne
  let R : ℝ := ‖z₀‖ + 2 * B
  letI : CompactSpace (BoundedConvexSupportPair Z R) :=
    compactSpace_boundedConvexSupportPair Z R hZclosed
  let support : BoundedConvexSupportPair Z R → ConvexSupportPair Z :=
    boundedPairSupport Z R
  have hattain : ∀ v : E, ‖v‖ ≤ B → v ∉ Z → ∃ p : BoundedConvexSupportPair Z R,
      ⟪(support p).1.2, v - (support p).1.1⟫_ℝ = Metric.infDist v Z := by
    intro v hvnorm hv
    exact exists_boundedConvexSupportPair_eval_eq_infDist
      hZne hZclosed hZconv z₀ hz₀ hB0 v hvnorm hv
  let A := X × (Unit ⊕ BoundedConvexSupportPair Z R)
  let mapA : A → X × (Unit ⊕ ConvexSupportPair Z) := fun xp =>
    (xp.1, Sum.elim (fun z => Sum.inl z)
      (fun q => Sum.inr (support q)) xp.2)
  have hmapA : Continuous mapA := by
    have hs : Continuous (Sum.elim (fun z : Unit => Sum.inl z)
        (fun q : BoundedConvexSupportPair Z R => Sum.inr (support q))) :=
      continuous_inl.sumElim (continuous_inr.comp
        (continuous_boundedPairSupport Z R))
    exact continuous_fst.prodMk (hs.comp continuous_snd)
  have hFb : Continuous ↿(hamiltonSupportValueOnFamily Z support u) := by
    have hmp : Continuous (fun pt : A × ℝ => (mapA pt.1, pt.2)) :=
      (hmapA.comp continuous_fst).prodMk continuous_snd
    have hh := hF.comp hmp
    convert hh using 1
    funext pt
    rcases pt with ⟨⟨x, o⟩, t⟩
    cases o <;> rfl
  have hFb' : Continuous ↿(hamiltonSupportDerivativeOnFamily Z support u L ψ) := by
    have hmp : Continuous (fun pt : A × ℝ => (mapA pt.1, pt.2)) :=
      (hmapA.comp continuous_fst).prodMk continuous_snd
    have hh := hF'.comp hmp
    convert hh using 1
    funext pt
    rcases pt with ⟨⟨x, o⟩, t⟩
    cases o <;> rfl
  apply hamilton_tensor_maximum_principle_compact_support
    (P := BoundedConvexSupportPair Z R) (Reach := fun v => ‖v‖ ≤ B)
    hZne hZclosed hZconv support hattain
    hpres hψ L hL u
  · exact hFb
  · exact hFb'
  · exact hpde
  · exact hinit
  · intro x t ht
    exact hbound x t ht

end Principle
end MorganTianLib
