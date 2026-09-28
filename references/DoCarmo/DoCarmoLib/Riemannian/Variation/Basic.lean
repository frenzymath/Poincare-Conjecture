import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3

/-!
# Variations of curves

This file formalizes do Carmo Ch. 9, Definition 2.1.  A variation is a continuous
two-parameter map whose zero slice is the original curve and which is `C^1` on
the strips of a finite subdivision of the time interval.  The definition is a
predicate on an ambient map `ℝ × ℝ → M`; only its restriction to the parameter
rectangle is relevant.

The finite-subdivision formulation is shared with the project's existing
piecewise-`C^1` curve results: `n` is the number of pieces and `τ 0, ..., τ n`
are the subdivision points.  Strict inequalities encode do Carmo's genuine
subdivision rather than a weakly monotone indexing with empty pieces.
-/

open Set
open scoped ContDiff Manifold Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 9, Definition 2.1.  `f` is a variation of
`c : [0,a] → M` with variation parameter in `(-ε, ε)` when it is continuous on
that rectangle, has zero slice `c`, and is `C^1` on every strip of a finite
strict subdivision of `[0,a]`.

Functions are represented on all of `ℝ` (respectively `ℝ × ℝ`), as elsewhere
in the library; every condition is restricted to the intended intervals. -/
structure IsVariation (I : ModelWithCorners ℝ E H) (c : ℝ → M) (a ε : ℝ)
    (f : ℝ × ℝ → M) : Prop where
  epsilon_pos : 0 < ε
  continuousOn : ContinuousOn f (Ioo (-ε) ε ×ˢ Icc 0 a)
  zero_slice : ∀ t ∈ Icc 0 a, f (0, t) = c t
  piecewise_contMDiff : ∃ (n : ℕ) (τ : ℕ → ℝ),
    0 < n ∧ τ 0 = 0 ∧ τ n = a ∧
      (∀ i < n, τ i < τ (i + 1)) ∧
      ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 f
        (Ioo (-ε) ε ×ˢ Icc (τ i) (τ (i + 1)))

/-- **Math.** The order-graded form of do Carmo Ch. 9, Definition 2.1.

`IsVariation` is the legacy `C¹` curve and exponential packaging interface.
Second and higher variations need the regularity of the surface, not merely the
regularity of each named covariant field extracted from it. This structure
records the same finite subdivision at an arbitrary differentiability order
`r`; in particular, `IsSmoothVariation` is the `C∞` predicate meant by do
Carmo's convention that "differentiable" means smooth. -/
structure IsVariationOfOrder (I : ModelWithCorners ℝ E H) (r : ℕ∞ω)
    (c : ℝ → M) (a ε : ℝ) (f : ℝ × ℝ → M) : Prop where
  epsilon_pos : 0 < ε
  continuousOn : ContinuousOn f (Ioo (-ε) ε ×ˢ Icc 0 a)
  zero_slice : ∀ t ∈ Icc 0 a, f (0, t) = c t
  piecewise_contMDiff : ∃ (n : ℕ) (τ : ℕ → ℝ),
    0 < n ∧ τ 0 = 0 ∧ τ n = a ∧
      (∀ i < n, τ i < τ (i + 1)) ∧
      ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I r f
        (Ioo (-ε) ε ×ˢ Icc (τ i) (τ (i + 1)))

/-- **Math.** A variation whose restrictions to all subdivision strips are
smooth in both parameters. -/
abbrev IsSmoothVariation (I : ModelWithCorners ℝ E H) (c : ℝ → M)
    (a ε : ℝ) (f : ℝ × ℝ → M) : Prop :=
  IsVariationOfOrder I ∞ c a ε f

namespace IsVariationOfOrder

variable {r r' : ℕ∞ω} {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}

/-- **Math.** A variation may be viewed at every lower differentiability
order without changing its subdivision. -/
theorem of_le (hf : IsVariationOfOrder I r c a ε f) (hrr' : r' ≤ r) :
    IsVariationOfOrder I r' c a ε f := by
  refine ⟨hf.epsilon_pos, hf.continuousOn, hf.zero_slice, ?_⟩
  rcases hf.piecewise_contMDiff with ⟨n, τ, hn, hτ0, hτn, hτ, hpieces⟩
  exact ⟨n, τ, hn, hτ0, hτn, hτ, fun i hi ↦ (hpieces i hi).of_le hrr'⟩

/-- **Math.** Forgetting all regularity above `C¹` gives the legacy
variation predicate used by the energy API. -/
theorem isVariation (hf : IsVariationOfOrder I r c a ε f)
    (hr : (1 : ℕ∞ω) ≤ r) : IsVariation I c a ε f := by
  refine ⟨hf.epsilon_pos, hf.continuousOn, hf.zero_slice, ?_⟩
  rcases hf.piecewise_contMDiff with ⟨n, τ, hn, hτ0, hτn, hτ, hpieces⟩
  exact ⟨n, τ, hn, hτ0, hτn, hτ, fun i hi ↦ (hpieces i hi).of_le hr⟩

end IsVariationOfOrder

namespace IsVariation

variable {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}

/-- **Math.** The original curve is the zero member of a variation. -/
@[simp] theorem apply_zero (hf : IsVariation I c a ε f) {t : ℝ}
    (ht : t ∈ Icc 0 a) : f (0, t) = c t :=
  hf.zero_slice t ht

/-- **Math.** The legacy variation predicate is exactly the order-one member
of the graded hierarchy. -/
theorem isVariationOfOrderOne (hf : IsVariation I c a ε f) :
    IsVariationOfOrder I 1 c a ε f :=
  ⟨hf.epsilon_pos, hf.continuousOn, hf.zero_slice, hf.piecewise_contMDiff⟩

end IsVariation

/-- **Math.** The curve `t ↦ f(s,t)` in a variation. -/
def curve (f : ℝ × ℝ → M) (s : ℝ) : ℝ → M :=
  fun t => f (s, t)

/-- **Math.** The transversal curve `s ↦ f(s,t)` in a variation. -/
def transversal (f : ℝ × ℝ → M) (t : ℝ) : ℝ → M :=
  fun s => f (s, t)

@[simp] theorem curve_apply (f : ℝ × ℝ → M) (s t : ℝ) : curve f s t = f (s, t) :=
  rfl

@[simp] theorem transversal_apply (f : ℝ × ℝ → M) (s t : ℝ) :
    transversal f t s = f (s, t) :=
  rfl

/-- **Math.** The zero curve in the family agrees with the curve being varied. -/
theorem IsVariation.curve_zero {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}
    (hf : IsVariation I c a ε f) : Set.EqOn (curve f 0) c (Icc 0 a) :=
  fun _ ht => hf.zero_slice _ ht

/-- **Math.** Every fixed-parameter member of a variation is a piecewise-`C^1`
curve on the original time interval. -/
theorem IsVariation.curve_isPiecewiseDifferentiableCurve
    {c : ℝ → M} {a ε s : ℝ} {f : ℝ × ℝ → M}
    (hf : IsVariation I c a ε f) (hs : s ∈ Ioo (-ε) ε) :
    Geodesic.IsPiecewiseDifferentiableCurve (I := I) (curve f s) 0 a := by
  have hslice_cont : ContinuousOn (fun t : ℝ => (s, t)) (Icc (0 : ℝ) a) :=
    continuousOn_const.prodMk continuousOn_id
  have hcurve_cont : ContinuousOn (curve f s) (Icc (0 : ℝ) a) := by
    change ContinuousOn (fun t => f (s, t)) (Icc (0 : ℝ) a)
    exact hf.continuousOn.comp' hslice_cont (fun _ ht => ⟨hs, ht⟩)
  rcases hf.piecewise_contMDiff with ⟨n, τ, hn, hτ0, hτn, hτ, hpieces⟩
  refine ⟨hcurve_cont, n, τ, hn, hτ0, hτn, hτ, ?_⟩
  intro i hi
  have hslice_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) 1
      (fun t : ℝ => (s, t)) (Icc (τ i) (τ (i + 1))) :=
    contMDiffOn_const.prodMk_space contMDiffOn_id
  change ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t => f (s, t))
    (Icc (τ i) (τ (i + 1)))
  exact (hpieces i hi).comp hslice_smooth (fun _ ht => ⟨hs, ht⟩)

/-- **Math.** Every member of an order-`r` variation has the same order of
regularity on every interval of the variation's subdivision. -/
theorem IsVariationOfOrder.curve_piecewise_contMDiff
    {r : ℕ∞ω} {c : ℝ → M} {a ε s : ℝ} {f : ℝ × ℝ → M}
    (hf : IsVariationOfOrder I r c a ε f) (hs : s ∈ Ioo (-ε) ε) :
    ∃ (n : ℕ) (τ : ℕ → ℝ),
      0 < n ∧ τ 0 = 0 ∧ τ n = a ∧
        (∀ i < n, τ i < τ (i + 1)) ∧
        ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I r (curve f s)
          (Icc (τ i) (τ (i + 1))) := by
  rcases hf.piecewise_contMDiff with ⟨n, τ, hn, hτ0, hτn, hτ, hpieces⟩
  refine ⟨n, τ, hn, hτ0, hτn, hτ, ?_⟩
  intro i hi
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) r
      (fun t : ℝ => (s, t)) (Icc (τ i) (τ (i + 1))) :=
    contMDiffOn_const.prodMk_space contMDiffOn_id
  change ContMDiffOn 𝓘(ℝ, ℝ) I r (fun t => f (s, t))
    (Icc (τ i) (τ (i + 1)))
  exact (hpieces i hi).comp hslice (fun _ ht => ⟨hs, ht⟩)

/-- **Math.** Every order-`r` variation with `r ≥ 1` has piecewise
differentiable member curves. -/
theorem IsVariationOfOrder.curve_isPiecewiseDifferentiableCurve
    {r : ℕ∞ω} {c : ℝ → M} {a ε s : ℝ} {f : ℝ × ℝ → M}
    (hf : IsVariationOfOrder I r c a ε f) (hr : (1 : ℕ∞ω) ≤ r)
    (hs : s ∈ Ioo (-ε) ε) :
    Geodesic.IsPiecewiseDifferentiableCurve (I := I) (curve f s) 0 a :=
  (hf.isVariation hr).curve_isPiecewiseDifferentiableCurve hs

/-- **Math.** do Carmo Ch. 9, Definition 2.1.  A variation is proper when all
curves in the family have the same initial and final points. -/
def IsProperVariation (c : ℝ → M) (a ε : ℝ) (f : ℝ × ℝ → M) : Prop :=
  ∀ s ∈ Ioo (-ε) ε, f (s, 0) = c 0 ∧ f (s, a) = c a

/-- **Math.** A differentiable variation has no time breakpoints: the whole
parameter rectangle is `C^1`. -/
def IsDifferentiableVariation (I : ModelWithCorners ℝ E H) (a ε : ℝ)
    (f : ℝ × ℝ → M) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 f (Ioo (-ε) ε ×ˢ Icc 0 a)

/-- **Math.** A differentiable variation surface at an arbitrary order. -/
def IsDifferentiableVariationOfOrder (I : ModelWithCorners ℝ E H) (r : ℕ∞ω)
    (a ε : ℝ) (f : ℝ × ℝ → M) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I r f (Ioo (-ε) ε ×ˢ Icc 0 a)

/-- **Math.** A globally smooth variation surface on its parameter rectangle. -/
abbrev IsSmoothDifferentiableVariation (I : ModelWithCorners ℝ E H)
    (a ε : ℝ) (f : ℝ × ℝ → M) : Prop :=
  IsDifferentiableVariationOfOrder I ∞ a ε f

/-- **Math.** The properness condition says exactly that every curve in the
variation has the same two endpoints. -/
theorem isProperVariation_iff (c : ℝ → M) (a ε : ℝ) (f : ℝ × ℝ → M) :
    IsProperVariation c a ε f ↔
      ∀ s ∈ Ioo (-ε) ε, curve f s 0 = c 0 ∧ curve f s a = c a :=
  Iff.rfl

/-- **Math.** A differentiable surface with zero slice `c` is a variation,
using the one-piece subdivision `0 < a`. -/
theorem IsDifferentiableVariation.isVariation {c : ℝ → M} {a ε : ℝ}
    {f : ℝ × ℝ → M} (hf : IsDifferentiableVariation I a ε f)
    (ha : 0 < a) (hε : 0 < ε) (hzero : ∀ t ∈ Icc 0 a, f (0, t) = c t) :
    IsVariation I c a ε f := by
  refine ⟨hε, ?_, hzero, 1, (fun i => if i = 0 then 0 else a), by simp, by simp,
    by simp, ?_, ?_⟩
  · exact hf.continuousOn
  · intro i hi
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst i
    simpa using ha
  · intro i hi
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst i
    simpa [IsDifferentiableVariation] using hf

/-- **Math.** A surface which is order-`r` differentiable on the whole
rectangle is an order-`r` variation with the one-piece subdivision. -/
theorem IsDifferentiableVariationOfOrder.isVariationOfOrder
    {r : ℕ∞ω} {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}
    (hf : IsDifferentiableVariationOfOrder I r a ε f)
    (ha : 0 < a) (hε : 0 < ε) (hzero : ∀ t ∈ Icc 0 a, f (0, t) = c t) :
    IsVariationOfOrder I r c a ε f := by
  refine ⟨hε, ?_, hzero, 1, (fun i => if i = 0 then 0 else a), by simp, by simp,
    by simp, ?_, ?_⟩
  · exact hf.continuousOn
  · intro i hi
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst i
    simpa using ha
  · intro i hi
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst i
    simpa [IsDifferentiableVariationOfOrder] using hf

/-- **Math.** The variational field `V(t) = ∂f/∂s (0,t)`, represented in the
model vector space of the tangent bundle, as are all fields along curves in
this library.  We differentiate the transversal itself rather than the full
surface: at a time breakpoint the latter need not have a total derivative,
while the transversal derivative is exactly what do Carmo's definition uses. -/
def variationalField (I : ModelWithCorners ℝ E H) (f : ℝ × ℝ → M) : ℝ → E :=
  fun t => mfderiv 𝓘(ℝ, ℝ) I (transversal f t) 0 1

@[simp] theorem variationalField_apply (I : ModelWithCorners ℝ E H)
    (f : ℝ × ℝ → M) (t : ℝ) :
    variationalField I f t = mfderiv 𝓘(ℝ, ℝ) I (transversal f t) 0 1 :=
  rfl

/-- **Math.** The variational field of a proper variation vanishes at the left
endpoint.  Indeed, properness makes the transversal `s ↦ f (s, 0)` equal to
the constant curve `c 0` on a neighbourhood of `s = 0`; the `mfderiv`
congruence theorem therefore identifies its derivative with `mfderiv_const`.
This is the endpoint implication used in do Carmo Ch. 9, Definition 2.1 and
the forward direction of Proposition 2.5. -/
theorem IsProperVariation.variationalField_zero
    {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}
    (hf : IsProperVariation c a ε f) (hε : 0 < ε) :
    variationalField I f 0 = 0 := by
  rw [variationalField_apply]
  have hnhds : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds (by constructor <;> linarith)
  have hEq : transversal f 0 =ᶠ[𝓝 (0 : ℝ)] (fun _ => c 0) := by
    filter_upwards [hnhds] with s hs
    exact (hf s hs).1
  rw [hEq.mfderiv_eq, mfderiv_const]
  rfl

/-- **Math.** The variational field of a proper variation vanishes at the
right endpoint.  This is the endpoint companion to
`IsProperVariation.variationalField_zero`; together they provide the
`V(0)=V(a)=0` hypothesis in the proper first- and second-variation formulas. -/
theorem IsProperVariation.variationalField_right
    {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}
    (hf : IsProperVariation c a ε f) (hε : 0 < ε) :
    variationalField I f a = 0 := by
  rw [variationalField_apply]
  have hnhds : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds (by constructor <;> linarith)
  have hEq : transversal f a =ᶠ[𝓝 (0 : ℝ)] (fun _ => c a) := by
    filter_upwards [hnhds] with s hs
    exact (hf s hs).2
  rw [hEq.mfderiv_eq, mfderiv_const]
  rfl

/-- **Math.** A proper `IsVariation` has a variational field that vanishes at
both endpoints.  This packages the two endpoint lemmas above with the
positivity of `ε` already stored in `IsVariation`. -/
theorem IsVariation.variationalField_eq_zero_endpoints
    {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}
    (hvar : IsVariation I c a ε f) (hproper : IsProperVariation c a ε f) :
    variationalField I f 0 = 0 ∧ variationalField I f a = 0 := by
  exact ⟨hproper.variationalField_zero hvar.epsilon_pos,
    hproper.variationalField_right hvar.epsilon_pos⟩

end Riemannian.Variation
