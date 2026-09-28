import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3Transport
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3CurveRegularity
import DoCarmoLib.Riemannian.Variation.ArbitraryParallelTransport

/-!
# do Carmo Chapter 3, Definition 3.1: parallel transport along a broken curve

do Carmo closes Definition 3.1 with

> Parallel transport extends to such curves by transporting successively over
> each differentiable segment.

`DoCarmoCh3Transport.lean` records that sentence as a *relation*,
`IsPiecewiseParallelTransport`, and its file docstring says an
existence/uniqueness theorem is still owed.  This file supplies it — and, in
doing so, has to correct the relation, because the original one is not the
statement do Carmo makes.

## The defect in the original relation

`IsPiecewiseParallelFieldAlongOn` asks for a single field `w` which is
`Jacobi.IsParallelFieldAlongOn` on each *closed* piece `[τ i, τ (i+1)]`.
Unfolding, the chart certificate `Jacobi.IsParallelSolOn` demands, at **every**
`t` of the closed piece,

`HasDerivWithinAt (chart reading of w) (-Γ(deriv u t, w t)(u t)) (Icc a' b') t`,

where `u` is the chart reading of the curve and `deriv` is the **two-sided**
derivative.  At an interior breakpoint `τ i` (`0 < i < n`) of a curve that
genuinely breaks, `u` has no two-sided derivative, so `deriv u (τ i)` is Lean's
junk value `0`.  Since `Γ` is linear in its first slot
(`chartChristoffelContraction_zero_left`), the coefficient collapses and the
constraint imposed at the corner becomes `w' (τ i) = 0` on each side — which the
genuine one-sided transport equations contradict unless the curve is unbroken
there.  So on a curve with a real corner the original relation is not
"successive transport"; it is successive transport *plus* a spurious condition
read off a junk derivative.

The condition is spurious rather than merely strong: it comes from `deriv`
having no information at the corner, not from any geometry.  Nothing downstream
consumed the relation, so nothing was proved from the bad clause.

## The fix

Transport is prescribed piece by piece, and the pieces are tied together only by
sharing the field at the breakpoints.  That is exactly do Carmo's "successively":

* `IsPiecewiseParallelAlong` (below) asks for a family `w : ℕ → ℝ → E`, one
  parallel field per piece, agreeing at each interior breakpoint.  Each piece is
  `C^r` there, so `Variation.IsParallelCovariantFieldAlongOn` applies to it with
  no corner in sight.
* The breakpoint-matching clause is the whole of the vertex condition, and it is
  stated where it is true: at the breakpoint value, not on a derivative.

`exists_isPiecewiseParallelAlong` then transports successively along the
subdivision by induction on the pieces, and
`isPiecewiseParallelAlong_unique` propagates uniqueness through the same
induction.  Together they are do Carmo's sentence as a theorem.

The curve is taken as a `SubdividedCurveOfOrder` so that the pieces — and hence
the vertices the transport is glued at — are data rather than an unspecified
existential witness.
-/

open Set Riemannian Riemannian.Variation
open scoped ContDiff Manifold Topology

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The corner is where the original relation goes wrong

The two lemmas below are the audit trail for the file docstring: at a point
where the chart reading has no two-sided derivative, the certificate's
coefficient is `0`, so the constraint it imposes is not the transport equation.
-/

/-- **Math.** Where a chart reading fails to be differentiable, the
parallel-transport coefficient built from its two-sided `deriv` vanishes
identically: `deriv` returns `0` there and `Γ` is linear in that slot.  This is
why imposing the closed-piece certificate *at* a corner says nothing about
transport. -/
theorem chartChristoffelContraction_deriv_eq_zero_of_not_differentiableAt
    (g : RiemannianMetric I M) (α : M) {u : ℝ → E} {t : ℝ}
    (hu : ¬ DifferentiableAt ℝ u t) (w y : E) :
    chartChristoffelContraction (I := I) g α (deriv u t) w y = 0 := by
  rw [deriv_zero_of_not_differentiableAt hu]
  exact chartChristoffelContraction_zero_left (I := I) g α w y

/-! ### Segments

The corner lemma above forces a design decision.  Every parallel predicate in
this library is `deriv`-based, so evaluating one *along the broken curve* on a
closed piece imposes a junk condition at the piece's endpoints for exactly the
reason just proved — the defect is not confined to the piecewise wrapper.

do Carmo's own phrasing avoids this: he transports "over each differentiable
segment", and a segment *is* a differentiable curve.  So the parallel condition
is stated along each segment, and only the breakpoint values are shared.  A
`Segmentation` records those segments. -/

/-- **Math.** A **segmentation** of a subdivided curve: for each piece, a curve
that is differentiable in do Carmo's sense on all of `ℝ` and agrees with the
broken curve on that piece.  This is what "each differentiable segment" names.

The hypothesis is stronger than `C`'s own `ContMDiffOn` pieces, which give
differentiability only *within* the closed piece; it asks each piece to be cut
out of a curve differentiable in a neighbourhood.  That is what makes the
two-sided derivative at a breakpoint refer to the segment rather than to the
corner.

The extra strength is only apparent, and `DoCarmoCh3SegmentReparam.lean` proves
it: `Segmentation.ofLocal` builds a segmentation from a segment defined only on an
open *neighbourhood* of its piece, by reparametrizing the domain so that the
composite never leaves that neighbourhood.  With `local_of_segmentation` as the
converse the two hypothesis classes are **equivalent**, so requiring the segments
to be defined for all time costs no generality.

Note the hypothesis there is on the *segment*, not on `C.toFun`: asking the broken
curve itself to be `C^1` near the closed piece would force differentiability at
the breakpoint and so exclude every corner. -/
structure Segmentation (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (C : SubdividedCurveOfOrder I 1 M) where
  /-- The differentiable segment carrying piece `i`. -/
  seg : ℕ → ℝ → M
  /-- Each segment is differentiable on all of `ℝ`. -/
  seg_contMDiff : ∀ i < C.n, ContMDiff 𝓘(ℝ, ℝ) I 1 (seg i)
  /-- Segment `i` reproduces the curve on piece `i`. -/
  seg_eqOn : ∀ i < C.n, EqOn (seg i) C.toFun (Icc (C.tau i) (C.tau (i + 1)))

namespace Segmentation

variable {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C)

/-- **Math.** Consecutive segments meet at the breakpoint they share: both
reproduce the curve there. -/
theorem seg_succ_eq (i : ℕ) (hi : i + 1 < C.n) :
    S.seg (i + 1) (C.tau (i + 1)) = S.seg i (C.tau (i + 1)) := by
  have hi' : i < C.n := Nat.lt_of_succ_lt hi
  rw [S.seg_eqOn (i + 1) hi ⟨le_rfl, (C.tau_strict (i + 1) hi).le⟩,
    S.seg_eqOn i hi' ⟨(C.tau_strict i hi').le, le_rfl⟩]

end Segmentation

/-! ### Differentiability at a vertex, from either side

`leftVelocity`/`rightVelocity` (`DoCarmoCh3Transport.lean`) are `mfderivWithin`
on `Iic`/`Ici`, and `vertexAngle` is the metric angle between them.  Those are
junk values unless the one-sided derivatives exist, so the bundled predicates
`HasLeftVelocity`/`HasRightVelocity` are what make `vertexAngle` the book's
angle.

The two lemmas below are the piece-relative step: a segmented curve is
differentiable at each vertex *within the adjacent piece*.  Passing from the
piece to the one-sided predicates is done in `DoCarmoCh3VertexAngle.lean`, which
proves that the closed piece and the half-line generate the same neighbourhood
filter at the shared endpoint — so piece-relative control is already one-sided
control, and nothing outside the piece is needed.

Neither lemma needs `[I.Boundaryless]`, so both are stated before it is
introduced: Definition 3.3's domain `A` need not be open, and its boundary
vertex-angle condition is exactly what this material feeds. -/

/-- **Math.** A segmented curve is differentiable at the right end of piece `i`
*within that piece*: segment `i` is differentiable there and agrees with the
curve on `[τ i, τ (i+1)]`. -/
theorem mdifferentiableWithinAt_piece_right {C : SubdividedCurveOfOrder I 1 M}
    (S : Segmentation I M C) {i : ℕ} (hi : i < C.n) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I C.toFun (Icc (C.tau i) (C.tau (i + 1)))
      (C.tau (i + 1)) := by
  have hseg : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (S.seg i)
      (Icc (C.tau i) (C.tau (i + 1))) (C.tau (i + 1)) :=
    ((S.seg_contMDiff i hi).mdifferentiable one_ne_zero _).mdifferentiableWithinAt
  exact hseg.congr (fun t ht => (S.seg_eqOn i hi ht).symm)
    (S.seg_eqOn i hi ⟨(C.tau_strict i hi).le, le_rfl⟩).symm

/-- **Math.** The same at the left end of piece `i`, i.e. on the other side of
the vertex it shares with piece `i - 1`. -/
theorem mdifferentiableWithinAt_piece_left {C : SubdividedCurveOfOrder I 1 M}
    (S : Segmentation I M C) {i : ℕ} (hi : i < C.n) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I C.toFun (Icc (C.tau i) (C.tau (i + 1)))
      (C.tau i) := by
  have hseg : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (S.seg i)
      (Icc (C.tau i) (C.tau (i + 1))) (C.tau i) :=
    ((S.seg_contMDiff i hi).mdifferentiable one_ne_zero _).mdifferentiableWithinAt
  exact hseg.congr (fun t ht => (S.seg_eqOn i hi ht).symm)
    (S.seg_eqOn i hi ⟨le_rfl, (C.tau_strict i hi).le⟩).symm

/-! ### Successive transport -/

variable [I.Boundaryless]

/-- **Math.** do Carmo Ch. 3, Def. 3.1, last sentence: a **piecewise parallel
field** along a segmented curve is a family `w i`, one field per piece, with
`w i` parallel *along segment `i`* over `[τ i, τ (i+1)]`, and consecutive fields
agreeing at the breakpoint they share.

Both clauses are stated where they are true.  The parallel condition refers to
the segment, which is differentiable at the breakpoint, rather than to the
broken curve, which is not; and the matching condition is on the field's
*value*, not on a derivative.  That is precisely "transporting successively over
each differentiable segment". -/
def IsPiecewiseParallelAlong (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C)
    (w : ℕ → ℝ → E) : Prop :=
  (∀ i < C.n, IsParallelCovariantFieldAlongOn (I := I) g (S.seg i) (w i)
      (C.tau i) (C.tau (i + 1))) ∧
    ∀ i, i + 1 < C.n → w (i + 1) (C.tau (i + 1)) = w i (C.tau (i + 1))

/-- **Math.** **do Carmo Ch. 3, Definition 3.1: existence of parallel transport
along a broken curve.**  Given a vector at the initial vertex, successive
transport over the differentiable segments produces a piecewise parallel field
taking that initial value.

The induction is on the number of pieces transported so far: the field on piece
`i + 1` is seeded with the value the field on piece `i` reached at their common
breakpoint, and each individual piece is handled by the arbitrary-`C¹`-curve
existence theorem `exists_parallelCovariantFieldAlongOn` — which applies because
a segment is differentiable at the breakpoint even where the curve is not. -/
theorem exists_isPiecewiseParallelAlong (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C) (w₀ : E) :
    ∃ w : ℕ → ℝ → E, IsPiecewiseParallelAlong (I := I) g S w ∧
      w 0 (C.tau 0) = w₀ := by
  classical
  -- Transport across piece `i` from a prescribed value at `τ i`.
  have step : ∀ i, i < C.n → ∀ v : E, ∃ f : ℝ → E,
      IsParallelCovariantFieldAlongOn (I := I) g (S.seg i) f
        (C.tau i) (C.tau (i + 1)) ∧ f (C.tau i) = v := by
    intro i hi v
    exact exists_parallelCovariantFieldAlongOn (I := I) (g := g)
      (C.tau_strict i hi) (S.seg_contMDiff i hi) v
  -- Build the family recursively, seeding each piece at the shared breakpoint.
  let F : ℕ → ℝ → E := fun i =>
    Nat.rec (motive := fun _ => ℝ → E)
      (if h : 0 < C.n then Classical.choose (step 0 h w₀) else fun _ => w₀)
      (fun k fk =>
        if h : k + 1 < C.n then
          Classical.choose (step (k + 1) h (fk (C.tau (k + 1)))) else fk)
      i
  have hF0 : F 0 = if h : 0 < C.n then Classical.choose (step 0 h w₀)
      else fun _ => w₀ := rfl
  have hFsucc : ∀ k, F (k + 1) =
      if h : k + 1 < C.n then
        Classical.choose (step (k + 1) h (F k (C.tau (k + 1)))) else F k :=
    fun _ => rfl
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · -- each piece is parallel along its segment
    intro i hi
    cases i with
    | zero =>
        rw [hF0, dif_pos hi]
        exact (Classical.choose_spec (step 0 hi w₀)).1
    | succ k =>
        rw [hFsucc k, dif_pos hi]
        exact (Classical.choose_spec (step (k + 1) hi (F k (C.tau (k + 1))))).1
  · -- consecutive fields match at the shared breakpoint
    intro i hi
    rw [hFsucc i, dif_pos hi]
    exact (Classical.choose_spec (step (i + 1) hi (F i (C.tau (i + 1))))).2
  · -- the initial value is `w₀`
    rw [hF0, dif_pos C.n_pos]
    exact (Classical.choose_spec (step 0 C.n_pos w₀)).2

/-- **Math.** **do Carmo Ch. 3, Definition 3.1: uniqueness of parallel transport
along a broken curve.**  Two piecewise parallel fields with the same value at the
initial vertex agree on every piece.

Uniqueness propagates through the same induction as existence: on piece `i` both
fields solve the same linear ODE along segment `i`, so single-piece uniqueness
(`IsParallelCovariantFieldAlongOn.eqOn_of_eq_at`) makes them agree there once
they agree at `τ i`; the matching clause then transfers that agreement across the
breakpoint to piece `i + 1`. -/
theorem isPiecewiseParallelAlong_unique (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} {S : Segmentation I M C} {w w' : ℕ → ℝ → E}
    (hw : IsPiecewiseParallelAlong (I := I) g S w)
    (hw' : IsPiecewiseParallelAlong (I := I) g S w')
    (h₀ : w' 0 (C.tau 0) = w 0 (C.tau 0)) :
    ∀ i < C.n, EqOn (w' i) (w i) (Icc (C.tau i) (C.tau (i + 1))) := by
  -- Agreement at the left endpoint of piece `i`, by induction on `i`.
  have hstart : ∀ i, i < C.n → w' i (C.tau i) = w i (C.tau i) := by
    intro i
    induction i with
    | zero => exact fun _ => h₀
    | succ k ih =>
        intro hk
        have hk' : k < C.n := Nat.lt_of_succ_lt hk
        -- both fields cross the breakpoint by their matching clauses
        rw [hw'.2 k hk, hw.2 k hk]
        -- and they already agree on piece `k`
        exact (single k hk' (ih hk')) ⟨(C.tau_strict k hk').le, le_rfl⟩
  exact fun i hi => single i hi (hstart i hi)
where
  /-- Single-piece uniqueness: agreement at `τ i` propagates along segment `i`. -/
  single (i : ℕ) (hi : i < C.n) (h : w' i (C.tau i) = w i (C.tau i)) :
      EqOn (w' i) (w i) (Icc (C.tau i) (C.tau (i + 1))) :=
    (hw'.1 i hi).eqOn_of_eq_at (hw.1 i hi)
      (isChartDifferentiableOn_of_contMDiff (I := I) (S.seg_contMDiff i hi))
      (fun _t _ht => (S.seg_contMDiff i hi).continuous.continuousAt)
      (left_mem_Icc.2 (C.tau_strict i hi).le) h

/-! ### Nonvacuity

`Segmentation` asks for more than Definition 3.1's `ContMDiffOn` pieces, so it is
worth exhibiting a genuinely broken curve that carries one — otherwise the
existence theorem above could be about an empty class of curves.  (The stronger
statement, that the extra hypothesis costs no generality at all, is
`Segmentation.ofLocal` in `DoCarmoCh3SegmentReparam.lean`.) -/

/-- **Math.** A curve concatenated from two differentiable curves meeting at
`m` — the shape of do Carmo's broken geodesics — carries a segmentation with two
pieces.  The concatenation is `Set.piecewise`, so it agrees with `c₀` up to `m`
and with `c₁` after, and no differentiability is claimed *at* `m`: that is the
point of the corner. -/
def segmentationOfConcat {c₀ c₁ : ℝ → M} {l m r : ℝ} (hlm : l < m) (hmr : m < r)
    (h₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 c₀) (h₁ : ContMDiff 𝓘(ℝ, ℝ) I 1 c₁)
    (hjoin : c₁ m = c₀ m) :
    Σ' C : SubdividedCurveOfOrder I 1 M, Segmentation I M C := by
  classical
  refine ⟨{ a := l, b := r, n := 2
            tau := fun i => if i = 0 then l else if i = 1 then m else r
            toFun := fun t => if t ≤ m then c₀ t else c₁ t
            n_pos := by norm_num
            tau_zero := by norm_num
            tau_last := by norm_num
            tau_strict := ?_
            continuous := ?_
            piecewise := ?_ },
          { seg := fun i => if i = 0 then c₀ else c₁
            seg_contMDiff := ?_
            seg_eqOn := ?_ }⟩
  · intro i hi
    interval_cases i <;> simpa using ‹_›
  -- continuity: each closed piece is continuous and they share the endpoint `m`
  · have hc₀ : ContinuousOn (fun t => if t ≤ m then c₀ t else c₁ t) (Icc l m) := by
      refine (h₀.continuous.continuousOn).congr fun t ht => ?_
      show (if t ≤ m then c₀ t else c₁ t) = c₀ t
      rw [if_pos ht.2]
    have hc₁ : ContinuousOn (fun t => if t ≤ m then c₀ t else c₁ t) (Icc m r) := by
      refine (h₁.continuous.continuousOn).congr fun t ht => ?_
      show (if t ≤ m then c₀ t else c₁ t) = c₁ t
      rcases le_or_gt t m with htm | htm
      · rw [if_pos htm, le_antisymm htm ht.1, hjoin]
      · rw [if_neg (not_le.mpr htm)]
    have hu := hc₀.union_of_isClosed hc₁ isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hlm.le hmr.le] at hu
  -- each piece is C¹, by agreeing with the corresponding segment there
  · intro i hi
    have hi2 : i < 2 := hi
    interval_cases i
    · refine (h₀.contMDiffOn (s := Icc l m)).congr fun t ht => ?_
      have htm : t ≤ m := by simpa using ht.2
      show (if t ≤ m then c₀ t else c₁ t) = c₀ t
      rw [if_pos htm]
    · refine (h₁.contMDiffOn (s := Icc m r)).congr fun t ht => ?_
      have hmt : m ≤ t := by simpa using ht.1
      show (if t ≤ m then c₀ t else c₁ t) = c₁ t
      rcases le_or_gt t m with htm | htm
      · rw [if_pos htm, le_antisymm htm hmt, hjoin]
      · rw [if_neg (not_le.mpr htm)]
  · intro i hi
    have hi2 : i < 2 := hi
    interval_cases i <;> simpa using ‹_›
  · intro i hi
    have hi2 : i < 2 := hi
    interval_cases i
    · intro t ht
      have htm : t ≤ m := by simpa using ht.2
      show c₀ t = (if t ≤ m then c₀ t else c₁ t)
      rw [if_pos htm]
    · intro t ht
      have hmt : m ≤ t := by simpa using ht.1
      show c₁ t = (if t ≤ m then c₀ t else c₁ t)
      rcases le_or_gt t m with htm | htm
      · rw [if_pos htm, le_antisymm htm hmt, hjoin]
      · rw [if_neg (not_le.mpr htm)]

/-- **Math.** The existence theorem is not about an empty class: every
concatenation of two differentiable curves — do Carmo's broken geodesic — admits
successive parallel transport of any prescribed initial vector. -/
theorem exists_isPiecewiseParallelAlong_concat (g : RiemannianMetric I M)
    {c₀ c₁ : ℝ → M} {l m r : ℝ} (hlm : l < m) (hmr : m < r)
    (h₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 c₀) (h₁ : ContMDiff 𝓘(ℝ, ℝ) I 1 c₁)
    (hjoin : c₁ m = c₀ m) (w₀ : E) :
    ∃ w : ℕ → ℝ → E,
      IsPiecewiseParallelAlong (I := I) g
        (segmentationOfConcat (I := I) hlm hmr h₀ h₁ hjoin).2 w ∧
      w 0 ((segmentationOfConcat (I := I) hlm hmr h₀ h₁ hjoin).1.tau 0) = w₀ :=
  exists_isPiecewiseParallelAlong (I := I) g _ w₀

/-! ### The transport map

Existence plus uniqueness make "the vector transported to the `i`-th vertex" a
function of the initial vector, so successive transport is a map rather than a
relation.  Building it as the composite of the per-segment transports —
themselves already known to be linear — is what makes linearity and
metric-preservation inherited rather than re-proved. -/

/-- **Math.** do Carmo Ch. 3, Def. 3.1: **successive parallel transport** from
the initial vertex to the `i`-th vertex, as the composite of the segment
transports over pieces `0, …, i-1`.  Each factor is
`parallelCovariantTransportAlong` on its own segment, evaluated at the right
endpoint of the piece. -/
def piecewiseTransport (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C) :
    ℕ → (E →ₗ[ℝ] E)
  | 0 => LinearMap.id
  | (i + 1) =>
      if h : i < C.n then
        (parallelCovariantTransportAlong (I := I) g (C.tau_strict i h)
          (S.seg_contMDiff i h)
          (right_mem_Icc.2 (C.tau_strict i h).le)).comp
            (piecewiseTransport g S i)
      else piecewiseTransport g S i

@[simp] theorem piecewiseTransport_zero (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C) :
    piecewiseTransport (I := I) g S 0 = LinearMap.id := rfl

/-- **Math.** The recursion step: transporting to vertex `i + 1` is transporting
to vertex `i` and then across segment `i`. -/
theorem piecewiseTransport_succ (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C) {i : ℕ}
    (hi : i < C.n) :
    piecewiseTransport (I := I) g S (i + 1) =
      (parallelCovariantTransportAlong (I := I) g (C.tau_strict i hi)
        (S.seg_contMDiff i hi)
        (right_mem_Icc.2 (C.tau_strict i hi).le)).comp
          (piecewiseTransport (I := I) g S i) := by
  rw [piecewiseTransport, dif_pos hi]

/-- **Math.** Successive transport is injective: each segment transport is, and
a composite of injections is one.  With `metricInner_piecewiseTransport` below
this is the broken-curve form of "parallel transport is an isometry". -/
theorem piecewiseTransport_injective (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C) :
    ∀ i, i ≤ C.n → Function.Injective (piecewiseTransport (I := I) g S i) := by
  intro i
  induction i with
  | zero => exact fun _ => fun x y h => h
  | succ k ih =>
      intro hk
      have hk' : k < C.n := hk
      rw [piecewiseTransport_succ (I := I) g S hk']
      exact (parallelCovariantTransportAlong_injective (I := I) g
        (C.tau_strict k hk') (S.seg_contMDiff k hk')
        (right_mem_Icc.2 (C.tau_strict k hk').le)).comp (ih hk'.le)

/-- **Math.** Successive transport preserves the Riemannian pairing: each
segment transport does (`metricInner_parallelCovariantTransportAlong`), and the
breakpoint identification `S.seg_succ_eq` means consecutive factors are compared
at the same point of `M`.  This is do Carmo's statement that transport along a
broken curve is an isometry between the endpoint tangent spaces. -/
theorem metricInner_piecewiseTransport (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} (S : Segmentation I M C) :
    ∀ i, i ≤ C.n → ∀ v w : E,
      g.metricInner (C.vertex i)
          (piecewiseTransport (I := I) g S i v : TangentSpace I (C.vertex i))
          (piecewiseTransport (I := I) g S i w) =
        g.metricInner (C.vertex 0) (v : TangentSpace I (C.vertex 0)) w := by
  -- Each vertex is a value of the segment adjacent to it, so the metric
  -- basepoints of consecutive steps agree.  Both `tau`-arguments are named
  -- through `C.vertex` to keep the dependent `TangentSpace` index fixed.
  have hL : ∀ i, i < C.n → S.seg i (C.tau i) = C.vertex i := fun i hi =>
    S.seg_eqOn i hi ⟨le_rfl, (C.tau_strict i hi).le⟩
  have hR : ∀ i, i < C.n → S.seg i (C.tau (i + 1)) = C.vertex (i + 1) := fun i hi =>
    S.seg_eqOn i hi ⟨(C.tau_strict i hi).le, le_rfl⟩
  intro i
  induction i with
  | zero => exact fun _ v w => rfl
  | succ k ih =>
      intro hk v w
      have hk' : k < C.n := hk
      -- transport across segment `k` preserves the pairing between its endpoints
      have hseg := metricInner_parallelCovariantTransportAlong (I := I) g
        (C.tau_strict k hk') (S.seg_contMDiff k hk')
        (right_mem_Icc.2 (C.tau_strict k hk').le)
        (piecewiseTransport (I := I) g S k v) (piecewiseTransport (I := I) g S k w)
      -- move both basepoints of `hseg` onto the vertices before composing
      rw [hL k hk', hR k hk'] at hseg
      rw [piecewiseTransport_succ (I := I) g S hk']
      exact hseg.trans (ih hk'.le v w)

/-- **Math.** The transport map computes the piecewise parallel field: the field
produced by successive transport reaches, at each vertex, exactly the value
`piecewiseTransport` assigns to it.  This is what makes the map and the relation
two descriptions of one thing rather than parallel constructions — the map is the
relation's unique solution, evaluated at the vertices. -/
theorem piecewiseTransport_eq_of_isPiecewiseParallelAlong (g : RiemannianMetric I M)
    {C : SubdividedCurveOfOrder I 1 M} {S : Segmentation I M C} {w : ℕ → ℝ → E}
    (hw : IsPiecewiseParallelAlong (I := I) g S w) (w₀ : E)
    (h₀ : w 0 (C.tau 0) = w₀) :
    ∀ i, i < C.n → w i (C.tau i) = piecewiseTransport (I := I) g S i w₀ := by
  intro i
  induction i with
  | zero => exact fun _ => h₀
  | succ k ih =>
      intro hk
      have hk' : k < C.n := Nat.lt_of_succ_lt hk
      -- cross the breakpoint with the matching clause, then identify the
      -- segment transport as the unique parallel field seeded at `τ k`
      rw [hw.2 k hk, piecewiseTransport_succ (I := I) g S hk']
      have huniq := (hw.1 k hk').eqOn_of_eq_at
        (parallelCovariantFieldSeed_isParallel (I := I) g (C.tau_strict k hk')
          (S.seg_contMDiff k hk') (piecewiseTransport (I := I) g S k w₀))
        (isChartDifferentiableOn_of_contMDiff (I := I) (S.seg_contMDiff k hk'))
        (fun _t _ht => (S.seg_contMDiff k hk').continuous.continuousAt)
        (left_mem_Icc.2 (C.tau_strict k hk').le)
        (by rw [parallelCovariantFieldSeed_left]; exact ih hk')
      exact huniq (right_mem_Icc.2 (C.tau_strict k hk').le)

end Riemannian.Geodesic
