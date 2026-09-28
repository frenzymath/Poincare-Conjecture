import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3

/-!
# Piecewise-curve regularity (do Carmo Ch. 3, Definition 3.1)

`DoCarmoCh3` defines `IsPiecewiseDifferentiableCurve` with `C¹` pieces, which is
the regularity the length theory consumes.  do Carmo's own "differentiable"
means `C^∞` (Ch. 0, Introduction, printed p. 2), so his Definition 3.1 asks for
`C^∞` pieces.

This file supplies the order-graded refinement, exactly as
`DoCarmoCh3SurfaceRegularity` does for Definition 3.3.  The legacy predicate
remains the order-one member of the hierarchy, so nothing downstream changes;
`IsPiecewiseSmoothCurve` is the faithful `C^∞` form of the book's definition.

Raising the order *in place* would have been wrong rather than merely
inconvenient: the predicate occurs under a `∀ c` inside
`IsMinimizingGeodesicSegment`, where a smaller curve class admits fewer
competitors and therefore weakens every minimizing statement.  Grading the
order keeps both readings available and lets each site name the one it means.
-/

open Manifold Set
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 3, Definition 3.1 at differentiability order `r`: a
continuous map on `[a,b]` which is `C^r` on every member of some finite strict
partition of the interval.  At order one this is definitionally the legacy
`IsPiecewiseDifferentiableCurve` predicate; at order `∞` it is do Carmo's own
definition, since his "differentiable" is `C^∞`. -/
def IsPiecewiseDifferentiableCurveOfOrder (I : ModelWithCorners ℝ E H) (r : ℕ∞ω)
    (c : ℝ → M) (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧
    ∃ (n : ℕ) (τ : ℕ → ℝ), 0 < n ∧ τ 0 = a ∧ τ n = b ∧
      (∀ i < n, τ i < τ (i + 1)) ∧
      ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I r c (Icc (τ i) (τ (i + 1)))

/-- **Math.** do Carmo Ch. 3, Definition 3.1 read with his own convention: the
pieces are `C^∞`.  This is the faithful form of the book's definition, and the
class over which his Ch. 7 Definition 2.4 infimizes. -/
abbrev IsPiecewiseSmoothCurve (I : ModelWithCorners ℝ E H)
    (c : ℝ → M) (a b : ℝ) : Prop :=
  IsPiecewiseDifferentiableCurveOfOrder I ∞ c a b

namespace IsPiecewiseDifferentiableCurveOfOrder

variable {r r' : ℕ∞ω} {c : ℝ → M} {a b : ℝ}

/-- **Math.** The curve is continuous on the whole closed interval. -/
theorem continuousOn (hc : IsPiecewiseDifferentiableCurveOfOrder I r c a b) :
    ContinuousOn c (Icc a b) :=
  hc.1

/-- **Math.** The continuity clause of Definition 3.1 is implied by the pieces:
a map that is `C^r` on each closed member of a finite partition is continuous on
the whole interval, since consecutive closed pieces overlap at their shared
endpoint.  So the predicate can be established from the partition data alone. -/
theorem of_pieces {n : ℕ} {τ : ℕ → ℝ} (hn : 0 < n)
    (hτ0 : τ 0 = a) (hτn : τ n = b) (hstrict : ∀ i < n, τ i < τ (i + 1))
    (hpieces : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I r c (Icc (τ i) (τ (i + 1)))) :
    IsPiecewiseDifferentiableCurveOfOrder I r c a b := by
  refine ⟨?_, n, τ, hn, hτ0, hτn, hstrict, hpieces⟩
  have key : ∀ m : ℕ, m ≤ n → ContinuousOn c (Icc (τ 0) (τ m)) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        intro hkn
        have hk : k < n := Nat.lt_of_succ_le hkn
        have hmono : ∀ i < n, τ i ≤ τ (i + 1) := fun i hi => (hstrict i hi).le
        have h0k : τ 0 ≤ τ k := by
          have : ∀ m : ℕ, m ≤ n → τ 0 ≤ τ m := by
            intro m
            induction m with
            | zero => intro _; exact le_rfl
            | succ j ih' =>
                intro hjn
                exact (ih' (Nat.le_of_succ_le hjn)).trans
                  (hmono j (Nat.lt_of_succ_le hjn))
          exact this k hk.le
        have hsplit : Icc (τ 0) (τ (k + 1)) =
            Icc (τ 0) (τ k) ∪ Icc (τ k) (τ (k + 1)) :=
          (Icc_union_Icc_eq_Icc h0k (hmono k hk)).symm
        rw [hsplit]
        exact (ih hk.le).union_of_isClosed
          ((hpieces k hk).continuousOn) isClosed_Icc isClosed_Icc
  simpa [hτ0, hτn] using key n le_rfl

/-- **Math.** A curve of order `r` is a curve of every lower order. -/
theorem of_le (hc : IsPiecewiseDifferentiableCurveOfOrder I r c a b)
    (hrr' : r' ≤ r) : IsPiecewiseDifferentiableCurveOfOrder I r' c a b := by
  obtain ⟨hcont, n, τ, hn, hτ0, hτn, hstrict, hpieces⟩ := hc
  exact ⟨hcont, n, τ, hn, hτ0, hτn, hstrict,
    fun i hi => (hpieces i hi).of_le hrr'⟩

/-- **Math.** Forgetting regularity above `C¹` gives the legacy Ch. 3
piecewise-curve predicate, which is what the length theory consumes. -/
theorem isPiecewiseDifferentiableCurve
    (hc : IsPiecewiseDifferentiableCurveOfOrder I r c a b) (hr : (1 : ℕ∞ω) ≤ r) :
    IsPiecewiseDifferentiableCurve (I := I) c a b :=
  hc.of_le hr

/-- **Math.** The parameter interval of a Definition 3.1 curve is
nondegenerate.  This is not a convention: the partition is *strict* and has at
least one piece, so `a < b` is forced.  Consequently the degenerate "curve on a
point" is not a competitor in any infimum indexed by this predicate. -/
theorem lt (hc : IsPiecewiseDifferentiableCurveOfOrder I r c a b) : a < b := by
  obtain ⟨-, n, τ, hn, hτ0, hτn, hstrict, -⟩ := hc
  have key : ∀ m : ℕ, 0 < m → m ≤ n → τ 0 < τ m := by
    intro m
    induction m with
    | zero => intro h; exact absurd h (lt_irrefl 0)
    | succ k ih =>
        intro _ hkn
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact hstrict 0 (Nat.lt_of_succ_le hkn)
        · exact (ih hk (Nat.le_of_succ_le hkn)).trans
            (hstrict k (Nat.lt_of_succ_le hkn))
  simpa [hτ0, hτn] using key n hn le_rfl

/-- **Math.** The endpoints of the interval are correctly ordered. -/
theorem le (hc : IsPiecewiseDifferentiableCurveOfOrder I r c a b) : a ≤ b :=
  hc.lt.le

end IsPiecewiseDifferentiableCurveOfOrder

namespace IsPiecewiseDifferentiableCurve

variable {c : ℝ → M} {a b : ℝ}

/-- **Math.** The legacy piecewise-curve predicate is exactly the order-one
member of the graded hierarchy. -/
theorem isPiecewiseDifferentiableCurveOfOrderOne
    (hc : IsPiecewiseDifferentiableCurve (I := I) c a b) :
    IsPiecewiseDifferentiableCurveOfOrder I 1 c a b :=
  hc

end IsPiecewiseDifferentiableCurve

/-- **Math.** do Carmo's own Definition 3.1 curves are in particular piecewise
`C¹`, so every statement proved for the legacy class applies to them. -/
theorem IsPiecewiseSmoothCurve.isPiecewiseDifferentiableCurve
    {c : ℝ → M} {a b : ℝ} (hc : IsPiecewiseSmoothCurve I c a b) :
    IsPiecewiseDifferentiableCurve (I := I) c a b :=
  IsPiecewiseDifferentiableCurveOfOrder.isPiecewiseDifferentiableCurve hc (by norm_num)

/-! ## Vertices: the subdivision carried as data

do Carmo's Definition 3.1 goes on to name the partition points `c(t_i)` the
*vertices* of `c`.  That name cannot be attached to the predicate above, because
a curve satisfying it admits many partitions — every refinement of a valid
partition is another one — so "the `i`-th vertex of `c`" is not a function of
`c`.  (An accessor is *definable* from the predicate with `Classical.choose`,
since the existential is over `ℕ → ℝ`; it is just not well specified, as it
depends on which witness choice happens to return.)

The fix is the same one `PiecewiseC1BoundaryParametrization` uses for the
boundary of Definition 3.3: carry the subdivision as structure data.  Vertices
are then honest projections, and the predicate is recovered by forgetting them.
-/

/-- **Math.** do Carmo Ch. 3, Definition 3.1 with the subdivision carried as
data: a continuous curve on `[a,b]`, a strict finite partition of `[a,b]`, and
`C^r` regularity on each closed piece.  Unlike
`IsPiecewiseDifferentiableCurveOfOrder`, this records *which* partition is
meant, which is what makes the vertices well defined. -/
structure SubdividedCurveOfOrder (I : ModelWithCorners ℝ E H) (r : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- Left endpoint of the parameter interval. -/
  a : ℝ
  /-- Right endpoint of the parameter interval. -/
  b : ℝ
  /-- Number of pieces of the subdivision. -/
  n : ℕ
  /-- The breakpoints, with `tau 0 = a` and `tau n = b`. -/
  tau : ℕ → ℝ
  /-- The curve, defined globally so that the piece derivatives are available. -/
  toFun : ℝ → M
  n_pos : 0 < n
  tau_zero : tau 0 = a
  tau_last : tau n = b
  tau_strict : ∀ i < n, tau i < tau (i + 1)
  continuous : ContinuousOn toFun (Icc a b)
  piecewise : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I r toFun (Icc (tau i) (tau (i + 1)))

/-- **Math.** A subdivided curve whose pieces are `C^∞`, i.e. do Carmo's own
Definition 3.1 with its partition and vertices retained. -/
abbrev SubdividedSmoothCurve (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  SubdividedCurveOfOrder I ∞ M

namespace SubdividedCurveOfOrder

variable {r r' : ℕ∞ω} (C : SubdividedCurveOfOrder I r M)

instance : CoeFun (SubdividedCurveOfOrder I r M) (fun _ ↦ ℝ → M) := ⟨toFun⟩

@[simp] theorem coe_apply (t : ℝ) : C t = C.toFun t := rfl

/-- **Math.** do Carmo Ch. 3, Definition 3.1: the `i`-th **vertex** of a
subdivided curve is the value `c(t_i)` at the `i`-th breakpoint.  This is a
genuine function of the curve *together with its subdivision*. -/
def vertex (i : ℕ) : M := C.toFun (C.tau i)

@[simp] theorem vertex_zero : C.vertex 0 = C.toFun C.a := by
  rw [vertex, C.tau_zero]

@[simp] theorem vertex_last : C.vertex C.n = C.toFun C.b := by
  rw [vertex, C.tau_last]

/-- **Math.** The breakpoints increase weakly along the subdivision. -/
theorem tau_le {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ C.n) : C.tau i ≤ C.tau j := by
  induction j with
  | zero => exact Nat.le_zero.mp hij ▸ le_rfl
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hik
      · exact le_rfl
      · exact (ih (Nat.lt_succ_iff.mp hik) ((Nat.le_succ k).trans hjn)).trans
          (C.tau_strict k (Nat.lt_of_succ_le hjn)).le

theorem a_le_b : C.a ≤ C.b := by
  simpa [C.tau_zero, C.tau_last] using C.tau_le (Nat.zero_le C.n) le_rfl

/-- **Math.** Every breakpoint lies in the parameter interval. -/
theorem tau_mem_Icc {i : ℕ} (hi : i ≤ C.n) : C.tau i ∈ Icc C.a C.b := by
  refine ⟨?_, ?_⟩
  · simpa [C.tau_zero] using C.tau_le (Nat.zero_le i) hi
  · simpa [C.tau_last] using C.tau_le hi le_rfl

/-- **Math.** Forgetting the subdivision gives the Definition 3.1 predicate at
the same differentiability order. -/
theorem isPiecewiseDifferentiableCurveOfOrder :
    IsPiecewiseDifferentiableCurveOfOrder I r C.toFun C.a C.b :=
  ⟨C.continuous, C.n, C.tau, C.n_pos, C.tau_zero, C.tau_last, C.tau_strict,
    C.piecewise⟩

/-- **Math.** The parameter interval is nondegenerate, since the subdivision is
strict with at least one piece. -/
theorem a_lt_b : C.a < C.b :=
  C.isPiecewiseDifferentiableCurveOfOrder.lt

/-- **Math.** A subdivided curve of order `r` is one of every lower order, with
the same subdivision and hence the same vertices. -/
def ofLe (hrr' : r' ≤ r) : SubdividedCurveOfOrder I r' M :=
  { C with piecewise := fun i hi => (C.piecewise i hi).of_le hrr' }

@[simp] theorem ofLe_toFun (hrr' : r' ≤ r) : (C.ofLe hrr').toFun = C.toFun := rfl

@[simp] theorem ofLe_vertex (hrr' : r' ≤ r) (i : ℕ) :
    (C.ofLe hrr').vertex i = C.vertex i := rfl

end SubdividedCurveOfOrder

/-- **Math.** Conversely, a curve satisfying Definition 3.1 can be equipped with
*some* subdivision realizing it.  The witness is not unique — which is exactly
why the vertices belong to `SubdividedCurveOfOrder` and not to the predicate. -/
theorem IsPiecewiseDifferentiableCurveOfOrder.exists_subdividedCurve {r : ℕ∞ω}
    {c : ℝ → M} {a b : ℝ} (hc : IsPiecewiseDifferentiableCurveOfOrder I r c a b) :
    ∃ C : SubdividedCurveOfOrder I r M, C.toFun = c ∧ C.a = a ∧ C.b = b := by
  obtain ⟨hcont, n, τ, hn, hτ0, hτn, hstrict, hpieces⟩ := hc
  let C : SubdividedCurveOfOrder I r M :=
    { a := a, b := b, n := n, tau := τ, toFun := c, n_pos := hn,
      tau_zero := hτ0, tau_last := hτn, tau_strict := hstrict,
      continuous := hcont, piecewise := hpieces }
  exact ⟨C, rfl, rfl, rfl⟩

end Geodesic
end Riemannian
