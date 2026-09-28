import DoCarmoLib.Riemannian.Connection.ParallelAlong
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3SegmentReparam

/-!
# Intrinsic parallel transport along piecewise-C1 curves

A broken curve has no two-sided velocity at a genuine corner.  The intrinsic
API therefore uses `IsParallelAlongWithinOn` on each closed piece of the broken
curve itself.  Its base and field equations both use honest within derivatives,
so bare piecewise-`C¹` regularity is sufficient and the endpoints are included.

The older extension-presented `Segmentation` API is retained as a compatibility
layer.  The new endpoint equivalence hides the chosen finite partition, and an
explicit two-presentation uniqueness theorem proves that its value is independent
of that choice.
-/

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** A piecewise parallel field along an extension-presented broken
curve.  On each closed piece the field is intrinsically parallel with
within-derivative endpoint semantics, and consecutive fields agree at their
shared vertex. -/
def IsPiecewiseParallelAlong (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C) (w : ℕ → ℝ → E) : Prop :=
  (∀ i < C.n,
      IsParallelAlongOn (I := I) g (S.seg i)
        (fun t => (w i t : TangentSpace I (S.seg i t)))
        (C.tau i) (C.tau (i + 1))) ∧
    ∀ i, i + 1 < C.n →
      w (i + 1) (C.tau (i + 1)) = w i (C.tau (i + 1))

/-- **Math.** The intrinsic segmented predicate agrees exactly with the
established corrected piecewise transport predicate, on every closed piece. -/
theorem isPiecewiseParallelAlong_iff_geodesic
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C) (w : ℕ → ℝ → E) :
    IsPiecewiseParallelAlong (I := I) g S w ↔
      Geodesic.IsPiecewiseParallelAlong (I := I) g S w :=
  Iff.rfl

/-- **Math.** An arbitrary extension-presented piecewise-`C¹` curve admits a
parallel field with any prescribed initial tangent, unique on every closed
piece. -/
theorem exists_unique_isPiecewiseParallelAlong
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C)
    (v₀ : TangentSpace I (C.toFun C.a)) :
    ∃ w : ℕ → ℝ → E,
      IsPiecewiseParallelAlong (I := I) g S w ∧
      w 0 (C.tau 0) = (v₀ : E) ∧
      ∀ w' : ℕ → ℝ → E,
        IsPiecewiseParallelAlong (I := I) g S w' →
        w' 0 (C.tau 0) = (v₀ : E) →
        ∀ i < C.n,
          EqOn (w' i) (w i) (Icc (C.tau i) (C.tau (i + 1))) := by
  obtain ⟨w, hw, hw₀⟩ :=
    Geodesic.exists_isPiecewiseParallelAlong (I := I) g S (v₀ : E)
  refine ⟨w, (isPiecewiseParallelAlong_iff_geodesic (I := I) g S w).2 hw,
    hw₀, ?_⟩
  intro w' hw' hw'₀
  exact Geodesic.isPiecewiseParallelAlong_unique (I := I) g hw
    ((isPiecewiseParallelAlong_iff_geodesic (I := I) g S w').1 hw')
    (hw'₀.trans hw₀.symm)

/-- **Math.** The same existence-and-uniqueness statement from local `C¹`
extensions of the individual pieces.  `Segmentation.ofLocal` turns precisely
this witness into the global segment extensions used above. -/
theorem exists_unique_isPiecewiseParallelAlong_ofLocal
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (hloc : ∀ i < C.n, ∃ (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧
      Icc (C.tau i) (C.tau (i + 1)) ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U ∧
      EqOn γ C.toFun (Icc (C.tau i) (C.tau (i + 1))))
    (v₀ : TangentSpace I (C.toFun C.a)) :
    ∃ w : ℕ → ℝ → E,
      IsPiecewiseParallelAlong (I := I) g
          (Geodesic.Segmentation.ofLocal (I := I) hloc) w ∧
      w 0 (C.tau 0) = (v₀ : E) ∧
      ∀ w' : ℕ → ℝ → E,
        IsPiecewiseParallelAlong (I := I) g
          (Geodesic.Segmentation.ofLocal (I := I) hloc) w' →
        w' 0 (C.tau 0) = (v₀ : E) →
        ∀ i < C.n,
          EqOn (w' i) (w i) (Icc (C.tau i) (C.tau (i + 1))) :=
  exists_unique_isPiecewiseParallelAlong (I := I) g
    (Geodesic.Segmentation.ofLocal (I := I) hloc) v₀

/-- **Math.** The model-space linear equivalence underlying endpoint transport along all
pieces. -/
noncomputable def piecewiseParallelTransportModelEquiv
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofInjectiveEndo
    (Geodesic.piecewiseTransport (I := I) g S C.n)
    (Geodesic.piecewiseTransport_injective (I := I) g S C.n le_rfl)

/-- **Math.** Parallel transport along an extension-presented piecewise-`C¹`
curve, as a freshly named linear equivalence between its actual endpoint
tangent spaces. -/
noncomputable def piecewiseParallelTransportTangentEquiv
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C) :
    TangentSpace I (C.toFun C.a) ≃ₗ[ℝ] TangentSpace I (C.toFun C.b) :=
  let P := piecewiseParallelTransportModelEquiv (I := I) g S
  { toFun := fun v => (P (v : E) : TangentSpace I (C.toFun C.b))
    invFun := fun v => (P.symm (v : E) : TangentSpace I (C.toFun C.a))
    left_inv := fun v => by
      change P.symm (P (v : E)) = (v : E)
      exact P.symm_apply_apply (v : E)
    right_inv := fun v => by
      change P (P.symm (v : E)) = (v : E)
      exact P.apply_symm_apply (v : E)
    map_add' := fun v w => by
      change P ((v : E) + (w : E)) = P (v : E) + P (w : E)
      exact P.map_add (v : E) (w : E)
    map_smul' := fun r v => by
      change P (r • (v : E)) = r • P (v : E)
      exact P.map_smul r (v : E) }

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem piecewiseParallelTransportTangentEquiv_apply
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C)
    (v : TangentSpace I (C.toFun C.a)) :
    piecewiseParallelTransportTangentEquiv (I := I) g S v =
      (Geodesic.piecewiseTransport (I := I) g S C.n (v : E) :
        TangentSpace I (C.toFun C.b)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Piecewise parallel transport is an isometry: it preserves the
Riemannian inner product between the endpoint tangent spaces. -/
theorem metricInner_piecewiseParallelTransportTangentEquiv
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C)
    (v w : TangentSpace I (C.toFun C.a)) :
    g.metricInner (C.toFun C.b)
        (piecewiseParallelTransportTangentEquiv (I := I) g S v)
        (piecewiseParallelTransportTangentEquiv (I := I) g S w) =
      g.metricInner (C.toFun C.a) v w := by
  have h := Geodesic.metricInner_piecewiseTransport (I := I) g S C.n le_rfl
    (v : E) (w : E)
  rw [C.vertex_last, C.vertex_zero] at h
  simpa only [piecewiseParallelTransportTangentEquiv_apply] using h

/-- **Math.** The endpoint equivalence computes the terminal value of every
piecewise parallel field with the prescribed initial value. -/
theorem piecewiseParallelTransportTangentEquiv_eq_terminal
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    {S : Geodesic.Segmentation I M C} {w : ℕ → ℝ → E}
    (hw : IsPiecewiseParallelAlong (I := I) g S w)
    (v₀ : TangentSpace I (C.toFun C.a))
    (h₀ : w 0 (C.tau 0) = (v₀ : E)) :
    (w (C.n - 1) (C.tau C.n) : TangentSpace I (C.toFun C.b)) =
      piecewiseParallelTransportTangentEquiv (I := I) g S v₀ := by
  have hn1 : 1 ≤ C.n := C.n_pos
  let i := C.n - 1
  have hi : i < C.n := by
    dsimp [i]
    omega
  have hisucc : i + 1 = C.n := by
    dsimp [i]
    omega
  have hwG : Geodesic.IsPiecewiseParallelAlong (I := I) g S w :=
    (isPiecewiseParallelAlong_iff_geodesic (I := I) g S w).1 hw
  have hleft : w i (C.tau i) =
      Geodesic.piecewiseTransport (I := I) g S i (v₀ : E) :=
    Geodesic.piecewiseTransport_eq_of_isPiecewiseParallelAlong
      (I := I) g hwG (v₀ : E) h₀ i hi
  have huniq := (hwG.1 i hi).eqOn_of_eq_at
    (Variation.parallelCovariantFieldSeed_isParallel (I := I) g
      (C.tau_strict i hi) (S.seg_contMDiff i hi)
      (Geodesic.piecewiseTransport (I := I) g S i (v₀ : E)))
    (Variation.isChartDifferentiableOn_of_contMDiff (I := I)
      (S.seg_contMDiff i hi))
    (fun _t _ht => (S.seg_contMDiff i hi).continuous.continuousAt)
    (left_mem_Icc.2 (C.tau_strict i hi).le)
    (by simpa only [Variation.parallelCovariantFieldSeed_left] using hleft)
  have hright := huniq (right_mem_Icc.2 (C.tau_strict i hi).le)
  have hright' : w i (C.tau C.n) =
      Variation.parallelCovariantFieldSeed (I := I) g
        (C.tau_strict i hi) (S.seg_contMDiff i hi)
        (Geodesic.piecewiseTransport (I := I) g S i (v₀ : E)) (C.tau C.n) := by
    simpa only [hisucc] using hright
  change w (C.n - 1) (C.tau C.n) =
    Geodesic.piecewiseTransport (I := I) g S C.n (v₀ : E)
  change w i (C.tau C.n) =
    Geodesic.piecewiseTransport (I := I) g S C.n (v₀ : E)
  calc
    w i (C.tau C.n) =
        Variation.parallelCovariantFieldSeed (I := I) g
          (C.tau_strict i hi) (S.seg_contMDiff i hi)
          (Geodesic.piecewiseTransport (I := I) g S i (v₀ : E)) (C.tau C.n) := hright'
    _ = Geodesic.piecewiseTransport (I := I) g S (i + 1) (v₀ : E) := by
      rw [Geodesic.piecewiseTransport_succ (I := I) g S hi]
      simp only [LinearMap.comp_apply,
        Variation.parallelCovariantTransportAlong_apply]
      congr 1
      exact congrArg C.tau hisucc.symm
    _ = Geodesic.piecewiseTransport (I := I) g S C.n (v₀ : E) := by
      rw [hisucc]

/-! ## Bare piecewise-C¹ curves: one dependent field -/

/-- **Math.** A finite strict `C¹` presentation of the bare curve `c` on `[a,b]`.
Unlike `Geodesic.Segmentation`, its pieces are the restrictions of `c` itself;
no globally differentiable extension is part of the data. -/
structure IntrinsicPiecewisePresentation (I : ModelWithCorners ℝ E H)
    (c : ℝ → M) (a b : ℝ) where
  n : ℕ
  tau : ℕ → ℝ
  n_pos : 0 < n
  tau_zero : tau 0 = a
  tau_last : tau n = b
  tau_strict : ∀ i < n, tau i < tau (i + 1)
  piecewise : ∀ i < n,
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc (tau i) (tau (i + 1)))

namespace IntrinsicPiecewisePresentation

variable {c : ℝ → M} {a b : ℝ}

/-- **Math.** Every breakpoint of an intrinsic presentation is weakly increasing in its
index. -/
theorem tau_le (P : IntrinsicPiecewisePresentation I c a b)
    {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ P.n) : P.tau i ≤ P.tau j := by
  induction j with
  | zero => exact Nat.le_zero.mp hij ▸ le_rfl
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hik
      · exact le_rfl
      · exact (ih (Nat.lt_succ_iff.mp hik) ((Nat.le_succ k).trans hjn)).trans
          (P.tau_strict k (Nat.lt_of_succ_le hjn)).le

/-- **Math.** Every breakpoint lies in the presented parameter interval. -/
theorem tau_mem_Icc (P : IntrinsicPiecewisePresentation I c a b)
    {i : ℕ} (hi : i ≤ P.n) : P.tau i ∈ Icc a b := by
  constructor
  · simpa only [P.tau_zero] using P.tau_le (Nat.zero_le i) hi
  · simpa only [P.tau_last] using P.tau_le hi le_rfl

/-- **Math.** A subdivided curve gives an intrinsic presentation by forgetting only its
redundant global continuity field. -/
def ofSubdivided (C : Geodesic.SubdividedCurveOfOrder I 1 M) :
    IntrinsicPiecewisePresentation I C.toFun C.a C.b where
  n := C.n
  tau := C.tau
  n_pos := C.n_pos
  tau_zero := C.tau_zero
  tau_last := C.tau_last
  tau_strict := C.tau_strict
  piecewise := C.piecewise

end IntrinsicPiecewisePresentation

/-- **Math.** A single dependent tangent field is parallel relative to a finite intrinsic
presentation when it is within-parallel on every closed piece. -/
def IsParallelAlongPresentation (g : RiemannianMetric I M)
    {c : ℝ → M} {a b : ℝ} (P : IntrinsicPiecewisePresentation I c a b)
    (V : ∀ t, TangentSpace I (c t)) : Prop :=
  ∀ i < P.n, IsParallelAlongWithinOn (I := I) g c V
    (P.tau i) (P.tau (i + 1))

/-- **Math.** Intrinsic parallelism along a bare piecewise-`C¹` curve.  The public object
is one dependent field along `c`; the finite presentation is existential and is
proved irrelevant below. -/
def IsIntrinsicPiecewiseParallelAlongOn (g : RiemannianMetric I M)
    (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (a b : ℝ) : Prop :=
  ∃ P : IntrinsicPiecewisePresentation I c a b,
    IsParallelAlongPresentation (I := I) g P V

namespace IsParallelAlongPresentation

variable {g : RiemannianMetric I M} {c : ℝ → M} {a b : ℝ}
  {P : IntrinsicPiecewisePresentation I c a b}
  {V W : ∀ t, TangentSpace I (c t)}

theorem add (hV : IsParallelAlongPresentation (I := I) g P V)
    (hW : IsParallelAlongPresentation (I := I) g P W) :
    IsParallelAlongPresentation (I := I) g P (fun t => V t + W t) :=
  fun i hi => (hV i hi).add (hW i hi)

theorem smul (r : ℝ) (hV : IsParallelAlongPresentation (I := I) g P V) :
    IsParallelAlongPresentation (I := I) g P (fun t => r • V t) :=
  fun i hi => (hV i hi).smul r

end IsParallelAlongPresentation

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** A global dependent field parallel on the intrinsic pieces of a
subdivided curve induces a parallel field for any extension-presented
segmentation of those same pieces. -/
theorem IsParallelAlongPresentation.toSegmentation
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C)
    {V : ∀ t, TangentSpace I (C.toFun t)}
    (hV : IsParallelAlongPresentation (I := I) g
      (IntrinsicPiecewisePresentation.ofSubdivided C) V) :
    IsPiecewiseParallelAlong (I := I) g S (fun _ t => (V t : E)) := by
  constructor
  · intro i hi
    apply (isParallelAlongOn_iff_isParallelFieldAlongOn (I := I)).2
    apply (isParallelAlongWithinOn_iff_isParallelFieldAlongOn
      (I := I) (S.seg_contMDiff i hi)).1
    exact (hV i hi).congr_curve (S.seg_eqOn i hi).symm (fun _ _ => rfl)
  · intro i hi
    rfl

/-- **Math.** Bare piecewise-`C¹` regularity supplies an intrinsic presentation. -/
theorem exists_intrinsicPiecewisePresentation
    {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b) :
    Nonempty (IntrinsicPiecewisePresentation I c a b) := by
  obtain ⟨_, n, tau, hn, hzero, hlast, hstrict, hpieces⟩ := hc
  exact ⟨⟨n, tau, hn, hzero, hlast, hstrict, hpieces⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** A fixed presentation carries one global dependent parallel field with any
prescribed initial tangent. -/
theorem exists_isParallelAlongPresentation
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (P : IntrinsicPiecewisePresentation I c a b)
    (v₀ : TangentSpace I (c a)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelAlongPresentation (I := I) g P V ∧ V a = v₀ := by
  have hmain : ∀ k : ℕ, 0 < k → k ≤ P.n →
      ∃ V : ∀ t, TangentSpace I (c t),
        (∀ i < k, IsParallelAlongWithinOn (I := I) g c V
          (P.tau i) (P.tau (i + 1))) ∧
        V (P.tau 0) = ((v₀ : E) : TangentSpace I (c (P.tau 0))) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
        intro _ hkn
        by_cases hkzero : k = 0
        · subst k
          have hzeroN : 0 < P.n := P.n_pos
          obtain ⟨V, hV, hV₀⟩ := exists_isParallelAlongWithinOn (I := I)
            (P.tau_strict 0 hzeroN) (P.piecewise 0 hzeroN)
            ((v₀ : E) : TangentSpace I (c (P.tau 0)))
          refine ⟨V, ?_, hV₀⟩
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          exact hV
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
          have hkle : k ≤ P.n := Nat.le_of_succ_le hkn
          obtain ⟨V, hV, hV₀⟩ := ih hkpos hkle
          have hklt : k < P.n := hkn
          obtain ⟨W, hW, hW₀⟩ := exists_isParallelAlongWithinOn (I := I)
            (P.tau_strict k hklt) (P.piecewise k hklt) (V (P.tau k))
          let Vg : ∀ t, TangentSpace I (c t) := fun t =>
            if t ≤ P.tau k then V t else W t
          have hVgV : ∀ i < k,
              EqOn Vg V (Icc (P.tau i) (P.tau (i + 1))) := by
            intro i hi t ht
            have hitk : P.tau (i + 1) ≤ P.tau k :=
              P.tau_le (Nat.succ_le_of_lt hi) hkle
            exact if_pos (ht.2.trans hitk)
          have hVgW : EqOn Vg W (Icc (P.tau k) (P.tau (k + 1))) := by
            intro t ht
            by_cases htk : t ≤ P.tau k
            · have hteq : t = P.tau k := le_antisymm htk ht.1
              subst t
              simp only [Vg, le_rfl, if_true, hW₀]
            · simp only [Vg, htk, if_false]
          refine ⟨Vg, ?_, ?_⟩
          · intro i hi
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | rfl
            · exact (hV i hik).congr (fun t ht => (hVgV i hik ht).symm)
            · exact hW.congr (fun t ht => (hVgW ht).symm)
          · have h0k : P.tau 0 ≤ P.tau k :=
              P.tau_le (Nat.zero_le k) hkle
            rw [show Vg (P.tau 0) = V (P.tau 0) from if_pos h0k, hV₀]
  obtain ⟨V, hV, hV₀⟩ := hmain P.n P.n_pos le_rfl
  refine ⟨V, hV, ?_⟩
  exact (congrArg V P.tau_zero).symm.trans hV₀

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Uniqueness for one fixed presentation, stated for the single dependent
field on the whole interval. -/
theorem eqOn_of_isParallelAlongPresentation
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (P : IntrinsicPiecewisePresentation I c a b)
    {V W : ∀ t, TangentSpace I (c t)}
    (hV : IsParallelAlongPresentation (I := I) g P V)
    (hW : IsParallelAlongPresentation (I := I) g P W)
    (h₀ : V a = W a) : EqOn V W (Icc a b) := by
  have hzero : V (P.tau 0) = W (P.tau 0) := by
    exact (congrArg V P.tau_zero).trans
      (h₀.trans (congrArg W P.tau_zero).symm)
  have hmain : ∀ k ≤ P.n, EqOn V W (Icc (P.tau 0) (P.tau k)) := by
    intro k hk
    induction k with
    | zero =>
        intro t ht
        have ht0 : t = P.tau 0 := le_antisymm ht.2 ht.1
        subst t
        exact hzero
    | succ k ih =>
        have hklt : k < P.n := hk
        have hleft := ih (Nat.le_of_succ_le hk)
        have hstart := hleft (right_mem_Icc.2
          (P.tau_le (Nat.zero_le k) (Nat.le_of_succ_le hk)))
        have hright := (hV k hklt).eqOn_of_eq_at (hW k hklt)
          (left_mem_Icc.2 (P.tau_strict k hklt).le) hstart
        intro t ht
        have hsplit : Icc (P.tau 0) (P.tau (k + 1)) =
            Icc (P.tau 0) (P.tau k) ∪ Icc (P.tau k) (P.tau (k + 1)) :=
          (Icc_union_Icc_eq_Icc
            (P.tau_le (Nat.zero_le k) (Nat.le_of_succ_le hk))
            (P.tau_strict k hklt).le).symm
        rw [hsplit] at ht
        exact ht.elim (fun htL => hleft htL) (fun htR => hright htR)
  simpa only [P.tau_zero, P.tau_last] using hmain P.n le_rfl

/-- **Math.** The metric pairing of two fields parallel for the same presentation is
preserved between the endpoints. -/
theorem metricInner_eq_of_isParallelAlongPresentation
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (P : IntrinsicPiecewisePresentation I c a b)
    {V W : ∀ t, TangentSpace I (c t)}
    (hV : IsParallelAlongPresentation (I := I) g P V)
    (hW : IsParallelAlongPresentation (I := I) g P W) :
    g.metricInner (c b) (V b) (W b) = g.metricInner (c a) (V a) (W a) := by
  have hmain : ∀ k ≤ P.n,
      g.metricInner (c (P.tau k)) (V (P.tau k)) (W (P.tau k)) =
        g.metricInner (c (P.tau 0)) (V (P.tau 0)) (W (P.tau 0)) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hklt : k < P.n := hk
        have hpiece := (hV k hklt).metricInner_eq (hW k hklt)
          (right_mem_Icc.2 (P.tau_strict k hklt).le)
          (left_mem_Icc.2 (P.tau_strict k hklt).le)
        exact hpiece.trans (ih (Nat.le_of_succ_le hk))
  let phi : ℝ → ℝ := fun t => g.metricInner (c t) (V t) (W t)
  exact (congrArg phi P.tau_last).symm.trans
    ((hmain P.n le_rfl).trans (congrArg phi P.tau_zero))

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Explicit presentation independence.  Two single dependent fields
which are parallel for arbitrary finite `C¹` presentations of the same bare
curve and have the same initial value agree on all of `[a,b]`. -/
theorem eqOn_of_two_intrinsicPresentations
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (P Q : IntrinsicPiecewisePresentation I c a b)
    {V W : ∀ t, TangentSpace I (c t)}
    (hV : IsParallelAlongPresentation (I := I) g P V)
    (hW : IsParallelAlongPresentation (I := I) g Q W)
    (h₀ : V a = W a) : EqOn V W (Icc a b) := by
  have walk : ∀ N : ℕ, ∀ (i j : ℕ) (x : ℝ),
      N = (P.n - i) + (Q.n - j) →
      i < P.n → j < Q.n →
      P.tau i ≤ x → x < P.tau (i + 1) →
      Q.tau j ≤ x → x < Q.tau (j + 1) →
      V x = W x → EqOn V W (Icc x b) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro i j x hN hi hj hPix hxPi hQjx hxQj hx
        let y := min (P.tau (i + 1)) (Q.tau (j + 1))
        have hxy : x < y := lt_min hxPi hxQj
        have hPnextb : P.tau (i + 1) ≤ b :=
          (P.tau_mem_Icc (Nat.succ_le_of_lt hi)).2
        have hyb : y ≤ b := (min_le_left _ _).trans hPnextb
        have hsubP : Icc x y ⊆ Icc (P.tau i) (P.tau (i + 1)) :=
          Icc_subset_Icc hPix (min_le_left _ _)
        have hsubQ : Icc x y ⊆ Icc (Q.tau j) (Q.tau (j + 1)) :=
          Icc_subset_Icc hQjx (min_le_right _ _)
        have hEqXY : EqOn V W (Icc x y) :=
          (hV i hi).eqOn_of_eq_at_of_overlap (hW j hj) hsubP hsubQ
            (left_mem_Icc.2 hxy.le) hx
        by_cases hyEq : y = b
        · simpa only [hyEq] using hEqXY
        · have hylt : y < b := lt_of_le_of_ne hyb hyEq
          have hEqY : V y = W y := hEqXY (right_mem_Icc.2 hxy.le)
          rcases lt_trichotomy (P.tau (i + 1)) (Q.tau (j + 1)) with hlt | heq | hgt
          · have hyP : y = P.tau (i + 1) := min_eq_left hlt.le
            have hiNext : i + 1 < P.n := by
              by_contra hnot
              have hiEq : i + 1 = P.n := by omega
              have : y = b := by rw [hyP, hiEq, P.tau_last]
              exact hyEq this
            have hmeasure :
                (P.n - (i + 1)) + (Q.n - j) < N := by
              rw [hN]
              omega
            have htail := ih _ hmeasure (i + 1) j y rfl hiNext hj
              (by rw [hyP])
              (by rw [hyP]; exact P.tau_strict (i + 1) hiNext)
              (hQjx.trans hxy.le)
              (by rw [hyP]; exact hlt) hEqY
            intro t ht
            have hsplit : Icc x b = Icc x y ∪ Icc y b :=
              (Icc_union_Icc_eq_Icc hxy.le hyb).symm
            rw [hsplit] at ht
            exact ht.elim (fun htL => hEqXY htL) (fun htR => htail htR)
          · have hyP : y = P.tau (i + 1) := min_eq_left heq.le
            have hiNext : i + 1 < P.n := by
              by_contra hnot
              have hiEq : i + 1 = P.n := by omega
              have : y = b := by rw [hyP, hiEq, P.tau_last]
              exact hyEq this
            have hjNext : j + 1 < Q.n := by
              by_contra hnot
              have hjEq : j + 1 = Q.n := by omega
              have : y = b := by rw [hyP, heq, hjEq, Q.tau_last]
              exact hyEq this
            have hmeasure :
                (P.n - (i + 1)) + (Q.n - (j + 1)) < N := by
              rw [hN]
              omega
            have htail := ih _ hmeasure (i + 1) (j + 1) y rfl hiNext hjNext
              (by rw [hyP])
              (by rw [hyP]; exact P.tau_strict (i + 1) hiNext)
              (by rw [hyP, heq])
              (by rw [hyP, heq]; exact Q.tau_strict (j + 1) hjNext) hEqY
            intro t ht
            have hsplit : Icc x b = Icc x y ∪ Icc y b :=
              (Icc_union_Icc_eq_Icc hxy.le hyb).symm
            rw [hsplit] at ht
            exact ht.elim (fun htL => hEqXY htL) (fun htR => htail htR)
          · have hyQ : y = Q.tau (j + 1) := min_eq_right hgt.le
            have hjNext : j + 1 < Q.n := by
              by_contra hnot
              have hjEq : j + 1 = Q.n := by omega
              have : y = b := by rw [hyQ, hjEq, Q.tau_last]
              exact hyEq this
            have hmeasure :
                (P.n - i) + (Q.n - (j + 1)) < N := by
              rw [hN]
              omega
            have htail := ih _ hmeasure i (j + 1) y rfl hi hjNext
              (hPix.trans hxy.le)
              (by rw [hyQ]; exact hgt)
              (by rw [hyQ])
              (by rw [hyQ]; exact Q.tau_strict (j + 1) hjNext) hEqY
            intro t ht
            have hsplit : Icc x b = Icc x y ∪ Icc y b :=
              (Icc_union_Icc_eq_Icc hxy.le hyb).symm
            rw [hsplit] at ht
            exact ht.elim (fun htL => hEqXY htL) (fun htR => htail htR)
  exact walk (P.n + Q.n) 0 0 a (by simp) P.n_pos Q.n_pos P.tau_zero.le
    (by simpa only [P.tau_zero] using P.tau_strict 0 P.n_pos)
    Q.tau_zero.le
    (by simpa only [Q.tau_zero] using Q.tau_strict 0 Q.n_pos) h₀

namespace IsIntrinsicPiecewiseParallelAlongOn

variable {g : RiemannianMetric I M} {c : ℝ → M} {a b : ℝ}
  {V W : ∀ t, TangentSpace I (c t)}

/-- **Math.** Presentation-independent uniqueness at the public existential predicate. -/
theorem eqOn (hV : IsIntrinsicPiecewiseParallelAlongOn (I := I) g c V a b)
    (hW : IsIntrinsicPiecewiseParallelAlongOn (I := I) g c W a b)
    (h₀ : V a = W a) : EqOn V W (Icc a b) := by
  obtain ⟨P, hVP⟩ := hV
  obtain ⟨Q, hWQ⟩ := hW
  exact eqOn_of_two_intrinsicPresentations (I := I) g P Q hVP hWQ h₀

end IsIntrinsicPiecewiseParallelAlongOn

/-- **Math.** A fixed, hidden intrinsic presentation chosen from the bare piecewise-`C¹`
witness.  All computational definitions below use this one presentation; the
two-presentation theorem above proves that the resulting public values do not
depend on the choice. -/
noncomputable def chosenIntrinsicPiecewisePresentation
    {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b) :
    IntrinsicPiecewisePresentation I c a b :=
  Classical.choice (exists_intrinsicPiecewisePresentation (I := I) hc)

/-- **Math.** The canonical single dependent parallel field along a bare piecewise-`C¹`
curve with prescribed initial tangent. -/
noncomputable def intrinsicPiecewiseParallelField
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v₀ : TangentSpace I (c a)) : ∀ t, TangentSpace I (c t) :=
  Classical.choose (exists_isParallelAlongPresentation (I := I) g
    (chosenIntrinsicPiecewisePresentation (I := I) hc) v₀)

theorem intrinsicPiecewiseParallelField_isParallel
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v₀ : TangentSpace I (c a)) :
    IsParallelAlongPresentation (I := I) g
      (chosenIntrinsicPiecewisePresentation (I := I) hc)
      (intrinsicPiecewiseParallelField (I := I) g hc v₀) :=
  (Classical.choose_spec (exists_isParallelAlongPresentation (I := I) g
    (chosenIntrinsicPiecewisePresentation (I := I) hc) v₀)).1

theorem intrinsicPiecewiseParallelField_initial
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v₀ : TangentSpace I (c a)) :
    intrinsicPiecewiseParallelField (I := I) g hc v₀ a = v₀ :=
  (Classical.choose_spec (exists_isParallelAlongPresentation (I := I) g
    (chosenIntrinsicPiecewisePresentation (I := I) hc) v₀)).2

/-- **Math.** Existence and uniqueness for a single dependent parallel field
along an arbitrary bare piecewise-`C¹` curve, including both endpoints of every
piece and the whole domain `[a,b]`. -/
theorem exists_unique_isIntrinsicPiecewiseParallelAlongOn
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v₀ : TangentSpace I (c a)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsIntrinsicPiecewiseParallelAlongOn (I := I) g c V a b ∧
      V a = v₀ ∧
      ∀ W : ∀ t, TangentSpace I (c t),
        IsIntrinsicPiecewiseParallelAlongOn (I := I) g c W a b →
        W a = v₀ → EqOn W V (Icc a b) := by
  let P := chosenIntrinsicPiecewisePresentation (I := I) hc
  let V := intrinsicPiecewiseParallelField (I := I) g hc v₀
  have hVP : IsParallelAlongPresentation (I := I) g P V :=
    intrinsicPiecewiseParallelField_isParallel (I := I) g hc v₀
  have hV₀ : V a = v₀ :=
    intrinsicPiecewiseParallelField_initial (I := I) g hc v₀
  refine ⟨V, ⟨P, hVP⟩, hV₀, ?_⟩
  intro W hW hW₀
  exact hW.eqOn ⟨P, hVP⟩ (hW₀.trans hV₀.symm)

/-- **Math.** The endpoint value of the canonical field, packaged as a linear map between
the actual endpoint tangent spaces. -/
noncomputable def intrinsicPiecewiseParallelTransportLinearMap
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b) :
    TangentSpace I (c a) →ₗ[ℝ] TangentSpace I (c b) where
  toFun v := intrinsicPiecewiseParallelField (I := I) g hc v b
  map_add' v w := by
    let P := chosenIntrinsicPiecewisePresentation (I := I) hc
    let Vv := intrinsicPiecewiseParallelField (I := I) g hc v
    let Vw := intrinsicPiecewiseParallelField (I := I) g hc w
    let Vsum := intrinsicPiecewiseParallelField (I := I) g hc (v + w)
    have hv := intrinsicPiecewiseParallelField_isParallel (I := I) g hc v
    have hw := intrinsicPiecewiseParallelField_isParallel (I := I) g hc w
    have hsum : IsParallelAlongPresentation (I := I) g P (fun t => Vv t + Vw t) :=
      hv.add hw
    have htarget : IsParallelAlongPresentation (I := I) g P Vsum :=
      intrinsicPiecewiseParallelField_isParallel (I := I) g hc (v + w)
    have hinit : Vv a + Vw a = Vsum a := by
      dsimp only [Vv, Vw, Vsum]
      rw [intrinsicPiecewiseParallelField_initial (I := I) g hc v,
        intrinsicPiecewiseParallelField_initial (I := I) g hc w,
        intrinsicPiecewiseParallelField_initial (I := I) g hc (v + w)]
    have heq := eqOn_of_isParallelAlongPresentation (I := I) g P hsum htarget hinit
    exact (heq (right_mem_Icc.2 hc.le)).symm
  map_smul' r v := by
    let P := chosenIntrinsicPiecewisePresentation (I := I) hc
    let Vv := intrinsicPiecewiseParallelField (I := I) g hc v
    let Vsmul := intrinsicPiecewiseParallelField (I := I) g hc (r • v)
    have hv := intrinsicPiecewiseParallelField_isParallel (I := I) g hc v
    have hsmul : IsParallelAlongPresentation (I := I) g P (fun t => r • Vv t) :=
      hv.smul r
    have htarget : IsParallelAlongPresentation (I := I) g P Vsmul :=
      intrinsicPiecewiseParallelField_isParallel (I := I) g hc (r • v)
    have hinit : r • Vv a = Vsmul a := by
      dsimp only [Vv, Vsmul]
      rw [intrinsicPiecewiseParallelField_initial (I := I) g hc v,
        intrinsicPiecewiseParallelField_initial (I := I) g hc (r • v)]
    have heq := eqOn_of_isParallelAlongPresentation (I := I) g P hsmul htarget hinit
    exact (heq (right_mem_Icc.2 hc.le)).symm

@[simp] theorem intrinsicPiecewiseParallelTransportLinearMap_apply
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v : TangentSpace I (c a)) :
    intrinsicPiecewiseParallelTransportLinearMap (I := I) g hc v =
      intrinsicPiecewiseParallelField (I := I) g hc v b := rfl

/-- **Math.** The canonical endpoint map preserves the Riemannian pairing. -/
theorem metricInner_intrinsicPiecewiseParallelTransportLinearMap
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v w : TangentSpace I (c a)) :
    g.metricInner (c b)
        (intrinsicPiecewiseParallelTransportLinearMap (I := I) g hc v)
        (intrinsicPiecewiseParallelTransportLinearMap (I := I) g hc w) =
      g.metricInner (c a) v w := by
  have h := metricInner_eq_of_isParallelAlongPresentation (I := I) g
    (chosenIntrinsicPiecewisePresentation (I := I) hc)
    (intrinsicPiecewiseParallelField_isParallel (I := I) g hc v)
    (intrinsicPiecewiseParallelField_isParallel (I := I) g hc w)
  simpa only [intrinsicPiecewiseParallelTransportLinearMap_apply,
    intrinsicPiecewiseParallelField_initial] using h

theorem intrinsicPiecewiseParallelTransportLinearMap_injective
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b) :
    Function.Injective (intrinsicPiecewiseParallelTransportLinearMap (I := I) g hc) := by
  intro v w hvw
  let L := intrinsicPiecewiseParallelTransportLinearMap (I := I) g hc
  have hmap : L (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hmetric := metricInner_intrinsicPiecewiseParallelTransportLinearMap
    (I := I) g hc (v - w) (v - w)
  change g.metricInner (c b) (L (v - w)) (L (v - w)) =
    g.metricInner (c a) (v - w) (v - w) at hmetric
  rw [hmap, g.metricInner_zero_left] at hmetric
  by_contra hne
  exact absurd hmetric.symm
    (g.metricInner_self_pos (c a) (v - w) (sub_ne_zero.2 hne)).ne'

/-- **Math.** Fresh intrinsic endpoint equivalence for an arbitrary bare
piecewise-`C¹` curve.  Its arguments expose only the metric and the regularity
witness, not a subdivision or segmentation. -/
noncomputable def intrinsicPiecewiseParallelTransportTangentEquiv
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b) :
    TangentSpace I (c a) ≃ₗ[ℝ] TangentSpace I (c b) :=
  LinearMap.linearEquivOfInjective
    (intrinsicPiecewiseParallelTransportLinearMap (I := I) g hc)
    (intrinsicPiecewiseParallelTransportLinearMap_injective (I := I) g hc) (by rfl)

@[simp] theorem intrinsicPiecewiseParallelTransportTangentEquiv_apply
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v : TangentSpace I (c a)) :
    intrinsicPiecewiseParallelTransportTangentEquiv (I := I) g hc v =
      intrinsicPiecewiseParallelField (I := I) g hc v b := rfl

/-- **Math.** The fresh endpoint equivalence is an isometry for the endpoint metrics. -/
theorem metricInner_intrinsicPiecewiseParallelTransportTangentEquiv
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (v w : TangentSpace I (c a)) :
    g.metricInner (c b)
        (intrinsicPiecewiseParallelTransportTangentEquiv (I := I) g hc v)
        (intrinsicPiecewiseParallelTransportTangentEquiv (I := I) g hc w) =
      g.metricInner (c a) v w := by
  simpa only [intrinsicPiecewiseParallelTransportTangentEquiv_apply,
    intrinsicPiecewiseParallelTransportLinearMap_apply] using
    metricInner_intrinsicPiecewiseParallelTransportLinearMap (I := I) g hc v w

/-- **Math.** Every intrinsic piecewise-parallel field, for any valid presentation, has
terminal value given by the fresh endpoint equivalence. -/
theorem intrinsicPiecewiseParallelTransportTangentEquiv_eq_terminal
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    {V : ∀ t, TangentSpace I (c t)}
    (hV : IsIntrinsicPiecewiseParallelAlongOn (I := I) g c V a b)
    (v₀ : TangentSpace I (c a)) (hV₀ : V a = v₀) :
    V b = intrinsicPiecewiseParallelTransportTangentEquiv (I := I) g hc v₀ := by
  rw [intrinsicPiecewiseParallelTransportTangentEquiv_apply]
  have hcanonical : IsIntrinsicPiecewiseParallelAlongOn (I := I) g c
      (intrinsicPiecewiseParallelField (I := I) g hc v₀) a b :=
    ⟨chosenIntrinsicPiecewisePresentation (I := I) hc,
      intrinsicPiecewiseParallelField_isParallel (I := I) g hc v₀⟩
  have hinit : V a = intrinsicPiecewiseParallelField (I := I) g hc v₀ a :=
    hV₀.trans (intrinsicPiecewiseParallelField_initial (I := I) g hc v₀).symm
  exact hV.eqOn hcanonical hinit (right_mem_Icc.2 hc.le)

/-- **Math.** The terminal characterization specialized to an explicitly supplied valid
presentation.  This is the public witness-independence theorem used by clients
which retain their own subdivision. -/
theorem intrinsicPiecewiseParallelTransportTangentEquiv_eq_terminal_of_presentation
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder I 1 c a b)
    (P : IntrinsicPiecewisePresentation I c a b)
    {V : ∀ t, TangentSpace I (c t)}
    (hV : IsParallelAlongPresentation (I := I) g P V)
    (v₀ : TangentSpace I (c a)) (hV₀ : V a = v₀) :
    V b = intrinsicPiecewiseParallelTransportTangentEquiv (I := I) g hc v₀ :=
  intrinsicPiecewiseParallelTransportTangentEquiv_eq_terminal
    (I := I) g hc ⟨P, hV⟩ v₀ hV₀

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Legacy segmented parallel transport and intrinsic piecewise
parallel transport have the same value at every initial tangent vector. -/
theorem piecewiseParallelTransportTangentEquiv_apply_eq_intrinsicPiecewiseParallelTransportTangentEquiv
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C)
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder
      I 1 C.toFun C.a C.b)
    (v : TangentSpace I (C.toFun C.a)) :
    piecewiseParallelTransportTangentEquiv (I := I) g S v =
      intrinsicPiecewiseParallelTransportTangentEquiv (I := I) g hc v := by
  let P := IntrinsicPiecewisePresentation.ofSubdivided C
  obtain ⟨V, hV, hV0⟩ := exists_isParallelAlongPresentation (I := I) g P v
  let w : ℕ → ℝ → E := fun _ t => (V t : E)
  have hw : IsPiecewiseParallelAlong (I := I) g S w :=
    hV.toSegmentation g S
  have hw0 : w 0 (C.tau 0) = (v : E) := by
    dsimp only [w]
    rw [C.tau_zero]
    exact congrArg (fun x : TangentSpace I (C.toFun C.a) => (x : E)) hV0
  have hl := piecewiseParallelTransportTangentEquiv_eq_terminal
    (I := I) g hw v hw0
  have hl' : V C.b =
      piecewiseParallelTransportTangentEquiv (I := I) g S v := by
    simpa only [w, C.tau_last] using hl
  have hi :=
    intrinsicPiecewiseParallelTransportTangentEquiv_eq_terminal_of_presentation
      (I := I) g hc P hV v hV0
  exact hl'.symm.trans hi

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The legacy segmentation-dependent endpoint equivalence is exactly
the intrinsic endpoint equivalence for the underlying broken curve. -/
theorem piecewiseParallelTransportTangentEquiv_eq_intrinsicPiecewiseParallelTransportTangentEquiv
    (g : RiemannianMetric I M)
    {C : Geodesic.SubdividedCurveOfOrder I 1 M}
    (S : Geodesic.Segmentation I M C)
    (hc : Geodesic.IsPiecewiseDifferentiableCurveOfOrder
      I 1 C.toFun C.a C.b) :
    piecewiseParallelTransportTangentEquiv (I := I) g S =
      intrinsicPiecewiseParallelTransportTangentEquiv (I := I) g hc := by
  ext v
  exact
    piecewiseParallelTransportTangentEquiv_apply_eq_intrinsicPiecewiseParallelTransportTangentEquiv
      (I := I) g S hc v

end Riemannian

end
