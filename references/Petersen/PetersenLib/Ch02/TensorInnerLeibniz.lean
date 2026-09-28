import PetersenLib.Ch02.Exercises32
import PetersenLib.Ch02.Exercises24
import PetersenLib.Ch02.CovariantAdjoint

/-!
# Petersen Ch. 2, §2.2.4 — The Leibniz rule for the tensor inner product on a
general orthonormal frame

`Exercise 2.5.32` (`exercise2_5_32`) proves the Leibniz rule
`D_X g(S,T) = g(∇_X S, T) + g(S, ∇_X T)` at a point where the orthonormal frame
`Efr` is *normal* — the connection cross terms `S(…, ∇_X Eᵢ, …)` then drop one by
one.  For **Prop. 2.2.8** (the `L²`-adjoint identity) we need the Leibniz rule to
hold at *every* point of a fixed **globally orthonormal** frame, where the cross
terms do **not** vanish individually.

The key observation (`tensorFieldMetricInner_leibniz_orthonormal`) is that the two
families of cross terms — the ones from differentiating `S` and the ones from
differentiating `T` — **cancel in pairs** by the skew-symmetry of the connection
coefficients `⟨∇_X Eₐ, E_b⟩ = -⟨∇_X E_b, Eₐ⟩` (`orthonormalFrame_cov_skew`,
which holds because `⟨Eₐ, E_b⟩ = δₐ_b` is constant).  The cancellation is
realized by the involution `(σ, l) ↦ (σ[i := l], σ i)` on index tuples.

This removes the normality hypothesis, so the pointwise Green identity underlying
Prop. 2.2.8 holds `μ`-a.e. for any smooth global orthonormal frame — discharging
the `hGreen` hypothesis of `adjoint_L2_identity` and leaving Stokes' theorem
(`hDiv`) as the sole genuine unformalized input.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2.4, §2.5 Ex. 32.
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [hm : HasMetric I M]

/-! ## Frame expansion in a tensor slot -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Expanding a tensor slot against a pointwise orthonormal frame: for a
`(0,k)`-tensor `S` and a frame `Efr` orthonormal at `p`,
`S(…, V, …) = Σ_l g(V, E_l) · S(…, E_l, …)` at `p`, the `i`-th slot expanded via
the orthonormal expansion `V = Σ_l g(V, E_l) E_l`.  Built from tensoriality
(a slot depends only on the value at `p`) and slot multilinearity. -/
theorem tensorOperator_slot_orthoExpand {k : ℕ} {S : TensorOperator I M k}
    (hS : IsTensorOperator S)
    (Efr : Fin (finrank ℝ E) → Π x : M, TangentSpace I x) {p : M}
    (horth : ∀ i j, hm.metric.metricInner p (Efr i p) (Efr j p) = if i = j then 1 else 0)
    (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k) (V : Π x : M, TangentSpace I x) :
    S (Function.update Y i V) p
      = ∑ l, hm.metric.metricInner p (V p) (Efr l p) * S (Function.update Y i (Efr l)) p := by
  classical
  have hexp : V p = ∑ l, hm.metric.metricInner p (V p) (Efr l p) • Efr l p :=
    metricInner_orthonormal_expansion horth (V p)
  -- The difference between `V` and its frame expansion vanishes at `p`.
  have hvanish : (fun q => V q - ∑ l, hm.metric.metricInner p (V p) (Efr l p) • Efr l q) p = 0 := by
    show V p - ∑ l, hm.metric.metricInner p (V p) (Efr l p) • Efr l p = 0
    rw [← hexp]; exact sub_self _
  have hz := isTensorOperator_slot_eq_zero_of_vanish hS Y i p
    (fun q => V q - ∑ l, hm.metric.metricInner p (V p) (Efr l p) • Efr l q) hvanish
  rw [hS.sub_slot] at hz
  have hsum := isTensorOperator_slot_sum_smul hS Y i
    (fun l => hm.metric.metricInner p (V p) (Efr l p)) Efr p
  rw [sub_eq_zero] at hz
  rw [hz, hsum]

/-! ## Skew-symmetry of the connection in an orthonormal frame -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The connection coefficients of a globally orthonormal frame are
skew-symmetric: `g(∇_X Eₐ, E_b) + g(∇_X E_b, Eₐ) = 0`.  This is metric
compatibility applied to the constant function `⟨Eₐ, E_b⟩ = δₐ_b`. -/
theorem orthonormalFrame_cov_skew (D : RiemannianConnection I hm.metric)
    {Efr : Fin (finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEfr : ∀ i, IsSmoothVectorField (Efr i))
    (horth : ∀ y i j, hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (X : Π x : M, TangentSpace I x) (p : M) (a b : Fin (finrank ℝ E)) :
    hm.metric.metricInner p (D.cov p (X p) (Efr a)) (Efr b p)
      + hm.metric.metricInner p (D.cov p (X p) (Efr b)) (Efr a p) = 0 := by
  have hconst : (fun q => hm.metric.metricInner q (Efr a q) (Efr b q))
      = fun _ => (if a = b then (1 : ℝ) else 0) := by
    funext q; exact horth q a b
  have hcompat := D.metric_compat (hEfr a) (hEfr b) p (X p)
  rw [dirTangent_eq_directionalDerivative, hconst, directionalDerivative_const] at hcompat
  rw [hm.metric.metricInner_comm p (Efr a p) (D.cov p (X p) (Efr b))] at hcompat
  linarith [hcompat]

/-! ## The general orthonormal Leibniz rule -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hm in
/-- The frame-tuple relabelling identity: replacing slot `i` of `E ∘ σ` by `E_l`
gives `E ∘ (σ[i := l])`. -/
theorem update_frameTuple {k : ℕ}
    (Efr : Fin (finrank ℝ E) → Π x : M, TangentSpace I x)
    (σ : Fin k → Fin (finrank ℝ E)) (i : Fin k) (l : Fin (finrank ℝ E)) :
    Function.update (fun j => Efr (σ j)) i (Efr l)
      = fun j => Efr (Function.update σ i l j) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **The general orthonormal Leibniz rule.** For a smooth *globally
orthonormal* frame `Efr` (not assumed normal at any point), the inner product of
tensors obeys the exact Leibniz rule at *every* point:
`D_X g(S,T) = g(∇_X S, T) + g(S, ∇_X T)`.  The connection cross terms
`S(…, ∇_X Eₐ, …)` do **not** vanish individually (as they do at a normal point in
`exercise2_5_32`) but cancel in pairs by the skew-symmetry
`g(∇_X Eₐ, E_b) = -g(∇_X E_b, Eₐ)` (`orthonormalFrame_cov_skew`), realized by the
slot–index swap involution.  This is the frame-independence input that upgrades
Petersen's normal-frame Green identity to hold everywhere. -/
theorem tensorFieldMetricInner_leibniz_orthonormal (D : RiemannianConnection I hm.metric)
    {k : ℕ} {S T : TensorOperator I M k} (hS : IsTensorOperator S) (hT : IsTensorOperator T)
    {Efr : Fin (finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEfr : ∀ i, IsSmoothVectorField (Efr i))
    (horth : ∀ y i j, hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (X : Π x : M, TangentSpace I x) (p : M) :
    directionalDerivative X (tensorFieldMetricInner Efr S T) p
      = tensorFieldMetricInner Efr (covariantDerivativeTensor D.toAffineConnection X S) T p
        + tensorFieldMetricInner Efr S (covariantDerivativeTensor D.toAffineConnection X T) p := by
  classical
  have hSsm : ∀ σ : Fin k → Fin (finrank ℝ E), ContMDiff I 𝓘(ℝ) ∞ (S (fun j => Efr (σ j))) :=
    fun σ => hS.smooth_eval _ (fun j => hEfr (σ j))
  have hTsm : ∀ σ : Fin k → Fin (finrank ℝ E), ContMDiff I 𝓘(ℝ) ∞ (T (fun j => Efr (σ j))) :=
    fun σ => hT.smooth_eval _ (fun j => hEfr (σ j))
  have hSdiff : ∀ σ : Fin k → Fin (finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ) (S (fun j => Efr (σ j))) p :=
    fun σ => ((hSsm σ) p).mdifferentiableAt (by decide)
  have hTdiff : ∀ σ : Fin k → Fin (finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ) (T (fun j => Efr (σ j))) p :=
    fun σ => ((hTsm σ) p).mdifferentiableAt (by decide)
  have hprod_diff : ∀ σ : Fin k → Fin (finrank ℝ E), MDifferentiableAt I 𝓘(ℝ)
      (fun x => S (fun j => Efr (σ j)) x * T (fun j => Efr (σ j)) x) p :=
    fun σ => (hSdiff σ).mul (hTdiff σ)
  -- CRUX: the per-slot cross-term cancellation via skew-symmetry.
  have hcancel : ∀ i : Fin k,
      (∑ σ : Fin k → Fin (finrank ℝ E),
          S (Function.update (fun j => Efr (σ j)) i
            (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p
          * T (fun j => Efr (σ j)) p)
        + (∑ σ : Fin k → Fin (finrank ℝ E),
          S (fun j => Efr (σ j)) p
          * T (Function.update (fun j => Efr (σ j)) i
            (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p) = 0 := by
    intro i
    -- the slot–index swap involution `(σ, l) ↦ (σ[i := l], σ i)`
    have hinv : Function.Involutive
        (fun q : (Fin k → Fin (finrank ℝ E)) × Fin (finrank ℝ E) =>
          (Function.update q.1 i q.2, q.1 i)) := by
      intro q
      obtain ⟨σ, l⟩ := q
      simp only [Prod.mk.injEq]
      exact ⟨by rw [Function.update_idem, Function.update_eq_self],
        Function.update_self i l σ⟩
    -- frame-expand a `∇`-cross slot of a `(0,k)`-tensor against the frame
    have hexpand : ∀ (U : TensorOperator I M k), IsTensorOperator U →
        ∀ σ : Fin k → Fin (finrank ℝ E),
        U (Function.update (fun j => Efr (σ j)) i
            (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p
          = ∑ l, hm.metric.metricInner p (D.cov p (X p) (Efr (σ i))) (Efr l p)
              * U (fun j => Efr (Function.update σ i l j)) p := by
      intro U hU σ
      rw [tensorOperator_slot_orthoExpand hU Efr (fun a b => horth p a b) (fun j => Efr (σ j)) i
          (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [AffineConnection.covField_apply, update_frameTuple]
    -- both sums as product-type double sums
    have hP : (∑ σ : Fin k → Fin (finrank ℝ E),
          S (Function.update (fun j => Efr (σ j)) i
            (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p
            * T (fun j => Efr (σ j)) p)
        = ∑ q : (Fin k → Fin (finrank ℝ E)) × Fin (finrank ℝ E),
            hm.metric.metricInner p (D.cov p (X p) (Efr (q.1 i))) (Efr q.2 p)
              * S (fun j => Efr (Function.update q.1 i q.2 j)) p * T (fun j => Efr (q.1 j)) p := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [hexpand S hS σ, Finset.sum_mul]
    have hQ : (∑ σ : Fin k → Fin (finrank ℝ E),
          S (fun j => Efr (σ j)) p
            * T (Function.update (fun j => Efr (σ j)) i
              (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p)
        = ∑ q : (Fin k → Fin (finrank ℝ E)) × Fin (finrank ℝ E),
            hm.metric.metricInner p (D.cov p (X p) (Efr (q.1 i))) (Efr q.2 p)
              * S (fun j => Efr (q.1 j)) p * T (fun j => Efr (Function.update q.1 i q.2 j)) p := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [hexpand T hT σ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hP, hQ, ← Equiv.sum_comp hinv.toPerm
        (fun q : (Fin k → Fin (finrank ℝ E)) × Fin (finrank ℝ E) =>
          hm.metric.metricInner p (D.cov p (X p) (Efr (q.1 i))) (Efr q.2 p)
            * S (fun j => Efr (q.1 j)) p * T (fun j => Efr (Function.update q.1 i q.2 j)) p),
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun q _ => ?_)
    simp only [Function.Involutive.coe_toPerm, Function.update_self, Function.update_idem,
      Function.update_eq_self]
    have hsk := orthonormalFrame_cov_skew D hEfr horth X p (q.1 i) q.2
    linear_combination (S (fun j => Efr (Function.update q.1 i q.2 j)) p
      * T (fun j => Efr (q.1 j)) p) * hsk
  -- per-σ product rule (cross terms retained)
  have key : ∀ σ : Fin k → Fin (finrank ℝ E),
      directionalDerivative X (fun q => S (fun j => Efr (σ j)) q * T (fun j => Efr (σ j)) q) p
        = (covariantDerivativeTensor D.toAffineConnection X S (fun j => Efr (σ j)) p
            * T (fun j => Efr (σ j)) p
          + S (fun j => Efr (σ j)) p
            * covariantDerivativeTensor D.toAffineConnection X T (fun j => Efr (σ j)) p)
          + ((∑ i, S (Function.update (fun j => Efr (σ j)) i
                (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p)
              * T (fun j => Efr (σ j)) p
            + S (fun j => Efr (σ j)) p
              * (∑ i, T (Function.update (fun j => Efr (σ j)) i
                (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p)) := by
    intro σ
    have hSform := covariantDerivativeTensor_formula D.toAffineConnection X S (fun j => Efr (σ j)) p
    have hTform := covariantDerivativeTensor_formula D.toAffineConnection X T (fun j => Efr (σ j)) p
    rw [eq_sub_iff_add_eq] at hSform hTform
    show directionalDerivative X (S (fun j => Efr (σ j)) * T (fun j => Efr (σ j))) p = _
    rw [directionalDerivative_mul (hSdiff σ) (hTdiff σ) X, ← hSform, ← hTform]
    ring
  -- assemble
  unfold tensorFieldMetricInner
  have hrw : (fun x => ∑ σ : Fin k → Fin (finrank ℝ E),
        S (fun j => Efr (σ j)) x * T (fun j => Efr (σ j)) x)
      = fun x => ∑ σ ∈ (Finset.univ : Finset (Fin k → Fin (finrank ℝ E))),
          (fun q => S (fun j => Efr (σ j)) q * T (fun j => Efr (σ j)) q) x := rfl
  rw [hrw, directionalDerivative_finset_sum (fun σ _ => hprod_diff σ) X]
  rw [Finset.sum_congr rfl (fun σ _ => key σ)]
  have hfinal : (∑ σ : Fin k → Fin (finrank ℝ E),
        (∑ i, S (Function.update (fun j => Efr (σ j)) i
          (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p)
        * T (fun j => Efr (σ j)) p)
      + (∑ σ : Fin k → Fin (finrank ℝ E),
        S (fun j => Efr (σ j)) p
        * (∑ i, T (Function.update (fun j => Efr (σ j)) i
          (D.toAffineConnection.covField X ((fun j => Efr (σ j)) i))) p)) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Finset.sum_add_distrib]
    exact hcancel i
  simp only [Finset.sum_add_distrib]
  linarith [hfinal]

end PetersenLib

end
