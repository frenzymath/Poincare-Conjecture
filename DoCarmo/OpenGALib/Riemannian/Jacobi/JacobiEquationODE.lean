import OpenGALib.Riemannian.Geodesic.LinearODE

/-!
# The Jacobi equation as a second-order linear ODE

do Carmo, *Riemannian Geometry*, Ch. 5, §2 (`def:dc-ch5-2-1`).  Along a geodesic
`γ : [0,a] → M`, a **Jacobi field** `J` satisfies the Jacobi equation

  `D²J/dt² + R(γ'(t), J(t)) γ'(t) = 0`.

do Carmo's own proof that a Jacobi field is *determined by its initial data*
`J(0), DJ/dt(0)` (and that the solution space is `2n`-dimensional) runs by
choosing a **parallel orthonormal frame** `e₁(t),…,eₙ(t)` along `γ`.  In such a
frame the covariant derivative `D/dt` becomes the ordinary derivative of the
components, the metric becomes the standard inner product, and writing
`J(t) = Σᵢ fᵢ(t) eᵢ(t)` turns the Jacobi equation into the second-order **linear**
system

  `fⱼ''(t) + Σᵢ aᵢⱼ(t) fᵢ(t) = 0`,   `aᵢⱼ(t) = ⟨R(γ',eᵢ)γ', eⱼ⟩`,

that is `f''(t) + A(t) f(t) = 0` for a continuous operator-valued coefficient
`A : ℝ → E →L[ℝ] E` (the curvature contraction in the frame).

This file develops that second-order linear ODE **abstractly**, over any complete
normed space `E`.  It is the analytic core of the existence/uniqueness clause of
`def:dc-ch5-2-1`.  The reduction is the classical order-lowering trick: pass to
the first-order system on `E × E` with state `(f, f')` and coefficient
`jacobiCompanion A`, then invoke the global linear-ODE theory of
`Riemannian.LinearODE` (existence on any compact interval + Grönwall uniqueness).

## Main results

* `Riemannian.Jacobi.IsJacobiPairOn` — `f` is a solution with velocity `v`.
* `Riemannian.Jacobi.exists_isJacobiPairOn` — existence for arbitrary initial
  data `(f₀, v₀)` on `[a,b]` (do Carmo's "there exists a `C^∞` solution").
* `Riemannian.Jacobi.IsJacobiPairOn.eqOn` — uniqueness: a solution is determined
  by `(f(a), v(a))` (do Carmo's "determined by its initial conditions").
* `Riemannian.Jacobi.IsJacobiPairOn.add`, `.smul` — the solutions form a linear
  space (do Carmo's "`2n` linearly independent Jacobi fields").

These are frame-coordinate statements; wiring them to the intrinsic geometric
Jacobi field (via a parallel orthonormal frame along `γ` and the pointwise
curvature operator `curvatureOperatorAt`) is the remaining step to close
`def:dc-ch5-2-1` and, downstream, `lem:dc-ch7-3-2` / `thm:dc-ch7-3-1`.
-/

open Set
open scoped Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Companion first-order operator** of the second-order system `f'' = -A(t) f`.
On the state `(x, y) = (f, f')` it acts by `(x, y) ↦ (y, -A(t) x)`, so that a
solution of `Ẏ = jacobiCompanion A t · Y` is exactly a pair `(f, f')` with
`f' = f'` and `(f')' = -A(t) f`. -/
def jacobiCompanion (A : ℝ → E →L[ℝ] E) (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.snd ℝ E E).prod (-(A t) ∘L ContinuousLinearMap.fst ℝ E E)

@[simp] theorem jacobiCompanion_apply (A : ℝ → E →L[ℝ] E) (t : ℝ) (p : E × E) :
    jacobiCompanion A t p = (p.2, -(A t) p.1) := rfl

/-- `f` is a **Jacobi field with (covariant) velocity `v`** for the coefficient
`A` on `[a,b]`: `f' = v` and `v' = -A(t) f`, i.e. `f'' + A(t) f = 0`. -/
def IsJacobiPairOn (A : ℝ → E →L[ℝ] E) (a b : ℝ) (f v : ℝ → E) : Prop :=
  (∀ t ∈ Icc a b, HasDerivWithinAt f (v t) (Icc a b) t) ∧
    (∀ t ∈ Icc a b, HasDerivWithinAt v (-(A t) (f t)) (Icc a b) t)

/-- A Jacobi pair `(f, v)` gives a solution of the first-order companion system. -/
theorem isSolOn_of_isJacobiPairOn {A : ℝ → E →L[ℝ] E} {a b : ℝ} {f v : ℝ → E}
    (h : IsJacobiPairOn A a b f v) :
    LinearODE.IsSolOn (jacobiCompanion A) a b (fun t => (f t, v t)) := by
  intro t ht
  have hp := (h.1 t ht).prodMk (h.2 t ht)
  simpa using hp

/-- Conversely, a solution `Y` of the companion system is a Jacobi pair
`(Y.1, Y.2)`. -/
theorem isJacobiPairOn_of_isSolOn {A : ℝ → E →L[ℝ] E} {a b : ℝ} {Y : ℝ → E × E}
    (h : LinearODE.IsSolOn (jacobiCompanion A) a b Y) :
    IsJacobiPairOn A a b (fun t => (Y t).1) (fun t => (Y t).2) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := ((ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasFDerivWithinAt t
      (h t ht).hasFDerivWithinAt).hasDerivWithinAt
    simpa using this
  · have := ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasFDerivWithinAt t
      (h t ht).hasFDerivWithinAt).hasDerivWithinAt
    simpa using this

/-- The companion operator is bounded pointwise by `max 1 ‖A t‖`. -/
theorem opNorm_jacobiCompanion_le {A : ℝ → E →L[ℝ] E} (t : ℝ) {C : ℝ}
    (hC : ‖A t‖ ≤ C) : ‖jacobiCompanion A t‖ ≤ max 1 C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (le_trans zero_le_one (le_max_left _ _)) ?_
  intro p
  rw [jacobiCompanion_apply, Prod.norm_def]
  have hp1 : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_sup_left
  have hp2 : ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_sup_right
  have hb1 : ‖p.2‖ ≤ max 1 C * ‖p‖ :=
    calc ‖p.2‖ ≤ ‖p‖ := hp2
      _ = 1 * ‖p‖ := (one_mul _).symm
      _ ≤ max 1 C * ‖p‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hb2 : ‖-(A t) p.1‖ ≤ max 1 C * ‖p‖ := by
    rw [norm_neg]
    calc ‖(A t) p.1‖ ≤ ‖A t‖ * ‖p.1‖ := (A t).le_opNorm _
      _ ≤ max 1 C * ‖p‖ :=
        mul_le_mul (le_trans hC (le_max_right _ _)) hp1 (norm_nonneg _)
          (le_trans zero_le_one (le_max_left _ _))
  exact sup_le hb1 hb2

/-- `t ↦ jacobiCompanion A t` is continuous wherever `A` is. -/
theorem continuousOn_jacobiCompanion {A : ℝ → E →L[ℝ] E} {s : Set ℝ}
    (hcont : ContinuousOn A s) : ContinuousOn (jacobiCompanion A) s := by
  have hEq : jacobiCompanion A = fun t =>
      (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E)
        + (ContinuousLinearMap.inr ℝ E E).comp
            ((-(A t)).comp (ContinuousLinearMap.fst ℝ E E)) := by
    funext t
    ext p <;>
      simp [jacobiCompanion]
  rw [hEq]
  refine continuousOn_const.add ?_
  exact continuousOn_const.clm_comp (hcont.neg.clm_comp continuousOn_const)

/-- A uniform operator-norm bound for the companion coefficient on a compact
interval, extracted from continuity of `A`. -/
theorem exists_nnnorm_bound_jacobiCompanion {A : ℝ → E →L[ℝ] E} {a b : ℝ}
    (hcont : ContinuousOn A (Icc a b)) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, ‖jacobiCompanion A t‖₊ ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨⟨max 1 C, le_trans zero_le_one (le_max_left _ _)⟩, fun t ht => ?_⟩
  rw [← NNReal.coe_le_coe]
  simpa only [coe_nnnorm, NNReal.coe_mk] using opNorm_jacobiCompanion_le t (hC t ht)

/-- **Existence (do Carmo `def:dc-ch5-2-1`).** For continuous curvature
coefficient `A` on `[a,b]` and any initial data `(f₀, v₀)` there is a Jacobi
field `f` with velocity `v`, `f a = f₀`, `v a = v₀`. -/
theorem exists_isJacobiPairOn {A : ℝ → E →L[ℝ] E} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b)) (f₀ v₀ : E) :
    ∃ f v : ℝ → E, f a = f₀ ∧ v a = v₀ ∧ IsJacobiPairOn A a b f v := by
  obtain ⟨K, hK⟩ := exists_nnnorm_bound_jacobiCompanion hcont
  obtain ⟨Y, hY0, hYd⟩ :=
    LinearODE.exists_hasDerivWithinAt_Icc hab (jacobiCompanion A) (f₀, v₀)
      (continuousOn_jacobiCompanion hcont) hK
  refine ⟨fun t => (Y t).1, fun t => (Y t).2, ?_, ?_, isJacobiPairOn_of_isSolOn hYd⟩
  · simp [hY0]
  · simp [hY0]

/-- **Uniqueness (do Carmo `def:dc-ch5-2-1`).** A Jacobi field is determined by
its initial position and velocity: two Jacobi pairs agreeing at `a` agree on
`[a,b]`. -/
theorem IsJacobiPairOn.eqOn {A : ℝ → E →L[ℝ] E} {a b : ℝ}
    (hcont : ContinuousOn A (Icc a b)) {f v g w : ℝ → E}
    (hfv : IsJacobiPairOn A a b f v) (hgw : IsJacobiPairOn A a b g w)
    (h0 : f a = g a) (h0' : v a = w a) :
    EqOn f g (Icc a b) ∧ EqOn v w (Icc a b) := by
  obtain ⟨K, hK⟩ := exists_nnnorm_bound_jacobiCompanion hcont
  have hsol : EqOn (fun t => (f t, v t)) (fun t => (g t, w t)) (Icc a b) :=
    LinearODE.IsSolOn.eqOn_of_left hK (isSolOn_of_isJacobiPairOn hfv)
      (isSolOn_of_isJacobiPairOn hgw) (by simp only [h0, h0'])
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact (Prod.ext_iff.mp (hsol ht)).1
  · exact (Prod.ext_iff.mp (hsol ht)).2

/-- The zero pair is a Jacobi pair. -/
theorem isJacobiPairOn_zero (A : ℝ → E →L[ℝ] E) (a b : ℝ) :
    IsJacobiPairOn A a b (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun t _ => ?_, fun t _ => ?_⟩
  · simpa using (hasDerivWithinAt_const t (Icc a b) (0 : E))
  · simpa using (hasDerivWithinAt_const t (Icc a b) (0 : E))

/-- **Zero solution.** A Jacobi field vanishing to first order at `a` vanishes on
all of `[a,b]` (the `2n → n+n` well-posedness with zero data). -/
theorem IsJacobiPairOn.eqOn_zero {A : ℝ → E →L[ℝ] E} {a b : ℝ}
    (hcont : ContinuousOn A (Icc a b)) {f v : ℝ → E}
    (hfv : IsJacobiPairOn A a b f v) (h0 : f a = 0) (h0' : v a = 0) :
    EqOn f (fun _ => 0) (Icc a b) :=
  (hfv.eqOn hcont (isJacobiPairOn_zero A a b) (by simpa using h0)
    (by simpa using h0')).1

/-- **Nontriviality forces `J'(a) ≠ 0` when `J(a) = 0`** (do Carmo `rem:dc-ch5-2-2`
/ the standing assumption in `lem:dc-ch7-3-2`: "since `J'(0) ≠ 0`"). A Jacobi field
that vanishes at `a` but is not identically zero has nonzero initial velocity. -/
theorem IsJacobiPairOn.velocity_ne_zero_of_left_zero {A : ℝ → E →L[ℝ] E} {a b : ℝ}
    (hcont : ContinuousOn A (Icc a b)) {f v : ℝ → E} (hfv : IsJacobiPairOn A a b f v)
    (hf0 : f a = 0) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hne : f t₀ ≠ 0) : v a ≠ 0 := by
  intro hv0
  exact hne (hfv.eqOn_zero hcont hf0 hv0 ht₀)

/-- **Superposition.** Jacobi pairs are closed under addition. -/
theorem IsJacobiPairOn.add {A : ℝ → E →L[ℝ] E} {a b : ℝ} {f v g w : ℝ → E}
    (hfv : IsJacobiPairOn A a b f v) (hgw : IsJacobiPairOn A a b g w) :
    IsJacobiPairOn A a b (fun t => f t + g t) (fun t => v t + w t) := by
  refine ⟨fun t ht => (hfv.1 t ht).add (hgw.1 t ht), fun t ht => ?_⟩
  show HasDerivWithinAt (fun t => v t + w t) (-(A t) (f t + g t)) (Icc a b) t
  rw [map_add, neg_add]
  exact (hfv.2 t ht).add (hgw.2 t ht)

/-- **Superposition.** Jacobi pairs are closed under scalar multiplication. -/
theorem IsJacobiPairOn.smul {A : ℝ → E →L[ℝ] E} {a b : ℝ} (c : ℝ) {f v : ℝ → E}
    (hfv : IsJacobiPairOn A a b f v) :
    IsJacobiPairOn A a b (fun t => c • f t) (fun t => c • v t) := by
  refine ⟨fun t ht => (hfv.1 t ht).const_smul c, fun t ht => ?_⟩
  show HasDerivWithinAt (fun t => c • v t) (-(A t) (c • f t)) (Icc a b) t
  rw [map_smul, ← smul_neg]
  exact (hfv.2 t ht).const_smul c

end Riemannian.Jacobi
