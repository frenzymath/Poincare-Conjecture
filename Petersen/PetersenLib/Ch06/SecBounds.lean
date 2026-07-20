import PetersenLib.Ch03.SectionalCurvature
import PetersenLib.Ch03.RicciSectional

/-!
# Petersen Ch. 6 — sectional curvature bounds (GTM 171, 3rd ed.)

`def:pet-ch6-sec-bounds`. Every comparison theorem of Petersen's Ch. 6 — Bonnet–Synge
(§6.3), Myers, Synge, Rauch (§6.4), the sphere theorems (§6.5) — has as its hypothesis a
*bound* on sectional curvature, `sec ≥ k`, `sec ≤ K`, or `k ≤ sec ≤ K`. Ch. 3 supplies only
the *exact* condition `HasConstantCurvature`, so none of those statements could even be
written. This file supplies the missing vocabulary.

## The design is forced by Ch. 3, not chosen

Petersen quantifies over 2-planes `σ ⊆ T_pM`; Ch. 3's `sectionalCurvature D p v w`
takes a *pair* of tangent vectors, and `HasConstantCurvature` (Ch. 3, §3.1.3) quantifies
over pairs with a `LinearIndependent ℝ ![v, w]` side condition. We match that verbatim.
Quantifying over 2-dimensional subspaces instead would be equivalent (`sec` depends only
on the plane spanned) but would need a `Submodule`-to-pair bridge at every use site and
would not defeq-match `HasConstantCurvature`, so the `HasConstantCurvature.hasSecIn`
bridge below would stop being `fun p v w hvw => ...`.

**The side condition is mandatory, not cosmetic.** `sectionalCurvature` is a quotient by
`bivectorInnerProduct g p v w v w = g(v∧w, v∧w)`, which vanishes exactly on dependent
pairs (`bivectorInnerProduct_self_eq_zero_of_not_linearIndependent`). So on a dependent
pair `sec = 0/0 = 0` by Lean's `div_zero` junk convention, and an *unconditional*
`∀ v w, k ≤ sec D p v w` would be **false for every `k > 0`** — it would silently make
`HasSecBoundedBelow D 1` uninhabited and every theorem downstream of it vacuous. This is
the trap this file is written around.

**Sign convention** (checked against Ch. 3, not assumed):
`sec(v,w) = g(R(w,v)v, w) / g(v∧w, v∧w)`, i.e. `curvatureTensorFourAt D p w v v w` over
the squared area — note the argument order `w v v w`.

## Instance discipline

The predicates and their API carry exactly the instances `sectionalCurvature` and
`HasConstantCurvature` carry (`FiniteDimensional`, `SigmaCompactSpace`, `T2Space`) and no
more, so they compose with Ch. 3 without friction. The *denominator-cleared* bridges are
segregated into their own section because `isAlgCurvatureForm_curvatureTensorFourAt`
genuinely needs the heavier context (`NeZero (finrank ℝ E)`, `I.Boundaryless`,
`CompleteSpace E`, `LocallyCompactSpace M`); paying that cost for the *definitions* would
infect every downstream statement with instances it does not need.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §6.2–§6.5.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] {g : RiemannianMetric I M}

/-! ## The pointwise predicates -/

/-- **Math.** `sec ≥ k` at `p` (`def:pet-ch6-sec-bounds`): every 2-plane in `T_pM` has
sectional curvature at least `k`. The `LinearIndependent ℝ ![v, w]` side condition is
**mandatory**: on a dependent pair `sectionalCurvature` is `0/0 = 0` by Lean's junk
convention, so the unconditional form would be false for every `k > 0`. Mirrors
`HasConstantCurvature`'s quantification exactly. -/
def HasSecBoundedBelowAt (D : RiemannianConnection I g) (p : M) (k : ℝ) : Prop :=
  ∀ v w : TangentSpace I p, LinearIndependent ℝ ![v, w] → k ≤ sectionalCurvature D p v w

/-- **Math.** `sec ≤ K` at `p` (`def:pet-ch6-sec-bounds`). See `HasSecBoundedBelowAt` on
why the linear-independence side condition cannot be dropped. -/
def HasSecBoundedAboveAt (D : RiemannianConnection I g) (p : M) (K : ℝ) : Prop :=
  ∀ v w : TangentSpace I p, LinearIndependent ℝ ![v, w] → sectionalCurvature D p v w ≤ K

/-- **Math.** `(M,g)` satisfies `sec ≥ k` (Petersen §6.3–§6.4: the hypothesis of
Bonnet–Synge, Myers and the sphere theorems). -/
def HasSecBoundedBelow (D : RiemannianConnection I g) (k : ℝ) : Prop :=
  ∀ p : M, HasSecBoundedBelowAt D p k

/-- **Math.** `(M,g)` satisfies `sec ≤ K` (Petersen §6.2, §6.4: the hypothesis of the
Cartan–Hadamard and Preissmann circle of results). -/
def HasSecBoundedAbove (D : RiemannianConnection I g) (K : ℝ) : Prop :=
  ∀ p : M, HasSecBoundedAboveAt D p K

/-- **Math.** `(M,g)` satisfies the two-sided pinch `k ≤ sec ≤ K` — the hypothesis of the
Rauch comparison theorem (Petersen §6.4) and of the pinching/sphere theorems (§6.5). -/
def HasSecIn (D : RiemannianConnection I g) (k K : ℝ) : Prop :=
  HasSecBoundedBelow D k ∧ HasSecBoundedAbove D K

/-- **Math.** `sec > 0` (Petersen §6.3, the hypothesis of Synge's theorem). This is
**not** `∃ k > 0, HasSecBoundedBelow D k` on a non-compact manifold: positive curvature
may decay to `0` at infinity without any uniform positive lower bound (the paraboloid),
so strict positivity needs its own predicate rather than being derived. -/
def HasSecPos (D : RiemannianConnection I g) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
    0 < sectionalCurvature D p v w

/-- **Math.** `sec < 0` (Petersen §6.2, the hypothesis of Preissmann's theorem). Dual to
`HasSecPos`; likewise not reducible to a uniform bound. -/
def HasSecNeg (D : RiemannianConnection I g) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
    sectionalCurvature D p v w < 0

/-! ## Basic API -/

/-- **Math.** `HasSecBoundedBelow` unfolded to a single quantifier block, for rewriting. -/
theorem hasSecBoundedBelow_iff (D : RiemannianConnection I g) (k : ℝ) :
    HasSecBoundedBelow D k ↔
      ∀ (p : M) (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
        k ≤ sectionalCurvature D p v w := Iff.rfl

/-- **Math.** `HasSecBoundedAbove` unfolded to a single quantifier block. -/
theorem hasSecBoundedAbove_iff (D : RiemannianConnection I g) (K : ℝ) :
    HasSecBoundedAbove D K ↔
      ∀ (p : M) (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
        sectionalCurvature D p v w ≤ K := Iff.rfl

/-- **Math.** Constant curvature `k` is in particular the lower bound `sec ≥ k`. The
proof is `fun p v w hvw => (h p v w hvw).ge` — definitional, because this file's
quantification was chosen to match `HasConstantCurvature`'s. -/
theorem HasConstantCurvature.hasSecBoundedBelow {D : RiemannianConnection I g} {k : ℝ}
    (h : HasConstantCurvature D k) : HasSecBoundedBelow D k :=
  fun p v w hvw => (h p v w hvw).ge

/-- **Math.** Constant curvature `k` is in particular the upper bound `sec ≤ k`. -/
theorem HasConstantCurvature.hasSecBoundedAbove {D : RiemannianConnection I g} {k : ℝ}
    (h : HasConstantCurvature D k) : HasSecBoundedAbove D k :=
  fun p v w hvw => (h p v w hvw).le

/-- **Math.** Constant curvature `k` is the degenerate pinch `k ≤ sec ≤ k`. This is the
sense in which the space forms of Ch. 5 are the boundary case of every §6.4 comparison
theorem, and the reason those theorems are sharp. -/
theorem HasConstantCurvature.hasSecIn {D : RiemannianConnection I g} {k : ℝ}
    (h : HasConstantCurvature D k) : HasSecIn D k k :=
  ⟨h.hasSecBoundedBelow, h.hasSecBoundedAbove⟩

/-- **Math.** A lower bound may be weakened. -/
theorem HasSecBoundedBelow.mono {D : RiemannianConnection I g} {k k' : ℝ}
    (h : HasSecBoundedBelow D k) (hk : k' ≤ k) : HasSecBoundedBelow D k' :=
  fun p v w hvw => hk.trans (h p v w hvw)

/-- **Math.** An upper bound may be weakened. -/
theorem HasSecBoundedAbove.mono {D : RiemannianConnection I g} {K K' : ℝ}
    (h : HasSecBoundedAbove D K) (hK : K ≤ K') : HasSecBoundedAbove D K' :=
  fun p v w hvw => (h p v w hvw).trans hK

/-- **Math.** A pinch may be widened on both sides. -/
theorem HasSecIn.mono {D : RiemannianConnection I g} {k k' K K' : ℝ}
    (h : HasSecIn D k K) (hk : k' ≤ k) (hK : K ≤ K') : HasSecIn D k' K' :=
  ⟨h.1.mono hk, h.2.mono hK⟩

/-- **Math.** Specialize a global lower bound to a point. -/
theorem HasSecBoundedBelow.at {D : RiemannianConnection I g} {k : ℝ}
    (h : HasSecBoundedBelow D k) (p : M) : HasSecBoundedBelowAt D p k := h p

/-- **Math.** Specialize a global upper bound to a point. -/
theorem HasSecBoundedAbove.at {D : RiemannianConnection I g} {K : ℝ}
    (h : HasSecBoundedAbove D K) (p : M) : HasSecBoundedAboveAt D p K := h p

/-- **Math.** A *uniform positive* lower bound gives `sec > 0` (Petersen §6.3: this is how
Myers' hypothesis feeds Synge's). The converse fails without compactness — see
`HasSecPos`. -/
theorem HasSecBoundedBelow.hasSecPos {D : RiemannianConnection I g} {k : ℝ}
    (h : HasSecBoundedBelow D k) (hk : 0 < k) : HasSecPos D :=
  fun p v w hvw => hk.trans_le (h p v w hvw)

/-- **Math.** A *uniform negative* upper bound gives `sec < 0` (Petersen §6.2). -/
theorem HasSecBoundedAbove.hasSecNeg {D : RiemannianConnection I g} {K : ℝ}
    (h : HasSecBoundedAbove D K) (hK : K < 0) : HasSecNeg D :=
  fun p v w hvw => (h p v w hvw).trans_lt hK

/-- **Math.** `sec > 0` is in particular the non-strict bound `sec ≥ 0`. -/
theorem HasSecPos.hasSecBoundedBelow {D : RiemannianConnection I g} (h : HasSecPos D) :
    HasSecBoundedBelow D 0 :=
  fun p v w hvw => (h p v w hvw).le

/-- **Math.** `sec < 0` is in particular the non-strict bound `sec ≤ 0`. -/
theorem HasSecNeg.hasSecBoundedAbove {D : RiemannianConnection I g} (h : HasSecNeg D) :
    HasSecBoundedAbove D 0 :=
  fun p v w hvw => (h p v w hvw).le

/-! ## The bridge to Ch. 3's curvature-operator bound -/

/-- **Math.** A two-sided pinch `k ≤ sec ≤ K` bounds `|sec|` by `max |k| |K|`, for
**every** pair `v, w` — with *no* linear-independence hypothesis.

The unconditional form is the whole point, and is what lets this lemma meet
`exercise3_4_30` (Petersen §3.4), whose hypothesis is literally
`∀ v w, |sectionalCurvature D p v w| ≤ k` with no side condition. A version carrying
`LinearIndependent ℝ ![v, w]` would be true but **useless**: it could not discharge that
hypothesis, i.e. the one lemma whose job is to connect this file to existing Ch. 3
material would fail to connect to it.

The dependent case is not an obstruction but a gift: there `g(v∧w, v∧w) = 0`, so
`sec = 0/0 = 0` by `div_zero`, and `|0| ≤ max |k| |K|` holds since `max |k| |K| ≥ |k| ≥ 0`.
So the junk convention that *forces* the side condition on the predicates themselves is
exactly what *removes* it here.

Tactic note for the next reader: `rw [bivectorPairing]` does **not** fire on the goal;
establish `bivectorInnerProduct g p v w v w = 0` as a `have` first, then rewrite. -/
theorem HasSecIn.abs_sectionalCurvature_le {D : RiemannianConnection I g} {k K : ℝ}
    (h : HasSecIn D k K) (p : M) (v w : TangentSpace I p) :
    |sectionalCurvature D p v w| ≤ max |k| |K| := by
  by_cases hvw : LinearIndependent ℝ ![v, w]
  · refine abs_le.mpr ⟨?_, ?_⟩
    · exact le_trans (neg_le_of_neg_le ((neg_le_abs k).trans (le_max_left _ _)))
        (h.1 p v w hvw)
    · exact (h.2 p v w hvw).trans ((le_abs_self K).trans (le_max_right _ _))
  · have hb : bivectorInnerProduct g p v w v w = 0 :=
      bivectorInnerProduct_self_eq_zero_of_not_linearIndependent g p hvw
    -- Unfold the `def` `sectionalCurvature` rather than rewriting with the `theorem`
    -- `sectionalCurvature_eq_curvatureTensorFourAt`: the latter, being a theorem, carries
    -- Ch. 3's *entire* section-variable block (`NeZero (finrank ℝ E)`, `I.Boundaryless`,
    -- `CompleteSpace E`, `LocallyCompactSpace M`) even though the def it is about carries
    -- none of it, and using it here would drag all four onto this lemma.
    simp only [sectionalCurvature, hb, div_zero, abs_zero]
    exact (abs_nonneg k).trans (le_max_left _ _)

/-! ## Denominator-cleared forms

These need the heavier context of `isAlgCurvatureForm_curvatureTensorFourAt`
(`NeZero (finrank ℝ E)`, `I.Boundaryless`, `CompleteSpace E`, `LocallyCompactSpace M`),
so they are segregated here rather than being allowed to infect the definitions above.
-/

section Cleared

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [LocallyCompactSpace M]

/-- **Math.** `sec ≤ K` at `p` with the denominator cleared:
`R(w,v,v,w) ≤ K·g(v∧w, v∧w)` for **every** pair `v, w`, no independence needed, since
both sides vanish on dependent pairs (the left by the antisymmetries of an algebraic
curvature form, the right by Cauchy–Schwarz equality). This is the form the §6.3/§6.4
Jacobi/Riccati proofs consume: a quotient cannot be manipulated under an ODE estimate,
a product can. -/
theorem HasSecBoundedAboveAt.curvatureTensorFourAt_le {D : RiemannianConnection I g}
    {p : M} {K : ℝ} (h : HasSecBoundedAboveAt D p K) (v w : TangentSpace I p) :
    curvatureTensorFourAt D p w v v w ≤ K * bivectorInnerProduct g p v w v w := by
  by_cases hvw : LinearIndependent ℝ ![v, w]
  · have hpos := bivectorInnerProduct_self_pos g p hvw
    have hs := h v w hvw
    rw [sectionalCurvature_eq_curvatureTensorFourAt, div_le_iff₀ hpos] at hs
    exact hs
  · have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
    have hz : curvatureTensorFourAt D p w v v w = 0 := by
      have h1 : curvatureTensorFourAt D p v w v w = 0 :=
        hAlg.diag_eq_zero_of_not_linearIndependent hvw
      have h2 := hAlg.antisymm₁₂ v w v w
      have h3 := hAlg.antisymm₃₄ w v v w
      linarith [h1, h2, h3]
    rw [hz, bivectorInnerProduct_self_eq_zero_of_not_linearIndependent g p hvw, mul_zero]

/-- **Math.** `sec ≥ k` at `p` with the denominator cleared:
`k·g(v∧w, v∧w) ≤ R(w,v,v,w)` for **every** pair `v, w`. Dual to
`HasSecBoundedAboveAt.curvatureTensorFourAt_le`. -/
theorem HasSecBoundedBelowAt.le_curvatureTensorFourAt {D : RiemannianConnection I g}
    {p : M} {k : ℝ} (h : HasSecBoundedBelowAt D p k) (v w : TangentSpace I p) :
    k * bivectorInnerProduct g p v w v w ≤ curvatureTensorFourAt D p w v v w := by
  by_cases hvw : LinearIndependent ℝ ![v, w]
  · have hpos := bivectorInnerProduct_self_pos g p hvw
    have hs := h v w hvw
    rw [sectionalCurvature_eq_curvatureTensorFourAt, le_div_iff₀ hpos] at hs
    exact hs
  · have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
    have hz : curvatureTensorFourAt D p w v v w = 0 := by
      have h1 : curvatureTensorFourAt D p v w v w = 0 :=
        hAlg.diag_eq_zero_of_not_linearIndependent hvw
      have h2 := hAlg.antisymm₁₂ v w v w
      have h3 := hAlg.antisymm₃₄ w v v w
      linarith [h1, h2, h3]
    rw [hz, bivectorInnerProduct_self_eq_zero_of_not_linearIndependent g p hvw, mul_zero]

/-- **Math.** Orthonormal-pair form: for `g(v,v) = g(w,w) = 1` and `g(v,w) = 0` the squared
area is `1`, so the bound reads simply `R(w,v,v,w) ≤ K`. This is the shape the Jacobi and
Riccati layers want, since the Jacobi equation along a unit-speed geodesic is naturally
written against a parallel orthonormal frame. -/
theorem HasSecBoundedAboveAt.curvatureTensorFourAt_le_of_orthonormal
    {D : RiemannianConnection I g} {p : M} {K : ℝ} (h : HasSecBoundedAboveAt D p K)
    {v w : TangentSpace I p} (hv : g.metricInner p v v = 1)
    (hw : g.metricInner p w w = 1) (hvw : g.metricInner p v w = 0) :
    curvatureTensorFourAt D p w v v w ≤ K := by
  have := h.curvatureTensorFourAt_le v w
  rwa [bivectorInnerProduct, hv, hw, hvw, g.metricInner_comm p w v, hvw,
    mul_zero, mul_one, sub_zero, mul_one] at this

/-- **Math.** Orthonormal-pair form of the lower bound: `k ≤ R(w,v,v,w)`. -/
theorem HasSecBoundedBelowAt.le_curvatureTensorFourAt_of_orthonormal
    {D : RiemannianConnection I g} {p : M} {k : ℝ} (h : HasSecBoundedBelowAt D p k)
    {v w : TangentSpace I p} (hv : g.metricInner p v v = 1)
    (hw : g.metricInner p w w = 1) (hvw : g.metricInner p v w = 0) :
    k ≤ curvatureTensorFourAt D p w v v w := by
  have := h.le_curvatureTensorFourAt v w
  rwa [bivectorInnerProduct, hv, hw, hvw, g.metricInner_comm p w v, hvw,
    mul_zero, mul_one, sub_zero, mul_one] at this

end Cleared

end PetersenLib
