import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3PiecewiseTransport
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Segmenting a broken curve from local regularity only

`DoCarmoCh3PiecewiseTransport.lean` proves do Carmo's Definition 3.1 sentence
"parallel transport extends to such curves by transporting successively over each
differentiable segment" for a curve carrying a `Segmentation`: a family of
curves, each `C^1` on **all of `ℝ`**, agreeing with the broken curve on its
piece.  That file's docstring flags the strength of the hypothesis as the
remaining gap:

> The hypothesis is genuinely stronger than `C`'s own `ContMDiffOn` pieces, which
> give differentiability only *within* the closed piece; it asks each piece to be
> cut out of a curve differentiable in a neighbourhood.

This file closes the gap in the honest direction.  Global differentiability of a
segment is **not** an extra geometric assumption: it is a reparametrization of
one that is local.  If each piece is cut out of a curve `C^1` merely on some
*open neighbourhood* of that closed piece, a segmentation exists.

Everything here is at order `1`, which is where `Segmentation` is stated and is
all the transport theorems consume.  The bound is real rather than an omission:
`reparam` is `C^1` and not `C^2` (`hasDerivAt_reparamDeriv_leftBranch`), so a
higher-order version needs a profile whose derivative meets `1` to higher order,
not merely this argument re-run.

One trap is worth naming, since falling into it makes the result vacuous.  The
local hypothesis must be on the **segment**, not on the broken curve: an open set
containing the closed piece `[τ i, τ (i+1)]` also contains a left-neighbourhood of
`τ i`, so asking the *curve* to be `C^1` there forces differentiability at the
breakpoint and thereby excludes every curve with a corner — the only curves
Definition 3.1 is about.  `local_hypothesis_on_curve_forbids_corner` and
`not_exists_contDiffOn_nbhd_abs` record this, and `exists_segment_for_abs` checks
that the corrected form does admit a curve with a corner.

## Why a reparametrization, and not an extension

The naive fix is to extend the curve past the piece.  The usual tool for that —
multiply by a bump function so the extension decays to `0` outside — is not
available for a curve valued in `M`: it needs a zero and a convex combination in
the target, and a bare manifold has neither.  (That is a statement about the
tool, not an impossibility proof: an extension can certainly exist, e.g. by
following a geodesic, at the cost of completeness or a local-existence argument.
The point is only that reparametrizing is cheaper and needs nothing.)

What can be reshaped without any structure on the target is the **domain**.
`reparam a b d` is a `C^1` map `ℝ → ℝ` which

* is the **identity** on `[a, b]` (`reparam_eqOn_Icc`), so precomposition does
  not disturb the curve on the piece; and
* has **range inside `(a - d, b + d)`** (`reparam_mem_Ioo`), so precomposition
  never evaluates the curve outside the neighbourhood where it is regular.

Concretely `reparam` follows `t` on `[a, b]` and relaxes exponentially onto the
asymptotes `a - d` and `b + d` outside it:

`reparam t = a - d + d·exp((t-a)/d)` for `t ≤ a`, `= t` on `[a, b]`, and
`= b + d - d·exp(-(t-b)/d)` for `t ≥ b`.

The exponential is chosen because its value **and** its derivative match the
identity's at the junctions (`exp 0 = 1` in both slots), which is exactly what
makes the glued map `C^1` there — the two endpoint lemmas
`hasDerivAt_reparam_left_endpoint` / `_right_endpoint` are where that is proved,
by taking the two one-sided derivatives and `Iic ∪ Ici = univ`.

Then `γ ∘ reparam` is `C^1` on all of `ℝ` and agrees with `γ` on `[a, b]`, which
is precisely a segment.  `Segmentation.ofLocal` assembles one piece at a time.

## What this buys, stated exactly

`local_of_segmentation` is the converse of `ofLocal`, so the two hypothesis
classes are **equivalent**: no subdivided curve satisfies the local form and fails
`Segmentation`.  This is therefore *not* a widening of what can be proved, and
saying otherwise would be wrong.  What it is:

* a statement that requiring each segment to be defined for all time **costs no
  generality** — the global form looked like an extra geometric assumption and is
  not one; and
* a convenience: a caller holding only a segment defined near the piece (a
  geodesic in an **incomplete** manifold, say) can invoke the transport theorems
  without constructing global segments by hand, because `reparam` does it.

`exists_isPiecewiseParallelAlong_of_local` and
`piecewiseTransport_injective_of_local` are that convenience for the relation and
for the map; neither proves anything the originals did not.
-/

open Set Riemannian Riemannian.Variation
open scoped ContDiff Manifold Topology

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Riemannian.Geodesic

/-! ### The reparametrization -/

/-- **Math.** A `C^1` reshaping of the line which is the identity on `[a, b]` and
whose range stays inside `(a - d, b + d)`: it follows `t` on the piece and
relaxes exponentially onto the asymptotes `a - d`, `b + d` outside it.

Precomposing a curve with this map therefore leaves the curve unchanged on
`[a, b]` while never evaluating it outside `(a - d, b + d)`.

`C^1` and no better, which is worth stating since the branches are individually
`C^∞`: at the junction `a` the left branch's second derivative is `1/d` while the
identity's is `0`, and those never agree, so `reparam` is genuinely not `C^2`.
That caps `Segmentation.ofLocal` at order one — enough for it, since
`Segmentation` is stated at order `1`, but it is the reason a higher-order version
would need a different profile (one whose derivative meets `1` to higher order). -/
def reparam (a b d : ℝ) : ℝ → ℝ := fun t =>
  if t ≤ a then a - d + d * Real.exp ((t - a) / d)
  else if t ≤ b then t
  else b + d - d * Real.exp (-((t - b) / d))

/-- **Math.** The derivative of `reparam a b d`, in the same three-branch shape.
It equals `1` on `[a, b]` — the junction values `exp 0 = 1` are what make the
glued map differentiable at `a` and `b`. -/
def reparamDeriv (a b d : ℝ) : ℝ → ℝ := fun t =>
  if t ≤ a then Real.exp ((t - a) / d)
  else if t ≤ b then 1
  else Real.exp (-((t - b) / d))

/-- **Math.** Why the exponential profile rather than the obvious cheap one:
**clamping is not `C^1`.**  `fun t => max a (min t b)` is the identity on `[a, b]`
with range in `[a, b]`, so it meets the two requirements above — but it has a
corner at each endpoint, where the derivative jumps from `0` to `1`.  Composing
with it would reintroduce exactly the non-differentiability this file exists to
avoid.

Stated at `a = 0`, `b = 1` since the obstruction is local and scale-free. -/
theorem not_differentiableAt_clamp :
    ¬ DifferentiableAt ℝ (fun t : ℝ => max 0 (min t 1)) 0 := by
  intro hd
  have hL : HasDerivWithinAt (fun t : ℝ => max 0 (min t 1)) 0 (Iic 0) 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
      (fun s hs => ?_) ?_
    · have hs0 : s ≤ 0 := hs
      rw [min_eq_left (by linarith : s ≤ 1), max_eq_left hs0]
    · simp
  have hR' : HasDerivWithinAt (fun t : ℝ => max 0 (min t 1)) 1 (Icc 0 1) 0 := by
    refine (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.congr (fun s hs => ?_) ?_
    · show max 0 (min s 1) = id s
      rw [min_eq_left hs.2, max_eq_right hs.1, id]
    · simp
  have hR : HasDerivWithinAt (fun t : ℝ => max 0 (min t 1)) 1 (Ici 0) 0 :=
    hR'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE zero_lt_one)
  have h1 := hd.hasDerivAt
  have e1 : deriv (fun t : ℝ => max 0 (min t 1)) 0 = 0 :=
    (uniqueDiffOn_Iic 0 0 self_mem_Iic).eq_deriv _ h1.hasDerivWithinAt hL
  have e2 : deriv (fun t : ℝ => max 0 (min t 1)) 0 = 1 :=
    (uniqueDiffOn_Ici 0 0 self_mem_Ici).eq_deriv _ h1.hasDerivWithinAt hR
  rw [e1] at e2
  exact zero_ne_one e2

/-- **Math.** `reparam` is the identity on the piece, so precomposition does not
move the curve there. -/
theorem reparam_eqOn_Icc (a b d : ℝ) : EqOn (reparam a b d) id (Icc a b) := by
  intro t ht
  simp only [reparam, id]
  split_ifs with h1 h2
  · rw [show t = a from le_antisymm h1 ht.1]; simp
  · rfl
  · exact absurd ht.2 h2

/-- **Math.** `reparam` never leaves `(a - d, b + d)`: outside the piece each
exponential branch is bounded by its asymptote.  This is what confines the
reparametrized curve to the neighbourhood on which it is regular. -/
theorem reparam_mem_Ioo {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d) (t : ℝ) :
    reparam a b d t ∈ Ioo (a - d) (b + d) := by
  simp only [reparam]
  split_ifs with h1 h2
  · have he : Real.exp ((t - a) / d) ≤ 1 :=
      Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
    have hp : 0 < Real.exp ((t - a) / d) := Real.exp_pos _
    constructor <;> nlinarith
  · exact ⟨by linarith, by linarith⟩
  · have hp : 0 < Real.exp (-((t - b) / d)) := Real.exp_pos _
    have he : Real.exp (-((t - b) / d)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      simp only [neg_nonpos]
      exact div_nonneg (by linarith [not_le.1 h2]) hd.le
    constructor <;> nlinarith

/-! ### Differentiability

Away from `a` and `b` the map agrees with one smooth branch on a neighbourhood.
At the junctions the two one-sided derivatives both equal `1`, and
`Iic ∪ Ici = univ` turns that into a genuine two-sided derivative. -/

/-- **Math.** The left branch of `reparam`, as a derivative statement valid at
every `t`.  Its derivative at `a` is `exp 0 = 1`, matching the identity. -/
theorem hasDerivAt_reparam_leftBranch (a d : ℝ) (hd : 0 < d) (t : ℝ) :
    HasDerivAt (fun s => a - d + d * Real.exp ((s - a) / d))
      (Real.exp ((t - a) / d)) t := by
  have h := ((((hasDerivAt_id t).sub_const a).div_const d).exp).const_mul d
  simp only [id] at h
  have hval : d * (Real.exp ((t - a) / d) * (1 / d)) = Real.exp ((t - a) / d) := by
    field_simp
  rw [hval] at h
  exact h.const_add (a - d)

/-- **Math.** The right branch of `reparam`, likewise; its derivative at `b` is
also `1`. -/
theorem hasDerivAt_reparam_rightBranch (b d : ℝ) (hd : 0 < d) (t : ℝ) :
    HasDerivAt (fun s => b + d - d * Real.exp (-((s - b) / d)))
      (Real.exp (-((t - b) / d))) t := by
  have h := ((((hasDerivAt_id t).sub_const b).div_const d).neg.exp).const_mul d
  simp only [id, Pi.neg_apply] at h
  have hval : d * (Real.exp (-((t - b) / d)) * -(1 / d))
      = -Real.exp (-((t - b) / d)) := by field_simp
  rw [hval] at h
  simpa using h.const_sub (b + d)

/-- **Math.** `reparam` is differentiable at the left junction `a`, with
derivative `1`: the exponential branch supplies the derivative from `Iic a`, the
identity from `Icc a b`, and both are `1`. -/
theorem hasDerivAt_reparam_left_endpoint (a b d : ℝ) (hab : a < b) (hd : 0 < d) :
    HasDerivAt (reparam a b d) (reparamDeriv a b d a) a := by
  have hval : reparamDeriv a b d a = 1 := by simp [reparamDeriv]
  rw [hval]
  have hL : HasDerivWithinAt (reparam a b d) 1 (Iic a) a := by
    have h := (hasDerivAt_reparam_leftBranch a d hd a).hasDerivWithinAt (s := Iic a)
    simp only [sub_self, zero_div, Real.exp_zero] at h
    refine h.congr (fun s hs => ?_) ?_
    · have hsa : s ≤ a := hs
      simp only [reparam, if_pos hsa]
    · simp only [reparam, if_pos (le_refl a)]
  have hR' : HasDerivWithinAt (reparam a b d) 1 (Icc a b) a := by
    have h := (hasDerivAt_id a).hasDerivWithinAt (s := Icc a b)
    refine h.congr (fun s hs => ?_) ?_
    · simp only [reparam, id]
      rcases eq_or_lt_of_le hs.1 with heq | hlt
      · rw [← heq]; simp
      · rw [if_neg (not_le.2 hlt), if_pos hs.2]
    · simp only [reparam, if_pos (le_refl a), id]
      simp
  have hu := hL.union (hR'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab))
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at hu

/-- **Math.** `reparam` is differentiable at the right junction `b`, with
derivative `1`, by the mirror-image argument. -/
theorem hasDerivAt_reparam_right_endpoint (a b d : ℝ) (hab : a < b) (hd : 0 < d) :
    HasDerivAt (reparam a b d) (reparamDeriv a b d b) b := by
  have hval : reparamDeriv a b d b = 1 := by
    simp only [reparamDeriv, if_neg (not_le.2 hab), if_pos (le_refl b)]
  rw [hval]
  have hL' : HasDerivWithinAt (reparam a b d) 1 (Icc a b) b := by
    have h := (hasDerivAt_id b).hasDerivWithinAt (s := Icc a b)
    refine h.congr (fun s hs => ?_) ?_
    · simp only [reparam, id]
      rcases eq_or_lt_of_le hs.1 with heq | hlt
      · rw [← heq]; simp
      · rw [if_neg (not_le.2 hlt), if_pos hs.2]
    · simp only [reparam, id, if_neg (not_le.2 hab), if_pos (le_refl b)]
  have hR : HasDerivWithinAt (reparam a b d) 1 (Ici b) b := by
    have h := (hasDerivAt_reparam_rightBranch b d hd b).hasDerivWithinAt (s := Ici b)
    simp only [sub_self, zero_div, neg_zero, Real.exp_zero] at h
    refine h.congr (fun s hs => ?_) ?_
    · have hbs : b ≤ s := hs
      simp only [reparam]
      rcases eq_or_lt_of_le hbs with heq | hlt
      · rw [← heq, if_neg (not_le.2 hab), if_pos (le_refl b)]; simp
      · rw [if_neg (not_le.2 (by linarith : a < s)), if_neg (not_le.2 hlt)]
    · simp only [reparam, if_neg (not_le.2 hab), if_pos (le_refl b)]
      simp
  have hu := (hL'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)).union hR
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at hu

/-- **Math.** `reparam` is differentiable everywhere, with derivative
`reparamDeriv`.  Off the junctions one branch agrees with it on a neighbourhood;
at the junctions this is the two endpoint lemmas. -/
theorem hasDerivAt_reparam (a b d : ℝ) (hab : a < b) (hd : 0 < d) (t : ℝ) :
    HasDerivAt (reparam a b d) (reparamDeriv a b d t) t := by
  rcases lt_trichotomy t a with hta | hta | hta
  · have hev : reparam a b d =ᶠ[𝓝 t]
        (fun s => a - d + d * Real.exp ((s - a) / d)) := by
      filter_upwards [Iio_mem_nhds hta] with s hs
      have hsa : s ≤ a := (hs : s < a).le
      simp only [reparam, if_pos hsa]
    rw [show reparamDeriv a b d t = Real.exp ((t - a) / d) by
      simp only [reparamDeriv, if_pos hta.le]]
    exact (hasDerivAt_reparam_leftBranch a d hd t).congr_of_eventuallyEq hev
  · rw [hta]
    exact hasDerivAt_reparam_left_endpoint a b d hab hd
  · rcases lt_trichotomy t b with htb | htb | htb
    · have hev : reparam a b d =ᶠ[𝓝 t] id := by
        filter_upwards [Ioo_mem_nhds hta htb] with s hs
        exact reparam_eqOn_Icc a b d (Ioo_subset_Icc_self hs)
      rw [show reparamDeriv a b d t = 1 by
        simp only [reparamDeriv, if_neg (not_le.2 hta), if_pos htb.le]]
      exact (hasDerivAt_id t).congr_of_eventuallyEq hev
    · rw [htb]
      exact hasDerivAt_reparam_right_endpoint a b d hab hd
    · have hev : reparam a b d =ᶠ[𝓝 t]
          (fun s => b + d - d * Real.exp (-((s - b) / d))) := by
        filter_upwards [Ioi_mem_nhds htb] with s hs
        have hbs : b < s := hs
        simp only [reparam, if_neg (not_le.2 (by linarith : a < s)),
          if_neg (not_le.2 hbs)]
      rw [show reparamDeriv a b d t = Real.exp (-((t - b) / d)) by
        simp only [reparamDeriv, if_neg (not_le.2 (by linarith : a < t)),
          if_neg (not_le.2 htb)]]
      exact (hasDerivAt_reparam_rightBranch b d hd t).congr_of_eventuallyEq hev

/-- **Math.** `reparamDeriv` is continuous: three continuous branches agreeing at
the junctions, glued on `Iic a ∪ Icc a b ∪ Ici b = ℝ`. -/
theorem continuous_reparamDeriv (a b d : ℝ) (hab : a < b) :
    Continuous (reparamDeriv a b d) := by
  have hcL : Continuous (fun t : ℝ => Real.exp ((t - a) / d)) :=
    Real.continuous_exp.comp ((continuous_id.sub continuous_const).div_const d)
  have hcR : Continuous (fun t : ℝ => Real.exp (-((t - b) / d))) :=
    Real.continuous_exp.comp (((continuous_id.sub continuous_const).div_const d).neg)
  have hc1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc a b) := continuousOn_const
  have h1 : ContinuousOn (reparamDeriv a b d) (Iic a) :=
    hcL.continuousOn.congr (fun s hs => by
      have hsa : s ≤ a := hs
      simp only [reparamDeriv, if_pos hsa])
  have h2 : ContinuousOn (reparamDeriv a b d) (Icc a b) :=
    hc1.congr (fun s hs => by
      simp only [reparamDeriv]
      rcases eq_or_lt_of_le hs.1 with heq | hlt
      · rw [if_pos heq.ge, ← heq]; simp
      · rw [if_neg (not_le.2 hlt), if_pos hs.2])
  have h3 : ContinuousOn (reparamDeriv a b d) (Ici b) :=
    hcR.continuousOn.congr (fun s hs => by
      have hbs : b ≤ s := hs
      simp only [reparamDeriv]
      rcases eq_or_lt_of_le hbs with heq | hlt
      · rw [← heq, if_neg (not_le.2 hab), if_pos (le_refl b)]; simp
      · rw [if_neg (not_le.2 (by linarith : a < s)), if_neg (not_le.2 hlt)])
  have h12 := h1.union_of_isClosed h2 isClosed_Iic isClosed_Icc
  rw [Iic_union_Icc_eq_Iic hab.le] at h12
  have hall := h12.union_of_isClosed h3 isClosed_Iic isClosed_Ici
  rw [Iic_union_Ici, continuousOn_univ] at hall
  exact hall

/-- **Math.** The exact regularity of `reparam` is `C^1`: at the junction `a` the
left branch's second derivative is `1/d`, while on `[a, b]` the map is the
identity and its second derivative is `0`.  Since `1/d ≠ 0`, the two one-sided
second derivatives disagree and `reparamDeriv` is not differentiable at `a`.

Recorded as the two one-sided values rather than as a `¬ ContDiff 2` statement,
which is what a consumer needing higher order would have to work around.  No
positivity of `d` is needed for the value itself. -/
theorem hasDerivAt_reparamDeriv_leftBranch (a d : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp ((t - a) / d)) (1 / d) a := by
  have h := (((hasDerivAt_id a).sub_const a).div_const d).exp
  simp only [id, sub_self, zero_div, Real.exp_zero] at h
  simpa using h

/-- **Math.** `reparamDeriv` is **not differentiable at the junction** `a`: its
left derivative there is `1/d` (the exponential branch) and its right derivative
is `0` (the identity branch), and `1/d ≠ 0`.

This is the sharpness statement proper, about `reparam`'s own derivative rather
than about one branch in isolation — the distinction matters, since a lemma about
`exp ((t-a)/d)` alone says nothing about the glued map. -/
theorem not_differentiableAt_reparamDeriv (a b d : ℝ) (hab : a < b) (hd : 0 < d) :
    ¬ DifferentiableAt ℝ (reparamDeriv a b d) a := by
  intro hdiff
  have hL : HasDerivWithinAt (reparamDeriv a b d) (1 / d) (Iic a) a := by
    have h := (hasDerivAt_reparamDeriv_leftBranch a d).hasDerivWithinAt (s := Iic a)
    refine h.congr (fun s hs => ?_) ?_
    · have hsa : s ≤ a := hs
      simp only [reparamDeriv, if_pos hsa]
    · simp only [reparamDeriv, if_pos (le_refl a)]
  have hR' : HasDerivWithinAt (reparamDeriv a b d) 0 (Icc a b) a := by
    have h := (hasDerivAt_const a (1 : ℝ)).hasDerivWithinAt (s := Icc a b)
    refine h.congr (fun s hs => ?_) ?_
    · simp only [reparamDeriv]
      rcases eq_or_lt_of_le hs.1 with heq | hlt
      · rw [if_pos heq.ge, ← heq]; simp
      · rw [if_neg (not_le.2 hlt), if_pos hs.2]
    · simp only [reparamDeriv, if_pos (le_refl a)]
      simp
  have hR : HasDerivWithinAt (reparamDeriv a b d) 0 (Ici a) a :=
    hR'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
  have h1 := hdiff.hasDerivAt
  have e1 : deriv (reparamDeriv a b d) a = 1 / d :=
    (uniqueDiffOn_Iic a a self_mem_Iic).eq_deriv _ h1.hasDerivWithinAt hL
  have e2 : deriv (reparamDeriv a b d) a = 0 :=
    (uniqueDiffOn_Ici a a self_mem_Ici).eq_deriv _ h1.hasDerivWithinAt hR
  rw [e1] at e2
  exact (one_div_ne_zero hd.ne') e2

/-- **Math.** So `reparam` is **not** `C^2`: it is differentiable everywhere with
`deriv = reparamDeriv` (`hasDerivAt_reparam`), and that derivative is not
differentiable at `a`.  The `C^1` regularity established above is exactly its
regularity, not merely what was proved about it. -/
theorem not_contDiff_two_reparam (a b d : ℝ) (hab : a < b) (hd : 0 < d) :
    ¬ ContDiff ℝ 2 (reparam a b d) := by
  intro hcd
  have hderiv : deriv (reparam a b d) = reparamDeriv a b d :=
    funext fun t => (hasDerivAt_reparam a b d hab hd t).deriv
  have h1 : ContDiff ℝ 1 (deriv (reparam a b d)) :=
    (contDiff_succ_iff_deriv (n := 1)).1 (by exact_mod_cast hcd) |>.2.2
  rw [hderiv] at h1
  exact not_differentiableAt_reparamDeriv a b d hab hd
    (h1.differentiable one_ne_zero a)

/-- **Math.** `reparam` is `C^1` on the line: it is differentiable with
continuous derivative.  Not `C^2` — see
`hasDerivAt_reparamDeriv_leftBranch`. -/
theorem contDiff_reparam (a b d : ℝ) (hab : a < b) (hd : 0 < d) :
    ContDiff ℝ 1 (reparam a b d) :=
  contDiff_one_iff_deriv.2
    ⟨fun t => (hasDerivAt_reparam a b d hab hd t).differentiableAt, by
      have hderiv : deriv (reparam a b d) = reparamDeriv a b d :=
        funext fun t => (hasDerivAt_reparam a b d hab hd t).deriv
      rw [hderiv]
      exact continuous_reparamDeriv a b d hab⟩

/-- **Math.** `reparam` as a map of the model space `ℝ`, in the manifold
regularity language the transport theorems consume. -/
theorem contMDiff_reparam (a b d : ℝ) (hab : a < b) (hd : 0 < d) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (reparam a b d) :=
  contMDiff_iff_contDiff.2 (contDiff_reparam a b d hab hd)

/-! ### Segments from local regularity

A curve `C^1` on an open neighbourhood of a piece becomes, after precomposition
with `reparam`, a curve `C^1` on all of `ℝ` that still agrees with it on the
piece — that is, a segment. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Local regularity suffices for a segment.**  If `γ` is `C^1` on an
open set `U` containing `[a, b]`, then `γ ∘ reparam` is `C^1` on **all** of `ℝ`
and agrees with `γ` on `[a, b]`.

The margin `d` is produced from compactness of `[a, b]`: a thickening of it still
fits inside `U`, and `reparam`'s range is confined to that thickening.  So no
extension of `γ` is performed — the composite only ever evaluates `γ` where it
was already regular. -/
theorem exists_contMDiff_eqOn_Icc_of_contMDiffOn {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U) :
    ∃ σ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 σ ∧ EqOn σ γ (Icc a b) := by
  -- a thickening of the compact piece still fits in `U`
  obtain ⟨d, hd, hdsub⟩ := isCompact_Icc.exists_thickening_subset_open hU hsub
  have hIoo : Ioo (a - d) (b + d) ⊆ U := by
    refine subset_trans (fun t ht => ?_) hdsub
    rw [Metric.thickening_eq_biUnion_ball]
    refine mem_iUnion₂.2 ⟨min (max t a) b, ?_, ?_⟩
    · exact ⟨le_min (le_max_right t a) hab.le, min_le_right _ _⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      rcases le_total t a with hta | hta
      · rw [max_eq_right hta, min_eq_left hab.le]
        constructor <;> [linarith [ht.1]; linarith]
      · rcases le_total t b with htb | htb
        · rw [max_eq_left hta, min_eq_left htb]; constructor <;> linarith
        · rw [max_eq_left hta, min_eq_right htb]
          constructor <;> [linarith; linarith [ht.2]]
  refine ⟨γ ∘ reparam a b d, ?_, ?_⟩
  · rw [← contMDiffOn_univ]
    exact hγ.comp (contMDiff_reparam a b d hab hd).contMDiffOn
      (fun t _ => hIoo (reparam_mem_Ioo hab.le hd t))
  · intro t ht
    show γ (reparam a b d t) = γ t
    rw [reparam_eqOn_Icc a b d ht]
    rfl

/-- **Math.** **do Carmo Definition 3.1 needs only local regularity.**  A
subdivided curve carries a `Segmentation` as soon as each piece is cut out of a
curve that is `C^1` on a *neighbourhood of that piece* — not on all of `ℝ`.

**The hypothesis is on the segment, not on the broken curve.**  That distinction
is the whole content, and getting it wrong makes the statement vacuous: asking
`C.toFun` itself to be `C^1` on an open `U ⊇ [τ i, τ (i+1)]` would force it to be
differentiable *at* `τ i`, since `U` contains a left-neighbourhood of that
breakpoint.  That is precisely what a broken curve fails, so such a hypothesis
would exclude every curve with a corner — the only curves Definition 3.1 is
about.  `local_hypothesis_on_curve_forbids_corner` below proves this, which is why
`γ` here is a separate function agreeing with `C.toFun` only on the closed piece.

This closes the gap flagged in `DoCarmoCh3PiecewiseTransport.lean`: the segments
being differentiable on all of `ℝ` is not an extra geometric hypothesis but a
reparametrization of a local one.  A broken geodesic in an **incomplete**
manifold, whose segments are genuinely undefined for all time, satisfies the
local form. -/
noncomputable def Segmentation.ofLocal {C : SubdividedCurveOfOrder I 1 M}
    (hloc : ∀ i < C.n, ∃ (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧
      Icc (C.tau i) (C.tau (i + 1)) ⊆ U ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U ∧
      EqOn γ C.toFun (Icc (C.tau i) (C.tau (i + 1)))) :
    Segmentation I M C := by
  classical
  -- choose, for each piece, the reparametrized segment
  have hseg : ∀ i, ∃ σ : ℝ → M, (i < C.n → ContMDiff 𝓘(ℝ, ℝ) I 1 σ) ∧
      (i < C.n → EqOn σ C.toFun (Icc (C.tau i) (C.tau (i + 1)))) := by
    intro i
    by_cases hi : i < C.n
    · obtain ⟨γ, U, hU, hsubU, hγU, hγeq⟩ := hloc i hi
      obtain ⟨σ, hσ, hσeq⟩ :=
        exists_contMDiff_eqOn_Icc_of_contMDiffOn (I := I) (C.tau_strict i hi) hU hsubU hγU
      exact ⟨σ, fun _ => hσ, fun _ => hσeq.trans hγeq⟩
    · exact ⟨C.toFun, fun h => absurd h hi, fun h => absurd h hi⟩
  exact { seg := fun i => Classical.choose (hseg i)
          seg_contMDiff := fun i hi => (Classical.choose_spec (hseg i)).1 hi
          seg_eqOn := fun i hi => (Classical.choose_spec (hseg i)).2 hi }

/-- **Math.** Why `Segmentation.ofLocal` hypothesises a separate segment `γ`
rather than regularity of `C.toFun` itself: an open set containing the closed
piece `[τ i, τ (i+1)]` also contains a left-neighbourhood of `τ i`, so demanding
`C^1` regularity of the curve there forces it to be differentiable **at the
breakpoint**.

A curve with a genuine corner fails that, so the naive local hypothesis would
have described only unbroken curves.  Stated for the ordinary derivative, which
is the chart reading of the manifold statement. -/
theorem local_hypothesis_on_curve_forbids_corner {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    DifferentiableAt ℝ f a :=
  have hmem : a ∈ U := hsub ⟨le_refl a, hab.le⟩
  ((hf.differentiableOn one_ne_zero) a hmem).differentiableAt (hU.mem_nhds hmem)

/-- **Math.** The corner is a real obstruction, not a technicality: `|·|` has one
at `0`, so it is `C^1` on no open neighbourhood of the piece `[0, 1]` even though
it is perfectly differentiable *within* that piece.  Together with
`local_hypothesis_on_curve_forbids_corner` this is why the segment is a separate
function in `ofLocal`. -/
theorem not_exists_contDiffOn_nbhd_abs :
    ¬ ∃ U : Set ℝ, IsOpen U ∧ Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ 1 (fun t : ℝ => |t|) U := by
  rintro ⟨U, hU, hsub, hC⟩
  exact not_differentiableAt_abs_zero
    (local_hypothesis_on_curve_forbids_corner zero_lt_one hU hsub hC)

/-- **Math.** And the corrected hypothesis *is* satisfied by that same broken
curve: on the piece `[0, 1]` the identity is a segment for `|·|`, being `C^1` on a
neighbourhood and agreeing with it there.  So replacing the curve by a segment is
what makes the local form non-vacuous on exactly the curves Definition 3.1 is
about. -/
theorem exists_segment_for_abs :
    ∃ γ : ℝ → ℝ, ContDiffOn ℝ 1 γ (Ioo (-1 : ℝ) 2) ∧
      EqOn γ (fun t : ℝ => |t|) (Icc 0 1) :=
  ⟨fun t => t, contDiffOn_id, fun _ ht => (abs_of_nonneg ht.1).symm⟩

/-- **Math.** The converse of `ofLocal`: a `Segmentation` satisfies the local
hypothesis, taking `U = univ`.

Together with `ofLocal` this says the two hypothesis classes are **equivalent**,
which is the precise form of the claim.  `ofLocal` is therefore not a weakening of
what can be proved — it is the statement that asking the segments to be defined
for all time costs no generality, so a caller holding only local data need not
manufacture global segments by hand.  It also transfers non-vacuity: the broken
curve of `segmentationOfConcat` satisfies the local form. -/
theorem local_of_segmentation {C : SubdividedCurveOfOrder I 1 M}
    (S : Segmentation I M C) :
    ∀ i < C.n, ∃ (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧
      Icc (C.tau i) (C.tau (i + 1)) ⊆ U ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U ∧
      EqOn γ C.toFun (Icc (C.tau i) (C.tau (i + 1))) := fun i hi =>
  ⟨S.seg i, univ, isOpen_univ, fun _ _ => mem_univ _,
    (S.seg_contMDiff i hi).contMDiffOn, S.seg_eqOn i hi⟩

/-- **Math.** The two hypothesis classes are **equivalent**, as an `↔` rather than
as two lemmas a reader has to notice compose.

This is the statement that fixes the register for everything above: `ofLocal` is
not a weakening, and no subdivided curve satisfies the local form while failing
`Segmentation`.  What is true is that the global form — which *looks* like an
extra geometric assumption — is not one. -/
theorem nonempty_segmentation_iff_local {C : SubdividedCurveOfOrder I 1 M} :
    Nonempty (Segmentation I M C) ↔
      ∀ i < C.n, ∃ (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧
        Icc (C.tau i) (C.tau (i + 1)) ⊆ U ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U ∧
        EqOn γ C.toFun (Icc (C.tau i) (C.tau (i + 1))) :=
  ⟨fun ⟨S⟩ => local_of_segmentation S, fun h => ⟨Segmentation.ofLocal (I := I) h⟩⟩

/-- **Math.** What `ofLocal` actually buys, stated precisely.  Its input asks each
segment to be `C^1` only on a neighbourhood of its piece; a `Segmentation` asks
for `C^1` on all of `ℝ`.  These are different demands on the *supplied* function:
`t ↦ 1/t` meets the first on any piece inside `(0, ∞)` and fails the second, and
it fails it for the geometrically relevant reason — it runs off the manifold as
`t → 0`, exactly as a geodesic in an incomplete manifold does at the edge of its
interval of definition.

So the caller of `ofLocal` may supply a segment defined only near the piece, which
is what a broken geodesic in an incomplete manifold provides and what the
`Segmentation` field type by itself rejects.  What `ofLocal` proves is that this
costs nothing: the two hypothesis classes are equivalent, with the
reparametrization supplying the missing direction. -/
theorem exists_contDiffOn_nbhd_not_contDiff :
    ∃ f : ℝ → ℝ, (∀ a b : ℝ, a < b → 0 < a →
      ∃ U : Set ℝ, IsOpen U ∧ Icc a b ⊆ U ∧ ContDiffOn ℝ 1 f U) ∧
      ¬ ContDiff ℝ 1 f := by
  refine ⟨fun t => 1 / t, ?_, ?_⟩
  · intro a b _ ha
    refine ⟨Ioi 0, isOpen_Ioi, fun t ht => lt_of_lt_of_le ha ht.1, ?_⟩
    exact ContDiffOn.div contDiffOn_const contDiffOn_id fun x hx => ne_of_gt hx
  · intro hcd
    have hc : Continuous (fun t : ℝ => 1 / t) := hcd.continuous
    have h1 : Filter.Tendsto (fun t : ℝ => 1 / t) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    have h2 : Filter.Tendsto (fun t : ℝ => 1 / t) (nhdsWithin 0 (Ioi 0))
        (nhds (1 / (0 : ℝ))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact not_tendsto_nhds_of_tendsto_atTop h1 _ h2

/-- **Math.** **do Carmo Ch. 3, Definition 3.1, final form: successive parallel
transport along a broken curve, from local regularity alone.**  Given a
subdivided curve whose pieces are each `C^1` on a neighbourhood of themselves,
and a vector at the initial vertex, there is a piecewise parallel field taking
that initial value.

Since `local_of_segmentation` gives the converse, this is a convenience rather
than new content: it saves the caller from constructing the segmentation, and it
is where the reparametrization is spent. -/
theorem exists_isPiecewiseParallelAlong_of_local [I.Boundaryless]
    (g : RiemannianMetric I M) {C : SubdividedCurveOfOrder I 1 M}
    (hloc : ∀ i < C.n, ∃ (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧
      Icc (C.tau i) (C.tau (i + 1)) ⊆ U ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U ∧
      EqOn γ C.toFun (Icc (C.tau i) (C.tau (i + 1))))
    (w₀ : E) :
    ∃ w : ℕ → ℝ → E,
      IsPiecewiseParallelAlong (I := I) g (Segmentation.ofLocal (I := I) hloc) w ∧
      w 0 (C.tau 0) = w₀ :=
  exists_isPiecewiseParallelAlong (I := I) g _ w₀

/-- **Math.** The transport **map** is available from local data too, with its
structural properties intact: successive transport to each vertex is injective.

Worth stating because it is the honest measure of what `ofLocal` delivers — not
just the existence relation but the whole `piecewiseTransport` API, since `ofLocal`
produces a genuine `Segmentation` and every map result is stated for an arbitrary
one.  `metricInner_piecewiseTransport` transfers the same way. -/
theorem piecewiseTransport_injective_of_local [I.Boundaryless]
    (g : RiemannianMetric I M) {C : SubdividedCurveOfOrder I 1 M}
    (hloc : ∀ i < C.n, ∃ (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧
      Icc (C.tau i) (C.tau (i + 1)) ⊆ U ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ U ∧
      EqOn γ C.toFun (Icc (C.tau i) (C.tau (i + 1)))) :
    ∀ i ≤ C.n, Function.Injective
      (piecewiseTransport (I := I) g (Segmentation.ofLocal (I := I) hloc) i) :=
  piecewiseTransport_injective (I := I) g _

end Riemannian.Geodesic
