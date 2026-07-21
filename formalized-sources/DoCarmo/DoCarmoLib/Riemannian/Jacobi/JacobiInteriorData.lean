import DoCarmoLib.Riemannian.Jacobi.JacobiReversal
import DoCarmoLib.Riemannian.Jacobi.JacobiRestriction
import DoCarmoLib.Riemannian.Jacobi.JacobiExistence

/-!
# Jacobi fields seeded at an interior time

The manifold existence theorem `exists_isJacobiFieldAlongOn` pins a Jacobi field
by its data at the **left endpoint** `a` of `[a, b]`. This file removes that
restriction: the data may be prescribed at an **arbitrary** `t₀ ∈ [a, b]`, the
field still living on the whole of `[a, b]`.

The obstruction is that the endpoint-seeded theorem only ever propagates
*forward*. It is removed in two steps.

**Backward uniqueness.** The Jacobi/geodesic system is invariant under `t ↦ -t`
(`IsJacobiFieldAlongOn.comp_neg`, `isGeodesicOn_comp_neg`), so the forward
uniqueness `IsJacobiFieldAlongOn.eqOn_zero` transports to the reversed field on
`[-b, -a]`, whose left endpoint carries the original data at `b`. This gives
`eqOn_zero_of_right` and, by subtraction, `eqOn_of_right`.

**Inverting the propagator.** Existence and forward uniqueness make the chosen
field `jacobiJIcc p` a linear function of its left-endpoint data `p ∈ E × E`, so
`Ψ_{t₀} : p ↦ (J(t₀), DJ(t₀))` is a linear endomorphism of `E × E`
(`jacobiPropagator`). Backward uniqueness on `[a, t₀]` says `Ψ_{t₀}` kills only
`0`, and an injective endomorphism of a finite-dimensional space is surjective;
so every prescribed pair at `t₀` is hit by some left-endpoint seed.

## Contents

* `neg_preimage_Icc` — `Neg.neg ⁻¹' [c, d] = [-d, -c]`, matching the interval
  shapes of the geodesic and Jacobi halves of the time reversal.
* `IsJacobiFieldAlongOn.eqOn_zero_of_right` — **backward uniqueness**: a Jacobi
  field along a geodesic vanishing with its covariant derivative at `b` vanishes
  on `[a, b]`.
* `IsJacobiFieldAlongOn.eqOn_of_right` — two Jacobi fields agreeing at `b` agree
  on `[a, b]`.
* `jacobiJIcc`, `jacobiDJIcc` and their API (`jacobiJIcc_spec`,
  `jacobiJIcc_isJacobiField`, `jacobiJIcc_left`, `jacobiDJIcc_left`,
  `eqOn_jacobiJIcc`) — the chosen Jacobi field with prescribed data at `a`, on a
  general interval `[a, b]` (the `[0, L]`-bound `jacobiJ` of `JacobiDimension`
  is not general enough here).
* `jacobiPropagator` (`+ _apply`, `_injective`, `_surjective`) — the linear
  propagator `(J(a), DJ(a)) ↦ (J(t₀), DJ(t₀))` and its bijectivity.
* `exists_isJacobiFieldAlongOn_at` — **interior-seeded existence**, the payload.

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer-general` (the consumer: the
variable-curvature Jacobi norm transfer needs its fields on an outer window
strictly containing the window the conclusion is read on, while
`cor:dc-ch5-2-5` pins them at the interior time `0`), `cor:dc-ch5-2-5`.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Reflection of an interval -/

/-- **Math.** The preimage of `[c, d]` under `t ↦ -t` is `[-d, -c]`.  Supplied so
that the geodesic side of the time reversal, `isGeodesicOn_comp_neg` — which
concludes on the *preimage* `Neg.neg ⁻¹' s` — can be paired with the Jacobi side
`IsJacobiFieldAlongOn.comp_neg`, which concludes on `Icc (-b) (-a)`. -/
theorem neg_preimage_Icc (c d : ℝ) :
    (Neg.neg ⁻¹' (Icc c d) : Set ℝ) = Icc (-d) (-c) := by
  rw [Set.neg_preimage, Set.neg_Icc]

section Backward

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Backward uniqueness along the geodesic**: a Jacobi field along a
geodesic vanishing together with its covariant derivative at the **right**
endpoint vanishes identically on `[a, b]`.

The mirror of `IsJacobiFieldAlongOn.eqOn_zero` (forward uniqueness), obtained
from it by time reversal: `IsJacobiFieldAlongOn.comp_neg` turns the field into a
Jacobi field on `[-b, -a]` whose *left* endpoint `-b` carries the original data
at `b`, and `isGeodesicOn_comp_neg` reverses the geodesic.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem IsJacobiFieldAlongOn.eqOn_zero_of_right
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    (hab : a ≤ b)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hJb : J b = 0) (hDJb : DJ b = 0) :
    ∀ t ∈ Icc a b, J t = 0 ∧ DJ t = 0 := by
  have hrev := hJac.comp_neg
  have hgeorev : IsGeodesicOn (I := I) g (fun t => γ (-t)) (Icc (-b) (-a)) := by
    have h := isGeodesicOn_comp_neg (I := I) hgeo
    rwa [neg_preimage_Icc] at h
  have hγcrev : ∀ t ∈ Icc (-b) (-a), ContinuousAt (fun t => γ (-t)) t := by
    intro t ht
    have hmem : -t ∈ Icc a b := by
      simp only [mem_Icc] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    exact (hγc (-t) hmem).comp continuous_neg.continuousAt
  have hz := hrev.eqOn_zero (by linarith) hgeorev hγcrev
    (by simpa using hJb) (by simpa using hDJb)
  intro t ht
  have hmem : -t ∈ Icc (-b) (-a) := by
    simp only [mem_Icc] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have h := hz (-t) hmem
  simp only [neg_neg, neg_eq_zero] at h
  exact h

/-- **Math.** **Uniqueness of Jacobi fields with prescribed terminal data**: two
Jacobi fields along a geodesic with the same value and covariant derivative at
the **right** endpoint agree on the whole of `[a, b]` (subtract and apply
`eqOn_zero_of_right`).  The mirror of `IsJacobiFieldAlongOn.eqOn_of_initial`.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem IsJacobiFieldAlongOn.eqOn_of_right
    {g : RiemannianMetric I M} {γ : ℝ → M} {J₁ DJ₁ J₂ DJ₂ : ℝ → E}
    {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (h₁ : IsJacobiFieldAlongOn (I := I) g γ J₁ DJ₁ a b)
    (h₂ : IsJacobiFieldAlongOn (I := I) g γ J₂ DJ₂ a b)
    (hJb : J₁ b = J₂ b) (hDJb : DJ₁ b = DJ₂ b) :
    ∀ t ∈ Icc a b, J₁ t = J₂ t ∧ DJ₁ t = DJ₂ t := by
  have hz := (h₁.sub hab hgeo hγc h₂).eqOn_zero_of_right hab.le hgeo hγc
    (sub_eq_zero.2 hJb) (sub_eq_zero.2 hDJb)
  intro t ht
  exact ⟨sub_eq_zero.1 (hz t ht).1, sub_eq_zero.1 (hz t ht).2⟩

end Backward

/-! ### The chosen Jacobi field with prescribed left-endpoint data on `[a, b]` -/

section Propagator

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
variable {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ}

/-- **Math.** The chosen Jacobi field `J` along `γ` on `[a, b]` with left-endpoint
data `(J(a), DJ(a)) = p`, extracted from `exists_isJacobiFieldAlongOn`.  The
general-`[a, b]` analogue of `jacobiJ` (`JacobiDimension`), which is hard-wired
to `[0, L]`. -/
def jacobiJIcc (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) (p : E × E) : ℝ → E :=
  (exists_isJacobiFieldAlongOn hab hgeo hγc p.1 p.2).choose

/-- **Math.** The covariant derivative field of `jacobiJIcc`. -/
def jacobiDJIcc (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) (p : E × E) : ℝ → E :=
  (exists_isJacobiFieldAlongOn hab hgeo hγc p.1 p.2).choose_spec.choose

variable (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
  (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)

/-- **Math.** The defining property of `jacobiJIcc` / `jacobiDJIcc`: they form a
Jacobi field on `[a, b]` taking the data `p` at `a`. -/
theorem jacobiJIcc_spec (p : E × E) :
    IsJacobiFieldAlongOn (I := I) g γ (jacobiJIcc hab hgeo hγc p)
        (jacobiDJIcc hab hgeo hγc p) a b
      ∧ jacobiJIcc hab hgeo hγc p a = p.1 ∧ jacobiDJIcc hab hgeo hγc p a = p.2 :=
  (exists_isJacobiFieldAlongOn hab hgeo hγc p.1 p.2).choose_spec.choose_spec

/-- **Math.** `(jacobiJIcc p, jacobiDJIcc p)` is a Jacobi field along `γ` on `[a, b]`. -/
theorem jacobiJIcc_isJacobiField (p : E × E) :
    IsJacobiFieldAlongOn (I := I) g γ (jacobiJIcc hab hgeo hγc p)
      (jacobiDJIcc hab hgeo hγc p) a b :=
  (jacobiJIcc_spec hab hgeo hγc p).1

/-- **Math.** `jacobiJIcc p` takes the value `p.1` at the left endpoint. -/
@[simp] theorem jacobiJIcc_left (p : E × E) : jacobiJIcc hab hgeo hγc p a = p.1 :=
  (jacobiJIcc_spec hab hgeo hγc p).2.1

/-- **Math.** `jacobiDJIcc p` takes the value `p.2` at the left endpoint. -/
@[simp] theorem jacobiDJIcc_left (p : E × E) : jacobiDJIcc hab hgeo hγc p a = p.2 :=
  (jacobiJIcc_spec hab hgeo hγc p).2.2

/-- **Math.** **Uniqueness, packaged.** Any Jacobi field on `[a, b]` with the same
left-endpoint data as `p` agrees with the chosen one on `[a, b]`.  The
general-`[a, b]` analogue of `eqOn_jacobiJ` (`JacobiDimension`). -/
theorem eqOn_jacobiJIcc {J DJ : ℝ → E} (p : E × E)
    (hJF : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (h0 : J a = p.1) (h0' : DJ a = p.2) :
    ∀ t ∈ Icc a b, J t = jacobiJIcc hab hgeo hγc p t
      ∧ DJ t = jacobiDJIcc hab hgeo hγc p t := by
  refine IsJacobiFieldAlongOn.eqOn_of_initial hab hgeo hγc hJF
    (jacobiJIcc_isJacobiField hab hgeo hγc p) ?_ ?_
  · rw [h0, jacobiJIcc_left]
  · rw [h0', jacobiDJIcc_left]

/-! ### The propagator `Ψ : (J(a), DJ(a)) ↦ (J(t₀), DJ(t₀))` -/

/-- **Math.** **The Jacobi propagator** `Ψ_{t₀} : (E × E) →ₗ[ℝ] (E × E)`, carrying the
left-endpoint data `(J(a), DJ(a))` of a Jacobi field to its data
`(J(t₀), DJ(t₀))` at a time `t₀ ∈ [a, b]`.  It is linear by superposition
(`IsJacobiFieldAlongOn.add`, `.smul`) together with forward uniqueness
(`eqOn_jacobiJIcc`): the sum of the chosen fields for `p` and `q` is *a* Jacobi
field with left-endpoint data `p + q`, hence *the* chosen one. -/
def jacobiPropagator (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) : (E × E) →ₗ[ℝ] (E × E) where
  toFun p := (jacobiJIcc hab hgeo hγc p t₀, jacobiDJIcc hab hgeo hγc p t₀)
  map_add' p q := by
    have hsum : IsJacobiFieldAlongOn (I := I) g γ
        (fun t => jacobiJIcc hab hgeo hγc p t + jacobiJIcc hab hgeo hγc q t)
        (fun t => jacobiDJIcc hab hgeo hγc p t + jacobiDJIcc hab hgeo hγc q t) a b :=
      (jacobiJIcc_isJacobiField hab hgeo hγc p).add hab hgeo hγc
        (jacobiJIcc_isJacobiField hab hgeo hγc q)
    have h := eqOn_jacobiJIcc hab hgeo hγc (p + q) hsum
      (by simp [Prod.fst_add]) (by simp [Prod.snd_add])
    exact Prod.ext ((h t₀ ht₀).1).symm ((h t₀ ht₀).2).symm
  map_smul' c p := by
    have hsm : IsJacobiFieldAlongOn (I := I) g γ
        (fun t => c • jacobiJIcc hab hgeo hγc p t)
        (fun t => c • jacobiDJIcc hab hgeo hγc p t) a b :=
      (jacobiJIcc_isJacobiField hab hgeo hγc p).smul c
    have h := eqOn_jacobiJIcc hab hgeo hγc (c • p) hsm
      (by simp [Prod.smul_fst]) (by simp [Prod.smul_snd])
    exact Prod.ext ((h t₀ ht₀).1).symm ((h t₀ ht₀).2).symm

/-- **Math.** The propagator evaluates the chosen field and its covariant derivative
at `t₀`. -/
@[simp] theorem jacobiPropagator_apply (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (p : E × E) :
    jacobiPropagator hab hgeo hγc t₀ ht₀ p
      = (jacobiJIcc hab hgeo hγc p t₀, jacobiDJIcc hab hgeo hγc p t₀) := rfl

/-- **Math.** **The propagator is injective.** If the chosen field for `p` has
vanishing data at `t₀`, then it vanishes at `a` as well, so `p = 0`: for
`t₀ = a` this is immediate, and for `a < t₀` it is backward uniqueness
(`eqOn_zero_of_right`) applied to the restriction of the field to `[a, t₀]`. -/
theorem jacobiPropagator_injective (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    Function.Injective (jacobiPropagator hab hgeo hγc t₀ ht₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  rw [jacobiPropagator_apply, Prod.ext_iff] at hp
  obtain ⟨hJ, hDJ⟩ := hp
  simp only at hJ hDJ
  rcases eq_or_lt_of_le ht₀.1 with heq | hlt
  · -- `t₀ = a`: the data are read directly at the left endpoint
    subst heq
    rw [jacobiJIcc_left] at hJ
    rw [jacobiDJIcc_left] at hDJ
    exact Prod.ext hJ hDJ
  · -- `a < t₀`: restrict to `[a, t₀]` and run the backward uniqueness
    have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₀.2
    have hres := (jacobiJIcc_isJacobiField hab hgeo hγc p).mono le_rfl hlt ht₀.2
    have hz := hres.eqOn_zero_of_right hlt.le (hgeo.mono hsub)
      (fun t ht => hγc t (hsub ht)) hJ hDJ
    obtain ⟨hJa, hDJa⟩ := hz a ⟨le_rfl, hlt.le⟩
    rw [jacobiJIcc_left] at hJa
    rw [jacobiDJIcc_left] at hDJa
    exact Prod.ext hJa hDJa

/-- **Math.** **The propagator is surjective**: an injective endomorphism of the
finite-dimensional space `E × E` is surjective. -/
theorem jacobiPropagator_surjective (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    Function.Surjective (jacobiPropagator hab hgeo hγc t₀ ht₀) :=
  LinearMap.injective_iff_surjective.mp (jacobiPropagator_injective hab hgeo hγc t₀ ht₀)

end Propagator

/-! ### Interior-seeded existence -/

section Interior

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Interior-seeded existence of Jacobi fields.** Along a geodesic
`γ : [a, b] → M`, for any time `t₀ ∈ [a, b]` — not merely the left endpoint —
and any prescribed value `J₀` and covariant derivative `DJ₀` in `T_{γ(t₀)}M`,
there is a Jacobi field `(J, DJ)` on the **whole** of `[a, b]` with
`J(t₀) = J₀` and `DJ(t₀) = DJ₀`.

Obtained by inverting the propagator `Ψ_{t₀}` of `jacobiPropagator`: it is an
injective endomorphism of the finite-dimensional space `E × E`, hence
surjective, and any `p` in the preimage of `(J₀, DJ₀)` seeds the required
field at `a`.

This is what lets a Jacobi field pinned by data at an **interior** time be read
on an outer window strictly containing it, as the variable-curvature norm
transfer of do Carmo Ch. 8 Thm 2.1 requires.

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer-general`, `cor:dc-ch5-2-5`. -/
theorem exists_isJacobiFieldAlongOn_at
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (J₀ DJ₀ : TangentSpace I (γ t₀)) :
    ∃ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b
      ∧ J t₀ = J₀ ∧ DJ t₀ = DJ₀ := by
  obtain ⟨p, hp⟩ := jacobiPropagator_surjective hab hgeo hγc t₀ ht₀ ((J₀ : E), (DJ₀ : E))
  rw [jacobiPropagator_apply, Prod.ext_iff] at hp
  exact ⟨jacobiJIcc hab hgeo hγc p, jacobiDJIcc hab hgeo hγc p,
    jacobiJIcc_isJacobiField hab hgeo hγc p, hp.1, hp.2⟩

end Interior

end Riemannian.Jacobi

end
