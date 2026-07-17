import PoincareLib.Ch01.JacobiExistence
import PoincareLib.Ch01.JacobiRestriction

/-!
# Poincaré Ch. 1, §1.4 — Jacobi fields with data prescribed at an *interior* time

Every existence/uniqueness statement for Jacobi fields in this development prescribes the
data `(J, ∇J)` at the **left endpoint** of the interval: `exists_isJacobiFieldAlongOn` builds
the field on `[a, b]` from `(J a, ∇J a)`, and `IsJacobiFieldAlongOn.eqOn_zero` propagates
vanishing rightwards from `a`.

That is not enough for the comparison theory. The radial Jacobi datum of
`exists_isRadialJacobi_of_geodesic_velocity` — the input to `sectional_curvature_comparison`
and `ricci_curvature_comparison` — is stated for a geodesic on `[a, b]` with `a < 0 < B < b`,
so that every time of `[0, B]` is *interior* (the chart pair system is a two-sided ODE, and
one-sided derivatives at `0` would not do). Its column clause

  `frameVec J t = 𝒥 t (frameVec ∇J 0)`   for every Jacobi field `J` on `[a, b]` with `J 0 = 0`

therefore quantifies over Jacobi fields on the *large* interval `[a, b]`, while the field one
actually wants to build is pinned by its data at the interior time `0`. Left-endpoint
existence cannot produce it.

This file closes that gap.

## The two results

* `IsJacobiFieldAlongOn.eqOn_zero_of_mem` — **two-sided uniqueness**: a Jacobi field vanishing
  to first order at *any* `c ∈ [a, b]` vanishes identically on `[a, b]`.
* `exists_isJacobiFieldAlongOn_mem` — **interior-data existence**: for any `c ∈ [a, b]` and any
  `(J₀, D₀)` in `T_{γc}M`, there is a Jacobi field on all of `[a, b]` with `J c = J₀`,
  `∇J c = D₀`.

## Why uniqueness is a *clopen* argument, not a walk

`IsJacobiFieldAlongOn.eqOn_zero` propagates vanishing from `a` by a supremum walk. One cannot
simply run that walk backwards from an interior `c`, and — more importantly — the obvious
"the vanishing set is closed because `J` is continuous" step is **false here**: `J t : E` is
the reading of `J` in the chart *at its own foot* `γ t`, so `t ↦ J t` genuinely jumps whenever
the chart changes. It is not a continuous `ℝ → E`.

The fix is that we never need closedness from continuity. In the chart window `[a', b']`
supplied by `IsJacobiFieldAlongOn` at a time `t₀`, the chart readings satisfy a linear ODE,
which has uniqueness in *both* time directions (`IsJacobiFieldOn.eqOn_of_left` and
`eqOn_of_right`). Hence:

  if the pair vanishes at even one point of the window, it vanishes on the whole window.

So the vanishing set `Z` meets a window only by containing it: `Z` is open in `[a, b]`, and its
complement is open too (a window around a non-vanishing time can contain no point of `Z`, else
the window rule would force vanishing at that time). `Z` is clopen and nonempty in the
connected `[a, b]`, so `Z = [a, b]`. No continuity of `J` is used anywhere.

## Existence from uniqueness

With two-sided uniqueness in hand, existence at an interior time is linear algebra. The
"data at `a` ↦ data at `c`" map `T : E × E → E × E` is

* well defined — left-endpoint existence plus `eqOn_of_initial`;
* linear — superposition (`IsJacobiFieldAlongOn.add`, `.smul`);
* injective — by `eqOn_zero_of_mem`: data `0` at `c` forces the field to vanish, in particular
  at `a`.

`E × E` is finite-dimensional, so `T` is surjective: some data at `a` produces the prescribed
data at `c`. This is the standard "the solution operator of a linear ODE is invertible"
argument, done at the manifold level so that no chart bookkeeping leaks out.

Blueprint: `lem:second-order-linear-ode`, `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-! ### Chart level: vanishing at one time of the window kills the window -/

/-- **Math.** **Two-sided vanishing for the chart pair system.** A chart Jacobi field that
vanishes to first order at *any* `c ∈ [a, b]` vanishes on all of `[a, b]`.

Forward from `c` this is `eqOn_of_left` against the zero solution; backward from `c` it is
`eqOn_of_right` against the zero solution. The linear ODE has uniqueness in both time
directions, which is what makes an interior time as good as an endpoint. -/
theorem IsJacobiFieldOn.eqOn_zero_of_mem {g : RiemannianMetric I M} {α : M}
    {u J DJ : ℝ → E} {a b : ℝ} {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖jacobiPairCoeffCoord (I := I) g α u t‖₊ ≤ K)
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    {c : ℝ} (hc : c ∈ Icc a b) (hJc : J c = 0) (hDJc : DJ c = 0) :
    EqOn J 0 (Icc a b) ∧ EqOn DJ 0 (Icc a b) := by
  have key : ∀ t ∈ Icc a b, J t = 0 ∧ DJ t = 0 := by
    intro t ht
    rcases le_total t c with htc | htc
    · -- `t ≤ c`: backward uniqueness on `[t, c]` (the pair vanishes at the *right* endpoint)
      have hsub : Icc t c ⊆ Icc a b := Icc_subset_Icc ht.1 hc.2
      have hz := (h.mono ht.1 hc.2).eqOn_of_right (fun s hs => hK s (hsub hs))
        (isJacobiFieldOn_zero (I := I) g α u t c) (by simpa using hJc) (by simpa using hDJc)
      exact ⟨by simpa using hz.1 (left_mem_Icc.2 htc),
        by simpa using hz.2 (left_mem_Icc.2 htc)⟩
    · -- `c ≤ t`: forward uniqueness on `[c, t]` (the pair vanishes at the *left* endpoint)
      have hsub : Icc c t ⊆ Icc a b := Icc_subset_Icc hc.1 ht.2
      have hz := (h.mono hc.1 ht.2).eqOn_zero (fun s hs => hK s (hsub hs)) hJc hDJc
      exact ⟨by simpa using hz.1 (right_mem_Icc.2 htc),
        by simpa using hz.2 (right_mem_Icc.2 htc)⟩
  exact ⟨fun t ht => by simpa using (key t ht).1, fun t ht => by simpa using (key t ht).2⟩

/-! ### Manifold level: two-sided uniqueness -/

/-- **Math.** **A Jacobi field vanishing to first order at *any* time vanishes identically.**
`IsJacobiFieldAlongOn.eqOn_zero` is the special case `c = a`.

The proof is a connectedness argument, not a walk. Around each `t₀ ∈ [a, b]` the definition of
`IsJacobiFieldAlongOn` supplies a chart window on which the chart readings solve a linear ODE;
by `IsJacobiFieldOn.eqOn_zero_of_mem` (two-sided uniqueness) the pair vanishes on the *whole*
window as soon as it vanishes at one of its times. So the vanishing set meets a window only by
swallowing it: both it and its complement are open in `[a, b]`. Since `[a, b]` is preconnected
and `c` lies in the vanishing set, that set is all of `[a, b]`.

Note that one may **not** argue "the vanishing set is closed because `J` is continuous": `J t`
is the reading of `J` in the chart at its own foot `γ t`, so `t ↦ J t` jumps at every change of
chart and is not a continuous map `ℝ → E`. The clopen argument above never differentiates or
takes limits of `J`, and so is insensitive to those jumps.

Blueprint: `lem:second-order-linear-ode` (uniqueness). -/
theorem IsJacobiFieldAlongOn.eqOn_zero_of_mem {g : RiemannianMetric I M} {γ : ℝ → M}
    {J DJ : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {c : ℝ} (hc : c ∈ Icc a b) (hJc : J c = 0) (hDJc : DJ c = 0) :
    ∀ t ∈ Icc a b, J t = 0 ∧ DJ t = 0 := by
  classical
  -- **The window rule.** Around every time there is an open `O` such that, on `O ∩ [a, b]`,
  -- the pair vanishes *everywhere* as soon as it vanishes *somewhere*.
  have window : ∀ t₀ ∈ Icc a b, ∃ O : Set ℝ, IsOpen O ∧ t₀ ∈ O ∧
      ((∃ s ∈ O ∩ Icc a b, J s = 0 ∧ DJ s = 0) →
        ∀ τ ∈ O ∩ Icc a b, J τ = 0 ∧ DJ τ = 0) := by
    intro t₀ ht₀
    obtain ⟨α, a', b', hab', ht', hsub', hnbhd', hsrc', hJF'⟩ := hJac t₀ ht₀
    obtain ⟨O, hOopen, ht₀O, hOsub⟩ := mem_nhdsWithin.1 hnbhd'
    -- the geodesic chart package on the window, hence a bound on the ODE coefficient
    have hu_diff : ∀ τ ∈ Icc a' b',
        DifferentiableAt ℝ (fun s => extChartAt I α (γ s)) τ := fun τ hτ =>
      hgeo.differentiableAt_extChartAt (hsub' hτ) (hγc τ (hsub' hτ)) (hsrc' τ hτ)
    have hu_cont : ContinuousOn (fun s => extChartAt I α (γ s)) (Icc a' b') :=
      fun τ hτ => (hu_diff τ hτ).continuousAt.continuousWithinAt
    have hu'_cont : ContinuousOn (deriv (fun s => extChartAt I α (γ s)))
        (Icc a' b') := fun τ hτ =>
      (hgeo.continuousAt_deriv_extChartAt (hsub' hτ) (hγc τ (hsub' hτ))
        (hsrc' τ hτ)).continuousWithinAt
    have hmem : ∀ τ ∈ Icc a' b',
        extChartAt I α (γ τ) ∈ interior (extChartAt I α).target := fun τ hτ => by
      rw [(isOpen_extChartAt_target α).interior_eq]
      exact (extChartAt I α).map_source
        (by rw [extChartAt_source]; exact hsrc' τ hτ)
    obtain ⟨K, hK⟩ := exists_nnnorm_jacobiPairCoeffCoord_le (I := I) g α
      hu_cont hu'_cont hmem
    refine ⟨O, hOopen, ht₀O, ?_⟩
    rintro ⟨s, hs, hJs, hDJs⟩ τ hτ
    have hs' : s ∈ Icc a' b' := hOsub hs
    have hτ' : τ ∈ Icc a' b' := hOsub hτ
    -- the chart readings vanish at `s`, hence on the whole window
    have hz := hJF'.eqOn_zero_of_mem hK hs'
      ((tangentCoordChange_eq_zero_iff (I := I) (hsrc' s hs')).2 hJs)
      ((tangentCoordChange_eq_zero_iff (I := I) (hsrc' s hs')).2 hDJs)
    exact ⟨(tangentCoordChange_eq_zero_iff (I := I) (hsrc' τ hτ')).1
        (by simpa using hz.1 hτ'),
      (tangentCoordChange_eq_zero_iff (I := I) (hsrc' τ hτ')).1
        (by simpa using hz.2 hτ')⟩
  -- **The clopen argument.** `U` = times with a window of vanishing, `V` = with a window of
  -- non-vanishing. Both are open, they cover `[a, b]`, they are disjoint on `[a, b]`, and `U`
  -- meets `[a, b]` at `c`. Preconnectedness of `[a, b]` forces `V` to miss it.
  set U : Set ℝ := {t | ∃ O : Set ℝ, IsOpen O ∧ t ∈ O ∧
    ∀ s ∈ O ∩ Icc a b, J s = 0 ∧ DJ s = 0} with hU
  set V : Set ℝ := {t | ∃ O : Set ℝ, IsOpen O ∧ t ∈ O ∧
    ∀ s ∈ O ∩ Icc a b, ¬(J s = 0 ∧ DJ s = 0)} with hV
  have hUopen : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    rintro t ⟨O, hO, htO, hall⟩
    exact ⟨O, fun s hs => ⟨O, hO, hs, hall⟩, hO, htO⟩
  have hVopen : IsOpen V := by
    rw [isOpen_iff_forall_mem_open]
    rintro t ⟨O, hO, htO, hall⟩
    exact ⟨O, fun s hs => ⟨O, hO, hs, hall⟩, hO, htO⟩
  have hcover : Icc a b ⊆ U ∪ V := by
    intro t₀ ht₀
    obtain ⟨O, hOopen, ht₀O, hrule⟩ := window t₀ ht₀
    by_cases hex : ∃ s ∈ O ∩ Icc a b, J s = 0 ∧ DJ s = 0
    · exact Or.inl ⟨O, hOopen, ht₀O, hrule hex⟩
    · exact Or.inr ⟨O, hOopen, ht₀O, fun s hs hvan => hex ⟨s, hs, hvan⟩⟩
  have hUc : c ∈ U := by
    obtain ⟨O, hOopen, hcO, hrule⟩ := window c hc
    exact ⟨O, hOopen, hcO, hrule ⟨c, ⟨hcO, hc⟩, hJc, hDJc⟩⟩
  -- the pair vanishes at every time of `[a, b] ∩ U`
  have hUvan : ∀ t ∈ Icc a b, t ∈ U → J t = 0 ∧ DJ t = 0 := by
    rintro t ht ⟨O, _, htO, hall⟩
    exact hall t ⟨htO, ht⟩
  intro t ht
  refine hUvan t ht ?_
  by_contra htU
  -- `t` is then in `V`, so `[a, b]` meets both `U` and `V` — but they are disjoint on `[a, b]`
  have htV : t ∈ V := (hcover ht).resolve_left htU
  obtain ⟨w, hwIcc, hwU, hwV⟩ :=
    isPreconnected_Icc (a := a) (b := b) U V hUopen hVopen hcover ⟨c, hc, hUc⟩ ⟨t, ht, htV⟩
  obtain ⟨O, _, hwO, hall⟩ := hwV
  exact hall w ⟨hwO, hwIcc⟩ (hUvan w hwIcc hwU)

/-! ### Interior-data existence -/

/-- **Math.** **A Jacobi field may be prescribed at any time of the interval, not just at the
left endpoint.** For `c ∈ [a, b]` and any `(J₀, D₀) ∈ T_{γc}M × T_{γc}M` there is a Jacobi field
on *all* of `[a, b]` with `J c = J₀` and `∇J c = D₀`.

This is what lets one feed the column clause of `exists_isRadialJacobi_of_geodesic_velocity` —
which quantifies over Jacobi fields on the large interval `[a, b]`, `a < 0 < B < b` — with a
field pinned by its data at the *interior* centre `0`. `exists_isJacobiFieldAlongOn` alone
cannot do this: it only prescribes at `a`.

The proof is the invertibility of the solution operator of a linear ODE. The map
`Φ : (J a, ∇J a) ↦ (J c, ∇J c)` is linear by superposition and injective by
`eqOn_zero_of_mem` (data `0` at `c` forces the field, hence its data at `a`, to vanish); as an
injective endomorphism of the finite-dimensional space `E × E` it is surjective, so some datum
at `a` produces the prescribed datum at `c`.

Blueprint: `lem:second-order-linear-ode` (existence). -/
theorem exists_isJacobiFieldAlongOn_mem {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ}
    (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {c : ℝ} (hc : c ∈ Icc a b) (J₀ D₀ : E) :
    ∃ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b ∧ J c = J₀ ∧ DJ c = D₀ := by
  classical
  -- the Jacobi field generated by a datum at the left endpoint
  have hex : ∀ P : E × E, ∃ JD : (ℝ → E) × (ℝ → E),
      IsJacobiFieldAlongOn (I := I) g γ JD.1 JD.2 a b ∧ JD.1 a = P.1 ∧ JD.2 a = P.2 := by
    intro P
    obtain ⟨J, DJ, h, hJ, hD⟩ := exists_isJacobiFieldAlongOn hab hgeo hγc P.1 P.2
    exact ⟨(J, DJ), h, hJ, hD⟩
  choose F hFjac hF1 hF2 using hex
  -- two Jacobi fields agreeing at `a` agree at `c`
  have hagree : ∀ (J DJ : ℝ → E), IsJacobiFieldAlongOn (I := I) g γ J DJ a b →
      ∀ P : E × E, J a = P.1 → DJ a = P.2 → J c = (F P).1 c ∧ DJ c = (F P).2 c := by
    intro J DJ h P hJa hDa
    exact IsJacobiFieldAlongOn.eqOn_of_initial hab hgeo hγc h (hFjac P)
      (by rw [hJa, hF1 P]) (by rw [hDa, hF2 P]) c hc
  -- the solution operator `data at a ↦ data at c`
  let Φ : (E × E) →ₗ[ℝ] (E × E) :=
    { toFun := fun P => ((F P).1 c, (F P).2 c)
      map_add' := by
        intro P Q
        have hsum := IsJacobiFieldAlongOn.add hab hgeo hγc (hFjac P) (hFjac Q)
        have := hagree _ _ hsum (P + Q)
          (by simp [hF1 P, hF1 Q]) (by simp [hF2 P, hF2 Q])
        exact Prod.ext this.1.symm this.2.symm
      map_smul' := by
        intro r P
        have hsm := IsJacobiFieldAlongOn.smul r (hFjac P)
        have := hagree _ _ hsm (r • P) (by simp [hF1 P]) (by simp [hF2 P])
        exact Prod.ext this.1.symm this.2.symm }
  -- `Φ` is injective: a field with zero data at `c` vanishes, in particular at `a`
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    have hP1 : (F P).1 c = 0 := congrArg Prod.fst hP
    have hP2 : (F P).2 c = 0 := congrArg Prod.snd hP
    have hz := IsJacobiFieldAlongOn.eqOn_zero_of_mem (hFjac P) hgeo hγc hc hP1 hP2
    have hza := hz a (left_mem_Icc.2 hab.le)
    have hp1 : P.1 = 0 := by rw [← hF1 P, hza.1]
    have hp2 : P.2 = 0 := by rw [← hF2 P, hza.2]
    exact Prod.ext (by simpa using hp1) (by simpa using hp2)
  -- injective endomorphism of a finite-dimensional space, hence surjective
  obtain ⟨P, hP⟩ := (LinearMap.injective_iff_surjective.1 hinj) (J₀, D₀)
  exact ⟨(F P).1, (F P).2, hFjac P, congrArg Prod.fst hP, congrArg Prod.snd hP⟩

end PoincareLib

end
