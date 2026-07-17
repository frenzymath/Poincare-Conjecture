import PoincareLib.Ch01.ExpDifferential

/-!
# Poincaré Ch. 1, §1.4 — `d(exp_p)_v` is singular exactly at conjugate points

The second sentence of `lem:exponential-differential-jacobi`: *`d(exp_p)_v` is singular if
and only if `exp_p(v)` is a conjugate point along `γ_v`.*

Given `d(exp_p)_v(Z) = Y_Z(1)` (`ExpDifferential`), this is a statement about the linear map
`Z ↦ Y_Z(1)`: it has a kernel vector `Z ≠ 0` exactly when some Jacobi field with `Y(0) = 0`,
not identically zero, also has `Y(1) = 0` — which is the definition of `γ 1` being conjugate
(`IsConjugatePointAt`).

Two small facts carry it:

* `tangentCoordChange_injective` — the chart reading of a tangent vector loses no
  information: `C_{x→β}` is injective, because the cocycle `C_{β→x} ∘ C_{x→β} = C_{x→x} = id`.
  So `chartVectorRep γ ζ J 1 = 0` really does say `J 1 = 0`.
* `IsJacobiFieldAlongOn.deriv_eq_zero_of_forall_eq_zero` — a Jacobi field that *vanishes
  identically* has vanishing covariant derivative at the left endpoint. Reading the chart
  Jacobi pair system at `a`, the first equation says `(J^α)' = DJ^α − Γ(u̇^α, J^α)`; with
  `J^α ≡ 0` the left side is `0` and the Γ term drops (it is linear in the `J` slot), so
  `DJ^α(a) = 0`, hence `DJ(a) = 0`.

Together with `IsJacobiFieldAlongOn.eqOn_zero` (Grönwall uniqueness: `J(a) = 0` and
`DJ(a) = 0` force `J ≡ 0`), these give both directions.

* `expDifferential_injective_iff_not_conjugate` — `d(exp_p)_v` is injective iff `exp_p(v)`
  is **not** conjugate to `p` along `γ_v`.

The injective direction is what `lem:local-diffeomorphism-bounded-curvature` consumes: no
conjugate points on `γ_v` ⟹ `d(exp_p)_v` is nonsingular ⟹ `exp_p` is a local diffeomorphism
at `v` (in finite dimension, injective ⟹ bijective).

Blueprint: `lem:exponential-differential-jacobi`, `def:conjugate-point`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

/-- **Math.** **A chart reading of a tangent vector loses no information.** The tangent
coordinate change `C_{x→β}` at the foot `x` is injective, by the cocycle
`C_{β→x} ∘ C_{x→β} = C_{x→x} = id`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem tangentCoordChange_injective {x β : M} (hx : x ∈ (chartAt H β).source) :
    Function.Injective (fun u : E => tangentCoordChange I x β x u) := by
  have hxx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hxβ : x ∈ (extChartAt I β).source := by rw [extChartAt_source]; exact hx
  have hmem : x ∈ (extChartAt I x).source ∩ (extChartAt I β).source
      ∩ (extChartAt I x).source := ⟨⟨hxx, hxβ⟩, hxx⟩
  intro u₁ u₂ h
  have hinv : ∀ u : E,
      tangentCoordChange I β x x (tangentCoordChange I x β x u) = u := by
    intro u
    rw [tangentCoordChange_comp (I := I) (v := u) hmem]
    exact tangentCoordChange_self (I := I) hxx
  simp only at h
  rw [← hinv u₁, ← hinv u₂, h]

/-- **Math.** **A Jacobi field vanishing identically has vanishing covariant derivative.**
If the manifold Jacobi field `(J, DJ)` along `γ` satisfies `J t = 0` for every `t ∈ [a,b]`
(with `a < b`), then `DJ a = 0`.

In a chart `α` around `γ a` the pair system's first equation reads
`(J^α)'(t) = DJ^α(t) − Γ^α(u̇^α(t), J^α(t))`. With `J ≡ 0` the chart reading `J^α` is
identically `0` on the chart's time window, so its derivative there is `0`; and the Γ term
vanishes because the Christoffel contraction is linear in the `J` slot
(`chartChristoffelContraction_zero_left` after `chartChristoffelContraction_symm`). Hence
`DJ^α(a) = 0`, and `DJ a = 0` since the chart reading is injective.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem IsJacobiFieldAlongOn.deriv_eq_zero_of_forall_eq_zero
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ} (hab : a < b)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hJ : ∀ t ∈ Icc a b, J t = 0) :
    DJ a = 0 := by
  classical
  have haIcc : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨α, a', b', hab', haI, hsub, _hnhds, hsrc, hsys⟩ := hJac a haIcc
  have haI' : a ∈ Icc a' b' := haI
  -- the chart reading of `J` is identically zero on the chart's time window
  have hrep0 : ∀ t ∈ Icc a' b', chartVectorRep (I := I) γ α J t = 0 := by
    intro t ht
    have : J t = 0 := hJ t (hsub ht)
    simp [chartVectorRep, this]
  -- so its derivative within that window is zero at `a`
  have hzero : HasDerivWithinAt (chartVectorRep (I := I) γ α J) 0 (Icc a' b') a :=
    (hasDerivWithinAt_const a (Icc a' b') (0 : E)).congr hrep0 (hrep0 a haI')
  -- the pair system's first equation at `a`
  have hsys1 := hsys.hasDerivWithinAt_fst a haI'
  -- the Γ term drops, since the chart reading of `J` vanishes at `a`
  have hΓ : Geodesic.chartChristoffelContraction (I := I) g α
      (deriv (fun t => extChartAt I α (γ t)) a)
      (chartVectorRep (I := I) γ α J a)
      (extChartAt I α (γ a)) = 0 := by
    rw [hrep0 a haI', Geodesic.chartChristoffelContraction_symm,
      Geodesic.chartChristoffelContraction_zero_left]
  rw [hΓ, sub_zero] at hsys1
  -- two derivatives of the same function within a set with unique differentials
  have huniq : UniqueDiffWithinAt ℝ (Icc a' b') a := uniqueDiffOn_Icc hab' a haI'
  have hDrep : chartVectorRep (I := I) γ α DJ a = 0 :=
    (huniq.eq_deriv _ hsys1 hzero).symm ▸ rfl
  -- the chart reading is injective, so `DJ a = 0`
  have hinj := tangentCoordChange_injective (I := I) (x := γ a) (β := α) (hsrc a haI')
  have : tangentCoordChange I (γ a) α (γ a) (DJ a)
      = tangentCoordChange I (γ a) α (γ a) 0 := by
    simpa [chartVectorRep] using hDrep
  exact hinj this

/-- **Math.** **`d(exp_p)_v` is singular exactly at conjugate points.** With the notation of
`hasFDerivAt_chartReading_expMapGlobal`, the differential `D` of `exp_p` at `v` is injective
if and only if `exp_p(v) = γ_v(1)` is **not** a conjugate point along `γ_v`.

`(⇐)` If `D Z = 0` with `Z ≠ 0`, the Jacobi field `Y_Z` (`Y_Z(0)=0`, `∇_X Y_Z(0)=Z`) has
`Y_Z(1) = 0` (the chart reading is injective) and is not identically zero (else
`deriv_eq_zero_of_forall_eq_zero` would force `Z = 0`) — so `γ_v(1)` is conjugate.

`(⇒)` If `γ_v(1)` is conjugate, witnessed by `(J, DJ)`, then `DJ 0 ≠ 0` (else Grönwall
uniqueness `IsJacobiFieldAlongOn.eqOn_zero` would make `J` identically zero) while
`D (DJ 0) = ` chart reading of `J 1 = 0` — so `D` is not injective.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem expDifferential_injective_iff_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : E) {ζ : M} {D : E →L[ℝ] E}
    (hζ : expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source)
    (hjac : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 →
      J 0 = 0 →
      D (DJ 0) = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1) :
    Function.Injective D
      ↔ ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1 := by
  classical
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) 1) := fun t _ =>
    isGeodesic_globalGeodesic g hg p v t
  have hγcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t := fun t _ =>
    (continuous_globalGeodesic g hg p v).continuousAt
  have hγ1 : γ 1 ∈ (chartAt H ζ).source := hζ
  -- reading `J 1` off its chart reading, which is injective
  have hread : ∀ J : ℝ → E, chartVectorRep (I := I) γ ζ J 1 = 0 ↔ J 1 = 0 := by
    intro J
    constructor
    · intro h
      refine tangentCoordChange_injective (I := I) (x := γ 1) (β := ζ) hγ1 ?_
      simpa [chartVectorRep] using h
    · intro h; simp [chartVectorRep, h]
  constructor
  · -- injective ⟹ no conjugate point
    intro hinj hconj
    obtain ⟨J, DJ, hJ, ⟨t, ht, hJt⟩, hJ0, hJ1⟩ := hconj
    -- `DJ 0 ≠ 0`, else Grönwall uniqueness kills `J`
    have hDJ0 : DJ 0 ≠ 0 := by
      intro h0
      exact hJt ((IsJacobiFieldAlongOn.eqOn_zero zero_le_one hJ hγgeo hγcont hJ0 h0 t ht).1)
    -- but `D` kills it
    have : D (DJ 0) = 0 := by rw [hjac J DJ hJ hJ0, (hread J).2 hJ1]
    exact hDJ0 (hinj (by rw [this, map_zero]))
  · -- no conjugate point ⟹ injective; by linearity it suffices to kill the kernel
    intro hnc
    have key : ∀ Z : E, D Z = 0 → Z = 0 := by
      intro Z hDZ
      by_contra hZne
      -- the Jacobi field with `J 0 = 0`, `∇_X J 0 = Z`
      obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
        exists_isJacobiFieldAlongOn (I := I) (g := g) (γ := γ) (a := 0) (b := 1) zero_lt_one
          hγgeo hγcont (0 : TangentSpace I (γ 0)) (Z : TangentSpace I (γ 0))
      have hJ0' : J 0 = 0 := hJ0
      have hDJ0' : DJ 0 = Z := hDJ0
      -- it vanishes at time 1
      have hJ1 : J 1 = 0 := by
        refine (hread J).1 ?_
        rw [← hjac J DJ hJ hJ0', hDJ0', hDZ]
      -- and it is not identically zero, since `Z ≠ 0`
      have hne : ∃ t ∈ Icc (0 : ℝ) 1, J t ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hz : DJ 0 = 0 :=
          IsJacobiFieldAlongOn.deriv_eq_zero_of_forall_eq_zero zero_lt_one hJ hall
        rw [hDJ0'] at hz
        exact hZne hz
      exact hnc ⟨J, DJ, hJ, hne, hJ0', hJ1⟩
    intro Z₁ Z₂ h
    have hsub : D (Z₁ - Z₂) = 0 := by rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (key _ hsub)

end PoincareLib

end
