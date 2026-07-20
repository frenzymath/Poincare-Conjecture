import MorganTianLib.Ch01.ScalarComparison
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Morgan–Tian Ch. 1, §1.9 — Operator Riccati comparison, lower form

The manifold-free analytic engine of `lem:rauch-lower` (radial shape-operator
lower bound under an upper curvature bound): if `U : (0, r₀) → Sym(E)` is a
differentiable family of symmetric endomorphisms of a nontrivial
finite-dimensional real inner product space with `U(r) → 0` as `r → 0⁺`,
satisfying the Riccati differential inequality
`⟪U'(r)X, X⟫ ≥ −⟪U(r)²X, X⟫ − 2a(r)⟪U(r)X, X⟫` with `a = s'/s` for a
positive differentiable `s` bounded near `0⁺`, then `U(r) ≥ 0` on `(0, r₀)`
(`operator_riccati_nonneg`).

Unlike the upper bound (`scalar_riccati_comparison` applied along a fixed
direction), the mirror bound cannot be reduced to a scalar inequality along a
fixed vector — the Cauchy–Schwarz inequality `⟪U²X, X⟫ ≥ ⟪UX, X⟫²` points the
wrong way. Instead one works with the smallest eigenvalue
`m(r) = min_{‖X‖=1} ⟪U(r)X, X⟫` (`minRayleigh`), which is only locally
Lipschitz:

* a minimizer `X₀` on the unit sphere is an eigenvector
  (`apply_eq_minRayleigh_smul`, via mathlib's Rayleigh-quotient theory), so
  `φ(y) = ⟪U(y)X₀, X₀⟫` is an upper support function of `m` at `x` whose
  derivative obeys `φ'(x) ≥ −m(x)² − 2a(x)m(x)` exactly;
* comparing difference quotients from the left against the support function
  (`eventually_lt_slope_of_upper_support`), the weighted function
  `h = (−m)·s²e^{−Wr}` (with `W` a bound for `‖U‖`) has left difference
  quotients eventually below every positive `δ` on any interval where `m < 0`;
* a barrier lemma (`le_of_left_slope_eventually_lt`, the reflected form of
  mathlib's fencing lemma for right liminf slopes) shows `h` is non-increasing
  there, while `h → 0` (or a nonpositive value) at the left endpoint of a
  maximal interval where `m < 0` — contradicting `h > 0` inside.

The file also records the elementary upper companion
(`operator_riccati_le`, blueprint `lem:operator-riccati-upper`): under
`⟪A'X, X⟫ ≤ k‖X‖² − ⟪A²X, X⟫` and `A(r) − (1/r)Id → 0`, one has
`A(r) ≤ (sn_k'(r)/sn_k(r))·Id` as quadratic forms — there Cauchy–Schwarz
points the right way, so the bound follows from `scalar_riccati_comparison`
applied along each fixed unit vector. This is the engine of the
shape-operator estimate in `thm:sectional-curvature-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.9
(blueprint `lem:operator-riccati-lower`, `lem:operator-riccati-upper`).
-/

open Real Filter Set Metric
open scoped Topology RealInnerProductSpace

namespace MorganTianLib

/-! ### The barrier lemma for left difference quotients -/

/-- **Math.** *Barrier (fencing) lemma for left difference quotients.* A
function continuous on `[c, d]` whose left difference quotients at every
`x ∈ (c, d]` are eventually (as `y → x⁻`) smaller than every positive `δ` is
non-increasing from `c` to `d`. This is the reflected form of the standard
fact that a continuous function whose right lower Dini derivative is
nonnegative is non-decreasing (compare with the linear barriers
`h(c) + ε(x − c)`). Blueprint: `lem:operator-riccati-lower`. -/
theorem le_of_left_slope_eventually_lt {h : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hcont : ContinuousOn h (Icc c d))
    (hslope : ∀ x ∈ Ioc c d, ∀ δ : ℝ, 0 < δ → ∀ᶠ y in 𝓝[<] x, slope h y x < δ) :
    h d ≤ h c := by
  rcases eq_or_lt_of_le hcd with rfl | hlt
  · exact le_rfl
  -- reflect: `g t = −h(−t)` has right slopes equal to the left slopes of `h`
  set g : ℝ → ℝ := fun t => -h (-t) with hg
  have hgcont : ContinuousOn g (Icc (-d) (-c)) := by
    have hmaps : ∀ t ∈ Icc (-d) (-c), -t ∈ Icc c d := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact ((hcont.comp continuous_neg.continuousOn hmaps).neg)
  -- fencing against the linear barriers `g(−d) + ε(t + d)`
  have hfence : ∀ ε : ℝ, 0 < ε → g (-c) ≤ g (-d) + ε * (-c - -d) := by
    intro ε hε
    have key := image_le_of_liminf_slope_right_lt_deriv_boundary (f := g)
      (f' := fun _ => 0) (a := -d) (b := -c) hgcont ?_
      (B := fun t => g (-d) + ε * (t - -d)) (B' := fun _ => ε) ?_ ?_ ?_
    · exact key ⟨by linarith, le_rfl⟩
    · -- right slopes of `g` are frequently `< r` for every `r > 0`
      intro x hx r hr
      have hx' : -x ∈ Ioc c d := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have hev := hslope (-x) hx' r hr
      have hmap : Tendsto (fun z : ℝ => -z) (𝓝[>] x) (𝓝[<] (-x)) := by
        refine continuous_neg.continuousWithinAt.tendsto_nhdsWithin ?_
        intro z hz
        exact mem_Iio.mpr (neg_lt_neg (mem_Ioi.mp hz))
      refine ((hmap.eventually hev).and self_mem_nhdsWithin).frequently.mono ?_
      rintro z ⟨hz, hz' : x < z⟩
      have hzx : z - x ≠ 0 := by intro hzero; simp at hz'; linarith [sub_eq_zero.mp hzero]
      calc slope g x z = (g z - g x) / (z - x) := slope_def_field g x z
        _ = (h (-x) - h (-z)) / (-x - -z) := by
            rw [hg]
            have hne : -x - -z = z - x := by ring
            rw [hne]
            ring_nf
        _ = slope h (-z) (-x) := (slope_def_field h (-z) (-x)).symm
        _ < r := hz
    · simp
    · intro x
      simpa using (((hasDerivAt_id x).sub_const (-d)).const_mul ε).const_add (g (-d))
    · exact fun _ _ _ => hε
  -- let `ε → 0`
  by_contra hcon
  push Not at hcon
  have hdc : 0 < d - c := by linarith
  have := hfence ((h d - h c) / (2 * (d - c)))
    (div_pos (by linarith) (by linarith))
  have harith : (h d - h c) / (2 * (d - c)) * (-c - -d) = (h d - h c) / 2 := by
    field_simp
    ring
  rw [harith] at this
  simp only [hg, neg_neg] at this
  linarith

/-! ### Upper support functions control left difference quotients -/

/-- **Math.** If `φ` is an upper support function of `m` at `x` (`m ≤ φ` with
equality at `x`) differentiable at `x`, then the left difference quotients of
`m` at `x` are eventually bounded below by `φ'(x) − δ` for every `δ > 0`:
for `y < x`, `(m x − m y)/(x − y) ≥ (φ x − φ y)/(x − y) → φ'(x)`.
Blueprint: `lem:operator-riccati-lower`. -/
theorem eventually_lt_slope_of_upper_support {m φ : ℝ → ℝ} {x b δ : ℝ}
    (hle : ∀ y, m y ≤ φ y) (heq : m x = φ x)
    (hφ : HasDerivAt φ b x) (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝[<] x, b - δ < slope m y x := by
  have hsub : Iio x ⊆ {x}ᶜ := fun y (hy : y < x) => ne_of_lt hy
  have hslope : Tendsto (slope φ x) (𝓝[<] x) (𝓝 b) :=
    (hasDerivAt_iff_tendsto_slope.mp hφ).mono_left (nhdsWithin_mono x hsub)
  have hev : ∀ᶠ y in 𝓝[<] x, b - δ < slope φ x y :=
    hslope.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with y hy (hyx : y < x)
  have hxy : 0 < x - y := by linarith
  have h1 : slope φ x y ≤ slope m y x := by
    rw [slope_comm φ x y, slope_def_field, slope_def_field]
    have hnum : φ x - φ y ≤ m x - m y := by
      have := hle y
      linarith [heq]
    exact div_le_div_of_nonneg_right hnum hxy.le
  linarith

/-! ### The smallest eigenvalue of a symmetric endomorphism -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The minimum of the quadratic form `X ↦ ⟪T X, X⟫` of a continuous
endomorphism `T` over the unit sphere — for `T` symmetric on a nontrivial
finite-dimensional space, its smallest eigenvalue.
Blueprint: `lem:operator-riccati-lower`. -/
noncomputable def minRayleigh (T : E →L[ℝ] E) : ℝ :=
  sInf ((fun X => ⟪T X, X⟫) '' sphere (0 : E) 1)

/-- **Math.** The quadratic form of `T` at a unit vector is bounded by the
operator norm: `|⟪T X, X⟫| ≤ ‖T‖` (Cauchy–Schwarz).
Blueprint: `lem:operator-riccati-lower`. -/
theorem abs_inner_map_self_le {T : E →L[ℝ] E} {X : E} (hX : ‖X‖ = 1) :
    |⟪T X, X⟫| ≤ ‖T‖ :=
  calc |⟪T X, X⟫| ≤ ‖T X‖ * ‖X‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖T‖ * ‖X‖ * ‖X‖ := by gcongr; exact T.le_opNorm X
    _ = ‖T‖ := by rw [hX]; ring

private theorem bddBelow_image_sphere (T : E →L[ℝ] E) :
    BddBelow ((fun X => ⟪T X, X⟫) '' sphere (0 : E) 1) := by
  refine ⟨-‖T‖, ?_⟩
  rintro v ⟨Y, hY, rfl⟩
  have hY1 : ‖Y‖ = 1 := by simpa using hY
  linarith [abs_inner_map_self_le (T := T) hY1, neg_abs_le ⟪T Y, Y⟫]

/-- **Math.** The smallest-eigenvalue functional bounds the quadratic form
from below at unit vectors: `minRayleigh T ≤ ⟪T X, X⟫` whenever `‖X‖ = 1`.
Blueprint: `lem:operator-riccati-lower`. -/
theorem minRayleigh_le {T : E →L[ℝ] E} {X : E} (hX : ‖X‖ = 1) :
    minRayleigh T ≤ ⟪T X, X⟫ :=
  csInf_le (bddBelow_image_sphere T) ⟨X, by simpa using hX, rfl⟩

/-! ### The operator Riccati comparison, upper form -/

/-- **Math.** **Operator Riccati comparison, upper form** — the engine of the
shape-operator estimate in `thm:sectional-curvature-comparison`. Let `A` be a
differentiable family of symmetric endomorphisms of a real inner product
space with `A(r) − (1/r)·Id → 0` as `r → 0⁺`, satisfying
`⟪A'(r)X, X⟫ ≤ k‖X‖² − ⟪A(r)(A(r)X), X⟫` on `(0, r₀)`. Then
`⟪A(r)X, X⟫ ≤ (sn_k'(r)/sn_k(r))·‖X‖²` for all `r ∈ (0, r₀)` and `X`.

Proof, following the blueprint: for a fixed unit vector `X` the function
`φ(r) = ⟪A(r)X, X⟫` satisfies `φ' ≤ k − ‖A X‖² ≤ k − φ²` (by symmetry
`⟪A(AX), X⟫ = ‖AX‖²`, and Cauchy–Schwarz — which points the right way for
the upper bound), while `|φ(r) − 1/r| = |⟪(A(r) − (1/r)Id)X, X⟫| ≤
‖A(r) − (1/r)Id‖ → 0`; the scalar Riccati comparison
(`scalar_riccati_comparison`) gives `φ ≤ sn_k'/sn_k`. The general case
follows by homogeneity. Blueprint: `lem:operator-riccati-upper`. -/
theorem operator_riccati_le {k r₀ : ℝ} (hk : 0 ≤ k) {A A' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E, ⟪A r X, Y⟫ = ⟪X, A r Y⟫)
    (h0 : Tendsto (fun r => A r - r⁻¹ • ContinuousLinearMap.id ℝ E)
      (𝓝[>] 0) (𝓝 0))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      ⟪A' r X, X⟫ ≤ k * ‖X‖ ^ 2 - ⟪A r (A r X), X⟫) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      ⟪A r X, X⟫ ≤ csK k r / snK k r * ‖X‖ ^ 2 := by
  -- the unit-vector case, by the scalar Riccati comparison
  have hunit : ∀ X : E, ‖X‖ = 1 → ∀ r ∈ Ioo (0 : ℝ) r₀,
      ⟪A r X, X⟫ ≤ csK k r / snK k r := by
    intro X hX
    have hφd : ∀ r ∈ Ioo (0 : ℝ) r₀,
        HasDerivAt (fun y => ⟪A y X, X⟫) ⟪A' r X, X⟫ r := by
      intro r hr
      have h1 : HasDerivAt (fun y => A y X) (A' r X) r := by
        simpa using (hA r hr).clm_apply (hasDerivAt_const r X)
      simpa using h1.inner ℝ (hasDerivAt_const r X)
    have hφric : ∀ r ∈ Ioo (0 : ℝ) r₀,
        ⟪A' r X, X⟫ + ⟪A r X, X⟫ ^ 2 ≤ k := by
      intro r hr
      have h1 := hric r hr X
      have h2 : ⟪A r (A r X), X⟫ = ‖A r X‖ ^ 2 := by
        rw [hsymm r hr (A r X) X]
        exact real_inner_self_eq_norm_sq _
      have h3 : ⟪A r X, X⟫ ^ 2 ≤ ‖A r X‖ ^ 2 := by
        have h4 := abs_real_inner_le_norm (A r X) X
        rw [hX, mul_one] at h4
        nlinarith [abs_nonneg ⟪A r X, X⟫, sq_abs ⟪A r X, X⟫]
      rw [h2, hX] at h1
      nlinarith
    have hφ0 : Tendsto (fun r => ⟪A r X, X⟫ - 1 / r) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using h0.norm)
      filter_upwards [self_mem_nhdsWithin] with r (hr : (0 : ℝ) < r)
      have hid : ⟪(A r - r⁻¹ • ContinuousLinearMap.id ℝ E) X, X⟫
          = ⟪A r X, X⟫ - 1 / r := by
        rw [ContinuousLinearMap.sub_apply, inner_sub_left,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
          real_inner_smul_left, real_inner_self_eq_norm_sq, hX]
        ring
      rw [← hid]
      simpa using
        abs_inner_map_self_le (T := A r - r⁻¹ • ContinuousLinearMap.id ℝ E) hX
    intro r hr
    exact scalar_riccati_comparison hk hφd hφric hφ0 r hr
  -- the general case, by homogeneity
  intro r hr X
  rcases eq_or_ne X 0 with rfl | hXne
  · simp
  have hX : (0 : ℝ) < ‖X‖ := norm_pos_iff.mpr hXne
  have hunit' := hunit ((‖X‖⁻¹ : ℝ) • X) (norm_smul_inv_norm (𝕜 := ℝ) hXne) r hr
  rw [map_smul, real_inner_smul_left, real_inner_smul_right] at hunit'
  have hsq : (0 : ℝ) ≤ ‖X‖ ^ 2 := sq_nonneg _
  calc ⟪A r X, X⟫ = ‖X‖ ^ 2 * (‖X‖⁻¹ * (‖X‖⁻¹ * ⟪A r X, X⟫)) := by
        field_simp
      _ ≤ ‖X‖ ^ 2 * (csK k r / snK k r) := mul_le_mul_of_nonneg_left hunit' hsq
      _ = csK k r / snK k r * ‖X‖ ^ 2 := by ring

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- **Math.** The minimum of the quadratic form over the unit sphere is
attained (the sphere is compact and nonempty, the form continuous).
Blueprint: `lem:operator-riccati-lower`. -/
theorem exists_norm_eq_one_minRayleigh (T : E →L[ℝ] E) :
    ∃ X₀ : E, ‖X₀‖ = 1 ∧ ⟪T X₀, X₀⟫ = minRayleigh T ∧
      IsMinOn (fun X => ⟪T X, X⟫) (sphere (0 : E) 1) X₀ := by
  have hne : (sphere (0 : E) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact ⟨(‖v‖⁻¹ : ℝ) • v, by simpa using norm_smul_inv_norm (𝕜 := ℝ) hv⟩
  have hcont : ContinuousOn (fun X : E => ⟪T X, X⟫) (sphere 0 1) :=
    (T.continuous.inner continuous_id).continuousOn
  obtain ⟨X₀, hX₀mem, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hcont
  have hX₀ : ‖X₀‖ = 1 := by simpa using hX₀mem
  refine ⟨X₀, hX₀, ?_, hmin⟩
  have hleast : IsLeast ((fun X => ⟪T X, X⟫) '' sphere (0 : E) 1) ⟪T X₀, X₀⟫ :=
    ⟨⟨X₀, hX₀mem, rfl⟩, by rintro v ⟨Y, hY, rfl⟩; exact hmin hY⟩
  exact hleast.csInf_eq.symm

/-- **Math.** The smallest-eigenvalue functional is 1-Lipschitz for the
operator norm: comparing minima through the minimizer of one of the two
forms, `minRayleigh T − minRayleigh T' ≤ ‖T − T'‖`.
Blueprint: `lem:operator-riccati-lower`. -/
theorem minRayleigh_sub_le (T T' : E →L[ℝ] E) :
    minRayleigh T - minRayleigh T' ≤ ‖T - T'‖ := by
  obtain ⟨Y, hY, hYval, -⟩ := exists_norm_eq_one_minRayleigh T'
  have h1 : minRayleigh T ≤ ⟪T Y, Y⟫ := minRayleigh_le hY
  have h2 : ⟪T Y, Y⟫ - ⟪T' Y, Y⟫ = ⟪(T - T') Y, Y⟫ := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_left]
  have h3 : |⟪(T - T') Y, Y⟫| ≤ ‖T - T'‖ := abs_inner_map_self_le hY
  linarith [le_abs_self ⟪(T - T') Y, Y⟫]

/-- **Math.** `|minRayleigh T − minRayleigh T'| ≤ ‖T − T'‖`.
Blueprint: `lem:operator-riccati-lower`. -/
theorem abs_minRayleigh_sub_le (T T' : E →L[ℝ] E) :
    |minRayleigh T - minRayleigh T'| ≤ ‖T - T'‖ := by
  rw [abs_sub_le_iff]
  refine ⟨minRayleigh_sub_le T T', ?_⟩
  rw [← norm_neg]
  simpa using minRayleigh_sub_le T' T

/-- **Math.** `|minRayleigh T| ≤ ‖T‖`.
Blueprint: `lem:operator-riccati-lower`. -/
theorem abs_minRayleigh_le (T : E →L[ℝ] E) : |minRayleigh T| ≤ ‖T‖ := by
  obtain ⟨X, hX, hXval, -⟩ := exists_norm_eq_one_minRayleigh T
  rw [abs_le]
  constructor
  · rw [← hXval]
    linarith [abs_inner_map_self_le (T := T) hX, neg_abs_le ⟪T X, X⟫]
  · rw [← hXval]
    linarith [abs_inner_map_self_le (T := T) hX, le_abs_self ⟪T X, X⟫]

omit [Nontrivial E] in
/-- **Math.** *A minimizer of the quadratic form of a symmetric endomorphism
on the unit sphere is an eigenvector, with eigenvalue the minimum value*:
`T X₀ = ⟪T X₀, X₀⟫ • X₀` (mathlib's Rayleigh-quotient theory).
Blueprint: `lem:operator-riccati-lower`. -/
theorem apply_eq_minRayleigh_smul {T : E →L[ℝ] E}
    (hsymm : ∀ X Y : E, ⟪T X, Y⟫ = ⟪X, T Y⟫) {X₀ : E} (hX₀ : ‖X₀‖ = 1)
    (hmin : IsMinOn (fun X => ⟪T X, X⟫) (sphere (0 : E) 1) X₀) :
    T X₀ = ⟪T X₀, X₀⟫ • X₀ := by
  have hsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun X Y => hsymm X Y
  have hX₀ne : X₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hX₀
    norm_num at hX₀
  have hextr : IsMinOn T.reApplyInnerSelf (sphere (0 : E) ‖X₀‖) X₀ := by
    rw [hX₀]
    intro Y hY
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hmin hY
  have hev := hsa.hasEigenvector_of_isMinOn hX₀ne hextr
  have happ : T X₀ = (⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) • X₀ := by
    simpa using hev.apply_eq_smul
  have hval : (⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) = ⟪T X₀, X₀⟫ := by
    have := congrArg (fun v => ⟪v, X₀⟫) happ
    simp only [real_inner_smul_left] at this
    rw [real_inner_self_eq_norm_sq, hX₀] at this
    simpa using this.symm
  rw [hval] at happ
  exact happ

/-! ### The operator Riccati comparison, lower form -/

/-- **Math.** **Operator Riccati comparison, lower form** — the analytic
engine of `lem:rauch-lower`. Let `E` be a nontrivial finite-dimensional real
inner product space, `s` differentiable and positive on `(0, r₀)` and bounded
near `0⁺`, and `U : (0, r₀) → Sym(E)` a differentiable family of symmetric
endomorphisms with `U(r) → 0` as `r → 0⁺` satisfying the Riccati differential
inequality
`⟪U'(r)X, X⟫ ≥ −⟪U(r)(U(r)X), X⟫ − 2(s'(r)/s(r))⟪U(r)X, X⟫`. Then `U(r) ≥ 0`
for all `r ∈ (0, r₀)`.

Proof, following the blueprint: let `m(r) = minRayleigh (U r)` be the
smallest eigenvalue, continuous with `|m| ≤ ‖U‖ → 0` at `0⁺`. At each `x` a
unit minimizer `X₀` is an eigenvector, so `φ(y) = ⟪U(y)X₀, X₀⟫` is an upper
support function of `m` at `x` with `φ'(x) ≥ −m(x)² − 2a(x)m(x)`, whence the
left difference quotients of `m` at `x` eventually exceed
`−m(x)² − 2a(x)m(x) − δ`. If `m(r₂) < 0`, take `W ≥ 0` bounding `‖U‖` on
`(0, r₂]` and `r₃ < r₂` the supremum of `{0} ∪ {r : m(r) ≥ 0}`; on
`(r₃, r₂]` the function `h = (−m)·s²·e^{−Wr}` has left difference quotients
eventually below every positive `δ` (the support-function bound plus
`ρ' = ρ(2a − W)` make the main term `ρ·(−m)·((−m) − W) ≤ 0`), so `h` is
non-increasing by the barrier lemma; but `h → 0` (if `r₃ = 0`, as `m → 0`
and `s` is bounded) or `h(r₃⁺) ≤ 0` (if `r₃ > 0`, as `m(r₃) ≥ 0` by
continuity), contradicting `h(r₂) > 0`. Blueprint:
`lem:operator-riccati-lower`. -/
theorem operator_riccati_nonneg {r₀ Cs : ℝ} {s s' : ℝ → ℝ}
    {U U' : ℝ → E →L[ℝ] E}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hsbdd : ∀ᶠ r in 𝓝[>] (0 : ℝ), |s r| ≤ Cs)
    (hU : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt U (U' r) r)
    (hsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E, ⟪U r X, Y⟫ = ⟪X, U r Y⟫)
    (hU0 : Tendsto U (𝓝[>] 0) (𝓝 0))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      -(⟪U r (U r X), X⟫ + 2 * (s' r / s r) * ⟪U r X, X⟫) ≤ ⟪U' r X, X⟫) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E, 0 ≤ ⟪U r X, X⟫ := by
  set m : ℝ → ℝ := fun r => minRayleigh (U r) with hm_def
  -- continuity of `m` on `(0, r₀)` from the 1-Lipschitz bound
  have hmten : ∀ x ∈ Ioo (0 : ℝ) r₀, ContinuousAt m x := by
    intro x hx
    have h1 : Tendsto (fun y => U y - U x) (𝓝 x) (𝓝 (U x - U x)) :=
      (hU x hx).continuousAt.tendsto.sub tendsto_const_nhds
    rw [sub_self] at h1
    have h2 : Tendsto (fun y => ‖U y - U x‖) (𝓝 x) (𝓝 0) := by
      simpa using h1.norm
    have h3 : Tendsto (fun y => m y - m x) (𝓝 x) (𝓝 0) :=
      squeeze_zero_norm
        (fun y => by simpa using abs_minRayleigh_sub_le (U y) (U x)) h2
    have h4 := h3.add_const (m x)
    simpa using h4
  -- `m → 0` at `0⁺`
  have hm0 : Tendsto m (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm (fun r => by simpa using abs_minRayleigh_le (U r)) ?_
    simpa using hU0.norm
  -- reduce to nonnegativity of `m`
  suffices hmain : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 ≤ m r by
    intro r hr X
    rcases eq_or_ne X 0 with rfl | hXne
    · simp
    have hunit : ‖(‖X‖⁻¹ : ℝ) • X‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hXne
    have h1 : (0 : ℝ) ≤ ⟪U r ((‖X‖⁻¹ : ℝ) • X), (‖X‖⁻¹ : ℝ) • X⟫ :=
      (hmain r hr).trans (minRayleigh_le hunit)
    rw [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
    have hX : (0 : ℝ) < ‖X‖ := norm_pos_iff.mpr hXne
    have hXi : (0 : ℝ) < ‖X‖⁻¹ := inv_pos.mpr hX
    by_contra hneg
    push Not at hneg
    have h3 : ‖X‖⁻¹ * (‖X‖⁻¹ * ⟪U r X, X⟫) < 0 :=
      mul_neg_of_pos_of_neg hXi (mul_neg_of_pos_of_neg hXi hneg)
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨r₂, hr₂, hm₂⟩ := hcon
  -- a bound `W` for `‖U‖` (hence `|m|`) on `(0, r₂]`
  obtain ⟨W, hW0, hWb⟩ : ∃ W, 0 ≤ W ∧ ∀ r ∈ Ioc (0 : ℝ) r₂, ‖U r‖ ≤ W := by
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖U r‖ ≤ 1 := by
      have h2 : Tendsto (fun r => ‖U r‖) (𝓝[>] 0) (𝓝 0) := by simpa using hU0.norm
      exact (h2.eventually (eventually_lt_nhds one_pos)).mono fun r hr => hr.le
    obtain ⟨ε, hε, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h1
    have hε₁pos : 0 < min ε r₂ := lt_min hε hr₂.1
    obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Icc (min ε r₂) r₂, ‖U x‖ ≤ C := by
      refine (isCompact_Icc).exists_bound_of_continuousOn fun x hx => ?_
      exact ((hU x ⟨lt_of_lt_of_le hε₁pos hx.1,
        lt_of_le_of_lt hx.2 hr₂.2⟩).continuousAt).continuousWithinAt
    refine ⟨max 1 C, le_trans zero_le_one (le_max_left _ _), fun r hr => ?_⟩
    rcases lt_or_ge r (min ε r₂) with hlt | hge
    · exact le_trans (hIoo ⟨hr.1, lt_of_lt_of_le hlt (min_le_left _ _)⟩)
        (le_max_left _ _)
    · exact le_trans (hC r ⟨hge, hr.2⟩) (le_max_right _ _)
  have hmW : ∀ r ∈ Ioc (0 : ℝ) r₂, -(m r) ≤ W := by
    intro r hr
    have := (abs_minRayleigh_le (U r)).trans (hWb r hr)
    have habs := neg_abs_le (m r)
    linarith
  -- `r₃`: the last time `m` was nonnegative before `r₂`
  set S : Set ℝ := insert 0 {r ∈ Ioc (0 : ℝ) r₂ | 0 ≤ m r} with hS
  have hS0 : (0 : ℝ) ∈ S := mem_insert _ _
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hSbdd : BddAbove S := by
    refine ⟨r₂, ?_⟩
    rintro x (rfl | ⟨hx, -⟩)
    · exact hr₂.1.le
    · exact hx.2
  set r₃ : ℝ := sSup S with hr₃def
  have hr₃0 : 0 ≤ r₃ := le_csSup hSbdd hS0
  have hr₃r₂ : r₃ < r₂ := by
    have hev : ∀ᶠ y in 𝓝 r₂, m y < 0 :=
      (hmten r₂ hr₂).eventually (eventually_lt_nhds hm₂)
    obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
    have hbound : ∀ x ∈ S, x ≤ max l 0 := by
      rintro x (rfl | ⟨hx1, hx2⟩)
      · exact le_max_right _ _
      by_contra hgt
      push Not at hgt
      have hxIoo : x ∈ Ioo l u :=
        ⟨lt_of_le_of_lt (le_max_left _ _) hgt, lt_of_le_of_lt hx1.2 hmem.2⟩
      exact absurd hx2 (not_le.mpr (hsub hxIoo))
    exact lt_of_le_of_lt (csSup_le hSne hbound) (max_lt hmem.1 hr₂.1)
  have hmneg : ∀ x ∈ Ioc r₃ r₂, m x < 0 := by
    intro x hx
    by_contra hge
    push Not at hge
    have hxS : x ∈ S :=
      mem_insert_of_mem _ ⟨⟨lt_of_le_of_lt hr₃0 hx.1, hx.2⟩, hge⟩
    exact absurd (le_csSup hSbdd hxS) (not_le.mpr hx.1)
  have hr₃m : 0 < r₃ → 0 ≤ m r₃ := by
    intro hr₃pos
    by_contra hneg
    push Not at hneg
    have hr₃mem : r₃ ∈ Ioo (0 : ℝ) r₀ :=
      ⟨hr₃pos, lt_trans (lt_of_lt_of_le hr₃r₂ le_rfl) hr₂.2⟩
    have hev : ∀ᶠ y in 𝓝 r₃, m y < 0 :=
      (hmten r₃ hr₃mem).eventually (eventually_lt_nhds hneg)
    obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
    obtain ⟨x, hxS, hxgt⟩ :=
      exists_lt_of_lt_csSup hSne (show max l 0 < r₃ from max_lt hmem.1 hr₃pos)
    have hxle : x ≤ r₃ := le_csSup hSbdd hxS
    rcases hxS with rfl | ⟨hx1, hx2⟩
    · exact absurd hxgt (not_lt.mpr (le_max_right _ _))
    have hxIoo : x ∈ Ioo l u :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hxgt, lt_of_le_of_lt hxle hmem.2⟩
    exact absurd hx2 (not_le.mpr (hsub hxIoo))
  -- the weighted function `h = (−m)·ρ` with `ρ = s²e^{−Wr}`
  set ρ : ℝ → ℝ := fun r => s r ^ 2 * Real.exp (-(W * r)) with hρ_def
  set h : ℝ → ℝ := fun r => -(m r) * ρ r with hh_def
  have hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r := by
    intro r hr
    have := hspos r hr
    positivity
  have hρd : ∀ x ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt ρ ((2 * s x * s' x - W * s x ^ 2) * Real.exp (-(W * x))) x := by
    intro x hx
    have h1 : HasDerivAt (fun r => s r ^ 2) (2 * s x * s' x) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hs x hx).pow 2
    have h2 : HasDerivAt (fun r => Real.exp (-(W * r)))
        (Real.exp (-(W * x)) * -W) x := by
      have h3 : HasDerivAt (fun r : ℝ => -(W * r)) (-W) x := by
        simpa using ((hasDerivAt_id x).const_mul W).neg
      exact HasDerivAt.exp h3
    have := h1.mul h2
    convert this using 1
    ring
  -- continuity of `h` on `(0, r₀)`
  have hhcont : ∀ x ∈ Ioo (0 : ℝ) r₀, ContinuousAt h x := by
    intro x hx
    exact ((hmten x hx).neg).mul ((hρd x hx).continuousAt)
  -- key: left difference quotients of `h` are eventually `< δ` on `(r₃, r₂]`
  have hslopeh : ∀ x ∈ Ioc r₃ r₂, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ y in 𝓝[<] x, slope h y x < δ := by
    intro x hx δ hδ
    have hxIoo : x ∈ Ioo (0 : ℝ) r₀ :=
      ⟨lt_of_le_of_lt hr₃0 hx.1, lt_of_le_of_lt hx.2 hr₂.2⟩
    have hx02 : x ∈ Ioc (0 : ℝ) r₂ := ⟨hxIoo.1, hx.2⟩
    have hρx : 0 < ρ x := hρpos x hxIoo
    have hsx : 0 < s x := hspos x hxIoo
    -- minimizer and eigenvector at `x`
    obtain ⟨X₀, hX₀unit, hX₀val, hX₀min⟩ := exists_norm_eq_one_minRayleigh (U x)
    have heig : U x X₀ = ⟪U x X₀, X₀⟫ • X₀ :=
      apply_eq_minRayleigh_smul (hsymm x hxIoo) hX₀unit hX₀min
    -- the support function `φ` and its derivative at `x`
    have hφd : HasDerivAt (fun y => ⟪U y X₀, X₀⟫) ⟪U' x X₀, X₀⟫ x := by
      have h1 : HasDerivAt (fun y => U y X₀) (U' x X₀) x := by
        simpa using (hU x hxIoo).clm_apply (hasDerivAt_const x X₀)
      simpa using h1.inner ℝ (hasDerivAt_const x X₀)
    -- derivative lower bound at the eigenvector, exact by the eigen relation
    have hφ'lb : -(m x ^ 2 + 2 * (s' x / s x) * m x) ≤ ⟪U' x X₀, X₀⟫ := by
      have h1 := hric x hxIoo X₀
      have h2 : ⟪U x X₀, X₀⟫ = m x := hX₀val
      have h3 : ⟪U x (U x X₀), X₀⟫ = m x ^ 2 := by
        rw [heig, map_smul, real_inner_smul_left, h2]
        ring
      rw [h3, h2] at h1
      linarith
    -- eventual lower bound for left slopes of `m`
    set δ₁ : ℝ := δ / (2 * ρ x) with hδ₁_def
    have hδ₁pos : 0 < δ₁ := by positivity
    have hm_slope : ∀ᶠ y in 𝓝[<] x, ⟪U' x X₀, X₀⟫ - δ₁ < slope m y x :=
      eventually_lt_slope_of_upper_support
        (fun y => minRayleigh_le hX₀unit) hX₀val.symm hφd hδ₁pos
    -- the product term converges
    set ρ'x : ℝ := (2 * s x * s' x - W * s x ^ 2) * Real.exp (-(W * x)) with hρ'x_def
    have hρslope : Tendsto (fun y => slope ρ y x) (𝓝[<] x) (𝓝 ρ'x) := by
      have h1 := hasDerivAt_iff_tendsto_slope.mp (hρd x hxIoo)
      have h2 := h1.mono_left
        (nhdsWithin_mono x (fun y (hy : y < x) => ne_of_lt hy))
      exact h2.congr fun y => slope_comm ρ x y
    have hwcont : Tendsto (fun y => -(m y)) (𝓝[<] x) (𝓝 (-(m x))) :=
      ((hmten x hxIoo).neg).tendsto.mono_left nhdsWithin_le_nhds
    have hprod : Tendsto (fun y => -(m y) * slope ρ y x) (𝓝[<] x)
        (𝓝 (-(m x) * ρ'x)) := hwcont.mul hρslope
    have hprod_ev : ∀ᶠ y in 𝓝[<] x,
        -(m y) * slope ρ y x < -(m x) * ρ'x + δ / 2 :=
      hprod.eventually (eventually_lt_nhds (by linarith))
    -- the main term is nonpositive: `ρ(m² + 2am) − m·ρ' = e·s²·m·(m + W) ≤ 0`
    have hmx : m x < 0 := hmneg x hx
    have hmxW : -(m x) ≤ W := hmW x hx02
    have hmain_le : ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + -(m x) * ρ'x ≤ 0 := by
      have hexp : (0 : ℝ) < Real.exp (-(W * x)) := Real.exp_pos _
      have hkey : ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + -(m x) * ρ'x
          = Real.exp (-(W * x)) * s x ^ 2 * (m x * (m x + W)) := by
        rw [hρ_def, hρ'x_def]
        field_simp
        ring
      rw [hkey]
      have h1 : m x * (m x + W) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hmx.le (by linarith)
      have h2 : (0 : ℝ) ≤ Real.exp (-(W * x)) * s x ^ 2 := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos h2 h1
    -- assemble the eventual bound for `slope h y x`
    filter_upwards [hm_slope, hprod_ev, self_mem_nhdsWithin]
      with y h1 h2 (h3 : y < x)
    have hxy : x - y ≠ 0 := by
      intro hzero
      have : x = y := by linarith [sub_eq_zero.mp hzero]
      linarith
    have hkey : slope h y x = ρ x * (-(slope m y x)) + -(m y) * slope ρ y x := by
      rw [slope_def_field, slope_def_field, slope_def_field, hh_def]
      field_simp
      ring
    have hb1 : -(slope m y x) < -(⟪U' x X₀, X₀⟫) + δ₁ := by linarith
    have hb2 : -(⟪U' x X₀, X₀⟫) ≤ m x ^ 2 + 2 * (s' x / s x) * m x := by
      linarith
    have hb3 : ρ x * (-(slope m y x)) <
        ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + ρ x * δ₁ := by
      have h4 : -(slope m y x) < m x ^ 2 + 2 * (s' x / s x) * m x + δ₁ := by
        linarith
      have h5 := mul_lt_mul_of_pos_left h4 hρx
      rw [mul_add] at h5
      exact h5
    have hδ₁ρ : ρ x * δ₁ = δ / 2 := by
      rw [hδ₁_def]
      field_simp
    rw [hkey]
    calc ρ x * (-(slope m y x)) + -(m y) * slope ρ y x
        < (ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + ρ x * δ₁)
          + (-(m x) * ρ'x + δ / 2) := by linarith
      _ = (ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + -(m x) * ρ'x)
          + (ρ x * δ₁ + δ / 2) := by ring
      _ ≤ 0 + (δ / 2 + δ / 2) := by rw [hδ₁ρ]; linarith
      _ = δ := by ring
  -- `h` is positive at `r₂`
  have hh2pos : 0 < h r₂ := by
    have hw2 : 0 < -(m r₂) := neg_pos.mpr hm₂
    have hρ2 : 0 < ρ r₂ := hρpos r₂ hr₂
    exact mul_pos hw2 hρ2
  -- but `h` drops below `h r₂` somewhere on `(r₃, r₂)`
  obtain ⟨rb, hrbmem, hrblt⟩ : ∃ rb ∈ Ioo r₃ r₂, h rb < h r₂ := by
    have hIoomem : Ioo r₃ r₂ ∈ 𝓝[>] r₃ := Ioo_mem_nhdsGT hr₃r₂
    rcases eq_or_lt_of_le hr₃0 with hr₃eq | hr₃pos
    · -- `r₃ = 0`: `h → 0` at `0⁺`
      have hten : Tendsto h (𝓝[>] r₃) (𝓝 0) := by
        rw [← hr₃eq]
        have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖h r‖ ≤ |m r| * Cs ^ 2 := by
          filter_upwards [hsbdd, self_mem_nhdsWithin] with r hr (hrpos : 0 < r)
          have hρle : ρ r ≤ Cs ^ 2 := by
            have h1 : s r ^ 2 ≤ Cs ^ 2 := by
              have := sq_abs (s r)
              nlinarith [abs_nonneg (s r)]
            have h2 : Real.exp (-(W * r)) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              nlinarith
            nlinarith [sq_nonneg (s r), Real.exp_pos (-(W * r))]
          have hρnn : 0 ≤ ρ r := by positivity
          rw [hh_def]
          simp only [norm_mul, Real.norm_eq_abs, abs_neg]
          calc |m r| * |ρ r| = |m r| * ρ r := by rw [abs_of_nonneg hρnn]
            _ ≤ |m r| * Cs ^ 2 := by
                exact mul_le_mul_of_nonneg_left hρle (abs_nonneg _)
        have hg0 : Tendsto (fun r => |m r| * Cs ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have := (hm0.abs).mul_const (Cs ^ 2)
          simpa using this
        exact squeeze_zero_norm' hbound hg0
      have hev := (hten.eventually (eventually_lt_nhds hh2pos)).and hIoomem
      obtain ⟨rb, hrb1, hrb2⟩ := hev.exists
      exact ⟨rb, hrb2, hrb1⟩
    · -- `r₃ > 0`: `h` continuous at `r₃` with `h r₃ ≤ 0`
      have hr₃mem : r₃ ∈ Ioo (0 : ℝ) r₀ := ⟨hr₃pos, lt_trans hr₃r₂ hr₂.2⟩
      have hh3 : h r₃ ≤ 0 := by
        have hw3 : -(m r₃) ≤ 0 := by linarith [hr₃m hr₃pos]
        have hρ3 : 0 ≤ ρ r₃ := (hρpos r₃ hr₃mem).le
        exact mul_nonpos_of_nonpos_of_nonneg hw3 hρ3
      have hten : Tendsto h (𝓝[>] r₃) (𝓝 (h r₃)) :=
        (hhcont r₃ hr₃mem).tendsto.mono_left nhdsWithin_le_nhds
      have hev := (hten.eventually
        (eventually_lt_nhds (lt_of_le_of_lt hh3 hh2pos))).and hIoomem
      obtain ⟨rb, hrb1, hrb2⟩ := hev.exists
      exact ⟨rb, hrb2, hrb1⟩
  -- the barrier lemma on `[rb, r₂]` gives the contradiction
  have hcontIcc : ContinuousOn h (Icc rb r₂) := by
    intro z hz
    have hzIoo : z ∈ Ioo (0 : ℝ) r₀ :=
      ⟨lt_of_le_of_lt hr₃0 (lt_of_lt_of_le hrbmem.1 hz.1),
        lt_of_le_of_lt hz.2 hr₂.2⟩
    exact (hhcont z hzIoo).continuousWithinAt
  have hslopeIcc : ∀ x ∈ Ioc rb r₂, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ y in 𝓝[<] x, slope h y x < δ := by
    intro x hx δ hδ
    exact hslopeh x ⟨lt_trans hrbmem.1 hx.1, hx.2⟩ δ hδ
  have hfinal := le_of_left_slope_eventually_lt hrbmem.2.le hcontIcc hslopeIcc
  linarith

end MorganTianLib
