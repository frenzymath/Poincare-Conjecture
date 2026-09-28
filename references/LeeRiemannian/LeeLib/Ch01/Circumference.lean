import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.ConstantSpeed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The circumference of a Euclidean circle

This file formalizes Theorem 1.4 of J. M. Lee, *Introduction to Riemannian Manifolds*
(2nd ed., GTM 176): **the circumference of a Euclidean circle of radius `R` is `2 π R`**.

"Circumference" is interpreted as the length of the circle *as a curve*, and length is
mathlib's canonical notion of the length of a curve: the total variation `eVariationOn`,
i.e. the supremum over all finite increasing sequences of parameters of the sum of the
lengths of the inscribed chords. Nothing here is defined to be `2 π R`; the value is
computed from the chord sums.

The Euclidean plane is modelled by `ℂ` and the circle of centre `c` and radius `R` by
mathlib's `circleMap c R θ = c + R * exp (θ * I)`.

## Main results

* `LeeLib.Ch01.dist_circleMap_circleMap`: the chord length formula
  `dist (circleMap c R x) (circleMap c R y) = |R| * |2 * sin ((x - y) / 2)|`.
* `LeeLib.Ch01.eVariationOn_circleMap_Icc_le`: the upper bound, from the fact that `circleMap c R`
  is `|R|`-Lipschitz.
* `LeeLib.Ch01.ofReal_le_eVariationOn_circleMap_Icc`: the lower bound, from the inscribed regular
  polygons.
* `LeeLib.Ch01.eVariationOn_circleMap_Icc`: the length of `circleMap c R` over `Icc a b` is
  `|R| * (b - a)`.
* `LeeLib.Ch01.circumference_circle`: **Theorem 1.4**, the circumference of a circle of radius `R`
  is `2 * π * R`, stated as
  `eVariationOn (circleMap c R) (Set.Icc 0 (2 * π)) = ENNReal.ofReal (2 * π * R)`.
* `LeeLib.Ch01.hasConstantSpeedOnWith_circleMap`: the standard parametrization of the circle has
  constant speed `|R|`.

## Implementation notes

The pinned mathlib has no bridge between `eVariationOn` and `∫ ‖deriv f‖`, so both bounds
are obtained by hand from the definition of `eVariationOn` as a supremum of chord sums.

## Tags

circle, circumference, arc length, total variation
-/

open Complex Filter Metric Real Set

open scoped ENNReal NNReal Topology

namespace LeeLib.Ch01

/-- **Chord length formula.** The distance between two points `circleMap c R x` and
`circleMap c R y` on the circle of centre `c` and radius `R` is `|R| * |2 sin ((x - y) / 2)|`. -/
theorem dist_circleMap_circleMap (c : ℂ) (R x y : ℝ) :
    dist (circleMap c R x) (circleMap c R y) = |R| * |2 * Real.sin ((x - y) / 2)| := by
  have hexp : Complex.exp ((y : ℂ) * Complex.I) * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1)
      = Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hsub : circleMap c R x - circleMap c R y
      = (R : ℂ) * (Complex.exp ((y : ℂ) * Complex.I)
          * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1)) := by
    rw [hexp]
    simp only [circleMap]
    ring
  rw [dist_eq_norm, hsub, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs]

/-- The chord length formula, in the form of an extended distance. -/
theorem edist_circleMap_circleMap (c : ℂ) (R x y : ℝ) :
    edist (circleMap c R x) (circleMap c R y)
      = ENNReal.ofReal (|R| * |2 * Real.sin ((x - y) / 2)|) := by
  rw [edist_dist, dist_circleMap_circleMap]

/-! ### The upper bound -/

/-- **Upper bound for the circumference.** Since `circleMap c R` is `|R|`-Lipschitz, its
length over `Icc a b` is at most `|R| * (b - a)`. -/
theorem eVariationOn_circleMap_Icc_le (c : ℂ) (R a b : ℝ) :
    eVariationOn (circleMap c R) (Set.Icc a b) ≤ ENNReal.ofReal (|R| * (b - a)) := by
  have hid : eVariationOn (id : ℝ → ℝ) (Set.Icc a b) ≤ ENNReal.ofReal (b - a) := by
    have h := (monotoneOn_id (s := (Set.univ : Set ℝ))).eVariationOn_le
      (a := a) (b := b) (Set.mem_univ a) (Set.mem_univ b)
    simpa using h
  have hlip : LipschitzOnWith (Real.nnabs R) (circleMap c R) Set.univ :=
    (lipschitzWith_circleMap c R).lipschitzOnWith
  have hcomp := hlip.comp_eVariationOn_le
    (g := (id : ℝ → ℝ)) (s := Set.Icc a b) (Set.mapsTo_univ _ _)
  simp only [Function.comp_def, id_eq] at hcomp
  calc eVariationOn (circleMap c R) (Set.Icc a b)
      ≤ (Real.nnabs R : ℝ≥0∞) * eVariationOn (id : ℝ → ℝ) (Set.Icc a b) := hcomp
    _ ≤ (Real.nnabs R : ℝ≥0∞) * ENNReal.ofReal (b - a) := by gcongr
    _ = ENNReal.ofReal (|R| * (b - a)) := by
        rw [ENNReal.ofReal_mul (abs_nonneg R)]
        congr 1
        rw [show |R| = ((Real.nnabs R : ℝ≥0) : ℝ) from (Real.coe_nnabs R).symm,
          ENNReal.ofReal_coe_nnreal]

/-! ### The lower bound -/

/-- The elementary chord identity behind the inscribed-polygon computation: `n` chords, each
subtending an angle `d / n`, have total length `d * sinc (d / (2 * n))` (times the radius). -/
private theorem nat_mul_two_mul_sin_half_div (d : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) * (2 * Real.sin (d / (2 * n))) = d * Real.sinc (d / (2 * n)) := by
  have hn' : (0 : ℝ) < n := by positivity
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · have ht : d / (2 * n) ≠ 0 := div_ne_zero hd (by positivity)
    rw [Real.sinc_of_ne_zero ht]
    field_simp

/-- The `n`-th inscribed polygon: the sum of the lengths of the `n` chords cut out on the arc
`circleMap c R '' Icc a b` by the regular subdivision of `Icc a b` into `n` equal pieces.
It equals `|R| * ((b - a) * sinc ((b - a) / (2 * n)))` once `(b - a) / (2 * n) ≤ π`. -/
private theorem inscribed_polygon_sum (R : ℝ) {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : n ≠ 0)
    (hle : (b - a) / (2 * n) ≤ π) :
    ∑ _i ∈ Finset.range n, ENNReal.ofReal
        (|R| * |2 * Real.sin (((a + (b - a) / n) - a) / 2)|)
      = ENNReal.ofReal (|R| * ((b - a) * Real.sinc ((b - a) / (2 * n)))) := by
  have hn' : (0 : ℝ) < n := by
    have : n ≠ 0 := hn
    positivity
  have harg : ((a + (b - a) / n) - a) / 2 = (b - a) / (2 * n) := by
    field_simp
    ring
  have ht0 : 0 ≤ (b - a) / (2 * n) := div_nonneg (by linarith) (by positivity)
  have hsin : 0 ≤ Real.sin ((b - a) / (2 * n)) := Real.sin_nonneg_of_nonneg_of_le_pi ht0 hle
  rw [harg, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  congr 1
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sin ((b - a) / (2 * n))),
    show (n : ℝ) * (|R| * (2 * Real.sin ((b - a) / (2 * n))))
      = |R| * ((n : ℝ) * (2 * Real.sin ((b - a) / (2 * n)))) from by ring,
    nat_mul_two_mul_sin_half_div (b - a) hn]

/-- **Lower bound for the circumference.** Approximating the arc by inscribed regular
polygons shows that the length of `circleMap c R` over `Icc a b` is at least
`|R| * (b - a)`. -/
theorem ofReal_le_eVariationOn_circleMap_Icc (c : ℂ) (R : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (|R| * (b - a)) ≤ eVariationOn (circleMap c R) (Set.Icc a b) := by
  -- The `n`-th inscribed polygon has length `|R| * ((b - a) * sinc ((b - a) / (2 n)))`.
  set F : ℕ → ℝ := fun n => |R| * ((b - a) * Real.sinc ((b - a) / (2 * n))) with hF
  have key : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (F n) ≤ eVariationOn (circleMap c R) (Set.Icc a b) := by
    have hev : ∀ᶠ n : ℕ in atTop, n ≠ 0 ∧ (b - a) / (2 * n) ≤ π := by
      have h1 : ∀ᶠ n : ℕ in atTop, n ≠ 0 := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        omega
      have h2 : ∀ᶠ n : ℕ in atTop, (b - a) / (2 * n) ≤ π := by
        have hlim : Tendsto (fun n : ℕ => (b - a) / (2 * (n : ℝ))) atTop (𝓝 0) := by
          simp_rw [mul_comm (2 : ℝ), ← div_div]
          simpa using (tendsto_const_div_atTop_nhds_zero_nat (b - a)).div_const 2
        exact hlim.eventually_le_const Real.pi_pos
      filter_upwards [h1, h2] with n hn1 hn2 using ⟨hn1, hn2⟩
    filter_upwards [hev] with n ⟨hn, hle⟩
    -- the regular subdivision of `Icc a b` into `n` pieces
    set u : ℕ → ℝ := fun i => a + i * ((b - a) / n) with hu
    have hn' : (0 : ℝ) < n := by positivity
    have hstep : 0 ≤ (b - a) / n := div_nonneg (by linarith) (le_of_lt hn')
    have humono : MonotoneOn u (Set.Iic n) := by
      intro i _ j _ hij
      simp only [hu]
      have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
      nlinarith
    have humem : ∀ i ≤ n, u i ∈ Set.Icc a b := by
      intro i hi
      constructor
      · simp only [hu]
        nlinarith [Nat.cast_nonneg (α := ℝ) i]
      · simp only [hu]
        have : (i : ℝ) ≤ n := Nat.cast_le.2 hi
        have : (i : ℝ) * ((b - a) / n) ≤ (n : ℝ) * ((b - a) / n) := by nlinarith
        rw [mul_div_cancel₀ _ (ne_of_gt hn')] at this
        linarith
    have hsum := eVariationOn.sum_le_of_monotoneOn_Iic (f := circleMap c R)
      (s := Set.Icc a b) (n := n) (u := u) humono humem
    refine le_trans (le_of_eq ?_) hsum
    rw [← inscribed_polygon_sum R hab hn hle]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [edist_circleMap_circleMap]
    congr 2
    simp only [hu]
    push_cast
    ring_nf
  -- the polygon lengths converge to `|R| * (b - a)`
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (F n)) atTop
      (𝓝 (ENNReal.ofReal (|R| * (b - a)))) := by
    have h0 : Tendsto (fun n : ℕ => (b - a) / (2 * (n : ℝ))) atTop (𝓝 0) := by
      simp_rw [mul_comm (2 : ℝ), ← div_div]
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (b - a)).div_const 2
    have hsinc : Tendsto (fun n : ℕ => Real.sinc ((b - a) / (2 * (n : ℝ)))) atTop (𝓝 1) := by
      have := (Real.continuous_sinc.tendsto 0).comp h0
      rwa [Real.sinc_zero] at this
    have : Tendsto F atTop (𝓝 (|R| * ((b - a) * 1))) := by
      exact tendsto_const_nhds.mul (tendsto_const_nhds.mul hsinc)
    rw [mul_one] at this
    exact ENNReal.tendsto_ofReal this
  exact le_of_tendsto hlim key

/-! ### The circumference theorem -/

/-- **The length of a circular arc.** The length (total variation) of the standard
parametrization `circleMap c R` of the circle of centre `c` and radius `R`, over the
parameter interval `Icc a b`, equals `|R| * (b - a)`. -/
theorem eVariationOn_circleMap_Icc (c : ℂ) (R : ℝ) {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (circleMap c R) (Set.Icc a b) = ENNReal.ofReal (|R| * (b - a)) :=
  le_antisymm (eVariationOn_circleMap_Icc_le c R a b)
    (ofReal_le_eVariationOn_circleMap_Icc c R hab)

/-- **Theorem 1.4 (Lee, *Introduction to Riemannian Manifolds*).**
*The circumference of a Euclidean circle of radius `R` is `2 π R`.*

The circle of centre `c` and radius `R ≥ 0` in the Euclidean plane `ℂ` is the curve
`circleMap c R : ℝ → ℂ`, `θ ↦ c + R * exp (θ * I)`, traversed once as `θ` runs over
`[0, 2π]`. Its circumference is its length as a curve, i.e. its total variation, and this
equals `2 * π * R`. -/
theorem circumference_circle (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    eVariationOn (circleMap c R) (Set.Icc 0 (2 * π)) = ENNReal.ofReal (2 * π * R) := by
  rw [eVariationOn_circleMap_Icc c R (by positivity), abs_of_nonneg hR]
  ring_nf

/-- The standard parametrization of the circle of radius `R` has constant speed `|R|`:
the length of the arc traced out for the parameter in `Icc x y` is `|R| * (y - x)`.
This is Lee's observation that `θ ↦ c + R e^{iθ}` is a constant-speed parametrization. -/
theorem hasConstantSpeedOnWith_circleMap (c : ℂ) (R : ℝ) :
    HasConstantSpeedOnWith (circleMap c R) Set.univ (Real.nnabs R) := by
  rw [hasConstantSpeedOnWith_iff_ordered]
  intro x _ y _ hxy
  rw [Set.univ_inter, eVariationOn_circleMap_Icc c R hxy]
  congr 1

end LeeLib.Ch01
