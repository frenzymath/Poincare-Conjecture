import PetersenLib.Ch01.RiemannianManifolds
import PetersenLib.Foundations.WhitneyEven
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Petersen Ch. 1, §1.4.4 — polar versus Cartesian coordinates and the
smoothness criterion at the origin

Writing `x = t·s` with `t = |x| > 0` and `s ∈ Sⁿ⁻¹`, the rotationally
symmetric metric `dt² + ρ²(t) ds²_{n-1}` reads in Cartesian coordinates as
```
(1/t² − ρ²(t)/t⁴) (Σ xⁱ dxⁱ)² + (ρ²(t)/t²) Σ (dxⁱ)²
```
(`polarToCartesianFormula`). For ambient dimension `n ≥ 1` it extends to a
smooth metric across the origin if and only if `ρ(0) = 0`, `ρ̇(0) = 1`, and
all even-order derivatives of `ρ` vanish at `0`
(`rotationallySymmetricSmoothnessCriterion`).

The proof of the criterion rests on the correspondence between smooth
functions of `x` near `0` that are rotationally invariant and smooth even
functions of `t` — Whitney's even-function theorem (`f` smooth even iff
`f(t) = g(t²)` with `g` smooth), provided by
`PetersenLib.Foundations.WhitneyEven` through the norm-composition theorems
`contDiff_even_comp_norm` and `contDiff_flat_comp_norm` and the Hadamard
quotient `hadamardDiv`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.4.
-/

noncomputable section

open Real Set Filter
open scoped ContDiff Topology

namespace PetersenLib

variable {n : ℕ}

/-- **Math.** Petersen §1.4.4 (Lemma, polar-coordinate change): write
`x = t·s`, `t = |x| > 0`, `s ∈ Sⁿ⁻¹`. Since `dt = (1/t) Σ xⁱ dxⁱ` and
`t² ds²_{n-1} = Σ (dxⁱ)² − dt²`, the rotationally symmetric metric is
```
dt² + ρ²(t) ds²_{n-1}
  = (1/t² − ρ²(t)/t⁴) (Σ sⁱ dxⁱ)² t² + (ρ²(t)/t²) Σ (dxⁱ)²,
```
stated here on tangent vectors `u, v` at `x ≠ 0`: the radial part
`dt(u) = ⟨x,u⟩/t` and the spherical part
`ds²(u,v) = (⟨u,v⟩ − ⟨x,u⟩⟨x,v⟩/t²)/t²` recombine into the displayed
Cartesian form. -/
theorem polarToCartesianFormula (ρ : ℝ → ℝ) (x u v : EuclideanSpace ℝ (Fin n))
    (hx : x ≠ 0) :
    (@inner ℝ _ _ x u / ‖x‖) * (@inner ℝ _ _ x v / ‖x‖) +
      (ρ ‖x‖) ^ 2 *
        ((@inner ℝ _ _ u v - @inner ℝ _ _ x u * @inner ℝ _ _ x v / ‖x‖ ^ 2) /
          ‖x‖ ^ 2) =
    (1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4) *
        (@inner ℝ _ _ x u * @inner ℝ _ _ x v) +
      (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 * @inner ℝ _ _ u v := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp
  ring

/-- **Math.** The rotationally symmetric metric `dt² + ρ²(t) ds²_{n-1}`
written in Cartesian coordinates: the bilinear form
`B_x(u, v) = (1/t² − ρ²(t)/t⁴)⟨x,u⟩⟨x,v⟩ + (ρ²(t)/t²)⟨u,v⟩` at `t = |x|`
(cf. `polarToCartesianFormula`). Extending this form smoothly across `x = 0`
is the subject of the smoothness criterion. -/
def rotSymCartesianForm (ρ : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4) *
      (@inner ℝ _ _ x u * @inner ℝ _ _ x v) +
    (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 * @inner ℝ _ _ u v

/-- The value of the Hadamard quotient at `0` is the derivative:
`hadamardDiv f 0 = ∫ s in 0..1, f' 0 = f' 0`. -/
private lemma hadamardDiv_zero (f : ℝ → ℝ) : hadamardDiv f 0 = deriv f 0 := by
  simp [hadamardDiv]

/-- The Hadamard quotient of a smooth function that is flat at `0` (all iterated
derivatives vanish) is again flat at `0`: differentiating under the integral sign,
`(hadamardDiv f)⁽ᵐ⁾(0) = ∫ s in 0..1, sᵐ f⁽ᵐ⁺¹⁾(0) = 0`. -/
private lemma hadamardDiv_flat {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hflat : ∀ m : ℕ, iteratedDeriv m f 0 = 0) (m : ℕ) :
    iteratedDeriv m (hadamardDiv f) 0 = 0 := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have he : hadamardDiv f = fun t => ∫ s in (0 : ℝ)..1, (1 : ℝ) * deriv f (t * s) := by
    funext t
    simp [hadamardDiv]
  rw [he, iteratedDeriv_parametricHadamard m (w := fun _ => (1 : ℝ)) (ξ := deriv f)
    continuous_const hd 0]
  have h1 : iteratedDeriv m (deriv f) 0 = 0 := by
    have h := hflat (m + 1)
    rwa [iteratedDeriv_succ'] at h
  calc (∫ s in (0 : ℝ)..1, (1 : ℝ) * s ^ m * iteratedDeriv m (deriv f) (0 * s))
      = ∫ s in (0 : ℝ)..1, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun s _hs => ?_
        rw [zero_mul, h1, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

/-- Backward direction of the smoothness criterion: the derivative conditions on `ρ`
produce the two smooth coefficient functions `F₁, F₂` (in fact globally, so any radius
works; we take `ε = 1`). Positivity of `ρ` is not needed in this direction, nor is
`n ≥ 1`. -/
private theorem smoothnessCriterion_backward (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (h0 : ρ 0 = 0) (h1 : deriv ρ 0 = 1)
    (h2 : ∀ l : ℕ, 1 ≤ l → iteratedDeriv (2 * l) ρ 0 = 0) :
    ∃ (ε : ℝ) (_ : 0 < ε) (F₁ F₂ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε) ∧
      0 < F₁ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Metric.ball 0 ε → x ≠ 0 →
        F₁ x = (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 ∧
        F₂ x = 1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4 := by
  -- odd and even parts of ρ
  set ρo : ℝ → ℝ := fun t => (1 / 2 : ℝ) * (ρ t - ρ (-t)) with hρo_def
  set ρe : ℝ → ℝ := fun t => (1 / 2 : ℝ) * (ρ t + ρ (-t)) with hρe_def
  have hρo_cd : ContDiff ℝ ∞ ρo := by
    rw [hρo_def]
    exact contDiff_const.mul (hρ.sub (hρ.comp contDiff_neg))
  have hρe_cd : ContDiff ℝ ∞ ρe := by
    rw [hρe_def]
    exact contDiff_const.mul (hρ.add (hρ.comp contDiff_neg))
  have hρo_odd : ∀ t, ρo (-t) = -ρo t := by
    intro t
    simp only [hρo_def, neg_neg]
    ring
  -- the even part is flat at 0
  have hρe_flat : ∀ m : ℕ, iteratedDeriv m ρe 0 = 0 := by
    intro m
    have hcalc : iteratedDeriv m ρe 0
        = (1 / 2 : ℝ) * ((1 + (-1 : ℝ) ^ m) * iteratedDeriv m ρ 0) := by
      have hadd : iteratedDeriv m (fun t => ρ t + ρ (-t)) 0
          = iteratedDeriv m ρ 0 + iteratedDeriv m (fun t => ρ (-t)) 0 :=
        iteratedDeriv_fun_add (hρ.contDiffAt.of_le (mod_cast le_top))
          ((hρ.comp contDiff_neg).contDiffAt.of_le (mod_cast le_top))
      have hneg : iteratedDeriv m (fun t => ρ (-t)) 0 = (-1 : ℝ) ^ m * iteratedDeriv m ρ 0 := by
        have h := iteratedDeriv_comp_neg m ρ 0
        rwa [neg_zero, smul_eq_mul] at h
      calc iteratedDeriv m ρe 0
          = (1 / 2 : ℝ) * iteratedDeriv m (fun t => ρ t + ρ (-t)) 0 := by
            simp only [hρe_def, iteratedDeriv_const_mul_field]
        _ = (1 / 2 : ℝ) * ((1 + (-1 : ℝ) ^ m) * iteratedDeriv m ρ 0) := by
            rw [hadd, hneg]
            ring
    rcases Nat.even_or_odd m with hm | hm
    · obtain ⟨k, hk⟩ := hm
      have hm2 : m = 2 * k := by omega
      subst hm2
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [hcalc]
        simp [iteratedDeriv_zero, h0]
      · rw [hcalc, Even.neg_one_pow ⟨k, two_mul k⟩, h2 k hkpos]
        ring
    · rw [hcalc, Odd.neg_one_pow hm]
      ring
  -- the two Hadamard quotients: ρ t = t * (K t + M t)
  set K : ℝ → ℝ := hadamardDiv ρo with hK_def
  set M : ℝ → ℝ := hadamardDiv ρe with hM_def
  have hK_cd : ContDiff ℝ ∞ K := contDiff_hadamardDiv hρo_cd
  have hM_cd : ContDiff ℝ ∞ M := contDiff_hadamardDiv hρe_cd
  have hK_even : ∀ t, K (-t) = K t := fun t => hadamardDiv_even_of_odd hρo_odd t
  have hM_flat : ∀ m : ℕ, iteratedDeriv m M 0 = 0 := hadamardDiv_flat hρe_cd hρe_flat
  have hρo0 : ρo 0 = 0 := eq_zero_of_odd hρo_odd
  have hρe0 : ρe 0 = 0 := by
    have h := hρe_flat 0
    rwa [iteratedDeriv_zero] at h
  have hρo_eq : ∀ t, ρo t = t * K t := by
    intro t
    have h := sub_eq_mul_hadamardDiv hρo_cd t
    rwa [hρo0, sub_zero] at h
  have hρe_eq : ∀ t, ρe t = t * M t := by
    intro t
    have h := sub_eq_mul_hadamardDiv hρe_cd t
    rwa [hρe0, sub_zero] at h
  have hM0 : M 0 = 0 := by
    have h := hM_flat 0
    rwa [iteratedDeriv_zero] at h
  -- K 0 = ρ̇(0) − ρ̇ₑ(0) = 1
  have hρe_d0 : deriv ρe 0 = 0 := by
    have h := hρe_flat 1
    rwa [iteratedDeriv_one] at h
  have hK0 : K 0 = 1 := by
    have hsum : deriv ρ 0 = deriv ρo 0 + deriv ρe 0 := by
      have hfun : ρ = fun t => ρo t + ρe t := by
        funext t
        simp only [hρo_def, hρe_def]
        ring
      conv_lhs => rw [hfun]
      exact deriv_add ((hρo_cd.differentiable (by simp)) 0)
        ((hρe_cd.differentiable (by simp)) 0)
    have hKd : K 0 = deriv ρo 0 := hadamardDiv_zero ρo
    rw [hKd]
    rw [h1, hρe_d0] at hsum
    linarith
  have hρ_eq : ∀ t, ρ t = t * (K t + M t) := by
    intro t
    have hsplit : ρ t = ρo t + ρe t := by
      simp only [hρo_def, hρe_def]
      ring
    rw [hsplit, hρo_eq t, hρe_eq t]
    ring
  -- second-order Hadamard quotients for the F₂ coefficient
  set E : ℝ → ℝ := fun t => 1 - K t ^ 2 with hE_def
  have hE_cd : ContDiff ℝ ∞ E := by
    rw [hE_def]
    exact contDiff_const.sub (hK_cd.pow 2)
  have hE_even : ∀ t, E (-t) = E t := by
    intro t
    simp only [hE_def]
    rw [hK_even t]
  have hE0 : E 0 = 0 := by
    simp only [hE_def]
    rw [hK0]
    norm_num
  set H1 : ℝ → ℝ := hadamardDiv E with hH1_def
  set H2 : ℝ → ℝ := hadamardDiv H1 with hH2_def
  have hH1_cd : ContDiff ℝ ∞ H1 := contDiff_hadamardDiv hE_cd
  have hH2_cd : ContDiff ℝ ∞ H2 := contDiff_hadamardDiv hH1_cd
  have hH1_odd : ∀ t, H1 (-t) = -H1 t := fun t => hadamardDiv_odd_of_even hE_even t
  have hH2_even : ∀ t, H2 (-t) = H2 t := fun t => hadamardDiv_even_of_odd hH1_odd t
  have hH10 : H1 0 = 0 := eq_zero_of_odd hH1_odd
  have hE_eq : ∀ t, E t = t * H1 t := by
    intro t
    have h := sub_eq_mul_hadamardDiv hE_cd t
    rwa [hE0, sub_zero] at h
  have hH1_eq : ∀ t, H1 t = t * H2 t := by
    intro t
    have h := sub_eq_mul_hadamardDiv hH1_cd t
    rwa [hH10, sub_zero] at h
  have hE2 : ∀ t, (1 : ℝ) - K t ^ 2 = t ^ 2 * H2 t := by
    intro t
    have h := hE_eq t
    rw [hH1_eq t] at h
    simp only [hE_def] at h
    rw [h]
    ring
  set V : ℝ → ℝ := hadamardDiv M with hV_def
  set X : ℝ → ℝ := hadamardDiv V with hX_def
  have hV_cd : ContDiff ℝ ∞ V := contDiff_hadamardDiv hM_cd
  have hX_cd : ContDiff ℝ ∞ X := contDiff_hadamardDiv hV_cd
  have hV_flat : ∀ m : ℕ, iteratedDeriv m V 0 = 0 := hadamardDiv_flat hM_cd hM_flat
  have hX_flat : ∀ m : ℕ, iteratedDeriv m X 0 = 0 := hadamardDiv_flat hV_cd hV_flat
  have hV0 : V 0 = 0 := by
    have h := hV_flat 0
    rwa [iteratedDeriv_zero] at h
  have hM_eq : ∀ t, M t = t * V t := by
    intro t
    have h := sub_eq_mul_hadamardDiv hM_cd t
    rwa [hM0, sub_zero] at h
  have hV_eq : ∀ t, V t = t * X t := by
    intro t
    have h := sub_eq_mul_hadamardDiv hV_cd t
    rwa [hV0, sub_zero] at h
  have hM2 : ∀ t, M t = t ^ 2 * X t := by
    intro t
    rw [hM_eq t, hV_eq t]
    ring
  -- assemble the witnesses
  refine ⟨1, one_pos, fun x => (K ‖x‖ + M ‖x‖) ^ 2,
    fun x => H2 ‖x‖ - X ‖x‖ * (2 * K ‖x‖ + M ‖x‖), ?_, ?_, ?_, ?_⟩
  · exact (((contDiff_even_comp_norm hK_cd hK_even).add
      (contDiff_flat_comp_norm hM_cd hM_flat)).pow 2).contDiffOn
  · exact ((contDiff_even_comp_norm hH2_cd hH2_even).sub
      ((contDiff_flat_comp_norm hX_cd hX_flat).mul
        ((contDiff_const.mul (contDiff_even_comp_norm hK_cd hK_even)).add
          (contDiff_flat_comp_norm hM_cd hM_flat)))).contDiffOn
  · show 0 < (K ‖(0 : EuclideanSpace ℝ (Fin n))‖ + M ‖(0 : EuclideanSpace ℝ (Fin n))‖) ^ 2
    rw [norm_zero, hK0, hM0]
    norm_num
  · intro x _hx hx0
    have hT : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    have h2ne : (‖x‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hT
    have h4ne : (‖x‖ : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 hT
    constructor
    · show (K ‖x‖ + M ‖x‖) ^ 2 = ρ ‖x‖ ^ 2 / ‖x‖ ^ 2
      rw [hρ_eq ‖x‖, mul_pow, mul_div_cancel_left₀ _ h2ne]
    · show H2 ‖x‖ - X ‖x‖ * (2 * K ‖x‖ + M ‖x‖) = 1 / ‖x‖ ^ 2 - ρ ‖x‖ ^ 2 / ‖x‖ ^ 4
      have hkey1 : (1 : ℝ) - K ‖x‖ ^ 2 = ‖x‖ ^ 2 * H2 ‖x‖ := hE2 ‖x‖
      have hkey2 : M ‖x‖ = ‖x‖ ^ 2 * X ‖x‖ := hM2 ‖x‖
      have hkey3 : ρ ‖x‖ = ‖x‖ * (K ‖x‖ + M ‖x‖) := hρ_eq ‖x‖
      have key : ‖x‖ ^ 4 * (H2 ‖x‖ - X ‖x‖ * (2 * K ‖x‖ + M ‖x‖))
          = ‖x‖ ^ 2 - ρ ‖x‖ ^ 2 := by
        linear_combination (-(‖x‖ ^ 2)) * hkey1
          + ((2 * K ‖x‖ + M ‖x‖) * ‖x‖ ^ 2) * hkey2
          + (ρ ‖x‖ + ‖x‖ * (K ‖x‖ + M ‖x‖)) * hkey3
      have hgoal : H2 ‖x‖ - X ‖x‖ * (2 * K ‖x‖ + M ‖x‖)
          = (‖x‖ ^ 2 - ρ ‖x‖ ^ 2) / ‖x‖ ^ 4 := by
        rw [eq_div_iff h4ne, ← key]
        ring
      have hsplit : (1 : ℝ) / ‖x‖ ^ 2 - ρ ‖x‖ ^ 2 / ‖x‖ ^ 4
          = (‖x‖ ^ 2 - ρ ‖x‖ ^ 2) / ‖x‖ ^ 4 := by
        field_simp
      rw [hgoal, hsplit]

/-- Forward direction of the smoothness criterion: if the two coefficient functions
extend smoothly over a ball around the origin, then `ρ` satisfies the derivative
conditions. Requires `n ≥ 1` (to have a direction to restrict along) and positivity
of `ρ` on some right-neighbourhood `(0, δ')` of `0`. -/
private theorem smoothnessCriterion_forward (hn : 0 < n) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {δ' : ℝ} (hδ' : 0 < δ') (hρpos : ∀ t, 0 < t → t < δ' → 0 < ρ t)
    {ε : ℝ} (hε : 0 < ε) {F₁ F₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF₁ : ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε)) (hF₂ : ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε))
    (hmatch : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Metric.ball 0 ε → x ≠ 0 →
      F₁ x = (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 ∧ F₂ x = 1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4) :
    ρ 0 = 0 ∧ deriv ρ 0 = 1 ∧ ∀ l : ℕ, 1 ≤ l → iteratedDeriv (2 * l) ρ 0 = 0 := by
  -- restrict along the ray through a unit vector
  set e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) with he₀_def
  have he₀_norm : ‖e₀‖ = 1 := by simp [he₀_def]
  have he₀_ne : e₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at he₀_norm
    exact one_ne_zero he₀_norm.symm
  have hsnorm : ∀ t : ℝ, ‖t • e₀‖ = |t| := by
    intro t
    rw [norm_smul, he₀_norm, mul_one, Real.norm_eq_abs]
  have hsmem : ∀ t : ℝ, |t| < ε → t • e₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε := by
    intro t ht
    rwa [mem_ball_zero_iff, hsnorm]
  have hsne : ∀ t : ℝ, t ≠ 0 → t • e₀ ≠ 0 := fun t ht => smul_ne_zero ht he₀_ne
  set a : ℝ → ℝ := fun t => F₁ (t • e₀) with ha_def
  set b : ℝ → ℝ := fun t => F₂ (t • e₀) with hb_def
  have hsmul : ContDiff ℝ ∞ fun t : ℝ => t • e₀ := contDiff_id.smul contDiff_const
  have hmaps : Set.MapsTo (fun t : ℝ => t • e₀) (Set.Ioo (-ε) ε)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε) := fun t ht =>
    hsmem t (abs_lt.mpr ⟨ht.1, ht.2⟩)
  have ha_cd : ContDiffOn ℝ ∞ a (Set.Ioo (-ε) ε) := hF₁.comp hsmul.contDiffOn hmaps
  have hb_cd : ContDiffOn ℝ ∞ b (Set.Ioo (-ε) ε) := hF₂.comp hsmul.contDiffOn hmaps
  have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (neg_lt_zero.mpr hε) hε
  have ha_cont : ContinuousAt a 0 := ha_cd.continuousOn.continuousAt hIoo_nhds
  have hb_cont : ContinuousAt b 0 := hb_cd.continuousOn.continuousAt hIoo_nhds
  -- the matching formulas along the ray
  have hafor : ∀ t : ℝ, t ≠ 0 → |t| < ε → a t = (ρ |t|) ^ 2 / t ^ 2 := by
    intro t ht htε
    have h := (hmatch (t • e₀) (hsmem t htε) (hsne t ht)).1
    rw [hsnorm] at h
    simp only [ha_def]
    rw [h, sq_abs]
  have hbfor : ∀ t : ℝ, t ≠ 0 → |t| < ε → b t = 1 / t ^ 2 - (ρ |t|) ^ 2 / t ^ 4 := by
    intro t ht htε
    have habs4 : |t| ^ 4 = t ^ 4 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by positivity)
    have h := (hmatch (t • e₀) (hsmem t htε) (hsne t ht)).2
    rw [hsnorm] at h
    simp only [hb_def]
    rw [h, sq_abs, habs4]
  -- a is even on the interval (both sides are given by the same formula)
  have ha_even : ∀ t : ℝ, |t| < ε → a (-t) = a t := by
    intro t htε
    rcases eq_or_ne t 0 with rfl | ht
    · rw [neg_zero]
    · rw [hafor (-t) (neg_ne_zero.mpr ht) (by rwa [abs_neg]), hafor t ht htε, abs_neg,
        neg_sq]
  -- a 0 = 1 from the F₂ matching clause and continuity
  have ha0 : a 0 = 1 := by
    have h₁ : Filter.Tendsto a (𝓝[>] 0) (𝓝 (a 0)) :=
      ha_cont.tendsto.mono_left nhdsWithin_le_nhds
    have hc : ContinuousAt (fun t : ℝ => 1 - t ^ 2 * b t) 0 :=
      continuousAt_const.sub (((continuous_pow 2).continuousAt).mul hb_cont)
    have h₂ : Filter.Tendsto (fun t : ℝ => 1 - t ^ 2 * b t) (𝓝[>] 0) (𝓝 1) := by
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa using h
    have heq : a =ᶠ[𝓝[>] (0 : ℝ)] fun t => 1 - t ^ 2 * b t := by
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      have htε : |t| < ε := by
        rw [abs_of_pos ht.1]
        exact ht.2
      rw [hafor t ht0 htε, hbfor t ht0 htε]
      field_simp
      ring
    exact tendsto_nhds_unique h₁ (h₂.congr' heq.symm)
  -- a is positive near 0
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a t :=
    Filter.Tendsto.eventually ha_cont (eventually_gt_nhds (by rw [ha0]; norm_num))
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.eventually_nhds_iff.mp hevent
  set δ : ℝ := min δ₀ ε with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos hε
  have hδ_le_ε : δ ≤ ε := min_le_right _ _
  have hapos : ∀ t : ℝ, |t| < δ → 0 < a t := by
    intro t ht
    apply hδ₀
    rw [Real.dist_eq, sub_zero]
    exact ht.trans_le (min_le_left _ _)
  -- an even bump cutoff, to globalize t√(a t) without changing it near 0
  set χ : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩ with hχ_def
  have hχ_rIn : χ.rIn = δ / 4 := rfl
  have hχ_rOut : χ.rOut = δ / 2 := rfl
  have hχ_one : ∀ t : ℝ, |t| ≤ δ / 4 → χ t = 1 := by
    intro t ht
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, hχ_rIn]
    exact ht
  have hχ_zero : ∀ t : ℝ, δ / 2 ≤ |t| → χ t = 0 := by
    intro t ht
    apply χ.zero_of_le_dist
    rw [Real.dist_eq, sub_zero, hχ_rOut]
    exact ht
  have hχ_even : ∀ t : ℝ, χ (-t) = χ t := fun t => χ.neg t
  -- the globalized positive even profile A, agreeing with a near 0
  set A : ℝ → ℝ := fun t => 1 + χ t * (a t - 1) with hA_def
  have hA_eq_a : ∀ t : ℝ, |t| ≤ δ / 4 → A t = a t := by
    intro t ht
    simp only [hA_def]
    rw [hχ_one t ht]
    ring
  have hA_pos : ∀ t : ℝ, 0 < A t := by
    intro t
    simp only [hA_def]
    rcases lt_or_ge |t| δ with h | h
    · have hat := hapos t h
      have hle := χ.le_one (x := t)
      have hrw : 1 + χ t * (a t - 1) = (1 - χ t) + χ t * a t := by ring
      rw [hrw]
      rcases eq_or_lt_of_le (χ.nonneg (x := t)) with h00 | h00
      · rw [← h00]
        norm_num
      · have hprod : 0 < χ t * a t := mul_pos h00 hat
        linarith
    · rw [hχ_zero t (by linarith)]
      norm_num
  have hA_even : ∀ t : ℝ, A (-t) = A t := by
    intro t
    simp only [hA_def]
    rw [hχ_even t]
    rcases lt_or_ge |t| (δ / 2) with h | h
    · have htε : |t| < ε := by
        have hhalf : δ / 2 < δ := by linarith
        linarith
      rw [ha_even t htε]
    · rw [hχ_zero t h]
      ring
  have hA_cd : ContDiff ℝ ∞ A := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge |t| δ with h | h
    · have hnhds : Set.Ioo (-ε) ε ∈ 𝓝 t := by
        have habs := abs_lt.mp (h.trans_le hδ_le_ε)
        exact Ioo_mem_nhds habs.1 habs.2
      have haAt : ContDiffAt ℝ ∞ a t := ha_cd.contDiffAt hnhds
      simp only [hA_def]
      exact contDiffAt_const.add (χ.contDiffAt.mul (haAt.sub contDiffAt_const))
    · have hev1 : ∀ᶠ s in 𝓝 t, δ / 2 < |s| := by
        have hopen : IsOpen {s : ℝ | δ / 2 < |s|} :=
          isOpen_lt continuous_const continuous_abs
        exact hopen.mem_nhds (by simp only [Set.mem_setOf_eq]; linarith)
      have hev2 : A =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [hev1] with s hs
        simp only [hA_def]
        rw [hχ_zero s hs.le]
        ring
      exact contDiffAt_const.congr_of_eventuallyEq hev2
  -- the globally smooth odd function r t = t √(A t), agreeing with ρ on (0, δm)
  set r : ℝ → ℝ := fun t => t * Real.sqrt (A t) with hr_def
  have hsq_cd : ContDiff ℝ ∞ fun t : ℝ => Real.sqrt (A t) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact hA_cd.contDiffAt.sqrt (hA_pos t).ne'
  have hr_cd : ContDiff ℝ ∞ r := by
    rw [hr_def]
    exact contDiff_id.mul hsq_cd
  have hr_odd : ∀ t : ℝ, r (-t) = -r t := by
    intro t
    simp only [hr_def]
    rw [hA_even t]
    ring
  set δm : ℝ := min (δ / 4) δ' with hδm_def
  have hδm_pos : 0 < δm := lt_min (by positivity) hδ'
  have hρr : ∀ t ∈ Set.Ioo (0 : ℝ) δm, ρ t = r t := by
    rintro t ⟨ht0, htm⟩
    have ht0' : t ≠ 0 := ne_of_gt ht0
    have ht4 : |t| ≤ δ / 4 := by
      rw [abs_of_pos ht0]
      exact le_of_lt (htm.trans_le (min_le_left _ _))
    have htδ : |t| < δ := by
      rw [abs_of_pos ht0]
      have h4 : t < δ / 4 := htm.trans_le (min_le_left _ _)
      linarith
    have htε : |t| < ε := htδ.trans_le hδ_le_ε
    have hρt : 0 < ρ t := hρpos t ht0 (htm.trans_le (min_le_right _ _))
    have hat : a t = (ρ t / t) ^ 2 := by
      have h := hafor t ht0' htε
      rw [abs_of_pos ht0] at h
      rw [h, div_pow]
    have hsqrt : Real.sqrt (A t) = ρ t / t := by
      rw [hA_eq_a t ht4, hat]
      exact Real.sqrt_sq (div_pos hρt ht0).le
    simp only [hr_def]
    rw [hsqrt]
    field_simp
  have hgerm : ∀ m : ℕ, iteratedDeriv m ρ 0 = iteratedDeriv m r 0 := fun m =>
    iteratedDeriv_eq_of_eqOn_Ioo hρ hr_cd hδm_pos hρr m
  have hA0 : A 0 = 1 := by
    rw [hA_eq_a 0 (by rw [abs_zero]; positivity), ha0]
  refine ⟨?_, ?_, ?_⟩
  · -- ρ 0 = 0
    have h := hgerm 0
    rw [iteratedDeriv_zero, iteratedDeriv_zero] at h
    rw [h]
    simp only [hr_def]
    rw [zero_mul]
  · -- deriv ρ 0 = 1
    have h := hgerm 1
    rw [iteratedDeriv_one, iteratedDeriv_one] at h
    rw [h]
    have hg_diff : DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (A t)) 0 :=
      (hsq_cd.differentiable (by simp)).differentiableAt
    have hd : HasDerivAt r (Real.sqrt (A 0)) 0 := by
      have h1 : HasDerivAt (fun y : ℝ => y) 1 0 := hasDerivAt_id 0
      have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (A t))
          (deriv (fun t : ℝ => Real.sqrt (A t)) 0) 0 := hg_diff.hasDerivAt
      have h3 := h1.mul h2
      simp only [one_mul, zero_mul, add_zero] at h3
      simpa only [hr_def] using h3
    rw [hd.deriv, hA0, Real.sqrt_one]
  · -- even-order derivatives vanish
    intro l _hl
    rw [hgerm (2 * l)]
    exact iteratedDeriv_even_of_odd hr_cd hr_odd l

/-- **Math.** Petersen §1.4.4, smoothness criterion, local-positivity form: for ambient
dimension `n ≥ 1`, and `ρ` smooth and positive on some right-neighbourhood `(0, δ)` of
`0`, the metric `dt² + ρ²(t) ds²_{n-1}` extends to a smooth metric on `ℝⁿ` near the
origin (in the sense of the coefficient functions `F₁, F₂` of `rotSymCartesianForm`)
if and only if `ρ(0) = 0`, `ρ̇(0) = 1`, and `ρ^{(2l)}(0) = 0` for `l ≥ 1`.
This auxiliary form, requiring positivity of `ρ` only near `0`, is what reflection
arguments for doubly warped products need at the far endpoint. -/
theorem rotationallySymmetricSmoothnessCriterion_aux (hn : 0 < n) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∃ δ > (0 : ℝ), ∀ t, 0 < t → t < δ → 0 < ρ t) :
    (∃ (ε : ℝ) (_ : 0 < ε) (F₁ F₂ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε) ∧
      0 < F₁ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Metric.ball 0 ε → x ≠ 0 →
        F₁ x = (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 ∧
        F₂ x = 1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4) ↔
    (ρ 0 = 0 ∧ deriv ρ 0 = 1 ∧
      ∀ l : ℕ, 1 ≤ l → iteratedDeriv (2 * l) ρ 0 = 0) := by
  constructor
  · rintro ⟨ε, hε, F₁, F₂, hF₁, hF₂, _hF₁0, hmatch⟩
    obtain ⟨δ', hδ', hρpos⟩ := hpos
    exact smoothnessCriterion_forward hn hρ hδ' hρpos hε hF₁ hF₂ hmatch
  · rintro ⟨h0, h1, h2⟩
    exact smoothnessCriterion_backward ρ hρ h0 h1 h2

/-- **Math.** Petersen §1.4.4 (Theorem, smoothness at the origin): for ambient
dimension `n ≥ 1`, the metric `dt² + ρ²(t) ds²_{n-1}` extends to a smooth metric on
`ℝⁿ` near the origin `t = 0` if and only if `ρ(0) = 0`, `ρ̇(0) = 1`, and all
even-order derivatives of `ρ` vanish at `0`: `ρ^{(2l)}(0) = 0` for `l ≥ 1`.

"Extends smoothly" is expressed through the two coefficient functions of the
Cartesian form `rotSymCartesianForm`: there are smooth functions
`F₁, F₂ : ℝⁿ → ℝ` on a neighbourhood of `0` with `F₁(x) = ρ²(t)/t²` and
`F₂(x) = 1/t² − ρ²(t)/t⁴` for `x ≠ 0` near `0`, and `F₁(0) > 0` (so the
extended form stays positive definite at the origin, where it equals
`F₁(0)⟨u,v⟩`).

The proof runs through Whitney's even-function theorem
(`PetersenLib.Foundations.WhitneyEven`): splitting `ρ` into odd and even parts, the
derivative conditions make the even part flat at `0`, and repeated Hadamard quotients
write `ρ²(t)/t²` and `1/t² − ρ²(t)/t⁴` as (smooth even) + (smooth flat) functions of
`t`, which are smooth in `x` by `contDiff_even_comp_norm`/`contDiff_flat_comp_norm`.
Conversely, restricting `F₁` along a ray gives `t√(F₁(t·e))` as a smooth odd function
agreeing with `ρ` near `0⁺`, forcing the derivative conditions. -/
theorem rotationallySymmetricSmoothnessCriterion (hn : 0 < n) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ t : ℝ, 0 < t → 0 < ρ t) :
    (∃ (ε : ℝ) (_ : 0 < ε) (F₁ F₂ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε) ∧
      0 < F₁ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Metric.ball 0 ε → x ≠ 0 →
        F₁ x = (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 ∧
        F₂ x = 1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4) ↔
    (ρ 0 = 0 ∧ deriv ρ 0 = 1 ∧
      ∀ l : ℕ, 1 ≤ l → iteratedDeriv (2 * l) ρ 0 = 0) :=
  rotationallySymmetricSmoothnessCriterion_aux hn ρ hρ
    ⟨1, one_pos, fun t ht _ => hpos t ht⟩

end PetersenLib
