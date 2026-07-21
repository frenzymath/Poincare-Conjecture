import PetersenLib.Ch01.WarpedProducts
import PetersenLib.Ch01.SmoothnessCriterion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Petersen Ch. 1, §1.4.5–§1.4.6 — smoothness of doubly warped products and
the Hopf fibrations

Two groups of results from Petersen §1.4.5–§1.4.6:

* **Endpoint smoothness of doubly warped products** (Props 1.4.7/1.4.8,
  `doublyWarpedSmoothAtZero`, `doublyWarpedSmoothAtB`): the metric
  `dt² + ρ²(t) ds²_p + φ²(t) ds²_q` extends smoothly across an endpoint where
  `ρ` vanishes iff `ρ` closes up like `± t` with vanishing even derivatives
  while `φ` stays positive with vanishing odd derivatives
  (`WarpingClosesSmoothlyAt`, `WarpingStaysPositiveAt`). As in
  `rotationallySymmetricSmoothnessCriterion`, "extends smoothly" is phrased
  through the coefficient functions of the Cartesian form on the blown-up
  factor `ℝ^{p+1}`; the proofs rest on Whitney's even-function theorem
  (`PetersenLib.Foundations.WhitneyEven`): the `ρ`-clauses reduce to the
  rotationally symmetric criterion of §1.4.4, and the bystander clause
  `F₃ = φ²(t)` is handled by splitting `φ` into an even part and a flat
  remainder (backward) and by extracting a smooth even germ `√F₃` along a ray
  (forward). The far endpoint `t = b` reduces to `t = 0` by the reflection
  `s = b − t`. The remark on the three resulting topological types is
  recorded as the bookkeeping predicate `doublyWarpedTopologyTypes`.

* **Hopf fibrations in coordinates** (Examples 1.4.10/1.4.11,
  `hopfFibrationRevisited`, `hopfFibrationGeneralSubmersion`): on the
  universal-cover model `ℝ × ℝ × ℝ → ℝ × ℝ` of
  `I × S¹ × S¹ → I × S¹`, the map `(t, θ₁, θ₂) ↦ (t, θ₁ − θ₂)` is a
  Riemannian submersion from `dt² + ρ²(t) dθ₁² + φ²(t) dθ₂²` to
  `dr² + (ρφ)²/(ρ² + φ²) dθ²`, fully proved (`IsFormRiemannianSubmersion`
  states the submersion conditions for possibly degenerate metric *forms*).
  The Hopf case `ρ = sin`, `φ = cos` with target coefficient `¼ sin²(2r)` is
  derived as a corollary.

Examples 1.4.12–1.4.14 (higher-dimensional and generalized Hopf fibrations)
require the Hopf distribution on `S^{2n+1}`, quotient metrics, the `SU(2)`
coframe and the Fubini–Study metric, none of which are available yet; they
are deliberately not stated here rather than being stated unfaithfully.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.5–§1.4.6.
-/

noncomputable section

open Real
open scoped ContDiff Manifold Topology

namespace PetersenLib

/-! ## Endpoint conditions for warping functions (Petersen §1.4.5) -/

/-- **Math.** Petersen §1.4.5 (Props 1.4.7/1.4.8, boundary conditions for the
collapsing warping function): `ρ` **closes smoothly at `t₀` with slope
`slope`** if `ρ(t₀) = 0`, `ρ̇(t₀) = slope` (Petersen: `+1` at a left
endpoint, `−1` at a right endpoint), and all higher even-order derivatives of
`ρ` vanish at `t₀`: `ρ^{(2l)}(t₀) = 0` for `l ≥ 1`. These are exactly the
conditions under which `ρ²(t) ds²_p` caps off the sphere factor `Sᵖ` to a
smooth `ℝ^{p+1}` near the endpoint. -/
def WarpingClosesSmoothlyAt (ρ : ℝ → ℝ) (t₀ slope : ℝ) : Prop :=
  ρ t₀ = 0 ∧ deriv ρ t₀ = slope ∧
    ∀ l : ℕ, 1 ≤ l → iteratedDeriv (2 * l) ρ t₀ = 0

/-- **Math.** Petersen §1.4.5 (Props 1.4.7/1.4.8, boundary conditions for the
bystander warping function): `φ` **stays positive at `t₀`** if `φ(t₀) > 0`
and all odd-order derivatives of `φ` vanish at `t₀`: `φ^{(2l+1)}(t₀) = 0`.
Equivalently (by Whitney's even-function theorem) `φ` extends to a smooth
positive even function of the distance to the endpoint, so `φ²(t) ds²_q`
stays a smooth nondegenerate metric on the factor `S^q` across the endpoint. -/
def WarpingStaysPositiveAt (φ : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < φ t₀ ∧ ∀ l : ℕ, iteratedDeriv (2 * l + 1) φ t₀ = 0

section EndpointSmoothness

open Set Filter

/-- Backward direction for the bystander factor: if all odd-order derivatives
of the smooth function `φ` vanish at `0`, then `x ↦ φ ‖x‖` is smooth on any
real inner product space. Whitney: split `φ = φₑ + φₒ` into even and odd
parts; `φₑ` is smooth even, and the vanishing odd derivatives make `φₒ` flat
at `0`, so both compose smoothly with the norm
(`contDiff_even_comp_norm`, `contDiff_flat_comp_norm`). -/
private theorem contDiff_comp_norm_of_odd_derivs_vanish {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hodd : ∀ l : ℕ, iteratedDeriv (2 * l + 1) φ 0 = 0) :
    ContDiff ℝ ∞ fun x : E => φ ‖x‖ := by
  set φe : ℝ → ℝ := fun t => (1 / 2 : ℝ) * (φ t + φ (-t)) with hφe_def
  set φo : ℝ → ℝ := fun t => (1 / 2 : ℝ) * (φ t - φ (-t)) with hφo_def
  have hφe_cd : ContDiff ℝ ∞ φe := by
    rw [hφe_def]
    exact contDiff_const.mul (hφ.add (hφ.comp contDiff_neg))
  have hφo_cd : ContDiff ℝ ∞ φo := by
    rw [hφo_def]
    exact contDiff_const.mul (hφ.sub (hφ.comp contDiff_neg))
  have hφe_even : ∀ t, φe (-t) = φe t := by
    intro t
    simp only [hφe_def, neg_neg]
    ring
  have hφo_odd : ∀ t, φo (-t) = -φo t := by
    intro t
    simp only [hφo_def, neg_neg]
    ring
  -- the odd part is flat at 0: even-order derivatives vanish by parity, and
  -- odd-order ones because those of φ (hypothesis) and of φₑ (parity) do
  have hφo_flat : ∀ k : ℕ, iteratedDeriv k φo 0 = 0 := by
    intro k
    rcases Nat.even_or_odd k with ⟨l, hl⟩ | ⟨l, hl⟩
    · subst hl
      have h := iteratedDeriv_even_of_odd hφo_cd hφo_odd l
      rwa [two_mul] at h
    · subst hl
      have hsplit : φ = fun t => φe t + φo t := by
        funext t
        simp only [hφe_def, hφo_def]
        ring
      have hadd : iteratedDeriv (2 * l + 1) (fun t => φe t + φo t) 0
          = iteratedDeriv (2 * l + 1) φe 0 + iteratedDeriv (2 * l + 1) φo 0 :=
        iteratedDeriv_fun_add
          (hφe_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
          (hφo_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
      have hφk := hodd l
      rw [hsplit, hadd, iteratedDeriv_odd_of_even hφe_cd hφe_even l] at hφk
      linarith
  have heq : (fun x : E => φ ‖x‖) = fun x : E => φe ‖x‖ + φo ‖x‖ := by
    funext x
    simp only [hφe_def, hφo_def]
    ring
  rw [heq]
  exact (contDiff_even_comp_norm hφe_cd hφe_even).add
    (contDiff_flat_comp_norm hφo_cd hφo_flat)

/-- Forward direction for the bystander factor: if `F₃` is smooth on a ball
around `0 ∈ ℝᵐ` with `F₃(0) > 0` and `F₃(x) = φ(|x|)²` off the origin, and
`φ > 0` on a right-neighbourhood of `0`, then `φ(0) > 0` and all odd-order
derivatives of `φ` vanish at `0`. Restricting `F₃` along a ray gives an even
germ; a bump-function globalization makes `√F₃(t·e)` a globally smooth even
function agreeing with `φ` near `0⁺`, so the odd derivatives vanish by
parity and germ transfer. -/
private theorem staysPositiveAt_zero_of_smooth_sq_extension {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {δ' : ℝ} (hδ' : 0 < δ') (hφpos : ∀ t, 0 < t → t < δ' → 0 < φ t)
    {ε : ℝ} (hε : 0 < ε) {F₃ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hF₃ : ContDiffOn ℝ ∞ F₃ (Metric.ball 0 ε)) (hF₃0 : 0 < F₃ 0)
    (hmatch : ∀ x : EuclideanSpace ℝ (Fin m), x ∈ Metric.ball 0 ε → x ≠ 0 →
      F₃ x = (φ ‖x‖) ^ 2) :
    WarpingStaysPositiveAt φ 0 := by
  -- restrict along the ray through a unit vector
  set e₀ : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single ⟨0, hm⟩ (1 : ℝ) with he₀_def
  have he₀_norm : ‖e₀‖ = 1 := by simp [he₀_def]
  have he₀_ne : e₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at he₀_norm
    exact one_ne_zero he₀_norm.symm
  have hsnorm : ∀ t : ℝ, ‖t • e₀‖ = |t| := by
    intro t
    rw [norm_smul, he₀_norm, mul_one, Real.norm_eq_abs]
  have hsmem : ∀ t : ℝ, |t| < ε → t • e₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε := by
    intro t ht
    rwa [mem_ball_zero_iff, hsnorm]
  have hsne : ∀ t : ℝ, t ≠ 0 → t • e₀ ≠ 0 := fun t ht => smul_ne_zero ht he₀_ne
  set c : ℝ → ℝ := fun t => F₃ (t • e₀) with hc_def
  have hsmul : ContDiff ℝ ∞ fun t : ℝ => t • e₀ := contDiff_id.smul contDiff_const
  have hmaps : Set.MapsTo (fun t : ℝ => t • e₀) (Set.Ioo (-ε) ε)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) := fun t ht =>
    hsmem t (abs_lt.mpr ⟨ht.1, ht.2⟩)
  have hc_cd : ContDiffOn ℝ ∞ c (Set.Ioo (-ε) ε) := hF₃.comp hsmul.contDiffOn hmaps
  have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (neg_lt_zero.mpr hε) hε
  have hc_cont : ContinuousAt c 0 := hc_cd.continuousOn.continuousAt hIoo_nhds
  -- the matching formula along the ray
  have hcfor : ∀ t : ℝ, t ≠ 0 → |t| < ε → c t = (φ |t|) ^ 2 := by
    intro t ht htε
    have h := hmatch (t • e₀) (hsmem t htε) (hsne t ht)
    rw [hsnorm] at h
    simp only [hc_def]
    exact h
  have hc0 : c 0 = F₃ 0 := by
    simp only [hc_def, zero_smul]
  -- c is even on the interval
  have hc_even : ∀ t : ℝ, |t| < ε → c (-t) = c t := by
    intro t htε
    rcases eq_or_ne t 0 with rfl | ht
    · rw [neg_zero]
    · rw [hcfor (-t) (neg_ne_zero.mpr ht) (by rwa [abs_neg]), hcfor t ht htε, abs_neg]
  -- φ(0)² = F₃(0), comparing the two limits of c along 0⁺
  have hφ0_sq : φ 0 ^ 2 = F₃ 0 := by
    have h₁ : Filter.Tendsto c (𝓝[>] 0) (𝓝 (F₃ 0)) := by
      have h := hc_cont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      rwa [hc0] at h
    have h₂ : Filter.Tendsto (fun t : ℝ => (φ t) ^ 2) (𝓝[>] 0) (𝓝 (φ 0 ^ 2)) :=
      ((hφ.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).pow 2
    have heq : (fun t : ℝ => (φ t) ^ 2) =ᶠ[𝓝[>] (0 : ℝ)] c := by
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      have htε : |t| < ε := by
        rw [abs_of_pos ht.1]
        exact ht.2
      rw [hcfor t ht0 htε, abs_of_pos ht.1]
    exact tendsto_nhds_unique (h₂.congr' heq) h₁
  -- φ(0) ≥ 0 from right-positivity; φ(0) ≠ 0 since φ(0)² = F₃(0) > 0
  have hφ0_pos : 0 < φ 0 := by
    have hφ0_nonneg : 0 ≤ φ 0 := by
      have hlim : Filter.Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) :=
        (hφ.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ φ t := by
        filter_upwards [Ioo_mem_nhdsGT hδ'] with t ht
        exact (hφpos t ht.1 ht.2).le
      exact ge_of_tendsto hlim hev
    have hne : φ 0 ≠ 0 := by
      intro h
      rw [h, zero_pow two_ne_zero] at hφ0_sq
      exact hF₃0.ne' hφ0_sq.symm
    exact hφ0_nonneg.lt_of_ne (Ne.symm hne)
  -- c is positive near 0
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c t :=
    Filter.Tendsto.eventually hc_cont (eventually_gt_nhds (by rw [hc0]; exact hF₃0))
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.eventually_nhds_iff.mp hevent
  set δ : ℝ := min δ₀ ε with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos hε
  have hδ_le_ε : δ ≤ ε := min_le_right _ _
  have hcpos : ∀ t : ℝ, |t| < δ → 0 < c t := by
    intro t ht
    apply hδ₀
    rw [Real.dist_eq, sub_zero]
    exact ht.trans_le (min_le_left _ _)
  -- an even bump cutoff, to globalize √(c t) without changing it near 0
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
  -- the globalized positive even profile C, agreeing with c near 0
  set C : ℝ → ℝ := fun t => 1 + χ t * (c t - 1) with hC_def
  have hC_eq_c : ∀ t : ℝ, |t| ≤ δ / 4 → C t = c t := by
    intro t ht
    simp only [hC_def]
    rw [hχ_one t ht]
    ring
  have hC_pos : ∀ t : ℝ, 0 < C t := by
    intro t
    simp only [hC_def]
    rcases lt_or_ge |t| δ with h | h
    · have hct := hcpos t h
      have hle := χ.le_one (x := t)
      have hrw : 1 + χ t * (c t - 1) = (1 - χ t) + χ t * c t := by ring
      rw [hrw]
      rcases eq_or_lt_of_le (χ.nonneg (x := t)) with h00 | h00
      · rw [← h00]
        norm_num
      · have hprod : 0 < χ t * c t := mul_pos h00 hct
        linarith
    · rw [hχ_zero t (by linarith)]
      norm_num
  have hC_even : ∀ t : ℝ, C (-t) = C t := by
    intro t
    simp only [hC_def]
    rw [hχ_even t]
    rcases lt_or_ge |t| (δ / 2) with h | h
    · have htε : |t| < ε := by
        have hhalf : δ / 2 < δ := by linarith
        linarith
      rw [hc_even t htε]
    · rw [hχ_zero t h]
      ring
  have hC_cd : ContDiff ℝ ∞ C := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge |t| δ with h | h
    · have hnhds : Set.Ioo (-ε) ε ∈ 𝓝 t := by
        have habs := abs_lt.mp (h.trans_le hδ_le_ε)
        exact Ioo_mem_nhds habs.1 habs.2
      have hcAt : ContDiffAt ℝ ∞ c t := hc_cd.contDiffAt hnhds
      simp only [hC_def]
      exact contDiffAt_const.add (χ.contDiffAt.mul (hcAt.sub contDiffAt_const))
    · have hev1 : ∀ᶠ s in 𝓝 t, δ / 2 < |s| := by
        have hopen : IsOpen {s : ℝ | δ / 2 < |s|} :=
          isOpen_lt continuous_const continuous_abs
        exact hopen.mem_nhds (by simp only [Set.mem_setOf_eq]; linarith)
      have hev2 : C =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [hev1] with s hs
        simp only [hC_def]
        rw [hχ_zero s hs.le]
        ring
      exact contDiffAt_const.congr_of_eventuallyEq hev2
  -- the smooth even germ √C, agreeing with φ on (0, δm)
  set g : ℝ → ℝ := fun t => Real.sqrt (C t) with hg_def
  have hg_cd : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact hC_cd.contDiffAt.sqrt (hC_pos t).ne'
  have hg_even : ∀ t : ℝ, g (-t) = g t := by
    intro t
    simp only [hg_def]
    rw [hC_even t]
  set δm : ℝ := min (δ / 4) δ' with hδm_def
  have hδm_pos : 0 < δm := lt_min (by positivity) hδ'
  have hφg : ∀ t ∈ Set.Ioo (0 : ℝ) δm, φ t = g t := by
    rintro t ⟨ht0, htm⟩
    have ht0' : t ≠ 0 := ne_of_gt ht0
    have ht4 : |t| ≤ δ / 4 := by
      rw [abs_of_pos ht0]
      exact le_of_lt (htm.trans_le (min_le_left _ _))
    have htδ : |t| < δ := lt_of_le_of_lt ht4 (by linarith)
    have htε : |t| < ε := htδ.trans_le hδ_le_ε
    have hφt : 0 < φ t := hφpos t ht0 (htm.trans_le (min_le_right _ _))
    have hct : c t = φ t ^ 2 := by
      have h := hcfor t ht0' htε
      rwa [abs_of_pos ht0] at h
    simp only [hg_def]
    rw [hC_eq_c t ht4, hct, Real.sqrt_sq hφt.le]
  refine ⟨hφ0_pos, fun l => ?_⟩
  rw [iteratedDeriv_eq_of_eqOn_Ioo hφ hg_cd hδm_pos hφg (2 * l + 1)]
  exact iteratedDeriv_odd_of_even hg_cd hg_even l

/-- **Math.** Petersen Proposition 1.4.7, local-positivity form: the
smoothness criterion for the doubly warped product at `t = 0`, assuming
positivity of the warping functions `ρ, φ` only on a right-neighbourhood of
`0`. This auxiliary form is what the reflection argument for the far
endpoint `t = b` (`doublyWarpedSmoothAtB`) consumes. -/
theorem doublyWarpedSmoothAtZero_aux (p : ℕ) (ρ φ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∃ δ > (0 : ℝ), ∀ t, 0 < t → t < δ → 0 < ρ t)
    (hφpos : ∃ δ > (0 : ℝ), ∀ t, 0 < t → t < δ → 0 < φ t) :
    (∃ (ε : ℝ) (_ : 0 < ε) (F₁ F₂ F₃ : EuclideanSpace ℝ (Fin (p + 1)) → ℝ),
      ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₃ (Metric.ball 0 ε) ∧
      0 < F₁ 0 ∧ 0 < F₃ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin (p + 1)), x ∈ Metric.ball 0 ε → x ≠ 0 →
        F₁ x = (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 ∧
        F₂ x = 1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4 ∧
        F₃ x = (φ ‖x‖) ^ 2) ↔
    (WarpingClosesSmoothlyAt ρ 0 1 ∧ WarpingStaysPositiveAt φ 0) := by
  constructor
  · rintro ⟨ε, hε, F₁, F₂, F₃, hF₁, hF₂, hF₃, hF₁0, hF₃0, hmatch⟩
    obtain ⟨δ', hδ', hφpos'⟩ := hφpos
    constructor
    · exact (rotationallySymmetricSmoothnessCriterion_aux (n := p + 1)
        p.succ_pos ρ hρ hpos).mp
        ⟨ε, hε, F₁, F₂, hF₁, hF₂, hF₁0, fun x hx hx0 =>
          ⟨(hmatch x hx hx0).1, (hmatch x hx hx0).2.1⟩⟩
    · exact staysPositiveAt_zero_of_smooth_sq_extension p.succ_pos hφ hδ' hφpos'
        hε hF₃ hF₃0 (fun x hx hx0 => (hmatch x hx hx0).2.2)
  · rintro ⟨hclose, hstay⟩
    obtain ⟨ε₁, hε₁, F₁, F₂, hF₁, hF₂, hF₁0, hmatch₁₂⟩ :=
      (rotationallySymmetricSmoothnessCriterion_aux (n := p + 1)
        p.succ_pos ρ hρ hpos).mpr hclose
    obtain ⟨hφ0, hφodd⟩ := hstay
    have hG : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin (p + 1)) => φ ‖x‖ :=
      contDiff_comp_norm_of_odd_derivs_vanish hφ hφodd
    refine ⟨ε₁, hε₁, F₁, F₂, fun x => (φ ‖x‖) ^ 2, hF₁, hF₂,
      (hG.pow 2).contDiffOn, hF₁0, ?_, ?_⟩
    · show 0 < (φ ‖(0 : EuclideanSpace ℝ (Fin (p + 1)))‖) ^ 2
      rw [norm_zero]
      exact pow_pos hφ0 2
    · intro x hx hx0
      exact ⟨(hmatch₁₂ x hx hx0).1, (hmatch₁₂ x hx hx0).2, rfl⟩

/-- **Math.** Petersen Proposition 1.4.7 (smoothness of a doubly warped
product at `t = 0`): let `ρ, φ` be smooth and positive on `(0, ∞)` (they are
the warping functions of the metric `dt² + ρ²(t) ds²_p + φ²(t) ds²_q` on
`(0, b) × Sᵖ × S^q`, which requires both to be positive on the interior).
Near `t = 0` the metric is the metric on
`(ball 0 ε \ {0}) × S^q ⊂ ℝ^{p+1} × S^q`
whose `ℝ^{p+1}`-part is the Cartesian form
`F₂(x) ⟨x,u⟩⟨x,v⟩ + F₁(x) ⟨u,v⟩` of `rotSymCartesianForm` (with `t = |x|`,
`F₁ = ρ²(t)/t²`, `F₂ = 1/t² − ρ²(t)/t⁴`) and whose `S^q`-part is
`F₃(x) g_{S^q}` with `F₃ = φ²(t)`. The metric **extends smoothly across
`t = 0`** — i.e. `F₁, F₂, F₃` extend to smooth functions on a ball around
`0 ∈ ℝ^{p+1}` with `F₁(0) > 0` and `F₃(0) > 0` — if and only if
`ρ(0) = 0`, `ρ̇(0) = 1`, `ρ^{(even)}(0) = 0` (`WarpingClosesSmoothlyAt ρ 0 1`)
and `φ(0) > 0`, `φ^{(odd)}(0) = 0` (`WarpingStaysPositiveAt φ 0`). The
topology near `t = 0` is then `ℝ^{p+1} × S^q`.

Petersen's argument, as formalized: the `ρ`-clauses are exactly the
rotationally symmetric criterion (Prop 1.4.6,
`rotationallySymmetricSmoothnessCriterion`) for the blown-up `ℝ^{p+1}`
factor, and `F₃ = φ²(|x|)` is smooth in `x` with `F₃(0) > 0` iff `φ` is
(up to sign, fixed by positivity) a smooth even function of `t` near `0`,
i.e. iff `φ(0) > 0` and `φ^{(odd)}(0) = 0` — Whitney's even-function theorem
(`PetersenLib.Foundations.WhitneyEven`). Note the positivity hypothesis on
`φ` is needed for the forward direction: the coefficient `F₃ = φ²` only
determines `φ` up to sign. -/
theorem doublyWarpedSmoothAtZero (p : ℕ) (ρ φ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ t : ℝ, 0 < t → 0 < ρ t) (hφpos : ∀ t : ℝ, 0 < t → 0 < φ t) :
    (∃ (ε : ℝ) (_ : 0 < ε) (F₁ F₂ F₃ : EuclideanSpace ℝ (Fin (p + 1)) → ℝ),
      ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₃ (Metric.ball 0 ε) ∧
      0 < F₁ 0 ∧ 0 < F₃ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin (p + 1)), x ∈ Metric.ball 0 ε → x ≠ 0 →
        F₁ x = (ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 ∧
        F₂ x = 1 / ‖x‖ ^ 2 - (ρ ‖x‖) ^ 2 / ‖x‖ ^ 4 ∧
        F₃ x = (φ ‖x‖) ^ 2) ↔
    (WarpingClosesSmoothlyAt ρ 0 1 ∧ WarpingStaysPositiveAt φ 0) :=
  doublyWarpedSmoothAtZero_aux p ρ φ hρ hφ
    ⟨1, one_pos, fun t ht _ => hpos t ht⟩
    ⟨1, one_pos, fun t ht _ => hφpos t ht⟩

/-- Reflection `s = b − t` for the collapsing condition: `ρ(b − ·)` closes
smoothly at `0` with slope `+1` iff `ρ` closes smoothly at `b` with slope
`−1` (odd-order derivatives change sign under the reflection, even-order
ones are preserved: `iteratedDeriv_comp_const_sub`). -/
private theorem warpingClosesSmoothlyAt_reflect {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (b : ℝ) :
    WarpingClosesSmoothlyAt (fun s => ρ (b - s)) 0 1 ↔
      WarpingClosesSmoothlyAt ρ b (-1) := by
  have hval : (fun s => ρ (b - s)) 0 = ρ b := by simp
  have hder : deriv (fun s => ρ (b - s)) 0 = -deriv ρ b := by
    have h := iteratedDeriv_comp_const_sub hρ b 1 0
    simp only [iteratedDeriv_one, pow_one, sub_zero, neg_one_mul] at h
    exact h
  have hiter : ∀ l : ℕ, iteratedDeriv (2 * l) (fun s => ρ (b - s)) 0
      = iteratedDeriv (2 * l) ρ b := by
    intro l
    have h := iteratedDeriv_comp_const_sub hρ b (2 * l) 0
    rwa [sub_zero, Even.neg_one_pow ⟨l, two_mul l⟩, one_mul] at h
  unfold WarpingClosesSmoothlyAt
  rw [hval, hder]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun l hl => (hiter l).symm.trans (h2 l hl)⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by rw [h1, neg_neg], fun l hl => (hiter l).trans (h2 l hl)⟩

/-- Reflection `s = b − t` for the bystander condition: `φ(b − ·)` stays
positive at `0` iff `φ` stays positive at `b` (odd-order derivatives change
sign under the reflection). -/
private theorem warpingStaysPositiveAt_reflect {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (b : ℝ) :
    WarpingStaysPositiveAt (fun s => φ (b - s)) 0 ↔ WarpingStaysPositiveAt φ b := by
  have hval : (fun s => φ (b - s)) 0 = φ b := by simp
  have hiter : ∀ l : ℕ, iteratedDeriv (2 * l + 1) (fun s => φ (b - s)) 0
      = -iteratedDeriv (2 * l + 1) φ b := by
    intro l
    have h := iteratedDeriv_comp_const_sub hφ b (2 * l + 1) 0
    rwa [sub_zero, Odd.neg_one_pow ⟨l, rfl⟩, neg_one_mul] at h
  unfold WarpingStaysPositiveAt
  rw [hval]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun l => ?_⟩
    have h := h1 l
    rw [hiter l] at h
    exact neg_eq_zero.mp h
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun l => ?_⟩
    rw [hiter l, h1 l, neg_zero]

/-- **Math.** Petersen Proposition 1.4.8 (smoothness of a doubly warped
product at `t = b`): let `ρ, φ` be smooth and positive on `(0, b)`. In the
reflected variable `s = b − t` the metric near `t = b` takes the same form as
in Prop 1.4.7, so — with the Cartesian coefficient functions now evaluated at
`ρ(b − |x|)`, `φ(b − |x|)` for `x ∈ ℝ^{p+1}` — the doubly warped metric
`dt² + ρ²(t) ds²_p + φ²(t) ds²_q` **extends smoothly across `t = b`** iff
`ρ(b) = 0`, `ρ̇(b) = −1`, `ρ^{(even)}(b) = 0`
(`WarpingClosesSmoothlyAt ρ b (−1)`) and `φ(b) > 0`, `φ^{(odd)}(b) = 0`
(`WarpingStaysPositiveAt φ b`); the sign `ρ̇(b) = −1` is the slope `+1` of
the reflected function `s ↦ ρ(b − s)` at `s = 0`. The topology near `t = b`
is again `ℝ^{p+1} × S^q`.

Proved from `doublyWarpedSmoothAtZero_aux` applied to the reflected warping
functions `ρ(b − ·)`, `φ(b − ·)` (positive on the right-neighbourhood
`(0, b)` of `0`), translating the endpoint conditions through
`iteratedDeriv_comp_const_sub`. -/
theorem doublyWarpedSmoothAtB (p : ℕ) (b : ℝ) (hb : 0 < b) (ρ φ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ t : ℝ, 0 < t → t < b → 0 < ρ t)
    (hφpos : ∀ t : ℝ, 0 < t → t < b → 0 < φ t) :
    (∃ (ε : ℝ) (_ : 0 < ε) (F₁ F₂ F₃ : EuclideanSpace ℝ (Fin (p + 1)) → ℝ),
      ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₃ (Metric.ball 0 ε) ∧
      0 < F₁ 0 ∧ 0 < F₃ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin (p + 1)), x ∈ Metric.ball 0 ε → x ≠ 0 →
        F₁ x = (ρ (b - ‖x‖)) ^ 2 / ‖x‖ ^ 2 ∧
        F₂ x = 1 / ‖x‖ ^ 2 - (ρ (b - ‖x‖)) ^ 2 / ‖x‖ ^ 4 ∧
        F₃ x = (φ (b - ‖x‖)) ^ 2) ↔
    (WarpingClosesSmoothlyAt ρ b (-1) ∧ WarpingStaysPositiveAt φ b) := by
  have hρr : ContDiff ℝ ∞ fun s => ρ (b - s) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hφr : ContDiff ℝ ∞ fun s => φ (b - s) :=
    hφ.comp (contDiff_const.sub contDiff_id)
  have haux := doublyWarpedSmoothAtZero_aux p (fun s => ρ (b - s))
    (fun s => φ (b - s)) hρr hφr
    ⟨b, hb, fun s hs hsb => hpos (b - s) (by linarith) (by linarith)⟩
    ⟨b, hb, fun s hs hsb => hφpos (b - s) (by linarith) (by linarith)⟩
  exact haux.trans (and_congr (warpingClosesSmoothlyAt_reflect hρ b)
    (warpingStaysPositiveAt_reflect hφ b))

end EndpointSmoothness

/-- **Math.** Petersen §1.4.5 (remark after Prop 1.4.8): the three
**topological types** of smoothly closed-up doubly warped products
`dt² + ρ²(t) ds²_p + φ²(t) ds²_q`. -/
inductive DoublyWarpedTopologyType : Type
  /-- `ρ` closes at `t = 0` only (`ρ, φ : [0, ∞)`): topology `ℝ^{p+1} × S^q`. -/
  | euclideanTimesSphere
  /-- `ρ` closes at both `t = 0` and `t = b`: topology `S^{p+1} × S^q`. -/
  | sphereTimesSphere
  /-- `ρ` closes at `t = 0`, `φ` closes at `t = b`: topology `S^{p+q+1}`. -/
  | sphere
  deriving DecidableEq

/-- **Math.** Petersen §1.4.5 (remark on the topologies of doubly warped
products): the boundary-condition combinations under which
`dt² + ρ²(t) ds²_p + φ²(t) ds²_q` on `(0, b) × Sᵖ × S^q` closes up to a
smooth metric on each of the three topological types:

* `ℝ^{p+1} × S^q` — `ρ` closes smoothly at `t = 0` (Prop 1.4.7) while `φ`
  stays positive there;
* `S^{p+1} × S^q` — `ρ` closes smoothly at both `t = 0` (slope `+1`) and
  `t = b` (slope `−1`, Prop 1.4.8), `φ` staying positive at both ends;
* `S^{p+q+1}` — `ρ` closes at `t = 0` and the *roles are interchanged* at
  `t = b`: there `φ` closes smoothly (slope `−1`) while `ρ` stays positive.

Only the boundary conditions are formalized here; the identification of the
resulting smooth manifolds (gluing `ℝ^{p+1} × S^q` caps, respectively the
`S^{p+q+1} = ∂(ℝ^{p+1} × ℝ^{q+1})`-decomposition into
`S^p × D^{q+1} ∪ D^{p+1} × S^q`) is topology beyond the present API. -/
def doublyWarpedTopologyTypes (ρ φ : ℝ → ℝ) (b : ℝ) :
    DoublyWarpedTopologyType → Prop
  | .euclideanTimesSphere =>
      WarpingClosesSmoothlyAt ρ 0 1 ∧ WarpingStaysPositiveAt φ 0
  | .sphereTimesSphere =>
      (WarpingClosesSmoothlyAt ρ 0 1 ∧ WarpingStaysPositiveAt φ 0) ∧
      (WarpingClosesSmoothlyAt ρ b (-1) ∧ WarpingStaysPositiveAt φ b)
  | .sphere =>
      (WarpingClosesSmoothlyAt ρ 0 1 ∧ WarpingStaysPositiveAt φ 0) ∧
      (WarpingClosesSmoothlyAt φ b (-1) ∧ WarpingStaysPositiveAt ρ b)

/-! ## Riemannian submersions between metric forms

The warped-product *forms* of `PetersenLib.Ch01.WarpedProducts` are defined
for arbitrary warping functions, which may vanish (as `sin` does at the poles
in the Hopf examples); they are then only positive semidefinite and do not
assemble into bundled `RiemannianMetric`s. The submersion condition of
Petersen §1.1 makes sense verbatim for such forms, so we state it directly. -/

section FormSubmersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **Math.** Petersen §1.1 (Riemannian submersion), transcribed for
pointwise bilinear *forms* rather than bundled metrics: `F : M → M'` is a
**Riemannian submersion from the form `gM` to the form `gN`** if `F` is
smooth, each differential `DF_p` is surjective, and whenever
`u, v ∈ T_pM` are `gM`-orthogonal to `ker DF_p` then
`gM(u, v) = gN(DF(u), DF(v))`. When `gM, gN` are the forms of Riemannian
metrics this is exactly `IsRiemannianSubmersion`; the unbundled version is
needed for warped-product forms whose warping functions vanish somewhere
(e.g. `ρ = sin` in the Hopf examples), so that the forms are only positive
semidefinite. -/
def IsFormRiemannianSubmersion
    (gM : ∀ p : M, TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ)
    (gN : ∀ q : M', TangentSpace I' q →L[ℝ] TangentSpace I' q →L[ℝ] ℝ)
    (F : M → M') : Prop :=
  ContMDiff I I' ∞ F ∧
    (∀ p : M, Function.Surjective (mfderiv I I' F p)) ∧
    ∀ (p : M) (u v : TangentSpace I p),
      (∀ w : TangentSpace I p, mfderiv I I' F p w = 0 → gM p u w = 0) →
      (∀ w : TangentSpace I p, mfderiv I I' F p w = 0 → gM p v w = 0) →
      gM p u v = gN (F p) (mfderiv I I' F p u) (mfderiv I I' F p v)

end FormSubmersion

/-! ## The Hopf submersion in coordinates (Petersen Examples 1.4.10–1.4.11)

Petersen's tori `I × S¹ × S¹ → I × S¹` are treated on the universal cover:
`ℝ × ℝ × ℝ → ℝ × ℝ`, `(t, θ₁, θ₂) ↦ (t, θ₁ − θ₂)`. The circle versions
follow by local isometry along the covering `ℝ → S¹ = ℝ/2πℤ`, since all the
data (`P`, the two forms) descend to the quotient tori. -/

section HopfSubmersion

/-- **Math.** Petersen Example 1.4.11: the universal-cover model of the map
`I × S¹ × S¹ → I × S¹`, `(t, e^{iθ₁}, e^{iθ₂}) ↦ (t, e^{i(θ₁ − θ₂)})`, namely
`P : ℝ × ℝ × ℝ → ℝ × ℝ`, `P(t, θ₁, θ₂) = (t, θ₁ − θ₂)`. For `ρ = sin`,
`φ = cos` this is the coordinate expression of the Hopf map `S³ → S²(1/2)`
(Example 1.4.10). -/
def hopfSubmersionMap : ℝ × ℝ × ℝ → ℝ × ℝ :=
  fun q => (q.1, q.2.1 - q.2.2)

/-- **Eng.** On the tangent spaces of `ℝ` (viewed through
`innerProductSpaceMetric ℝ`) the metric inner product is plain
multiplication of real numbers. -/
theorem innerProductSpaceMetric_real_mul (t : ℝ) (a b : ℝ) :
    (innerProductSpaceMetric ℝ).metricInner t a b = b * a := rfl

/-- **Eng.** The differential of `hopfSubmersionMap` at any point is the
linear map `(a, b, c) ↦ (a, b − c)`. -/
theorem hopfSubmersionMap_mfderiv_apply (p : ℝ × ℝ × ℝ)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) p) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      hopfSubmersionMap p u = (u.1, u.2.1 - u.2.2) := by
  have h21 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × ℝ × ℝ => q.2.1) :=
    (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
  have h22 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × ℝ × ℝ => q.2.2) :=
    (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
  have hd21 : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      (fun q : ℝ × ℝ × ℝ => q.2.1) p := (h21 p).mdifferentiableAt (by simp)
  have hd22 : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      (fun q : ℝ × ℝ × ℝ => q.2.2) p := (h22 p).mdifferentiableAt (by simp)
  have hdsub : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      (fun q : ℝ × ℝ × ℝ => q.2.1 - q.2.2) p := hd21.sub hd22
  have key : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      hopfSubmersionMap p =
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
          (Prod.fst : ℝ × ℝ × ℝ → ℝ) p).prod
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
          (fun q : ℝ × ℝ × ℝ => q.2.1 - q.2.2) p) :=
    mfderiv_prodMk mdifferentiableAt_fst hdsub
  have hsubapp : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      (fun q : ℝ × ℝ × ℝ => q.2.1 - q.2.2) p u = u.2.1 - u.2.2 := by
    show mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
        ((fun q : ℝ × ℝ × ℝ => q.2.1) - (fun q : ℝ × ℝ × ℝ => q.2.2)) p u
        = u.2.1 - u.2.2
    rw [mfderiv_sub hd21 hd22,
      ← mfderiv_proj21_apply (I₁ := 𝓘(ℝ, ℝ)) (I₂ := 𝓘(ℝ, ℝ)) p u,
      ← mfderiv_proj22_apply (I₁ := 𝓘(ℝ, ℝ)) (I₂ := 𝓘(ℝ, ℝ)) p u]
    rfl
  have hfstapp : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × ℝ × ℝ → ℝ) p u = u.1 := by
    rw [mfderiv_fst]; rfl
  rw [key, ← hfstapp, ← hsubapp]
  rfl

/-- **Eng.** The doubly warped form `dt² + ρ²(t) dθ₁² + φ²(t) dθ₂²` on
`ℝ × ℝ × ℝ` (both factor metrics the standard one on `ℝ`), written out on
components of tangent vectors. -/
theorem doublyWarpedProductForm_real_apply (ρ φ : ℝ → ℝ) (p : ℝ × ℝ × ℝ)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) p) :
    doublyWarpedProductForm (innerProductSpaceMetric ℝ) (innerProductSpaceMetric ℝ)
        ρ φ p u v =
      u.1 * v.1 + (ρ p.1 ^ 2 * (u.2.1 * v.2.1) + φ p.1 ^ 2 * (u.2.2 * v.2.2)) := by
  have hfu : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      Prod.fst p u = u.1 := by rw [mfderiv_fst]; rfl
  have hfv : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ)
      Prod.fst p v = v.1 := by rw [mfderiv_fst]; rfl
  rw [doublyWarpedProductForm_apply, hfu, hfv, mfderiv_proj21_apply,
    mfderiv_proj21_apply, mfderiv_proj22_apply, mfderiv_proj22_apply]
  simp only [innerProductSpaceMetric_real_mul]
  ring

/-- **Eng.** The warped form `η²(t) dt² + σ²(t) dθ²` on `ℝ × ℝ` written out
on components of tangent vectors. -/
theorem warpedProductForm_real_apply (η σ : ℝ → ℝ) (q : ℝ × ℝ)
    (x y : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) q) :
    warpedProductForm (innerProductSpaceMetric ℝ) η σ q x y =
      η q.1 ^ 2 * (x.1 * y.1) + σ q.1 ^ 2 * (x.2 * y.2) := by
  have hfx : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.fst q x = x.1 := by
    rw [mfderiv_fst]; rfl
  have hfy : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.fst q y = y.1 := by
    rw [mfderiv_fst]; rfl
  have hsx : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd q x = x.2 := by
    rw [mfderiv_snd]; rfl
  have hsy : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd q y = y.2 := by
    rw [mfderiv_snd]; rfl
  rw [warpedProductForm_apply, hfx, hfy, hsx, hsy]
  simp only [innerProductSpaceMetric_real_mul]
  ring

/-- **Math.** Petersen Example 1.4.11 (target coefficient): the square of the
target warping function `ρφ/√(ρ² + φ²)` is Petersen's `dθ²`-coefficient
`(ρφ)²/(ρ² + φ²)`. -/
theorem hopfTargetWarping_sq (ρ φ : ℝ → ℝ) (t : ℝ) :
    (ρ t * φ t / Real.sqrt (ρ t ^ 2 + φ t ^ 2)) ^ 2 =
      (ρ t * φ t) ^ 2 / (ρ t ^ 2 + φ t ^ 2) := by
  rw [div_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]

/-- **Math.** Petersen Example 1.4.11 (the algebraic heart): if
`(·, a, b) ∈ ℝ³` is orthogonal to the kernel `{(0, c, c)}` of
`DP(a, b, c) = (a, b − c)` for the form `dt² + ρ² dθ₁² + φ² dθ₂²`, i.e.
`ρ²a + φ²b = 0`, then the horizontal part of the form agrees with the target
coefficient: `ρ²·ac + φ²·bd = (ρφ/√(ρ²+φ²))²·(a−b)(c−d)`. (One-sided
horizontality suffices: the kernel component of the other vector pairs to
zero on both sides.) -/
theorem hopfSubmersion_horizontal_algebra {ρ φ a b : ℝ} (c d : ℝ)
    (h : ρ ^ 2 * a + φ ^ 2 * b = 0) :
    ρ ^ 2 * (a * c) + φ ^ 2 * (b * d) =
      (ρ * φ / Real.sqrt (ρ ^ 2 + φ ^ 2)) ^ 2 * ((a - b) * (c - d)) := by
  rw [div_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), mul_pow]
  rcases eq_or_ne (ρ ^ 2 + φ ^ 2) 0 with h0 | h0
  · have hρ2 : ρ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg φ]) (sq_nonneg ρ)
    have hφ2 : φ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ρ]) (sq_nonneg φ)
    have hρ0 : ρ = 0 := pow_eq_zero_iff two_ne_zero |>.mp hρ2
    have hφ0 : φ = 0 := pow_eq_zero_iff two_ne_zero |>.mp hφ2
    simp [hρ0, hφ0]
  · rw [div_mul_eq_mul_div, eq_div_iff h0]
    linear_combination (ρ ^ 2 * c + φ ^ 2 * d) * h

/-- **Math.** Petersen Example 1.4.11 (the general Hopf-type submersion): on
the universal cover of `I × S¹ × S¹`, the map
`P(t, θ₁, θ₂) = (t, θ₁ − θ₂)` is *always* a Riemannian submersion from the
doubly warped form `dt² + ρ²(t) dθ₁² + φ²(t) dθ₂²` to the rotationally
symmetric form
`dr² + (ρφ/√(ρ² + φ²))²(r) dθ² = dr² + ((ρφ)²/(ρ² + φ²))(r) dθ²`
(coefficient identity: `hopfTargetWarping_sq`). Concretely: `P` is smooth,
`DP(a, b, c) = (a, b − c)` is surjective at every point, and on vectors
orthogonal to the kernel `{(0, c, c)}` — i.e. with `ρ²u₂ + φ²u₃ = 0` — the
two forms agree. Petersen states this on `I × S¹ × S¹ → I × S¹`; the circle
version follows from this one by the local isometry `ℝ → S¹` on each angular
factor, both forms being invariant under the deck translations
`θᵢ ↦ θᵢ + 2π`. -/
theorem hopfFibrationGeneralSubmersion (ρ φ : ℝ → ℝ) :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (innerProductSpaceMetric ℝ)
        (innerProductSpaceMetric ℝ) ρ φ)
      (warpedProductForm (innerProductSpaceMetric ℝ) (fun _ => 1)
        (fun t => ρ t * φ t / Real.sqrt (ρ t ^ 2 + φ t ^ 2)))
      hopfSubmersionMap := by
  refine ⟨?_, ?_, ?_⟩
  · -- Smoothness: both components of `P` are smooth.
    have h21 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × ℝ × ℝ => q.2.1) :=
      (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
    have h22 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × ℝ × ℝ => q.2.2) :=
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
    exact (contMDiff_fst (I := 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))).prodMk (h21.sub h22)
  · -- Surjectivity of `DP(a, b, c) = (a, b − c)`: preimage `(y₁, y₂, 0)`.
    intro p y
    refine ⟨show ℝ × ℝ × ℝ from (y.1, y.2, 0), ?_⟩
    rw [hopfSubmersionMap_mfderiv_apply]
    exact Prod.ext rfl (sub_zero y.2)
  · -- The metric identity on vectors orthogonal to `ker DP = {(0, c, c)}`.
    intro p u v hu _hv
    have hker : mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        hopfSubmersionMap p (show ℝ × ℝ × ℝ from (0, 1, 1)) = 0 := by
      rw [hopfSubmersionMap_mfderiv_apply]
      exact Prod.ext rfl (sub_self 1)
    have hu' : ρ p.1 ^ 2 * u.2.1 + φ p.1 ^ 2 * u.2.2 = 0 := by
      have h := hu (show ℝ × ℝ × ℝ from (0, 1, 1)) hker
      rw [doublyWarpedProductForm_real_apply] at h
      simpa using h
    rw [doublyWarpedProductForm_real_apply, warpedProductForm_real_apply]
    simp only [hopfSubmersionMap_mfderiv_apply]
    simp only [hopfSubmersionMap]
    linear_combination
      hopfSubmersion_horizontal_algebra (ρ := ρ p.1) (φ := φ p.1) v.2.1 v.2.2 hu'

/-- **Math.** Petersen Example 1.4.10 (the Hopf fibration revisited), on the
universal-cover model: write `S³(1)` as the doubly warped product
`dt² + sin²(t) dθ₁² + cos²(t) dθ₂²`, `t ∈ [0, π/2]`, via
`(t, e^{iθ₁}, e^{iθ₂}) ↦ (sin(t)e^{iθ₁}, cos(t)e^{iθ₂}) ∈ S³ ⊂ ℂ²`, and
`S²(1/2)` as `dr² + ¼ sin²(2r) dθ²` via
`(r, e^{iθ}) ↦ (½cos(2r), ½sin(2r)e^{iθ})`. In these coordinates the Hopf map
is `(t, θ₁, θ₂) ↦ (t, θ₁ − θ₂)` — Wilhelm's map — and it is a Riemannian
submersion: this is the case `ρ = sin`, `φ = cos` of
`hopfFibrationGeneralSubmersion`, with target coefficient
`(sin·cos)²/(sin² + cos²) = ¼sin²(2r)`, i.e. warping function `½ sin(2r)`.
As in Example 1.4.11 the statement is on the universal cover
`ℝ × ℝ × ℝ → ℝ × ℝ` of the torus coordinates; the identification with the
genuine spheres `S³(1) → S²(1/2)` (and with `SU(2)`, Example 1.4.13) needs
the coordinate immersions above and is beyond the present API. -/
theorem hopfFibrationRevisited :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (innerProductSpaceMetric ℝ)
        (innerProductSpaceMetric ℝ) Real.sin Real.cos)
      (warpedProductForm (innerProductSpaceMetric ℝ) (fun _ => 1)
        (fun r => Real.sin (2 * r) / 2))
      hopfSubmersionMap := by
  have hfun : (fun t => Real.sin t * Real.cos t /
      Real.sqrt (Real.sin t ^ 2 + Real.cos t ^ 2)) =
      fun r => Real.sin (2 * r) / 2 := by
    funext t
    rw [Real.sin_sq_add_cos_sq, Real.sqrt_one, div_one, Real.sin_two_mul]
    ring
  simpa only [hfun] using hopfFibrationGeneralSubmersion Real.sin Real.cos

end HopfSubmersion

end PetersenLib
