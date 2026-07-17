import PoincareLib.Ch01.RadialComparison
import PoincareLib.Ch01.TraceRiccati
import PoincareLib.Ch01.RadialJacobiExists

/-!
# Morgan–Tian Ch. 1, §1.4 — the *sharp* trace Riccati comparison

`PoincareLib.Ch01.TraceRiccati` proves the trace comparison with the constant
`m = dim E`. Along a radial geodesic the relevant operator acts on the *full*
tangent space `T_pM` (dimension `n`), but the radial direction `u = γ'(0)` is a
distinguished eigendirection: it carries no curvature (`ℛ(r)u = 0`, since
`R(u, u)· = 0`) and the shape operator has eigenvalue exactly `1/r` there
(`A(r)u = (1/r)u`, because the radial Jacobi field is `𝒥(r)u = r·u`). The sharp
comparison therefore splits that direction off and runs the Riccati argument in
the remaining `n − 1` dimensions:

  `Tr A(r) − 1/r ≤ (n − 1)·sn_k'(r)/sn_k(r)`.

This is the inequality that integrates to `det 𝒥(r) ≤ r · sn_k(r)^{n−1}` and
hence to Bishop–Gromov; the naive constant `n` would give the *false* bound
`det 𝒥(r) ≤ sn_k(r)^n`.

## Results

* `sq_trace_sub_le` — the sharp trace Cauchy–Schwarz inequality: for a symmetric
  `A` with `A u = c·u`, `u` a unit vector,
  `(Tr A − c)² ≤ (m − 1)·(Tr(A²) − c²)`. Proved in an orthonormal basis whose
  first vector is `u`, splitting off that index and applying Cauchy–Schwarz to
  the remaining `m − 1` diagonal entries.
* `trace_riccati_comparison_perp` — the sharp trace Riccati comparison: with the
  Ricci-type bound `Tr A' + Tr(A²) ≤ (m − 1)·k` and the radial eigenvector data
  `A(r)u = (1/r)u`, the function `φ = Tr A − 1/r` satisfies
  `φ' + φ²/(m − 1) ≤ (m − 1)·k` and `φ/(m−1) − 1/r → 0`, so
  `φ ≤ (m − 1)·sn_k'/sn_k`.
* `IsRadialJacobi.apply_radial` / `shapeOp_apply_radial` — the radial column of
  the matrix Jacobi field is `𝒥(t)u = t·u`, `𝒥'(t)u = u`, hence
  `A(t)u = (1/t)u`.
* `trace_shapeOp_le_perp` — the geometric wrapper: the sharp mean-curvature
  comparison for the shape operator of the geodesic spheres.

Blueprint: `lem:trace-riccati-comparison`, `thm:ricci-curvature-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Real Filter Set Module
open scoped Topology RealInnerProductSpace

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ### The sharp trace Cauchy–Schwarz inequality -/

/-- **Math.** **Sharp trace Cauchy–Schwarz inequality.** Let `A` be a symmetric
endomorphism of the `m`-dimensional real inner product space `E`, and suppose the
unit vector `u` is an eigenvector, `A u = c·u`. Then

  `(Tr A − c)² ≤ (m − 1)·(Tr(A²) − c²)`.

In eigenvalue terms this is `(∑_{i≥2} λᵢ)² ≤ (m−1)·∑_{i≥2} λᵢ²`, the ordinary
Cauchy–Schwarz inequality after the eigenvalue `c` has been removed. The proof
extends `{u}` to an orthonormal basis `(eᵢ)` of `E` (`u` is one of the basis
vectors), writes `Tr A = ∑ ⟪A eᵢ, eᵢ⟫` and `Tr(A²) = ∑ ‖A eᵢ‖²` (symmetry of
`A`), notes that the `u`-terms are `c` and `c²`, and applies
`⟪A eᵢ, eᵢ⟫² ≤ ‖A eᵢ‖²` (Cauchy–Schwarz in `E`, `eᵢ` unit) together with the
discrete Cauchy–Schwarz inequality over the remaining `m − 1` indices.

This is what upgrades the constant `n` of `sq_trace_le_finrank_mul_trace_comp_self`
to the sharp constant `n − 1` in the radial setting.

Blueprint: `lem:trace-riccati-comparison`. -/
theorem sq_trace_sub_le {A : E →L[ℝ] E} (hsym : ∀ v w : E, ⟪A v, w⟫ = ⟪v, A w⟫)
    {u : E} (hu : ‖u‖ = 1) {c : ℝ} (hAu : A u = c • u) :
    (LinearMap.trace ℝ E ↑A - c) ^ 2
      ≤ ((finrank ℝ E : ℝ) - 1)
        * (LinearMap.trace ℝ E ↑(A ∘L A) - c ^ 2) := by
  classical
  -- `{u}` is an orthonormal subset; extend it to an orthonormal basis
  have hon : Orthonormal ℝ ((↑) : ({u} : Set E) → E) := by
    constructor
    · rintro ⟨x, hx⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hu
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      rw [Set.mem_singleton_iff] at hx hy
      exact absurd (Subtype.ext (hx.trans hy.symm)) hxy
  obtain ⟨s, bs, hsub, hcoe⟩ := hon.exists_orthonormalBasis_extension
  have humem : u ∈ s := by
    have : u ∈ (s : Set E) := hsub rfl
    exact_mod_cast this
  set i₀ : {x // x ∈ s} := ⟨u, humem⟩ with hi₀
  have hbi₀ : bs i₀ = u := by rw [hcoe]
  have hne : Nonempty {x // x ∈ s} := ⟨i₀⟩
  have hcard : Fintype.card {x // x ∈ s} = finrank ℝ E :=
    (Module.finrank_eq_card_basis bs.toBasis).symm
  have hm1 : 1 ≤ finrank ℝ E := by
    rw [← hcard]
    exact Fintype.card_pos
  -- the diagonal entries of `A` and of `A²`
  set a : {x // x ∈ s} → ℝ := fun i => ⟪bs i, A (bs i)⟫ with hadef
  set q : {x // x ∈ s} → ℝ := fun i => ⟪bs i, A (A (bs i))⟫ with hqdef
  have htrA : LinearMap.trace ℝ E ↑A = ∑ i, a i :=
    LinearMap.trace_eq_sum_inner (↑A : E →ₗ[ℝ] E) bs
  have htrAA : LinearMap.trace ℝ E ↑(A ∘L A) = ∑ i, q i := by
    rw [LinearMap.trace_eq_sum_inner (↑(A ∘L A) : E →ₗ[ℝ] E) bs]
    simp [hqdef]
  -- the `u`-entries are `c` and `c²`
  have hu2 : ⟪u, u⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have ha0 : a i₀ = c := by
    rw [hadef]
    simp only [hbi₀, hAu, real_inner_smul_right, hu2]
    ring
  have hq0 : q i₀ = c ^ 2 := by
    rw [hqdef]
    simp only [hbi₀, hAu, map_smul, real_inner_smul_right, hu2]
    ring
  -- each diagonal entry of `A²` dominates the square of that of `A`
  have hdiag : ∀ i, a i ^ 2 ≤ q i := by
    intro i
    have hnorm : ‖bs i‖ = 1 := bs.orthonormal.1 i
    have h1 : q i = ‖A (bs i)‖ ^ 2 := by
      rw [hqdef]
      simp only
      rw [real_inner_comm, hsym (A (bs i)) (bs i), real_inner_self_eq_norm_sq]
    have h2 : |⟪bs i, A (bs i)⟫| ≤ ‖A (bs i)‖ := by
      have := abs_real_inner_le_norm (bs i) (A (bs i))
      rwa [hnorm, one_mul] at this
    rw [h1, hadef]
    simp only
    nlinarith [mul_self_le_mul_self (abs_nonneg ⟪bs i, A (bs i)⟫) h2,
      sq_abs ⟪bs i, A (bs i)⟫]
  -- split off the index `i₀`
  set t : Finset {x // x ∈ s} := Finset.univ.erase i₀ with htdef
  have hsplit_a : LinearMap.trace ℝ E ↑A - c = ∑ i ∈ t, a i := by
    rw [htrA, ← Finset.add_sum_erase _ a (Finset.mem_univ i₀), ha0, htdef]
    ring
  have hsplit_q :
      LinearMap.trace ℝ E ↑(A ∘L A) - c ^ 2 = ∑ i ∈ t, q i := by
    rw [htrAA, ← Finset.add_sum_erase _ q (Finset.mem_univ i₀), hq0, htdef]
    ring
  have hcardt : (t.card : ℝ) = (finrank ℝ E : ℝ) - 1 := by
    have : t.card = finrank ℝ E - 1 := by
      rw [htdef, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
        hcard]
    rw [this, Nat.cast_sub hm1]
    norm_num
  have hnn : (0 : ℝ) ≤ (finrank ℝ E : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hm1
    linarith
  -- discrete Cauchy–Schwarz over the remaining `m − 1` indices
  have hCS : (∑ i ∈ t, a i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, a i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hsplit_a, hsplit_q]
  calc (∑ i ∈ t, a i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, a i ^ 2 := hCS
    _ = ((finrank ℝ E : ℝ) - 1) * ∑ i ∈ t, a i ^ 2 := by rw [hcardt]
    _ ≤ ((finrank ℝ E : ℝ) - 1) * ∑ i ∈ t, q i :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => hdiag i) hnn

/-! ### The sharp trace Riccati comparison -/

/-- **Math.** **Sharp trace Riccati comparison** — the analytic heart of the
Ricci comparison theorem and of Bishop–Gromov.

Let `E` have dimension `m ≥ 2`, fix `k ≥ 0` and `r₀ > 0`, and let `A(r)`,
`0 < r < r₀`, be a differentiable family of symmetric endomorphisms of `E` such
that the unit vector `u` is the radial eigendirection, `A(r)u = (1/r)·u`. Assume
the *Ricci* bound in traced Riccati form
`Tr A'(r) + Tr(A(r)²) ≤ (m − 1)·k` (in the application, `= −Ric(γ',γ') ≤ (n−1)k`)
and the asymptotics `Tr A(r) − m/r → 0` as `r → 0⁺`. Then

  `Tr A(r) − 1/r ≤ (m − 1)·sn_k'(r)/sn_k(r)`  for all `r ∈ (0, r₀)`.

Proof: put `φ = Tr A − 1/r`, so `φ' = Tr A' + 1/r²`. The sharp trace
Cauchy–Schwarz inequality (`sq_trace_sub_le`, with `c = 1/r`) gives
`φ² ≤ (m − 1)·(Tr(A²) − 1/r²)`, whence
`φ' = Tr A' + 1/r² ≤ (m−1)k − Tr(A²) + 1/r² ≤ (m−1)k − φ²/(m−1)`.
So `ψ = φ/(m−1)` satisfies the scalar Riccati inequality `ψ' + ψ² ≤ k`, and
`ψ − 1/r = (Tr A − m/r)/(m−1) → 0`; `scalar_riccati_comparison` gives
`ψ ≤ sn_k'/sn_k`, i.e. `φ ≤ (m−1)·sn_k'/sn_k`.

Note the constant: the radial direction contributes the eigenvalue `1/r` to
`Tr A` and is removed on both sides, leaving exactly `m − 1` dimensions. Using
`m` instead would make the volume comparison false.

Blueprint: `lem:trace-riccati-comparison`, `thm:ricci-curvature-comparison`. -/
theorem trace_riccati_comparison_perp {k r₀ : ℝ} (hk : 0 ≤ k)
    (hdim : 2 ≤ finrank ℝ E) {A A' : ℝ → E →L[ℝ] E} {u : E} (hu : ‖u‖ = 1)
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsym : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ v w : E, ⟪A r v, w⟫ = ⟪v, A r w⟫)
    (hAu : ∀ r ∈ Ioo (0 : ℝ) r₀, A r u = (1 / r) • u)
    (hRic : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A' r) + LinearMap.trace ℝ E ↑(A r ∘L A r)
        ≤ ((finrank ℝ E : ℝ) - 1) * k)
    (h0 : Tendsto
      (fun r => LinearMap.trace ℝ E ↑(A r) - (finrank ℝ E : ℝ) / r)
      (𝓝[>] 0) (𝓝 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A r) - 1 / r
        ≤ ((finrank ℝ E : ℝ) - 1) * (csK k r / snK k r) := by
  set n : ℝ := (finrank ℝ E : ℝ) - 1 with hndef
  have hn : 0 < n := by
    have : (2 : ℝ) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hdim
    rw [hndef]; linarith
  -- the trace functional as a continuous linear map on endomorphisms
  set L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)) with hL
  have hLapp : ∀ T : E →L[ℝ] E, L T = LinearMap.trace ℝ E ↑T := fun T => rfl
  -- the normalized radial-corrected trace `ψ = (Tr A − 1/r)/(m−1)`
  set ψ : ℝ → ℝ := fun r => (LinearMap.trace ℝ E ↑(A r) - 1 / r) / n with hψdef
  set ψ' : ℝ → ℝ :=
    fun r => (LinearMap.trace ℝ E ↑(A' r) + 1 / r ^ 2) / n with hψ'def
  have hψd : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ψ (ψ' r) r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have htr : HasDerivAt (fun x => LinearMap.trace ℝ E ↑(A x))
        (LinearMap.trace ℝ E ↑(A' r)) r := by
      have h := L.hasFDerivAt.comp_hasDerivAt r (hA r hr)
      simpa only [Function.comp_def, hLapp] using h
    have hinv : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / r ^ 2)) r := by
      simpa [one_div] using hasDerivAt_inv hr0
    have h := (htr.sub hinv).div_const n
    have heq : LinearMap.trace ℝ E ↑(A' r) - -(1 / r ^ 2)
        = LinearMap.trace ℝ E ↑(A' r) + 1 / r ^ 2 := by ring
    rw [heq] at h
    exact h
  -- the scalar Riccati inequality `ψ' + ψ² ≤ k`
  have hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ψ' r + ψ r ^ 2 ≤ k := by
    intro r hr
    have hCS := sq_trace_sub_le (hsym r hr) hu (hAu r hr)
    have hsq : ((1 : ℝ) / r) ^ 2 = 1 / r ^ 2 := by
      rw [div_pow]; norm_num
    rw [hsq] at hCS
    have hR := hRic r hr
    have hRn := mul_le_mul_of_nonneg_left hR hn.le
    have key : (LinearMap.trace ℝ E ↑(A' r) + 1 / r ^ 2) * n
        + (LinearMap.trace ℝ E ↑(A r) - 1 / r) ^ 2 ≤ k * n ^ 2 := by
      nlinarith [hCS, hRn]
    have heq : ψ' r + ψ r ^ 2
        = ((LinearMap.trace ℝ E ↑(A' r) + 1 / r ^ 2) * n
            + (LinearMap.trace ℝ E ↑(A r) - 1 / r) ^ 2) / n ^ 2 := by
      rw [hψ'def, hψdef]
      field_simp
    rw [heq, div_le_iff₀ (pow_pos hn 2)]
    exact key
  -- the asymptotics `ψ − 1/r → 0`
  have h0' : Tendsto (fun r => ψ r - 1 / r) (𝓝[>] 0) (𝓝 0) := by
    have h := h0.div_const n
    rw [zero_div] at h
    refine h.congr fun r => ?_
    rw [hψdef]
    simp only
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    · field_simp
      ring
  -- conclude by the scalar Riccati comparison
  have hcmp := scalar_riccati_comparison hk hψd hric h0'
  intro r hr
  have h := hcmp r hr
  rw [hψdef] at h
  simp only at h
  rw [div_le_iff₀ hn] at h
  calc LinearMap.trace ℝ E ↑(A r) - 1 / r ≤ csK k r / snK k r * n := h
    _ = n * (csK k r / snK k r) := by ring

/-! ### The radial column of the matrix Jacobi field -/

section Radial

variable [CompleteSpace E] [Nontrivial E] {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- **Math.** **The radial Jacobi field.** If the unit radial direction `u`
satisfies `ℛ(t)u = 0` (which holds along a geodesic: `R(u, γ')γ' = 0` for
`u = γ'`), then the `u`-column of the matrix Jacobi field is the *affine* Jacobi
field `𝒥(t)u = t·u`, with `𝒥'(t)u = u`.

Proof: `t ↦ (𝒥(t)u, 𝒥'(t)u)` solves the vector Jacobi equation `y'' + ℛ y = 0`
(`IsJacobiSolOn.apply`), and so does `t ↦ (t·u, u)` since `ℛ(t)(t·u) = t·ℛ(t)u = 0`;
both have initial data `(0, u)` (`𝒥(0) = 0`, `𝒥'(0) = 1`), so they agree on
`[0, b]` by ODE uniqueness (`IsJacobiSolOn.eqOn_of_left`).

Blueprint: `lem:trace-riccati-comparison`. -/
theorem IsRadialJacobi.apply_radial (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) {u : E}
    (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, 𝒥 t u = t • u ∧ 𝒥' t u = u := by
  have h₁ : IsJacobiSolOn ℛ 0 b (fun t => 𝒥 t u) (fun t => 𝒥' t u) :=
    h.sol.apply u
  have h₂ : IsJacobiSolOn ℛ 0 b (fun t : ℝ => t • u) (fun _ => u) := by
    constructor
    · intro t _
      have : HasDerivAt (fun t : ℝ => t • u) ((1 : ℝ) • u) t :=
        (hasDerivAt_id t).smul_const u
      simpa using this.hasDerivWithinAt
    · intro t ht
      have hz : -(ℛ t) ((fun t : ℝ => t • u) t) = 0 := by
        simp [map_smul, hRu t ht]
      rw [hz]
      exact (hasDerivWithinAt_const t _ u)
  have hy : (fun t => 𝒥 t u) 0 = (fun t : ℝ => t • u) 0 := by
    simp [h.fst_zero]
  have hv : (fun t => 𝒥' t u) 0 = (fun _ : ℝ => u) 0 := by
    simp [h.snd_one]
  obtain ⟨he₁, he₂⟩ := IsJacobiSolOn.eqOn_of_left h.curv_cont h₁ h₂ hy hv
  exact fun t ht => ⟨he₁ ht, he₂ ht⟩

omit [FiniteDimensional ℝ E] in
/-- **Math.** The radial direction is an eigendirection of the shape operator
with the *round-sphere* eigenvalue `1/r`: `A(r)u = (1/r)·u`. Indeed `𝒥(r)u = r·u`
and `𝒥'(r)u = u` (`IsRadialJacobi.apply_radial`), so
`𝒥(r)⁻¹u = (1/r)·u` and `A(r)u = 𝒥'(r)(𝒥(r)⁻¹u) = (1/r)·u`.

Blueprint: `lem:trace-riccati-comparison`. -/
theorem shapeOp_apply_radial (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) {u : E}
    (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) b)
    (hunit : IsUnit (𝒥 r)) : shapeOp 𝒥 𝒥' r u = (1 / r) • u := by
  have hrIcc : r ∈ Icc (0 : ℝ) b := ⟨hr.1.le, hr.2.le⟩
  obtain ⟨hJ, hJ'⟩ := h.apply_radial hRu r hrIcc
  have hr0 : r ≠ 0 := hr.1.ne'
  -- `𝒥 r (r⁻¹ • u) = u`
  have hkey : 𝒥 r (r⁻¹ • u) = u := by
    rw [map_smul, hJ, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hinv : Ring.inverse (𝒥 r) u = r⁻¹ • u := by
    calc Ring.inverse (𝒥 r) u = Ring.inverse (𝒥 r) (𝒥 r (r⁻¹ • u)) := by rw [hkey]
      _ = (Ring.inverse (𝒥 r) * 𝒥 r) (r⁻¹ • u) := rfl
      _ = (1 : E →L[ℝ] E) (r⁻¹ • u) := by rw [Ring.inverse_mul_cancel _ hunit]
      _ = r⁻¹ • u := rfl
  rw [shapeOp_apply, hinv, map_smul, hJ', one_div]

/-! ### The geometric wrapper -/

/-- **Math.** **Sharp mean-curvature comparison** (`thm:ricci-curvature-comparison`,
the form that integrates to Bishop–Gromov).

Along the radial geodesic, in the parallel frame, assume:
* the unit radial direction `u` is curvature-free, `ℛ(t)u = 0` (always true:
  `R(u, u)· = 0`);
* no conjugate points on `(0, r₀)`, i.e. `𝒥(r)` is invertible there;
* the **Ricci** lower bound `Ric(γ',γ') ≥ −(n−1)k`, i.e. `Tr ℛ(r) ≥ −(n−1)k`.

Then the mean curvature of the geodesic spheres, corrected by the radial
eigenvalue `1/r`, obeys the sharp bound

  `Tr A(r) − 1/r ≤ (n − 1)·sn_k'(r)/sn_k(r)`.

Proof: the traced Riccati equation `Tr A' + Tr(A²) = −Tr ℛ ≤ (n−1)k` and the
radial eigendata `A(r)u = (1/r)u` (`shapeOp_apply_radial`) are exactly the
hypotheses of `trace_riccati_comparison_perp`; the asymptotics
`Tr A(r) − n/r → 0` come from `A(r) − (1/r)Id → 0`
(`tendsto_shapeOp_sub_inv_smul_id`) and continuity of the trace.

Integrating this inequality gives `(log det 𝒥)'(r) ≤ 1/r + (n−1)·sn_k'/sn_k`,
i.e. `det 𝒥(r) ≤ r·sn_k(r)^{n−1}` — the volume-element comparison behind
`thm:bishop-gromov`. Blueprint: `thm:ricci-curvature-comparison`. -/
theorem trace_shapeOp_le_perp (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b) (hdim : 2 ≤ finrank ℝ E) {u : E}
    (hu : ‖u‖ = 1) (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r) - 1 / r
        ≤ ((finrank ℝ E : ℝ) - 1) * (csK k r / snK k r) := by
  set L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)) with hL
  have hLapp : ∀ T : E →L[ℝ] E, L T = LinearMap.trace ℝ E ↑T := fun T => rfl
  refine trace_riccati_comparison_perp hk hdim (A := shapeOp 𝒥 𝒥')
    (A' := fun r => -(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r) hu
    (hasDerivAt_shapeOp_of_lt h hr₀ hunit)
    (shapeOp_symm_of_lt h hb hr₀ hunit) ?_ ?_ ?_
  · -- the radial eigendirection
    intro r hr
    exact shapeOp_apply_radial h hRu ⟨hr.1, hr.2.trans_le hr₀⟩ (hunit r hr)
  · -- traced Riccati: `Tr A' + Tr(A²) = −Tr ℛ ≤ (n−1)k`
    intro r hr
    have hcomp : (shapeOp 𝒥 𝒥' r ∘L shapeOp 𝒥 𝒥' r)
        = shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r := rfl
    have hsplit : LinearMap.trace ℝ E
          ↑(-(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r)
        = -LinearMap.trace ℝ E ↑(ℛ r)
          - LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r) := by
      rw [← hLapp, ← hLapp, ← hLapp, map_sub, map_neg]
    rw [hcomp, hsplit]
    have := hric r hr
    linarith
  · -- asymptotics `Tr A(r) − n/r → 0`
    have h0 := tendsto_shapeOp_sub_inv_smul_id h hb
    have hcont : Tendsto
        (fun r => L (shapeOp 𝒥 𝒥' r - r⁻¹ • ContinuousLinearMap.id ℝ E))
        (𝓝[>] (0 : ℝ)) (𝓝 (L 0)) := (L.continuous.tendsto 0).comp h0
    rw [map_zero] at hcont
    refine hcont.congr fun r => ?_
    rw [map_sub, map_smul, hLapp, hLapp]
    have hid : LinearMap.trace ℝ E ↑(ContinuousLinearMap.id ℝ E)
        = (finrank ℝ E : ℝ) := by simp
    rw [hid]
    simp [div_eq_inv_mul]

end Radial

end PoincareLib

end
