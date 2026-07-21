import MorganTianLib.Ch01.VolumeElement

/-!
# Morgan–Tian Ch. 1, §1.4 — small-time asymptotics and positivity of the radial volume element

This file completes the analytic description of the radial volume element
`λ(r) = det 𝒥(r)` of `lem:geodesic-polar-form`(4) (`MorganTianLib.volumeElement`)
near the centre of the geodesic polar coordinates:

* `tendsto_volumeElement_div_pow` — the **normalisation at `r = 0`**,
  `λ(r)/r^m → 1` as `r → 0⁺` (`m = dim E`). This is the determinant form of the
  expansion `𝒥(r) = r·Id + O(r³)` of `lem:jacobi-small-time`: the rescaled
  Jacobi field `r⁻¹ 𝒥(r)` converges to the identity in `E →L[ℝ] E`, and the
  determinant is continuous in finite dimension, so
  `λ(r)/r^m = det (r⁻¹ 𝒥(r)) → det Id = 1`.

* `volumeElement_pos` — **positivity of the volume element before the first
  conjugate point**: if `𝒥(r)` is invertible on `(0, r₀)` (no conjugate point),
  then `λ(r) > 0` there. Indeed `λ` is continuous and nowhere zero on the
  preconnected set `(0, r₀)`, and it is positive near `0` by the previous item;
  a sign change would force a zero by the intermediate value theorem.

Together these are what makes the logarithmic derivative `∂_r log λ = Tr A`
(`hasDerivAt_volumeElement`) usable, and they supply the initial condition
`λ(r)/sn_k^{m}(r) → 1` for the monotonicity argument behind
`lem:volume-element-comparison`, `thm:ricci-curvature-comparison` and
`thm:bishop-gromov`.

Blueprint: `lem:radial-volume-element`, `lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Topology

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E] [FiniteDimensional ℝ E]

variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

omit [CompleteSpace E] [Nontrivial E] in
/-- **Math.** The determinant of an endomorphism is a continuous function of the
endomorphism, in finite dimension: reading `f` in a basis is a linear map between
finite-dimensional spaces (hence continuous), and `det` of a matrix is a
polynomial in its entries.

Blueprint: `lem:radial-volume-element`. -/
theorem continuous_linearMap_det :
    Continuous fun f : E →L[ℝ] E => LinearMap.det ((f : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  classical
  set m := Module.finrank ℝ E with hm
  set bE := Module.finBasis ℝ E with hbE
  -- reading an endomorphism in the basis `bE` is a linear map out of a
  -- finite-dimensional space, hence continuous
  have hlin : Continuous fun f : E →L[ℝ] E =>
      (LinearMap.toMatrix bE bE ((f : E →L[ℝ] E) : E →ₗ[ℝ] E) :
        Matrix (Fin m) (Fin m) ℝ) :=
    LinearMap.continuous_of_finiteDimensional
      (((LinearMap.toMatrix bE bE).toLinearMap).comp (ContinuousLinearMap.coeLM ℝ))
  simpa [LinearMap.det_toMatrix] using hlin.matrix_det

omit [FiniteDimensional ℝ E] in
/-- **Math.** The **rescaled matrix Jacobi field converges to the identity**:
`r⁻¹ 𝒥(r) → Id` in `E →L[ℝ] E` as `r → 0⁺`. This is the expansion
`𝒥(r) = r·Id + O(r³)` of `lem:jacobi-small-time`, divided by `r`; quantitatively
`‖Id − r⁻¹ 𝒥(r)‖ ≤ C M r²/6`.

Blueprint: `lem:radial-volume-element`. -/
theorem tendsto_inv_smul_jacobi (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b) :
    Tendsto (fun r : ℝ => r⁻¹ • 𝒥 r) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  set M : ℝ := Real.exp (max 1 C * b) with hM
  -- quantitative bound `‖r⁻¹ • 𝒥 r − 1‖ ≤ C M r²/6` on `(0, b]`
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖r⁻¹ • 𝒥 r - 1‖ ≤ C * M * r ^ 2 / 6 := by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < b :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hb)
    filter_upwards [hev, self_mem_nhdsWithin] with r hrb (hr0 : (0 : ℝ) < r)
    have := h.sol.norm_one_sub_inv_smul_fst_le h.coeff_cont h.coeff_bound
      h.fst_zero h.snd_one (⟨hr0, hrb.le⟩ : r ∈ Ioc (0 : ℝ) b)
    rwa [norm_sub_rev] at this
  have hzero : Tendsto (fun r : ℝ => C * M * r ^ 2 / 6) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => C * M * r ^ 2 / 6 :=
      (continuous_const.mul (continuous_pow 2)).div_const 6
    have h0 : Tendsto (fun r : ℝ => C * M * r ^ 2 / 6) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using hc.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have := squeeze_zero_norm' hbound hzero
  simpa using this.add_const (1 : E →L[ℝ] E)

/-- **Math.** **Normalisation of the radial volume element at the centre**:
with `m = dim E`,
$$\frac{\lambda(r)}{r^{m}} \longrightarrow 1 \qquad (r \to 0^{+}),
\qquad \lambda(r) = \det \mathcal J(r).$$
Equivalently `λ(r) = r^m(1 + o(1))`, the determinant form of
`g_{ij}(r,θ) = r²(ĝ_{ij}(θ) + O(r²))` in `lem:geodesic-polar-form`(3).

Proof: `r⁻¹ 𝒥(r) → Id` (`tendsto_inv_smul_jacobi`), `det` is continuous in
finite dimension (`continuous_linearMap_det`), and
`det (r⁻¹ 𝒥(r)) = (r⁻¹)^m det 𝒥(r) = λ(r)/r^m` by `LinearMap.det_smul`.

Blueprint: `lem:radial-volume-element`. -/
theorem tendsto_volumeElement_div_pow (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b) :
    Tendsto (fun r : ℝ => volumeElement 𝒥 r / r ^ Module.finrank ℝ E)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcont := (continuous_linearMap_det (E := E)).continuousAt (x := (1 : E →L[ℝ] E))
  have hcomp : Tendsto
      (fun r : ℝ => LinearMap.det (((r⁻¹ • 𝒥 r : E →L[ℝ] E) : E →ₗ[ℝ] E)))
      (𝓝[>] (0 : ℝ)) (𝓝 (LinearMap.det ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E))) :=
    hcont.tendsto.comp (tendsto_inv_smul_jacobi h hb)
  have hone : LinearMap.det ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 := by
    have : ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = LinearMap.id := rfl
    rw [this, LinearMap.det_id]
  rw [hone] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : (0 : ℝ) < r)
  have hcoe : ((r⁻¹ • 𝒥 r : E →L[ℝ] E) : E →ₗ[ℝ] E)
      = r⁻¹ • ((𝒥 r : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
  rw [hcoe, LinearMap.det_smul, volumeElement, div_eq_inv_mul, inv_pow]

/-- **Math.** **Positivity of the radial volume element before the first
conjugate point.** If the matrix Jacobi field `𝒥` is invertible on `(0, r₀)` —
i.e. the radial geodesic has no conjugate point to the centre there, so `exp_p`
is non-singular — then
$$\lambda(r) = \det \mathcal J(r) > 0 \qquad \text{for all } r \in (0, r₀).$$

Proof: invertibility gives `λ ≠ 0` on `(0, r₀)`, and `λ` is continuous there.
By `tendsto_volumeElement_div_pow`, `λ(r)/r^m → 1 > 0`, so `λ > 0` at some point
of `(0, r₀)`. A point with `λ < 0` would, by the intermediate value theorem on
the interval joining the two points (contained in the order-connected set
`(0, r₀)`), produce a zero of `λ` — a contradiction.

Blueprint: `lem:radial-volume-element`, `lem:volume-element-comparison`. -/
theorem volumeElement_pos (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) {r₀ : ℝ} (hr₀ : r₀ ≤ b)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < volumeElement 𝒥 r := by
  classical
  intro r hr
  have hr₀0 : 0 < r₀ := hr.1.trans hr.2
  have hb : 0 < b := lt_of_lt_of_le hr₀0 hr₀
  set m := Module.finrank ℝ E with hm
  -- `λ` never vanishes on `(0, r₀)`
  have hne : ∀ s ∈ Ioo (0 : ℝ) r₀, volumeElement 𝒥 s ≠ 0 := by
    intro s hs
    obtain ⟨u, hu⟩ := hunit s hs
    obtain ⟨g, hg⟩ : ∃ g : E →L[ℝ] E, 𝒥 s * g = 1 :=
      ⟨(↑u⁻¹ : E →L[ℝ] E), by rw [← hu]; exact u.mul_inv⟩
    have hdet : volumeElement 𝒥 s * LinearMap.det ((g : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 := by
      have hmul : ((𝒥 s * g : E →L[ℝ] E) : E →ₗ[ℝ] E)
          = ((𝒥 s : E →L[ℝ] E) : E →ₗ[ℝ] E) * ((g : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
      have := congrArg (fun f : E →L[ℝ] E => LinearMap.det ((f : E →L[ℝ] E) : E →ₗ[ℝ] E)) hg
      simp only [hmul] at this
      rw [map_mul] at this
      have hone : LinearMap.det ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 := by
        have h1 : ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = LinearMap.id := rfl
        rw [h1, LinearMap.det_id]
      rw [hone] at this
      exact this
    intro h0
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  -- `λ` is continuous on `(0, r₀)`
  have hJcont : ContinuousOn 𝒥 (Ioo (0 : ℝ) r₀) :=
    (h.sol.continuousOn_fst).mono fun s hs => ⟨hs.1.le, hs.2.le.trans hr₀⟩
  have hcont : ContinuousOn (volumeElement 𝒥) (Ioo (0 : ℝ) r₀) :=
    (continuous_linearMap_det (E := E)).comp_continuousOn hJcont
  -- `λ > 0` somewhere on `(0, r₀)`, by the normalisation at the centre
  obtain ⟨r₁, hr₁mem, hr₁pos⟩ : ∃ r₁ ∈ Ioo (0 : ℝ) r₀, 0 < volumeElement 𝒥 r₁ := by
    have htend := tendsto_volumeElement_div_pow h hb
    have hgt : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < volumeElement 𝒥 s / s ^ m :=
      htend.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    have hlt : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < r₀ :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hr₀0)
    obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ :=
      ((hgt.and hlt).and self_mem_nhdsWithin).exists
    refine ⟨s, ⟨hs0, hs2⟩, ?_⟩
    have hpow : (0 : ℝ) < s ^ m := pow_pos hs0 m
    have := mul_pos hs1 hpow
    rwa [div_mul_cancel₀ _ (ne_of_gt hpow)] at this
  -- a negative value would force a zero, by the intermediate value theorem
  by_contra hneg
  have hlt0 : volumeElement 𝒥 r < 0 := lt_of_le_of_ne (not_lt.mp hneg) (hne r hr)
  have hsub : uIcc r r₁ ⊆ Ioo (0 : ℝ) r₀ :=
    (Set.ordConnected_Ioo (a := (0 : ℝ)) (b := r₀)).uIcc_subset hr hr₁mem
  have hivt : uIcc (volumeElement 𝒥 r) (volumeElement 𝒥 r₁)
      ⊆ volumeElement 𝒥 '' uIcc r r₁ :=
    intermediate_value_uIcc (hcont.mono hsub)
  have h0mem : (0 : ℝ) ∈ uIcc (volumeElement 𝒥 r) (volumeElement 𝒥 r₁) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hlt0.le, hr₁pos.le⟩)
  obtain ⟨c, hc, hc0⟩ := hivt h0mem
  exact hne c (hsub hc) hc0

end MorganTianLib

end
