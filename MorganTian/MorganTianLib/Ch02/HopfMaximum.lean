import MorganTianLib.Ch02.HopfChart
import MorganTianLib.Ch02.HopfBarrierAnnulus
import MorganTianLib.Ch02.LaplacianExtremum

/-!
# Morgan–Tian Ch. 2 §2.2 — the Hopf strong maximum principle

Blueprint `lem:hopf-strong-maximum` (E. Hopf): let `U` be a connected open
set in a Riemannian manifold and `h` a smooth function on `U` with `Δh ≥ 0`
on `U`. If `h` attains its supremum over `U` at a point of `U`, then `h` is
constant on `U`.

The proof is the classical barrier argument, following the blueprint text.
The set `{h = m}` (`m` the maximum value) is closed in `U` and, by the chart
argument packaged in `hopf_eqOn_max_near`, open in `U`; preconnectedness
closes the argument (`IsPreconnected.subset_of_closure_inter_subset`). The
chart argument works in a fixed chart at a maximum point `z`: assuming a
nearby point with `h < m`, one finds a Euclidean ball `D(x₀, R)` touching
the compact set `F = {V = m}` (`V` the coordinate representation of `h`)
from outside at some `y₁`, with `V < m` on the open ball; `Δ` reads in the
chart as the elliptic operator `chartLaplaceOp` with continuous coefficients
and positive-definite leading part, so by
`exists_pos_forall_barrier_elliptic_pos` the barrier
`w = exp(−κ‖·−x₀‖²) − exp(−κR²)` satisfies `L w > 0` on the closed annulus
`A = {R/2 ≤ ‖y−x₀‖ ≤ R}` for a suitable exponent `κ > 0`. The perturbation
`v = h + ε w` (with `ε = δ/2`, `δ` the gap of `h` below `m` on the inner
sphere) then attains its maximum over `A` neither at an interior point
(there `Δv > 0`, contradicting `lem:laplacian-nonpositive-at-max`) nor on
the inner sphere (where `v < m ≤ max`), so at a point `q` of the outer
sphere with `v(q) = m = h(q)`; but then `dh(q) = 0` (the manifold Fermat
lemma), so the derivative of `v` at `q` along the inward direction `x₀ − q`
is `ε` times the inward radial derivative of the barrier, which is strictly
positive — contradicting maximality of `v` at `q` along the segment towards
`x₀` (`IsLocalMaxOn.hasFDerivWithinAt_nonpos`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
§2.2, Lemma 2.9 (blueprint `lem:hopf-strong-maximum`).
-/

open scoped ContDiff Manifold Topology Bundle InnerProductSpace
open Riemannian Riemannian.Tensor Filter Set Metric

noncomputable section

namespace MorganTianLib

/-- **Math.** The model basis is nondegenerate for the inner product: a vector
orthogonal to every `finBasis` vector is zero.
Blueprint: `lem:hopf-strong-maximum` (nondegeneracy of the frame). -/
theorem eq_zero_of_inner_finBasis_eq_zero {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] {v : E'}
    (hv : ∀ a, ⟪v, (Module.finBasis ℝ E') a⟫_ℝ = 0) : v = 0 := by
  have hvv : ⟪v, v⟫_ℝ = 0 := by
    nth_rewrite 2 [← (Module.finBasis ℝ E').sum_repr v]
    rw [inner_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [real_inner_smul_right, hv a, mul_zero]
  exact inner_self_eq_zero.mp hvv

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]


/-- **Math.** Localized chart formula: `Δf(p) = L(f ∘ φ⁻¹)(φ(p))` for `f`
smooth only on an open set `O ∋ p` — glue with a bump function and use
germ-locality of both sides. Blueprint: `lem:laplacian-christoffel-formula`. -/
theorem laplacianAt_eq_chartLaplaceOp_of_contMDiffOn (g : RiemannianMetric I M)
    {f : M → ℝ} {O : Set M} (hO : IsOpen O)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f O) {α p : M} (hpO : p ∈ O)
    (hp : p ∈ (chartAt H α).source) :
    laplacianAt g g.leviCivitaConnection f p
      = chartLaplaceOp (I := I) g α (f ∘ (extChartAt I α).symm)
          (extChartAt I α p) := by
  obtain ⟨f', hf', hff'⟩ :=
    exists_contMDiff_eventuallyEq_of_contMDiffOn (I := I) hO hpO hf
  have hq : (extChartAt I α).symm (extChartAt I α p) = p :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  have hyt : extChartAt I α p ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rwa [extChartAt_source])
  have hsymm_cont : ContinuousAt (extChartAt I α).symm (extChartAt I α p) :=
    (continuousOn_extChartAt_symm (I := I) α _ hyt).continuousAt
      (extChartAt_target_mem_nhds' hyt)
  have htend : Tendsto (extChartAt I α).symm (𝓝 (extChartAt I α p)) (𝓝 p) := by
    have := hsymm_cont.tendsto
    rwa [hq] at this
  calc laplacianAt g g.leviCivitaConnection f p
      = laplacianAt g g.leviCivitaConnection f' p :=
        laplacianAt_congr_of_eventuallyEq g g.leviCivitaConnection hff'.symm
    _ = chartLaplaceOp (I := I) g α (f' ∘ (extChartAt I α).symm)
          (extChartAt I α p) := laplacianAt_eq_chartLaplaceOp g hf' hp
    _ = chartLaplaceOp (I := I) g α (f ∘ (extChartAt I α).symm)
          (extChartAt I α p) :=
        chartLaplaceOp_congr g α (hff'.comp_tendsto htend)

/-- **Math.** **Openness step of the Hopf strong maximum principle**: if a
smooth function `h` on an open set `U` has `Δh ≥ 0` on `U`, is bounded above
by `m` on `U`, and attains the value `m` at `z ∈ U`, then `h ≡ m` on an open
neighbourhood of `z` inside `U` — the barrier argument in a chart at `z`.
Blueprint: `lem:hopf-strong-maximum` (the set `E` is open). -/
theorem hopf_eqOn_max_near (g : RiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) {h : M → ℝ}
    (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U)
    (hsub : ∀ x ∈ U, 0 ≤ laplacianAt g g.leviCivitaConnection h x)
    {m : ℝ} (hle : ∀ x ∈ U, h x ≤ m)
    {z : M} (hz : z ∈ U) (hzm : h z = m) :
    ∃ O : Set M, IsOpen O ∧ z ∈ O ∧ O ⊆ U ∧ ∀ x ∈ O, h x = m := by
  classical
  -- ### chart set-up at `z`
  have hzsrc : z ∈ (chartAt H z).source := mem_chart_source H z
  have hzsrc' : z ∈ (extChartAt I z).source := by
    rw [extChartAt_source]; exact hzsrc
  set U' : Set M := U ∩ (chartAt H z).source with hU'def
  have hU'open : IsOpen U' := hU.inter (chartAt H z).open_source
  have hzU' : z ∈ U' := ⟨hz, hzsrc⟩
  -- the open coordinate image of `U'`
  set T : Set E := (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' U'
    with hTdef
  have hTopen : IsOpen T :=
    (continuousOn_extChartAt_symm (I := I) z).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := I) z) hU'open
  have hzT : extChartAt I z z ∈ T :=
    ⟨(extChartAt I z).map_source hzsrc', by
      rw [mem_preimage, (extChartAt I z).left_inv hzsrc']
      exact hzU'⟩
  have hTtarget : T ⊆ (extChartAt I z).target := inter_subset_left
  have hsymmT : ∀ y ∈ T, (extChartAt I z).symm y ∈ U' := fun y hy => hy.2
  -- ### radius: `closedBall (φ z) (3ρ) ⊆ T`
  obtain ⟨ρ', hρ'pos, hballρ'⟩ := Metric.isOpen_iff.mp hTopen _ hzT
  set ρ : ℝ := ρ' / 4 with hρdef
  have hρpos : 0 < ρ := by positivity
  have h3ρ : closedBall (extChartAt I z z) (3 * ρ) ⊆ T := fun y hy => by
    apply hballρ'
    rw [mem_ball]
    have h1 := mem_closedBall.mp hy
    have h2 : ρ = ρ' / 4 := hρdef
    linarith
  set K : Set E := closedBall (extChartAt I z z) (2 * ρ) with hKdef
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hKT : K ⊆ T := fun y hy => h3ρ (by
    rw [mem_closedBall] at hy ⊢
    linarith)
  -- ### globally smooth extension of `h` near the compact `φ⁻¹(K)`
  have hKMcompact : IsCompact ((extChartAt I z).symm '' K) :=
    hKcompact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) z).mono
        fun y hy => hTtarget (hKT hy))
  have hKMU : (extChartAt I z).symm '' K ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact (hsymmT y (hKT hy)).1
  obtain ⟨h', hh', W, hWopen, hKW₀, hWU, hWeq⟩ :=
    exists_contMDiff_eqOn_open_of_contMDiffOn hU hKMcompact hKMU hh
  have hKW : ∀ y ∈ K, (extChartAt I z).symm y ∈ W := fun y hy =>
    hKW₀ (mem_image_of_mem _ hy)
  -- the coordinate representation of `h'`
  set V : E → ℝ := h' ∘ (extChartAt I z).symm with hVdef
  have hVsmooth : ContDiffOn ℝ ∞ V (extChartAt I z).target :=
    (hh'.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := I) z)).contDiffOn
  have hVcont : ContinuousOn V K :=
    hVsmooth.continuousOn.mono fun y hy => hTtarget (hKT hy)
  -- `V ≤ m` on `K`, `V(φ z) = m`
  have hVle : ∀ y ∈ K, V y ≤ m := by
    intro y hy
    show h' ((extChartAt I z).symm y) ≤ m
    rw [hWeq (hKW y hy)]
    exact hle _ (hsymmT y (hKT hy)).1
  have hzK : extChartAt I z z ∈ K := mem_closedBall_self (by positivity)
  have hVz : V (extChartAt I z z) = m := by
    show h' ((extChartAt I z).symm (extChartAt I z z)) = m
    rw [hWeq (hKW _ hzK), (extChartAt I z).left_inv hzsrc']
    exact hzm
  -- ### the open patch and the claim
  refine ⟨U' ∩ extChartAt I z ⁻¹' ball (extChartAt I z z) ρ,
    ((continuousOn_extChartAt (I := I) z).mono
        (fun x hx => by rw [extChartAt_source]; exact hx.2)).isOpen_inter_preimage
      hU'open isOpen_ball,
    ⟨hzU', by simpa using hρpos⟩, fun x hx => hx.1.1, ?_⟩
  intro x hxpatch
  by_contra hxm
  obtain ⟨hxU', hxball⟩ := hxpatch
  have hxsrc' : x ∈ (extChartAt I z).source := by
    rw [extChartAt_source]; exact hxU'.2
  -- ### the center of the touching ball
  set x₀ : E := extChartAt I z x with hx₀def
  have hx₀ball : dist x₀ (extChartAt I z z) < ρ := mem_ball.mp hxball
  have hx₀K : x₀ ∈ K := by
    rw [hKdef, mem_closedBall]
    linarith
  have hVx₀ : V x₀ < m := by
    have hVx : V x₀ = h x := by
      show h' ((extChartAt I z).symm (extChartAt I z x)) = h x
      rw [(extChartAt I z).left_inv hxsrc',
        hWeq (by rw [← (extChartAt I z).left_inv hxsrc']; exact hKW _ hx₀K)]
    rw [hVx]
    exact lt_of_le_of_ne (hle x hxU'.1) hxm
  -- ### the touching ball: `F`, `R`, `y₁`
  set F : Set E := K ∩ V ⁻¹' {m} with hFdef
  have hFmem : ∀ y, y ∈ F ↔ y ∈ K ∧ V y = m := fun y => by
    rw [hFdef, mem_inter_iff, mem_preimage, mem_singleton_iff]
  have hFclosed : IsClosed F :=
    hVcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hFcompact : IsCompact F :=
    hKcompact.of_isClosed_subset hFclosed fun y hy => hy.1
  have hFne : F.Nonempty := ⟨extChartAt I z z, (hFmem _).mpr ⟨hzK, hVz⟩⟩
  have hx₀F : x₀ ∉ F := fun hc => absurd ((hFmem _).mp hc).2 (ne_of_lt hVx₀)
  obtain ⟨y₁, hy₁F, hRdist⟩ := hFcompact.exists_infDist_eq_dist hFne x₀
  set R : ℝ := Metric.infDist x₀ F with hRdef
  have hRpos : 0 < R := by
    rcases (Metric.infDist_nonneg (s := F) (x := x₀)).lt_or_eq with hgt | heq
    · exact hgt
    · exfalso
      have hd0 : dist x₀ y₁ = 0 := by rw [← hRdist]; exact heq.symm
      rw [dist_eq_zero] at hd0
      exact hx₀F (hd0 ▸ hy₁F)
  have hRρ : R < ρ := by
    have h1 : R ≤ dist x₀ (extChartAt I z z) :=
      Metric.infDist_le_dist_of_mem ((hFmem _).mpr ⟨hzK, hVz⟩)
    linarith
  -- ### the annulus
  set A : Set E := closedBall x₀ R \ ball x₀ (R / 2) with hAdef
  have hAcompact : IsCompact A := (isCompact_closedBall _ _).diff isOpen_ball
  have hcbK : closedBall x₀ R ⊆ K := by
    intro y hy
    rw [hKdef, mem_closedBall]
    have h1 : dist y x₀ ≤ R := mem_closedBall.mp hy
    calc dist y (extChartAt I z z)
        ≤ dist y x₀ + dist x₀ (extChartAt I z z) := dist_triangle _ _ _
      _ ≤ 2 * ρ := by linarith
  have hAK : A ⊆ K := fun y hy => hcbK hy.1
  have hAT : A ⊆ (extChartAt I z).target := fun y hy => hTtarget (hKT (hAK hy))
  have hx₀A : x₀ ∉ A := fun hc => hc.2 (mem_ball_self (by positivity))
  -- strictly below the max inside the ball
  have hlt_inside : ∀ y, dist y x₀ < R → V y < m := by
    intro y hyd
    have hyK : y ∈ K := hcbK (mem_closedBall.mpr hyd.le)
    refine lt_of_le_of_ne (hVle y hyK) fun hc => ?_
    have hyF : y ∈ F := (hFmem _).mpr ⟨hyK, hc⟩
    have h2 : R ≤ dist x₀ y := Metric.infDist_le_dist_of_mem hyF
    have h3 : dist x₀ y = dist y x₀ := dist_comm _ _
    linarith
  -- ### the barrier exponent
  obtain ⟨κ, hκpos, hκ⟩ := exists_pos_forall_barrier_elliptic_pos
    (Module.finBasis ℝ E)
    (fun v hv => eq_zero_of_inner_finBasis_eq_zero hv)
    (A := fun y a c => chartInvGramOnE (I := I) g z a c y)
    (b := fun y k => chartLaplaceB (I := I) g z k y)
    hAcompact
    (fun a c => (chartInvGramOnE_continuousOn g z a c).mono hAT)
    (fun k => (chartLaplaceB_continuousOn g z k).mono hAT)
    (fun y hy ξ hξ => chartInvGramOnE_quadratic_pos g z (hAT hy) hξ)
    hx₀A
  have hκ' : ∀ y ∈ A, 0 < chartLaplaceOp (I := I) g z (hopfBarrier κ x₀) y :=
    fun y hy => hκ y hy
  -- ### the inner-sphere gap and `ε`
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne _))
  have hsne : (sphere x₀ (R / 2)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  have hsK : sphere x₀ (R / 2) ⊆ K := fun y hy =>
    hcbK (mem_closedBall.mpr (by rw [mem_sphere] at hy; linarith))
  obtain ⟨ys, hys, hysmax⟩ := (isCompact_sphere x₀ (R / 2)).exists_isMaxOn hsne
    (hVcont.mono hsK)
  set δ : ℝ := m - V ys with hδdef
  have hδpos : 0 < δ := by
    have : V ys < m := hlt_inside ys (by rw [mem_sphere] at hys; linarith [hys])
    rw [hδdef]
    linarith
  set ε : ℝ := δ / 2 with hεdef
  have hεpos : 0 < ε := by positivity
  -- ### the perturbed function and its maximum over the annulus
  set c₀ : ℝ := Real.exp (-κ * R ^ 2) with hc₀def
  set VE : E → ℝ := fun y => V y + ε * (hopfBarrier κ x₀ y - c₀) with hVEdef
  have hVEcont : ContinuousOn VE A :=
    (hVcont.mono hAK).add (continuousOn_const.mul
      (((hopfBarrier_contDiff κ x₀).continuous.sub continuous_const).continuousOn))
  have hy₁A : y₁ ∈ A := by
    have hd : dist y₁ x₀ = R := by rw [dist_comm, ← hRdist, hRdef]
    constructor
    · rw [mem_closedBall, hd]
    · intro hc
      rw [mem_ball, hd] at hc
      linarith
  obtain ⟨q, hqA, hqmax⟩ := hAcompact.exists_isMaxOn ⟨y₁, hy₁A⟩ hVEcont
  have hy₁norm : ‖y₁ - x₀‖ = R := by
    rw [← dist_eq_norm, dist_comm, ← hRdist, hRdef]
  have hVEy₁ : VE y₁ = m := by
    show V y₁ + ε * (hopfBarrier κ x₀ y₁ - c₀) = m
    rw [hopfBarrier_eq_of_norm_eq hy₁norm, ← hc₀def, ((hFmem _).mp hy₁F).2]
    ring
  have hmq : m ≤ VE q := hVEy₁ ▸ hqmax hy₁A
  have hq_le : dist q x₀ ≤ R := mem_closedBall.mp hqA.1
  have hq_ge : R / 2 ≤ dist q x₀ := by
    by_contra hc
    push Not at hc
    exact hqA.2 (mem_ball.mpr hc)
  -- ### the manifold point behind `q`
  have hqT : q ∈ T := hKT (hAK hqA)
  have hqtarget : q ∈ (extChartAt I z).target := hTtarget hqT
  set qM : M := (extChartAt I z).symm q with hqMdef
  have hqMU' : qM ∈ U' := hsymmT q hqT
  have hqMsrc : qM ∈ (chartAt H z).source := hqMU'.2
  have hφqM : extChartAt I z qM = q := (extChartAt I z).right_inv hqtarget
  have hqMW : qM ∈ W := hKW q (hAK hqA)
  -- ### `q` is not on the inner sphere
  have hq_ne_inner : dist q x₀ ≠ R / 2 := by
    intro hc
    have h1 : V q ≤ V ys := hysmax (by rw [mem_sphere]; exact hc)
    have h2 : hopfBarrier κ x₀ q - c₀ ≤ 1 := by
      have hb1 : hopfBarrier κ x₀ q ≤ 1 := hopfBarrier_le_one hκpos.le x₀ q
      have hb2 : 0 < c₀ := Real.exp_pos _
      linarith
    have h3 : VE q ≤ m - δ + ε := by
      have h4 : ε * (hopfBarrier κ x₀ q - c₀) ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left h2 hεpos.le
      have h5 : V q ≤ m - δ := by rw [hδdef]; linarith
      show V q + ε * (hopfBarrier κ x₀ q - c₀) ≤ m - δ + ε
      linarith
    rw [hεdef] at h3
    linarith
  -- ### `q` is not an interior point of the annulus: elliptic contradiction
  have hq_not_interior : ¬ dist q x₀ < R := by
    intro hqlt
    have hqgt : R / 2 < dist q x₀ := lt_of_le_of_ne hq_ge (Ne.symm hq_ne_inner)
    -- a ball around `q` inside `A`
    set r₀ : ℝ := min (dist q x₀ - R / 2) (R - dist q x₀) with hr₀def
    have hr₀pos : 0 < r₀ := lt_min (by linarith) (by linarith)
    have hballA : ball q r₀ ⊆ A := by
      intro y hy
      rw [mem_ball] at hy
      constructor
      · rw [mem_closedBall]
        have h5 : dist y q < R - dist q x₀ :=
          lt_of_lt_of_le hy (min_le_right _ _)
        calc dist y x₀ ≤ dist y q + dist q x₀ := dist_triangle _ _ _
          _ ≤ R := by linarith
      · intro hc
        rw [mem_ball] at hc
        have h5 : dist q x₀ ≤ dist q y + dist y x₀ := dist_triangle _ _ _
        have h6 : dist q y < dist q x₀ - R / 2 := by
          rw [dist_comm]
          exact lt_of_lt_of_le hy (min_le_left _ _)
        linarith
    -- the perturbation upstairs
    set vM : M → ℝ :=
      fun x' => h' x' + ε * (hopfBarrier κ x₀ (extChartAt I z x') - c₀)
      with hvMdef
    have hvMsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ vM (chartAt H z).source := by
      have hbar : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (hopfBarrier κ x₀) :=
        contMDiff_iff_contDiff.mpr (hopfBarrier_contDiff κ x₀)
      exact (hh'.contMDiffOn).add (ContMDiffOn.mul contMDiffOn_const
        ((hbar.comp_contMDiffOn (contMDiffOn_extChartAt (I := I))).sub
          contMDiffOn_const))
    -- `vM` has a local maximum at `qM`
    have hlocmax : IsLocalMax vM qM := by
      have hcont_φ : ContinuousAt (extChartAt I z) qM :=
        continuousAt_extChartAt' (by rwa [extChartAt_source])
      have hb : ball q r₀ ∈ 𝓝 (extChartAt I z qM) := by
        rw [hφqM]
        exact ball_mem_nhds _ hr₀pos
      filter_upwards [hcont_φ hb,
        (chartAt H z).open_source.mem_nhds hqMsrc] with x' h1 h2
      have hx'src : x' ∈ (extChartAt I z).source := by
        rw [extChartAt_source]; exact h2
      have e1 : vM x' = VE (extChartAt I z x') := by
        show h' x' + _ = h' ((extChartAt I z).symm (extChartAt I z x')) + _
        rw [(extChartAt I z).left_inv hx'src]
      have e2 : vM qM = VE q := by
        show h' qM + ε * (hopfBarrier κ x₀ (extChartAt I z qM) - c₀)
          = h' ((extChartAt I z).symm q) + ε * (hopfBarrier κ x₀ q - c₀)
        rw [hφqM, hqMdef]
      rw [e1, e2]
      exact hqmax (hballA h1)
    -- the Laplacian of `vM` at `qM` is nonpositive …
    have hΔ1 : laplacianAt g g.leviCivitaConnection vM qM ≤ 0 :=
      (laplacianAt_nonpos_of_isLocalMaxOn g g.leviCivitaConnection
        (chartAt H z).open_source hvMsmooth hqMsrc
        (hlocmax.filter_mono nhdsWithin_le_nhds)).2
    -- … but the chart formula makes it positive
    have hΔ2 : 0 < laplacianAt g g.leviCivitaConnection vM qM := by
      rw [laplacianAt_eq_chartLaplaceOp_of_contMDiffOn g
        (chartAt H z).open_source hvMsmooth hqMsrc hqMsrc, hφqM]
      have hev2 : (vM ∘ (extChartAt I z).symm) =ᶠ[𝓝 q] VE := by
        filter_upwards [(isOpen_extChartAt_target (I := I) z).mem_nhds
          hqtarget] with y hy
        show h' ((extChartAt I z).symm y)
            + ε * (hopfBarrier κ x₀ (extChartAt I z ((extChartAt I z).symm y))
                - c₀)
          = V y + ε * (hopfBarrier κ x₀ y - c₀)
        rw [(extChartAt I z).right_inv hy]
        rfl
      rw [chartLaplaceOp_congr g z hev2, hVEdef,
        chartLaplaceOp_add_smul g z (isOpen_extChartAt_target (I := I) z)
          hqtarget hVsmooth (hopfBarrier_contDiff κ x₀) ε c₀]
      have h3 : chartLaplaceOp (I := I) g z V q
          = laplacianAt g g.leviCivitaConnection h' qM := by
        have h4 := laplacianAt_eq_chartLaplaceOp g hh' (α := z) (p := qM)
          hqMsrc
        rw [hφqM, ← hVdef] at h4
        exact h4.symm
      have h5 : 0 ≤ laplacianAt g g.leviCivitaConnection h' qM := by
        have h6 : laplacianAt g g.leviCivitaConnection h' qM
            = laplacianAt g g.leviCivitaConnection h qM :=
          laplacianAt_congr_of_eventuallyEq g _ (by
            filter_upwards [hWopen.mem_nhds hqMW] with x' hx'
            exact hWeq hx')
        rw [h6]
        exact hsub qM hqMU'.1
      have h7 := hκ' q hqA
      have h8 := mul_pos hεpos h7
      rw [h3]
      linarith
    linarith
  -- ### hence `q` is on the outer sphere, where `V q = m`
  have hqR : dist q x₀ = R := by
    rcases lt_or_eq_of_le hq_le with hlt | he
    · exact absurd hlt hq_not_interior
    · exact he
  have hqnorm : ‖q - x₀‖ = R := by rw [← dist_eq_norm]; exact hqR
  have hVEq : VE q = V q := by
    show V q + ε * (hopfBarrier κ x₀ q - c₀) = V q
    rw [hopfBarrier_eq_of_norm_eq hqnorm, ← hc₀def]
    ring
  have hVq : V q = m :=
    le_antisymm (hVle q (hAK hqA)) (by rw [← hVEq]; exact hmq)
  -- ### the manifold Fermat lemma at `qM` kills the first-order term of `V`
  have hh'q : h' qM = m := hVq
  have hlocmax_h' : IsLocalMax h' qM := by
    filter_upwards [hWopen.mem_nhds hqMW] with x' hx'
    rw [hWeq hx', hh'q]
    exact hle x' (hWU hx')
  have hgrad : mfderiv I 𝓘(ℝ, ℝ) h' qM = 0 :=
    mfderiv_eq_zero_of_isLocalMax hh' hlocmax_h'
  have hfderivV : fderiv ℝ V q = 0 := by
    have hsymm_md : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I z).symm q :=
      ((contMDiffOn_extChartAt_symm (I := I) z q hqtarget).contMDiffAt
        (extChartAt_target_mem_nhds' hqtarget)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hh'md : MDifferentiableAt I 𝓘(ℝ, ℝ) h' ((extChartAt I z).symm q) :=
      (hh' ((extChartAt I z).symm q)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hcomp := mfderiv_comp q hh'md hsymm_md
    have hVfd : fderiv ℝ V q
        = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (h' ∘ (extChartAt I z).symm) q :=
      (mfderiv_eq_fderiv (f := V)).symm
    rw [hVfd, hcomp]
    have : mfderiv I 𝓘(ℝ, ℝ) h' ((extChartAt I z).symm q) = 0 := hgrad
    rw [this, ContinuousLinearMap.zero_comp]
  -- ### the radial derivative contradiction
  have hbar_diff : DifferentiableAt ℝ (hopfBarrier κ x₀) q :=
    ((hopfBarrier_contDiff κ x₀).differentiable (by simp)).differentiableAt
  have hV_diff : DifferentiableAt ℝ V q :=
    ((hVsmooth.contDiffAt ((isOpen_extChartAt_target (I := I) z).mem_nhds
      hqtarget)).differentiableAt (by simp))
  have hVE_deriv : HasFDerivAt VE (ε • fderiv ℝ (hopfBarrier κ x₀) q) q := by
    have h8 : HasFDerivAt VE
        (fderiv ℝ V q + ε • fderiv ℝ (hopfBarrier κ x₀) q) q :=
      hV_diff.hasFDerivAt.add
        ((hbar_diff.hasFDerivAt.sub_const c₀).const_mul ε)
    rwa [hfderivV, zero_add] at h8
  have hseg : segment ℝ q (q + (1 / 2 : ℝ) • (x₀ - q)) ⊆ A := by
    rintro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
    have hwx₀ : q + t • (q + (1 / 2 : ℝ) • (x₀ - q) - q) - x₀
        = (1 - t / 2) • (q - x₀) := by module
    have hnorm : dist (q + t • (q + (1 / 2 : ℝ) • (x₀ - q) - q)) x₀
        = (1 - t / 2) * R := by
      rw [dist_eq_norm, hwx₀, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), ← dist_eq_norm, hqR]
    constructor
    · rw [mem_closedBall, hnorm]
      nlinarith
    · intro hc
      rw [mem_ball, hnorm] at hc
      nlinarith
  have hcone : (1 / 2 : ℝ) • (x₀ - q) ∈ posTangentConeAt A q :=
    mem_posTangentConeAt_of_segment_subset hseg
  have hnonpos :=
    (hqmax.localize).hasFDerivWithinAt_nonpos hVE_deriv.hasFDerivWithinAt hcone
  have hinner : ⟪q - x₀, x₀ - q⟫_ℝ = -(R ^ 2) := by
    rw [show x₀ - q = -(q - x₀) from (neg_sub _ _).symm, inner_neg_right,
      real_inner_self_eq_norm_sq, hqnorm]
  have hcalc : (ε • fderiv ℝ (hopfBarrier κ x₀) q) ((1 / 2 : ℝ) • (x₀ - q))
      = ε * (1 / 2) * (-2 * κ * Real.exp (-κ * R ^ 2) * -(R ^ 2)) := by
    rw [ContinuousLinearMap.smul_apply,
      (fderiv ℝ (hopfBarrier κ x₀) q).map_smul, fderiv_hopfBarrier,
      hinner]
    have hqx : ‖q - x₀‖ ^ 2 = R ^ 2 := by rw [hqnorm]
    rw [hqx]
    simp only [smul_eq_mul]
    ring
  rw [hcalc] at hnonpos
  have hfinal : 0 < ε * (1 / 2) * (-2 * κ * Real.exp (-κ * R ^ 2) * -(R ^ 2)) := by
    have hrew : ε * (1 / 2) * (-2 * κ * Real.exp (-κ * R ^ 2) * -(R ^ 2))
        = ε * κ * Real.exp (-κ * R ^ 2) * R ^ 2 := by ring
    rw [hrew]
    exact mul_pos (mul_pos (mul_pos hεpos hκpos) (Real.exp_pos _))
      (pow_pos hRpos 2)
  linarith

/-- **Math.** **The Hopf strong maximum principle** (E. Hopf; Morgan–Tian
Ch. 2, Lemma 2.9). Let `(M,g)` be a Riemannian manifold, `U ⊆ M` a connected
open set, and `h` a smooth function on `U` with `Δh ≥ 0` at every point of
`U`. If `h` attains its supremum over `U` at a point `z ∈ U`, then `h` is
identically equal to `h z` on `U`. Blueprint: `lem:hopf-strong-maximum`. -/
theorem hopf_strong_maximum (g : RiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) {h : M → ℝ}
    (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U)
    (hsub : ∀ x ∈ U, 0 ≤ laplacianAt g g.leviCivitaConnection h x)
    {z : M} (hz : z ∈ U) (hmax : ∀ x ∈ U, h x ≤ h z) :
    ∀ x ∈ U, h x = h z := by
  classical
  set m := h z with hm
  -- the union of the open patches where `h ≡ m`, over all maximum points
  set u : Set M := ⋃ (z' : {x // x ∈ U ∧ h x = m}),
    Classical.choose (hopf_eqOn_max_near g hU hh hsub hmax z'.2.1 z'.2.2)
    with hu
  have hu_spec : ∀ z' : {x // x ∈ U ∧ h x = m},
      IsOpen (Classical.choose
          (hopf_eqOn_max_near g hU hh hsub hmax z'.2.1 z'.2.2)) ∧
        z'.1 ∈ Classical.choose
          (hopf_eqOn_max_near g hU hh hsub hmax z'.2.1 z'.2.2) ∧
        Classical.choose
          (hopf_eqOn_max_near g hU hh hsub hmax z'.2.1 z'.2.2) ⊆ U ∧
        ∀ x ∈ Classical.choose
          (hopf_eqOn_max_near g hU hh hsub hmax z'.2.1 z'.2.2), h x = m := by
    intro z'
    obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec
      (hopf_eqOn_max_near g hU hh hsub hmax z'.2.1 z'.2.2)
    exact ⟨h1, h2, h3, h4⟩
  have huopen : IsOpen u := isOpen_iUnion fun z' => (hu_spec z').1
  have hum : ∀ x ∈ u, h x = m := by
    intro x hx
    obtain ⟨s, ⟨z', rfl⟩, hz'⟩ := hx
    exact (hu_spec z').2.2.2 x hz'
  have huU : u ⊆ U := by
    intro x hx
    obtain ⟨s, ⟨z', rfl⟩, hz'⟩ := hx
    exact (hu_spec z').2.2.1 hz'
  have hcont : ContinuousOn h U := hh.continuousOn
  have hzu : z ∈ u :=
    mem_iUnion.mpr ⟨⟨z, hz, rfl⟩, (hu_spec ⟨z, hz, rfl⟩).2.1⟩
  -- `u` is relatively closed in `U`: limit points in `U` satisfy `h = m` by
  -- continuity, hence generate their own patch
  have hclosure : closure u ∩ U ⊆ u := by
    rintro x ⟨hxcl, hxU⟩
    haveI hne : (𝓝[u] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hxcl
    have htend : Tendsto h (𝓝[u] x) (𝓝 (h x)) :=
      ((hcont x hxU).mono huU).tendsto
    have htend' : Tendsto h (𝓝[u] x) (𝓝 m) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_mem_nhdsWithin] with y hy
      exact (hum y hy).symm
    have hxm : h x = m := tendsto_nhds_unique htend htend'
    exact mem_iUnion.mpr ⟨⟨x, hxU, hxm⟩, (hu_spec ⟨x, hxU, hxm⟩).2.1⟩
  have hsubset : U ⊆ u :=
    hUc.subset_of_closure_inter_subset huopen ⟨z, hz, hzu⟩ hclosure
  exact fun x hx => hum x (hsubset hx)

end MorganTianLib

end
