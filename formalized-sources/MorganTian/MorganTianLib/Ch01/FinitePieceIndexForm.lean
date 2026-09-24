import MorganTianLib.Ch01.FinitePieceVariation
import MorganTianLib.Ch01.MinimalGeodesicNoConjugate

/-!
# Nonnegative index form for finitely many coefficient pieces

For a minimizing geodesic, the sum of the index forms of finitely many
smooth fields matching at junctions is nonnegative. The proof constructs an
actual curve variation, compares its energy with the squared endpoint
distance, and applies the second derivative test.
-/

open Set Filter Riemannian Riemannian.Geodesic Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [CompleteSpace E] [T2Space (TangentBundle I M)]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** Nonnegativity of the sum of the index forms of any finite number
of smooth matching pieces with zero outer endpoints, along a minimizing
geodesic. The chart partition may be arbitrarily fine. -/
theorem sum_indexForm_nonneg_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {W : ℕ → ℝ → 𝔼} {Wg : ℝ → 𝔼}
    {N : ℕ} {τ : ℕ → ℝ} {β : ℕ → M} {r : ℝ}
    (ha : a < 0) (hb : 1 < b)
    (hN : 0 < N) (hr : 0 < r) (hmono : ∀ i, τ i < τ (i + 1))
    (hτ0 : τ 0 = 0) (hτN : τ N = 1) (_hτmem : ∀ i ≤ N, τ i ∈ Icc (0 : ℝ) 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    (hW : ∀ i < N, ContDiffOn ℝ 3 (W i) (Ioo a b))
    (hmatch : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), Wg t = W i t)
    (hW0 : Wg 0 = 0) (hW1 : Wg 1 = 0)
    (hslack : ∀ i < N, ∀ t ∈ Ioo (τ i - r) (τ (i + 1) + r),
      t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source ∧
        extChartAt I (β i) (γ t) ∈ interior (extChartAt I (β i)).target) :
    0 ≤ ∑ i ∈ Finset.range N, indexForm (frameCurvOp (I := I) g γ e)
      (τ i) (τ (i + 1)) (W i) (deriv (W i)) (W i) (deriv (W i)) := by
  classical
  obtain ⟨u, ρ, ε, hρ, hε, hερ, hCD, hbox, hline, hjL, hjR, hvar, hsrcL, hsrcR, hEnl⟩ :=
    exists_finitePieceVariationData (I := I) g hg hN hr hmono hgeo hγc hPar hW hmatch hslack
  have hab : a < b := ha.trans (by linarith)
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Ioo a b := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hsm : StrictMono τ := strictMono_nat_of_lt_succ hmono
  -- the enlarged data, with the *smaller* radius `ε ≤ ρ`, which is what the piece lemmas want
  have hboxε : ∀ i < N, ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ε) (τ (i + 1) + ε),
      u i p ∈ (extChartAt I (β i)).target := fun i hi p hp =>
    hbox i hi p ⟨hp.1, Ioo_subset_Ioo (by linarith) (by linarith) hp.2⟩
  have hEnlε : ∀ i < N, ∀ t ∈ Icc (τ i - ε) (τ (i + 1) + ε),
      t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source := fun i hi t ht =>
    hEnl i hi t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the piece energies, their first derivatives, and their second derivatives
  set f : ℕ → ℝ → ℝ := fun i s => ∫ t in (τ i)..(τ (i + 1)),
    energyDensity (chartMetricBilin (I := I) g (β i)) (u i) ((0 : ℝ), (1 : ℝ)) (s, t) with hfdef
  set f' : ℕ → ℝ → ℝ := fun i s => ∫ t in (τ i)..(τ (i + 1)),
    deriv (fun r =>
      energyDensity (chartMetricBilin (I := I) g (β i)) (u i) ((0 : ℝ), (1 : ℝ)) (r, t)) s
    with hf'def
  set L : ℕ → ℝ := fun i => indexForm (frameCurvOp (I := I) g γ e) (τ i) (τ (i + 1))
    (W i) (deriv (W i))
    (W i) (deriv (W i)) with hLdef
  -- ### the first derivative of each piece energy, on a whole neighbourhood of `0`
  have hd : ∀ i < N, ∀ s ∈ Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s := fun i hi s hs =>
    hasDerivAt_pieceEnergy_chartMetricBilin (I := I) g (hmono i).le hε (hCD i hi)
      (hboxε i hi) hs
  -- ### the second derivative of each piece energy IS the index form of its coefficients
  have hd2 : ∀ i < N, HasDerivAt (f' i) (L i) 0 := by
    intro i hi
    have hWd : ∀ t ∈ Ioo (τ i - ε) (τ (i + 1) + ε),
        DifferentiableAt ℝ (W i) t := by
      intro t ht
      have htab : t ∈ Ioo a b := (hEnlε i hi t (Ioo_subset_Icc_self ht)).1
      exact ((hW i hi).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds htab)
    have hsrc₀ : γ (τ i) ∈ (chartAt H (β i)).source :=
      (hEnlε i hi (τ i) ⟨by linarith, by linarith [hmono i]⟩).2
    have hsrc₁ : γ (τ (i + 1)) ∈ (chartAt H (β i)).source :=
      (hEnlε i hi (τ (i + 1)) ⟨by linarith [hmono i], by linarith⟩).2
    have hj₀ := covDerivAlong_fst_eq_zero_of_globalGeodesic_junction (I := I) (α := β i)
      (u := u i) g hg ((hCD i hi).of_le (by norm_num)) hsrc₀ (hjL i hi)
    have hj₁ := covDerivAlong_fst_eq_zero_of_globalGeodesic_junction (I := I) (α := β i)
      (u := u i) g hg ((hCD i hi).of_le (by norm_num)) hsrc₁ (hjR i hi)
    have hkey := hasDerivAt_deriv_pieceEnergy_indexIntegrand (I := I) g (α := β i)
      (u := u i) (W := W i) hgeo hγc hPar horth (hmono i) hε
      (fun t ht => ⟨Ioo_subset_Icc_self (hEnlε i hi t ht).1, (hEnlε i hi t ht).2⟩)
      hWd (hCD i hi) (hboxε i hi) (hline i hi) (hvar i hi) hj₀ hj₁
    -- `deriv (f i)` and `f' i` agree on a neighbourhood of `0`
    refine hkey.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by linarith : (-ε : ℝ) < 0) hε] with s hs
    exact ((hd i hi s hs).deriv).symm
  -- ### the varied curve has fixed endpoints, because the field vanishes there
  have hV0 : (frameFieldOf (I := I) g γ e Wg (τ 0) : E) = 0 := by
    refine frameFieldOf_eq_zero (I := I) ?_
    rw [hτ0, hW0]
  have hV1 : (frameFieldOf (I := I) g γ e Wg (τ N) : E) = 0 := by
    refine frameFieldOf_eq_zero (I := I) ?_
    rw [hτN, hW1]
  have hgg0 : ∀ s : ℝ, globalGeodesic (I := I) g hg (γ (τ 0))
      ((frameFieldOf (I := I) g γ e Wg (τ 0) : E)) s = γ (τ 0) := by
    have hconst : globalGeodesic (I := I) g hg (γ (τ 0))
        ((frameFieldOf (I := I) g γ e Wg (τ 0) : E)) = fun _ => γ (τ 0) := by
      rw [show ((frameFieldOf (I := I) g γ e Wg (τ 0) : E)) = 0 from hV0]
      exact globalGeodesic_zero_velocity (I := I) g hg (γ (τ 0))
    intro s; rw [hconst]
  have hggN : ∀ s : ℝ, globalGeodesic (I := I) g hg (γ (τ N))
      ((frameFieldOf (I := I) g γ e Wg (τ N) : E)) s = γ (τ N) := by
    have hconst : globalGeodesic (I := I) g hg (γ (τ N))
        ((frameFieldOf (I := I) g γ e Wg (τ N) : E)) = fun _ => γ (τ N) := by
      rw [show ((frameFieldOf (I := I) g γ e Wg (τ N) : E)) = 0 from hV1]
      exact globalGeodesic_zero_velocity (I := I) g hg (γ (τ N))
    intro s; rw [hconst]
  -- ### the finitely many junction neighbourhoods, intersected
  have hEv : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i ∈ Finset.range N,
      (u i (s, τ i) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e Wg (τ i) : E)) s)) ∧
      (u i (s, τ (i + 1)) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e Wg (τ (i + 1)) : E)) s)) ∧
      (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e Wg (τ i) : E)) s
          ∈ (chartAt H (β i)).source) ∧
      (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e Wg (τ (i + 1)) : E)) s
          ∈ (chartAt H (β i)).source) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact (hjL i hi').and ((hjR i hi').and ((hsrcL i hi').and (hsrcR i hi')))
  -- ### the chart families are smooth in time, and stay in the chart targets
  have hu1 : ∀ (s : ℝ), ∀ i < N, ContDiff ℝ 1 (fun t => u i (s, t)) := fun s i hi =>
    ((hCD i hi).comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  have hmemT : ∀ s ∈ Ioo (-ε) ε, ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
      u i (s, t) ∈ (extChartAt I (β i)).target := fun s hs i hi t ht =>
    hboxε i hi (s, t) ⟨hs, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  -- ### `2 𝓔 (s)` is the energy of the glued broken path, hence `≥ d(γ 0, γ 1)²`
  have hE0mem : γ (τ 0) ∈ (chartAt H (β 0)).source :=
    (hEnlε 0 hN (τ 0) ⟨by linarith, by linarith [hmono 0]⟩).2
  have hm : (N - 1) + 1 = N := Nat.succ_pred_eq_of_pos hN
  have hmN : N - 1 < N := by omega
  have hENmem : γ (τ N) ∈ (chartAt H (β (N - 1))).source := by
    have := (hEnlε (N - 1) hmN (τ ((N - 1) + 1))
      ⟨by linarith [hmono (N - 1)], by linarith⟩).2
    rwa [hm] at this
  have hEnergy : ∀ s ∈ Ioo (-ε) ε, (∀ i ∈ Finset.range N,
      (u i (s, τ i) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e Wg (τ i) : E)) s)) ∧
      (u i (s, τ (i + 1)) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e Wg (τ (i + 1)) : E)) s)) ∧
      (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e Wg (τ i) : E)) s
          ∈ (chartAt H (β i)).source) ∧
      (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e Wg (τ (i + 1)) : E)) s
          ∈ (chartAt H (β i)).source)) →
      dist (γ 0) (γ 1) ^ 2 ≤ 2 * ∑ i ∈ Finset.range N, f i s := by
    intro s hsε hs
    -- the two chart readings at a junction are the same manifold point
    have hjuncS : ∀ i, i + 1 < N →
        (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
          = (extChartAt I (β i)).symm (u i (s, τ (i + 1))) := by
      intro i hi1
      obtain ⟨-, h2, -, h4⟩ := hs i (Finset.mem_range.mpr (by omega))
      obtain ⟨h1', -, h3', -⟩ := hs (i + 1) (Finset.mem_range.mpr hi1)
      rw [h1', h2, (extChartAt I (β (i + 1))).left_inv (by rwa [extChartAt_source]),
        (extChartAt I (β i)).left_inv (by rwa [extChartAt_source])]
    -- the endpoints of the glued path are those of `γ`
    have h01 : (0 : ℝ) < τ 1 := by rw [← hτ0]; exact hmono 0
    have hE0 : brokenPath (I := I) β u τ N s 0 = γ 0 := by
      rw [brokenPath_eq_of_mem_Icc (I := I) hmono hN hjuncS hN ⟨hτ0.le, h01.le⟩]
      obtain ⟨h1, -, -, -⟩ := hs 0 (Finset.mem_range.mpr hN)
      rw [← hτ0, h1, hgg0 s]
      exact (extChartAt I (β 0)).left_inv (by rw [extChartAt_source]; exact hE0mem)
    have hE1 : brokenPath (I := I) β u τ N s 1 = γ 1 := by
      have hτle : τ (N - 1) ≤ (1 : ℝ) := by
        have := hsm.monotone (show N - 1 ≤ N by omega)
        rw [hτN] at this; exact this
      rw [brokenPath_eq_of_mem_Icc (I := I) hmono hN hjuncS hmN
        (by rw [hm, hτN]; exact ⟨hτle, le_rfl⟩)]
      obtain ⟨-, h2, -, -⟩ := hs (N - 1) (Finset.mem_range.mpr hmN)
      rw [hm] at h2
      rw [← hτN, h2, hggN s]
      exact (extChartAt I (β (N - 1))).left_inv (by rw [extChartAt_source]; exact hENmem)
    have hkey := sq_dist_le_sum_chartFamily_energy (I := I) g hg hmono hN hτ0 hτN hjuncS
      (fun i hi t ht => hmemT s hsε i hi t ht) (fun i hi => hu1 s i hi)
    rw [hE0, hE1] at hkey
    have hRHS : ∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
          chartMetricInner (I := I) g (β i) (u i (s, t))
            (deriv (fun r => u i (s, r)) t) (deriv (fun r => u i (s, r)) t)
        = 2 * ∑ i ∈ Finset.range N, f i s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      exact (two_mul_pieceEnergy_eq_chartMetricInner (I := I) g (β i)
        ((hCD i (Finset.mem_range.mp hi)).differentiable (by norm_num)) s
        (τ i) (τ (i + 1))).symm
    rwa [hRHS] at hkey
  -- ### at `s = 0` the energy of the (unvaried) minimizing geodesic is exactly `d²`
  have hZero : 2 * ∑ i ∈ Finset.range N, f i 0 = dist (γ 0) (γ 1) ^ 2 := by
    have hRHS0 : 2 * ∑ i ∈ Finset.range N, f i 0
        = ∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
            chartMetricInner (I := I) g (β i) (extChartAt I (β i) (γ t))
              (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
              (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [two_mul_pieceEnergy_eq_chartMetricInner (I := I) g (β i)
        ((hCD i hi').differentiable (by norm_num)) 0 (τ i) (τ (i + 1))]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (hmono i).le] at ht
      have heq : EqOn (fun r => extChartAt I (β i) (γ r)) (fun r => u i ((0 : ℝ), r))
          (Icc (τ i) (τ (i + 1))) := fun r hr => ((hline i hi' r hr).self_of_nhds).symm
      have heq' : extChartAt I (β i) (γ t) = u i ((0 : ℝ), t) := heq ht
      have hdw : derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t
          = deriv (fun r => u i ((0 : ℝ), r)) t :=
        derivWithin_eq_deriv_of_eqOn_Icc (hmono i) heq ht
          (((hu1 0 i hi').differentiable (by norm_num)).differentiableAt)
      rw [hdw, heq']
    rw [hRHS0]
    exact sum_chart_energy_eq_sq_dist_of_minimizing (I := I) g hg
      (hgeo.mono Ioo_subset_Icc_self) isOpen_Ioo isPreconnected_Ioo
      (fun t ht => (hγc t (Ioo_subset_Icc_self ht)).continuousWithinAt) hIcc01
      (fun i _ => (hmono i).le) hτ0 hτN
      (fun i hi t ht => (hEnl i hi t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2) hmin
  -- ### hence `s = 0` is a local minimum of the total energy
  have hLocMin : IsLocalMin (fun s => ∑ i ∈ Finset.range N, f i s) 0 := by
    filter_upwards [hEv, Ioo_mem_nhds (by linarith : (-ε : ℝ) < 0) hε] with s hs hsε
    have h1 := hEnergy s hsε hs
    linarith
  -- ### the second-derivative test
  have hnn : 0 ≤ ∑ i ∈ Finset.range N, L i := by
    rw [← deriv_deriv_sum_eq hε hd hd2]
    exact deriv_deriv_nonneg_of_isLocalMin hLocMin (continuousAt_sum hε hd)
  exact hnn

end MorganTianLib
