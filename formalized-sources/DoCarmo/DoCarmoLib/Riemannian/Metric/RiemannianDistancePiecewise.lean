import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3
import DoCarmoLib.Riemannian.Metric.SmoothPathApproximation
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Piecewise path presentation of the Riemannian distance

do Carmo defines distance using piecewise differentiable curves.  By the
chapter-zero convention, each differentiable piece is `C^∞`; Mathlib's
`riemannianEDist` uses `C^1` paths.  This file supplies the comparison between
the explicit finite-partition presentation and Mathlib's distance.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold Topology ENNReal

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- **Math.** The infimum of lengths of piecewise-`C^∞` curves joining two
points, in do Carmo's explicit-partition presentation.  The partition is
recorded directly rather than through a bundled curve class. -/
noncomputable def piecewiseRiemannianEDist (g : RiemannianMetric I M)
    (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  ⨅ (γ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ) (_ : 0 < n)
      (_ : ∀ i < n, τ i ≤ τ (i + 1))
      (_ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (τ i) (τ (i + 1))))
      (_ : γ (τ 0) = x) (_ : γ (τ n) = y),
    Manifold.pathELength I γ (τ 0) (τ n)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
/-- **Math.** The Riemannian distance is below the length of every piecewise-`C^1`
partition. -/
theorem riemannianEDist_le_pathELength_piecewise_partition
    (g : RiemannianMetric I M) {γ : ℝ → M} {n : ℕ} {τ : ℕ → ℝ}
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (τ i) (τ (i + 1))))
    {s t : ℝ} (hs : τ 0 ≤ s) (hst : s ≤ t) (ht : t ≤ τ n) :
    letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I (γ s) (γ t) ≤ Manifold.pathELength I γ s t := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  have key : ∀ m : ℕ, m ≤ n → ∀ s t : ℝ, τ 0 ≤ s → s ≤ t → t ≤ τ m →
      Manifold.riemannianEDist I (γ s) (γ t) ≤ Manifold.pathELength I γ s t := by
    intro m
    induction m with
    | zero =>
        intro _ s t hs hst ht
        have hts : t = s := le_antisymm (ht.trans hs) hst
        subst hts
        rw [Manifold.riemannianEDist_self]
        exact bot_le
    | succ m ih =>
        intro hmn s t hs hst ht
        have hmn' : m < n := hmn
        rcases le_total t (τ m) with htm | htm
        · exact ih (le_of_lt hmn') s t hs hst htm
        rcases le_total (τ m) s with hsm | hsm
        · exact Manifold.riemannianEDist_le_pathELength
            ((hγ m hmn').mono (Icc_subset_Icc hsm ht)) rfl rfl hst
        · calc
            Manifold.riemannianEDist I (γ s) (γ t)
                ≤ Manifold.riemannianEDist I (γ s) (γ (τ m)) +
                    Manifold.riemannianEDist I (γ (τ m)) (γ t) :=
              Manifold.riemannianEDist_triangle
            _ ≤ Manifold.pathELength I γ s (τ m) +
                Manifold.pathELength I γ (τ m) t := by
              gcongr
              · exact ih (le_of_lt hmn') s (τ m) hs hsm le_rfl
              · exact Manifold.riemannianEDist_le_pathELength
                  ((hγ m hmn').mono (Icc_subset_Icc le_rfl ht)) rfl rfl htm
            _ = Manifold.pathELength I γ s t :=
              Manifold.pathELength_add hsm htm
  exact key n le_rfl s t hs hst ht

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A minimizing geodesic segment realizes Mathlib's Riemannian
extended distance between its endpoints. -/
theorem Geodesic.IsMinimizingGeodesicSegment.riemannianEDist_eq_pathELength
    (g : RiemannianMetric I M) {γ : ℝ → M}
    (hmin : Geodesic.IsMinimizingGeodesicSegment (I := I) g γ 0 1)
    (hγ : Geodesic.IsPiecewiseDifferentiableCurve (I := I) γ 0 1) :
    letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I (γ 0) (γ 1) =
      Manifold.pathELength I γ 0 1 := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  apply le_antisymm
  · rcases hγ.2 with ⟨n, τ, _hn, hτ0, hτn, _hτ, hpieces⟩
    simpa [hτ0, hτn] using
      (riemannianEDist_le_pathELength_piecewise_partition g hpieces
        (by simp [hτ0]) zero_le_one (by simp [hτn]))
  · by_contra h
    have hlt : Manifold.riemannianEDist I (γ 0) (γ 1) <
        Manifold.pathELength I γ 0 1 := lt_of_not_ge h
    obtain ⟨σ, hσ0, hσ1, hσ, hσlt⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    have hpw : Geodesic.IsPiecewiseDifferentiableCurve (I := I) σ 0 1 := by
      refine ⟨hσ.continuousOn, ⟨1, (fun i : ℕ => (i : ℝ)), Nat.zero_lt_one,
        by norm_num, by norm_num, ?_, ?_⟩⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        norm_num
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simpa using hσ
    exact (not_lt_of_ge (hmin.2.2 σ hpw hσ0 hσ1)) hσlt

/-- **Math.** A strict gap above an extended nonnegative length contains a positive
multiplicative thickening of that length. -/
private theorem exists_pos_ofReal_one_add_mul_lt {L R : ℝ≥0∞} (h : L < R) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ENNReal.ofReal (1 + epsilon) * L < R := by
  by_cases hL0 : L = 0
  · exact ⟨1, one_pos, by simpa [hL0] using h⟩
  have hLtop : L ≠ ⊤ := ne_top_of_lt h
  by_cases hRtop : R = ⊤
  · refine ⟨1, one_pos, ?_⟩
    rw [hRtop]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hLtop)
  have hreal : L.toReal < R.toReal :=
    (ENNReal.toReal_lt_toReal hLtop hRtop).2 h
  have hLpos : 0 < L.toReal := ENNReal.toReal_pos hL0 hLtop
  let epsilon : ℝ := (R.toReal / L.toReal - 1) / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    rw [div_pos_iff]
    exact Or.inl ⟨by rw [sub_pos, one_lt_div hLpos]; exact hreal, by norm_num⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  have hprodtop : ENNReal.ofReal (1 + epsilon) * L ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hLtop))
  rw [← ENNReal.toReal_lt_toReal hprodtop hRtop]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  dsimp [epsilon]
  field_simp
  nlinarith

/-- **Math.** The infimum over explicit finite partitions whose pieces are
`C^∞` agrees with Mathlib's infimum over `C^1` paths. -/
theorem piecewiseRiemannianEDist_eq_riemannianEDist
    (g : RiemannianMetric I M) (x y : M) :
    letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨g.toRiemannianMetric⟩
    piecewiseRiemannianEDist (I := I) g x y = Manifold.riemannianEDist I x y := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  apply le_antisymm
  · by_contra h
    have hlt : Manifold.riemannianEDist I x y <
        piecewiseRiemannianEDist (I := I) g x y := lt_of_not_ge h
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    obtain ⟨epsilon, hepsilon, hgap⟩ := exists_pos_ofReal_one_add_mul_lt hlen
    obtain ⟨sigma, n, tau, hn, htau, hsmooth, hsigma0, hsigma1, hsigmaLen⟩ :=
      exists_piecewiseSmooth_pathELength_le (I := I) g hγ hepsilon
    have hcandidate : piecewiseRiemannianEDist (I := I) g x y ≤
        Manifold.pathELength I sigma (tau 0) (tau n) := by
      unfold piecewiseRiemannianEDist
      refine iInf_le_of_le sigma ?_
      refine iInf_le_of_le n ?_
      refine iInf_le_of_le tau ?_
      refine iInf_le_of_le hn ?_
      refine iInf_le_of_le htau ?_
      refine iInf_le_of_le hsmooth ?_
      refine iInf_le_of_le (hsigma0.trans hγ0) ?_
      exact iInf_le_of_le (hsigma1.trans hγ1) le_rfl
    exact (not_lt_of_ge hcandidate) (hsigmaLen.trans_lt hgap)
  · unfold piecewiseRiemannianEDist
    refine le_iInf fun γ => ?_
    refine le_iInf fun n => ?_
    refine le_iInf fun τ => ?_
    refine le_iInf fun _hn => ?_
    refine le_iInf fun hτ => ?_
    refine le_iInf fun hpieces => ?_
    refine le_iInf fun h0 => ?_
    refine le_iInf fun h1 => ?_
    have hτ0n : τ 0 ≤ τ n :=
      Riemannian.Exponential.partition_le hτ (Nat.zero_le n) le_rfl
    simpa [h0, h1] using
      (riemannianEDist_le_pathELength_piecewise_partition g
        (s := τ 0) (t := τ n)
        (fun i hi => (hpieces i hi).of_le (by norm_num))
        le_rfl hτ0n le_rfl)

/-- **Math.** A minimizing geodesic segment on `[0,1]` realizes the
piecewise Riemannian distance between its endpoints (do Carmo Ch. 7,
the observation following Proposition 2.5). -/
theorem Geodesic.IsMinimizingGeodesicSegment.piecewiseRiemannianEDist_eq_pathELength
    (g : RiemannianMetric I M) {γ : ℝ → M}
    (hmin : Geodesic.IsMinimizingGeodesicSegment (I := I) g γ 0 1)
    (hγ : Geodesic.IsPiecewiseDifferentiableCurve (I := I) γ 0 1) :
    letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨g.toRiemannianMetric⟩
    piecewiseRiemannianEDist (I := I) g (γ 0) (γ 1) =
      Manifold.pathELength I γ 0 1 := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  rw [piecewiseRiemannianEDist_eq_riemannianEDist]
  exact hmin.riemannianEDist_eq_pathELength g hγ

end Riemannian
