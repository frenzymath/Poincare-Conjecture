import PetersenLib.Ch05.MetricTopology
import PetersenLib.Ch05.DistanceSegments
import OpenGALib.Riemannian.Geodesic.HopfRinow.CurveReadback
import OpenGALib.Riemannian.Metric.RiemannianDistance

/-!
# Petersen Ch. 5 — the length bridge `pathELength = ofReal · curveLength`

Reusable infrastructure connecting Petersen's native metric layer (§5.3:
`curveLength`, `riemannianDistance`, all defined by integrating the intrinsic
speed `√(g_{γt}(ċ, ċ))` of piecewise-`C^∞` curves) with the mathlib Riemannian
distance `Manifold.riemannianEDist` (the `ℝ≥0∞`-valued infimum of
`Manifold.pathELength` over `C¹` paths).  The vendored do Carmo Hopf–Rinow /
exponential-map cone in `PetersenLib/Vendored/OpenGA/` speaks entirely in
`riemannianEDist`; this file supplies the one-directional comparison that lets
those results certify Petersen segments and lower distance bounds.

The key facts, under the tangent `RiemannianBundle` carried by `g`:

* `enorm_mfderiv_eq_ofReal_sqrt_curveSpeedSq` — the fibre enorm of the intrinsic
  velocity is `√(curveSpeedSq g γ t)`: the pointwise heart of the bridge.
* `pathELength_eq_ofReal_curveLength` — for a `C^∞` curve on `[a, b]`,
  `pathELength I γ a b = ofReal (curveLength g γ a b)`.
* `riemannianEDist_le_ofReal_curveLength_of_isPiecewiseSmoothCurve` — a
  piecewise-`C^∞` curve `γ : [a,b] → M` is a `riemannianEDist`-competitor:
  `riemannianEDist I (γ a) (γ b) ≤ ofReal (curveLength g γ a b)`.
* `riemannianEDist_le_ofReal_riemannianDistance` — **the (≤) half of the bridge**,
  `riemannianEDist I p q ≤ ofReal (riemannianDistance g p q)` on a connected
  manifold.  Combined with the cone's `edist p (exp_p v) = ofReal |v|_g` this
  gives the substantive **lower** distance bound `|v|_g ≤ d(p, exp_p v)` that
  drives "short geodesics are segments" (Thm 5.5.4) and "segments exist"
  (Cor 5.7.2) — without the research-level smooth-approximation-of-paths that
  the reverse (≥) half of the bridge requires.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** Under the tangent `RiemannianBundle` of `g`, the fibre enorm of the
intrinsic velocity `γ'(t)` of a curve differentiable at `t` is the square root of
Petersen's squared speed: `‖γ'(t)‖ₑ = √(g_{γt}(ċ, ċ)) = √(curveSpeedSq g γ t)`.
This is the pointwise link between the mathlib path-length integrand
`‖mfderiv γ t 1‖ₑ` and the Petersen length integrand. -/
theorem enorm_mfderiv_eq_ofReal_sqrt_curveSpeedSq (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (curveSpeedSq (I := I) g γ t)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [enorm_tangent_eq_sqrt_metricInner (I := I) g (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1),
    curveSpeedSq_eq_metricInner_velocity (I := I) g hγ]
  rfl

/-- **Math.** **The length bridge for a `C^∞` curve.** For a curve `γ` that is
`C^∞` on `[a, b]` (`a ≤ b`), the mathlib path length equals the Petersen curve
length up to `ENNReal.ofReal`:
`Manifold.pathELength I γ a b = ofReal (curveLength g γ a b)`.
Both are the integral of the intrinsic speed `√(curveSpeedSq g γ t)`; the mathlib
side is a lower `ℝ≥0∞`-integral of the enorm, converted to `ofReal` of the
Bochner integral using integrability and nonnegativity of the speed. -/
theorem pathELength_eq_ofReal_curveLength (g : RiemannianMetric I M) {γ : ℝ → M}
    {a b : ℝ} (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b)) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I γ a b
      = ENNReal.ofReal (curveLength (I := I) g γ a b) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [Manifold.pathELength_self, curveLength_def]
  -- integrability of the speed on the interior
  have hint : IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      MeasureTheory.volume a b :=
    ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g hab hγ
  have hintOn : IntegrableOn (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      (Ioo a b) :=
    (hint.1).mono_set Ioo_subset_Ioc_self
  -- pointwise identification of the integrand on the interior
  have hpt : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (curveSpeedSq (I := I) g γ t)) := by
    intro t ht
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by norm_num)
    exact enorm_mfderiv_eq_ofReal_sqrt_curveSpeedSq (I := I) g hmd
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    setLIntegral_congr_fun measurableSet_Ioo hpt,
    ← ofReal_integral_eq_lintegral_ofReal hintOn
      (ae_of_all _ fun t => Real.sqrt_nonneg _),
    curveLength_def, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- **Math.** **A piecewise-`C^∞` curve is a `riemannianEDist` competitor.**  If
`γ` is piecewise `C^∞` on `[a, b]` then
`riemannianEDist I (γ a) (γ b) ≤ ofReal (curveLength g γ a b)`: telescoping the
mathlib triangle inequality over the partition, each `C^∞` piece is a single
`C¹` path with `pathELength = ofReal (curveLength · piece)`, and the Petersen
lengths add. -/
theorem riemannianEDist_le_ofReal_curveLength_of_isPiecewiseSmoothCurve
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I (γ a) (γ b)
      ≤ ENNReal.ofReal (curveLength (I := I) g γ a b) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hγint := hγ.intervalIntegrable_sqrt_curveSpeedSq g
  obtain ⟨-, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  subst hu0; subst hun
  -- accumulate over the partition prefix `[u 0, u k]`
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      Manifold.riemannianEDist I (γ (u 0)) (γ (u ⟨k, hk⟩))
        ≤ ENNReal.ofReal (curveLength (I := I) g γ (u 0) (u ⟨k, hk⟩)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, curveLength_self, Manifold.riemannianEDist_self]
      simp
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hk1 : k < n + 1 := by omega
      have hcast : (⟨k, hk1⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).castSucc := rfl
      have hsucc : (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).succ := rfl
      have hle_prefix : u 0 ≤ u ⟨k, hk1⟩ := hmono (Fin.zero_le _)
      have hle_piece : u ⟨k, hk1⟩ ≤ u ⟨k + 1, hk⟩ := by
        rw [hcast, hsucc]; exact hmono Fin.castSucc_lt_succ.le
      have hle_last : u ⟨k + 1, hk⟩ ≤ u (Fin.last n) := hmono (Fin.le_last _)
      -- the smooth piece `[u k, u (k+1)]`
      have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) := by
        rw [hcast, hsucc]; exact hsmooth ⟨k, hkn⟩
      -- length additivity on the Petersen side
      have hsubL : Set.uIcc (u 0) (u ⟨k, hk1⟩) ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_prefix,
          Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc_right (hle_piece.trans hle_last)
      have hsubR : Set.uIcc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)
          ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_piece,
          Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc hle_prefix hle_last
      have hsplit : curveLength (I := I) g γ (u 0) (u ⟨k + 1, hk⟩)
          = curveLength (I := I) g γ (u 0) (u ⟨k, hk1⟩)
            + curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
        curveLength_additive (I := I) g γ (hγint.mono_set hsubL) (hγint.mono_set hsubR)
      -- single-piece `riemannianEDist` bound via the length bridge
      have hpiece : Manifold.riemannianEDist I (γ (u ⟨k, hk1⟩)) (γ (u ⟨k + 1, hk⟩))
          ≤ ENNReal.ofReal (curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) := by
        have hpath := pathELength_eq_ofReal_curveLength (I := I) g hle_piece hsm
        have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) :=
          hsm.of_le (by exact_mod_cast le_top)
        calc Manifold.riemannianEDist I (γ (u ⟨k, hk1⟩)) (γ (u ⟨k + 1, hk⟩))
            ≤ Manifold.pathELength I γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
              Manifold.riemannianEDist_le_pathELength hC1 rfl rfl hle_piece
          _ = ENNReal.ofReal (curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) := hpath
      -- assemble via the triangle inequality
      have hnn1 : 0 ≤ curveLength (I := I) g γ (u 0) (u ⟨k, hk1⟩) :=
        curveLength_nonneg (I := I) g γ hle_prefix
      have hnn2 : 0 ≤ curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
        curveLength_nonneg (I := I) g γ hle_piece
      calc Manifold.riemannianEDist I (γ (u 0)) (γ (u ⟨k + 1, hk⟩))
          ≤ Manifold.riemannianEDist I (γ (u 0)) (γ (u ⟨k, hk1⟩))
              + Manifold.riemannianEDist I (γ (u ⟨k, hk1⟩)) (γ (u ⟨k + 1, hk⟩)) :=
            Manifold.riemannianEDist_triangle
        _ ≤ ENNReal.ofReal (curveLength (I := I) g γ (u 0) (u ⟨k, hk1⟩))
              + ENNReal.ofReal (curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) :=
            add_le_add (ih hk1) hpiece
        _ = ENNReal.ofReal (curveLength (I := I) g γ (u 0) (u ⟨k + 1, hk⟩)) := by
            rw [hsplit, ENNReal.ofReal_add hnn1 hnn2]
  have hfin := key n n.lt_succ_self
  have hlast : (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = Fin.last n := rfl
  rwa [hlast] at hfin

/-- **Math.** **The (≤) half of the distance bridge.**  On a connected manifold,
the mathlib Riemannian edistance is bounded by the Petersen distance:
`riemannianEDist I p q ≤ ofReal (riemannianDistance g p q)`.
Every piecewise-`C^∞` competitor `γ` of the Petersen infimum is a
`riemannianEDist`-competitor of the same length
(`riemannianEDist_le_ofReal_curveLength_of_isPiecewiseSmoothCurve`); passing to
the infimum gives the bound.  Connectedness guarantees the competitor set is
nonempty (so the Petersen distance is a genuine infimum, not the junk value). -/
theorem riemannianEDist_le_ofReal_riemannianDistance [ConnectedSpace M]
    (g : RiemannianMetric I M) (p q : M) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I p q
      ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set S : Set ℝ := {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
    γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1} with hS
  have hSne : S.Nonempty := by
    obtain ⟨γ, hγ, h0, h1⟩ := exists_isPiecewiseSmoothCurve_connecting (I := I) p q
    exact ⟨curveLength (I := I) g γ 0 1, γ, hγ, h0, h1, rfl⟩
  -- each competitor bounds `riemannianEDist` from above
  have hcompet : ∀ L ∈ S, Manifold.riemannianEDist I p q ≤ ENNReal.ofReal L := by
    rintro L ⟨γ, hγ, h0, h1, rfl⟩
    have h := riemannianEDist_le_ofReal_curveLength_of_isPiecewiseSmoothCurve (I := I) g hγ
    rwa [h0, h1] at h
  have hd : riemannianDistance (I := I) g p q = sInf S := rfl
  -- push through the infimum with an `ε`-argument
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨L, hLS, hLlt⟩ := Real.lt_sInf_add_pos hSne (ε := (ε : ℝ)) (by exact_mod_cast hε)
  calc Manifold.riemannianEDist I p q
      ≤ ENNReal.ofReal L := hcompet L hLS
    _ ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q + (ε : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by rw [hd]; exact hLlt.le)
    _ = ENNReal.ofReal (riemannianDistance (I := I) g p q) + ε := by
        rw [ENNReal.ofReal_add (riemannianDistance_nonneg (I := I) g p q)
          (by positivity), ENNReal.ofReal_coe_nnreal]

end PetersenLib

end
