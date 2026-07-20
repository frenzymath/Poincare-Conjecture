import PetersenLib.Ch05.DistanceSegments
import PetersenLib.Ch05.MetricTopology
import PetersenLib.Ch01.RiemannianManifolds

/-!
# Petersen Ch. 5, §5.6.1 — local Riemannian isometries

The definitional spine of Petersen §5.6.1 together with the metric (length /
distance) half of Proposition 5.6.1.

* `def:pet-ch5-local-isometry` — `IsLocalRiemannianIsometry`: a smooth map
  `F : (M, g_M) → (N, g_N)` whose differential `DF_p : T_pM → T_{F p}N` is, at
  every point, a **linear isometry** of inner-product spaces (norm-preserving —
  equivalently inner-product preserving — *and* bijective).  We reuse the Ch. 1
  predicate `PetersenLib.PreservesMetric` (`F^*g_N = g_M`) for the
  inner-product-preserving clause.

* `prop:pet-ch5-local-isometry-properties`, part (3) —
  `localIsometry_distanceDecreasing`: a local isometry is distance decreasing,
  `d_N(F p, F q) ≤ d_M(p, q)`.  The heart is that `F` **preserves the length of
  every curve** (`localIsometry_curveLength` for smooth curves,
  `localIsometry_curveLength_piecewise` for the piecewise-smooth competitors of
  the distance infimum): `L_N(F ∘ γ) = L_M(γ)`, because `DF` preserves the
  intrinsic speed pointwise (`localIsometry_curveSpeedSq`).  Together with the
  competitor-set inclusion `Ω_{p,q} ↦ Ω_{F p, F q}` this gives the infimum bound.
  Part (4) (a bijective local isometry is distance *preserving*) is
  `localIsometry_distancePreserving`.

Parts (1)–(2) of Prop. 5.6.1 (a local isometry maps geodesics to geodesics and
is natural with respect to `exp`) are proved in
`PetersenLib.Ch05.LocalIsometryGeodesics`, which imports this file:
`localIsometry_mapsGeodesicsToGeodesics` and `localIsometry_expNaturality`.  They
need no connection theory — `IsGeodesic` is the moving-foot coordinate equation,
so the Christoffel transformation law under a local isometry is proved exactly as
in `PetersenLib.Ch05.ChartTransition`, from the §5.1 mixed-partials axioms.  The
metric part below is independent of them.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless]

/-! ## The definition -/

/-- **Math.** Petersen Ch. 5, §5.6.1 (`def:pet-ch5-local-isometry`): a map
`F : (M, g_M) → (N, g_N)` is a **local Riemannian isometry** if it is smooth and
for each `p ∈ M` the differential `DF_p : T_pM → T_{F p}N` is a linear isometry
of inner-product spaces.  Concretely `F` is `C^∞`, it **preserves the metric**
(`PetersenLib.PreservesMetric`, i.e. `g_N(DF u, DF v) = g_M(u, v)`, so `DF_p` is
norm-preserving), and each `DF_p` is bijective (so `DF_p` is an isometric
*isomorphism* of tangent spaces, matching Petersen's phrase "linear isometry";
this forces `dim M = dim N`).  A coordinate chart with the induced metric is the
prototypical example. -/
def IsLocalRiemannianIsometry (gM : RiemannianMetric I M) (gN : RiemannianMetric I' M')
    (F : M → M') : Prop :=
  ContMDiff I I' ∞ F ∧ PreservesMetric gM gN F ∧
    ∀ p : M, Function.Bijective (mfderiv I I' F p)

namespace IsLocalRiemannianIsometry

variable {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {F : M → M'}

theorem contMDiff (hF : IsLocalRiemannianIsometry gM gN F) : ContMDiff I I' ∞ F := hF.1

theorem preservesMetric (hF : IsLocalRiemannianIsometry gM gN F) :
    PreservesMetric gM gN F := hF.2.1

theorem bijective_mfderiv (hF : IsLocalRiemannianIsometry gM gN F) (p : M) :
    Function.Bijective (mfderiv I I' F p) := hF.2.2 p

theorem mdifferentiable (hF : IsLocalRiemannianIsometry gM gN F) :
    MDifferentiable I I' F := hF.1.mdifferentiable (by norm_num)

theorem mdifferentiableAt (hF : IsLocalRiemannianIsometry gM gN F) (p : M) :
    MDifferentiableAt I I' F p := hF.mdifferentiable p

theorem continuous (hF : IsLocalRiemannianIsometry gM gN F) : Continuous F :=
  hF.1.continuous

end IsLocalRiemannianIsometry

/-- **Math.** The identity map is a local Riemannian isometry of `(M, g)` to
itself. -/
theorem isLocalRiemannianIsometry_id (g : RiemannianMetric I M) :
    IsLocalRiemannianIsometry g g (id : M → M) := by
  refine ⟨contMDiff_id, fun p u v => ?_, fun p => ?_⟩
  · rw [mfderiv_id]; rfl
  · rw [mfderiv_id]; exact Function.bijective_id

/-- **Math.** A (global) Riemannian isometry is in particular a local Riemannian
isometry: it is a diffeomorphism, so its differential is everywhere a linear
isometric isomorphism. -/
theorem IsRiemannianIsometry.isLocalRiemannianIsometry {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {F : M → M'} (hF : IsRiemannianIsometry gM gN F) :
    IsLocalRiemannianIsometry gM gN F := by
  obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := hF
  refine ⟨?_, hpres, fun p => ?_⟩
  · rw [← hΦ]; exact Φ.contMDiff
  · -- `F = Φ`, a diffeomorphism, so `DF_p` is a continuous linear equiv, hence bijective
    have hd : mfderiv I I' F p = mfderiv I I' (Φ : M → M') p := by rw [hΦ]
    rw [hd, ← Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ (by norm_num) (x := p)]
    exact (Φ.mfderivToContinuousLinearEquiv (by norm_num) p).bijective

/-! ## Length preservation -/

/-- **Math.** A local Riemannian isometry preserves the **intrinsic squared speed**
of a curve at every point of differentiability: `|d(F∘γ)/dt|²_{g_N} = |dγ/dt|²_{g_M}`.
This is the pointwise heart of length preservation: by the chain rule
`d(F∘γ)/dt = DF(dγ/dt)` and `DF` preserves the inner product. -/
theorem localIsometry_curveSpeedSq {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F) {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    curveSpeedSq (I := I') gN (F ∘ γ) t = curveSpeedSq (I := I) gM γ t := by
  have hFdiff : MDifferentiableAt I I' F (γ t) := hF.mdifferentiableAt (γ t)
  have hFγ : MDifferentiableAt 𝓘(ℝ, ℝ) I' (F ∘ γ) t := hFdiff.comp t hγ
  rw [curveSpeedSq_eq_metricInner_velocity gN hFγ, curveSpeedSq_eq_metricInner_velocity gM hγ,
    velocity_comp t hFdiff hγ]
  exact (hF.preservesMetric (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t)).symm

/-- **Math.** A local Riemannian isometry preserves the **length of a smooth
curve**: `L_N(F ∘ γ)|_a^b = L_M(γ)|_a^b`. The speed integrands agree at every
time by `localIsometry_curveSpeedSq`. -/
theorem localIsometry_curveLength {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (a b : ℝ) :
    curveLength (I := I') gN (F ∘ γ) a b = curveLength (I := I) gM γ a b := by
  rw [curveLength_def, curveLength_def]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [localIsometry_curveSpeedSq hF (hγ.mdifferentiableAt (by norm_num))]

/-- **Math.** The composite of a piecewise smooth curve with a smooth map is
piecewise smooth: the same partition works, since `F` composes with each smooth
piece and preserves continuity. -/
theorem isPiecewiseSmoothCurve_comp {F : M → M'} (hF : ContMDiff I I' ∞ F) {γ : ℝ → M}
    {a b : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) :
    IsPiecewiseSmoothCurve (I := I') (F ∘ γ) a b := by
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  exact ⟨hF.continuous.comp_continuousOn hcont, n, u, hmono, hu0, hun,
    fun i => hF.comp_contMDiffOn (hsmooth i)⟩

/-- **Math.** A local Riemannian isometry preserves the length of a curve that is
`C^∞` on a **closed interval** `[c, d]`: `L_N(F ∘ γ)|_c^d = L_M(γ)|_c^d`. The
speed integrands agree at every interior time (where the curve is
differentiable), and the two endpoints are a null set. -/
theorem localIsometry_curveLength_contMDiffOn {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F)
    {γ : ℝ → M} {c d : ℝ} (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc c d)) :
    curveLength (I := I') gN (F ∘ γ) c d = curveLength (I := I) gM γ c d := by
  rw [curveLength_def, curveLength_def]
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : volume ({c, d} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hxI
  rw [Set.uIoc_of_le hcd, Set.mem_Ioc] at hxI
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  have hxIoo : x ∈ Ioo c d := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.2⟩
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ x :=
    (hγ.contMDiffAt (Icc_mem_nhds hxIoo.1 hxIoo.2)).mdifferentiableAt (by norm_num)
  rw [localIsometry_curveSpeedSq hF hmdiff]

/-- **Math.** A local Riemannian isometry preserves the length of a
**piecewise** smooth curve: `L_N(F ∘ γ)|_a^b = L_M(γ)|_a^b`. Telescoping the
length over the partition, each closed smooth piece is handled by
`localIsometry_curveLength_contMDiffOn`. -/
theorem localIsometry_curveLength_piecewise {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F)
    {γ : ℝ → M} {a b : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) :
    curveLength (I := I') gN (F ∘ γ) a b = curveLength (I := I) gM γ a b := by
  have hFγ : IsPiecewiseSmoothCurve (I := I') (F ∘ γ) a b :=
    isPiecewiseSmoothCurve_comp hF.contMDiff hγ
  have hFint := hFγ.intervalIntegrable_sqrt_curveSpeedSq gN
  have hγint := hγ.intervalIntegrable_sqrt_curveSpeedSq gM
  obtain ⟨-, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  subst hu0; subst hun
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      curveLength (I := I') gN (F ∘ γ) (u 0) (u ⟨k, hk⟩)
        = curveLength (I := I) gM γ (u 0) (u ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, curveLength_self, curveLength_self]
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
      -- split the length at `u ⟨k, hk1⟩` on both sides
      have hsubL : Set.uIcc (u 0) (u ⟨k, hk1⟩) ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_prefix, Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc_right (hle_piece.trans hle_last)
      have hsubR : Set.uIcc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_piece, Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc hle_prefix hle_last
      have hsplitF : curveLength (I := I') gN (F ∘ γ) (u 0) (u ⟨k + 1, hk⟩)
          = curveLength (I := I') gN (F ∘ γ) (u 0) (u ⟨k, hk1⟩)
            + curveLength (I := I') gN (F ∘ γ) (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
        curveLength_additive (I := I') gN (F ∘ γ) (hFint.mono_set hsubL) (hFint.mono_set hsubR)
      have hsplitγ : curveLength (I := I) gM γ (u 0) (u ⟨k + 1, hk⟩)
          = curveLength (I := I) gM γ (u 0) (u ⟨k, hk1⟩)
            + curveLength (I := I) gM γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
        curveLength_additive (I := I) gM γ (hγint.mono_set hsubL) (hγint.mono_set hsubR)
      have hpiece : curveLength (I := I') gN (F ∘ γ) (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)
          = curveLength (I := I) gM γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) := by
        have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) := by
          rw [hcast, hsucc]; exact hsmooth ⟨k, hkn⟩
        exact localIsometry_curveLength_contMDiffOn hF hle_piece hsm
      rw [hsplitF, hsplitγ, ih hk1, hpiece]
  have hfin := key n n.lt_succ_self
  have hlast : (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = Fin.last n := rfl
  rwa [hlast] at hfin

/-- **Math.** Petersen Ch. 5, Proposition 5.6.1 (3): a local Riemannian isometry
is **distance decreasing**, `d_N(F p, F q) ≤ d_M(p, q)`.  For any piecewise
smooth curve `γ` from `p` to `q`, the image `F ∘ γ` is a piecewise smooth curve
from `F p` to `F q` of the *same length* (`localIsometry_curveLength_piecewise`),
so it is a competitor for the infimum defining `d_N(F p, F q)`; taking the
infimum over all such `γ` gives the bound.  (`M` is assumed connected so that the
competitor set is nonempty.) -/
theorem localIsometry_distanceDecreasing [ConnectedSpace M] {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F)
    (p q : M) :
    riemannianDistance (I := I') gN (F p) (F q) ≤ riemannianDistance (I := I) gM p q := by
  refine le_csInf ?_ ?_
  · obtain ⟨γ, hγ, h0, h1⟩ := exists_isPiecewiseSmoothCurve_connecting (I := I) p q
    exact ⟨curveLength (I := I) gM γ 0 1, γ, hγ, h0, h1, rfl⟩
  · rintro L ⟨γ, hγ, h0, h1, rfl⟩
    have hFγ : IsPiecewiseSmoothCurve (I := I') (F ∘ γ) 0 1 :=
      isPiecewiseSmoothCurve_comp hF.contMDiff hγ
    calc riemannianDistance (I := I') gN (F p) (F q)
        ≤ curveLength (I := I') gN (F ∘ γ) 0 1 :=
          riemannianDistance_le_curveLength (I := I') gN hFγ
            (by rw [Function.comp_apply, h0]) (by rw [Function.comp_apply, h1])
      _ = curveLength (I := I) gM γ 0 1 := localIsometry_curveLength_piecewise hF hγ

/-- **Math.** Petersen Ch. 5, Proposition 5.6.1 (4): a **bijective** local
Riemannian isometry is **distance preserving**.  If `F : M → N` and `G : N → M`
are local Riemannian isometries with `G ∘ F = id`, then both are distance
decreasing (`localIsometry_distanceDecreasing`), and applying the bound to `G`
at `F p, F q` gives the reverse inequality, hence equality
`d_N(F p, F q) = d_M(p, q)`. -/
theorem localIsometry_distancePreserving [ConnectedSpace M] [ConnectedSpace M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {F : M → M'} {G : M' → M}
    (hF : IsLocalRiemannianIsometry gM gN F) (hG : IsLocalRiemannianIsometry gN gM G)
    (hGF : Function.LeftInverse G F) (p q : M) :
    riemannianDistance (I := I') gN (F p) (F q) = riemannianDistance (I := I) gM p q := by
  refine le_antisymm (localIsometry_distanceDecreasing hF p q) ?_
  have h := localIsometry_distanceDecreasing hG (F p) (F q)
  rwa [hGF p, hGF q] at h

end PetersenLib

end
