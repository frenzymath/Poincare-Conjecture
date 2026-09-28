import PetersenLib.Ch05.OpenSubmanifoldFlat
import PetersenLib.Ch05.SegmentTranslate

/-!
# Petersen Ch. 5, §5.3 — Example 5.3.7: the punctured plane has no segment from `(-1,0)` to `(1,0)`

Petersen's recurring counterexample: `ℝ² − {(0,0)}` with the induced (flat)
metric.  Its two points `p = (-1, 0)` and `q = (1, 0)` are at distance
`|pq| = 2` — the Euclidean distance, approached by detours through `(0, δ)` as
`δ ↓ 0` — but *no* segment joins them, because a segment would have to pass
through the deleted origin.  Hence (Example 5.3.7) **not every pair of points of
a Riemannian manifold is joined by a segment**; the completeness hypothesis in
Hopf–Rinow is not decorative.

Contents:

* `puncturedPlane`, `puncturedPlaneMetric` — `ℝ² − {0}` as an open submanifold of
  `E² = EuclideanSpace ℝ (Fin 2)`, with the flat metric `opensFlatMetric`;
* `pLeft`, `pRight` — the points `(-1, 0)` and `(1, 0)`;
* `riemannianDistance_pLeft_pRight` — `|pq| = 2` (Example 5.3.1's distance
  computation);
* `no_segment_pLeft_pRight` — no segment joins `pLeft` to `pRight`;
* `example_punctured_plane_no_segment` — **Example 5.3.7**: it is *not* the case
  that every pair of points of `ℝ² − {0}` is joined by a segment.

The proof of `no_segment_pLeft_pRight` is Petersen's: a segment `σ : [0, b] → M`
is parametrized proportionally to arc length, so its midtime `b/2` splits it into
two halves of length exactly `1` each; the chord bound
(`norm_sub_le_curveLength_opensFlatMetric`) forces `‖p − σ(b/2)‖ ≤ 1` and
`‖σ(b/2) − q‖ ≤ 1`, and since `‖p − q‖ = 2` the Cauchy–Schwarz equality case
(`inner_eq_norm_mul_iff_real`) pins `σ(b/2)` to the Euclidean midpoint `(0,0)` —
which is not a point of the punctured plane.

**What this file does NOT provide.**  It does *not* prove Example 5.3.1
(`ex:pet-ch5-infimum-not-realized`) in full: `riemannianDistance_pLeft_pRight` is
only that example's distance half.  The other half — that *no curve whatsoever*
from `pLeft` to `pRight` has length `2` — does not follow from the argument here,
which uses the proportional-arc-length clause of `IsSegment` to locate the
half-length time; for an arbitrary parametrization one needs an intermediate
value theorem for `t ↦ curveLength g γ 0 t`.  It also says nothing about the
*geodesics* of the punctured plane (Example 5.2.7); the coefficient input for
that, `chartChristoffel_opensFlatMetric`, is in `Ch05/OpenSubmanifoldFlat.lean`,
but converting it into `IsGeodesic` statements is separate work.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §5.3, Example 5.3.7.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Bornology TopologicalSpace Set
open scoped ContDiff Manifold Topology

namespace PetersenLib

/-! ## The Euclidean plane and its standard basis -/

/-- The Euclidean plane `ℝ²`, the ambient space of Petersen's punctured-plane
examples. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- **Math.** The plane vector with coordinates `(a, b)`, written in the standard
orthonormal basis of `E²`. -/
def vec (a b : ℝ) : E2 :=
  a • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + b • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

@[simp] theorem vec_zero : vec 0 0 = 0 := by simp [vec]

/-- **Math.** Coordinates add: `(a, b) + (c, d) = (a + c, b + d)`. -/
theorem vec_add (a b c d : ℝ) : vec a b + vec c d = vec (a + c) (b + d) := by
  simp only [vec, add_smul]; abel

/-- **Math.** Coordinates scale: `t · (a, b) = (t a, t b)`. -/
theorem vec_smul (t a b : ℝ) : t • vec a b = vec (t * a) (t * b) := by
  simp only [vec, smul_add, smul_smul]

/-- **Math.** Coordinates subtract: `(a, b) − (c, d) = (a − c, b − d)`. -/
theorem vec_sub (a b c d : ℝ) : vec a b - vec c d = vec (a - c) (b - d) := by
  simp only [vec, sub_smul]; abel

/-- **Math.** The standard basis of `E²` is orthonormal, so `‖(a, b)‖² = a² + b²`
(Pythagoras). -/
theorem norm_vec_sq (a b : ℝ) : ‖vec a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have horth : (inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) : ℝ) = 0 := by
    simp [EuclideanSpace.inner_single_left]
  rw [vec, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, horth,
    norm_smul, norm_smul]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Math.** The Euclidean norm in coordinates: `‖(a, b)‖ = √(a² + b²)`. -/
theorem norm_vec (a b : ℝ) : ‖vec a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← norm_vec_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **Math.** A plane vector is nonzero as soon as its coordinates do not both
vanish (equivalently `a² + b² ≠ 0`). -/
theorem vec_ne_zero {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : vec a b ≠ 0 := by
  intro hc
  exact h (by rw [← norm_vec_sq, hc]; simp)

/-- **Math.** A sum of two squares vanishes only when both terms do. -/
theorem sq_add_sq_ne_zero {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : a ^ 2 + b ^ 2 ≠ 0 := by
  intro hc
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg a) (sq_nonneg b)).mp hc
  rcases h with h | h
  · exact h (pow_eq_zero_iff two_ne_zero |>.mp ha)
  · exact h (pow_eq_zero_iff two_ne_zero |>.mp hb)

/-! ## The punctured plane -/

/-- **Math.** Petersen §5.3 (Examples 5.3.1 and 5.3.7): the **punctured plane**
`ℝ² − {(0,0)}`, an open submanifold of `E²`. -/
def puncturedPlane : Opens E2 := ⟨{x | x ≠ 0}, isOpen_ne⟩

@[simp] theorem mem_puncturedPlane {x : E2} : x ∈ puncturedPlane ↔ x ≠ 0 := Iff.rfl

/-- **Math.** The punctured plane carries the metric **induced from `ℝ²`**, i.e.
the flat metric `opensFlatMetric`. -/
def puncturedPlaneMetric : RiemannianMetric 𝓘(ℝ, E2) puncturedPlane :=
  opensFlatMetric E2 puncturedPlane

/-- **Math.** Petersen's point `p = (-1, 0)` of the punctured plane. -/
def pLeft : puncturedPlane := ⟨vec (-1) 0, vec_ne_zero (sq_add_sq_ne_zero (Or.inl (by norm_num)))⟩

/-- **Math.** Petersen's point `q = (1, 0)` of the punctured plane. -/
def pRight : puncturedPlane := ⟨vec 1 0, vec_ne_zero (sq_add_sq_ne_zero (Or.inl (by norm_num)))⟩

@[simp] theorem coe_pLeft : (pLeft : E2) = vec (-1) 0 := rfl
@[simp] theorem coe_pRight : (pRight : E2) = vec 1 0 := rfl

/-- **Math.** The Euclidean chord from `(-1, 0)` to `(1, 0)` has length `2`. -/
theorem norm_pLeft_sub_pRight : ‖(pLeft : E2) - (pRight : E2)‖ = 2 := by
  rw [coe_pLeft, coe_pRight, vec_sub, norm_vec]
  norm_num
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-! ## Straight curves inside the punctured plane -/

/-- **Math.** The affine curve `t ↦ p + t v` viewed as a curve *in the punctured
plane*, given a proof that it never hits the origin. -/
def straightSub (p v : E2) (h : ∀ t : ℝ, p + t • v ≠ 0) : ℝ → puncturedPlane :=
  fun t => ⟨p + t • v, h t⟩

@[simp] theorem coe_straightSub (p v : E2) (h : ∀ t : ℝ, p + t • v ≠ 0) (t : ℝ) :
    (straightSub p v h t : E2) = p + t • v := rfl

theorem coe_straightSub_fun (p v : E2) (h : ∀ t : ℝ, p + t • v ≠ 0) :
    (fun r => (straightSub p v h r : E2)) = fun s => p + s • v := rfl

/-- **Math.** A straight curve avoiding the origin is `C^∞` *as a curve into the
punctured plane*: smoothness into an open submanifold is smoothness of the
ambient composite (`ContMDiff.subtypeVal_comp_iff`). -/
theorem contMDiff_straightSub (p v : E2) (h : ∀ t : ℝ, p + t • v ≠ 0) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) ∞ (straightSub p v h) := by
  rw [← ContMDiff.subtypeVal_comp_iff puncturedPlane]
  exact contMDiff_iff_contDiff.mpr (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- **Math.** A straight curve avoiding the origin is piecewise `C^∞` on any
`[a, b]` with `a ≤ b`: it is globally smooth, so one piece suffices. -/
theorem isPiecewiseSmoothCurve_straightSub (p v : E2) (h : ∀ t : ℝ, p + t • v ≠ 0)
    {a b : ℝ} (hab : a ≤ b) :
    IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) (straightSub p v h) a b := by
  have hmono : Monotone (![a, b] : Fin 2 → ℝ) :=
    Fin.monotone_iff_le_succ.mpr (fun i => by fin_cases i; simpa using hab)
  have := isPiecewiseSmoothCurve_of_forall_contMDiffOn
    (I := 𝓘(ℝ, E2)) (γ := straightSub p v h) (u := ![a, b]) hmono
    (fun i => by fin_cases i; exact (contMDiff_straightSub p v h).contMDiffOn)
  simpa using this

/-- **Math.** The intrinsic length of a straight curve inside the punctured plane
is its Euclidean length `‖v‖ (c − a)`: the flat metric is computed by the ambient
geometry (`curveLength_transfer`). -/
theorem curveLength_straightSub (p v : E2) (h : ∀ t : ℝ, p + t • v ≠ 0) (a c : ℝ) :
    curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric (straightSub p v h) a c
      = ‖v‖ * (c - a) := by
  rw [puncturedPlaneMetric, curveLength_transfer, coe_straightSub_fun]
  exact curveLength_euclidean_straight 2 p v a c

/-! ## The detour through `(0, δ)` and the upper bound `|pq| ≤ 2` -/

section Detour

variable {δ : ℝ} (hδ : 0 < δ)
include hδ

/-- The first leg `(-1, 0) → (0, δ)` never meets the origin: at time `t` it sits
at `(t − 1, t δ)`, and `t − 1 = 0` forces `t = 1`, where the second coordinate is
`δ ≠ 0`. -/
theorem detourFst_ne_zero (t : ℝ) : vec (-1) 0 + t • (vec 1 δ) ≠ 0 := by
  rw [vec_smul, vec_add]
  exact vec_ne_zero (sq_add_sq_ne_zero (by
    rcases eq_or_ne t 1 with rfl | ht
    · exact Or.inr (by simpa using hδ.ne')
    · exact Or.inl (by intro hc; exact ht (by linarith [hc]))))

/-- The second leg `(0, δ) → (1, 0)` never meets the origin: at time `t` it sits
at `(t, δ (1 − t))`, and `t = 0` leaves the second coordinate `δ ≠ 0`. -/
theorem detourSnd_ne_zero (t : ℝ) : vec 0 δ + t • (vec 1 (-δ)) ≠ 0 := by
  rw [vec_smul, vec_add]
  exact vec_ne_zero (sq_add_sq_ne_zero (by
    rcases eq_or_ne t 0 with rfl | ht
    · exact Or.inr (by simpa using hδ.ne')
    · exact Or.inl (by simpa using ht)))

/-- The first leg of Petersen's detour: the straight curve from `(-1, 0)` to
`(0, δ)`, parametrized on `[0, 1]`. -/
def detourFst : ℝ → puncturedPlane := straightSub (vec (-1) 0) (vec 1 δ) (detourFst_ne_zero hδ)

/-- The second leg of Petersen's detour: the straight curve from `(0, δ)` to
`(1, 0)`, parametrized on `[0, 1]`. -/
def detourSnd : ℝ → puncturedPlane := straightSub (vec 0 δ) (vec 1 (-δ)) (detourSnd_ne_zero hδ)

theorem detourFst_zero : detourFst hδ 0 = pLeft := by
  apply Subtype.ext; simp [detourFst, pLeft]

theorem detourFst_one : (detourFst hδ 1 : E2) = vec 0 δ := by
  simp [detourFst, vec_add]

theorem detourSnd_zero : (detourSnd hδ 0 : E2) = vec 0 δ := by
  simp [detourSnd]

theorem detourSnd_one : detourSnd hδ 1 = pRight := by
  apply Subtype.ext
  simp [detourSnd, pRight, vec_add]

theorem detour_glue : detourFst hδ 1 = detourSnd hδ 0 := by
  apply Subtype.ext
  rw [detourFst_one, detourSnd_zero]

/-- **Math.** Each leg of the detour has Euclidean length `√(1 + δ²)`. -/
theorem curveLength_detourFst :
    curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric (detourFst hδ) 0 1
      = Real.sqrt (1 + δ ^ 2) := by
  rw [detourFst, curveLength_straightSub, norm_vec]
  norm_num

theorem curveLength_detourSnd :
    curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric (detourSnd hδ) 0 1
      = Real.sqrt (1 + δ ^ 2) := by
  rw [detourSnd, curveLength_straightSub, norm_vec]
  norm_num

theorem isPiecewiseSmoothCurve_detourFst :
    IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) (detourFst hδ) 0 1 :=
  isPiecewiseSmoothCurve_straightSub _ _ _ zero_le_one

theorem isPiecewiseSmoothCurve_detourSnd :
    IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) (detourSnd hδ) 0 1 :=
  isPiecewiseSmoothCurve_straightSub _ _ _ zero_le_one

/-- **Math.** Petersen's detour from `(-1, 0)` to `(1, 0)` via `(0, δ)`: a
piecewise `C^∞` curve `[0, 1] → ℝ² − {0}` of length `2 √(1 + δ²)`. -/
theorem isPiecewiseSmoothCurve_detour :
    IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2))
      (curveConcat (detourFst hδ) (detourSnd hδ)) 0 1 :=
  isPiecewiseSmoothCurve_curveConcat (isPiecewiseSmoothCurve_detourFst hδ)
    (isPiecewiseSmoothCurve_detourSnd hδ) (detour_glue hδ)

theorem curveLength_detour :
    curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
        (curveConcat (detourFst hδ) (detourSnd hδ)) 0 1
      = 2 * Real.sqrt (1 + δ ^ 2) := by
  rw [curveLength_curveConcat (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
    (isPiecewiseSmoothCurve_detourFst hδ) (isPiecewiseSmoothCurve_detourSnd hδ)
    (detour_glue hδ), curveLength_detourFst, curveLength_detourSnd]
  ring

/-- **Math.** The detour bounds the distance: `|pq| ≤ 2 √(1 + δ²)` for every
`δ > 0`. -/
theorem riemannianDistance_le_detour :
    riemannianDistance (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft pRight
      ≤ 2 * Real.sqrt (1 + δ ^ 2) := by
  rw [← curveLength_detour hδ]
  refine riemannianDistance_le_curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
    (isPiecewiseSmoothCurve_detour hδ) ?_ ?_
  · rw [curveConcat_zero, detourFst_zero]
  · rw [curveConcat_one, detourSnd_one]

end Detour

/-- **Math.** `pLeft` and `pRight` are joined by *some* piecewise `C^∞` curve
inside the punctured plane (the `δ = 1` detour), so Petersen's `Ω_{p,q}` is
nonempty and `|pq|` is a genuine infimum rather than the junk value `sInf ∅`. -/
theorem exists_curve_pLeft_pRight :
    ∃ γ : ℝ → puncturedPlane, IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) γ 0 1 ∧
      γ 0 = pLeft ∧ γ 1 = pRight :=
  ⟨curveConcat (detourFst one_pos) (detourSnd one_pos),
    isPiecewiseSmoothCurve_detour one_pos,
    by rw [curveConcat_zero, detourFst_zero], by rw [curveConcat_one, detourSnd_one]⟩

/-! ## The distance `|(-1,0)(1,0)| = 2` -/

/-- **Math.** Petersen Example 5.3.1 (distance half): in `ℝ² − {(0,0)}` with the
induced metric, `|(-1,0)(1,0)| = 2`.  The lower bound is the ambient chord bound
(`norm_sub_le_riemannianDistance_opensFlatMetric`); the upper bound is the family
of detours through `(0, δ)`, of length `2 √(1 + δ²) → 2` as `δ ↓ 0`.

**Caveat.** This is *only* the distance half of Example 5.3.1; it does not prove
that the infimum is unrealized. -/
theorem riemannianDistance_pLeft_pRight :
    riemannianDistance (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft pRight = 2 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: let `δ ↓ 0` along the detours
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδ : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hbound := riemannianDistance_le_detour hδ
    rw [hsq] at hbound
    refine hbound.trans ?_
    have h1 : Real.sqrt (1 + ε) ≤ (2 + ε) / 2 := by
      have hle : (1 : ℝ) + ε ≤ ((2 + ε) / 2) ^ 2 := by nlinarith
      calc Real.sqrt (1 + ε) ≤ Real.sqrt (((2 + ε) / 2) ^ 2) := Real.sqrt_le_sqrt hle
        _ = (2 + ε) / 2 := Real.sqrt_sq (by linarith)
    linarith
  · -- lower bound: the ambient Euclidean chord
    have h := norm_sub_le_riemannianDistance_opensFlatMetric (n := 2) puncturedPlane
      pLeft pRight exists_curve_pLeft_pRight
    rwa [norm_pLeft_sub_pRight] at h

/-! ## No segment joins `(-1,0)` to `(1,0)` -/

/-- **Math.** Petersen Example 5.3.7: **no segment of `ℝ² − {(0,0)}` joins
`(-1, 0)` to `(1, 0)`**.  Suppose `σ : [0, b] → ℝ² − {0}` were one.  Its
parametrization is proportional to arc length, `L(σ)|₀ᵗ = k t`, and
`L(σ)|₀^b = |pq| = 2`, so `k b = 2` and the midtime `b/2` splits `σ` into two
halves of length exactly `1`.  Writing `m = σ(b/2)`, the chord bound gives
`‖p − m‖ ≤ 1` and `‖m − q‖ ≤ 1`, while `‖p − q‖ = 2`; the triangle inequality is
therefore an equality, and the Cauchy–Schwarz equality case
(`inner_eq_norm_mul_iff_real`) forces `m − p = q − m`, i.e. `m` is the Euclidean
midpoint `(0,0)`.  But `(0,0)` is not a point of the punctured plane. -/
theorem no_segment_pLeft_pRight :
    ¬ ∃ (γ : ℝ → puncturedPlane) (b : ℝ),
        IsSegment (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ 0 b ∧ γ 0 = pLeft ∧ γ b = pRight := by
  rintro ⟨γ, b, ⟨hpw, hlen, k, hk0, hprop⟩, h0, hb⟩
  -- the domain of a piecewise smooth curve on `[0, b]` has `0 ≤ b`
  have hb0 : 0 ≤ b := by
    obtain ⟨-, n, u, hmono, hu0, hun, -⟩ := hpw
    rw [← hu0, ← hun]
    exact hmono (Fin.zero_le _)
  -- the total length is the distance, namely `2`
  have htot : curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ 0 b = 2 := by
    rw [hlen, h0, hb, riemannianDistance_pLeft_pRight]
  -- proportionality at `t = b` gives `k b = 2`, hence `b > 0`
  have hkb : k * b = 2 := by
    have := hprop b ⟨hb0, le_rfl⟩
    rw [htot, sub_zero] at this
    exact this.symm
  have hbpos : 0 < b := by
    rcases hb0.eq_or_lt with rfl | h
    · rw [mul_zero] at hkb; norm_num at hkb
    · exact h
  -- proportionality at `t = b/2` gives length `1` on the first half
  have hhalf : curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ 0 (b / 2) = 1 := by
    have := hprop (b / 2) ⟨by linarith, by linarith⟩
    rw [sub_zero] at this
    rw [this]; nlinarith
  -- additivity gives length `1` on the second half
  have hhalf' : curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ (b / 2) b = 1 := by
    have hadd := hpw.curveLength_add (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
      (by linarith : (0:ℝ) ≤ b / 2) (by linarith : b / 2 ≤ b)
    rw [htot, hhalf] at hadd
    linarith
  set m : E2 := (γ (b / 2) : E2) with hm
  -- the first half, reparametrized to `[0, 1]`, is a competitor from `p` to `m`
  have hfst : ‖(pLeft : E2) - m‖ ≤ 1 := by
    have hpw' : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2))
        (fun s => γ (b / 2 * s + 0)) 0 1 := by
      refine isPiecewiseSmoothCurve_comp_mul_add (I := 𝓘(ℝ, E2)) (by linarith) ?_
      have he1 : b / 2 * 0 + 0 = 0 := by ring
      have he2 : b / 2 * 1 + 0 = b / 2 := by ring
      rw [he1, he2]
      exact hpw.mono le_rfl (by linarith) (by linarith)
    have hlen' : curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
        (fun s => γ (b / 2 * s + 0)) 0 1 = 1 := by
      rw [curveLength_comp_mul_add (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ
        (by linarith : (0:ℝ) ≤ b / 2) 0 0 1]
      have he1 : b / 2 * 0 + 0 = 0 := by ring
      have he2 : b / 2 * 1 + 0 = b / 2 := by ring
      rw [he1, he2, hhalf]
    have hchord : ‖(pLeft : E2) - (γ (b / 2) : E2)‖
        ≤ curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
            (fun s => γ (b / 2 * s + 0)) 0 1 :=
      norm_sub_le_curveLength_opensFlatMetric (n := 2) puncturedPlane
        (γ := fun s => γ (b / 2 * s + 0)) (x := pLeft) (y := γ (b / 2)) hpw'
        (by simpa using h0) (by norm_num)
    rw [hlen'] at hchord
    exact hchord
  -- the second half, reparametrized to `[0, 1]`, is a competitor from `m` to `q`
  have hsnd : ‖m - (pRight : E2)‖ ≤ 1 := by
    have hpw' : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2))
        (fun s => γ (b / 2 * s + b / 2)) 0 1 := by
      refine isPiecewiseSmoothCurve_comp_mul_add (I := 𝓘(ℝ, E2)) (by linarith) ?_
      have he1 : b / 2 * 0 + b / 2 = b / 2 := by ring
      have he2 : b / 2 * 1 + b / 2 = b := by ring
      rw [he1, he2]
      exact hpw.mono (by linarith) (by linarith) le_rfl
    have hlen' : curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
        (fun s => γ (b / 2 * s + b / 2)) 0 1 = 1 := by
      rw [curveLength_comp_mul_add (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ
        (by linarith : (0:ℝ) ≤ b / 2) (b / 2) 0 1]
      have he1 : b / 2 * 0 + b / 2 = b / 2 := by ring
      have he2 : b / 2 * 1 + b / 2 = b := by ring
      rw [he1, he2, hhalf']
    have hchord : ‖(γ (b / 2) : E2) - (pRight : E2)‖
        ≤ curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric
            (fun s => γ (b / 2 * s + b / 2)) 0 1 :=
      norm_sub_le_curveLength_opensFlatMetric (n := 2) puncturedPlane
        (γ := fun s => γ (b / 2 * s + b / 2)) (x := γ (b / 2)) (y := pRight) hpw'
        (by norm_num)
        (by show γ (b / 2 * 1 + b / 2) = pRight
            rw [show b / 2 * 1 + b / 2 = b by ring]; exact hb)
    rw [hlen'] at hchord
    exact hchord
  -- Cauchy–Schwarz equality: `m` is forced to be the Euclidean midpoint `(0,0)`
  set a : E2 := m - (pLeft : E2) with ha
  set c : E2 := (pRight : E2) - m with hc
  have hna : ‖a‖ ≤ 1 := by rw [ha, ← norm_neg]; simpa using hfst
  have hnc : ‖c‖ ≤ 1 := by rw [hc, ← norm_neg]; simpa using hsnd
  have hac : a + c = (pRight : E2) - (pLeft : E2) := by rw [ha, hc]; abel
  have hnac : ‖a + c‖ = 2 := by rw [hac, ← norm_neg, neg_sub]; exact norm_pLeft_sub_pRight
  have htri : ‖a + c‖ ≤ ‖a‖ + ‖c‖ := norm_add_le a c
  have hna1 : ‖a‖ = 1 := by rw [hnac] at htri; linarith
  have hnc1 : ‖c‖ = 1 := by rw [hnac] at htri; linarith
  have hinner : (inner ℝ a c : ℝ) = ‖a‖ * ‖c‖ := by
    have hexp := norm_add_sq_real a c
    rw [hnac, hna1, hnc1] at hexp
    rw [hna1, hnc1]
    nlinarith [hexp]
  have heq : ‖c‖ • a = ‖a‖ • c := (inner_eq_norm_mul_iff_real).mp hinner
  rw [hna1, hnc1, one_smul, one_smul] at heq
  -- `a = c` means `m − p = q − m`, i.e. `2 m = p + q = 0`
  have hmid : (2 : ℝ) • m = (pLeft : E2) + (pRight : E2) := by
    rw [ha, hc] at heq
    have : m - (pLeft : E2) = (pRight : E2) - m := heq
    rw [two_smul]
    linear_combination (norm := module) this
  have hpq : (pLeft : E2) + (pRight : E2) = 0 := by
    rw [coe_pLeft, coe_pRight, vec_add]
    norm_num
  rw [hpq] at hmid
  have hm0 : m = 0 := by
    have := hmid
    rw [smul_eq_zero] at this
    rcases this with h | h
    · norm_num at h
    · exact h
  exact (γ (b / 2)).2 hm0

/-- **Math.** **Example 5.3.7** (Petersen §5.3, `ex:pet-ch5-punctured-plane-no-segment`).
In `ℝ² − {(0,0)}`, **not every pair of points is joined by a segment**: the pair
`(-1, 0)`, `(1, 0)` is not (`no_segment_pLeft_pRight`).  Together with
`thm:pet-ch5-hopf-rinow`, this shows the completeness hypothesis there cannot be
dropped.

The segment's domain `[a, b]` is left completely free — no normalization is
assumed — so this is the full strength of Petersen's assertion; the reduction to
a domain of the form `[0, b]` is `IsSegment.translate`. -/
theorem example_punctured_plane_no_segment :
    ¬ ∀ (x y : puncturedPlane), ∃ (γ : ℝ → puncturedPlane) (a b : ℝ),
        IsSegment (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ a b ∧ γ a = x ∧ γ b = y := by
  intro h
  obtain ⟨γ, a, b, hseg, ha, hb⟩ := h pLeft pRight
  refine no_segment_pLeft_pRight ⟨fun s => γ (1 * s + a), b - a, hseg.translate, ?_, ?_⟩
  · show γ (1 * 0 + a) = pLeft
    rw [show (1 : ℝ) * 0 + a = a by ring]; exact ha
  · show γ (1 * (b - a) + a) = pRight
    rw [show (1 : ℝ) * (b - a) + a = b by ring]; exact hb

end PetersenLib
