import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Petersen Ch. 3, §3.2.5 — conjugate versus focal points for an ellipse (Fig. 3.1)

Petersen illustrates the difference between conjugate and focal points with an
ellipse (`rem:pet-ch3-conjugate-vs-focal-example`, page 102, Fig. 3.1):

> "Figure 3.1 shows that conjugate points for the lower part of the ellipse occur
> along the evolute of the lower part of the ellipse. However, when we consider the
> entire ellipse, then the focal set is the line between the focal points of the
> ellipse as the normal lines from the top and bottom of the ellipse intersect
> along this line."

This file formalizes that picture, in the plane, for `c(t) = (a cos t, b sin t)`
with `0 < b < a`:

* `centerOfCurvature_ellipse` — the **centre of curvature** of the ellipse at `c(t)`
  is the classical evolute point `e(t) = (((a²−b²)/a) cos³t, ((b²−a²)/b) sin³t)`.
  The centre of curvature is exactly where infinitesimally near normals meet, i.e.
  the conjugate point along the normal line, so this is the first sentence.
* `mem_ellipseNormalLine_axis` — the normal at `t` and the normal at `−t` (the top
  and bottom arcs, by the symmetry `t ↦ −t`) **both** pass through the single point
  `(((a²−b²)/a)·cos t, 0)` on the major axis, and `axis_inter_eq` says that is the
  *only* point of the normal at `t` on that axis.  So the normals from top and
  bottom do intersect along a segment of the major axis — the second sentence.
* `ellipseEvolute_zero` / `ellipseEvolute_pi` — as `t` varies the intersection
  sweeps the segment between `(±(a²−b²)/a, 0)`, and those two endpoints are exactly
  the evolute's cusps on the major axis, `e(0)` and `e(π)`.

## Petersen's identification of the endpoints is false

The endpoints of that segment are `±(a²−b²)/a`.  The **foci** of the ellipse are at
`±√(a²−b²)`.  These are different, and `evolute_cusp_lt_focus` proves the strict
inequality
```
(a²−b²)/a < √(a²−b²)      for every 0 < b < a,
```
(equivalently `c²/a < c` for `c = √(a²−b²)`, since `c < a`).  So the focal set is
strictly *smaller* than the segment joining the foci, and the two never coincide.

Petersen's geometry is right and his Fig. 3.1 is right — the black segment drawn
there is visibly shorter than the distance between the foci — but the *prose*
identification of its endpoints with "the focal points of the ellipse" is a slip,
conflating the Riemannian *focal points* he had just defined ("a focal point occurs
when integral curves for `∇r` meet") with the two *conic foci*.  The correct
statement is: the focal set is the segment between the two **cusps of the evolute**
on the major axis.

## Modelling

Everything here is elementary plane calculus, deliberately independent of the
manifold layer: there is no `FocalPoint` definition in `PetersenLib`
(`Ch03/DistanceFunctions.lean` explicitly punts on it — "the companion notion of a
focal point … is not formalized here"), and no geodesic-flow, normal-exponential or
caustic API to state the remark at that altitude.  A `remark` node is an
illustration, and this is the illustration, made precise; the link to
`ConjugatePoint` is by prose, not by a formal dependency.

Two implementation notes.  We work in `ℝ × ℝ` rather than `EuclideanSpace ℝ (Fin 2)`
because `HasDerivAt.prodMk` makes the calculus immediate.  This is safe because the
centre-of-curvature formula is used in its **square-root-free** form
`κ⁻¹ • N = (‖v‖²/(v₁w₂ − v₂w₁)) • (−v₂, v₁)`, in which no norm — and hence no
`Real.sqrt`, and no dependence on which norm `ℝ × ℝ` carries — ever appears.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), §3.2.5, page 102.
-/

open Real

noncomputable section

namespace PetersenLib

namespace EllipseEvolute

variable {a b : ℝ}

/-! ## The ellipse, its derivatives, and its evolute -/

/-- The ellipse `t ↦ (a cos t, b sin t)`. -/
def ellipse (a b t : ℝ) : ℝ × ℝ := (a * cos t, b * sin t)

/-- The velocity `c'(t)` of `ellipse a b` (justified by `hasDerivAt_ellipse`). -/
def ellipseVel (a b t : ℝ) : ℝ × ℝ := (-(a * sin t), b * cos t)

/-- The acceleration `c''(t)` of `ellipse a b` (justified by `hasDerivAt_ellipseVel`). -/
def ellipseAcc (a b t : ℝ) : ℝ × ℝ := (-(a * cos t), -(b * sin t))

/-- The classical **evolute** of the ellipse — an astroid-like curve with four cusps,
two of them on the major axis at `t = 0, π`. -/
def ellipseEvolute (a b t : ℝ) : ℝ × ℝ :=
  (((a ^ 2 - b ^ 2) / a) * cos t ^ 3, ((b ^ 2 - a ^ 2) / b) * sin t ^ 3)

/-- The **centre of curvature** (centre of the osculating circle) of a regular plane
curve with position `p`, velocity `v` and acceleration `w`.

This is the square-root-free form of `p + κ⁻¹ • N`, where `κ = (v₁w₂ − v₂w₁)/‖v‖³` is
the signed curvature and `N = (−v₂, v₁)/‖v‖` is the unit tangent rotated by `+90°`:
the two `‖v‖`-powers combine to `κ⁻¹ • N = (‖v‖²/(v₁w₂ − v₂w₁)) • (−v₂, v₁)`, in which
no square root survives.  The centre of curvature is the limit of the intersections of
the normal at `p` with nearby normals — i.e. the conjugate point along the normal. -/
def centerOfCurvature (p v w : ℝ × ℝ) : ℝ × ℝ :=
  p + ((v.1 ^ 2 + v.2 ^ 2) / (v.1 * w.2 - v.2 * w.1)) • (-v.2, v.1)

/-- The **normal line** to the ellipse at parameter `t`: the ellipse's velocity is
`(−a sin t, b cos t)`, so `(b cos t, a sin t)` is a normal direction. -/
def ellipseNormalLine (a b t : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ s : ℝ, p = ellipse a b t + s • (b * cos t, a * sin t)}

/-! ## The derivatives are what we said -/

theorem hasDerivAt_ellipse (a b t : ℝ) : HasDerivAt (ellipse a b) (ellipseVel a b t) t := by
  have h1 : HasDerivAt (fun t : ℝ => a * cos t) (-(a * sin t)) t := by
    simpa [mul_neg] using (Real.hasDerivAt_cos t).const_mul a
  have h2 : HasDerivAt (fun t : ℝ => b * sin t) (b * cos t) t :=
    (Real.hasDerivAt_sin t).const_mul b
  exact h1.prodMk h2

theorem hasDerivAt_ellipseVel (a b t : ℝ) :
    HasDerivAt (ellipseVel a b) (ellipseAcc a b t) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(a * sin t)) (-(a * cos t)) t :=
    ((Real.hasDerivAt_sin t).const_mul a).neg
  have h2 : HasDerivAt (fun t : ℝ => b * cos t) (-(b * sin t)) t := by
    simpa [mul_neg] using (Real.hasDerivAt_cos t).const_mul b
  exact h1.prodMk h2

/-! ## The evolute is the locus of centres of curvature -/

/-- The "cross product" `v₁w₂ − v₂w₁` of the ellipse's velocity and acceleration is the
constant `ab` — a pleasant accident that makes the whole computation rational. -/
theorem ellipse_cross (a b t : ℝ) :
    (ellipseVel a b t).1 * (ellipseAcc a b t).2 - (ellipseVel a b t).2 * (ellipseAcc a b t).1
      = a * b := by
  simp only [ellipseVel, ellipseAcc]
  linear_combination (a * b) * sin_sq_add_cos_sq t

/-- **Math.** Petersen §3.2.5, Fig. 3.1, first sentence, made precise: the **centre of
curvature** of the ellipse `c(t) = (a cos t, b sin t)` — the point where the normals
infinitesimally near `c(t)` meet, i.e. the conjugate point along the normal at `c(t)` —
is the evolute point
`e(t) = (((a²−b²)/a) cos³t, ((b²−a²)/b) sin³t)`.

**Eng.** `v × w = ab` is constant (`ellipse_cross`), so the square-root-free centre of
curvature `c + ((v₁²+v₂²)/(v×w)) • (−v₂, v₁)` is a rational expression in `sin t`,
`cos t`, and the identity collapses under `sin²t + cos²t = 1`. -/
theorem centerOfCurvature_ellipse (ha : a ≠ 0) (hb : b ≠ 0) (t : ℝ) :
    centerOfCurvature (ellipse a b t) (ellipseVel a b t) (ellipseAcc a b t)
      = ellipseEvolute a b t := by
  have hs2 : sin t ^ 2 = 1 - cos t ^ 2 := by linarith [sin_sq_add_cos_sq t]
  have hc2 : cos t ^ 2 = 1 - sin t ^ 2 := by linarith [sin_sq_add_cos_sq t]
  have hcross := ellipse_cross a b t
  -- The speed² `a²sin²t + b²cos²t` is rewritten purely in `cos t` for the first
  -- component and purely in `sin t` for the second; each is then a rational identity.
  have hnumC : (ellipseVel a b t).1 ^ 2 + (ellipseVel a b t).2 ^ 2
      = a ^ 2 * (1 - cos t ^ 2) + b ^ 2 * cos t ^ 2 := by
    show (-(a * sin t)) ^ 2 + (b * cos t) ^ 2 = _
    rw [← hs2]; ring
  have hnumS : (ellipseVel a b t).1 ^ 2 + (ellipseVel a b t).2 ^ 2
      = a ^ 2 * sin t ^ 2 + b ^ 2 * (1 - sin t ^ 2) := by
    show (-(a * sin t)) ^ 2 + (b * cos t) ^ 2 = _
    rw [← hc2]; ring
  simp only [centerOfCurvature]
  rw [hcross]
  refine Prod.ext ?_ ?_
  · rw [hnumC]
    show a * cos t + (a ^ 2 * (1 - cos t ^ 2) + b ^ 2 * cos t ^ 2) / (a * b) * -(b * cos t)
        = (a ^ 2 - b ^ 2) / a * cos t ^ 3
    field_simp
    ring
  · rw [hnumS]
    show b * sin t + (a ^ 2 * sin t ^ 2 + b ^ 2 * (1 - sin t ^ 2)) / (a * b) * -(a * sin t)
        = (b ^ 2 - a ^ 2) / b * sin t ^ 3
    field_simp
    ring

/-- The evolute's cusp on the positive major axis, `e(0) = ((a²−b²)/a, 0)`. -/
theorem ellipseEvolute_zero (a b : ℝ) : ellipseEvolute a b 0 = ((a ^ 2 - b ^ 2) / a, 0) := by
  simp [ellipseEvolute]

/-- The evolute's cusp on the negative major axis, `e(π) = (−(a²−b²)/a, 0)`. -/
theorem ellipseEvolute_pi (a b : ℝ) :
    ellipseEvolute a b Real.pi = (-((a ^ 2 - b ^ 2) / a), 0) := by
  simp only [ellipseEvolute, Real.cos_pi, Real.sin_pi, Prod.mk.injEq]
  norm_num

/-! ## The normals from the top and the bottom meet on the major axis -/

/-- **Math.** Petersen §3.2.5, Fig. 3.1, second sentence, made precise: the normal to
the ellipse at `t` and the normal at `−t` — a point of the top arc and its mirror image
on the bottom arc — **both** pass through the single major-axis point
`(((a²−b²)/a)·cos t, 0)`.  So the normals from the top and the bottom of the ellipse do
intersect along the major axis, as Petersen says.

**Eng.** On the normal `c(t) + s·(b cos t, a sin t)` the height is `b sin t + s a sin t`,
which vanishes (for `sin t ≠ 0`) exactly at `s = −b/a`, leaving the abscissa
`a cos t − (b²/a) cos t = ((a²−b²)/a) cos t`.  Since `cos(−t) = cos t`, the parameters
`t` and `−t` give the *same* point. -/
theorem mem_ellipseNormalLine_axis (ha : a ≠ 0) (t : ℝ) :
    (((a ^ 2 - b ^ 2) / a) * cos t, (0 : ℝ)) ∈ ellipseNormalLine a b t
      ∧ (((a ^ 2 - b ^ 2) / a) * cos t, (0 : ℝ)) ∈ ellipseNormalLine a b (-t) := by
  constructor
  · refine ⟨-(b / a), ?_⟩
    simp only [ellipse, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · field_simp; ring
    · field_simp; ring
  · refine ⟨-(b / a), ?_⟩
    simp only [ellipse, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq,
      cos_neg, sin_neg]
    refine ⟨?_, ?_⟩
    · field_simp; ring
    · field_simp; ring

/-- The major-axis crossing is *unique*: a point of the normal at `t` lying on the major
axis has abscissa `((a²−b²)/a)·cos t` — provided `sin t ≠ 0`, i.e. away from the two
vertices, where the normal *is* the major axis. -/
theorem axis_inter_eq (ha : a ≠ 0) {t : ℝ} (ht : sin t ≠ 0) {p : ℝ × ℝ}
    (hp : p ∈ ellipseNormalLine a b t) (hp2 : p.2 = 0) :
    p.1 = ((a ^ 2 - b ^ 2) / a) * cos t := by
  obtain ⟨s, rfl⟩ := hp
  simp only [ellipse, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul] at hp2 ⊢
  -- `b sin t + s * (a sin t) = 0` and `sin t ≠ 0` force `s = -b/a`
  have hs : s = -(b / a) := by
    have h : (b + s * a) * sin t = 0 := by linarith [hp2]
    rcases mul_eq_zero.mp h with h1 | h2
    · field_simp; linarith [h1]
    · exact absurd h2 ht
  rw [hs]
  field_simp
  ring

/-! ## The correction: those endpoints are not the foci -/

/-- **Math.** The endpoint of the focal segment, `(a²−b²)/a`, is **strictly less** than
the abscissa `√(a²−b²)` of the focus, for every genuine ellipse `0 < b < a`.

Hence the focal set — the segment between the evolute's two major-axis cusps — is
strictly contained in the segment joining the two foci, and Petersen's identification
of the two is false.

**Eng.** Write `c = √(a²−b²)`, so the claim is `c²/a < c`, i.e. `c < a`; and `c < a`
because `c² = a² − b² < a²` with `b > 0`. -/
theorem evolute_cusp_lt_focus (hb : 0 < b) (hab : b < a) :
    (a ^ 2 - b ^ 2) / a < √(a ^ 2 - b ^ 2) := by
  have ha : 0 < a := hb.trans hab
  have hpos : 0 < a ^ 2 - b ^ 2 := by nlinarith
  set c := √(a ^ 2 - b ^ 2) with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr hpos
  have hcsq : c ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt hpos.le
  -- `c < a`, since `c² = a² − b² < a²`
  have hca : c < a := by nlinarith [hcpos, ha]
  rw [← hcsq]
  rw [div_lt_iff₀ ha]
  nlinarith [hcpos, hca]

end EllipseEvolute

open EllipseEvolute in
/-- **Math.** Petersen §3.2.5, Fig. 3.1 (`rem:pet-ch3-conjugate-vs-focal-example`):
conjugate versus focal points for an ellipse `c(t) = (a cos t, b sin t)`, `0 < b < a`.

* `(1)` *Conjugate points occur along the evolute.*  The centre of curvature at `c(t)`
  — the point where the normals infinitesimally near `c(t)` meet, i.e. the conjugate
  point along the normal — is the evolute point
  `e(t) = (((a²−b²)/a) cos³t, ((b²−a²)/b) sin³t)`.
* `(2)` *The normals from the top and the bottom intersect along the major axis.*  The
  normal at `t` and the normal at `−t` both pass through `(((a²−b²)/a)·cos t, 0)`, and
  (for `sin t ≠ 0`) that is the only point of the normal at `t` on the major axis.  So
  the focal set is the segment swept by `((a²−b²)/a)·cos t`, whose endpoints `e(0)` and
  `e(π)` are the evolute's two cusps on the major axis.
* `(3)` *But that segment is not the one between the foci.*  Its endpoints are
  `±(a²−b²)/a`, while the foci sit at `±√(a²−b²)`, and `(a²−b²)/a < √(a²−b²)` strictly.

Part `(3)` corrects the remark: Petersen writes that "the focal set is the line between
the focal points of the ellipse", but the segment his own Fig. 3.1 draws — and that the
normals actually sweep — is strictly shorter, being the segment between the evolute's
cusps.  The slip is a conflation of the Riemannian *focal point* just defined ("a focal
point occurs when integral curves for `∇r` meet") with the two *conic foci*.

**Eng.** All three parts are elementary plane calculus; see the module docstring for the
altitude note (there is no `FocalPoint` definition in `PetersenLib` to state this at the
manifold level, so the link to `ConjugatePoint` is by prose). -/
theorem conjugateVsFocal_ellipse {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    (∀ t : ℝ, centerOfCurvature (ellipse a b t) (ellipseVel a b t) (ellipseAcc a b t)
        = ellipseEvolute a b t)
    ∧ (∀ t : ℝ, (((a ^ 2 - b ^ 2) / a) * cos t, (0 : ℝ)) ∈ ellipseNormalLine a b t
        ∧ (((a ^ 2 - b ^ 2) / a) * cos t, (0 : ℝ)) ∈ ellipseNormalLine a b (-t))
    ∧ (ellipseEvolute a b 0 = ((a ^ 2 - b ^ 2) / a, 0)
        ∧ ellipseEvolute a b Real.pi = (-((a ^ 2 - b ^ 2) / a), 0))
    ∧ (a ^ 2 - b ^ 2) / a < √(a ^ 2 - b ^ 2) := by
  have ha : (0 : ℝ) < a := hb.trans hab
  exact ⟨fun t => centerOfCurvature_ellipse ha.ne' hb.ne' t,
    fun t => mem_ellipseNormalLine_axis ha.ne' t,
    ⟨ellipseEvolute_zero a b, ellipseEvolute_pi a b⟩,
    evolute_cusp_lt_focus hb hab⟩

end PetersenLib
