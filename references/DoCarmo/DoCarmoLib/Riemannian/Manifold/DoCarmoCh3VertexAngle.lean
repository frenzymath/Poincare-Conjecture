import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3PiecewiseTransport

/-!
# do Carmo Chapter 3: the vertex angle of a broken curve

do Carmo's Definition 3.1 names, at each partition point `c(t_i)`, the *vertex
angle*: the angle between `lim_{t→t_i⁺} c'(t)` and `lim_{t→t_i⁻} c'(t)`.
`DoCarmoCh3Transport.lean` writes those one-sided velocities as `mfderivWithin`
on `Ici`/`Iic` and their metric angle as `vertexAngle`, and records existence in
the predicates `HasLeftVelocity` / `HasRightVelocity`.

That left the definition **unconstrained**: `mfderivWithin` returns a junk value
where the one-sided derivative does not exist, so `leftVelocity`/`rightVelocity`
are do Carmo's velocities only once existence is known — and the two predicates
that record existence had no producer anywhere in the library. Every use site
consumed a witness; nothing built one. So `vertexAngle` was a well-typed
expression with no theorem forcing it to be an angle between actual velocities.

This file supplies the producers, and then the vertex-angle statement Definition
3.3 needs.

## The two obstructions, and why neither survived

Both reasons the bridge was previously believed impossible turned out to be
false, so they are recorded here as the lemmas that refute them.

**The one-sided filter is not a stronger demand than the piece.**
`HasLeftVelocity` asks for the derivative within all of `Iic t`, while a
`Segmentation` controls the curve only on its own piece `[τ i, τ (i+1)]`. But
`mfderivWithin` depends on the set only through the neighbourhood filter it
generates, and `Icc a b =ᶠ[𝓝 b] Iic b` when `a < b` (`Icc_eventuallyEq_Iic`
below — on the neighbourhood `Ioi a` the two sets have the same elements). So
control on the piece *is* control within `Iic` at the endpoint; nothing outside
the piece is needed, and no half-neighbourhood hypothesis has to be added.

**The `smulRight` mismatch is a `One ℝ` instance path, not a type error.**
Converting a plain `MDifferentiableWithinAt` into the bundled predicate needs
`(id ℝ).smulRight (mfderivWithin … 1) = mfderivWithin …`.  This is **not** a `rfl`:
`smulRight` retypes its domain from `TangentSpace 𝓘(ℝ,ℝ) t` to plain `ℝ`, so the two
`1`s arrive by different instance paths (`Real.instOne` against the semiring-derived
one), and the goal can print as the tautology `(mfderiv[s] c t) 1 = (mfderiv[s] c t) 1`
while still failing.  What it *does* need is only `ext_ring` and then `one_smul` —
see `smulRight_mfderivWithin_one`.

Two corrections to earlier readings of this, both from audits, since the sequence is
the instructive part. It was first recorded as a `TangentSpace` obstruction that
five tactics could not touch: wrong object, and wrong conclusion. The fix then
over-corrected the other way, using a `change` to name the instance and claiming the
`change` was necessary: it is not, and it has been removed. `rfl` genuinely fails,
and so does `simp` after `ext_ring`; that is the whole of the difficulty.

## What the vertex angle is then good for

do Carmo's Definition 3.3 requires the boundary of a parametrized surface to have
vertex angles different from `π`. `IsNonPiAngle` states that condition for plane
vectors; `IsNonPiVertexAngle` below states it on the manifold, and
`isNonPiVertexAngle_iff_vertexAngle_ne_pi` proves it equivalent to
`vertexAngle ≠ π` — which is what makes the metric angle, and not just the
algebraic non-opposition, the object Definition 3.3 constrains.

## What the producer chain does and does not buy

One caveat, from an audit of this file, kept where it cannot be missed.
`mfderivWithin`'s junk value is `0`, so `leftVelocity c t ≠ 0` *by itself* implies
the derivative exists (`mdifferentiableWithinAt_Iic_of_leftVelocity_ne_zero`). Any
statement whose hypothesis is nonvanishing therefore gets existence for free, and
routing it through a `Segmentation` adds nothing.

The segmentation is not thereby pointless — it gives existence **without** assuming
nonvanishing, at every interior vertex, from the curve's regularity alone. But it is
useless for the angle statements specifically, because those need nonvanishing
anyway (`angle` returns `π/2` at a zero vector). The two routes are kept separate
for that reason, and no theorem pretends to combine them.
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped ContDiff Manifold Topology

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Riemannian.Geodesic

/-! ### A closed piece is a one-sided neighbourhood of each of its endpoints -/

/-- **Math.** Near its left endpoint, a nondegenerate closed interval and the
closed half-line agree: on the neighbourhood `Iio b` of `a`, membership in
`Icc a b` and in `Ici a` are the same condition.  Hence any notion of derivative
that depends on the set only through `𝓝[·] a` cannot tell them apart. -/
theorem Icc_eventuallyEq_Ici {a b : ℝ} (hab : a < b) : Icc a b =ᶠ[𝓝 a] Ici a := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [Iio_mem_nhds hab] with x hx
  simp only [mem_Icc, mem_Ici]
  exact ⟨And.left, fun h => ⟨h, le_of_lt hx⟩⟩

/-- **Math.** The same at the right endpoint: `Icc a b` and `Iic b` agree on the
neighbourhood `Ioi a` of `b`. -/
theorem Icc_eventuallyEq_Iic {a b : ℝ} (hab : a < b) : Icc a b =ᶠ[𝓝 b] Iic b := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [Ioi_mem_nhds hab] with x hx
  simp only [mem_Icc, mem_Iic]
  exact ⟨And.right, fun h => ⟨le_of_lt hx, h⟩⟩

end Riemannian.Geodesic

/-! ### When is the metric angle equal to `π`?

`vertexAngle` is `RiemannianMetric.angle`, an `arccos` of the normalized pairing.
Deciding `= π` therefore needs the sharp Cauchy–Schwarz bound with its equality
case, which the library did not have for `metricInner`. -/

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Cauchy–Schwarz for the Riemannian inner product:**
`g_x(V,W)² ≤ g_x(V,V) g_x(W,W)`, by nonnegativity of the quadratic
`t ↦ g_x(V + tW, V + tW)` and its discriminant. -/
theorem metricInner_sq_le_mul (g : RiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    g.metricInner x V W ^ 2 ≤ g.metricInner x V V * g.metricInner x W W := by
  have key : ∀ t : ℝ, 0 ≤ g.metricInner x W W * (t * t)
      + 2 * g.metricInner x V W * t + g.metricInner x V V := by
    intro t
    have h := g.metricInner_self_nonneg x (V + t • W)
    have expand : g.metricInner x (V + t • W) (V + t • W)
        = g.metricInner x W W * (t * t) + 2 * g.metricInner x V W * t
          + g.metricInner x V V := by
      simp only [metricInner_add_left, metricInner_add_right,
        metricInner_smul_left, metricInner_smul_right]
      rw [g.metricInner_comm x W V]
      ring
    rw [expand] at h
    exact h
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-- **Math.** The normalized pairing of two nonzero vectors is at least `-1`.
This is the half of Cauchy–Schwarz that `arccos` needs in order for the angle to
reach `π` only in the degenerate direction. -/
theorem neg_one_le_metricInner_div (g : RiemannianMetric I M) (x : M)
    {v w : TangentSpace I x} (hv : v ≠ 0) (hw : w ≠ 0) :
    -1 ≤ g.metricInner x v w /
      (Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w)) := by
  have hvv : 0 < g.metricInner x v v := g.metricInner_self_pos x v hv
  have hww : 0 < g.metricInner x w w := g.metricInner_self_pos x w hw
  have hsv : 0 < Real.sqrt (g.metricInner x v v) := Real.sqrt_pos.2 hvv
  have hsw : 0 < Real.sqrt (g.metricInner x w w) := Real.sqrt_pos.2 hww
  have hprod : 0 < Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w) :=
    mul_pos hsv hsw
  rw [le_div_iff₀ hprod]
  have hcs := metricInner_sq_le_mul (I := I) g x v w
  have hsq : (Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w)) ^ 2
      = g.metricInner x v v * g.metricInner x w w := by
    rw [mul_pow, Real.sq_sqrt hvv.le, Real.sq_sqrt hww.le]
  nlinarith [hcs, hprod, hsq]

/-- **Math.** **The equality case of Cauchy–Schwarz.**  If
`g_x(v,w)² = g_x(v,v) g_x(w,w)` and `v ≠ 0`, then `w` is a multiple of `v`, with
the coefficient forced to be `g_x(v,w)/g_x(v,v)`.  The proof is positive
definiteness applied to the residual `w - c • v`, whose length is `0` exactly
when equality holds. -/
theorem eq_smul_of_metricInner_sq_eq (g : RiemannianMetric I M) (x : M)
    {v w : TangentSpace I x} (hv : v ≠ 0)
    (heq : g.metricInner x v w ^ 2 = g.metricInner x v v * g.metricInner x w w) :
    w = (g.metricInner x v w / g.metricInner x v v) • v := by
  have hvv : 0 < g.metricInner x v v := g.metricInner_self_pos x v hv
  set c : ℝ := g.metricInner x v w / g.metricInner x v v with hc
  have hres : g.metricInner x (w - c • v) (w - c • v) = 0 := by
    simp only [metricInner_sub_left, metricInner_sub_right,
      metricInner_smul_left, metricInner_smul_right]
    rw [g.metricInner_comm x w v, hc]
    field_simp
    nlinarith [heq]
  by_contra hne
  exact absurd hres (ne_of_gt (g.metricInner_self_pos x _ (sub_ne_zero.2 hne)))

/-- **Math.** **The metric angle is `π` exactly for antiparallel vectors:** for
`v, w ≠ 0`, `∠(v,w) = π ↔ w = c • v` for some `c < 0`.

Forward: `arccos` reaches `π` only at `-1`, and the normalized pairing is `≥ -1`
by Cauchy–Schwarz, so equality holds in Cauchy–Schwarz and the equality case
gives the multiple, whose coefficient is negative because the pairing is.
Backward: the pairing of `v` with `c • v` is `c g_x(v,v)` and the normalizing
product is `(-c) g_x(v,v)`, so the quotient is exactly `-1`. -/
theorem angle_eq_pi_iff (g : RiemannianMetric I M) (x : M)
    {v w : TangentSpace I x} (hv : v ≠ 0) (hw : w ≠ 0) :
    g.angle x v w = Real.pi ↔ ∃ c : ℝ, c < 0 ∧ w = c • v := by
  have hvv : 0 < g.metricInner x v v := g.metricInner_self_pos x v hv
  have hww : 0 < g.metricInner x w w := g.metricInner_self_pos x w hw
  have hsv : 0 < Real.sqrt (g.metricInner x v v) := Real.sqrt_pos.2 hvv
  have hsw : 0 < Real.sqrt (g.metricInner x w w) := Real.sqrt_pos.2 hww
  have hprod : 0 < Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w) :=
    mul_pos hsv hsw
  have hsq : (Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w)) ^ 2
      = g.metricInner x v v * g.metricInner x w w := by
    rw [mul_pow, Real.sq_sqrt hvv.le, Real.sq_sqrt hww.le]
  rw [angle, Real.arccos_eq_pi]
  constructor
  · intro hle
    -- the quotient is `≤ -1` and `≥ -1`, hence `= -1`: equality in Cauchy–Schwarz
    have heq1 : g.metricInner x v w /
        (Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w)) = -1 :=
      le_antisymm hle (neg_one_le_metricInner_div (I := I) g x hv hw)
    rw [div_eq_iff (ne_of_gt hprod)] at heq1
    have hneg : g.metricInner x v w < 0 := by rw [heq1]; nlinarith [hprod]
    have hcs : g.metricInner x v w ^ 2 = g.metricInner x v v * g.metricInner x w w := by
      rw [heq1]; nlinarith [hsq]
    exact ⟨g.metricInner x v w / g.metricInner x v v,
      div_neg_of_neg_of_pos hneg hvv, eq_smul_of_metricInner_sq_eq (I := I) g x hv hcs⟩
  · rintro ⟨c, hcneg, rfl⟩
    have hcv : g.metricInner x v (c • v) = c * g.metricInner x v v := by
      rw [metricInner_smul_right]
    have hcc : g.metricInner x (c • v) (c • v) = c ^ 2 * g.metricInner x v v := by
      rw [metricInner_smul_left, metricInner_smul_right]; ring
    rw [hcv, hcc, show c ^ 2 * g.metricInner x v v
        = (-c) ^ 2 * g.metricInner x v v by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
    rw [div_le_iff₀ (mul_pos hsv (mul_pos (by linarith : (0 : ℝ) < -c) hsv))]
    have hs : Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x v v)
        = g.metricInner x v v := Real.mul_self_sqrt hvv.le
    nlinarith [hs, hvv]

end Riemannian.RiemannianMetric

namespace Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The bundled one-sided predicates, and their first producers -/

/-- **Math.** A one-dimensional derivative is determined by its value at `1`:
`(id ℝ).smulRight (L 1) = L` for `L` out of `TangentSpace 𝓘(ℝ,ℝ) t`.  This is the
bridge between the plain `mfderivWithin` and the bundled form
`HasLeftVelocity`/`HasRightVelocity` are stated in.

It does not close by `rfl`, because `smulRight` retypes the domain to plain `ℝ` and
the two occurrences of `1` then come by different `One ℝ` instance paths.  But it
needs no more than an `ext_ring` followed by `one_smul`: applying the maps to `1`
puts both sides in the same form.  (An audit checked whether a `change` naming the
intended instance was required here — it is not, and the version that used one has
been simplified away.  What is genuinely not enough is `rfl`, and `simp` after
`ext_ring` also leaves the goal open.) -/
theorem smulRight_mfderivWithin_one (c : ℝ → M) (s : Set ℝ) (t : ℝ) :
    (ContinuousLinearMap.id ℝ ℝ).smulRight (mfderivWithin 𝓘(ℝ, ℝ) I c s t (1 : ℝ))
      = mfderivWithin 𝓘(ℝ, ℝ) I c s t := by
  apply ContinuousLinearMap.ext_ring
  exact one_smul _ _

/-- **Math.** **Existence of do Carmo's incoming velocity.**  Left
differentiability at `t` makes `leftVelocity c t` an actual one-sided
derivative — i.e. it produces a `HasLeftVelocity` witness, which is what the
predicate was missing. -/
theorem hasLeftVelocity_leftVelocity {c : ℝ → M} {t : ℝ}
    (h : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I c (Iic t) t) :
    HasLeftVelocity (I := I) c t (leftVelocity (I := I) c t) := by
  unfold HasLeftVelocity leftVelocity
  rw [smulRight_mfderivWithin_one]
  exact h.hasMFDerivWithinAt

/-- **Math.** **Existence of do Carmo's outgoing velocity**, dually. -/
theorem hasRightVelocity_rightVelocity {c : ℝ → M} {t : ℝ}
    (h : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I c (Ici t) t) :
    HasRightVelocity (I := I) c t (rightVelocity (I := I) c t) := by
  unfold HasRightVelocity rightVelocity
  rw [smulRight_mfderivWithin_one]
  exact h.hasMFDerivWithinAt

/-- **Math.** A left velocity witness is unique: it is `leftVelocity`. -/
theorem hasLeftVelocity_iff_eq_leftVelocity {c : ℝ → M} {t : ℝ}
    {v : TangentSpace I (c t)}
    (h : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I c (Iic t) t) :
    HasLeftVelocity (I := I) c t v ↔ v = leftVelocity (I := I) c t :=
  ⟨fun hv => (leftVelocity_eq_of_hasLeftVelocity hv).symm,
    fun hv => hv ▸ hasLeftVelocity_leftVelocity h⟩

/-- **Math.** A right velocity witness is unique: it is `rightVelocity`. -/
theorem hasRightVelocity_iff_eq_rightVelocity {c : ℝ → M} {t : ℝ}
    {v : TangentSpace I (c t)}
    (h : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I c (Ici t) t) :
    HasRightVelocity (I := I) c t v ↔ v = rightVelocity (I := I) c t :=
  ⟨fun hv => (rightVelocity_eq_of_hasRightVelocity hv).symm,
    fun hv => hv ▸ hasRightVelocity_rightVelocity h⟩

/-! ### The velocities at a vertex of an actual broken curve

The producers above take one-sided differentiability as input.  A `Segmentation`
supplies it at every vertex: each piece is cut out of a curve differentiable in a
neighbourhood, so the segment's two-sided derivative at the breakpoint is the
curve's one-sided derivative there.  The transfer from the piece to the half-line
is `Icc_eventuallyEq_Ici` / `Icc_eventuallyEq_Iic` above — which is why no extra
half-neighbourhood hypothesis is needed. -/

variable {C : SubdividedCurveOfOrder I 1 M}

/-- **Math.** At the right endpoint of piece `i`, a segmented curve is
differentiable within `Iic`: segment `i` is differentiable everywhere and agrees
with the curve on the closed piece, and the piece is a left-neighbourhood of its
own right endpoint. -/
theorem mdifferentiableWithinAt_Iic_of_segmentation (S : Segmentation I M C)
    {i : ℕ} (hi : i < C.n) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I C.toFun (Iic (C.tau (i + 1))) (C.tau (i + 1)) :=
  (mdifferentiableWithinAt_congr_set (Icc_eventuallyEq_Iic (C.tau_strict i hi))).mp
    (mdifferentiableWithinAt_piece_right (I := I) S hi)

/-- **Math.** Dually at the left endpoint of piece `i`, within `Ici`. -/
theorem mdifferentiableWithinAt_Ici_of_segmentation (S : Segmentation I M C)
    {i : ℕ} (hi : i < C.n) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I C.toFun (Ici (C.tau i)) (C.tau i) :=
  (mdifferentiableWithinAt_congr_set (Icc_eventuallyEq_Ici (C.tau_strict i hi))).mp
    (mdifferentiableWithinAt_piece_left (I := I) S hi)

/-- **Math.** **do Carmo Def. 3.1: the incoming velocity exists at every
interior vertex.**  At the vertex `τ (i+1)` shared by pieces `i` and `i+1`, the
curve has a genuine left derivative, so `leftVelocity` there is the limit
`lim_{t→t_i⁻} c'(t)` of the book rather than a junk value. -/
theorem hasLeftVelocity_of_segmentation (S : Segmentation I M C) {i : ℕ}
    (hi : i < C.n) :
    HasLeftVelocity (I := I) C.toFun (C.tau (i + 1))
      (leftVelocity (I := I) C.toFun (C.tau (i + 1))) :=
  hasLeftVelocity_leftVelocity (mdifferentiableWithinAt_Iic_of_segmentation S hi)

/-- **Math.** **do Carmo Def. 3.1: the outgoing velocity exists at every
vertex**, dually: at `τ i` the curve has a genuine right derivative. -/
theorem hasRightVelocity_of_segmentation (S : Segmentation I M C) {i : ℕ}
    (hi : i < C.n) :
    HasRightVelocity (I := I) C.toFun (C.tau i)
      (rightVelocity (I := I) C.toFun (C.tau i)) :=
  hasRightVelocity_rightVelocity (mdifferentiableWithinAt_Ici_of_segmentation S hi)

/-- **Math.** At an interior vertex both one-sided velocities exist, so
`vertexAngle` at that vertex is the angle between two actual velocities — which
is do Carmo's vertex angle.  This is the statement the definition was missing:
`vertexAngle` is now constrained at the vertices of a segmented curve, not merely
well typed. -/
theorem hasVelocities_of_segmentation (S : Segmentation I M C) {i : ℕ}
    (hi : i + 1 < C.n) :
    HasLeftVelocity (I := I) C.toFun (C.tau (i + 1))
        (leftVelocity (I := I) C.toFun (C.tau (i + 1))) ∧
      HasRightVelocity (I := I) C.toFun (C.tau (i + 1))
        (rightVelocity (I := I) C.toFun (C.tau (i + 1))) :=
  ⟨hasLeftVelocity_of_segmentation S (Nat.lt_of_succ_lt hi),
    hasRightVelocity_of_segmentation S hi⟩

/-! ### The vertex-angle condition of Definition 3.3, on the manifold

do Carmo's Definition 3.3 requires the boundary of a parametrized surface to be a
piecewise differentiable curve *with vertex angles different from `π`*.
`IsNonPiAngle` (`DoCarmoCh3SurfaceBoundary.lean`) states that for plane vectors,
by non-opposition; the manifold-level condition was missing.

Both readings are stated below and proved equivalent: the algebraic one, which is
what a proof will normally destructure, and the metric one `vertexAngle ≠ π`,
which is what the book writes. The equivalence is what makes the metric angle the
object being constrained, rather than a parallel definition that happens to sit
next to it. -/

/-- **Math.** do Carmo Ch. 3, Def. 3.3: the **vertex angle at `t` differs from
`π`**, in the algebraic form — both one-sided velocities are nonzero and the
outgoing one is not a negative multiple of the incoming one.  This is the
manifold-level counterpart of `IsNonPiAngle` for plane vectors, and by
`isNonPiVertexAngle_iff_vertexAngle_ne_pi` it is exactly `vertexAngle ≠ π`.

Note both velocities are required nonzero: for a zero velocity, `angle` returns
the conventional `π/2`, so `vertexAngle ≠ π` would hold vacuously without saying
anything about a corner.

The predicate takes **no metric**, which is not an omission: non-opposition of two
tangent vectors is an affine condition, so — by
`isNonPiVertexAngle_iff_vertexAngle_ne_pi` — whether a vertex angle equals `π` is
independent of the Riemannian metric used to measure it.  `IsNonPiAngle` for plane
vectors is metric-free for the same reason. -/
def IsNonPiVertexAngle (c : ℝ → M) (t : ℝ) : Prop :=
  leftVelocity (I := I) c t ≠ 0 ∧ rightVelocity (I := I) c t ≠ 0 ∧
    ¬ ∃ a : ℝ, a < 0 ∧ rightVelocity (I := I) c t = a • leftVelocity (I := I) c t

/-- **Math.** The two readings of Definition 3.3's condition agree: given nonzero
one-sided velocities, the algebraic non-opposition is exactly `vertexAngle ≠ π`.

Since the left side does not mention `g`, this also says the vertex-angle
condition is the *same* condition for every Riemannian metric on `M`. -/
theorem isNonPiVertexAngle_iff_vertexAngle_ne_pi (g : RiemannianMetric I M)
    (c : ℝ → M) (t : ℝ)
    (hl : leftVelocity (I := I) c t ≠ 0) (hr : rightVelocity (I := I) c t ≠ 0) :
    IsNonPiVertexAngle (I := I) c t ↔ vertexAngle (I := I) g c t ≠ Real.pi := by
  have hpi : vertexAngle (I := I) g c t = Real.pi ↔
      ∃ a : ℝ, a < 0 ∧ rightVelocity (I := I) c t = a • leftVelocity (I := I) c t := by
    rw [vertexAngle_eq_angle_left_right]
    exact RiemannianMetric.angle_eq_pi_iff (I := I) g (c t) hl hr
  rw [IsNonPiVertexAngle, show (vertexAngle (I := I) g c t ≠ Real.pi)
    = ¬ (vertexAngle (I := I) g c t = Real.pi) from rfl, not_congr hpi]
  exact ⟨fun h => h.2.2, fun h => ⟨hl, hr, h⟩⟩

/-! #### Nonvanishing already implies existence

A fresh-context audit of this file caught something worth stating outright rather
than leaving implicit, because it changes what the producer chain above is for.

`mfderivWithin` returns `0` where the derivative does not exist.  So a *nonzero*
`leftVelocity` cannot be a junk value: `leftVelocity c t ≠ 0` implies
`MDifferentiableWithinAt … (Iic t) t` all by itself, with no segmentation and no
piece lemma.  Any theorem whose hypothesis is `leftVelocity ≠ 0` therefore gets
existence for free, and routing it through `hasVelocities_of_segmentation` adds
nothing — the earlier version of `isNonPiVertexAngle_iff_of_segmentation` did
exactly that, in a discarded `have`, which made the segmentation route look
load-bearing when it was not.

Both facts are worth having, and they answer different questions. Nonvanishing is
the cheap route to existence *at a vertex you already know is nondegenerate*;
the segmentation is the route to existence at *every* vertex, including ones where
the velocity might vanish, and it is the only one that follows from the curve's
regularity rather than from a hypothesis about the answer. -/

/-- **Math.** A nonzero one-sided velocity is automatically a genuine derivative:
`mfderivWithin`'s junk value is `0`, so a nonvanishing `leftVelocity` witnesses its
own existence. -/
theorem mdifferentiableWithinAt_Iic_of_leftVelocity_ne_zero {c : ℝ → M} {t : ℝ}
    (h : leftVelocity (I := I) c t ≠ 0) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I c (Iic t) t := by
  by_contra hc
  rw [leftVelocity, mfderivWithin_zero_of_not_mdifferentiableWithinAt hc] at h
  simp at h

/-- **Math.** The same on the right. -/
theorem mdifferentiableWithinAt_Ici_of_rightVelocity_ne_zero {c : ℝ → M} {t : ℝ}
    (h : rightVelocity (I := I) c t ≠ 0) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I c (Ici t) t := by
  by_contra hc
  rw [rightVelocity, mfderivWithin_zero_of_not_mdifferentiableWithinAt hc] at h
  simp at h

/-- **Math.** Consequently the nonvanishing hypotheses of
`isNonPiVertexAngle_iff_vertexAngle_ne_pi` carry existence with them: at a vertex
where `IsNonPiVertexAngle` holds, both one-sided velocities are genuine
derivatives.  So the predicate never asserts non-opposition between junk values. -/
theorem hasVelocities_of_isNonPiVertexAngle {c : ℝ → M} {t : ℝ}
    (h : IsNonPiVertexAngle (I := I) c t) :
    HasLeftVelocity (I := I) c t (leftVelocity (I := I) c t) ∧
      HasRightVelocity (I := I) c t (rightVelocity (I := I) c t) :=
  ⟨hasLeftVelocity_leftVelocity
      (mdifferentiableWithinAt_Iic_of_leftVelocity_ne_zero h.1),
    hasRightVelocity_rightVelocity
      (mdifferentiableWithinAt_Ici_of_rightVelocity_ne_zero h.2.1)⟩

/-! #### Which route to existence is the useful one

`hasVelocities_of_segmentation` (above) and `hasVelocities_of_isNonPiVertexAngle`
both produce witnesses, and the difference between them is the whole point.

The segmentation route is **unconditional**: it covers every interior vertex,
including one where a velocity vanishes because the curve momentarily stops, and it
derives existence from the curve's own regularity. The nonvanishing route needs
`leftVelocity ≠ 0`, which is a hypothesis about the answer, and it says nothing at a
degenerate vertex.

So a statement about the vertex *angle* — which needs nonvanishing anyway, since
`angle` returns `π/2` at a zero vector — gets its existence for free and does not
need the segmentation. That is the substance of the audit finding: an earlier
version of this file stated an `iff` here with `≠ 0` hypotheses and invoked the
chain in a discarded `have`, which made the segmentation look load-bearing when the
hypotheses had already done its work. There is no honest theorem combining the two,
so none is stated; the segmentation's payoff is existence where nonvanishing is
*not* assumed, and that is `hasVelocities_of_segmentation` itself. -/

/-! ### The condition is two-sided

A predicate can be faithful and still be worthless if it is vacuously true or
unsatisfiable, and a sorry-free build does not distinguish those cases.  The two
lemmas below pin `IsNonPiVertexAngle` down from both sides: it *fails* at a cusp
and *holds* at a corner-free point. -/

/-- **Math.** The condition genuinely excludes a cusp: if the outgoing velocity is
the negative of the incoming one, `IsNonPiVertexAngle` fails.  So the predicate is
not vacuously true.

No nonvanishing hypothesis is needed here — if the incoming velocity is `0` the
outgoing one is too, and the predicate fails on its first clause instead.
`vertexAngle_eq_pi_of_reversed` is the sharper statement for the nondegenerate
case, where the failure is the angle itself. -/
theorem not_isNonPiVertexAngle_of_reversed {c : ℝ → M} {t : ℝ}
    (hcusp : rightVelocity (I := I) c t = (-1 : ℝ) • leftVelocity (I := I) c t) :
    ¬ IsNonPiVertexAngle (I := I) c t := fun h =>
  h.2.2 ⟨-1, by norm_num, hcusp⟩

/-- **Math.** At a cusp with nonzero incoming velocity the vertex angle is exactly
`π`, so `vertexAngle` attains the value do Carmo's Definition 3.3 rules out.  With
`isNonPiVertexAngle_of_eq` (angle `0`) this shows the vertex angle is not pinned to
one value by the definitions: both the excluded and the permitted case occur. -/
theorem vertexAngle_eq_pi_of_reversed (g : RiemannianMetric I M) {c : ℝ → M} {t : ℝ}
    (hne : leftVelocity (I := I) c t ≠ 0)
    (hcusp : rightVelocity (I := I) c t = (-1 : ℝ) • leftVelocity (I := I) c t) :
    vertexAngle (I := I) g c t = Real.pi := by
  have hr : rightVelocity (I := I) c t ≠ 0 := by
    rw [hcusp]
    simpa using hne
  rw [vertexAngle_eq_angle_left_right]
  exact (RiemannianMetric.angle_eq_pi_iff (I := I) g (c t) hne hr).2
    ⟨-1, by norm_num, hcusp⟩

/-- **Math.** The condition is satisfiable: at a point where the two one-sided
velocities agree and are nonzero — a corner-free point, angle `0` — it holds.  A
positive multiple of a nonzero vector is never a negative multiple of it. -/
theorem isNonPiVertexAngle_of_eq {c : ℝ → M} {t : ℝ}
    (hne : leftVelocity (I := I) c t ≠ 0)
    (hsmooth : rightVelocity (I := I) c t = leftVelocity (I := I) c t) :
    IsNonPiVertexAngle (I := I) c t := by
  refine ⟨hne, by rw [hsmooth]; exact hne, ?_⟩
  rintro ⟨a, ha, heq⟩
  rw [hsmooth] at heq
  have hz : (1 - a) • leftVelocity (I := I) c t = 0 := by
    rw [sub_smul, one_smul, ← heq, sub_self]
  rcases smul_eq_zero.1 hz with h1 | h2
  · exact absurd h1 (by intro h; rw [sub_eq_zero] at h; linarith)
  · exact hne h2

end Riemannian.Geodesic
