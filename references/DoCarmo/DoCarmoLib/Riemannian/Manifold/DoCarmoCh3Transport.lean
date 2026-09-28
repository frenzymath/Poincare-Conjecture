import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3
import DoCarmoLib.Riemannian.Jacobi.ParallelFieldAlong

/-!
# do Carmo Chapter 3: vertices and piecewise parallel transport

The piecewise-curve definition in `DoCarmoCh3` records the finite partition and
the `C¹` regularity on each piece.  This file adds the two constructions that
do Carmo uses immediately afterwards:

* one-sided velocities at a vertex, represented by `mfderivWithin` on `Iic` and
  `Ici`, and their metric angle;
* a relation saying that an own-foot field is parallel on every member of a
  finite partition, together with the induced endpoint transport relation.

**The transport relation in this file is defective and superseded.**  It imposes
the parallel-transport ODE at the endpoints of each closed piece, using the
two-sided `deriv` of the chart reading — which does not exist at a corner, so
the condition degenerates there instead of constraining transport.  Both
predicates carry the details in their own docstrings.  The corrected definition,
with the existence and uniqueness theorems do Carmo's Definition 3.1 asserts, is
`DoCarmoCh3PiecewiseTransport.lean`.  The vertex/velocity material above is
unaffected.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace Riemannian

namespace RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Math.** The (unoriented) angle between two tangent vectors for a
Riemannian metric.  As in the usual inner-product definition, a zero vector
gives the conventional value `π / 2`. -/
def angle (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) : ℝ :=
  Real.arccos
    (g.metricInner x v w /
      (Real.sqrt (g.metricInner x v v) * Real.sqrt (g.metricInner x w w)))

/-- **Math.** The metric angle is symmetric. -/
theorem angle_comm (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.angle x v w = g.angle x w v := by
  unfold angle
  rw [g.metricInner_comm, mul_comm]

@[simp]
theorem angle_zero_left (g : RiemannianMetric I M) (x : M)
    (w : TangentSpace I x) : g.angle x 0 w = Real.pi / 2 := by
  unfold angle
  rw [g.metricInner_zero_left, zero_div, Real.arccos_zero]

@[simp]
theorem angle_zero_right (g : RiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : g.angle x v 0 = Real.pi / 2 := by
  unfold angle
  rw [g.metricInner_zero_right, zero_div, Real.arccos_zero]

end RiemannianMetric

namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Math.** The left one-sided velocity of a curve at `t`, obtained by
the derivative on the half-line `(-∞, t]`. -/
def leftVelocity (c : ℝ → M) (t : ℝ) : TangentSpace I (c t) :=
  mfderivWithin 𝓘(ℝ, ℝ) I c (Iic t) t (1 : ℝ)

/-- **Math.** The right one-sided velocity of a curve at `t`, obtained by
the derivative on the half-line `[t, ∞)`. -/
def rightVelocity (c : ℝ → M) (t : ℝ) : TangentSpace I (c t) :=
  mfderivWithin 𝓘(ℝ, ℝ) I c (Ici t) t (1 : ℝ)

/-- **Math.** A specified tangent vector is the left derivative of a curve at a vertex. -/
def HasLeftVelocity (c : ℝ → M) (t : ℝ)
    (v : TangentSpace I (c t)) : Prop :=
  HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (Iic t) t
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- **Math.** A specified tangent vector is the right derivative of a curve at a vertex. -/
def HasRightVelocity (c : ℝ → M) (t : ℝ)
    (v : TangentSpace I (c t)) : Prop :=
  HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c (Ici t) t
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

private theorem velocity_eq_of_has_deriv
    {c : ℝ → M} {t : ℝ} {s : Set ℝ} {v : TangentSpace I (c t)}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I c s t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v))
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    (mfderivWithin 𝓘(ℝ, ℝ) I c s t) (1 : ℝ) = v := by
  have hh := h.mfderivWithin hs
  have hv := congrArg (fun L => L (1 : ℝ)) hh
  change (mfderivWithin 𝓘(ℝ, ℝ) I c s t) 1 =
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v) 1 at hv
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] at hv
  exact hv

/-- **Math.** The left velocity agrees with any derivative witness. -/
theorem leftVelocity_eq_of_hasLeftVelocity
    {c : ℝ → M} {t : ℝ} {v : TangentSpace I (c t)}
    (h : HasLeftVelocity (I := I) c t v) :
    leftVelocity (I := I) c t = v := by
  exact velocity_eq_of_has_deriv h (uniqueDiffWithinAt_Iic t).uniqueMDiffWithinAt

/-- **Math.** The right velocity agrees with any derivative witness. -/
theorem rightVelocity_eq_of_hasRightVelocity
    {c : ℝ → M} {t : ℝ} {v : TangentSpace I (c t)}
    (h : HasRightVelocity (I := I) c t v) :
    rightVelocity (I := I) c t = v := by
  exact velocity_eq_of_has_deriv h (uniqueDiffWithinAt_Ici t).uniqueMDiffWithinAt

/-- **Math.** At an interior vertex of a piecewise differentiable curve, the
vertex angle is the metric angle between its outgoing and incoming one-sided
velocities. -/
def vertexAngle (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ) : ℝ :=
  g.angle (c t) (rightVelocity (I := I) c t) (leftVelocity (I := I) c t)

/-- **Math.** Swapping incoming and outgoing velocities does not change the vertex angle. -/
theorem vertexAngle_eq_angle_left_right (g : RiemannianMetric I M)
    (c : ℝ → M) (t : ℝ) :
    vertexAngle (I := I) g c t =
      g.angle (c t) (leftVelocity (I := I) c t) (rightVelocity (I := I) c t) := by
  exact RiemannianMetric.angle_comm g (c t)
    (rightVelocity (I := I) c t) (leftVelocity (I := I) c t)

/-! ### Piecewise parallel fields and endpoint transport -/

/-- **Math.** An own-foot field is piecewise parallel along `c` on `[a,b]` if
`c` has a finite strict differentiability partition and the field is parallel
on every partition segment.  Requiring one global own-foot field records the
matching condition at each vertex.

**Defective; do not build on this.**  Use
`Riemannian.Geodesic.IsPiecewiseParallelAlong` in
`DoCarmoCh3PiecewiseTransport.lean`, which carries the existence and uniqueness
theorems.  The problem is at the corners: `Jacobi.IsParallelFieldAlongOn` on the
*closed* piece `[τ i, τ (i+1)]` imposes its ODE at every point of that piece,
with the coefficient built from the **two-sided** `deriv` of the chart reading.
At an interior breakpoint of a curve that genuinely breaks, that derivative does
not exist, so `deriv` returns `0` and — the Christoffel contraction being linear
in that slot — the condition imposed at the corner degenerates instead of
constraining transport.  See
`chartChristoffelContraction_deriv_eq_zero_of_not_differentiableAt`.  Nothing
was proved from the bad clause, since this predicate has no consumers. -/
def IsPiecewiseParallelFieldAlongOn (g : RiemannianMetric I M)
    (c : ℝ → M) (w : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧
    ∃ (n : ℕ) (τ : ℕ → ℝ), 0 < n ∧ τ 0 = a ∧ τ n = b ∧
      (∀ i < n, τ i < τ (i + 1)) ∧
      (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc (τ i) (τ (i + 1)))) ∧
      ∀ i < n,
        Jacobi.IsParallelFieldAlongOn (I := I) g c w (τ i) (τ (i + 1))

/-- **Math.** Endpoint transport along a piecewise differentiable curve is
the relation obtained by evaluating a piecewise parallel field at the two
endpoints.

**Defective; do not build on this** — it inherits the corner problem of
`IsPiecewiseParallelFieldAlongOn` above.  The successive-transport content of do
Carmo's definition is now a theorem, for a corrected predicate, in
`DoCarmoCh3PiecewiseTransport.lean`: `exists_isPiecewiseParallelAlong` and
`isPiecewiseParallelAlong_unique`, with the transport map itself given by
`piecewiseTransport`. -/
def IsPiecewiseParallelTransport (g : RiemannianMetric I M)
    (c : ℝ → M) (a b : ℝ)
    (v₀ : TangentSpace I (c a)) (v₁ : TangentSpace I (c b)) : Prop :=
  ∃ w : ℝ → E,
    IsPiecewiseParallelFieldAlongOn (I := I) g c w a b ∧
      (w a : TangentSpace I (c a)) = v₀ ∧
      (w b : TangentSpace I (c b)) = v₁

/-- **Math.** The field's underlying curve is piecewise differentiable. -/
theorem IsPiecewiseParallelFieldAlongOn.isPiecewiseDifferentiableCurve
    {g : RiemannianMetric I M} {c : ℝ → M} {w : ℝ → E} {a b : ℝ}
    (h : IsPiecewiseParallelFieldAlongOn (I := I) g c w a b) :
    IsPiecewiseDifferentiableCurve (I := I) c a b :=
  by
    rcases h with ⟨hcont, ⟨n, τ, hn, hτ0, hτn, hstrict, hsmooth, _⟩⟩
    exact ⟨hcont, ⟨n, τ, hn, hτ0, hτn, hstrict, hsmooth⟩⟩

/-- **Math.** Endpoint transport is exactly the existence of a witnessing field. -/
theorem isPiecewiseParallelTransport_iff
    {g : RiemannianMetric I M} {c : ℝ → M} {a b : ℝ}
    {v₀ : TangentSpace I (c a)} {v₁ : TangentSpace I (c b)} :
    IsPiecewiseParallelTransport (I := I) g c a b v₀ v₁ ↔
      ∃ w : ℝ → E,
        IsPiecewiseParallelFieldAlongOn (I := I) g c w a b ∧
          (w a : TangentSpace I (c a)) = v₀ ∧
          (w b : TangentSpace I (c b)) = v₁ :=
  Iff.rfl

end Geodesic
end Riemannian
