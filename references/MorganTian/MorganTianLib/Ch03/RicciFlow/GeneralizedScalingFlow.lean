import MorganTianLib.Ch03.RicciFlow.GeneralizedScalingEquationBridge
import MorganTianLib.Ch03.RicciFlow.GeneralizedScalingTransport

/-!
# Morgan--Tian Ch. 3 - affine transport of generalized Ricci flows

This module packages the already checked affine space-time and ordinary-chart
equation transports into a genuine generalized Ricci-flow transport.  The
horizontal metric is scaled on the changed time vector field, while each
adapted chart is pulled back by the inverse affine product map.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian TopologicalSpace

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

noncomputable local instance [NeZero n] :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
  ⟨by simpa using (NeZero.out : n ≠ 0)⟩

/-- **Math.** The affine scaling changes the time differential by the positive
factor, so its kernel (the horizontal distribution) is unchanged. -/
theorem GeneralizedSpaceTime.affineTimeChange_isHorizontal_iff
    {S : GeneralizedSpaceTime n (N := N)} (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (x : N) (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    (S.affineTimeChange n Q hQ a).IsHorizontal n x v ↔
      S.IsHorizontal n x v := by
  rw [GeneralizedSpaceTime.IsHorizontal,
    GeneralizedSpaceTime.IsHorizontal,
    GeneralizedSpaceTime.affineTimeChange_timeDifferential_eq]
  constructor
  · intro hv
    have hv' : Q * S.timeDifferential (n := n) x v = 0 := by
      simpa only [smul_apply, smul_eq_mul] using hv
    rcases mul_eq_zero.mp hv' with hQ0 | hv0
    · exact (hQ.ne' hQ0).elim
    · exact hv0
  · intro hv
    simp only [smul_apply, smul_eq_mul, hv, mul_zero]

/-- **Math.** Positive constant scaling of a horizontal metric, transported to the
affine-changed time vector and time differential. -/
def GeneralizedSpaceTime.HorizontalMetric.affineTimeChange
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (S.affineTimeChange n Q hQ a).HorizontalMetric n where
  inner x := Q • G.inner x
  symm x v w := by
    simp only [smul_apply, smul_eq_mul]
    rw [G.symm x v w]
  timeVector_null x v := by
    rw [GeneralizedSpaceTime.affineTimeChange_timeVector]
    simp only [smul_apply, map_smul, smul_eq_mul]
    rw [G.timeVector_null]
    ring
  pos x v hv hv0 := by
    simp only [smul_apply, smul_eq_mul]
    exact mul_pos hQ (G.pos x v
      ((S.affineTimeChange_isHorizontal_iff n Q hQ a x v).mp hv) hv0)
  smooth := G.smooth.const_smul_section

@[simp]
theorem GeneralizedSpaceTime.HorizontalMetric.affineTimeChange_inner
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (x : N)
    (v w : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    (G.affineTimeChange n Q hQ a).inner x v w = Q * G.inner x v w :=
  rfl

/- The inverse affine product map leaves the spatial coordinate unchanged.
Consequently, the spatial plaque in the transported chart is the old plaque
at the inverse-transformed time. -/
theorem GeneralizedSpaceTimeLocalChart.affineTimeChange_spatialPlaque_eq
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    (fun q : c.spatialOpens n =>
        (affineTimeChangeChart n c Q hQ a)
          ((q : EuclideanSpace ℝ (Fin n)), s)) =
      (fun q : c.spatialOpens n =>
        c.equiv ((q : EuclideanSpace ℝ (Fin n)), (s - a) / Q)) := by
  funext q
  simp only [affineTimeChangeChart]
  change c.equiv
      ((affineTimeProductDiffeomorph
        (E := EuclideanSpace ℝ (Fin n)) Q a hQ.ne').symm.toEquiv
        ((q : EuclideanSpace ℝ (Fin n)), s)) = _
  let A := affineTimeProductDiffeomorph
      (E := EuclideanSpace ℝ (Fin n)) Q a hQ.ne'
  have hprod := A.toEquiv.apply_symm_apply
    ((q : EuclideanSpace ℝ (Fin n)), s)
  change A.toEquiv (A.symm.toEquiv
      ((q : EuclideanSpace ℝ (Fin n)), s)) =
    ((q : EuclideanSpace ℝ (Fin n)), s) at hprod
  have hAapply (u : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      A.toEquiv (u, t) = (u, Q * t + a) := by
    simpa [A] using affineTimeProductDiffeomorph_apply
      (E := EuclideanSpace ℝ (Fin n)) Q a hQ.ne' u t
  rw [hAapply] at hprod
  have hfirst : (A.symm.toEquiv
      ((q : EuclideanSpace ℝ (Fin n)), s)).1 =
        (q : EuclideanSpace ℝ (Fin n)) := by
    have h := congrArg Prod.fst hprod
    simpa [A, affineTimeProductDiffeomorph_apply] using h
  have hsecond : Q * (A.symm.toEquiv
      ((q : EuclideanSpace ℝ (Fin n)), s)).2 + a = s := by
    have h := congrArg Prod.snd hprod
    simpa [A, affineTimeProductDiffeomorph_apply] using h
  have hcoord :
      A.symm.toEquiv
          ((q : EuclideanSpace ℝ (Fin n)), s) =
        ((q : EuclideanSpace ℝ (Fin n)), (s - a) / Q) := by
    apply Prod.ext
    · exact hfirst
    · apply (eq_div_iff hQ.ne').2
      nlinarith [hsecond]
  rw [hcoord]

theorem GeneralizedSpaceTimeLocalChart.affineTimeChange_spatialDifferential
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) (p : c.spatialOpens n) :
    mfderiv
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersEuclideanHalfSpace n.succ)
        (fun q : c.spatialOpens n =>
          (affineTimeChangeChart n c Q hQ a)
            ((q : EuclideanSpace ℝ (Fin n)), s)) p =
      mfderiv
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersEuclideanHalfSpace n.succ)
        (fun q : c.spatialOpens n =>
          c.equiv ((q : EuclideanSpace ℝ (Fin n)), (s - a) / Q)) p := by
  rw [c.affineTimeChange_spatialPlaque_eq n Q hQ a s]

/- The local chart witnesses in the generalized-flow equation transport by the
ordinary parabolic rescaling theorem. -/
noncomputable def GeneralizedRicciFlow.affineTimeChange
    [NeZero n] (F : GeneralizedRicciFlow n (N := N))
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    GeneralizedRicciFlow n (N := N) := by
  classical
  refine
    { spaceTime := F.spaceTime.affineTimeChange n Q hQ a
      metric := F.metric.affineTimeChange n Q hQ a
      equation := ?_ }
  intro x
  let c := F.spaceTime.localProduct x
  let g := Classical.choose (F.equation x)
  have hg := Classical.choose_spec (F.equation x)
  obtain ⟨hreal, heq⟩ := hg
  let g' : ℝ → RiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (c.spatialOpens n) :=
    fun s => parabolicRescaledMetricFamily g Q hQ a s
  refine ⟨g', ?_, ?_⟩
  · intro s hs p v w
    have ht : (s - a) / Q ∈ c.timeSource := by
      exact parabolicRescaledMetricFamily_sourceTime_mem Q hQ a hs
    have hbase := hreal ((s - a) / Q) ht p v w
    have hpoint :
        ((F.spaceTime.affineTimeChange n Q hQ a).localProduct x).equiv
            ((p : EuclideanSpace ℝ (Fin n)), s) =
          c.equiv ((p : EuclideanSpace ℝ (Fin n)), (s - a) / Q) := by
      change (affineTimeChangeChart n c Q hQ a)
          ((p : EuclideanSpace ℝ (Fin n)), s) = _
      exact congrFun (c.affineTimeChange_spatialPlaque_eq n Q hQ a s) p
    have hdv :
        ((F.spaceTime.affineTimeChange n Q hQ a).localProduct x).spatialDifferential
            n s p v = c.spatialDifferential n ((s - a) / Q) p v := by
      change
        (mfderiv
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersEuclideanHalfSpace n.succ)
            (fun q : c.spatialOpens n =>
              (affineTimeChangeChart n c Q hQ a)
                ((q : EuclideanSpace ℝ (Fin n)), s)) p) v = _
      exact congrArg (fun L => L v)
        (c.affineTimeChange_spatialDifferential n Q hQ a s p)
    have hdw :
        ((F.spaceTime.affineTimeChange n Q hQ a).localProduct x).spatialDifferential
            n s p w = c.spatialDifferential n ((s - a) / Q) p w := by
      change
        (mfderiv
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersEuclideanHalfSpace n.succ)
            (fun q : c.spatialOpens n =>
              (affineTimeChangeChart n c Q hQ a)
                ((q : EuclideanSpace ℝ (Fin n)), s)) p) w = _
      exact congrArg (fun L => L w)
        (c.affineTimeChange_spatialDifferential n Q hQ a s p)
    change
        (parabolicRescaledMetricFamily g Q hQ a s).metricInner p v w =
        (F.metric.affineTimeChange n Q hQ a).inner
          (((F.spaceTime.affineTimeChange n Q hQ a).localProduct x).equiv
            ((p : EuclideanSpace ℝ (Fin n)), s))
          (((F.spaceTime.affineTimeChange n Q hQ a).localProduct x).spatialDifferential
            n s p v)
          (((F.spaceTime.affineTimeChange n Q hQ a).localProduct x).spatialDifferential
            n s p w)
    rw [parabolicRescaledMetricFamily_metricInner]
    rw [GeneralizedSpaceTime.HorizontalMetric.affineTimeChange_inner]
    change Q * (g ((s - a) / Q)).metricInner p v w = _
    rw [hbase]
    rw [hdv, hdw, hpoint]
  · intro s hs p v w
    exact
      (c.isRicciFlowEquationOn_parabolicRescaledMetricFamily n heq Q hQ a
        s hs p v w)

end MorganTianLib

end
