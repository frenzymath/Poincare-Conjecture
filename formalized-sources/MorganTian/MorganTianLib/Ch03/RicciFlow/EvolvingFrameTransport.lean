import MorganTianLib.Ch03.RicciFlow.EvolvingFrame

/-!
# Morgan--Tian Ch. 3 -- transport-to-frame bridge

The transport formulation and the finite moving-frame formulation encode the
same Ricci-dual ODE.  This module records the direct passage from a transport
operator to a frame indexed by any finite set of initial vectors.  The result
is useful when a curvature-component estimate is stated in frame coordinates
but the available ODE producer is an operator-valued transport.
-/

open Set

noncomputable section

namespace MorganTianLib

/-! ## Turning transport data into frame data -/

/-- **Math.** Apply an evolving transport to a finite family of initial vectors. -/
def EvolvingTransportData.toFrameData
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G) (basis : ι → V) :
    EvolvingFrameData V ι J G :=
  { frame := fun t a => P.transport t (basis a)
    dualRicci := P.dualRicci
    frame_deriv := fun t a => P.transport_deriv t (basis a)
    dualRicci_left := P.dualRicci_left
    dualRicci_right := P.dualRicci_right }

@[simp] theorem EvolvingTransportData.toFrameData_frame
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G) (basis : ι → V) (t : ℝ) (a : ι) :
    (P.toFrameData basis).frame t a = P.transport t (basis a) := rfl

@[simp] theorem EvolvingTransportData.toFrameData_dualRicci
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G) (basis : ι → V) (t : ℝ) :
    (P.toFrameData basis).dualRicci t = P.dualRicci t := rfl

/-- **Math.** Initial orthonormality of the seed family is propagated by transport. -/
theorem EvolvingTransportData.isOrthonormal_toFrameData
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G) (basis : ι → V)
    (hinit : ∀ a b, G.metric 0 (basis a) (basis b) = if a = b then 1 else 0)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsOrthonormalEvolvingFrame (P.toFrameData basis) t := by
  have hzero : IsOrthonormalEvolvingFrame (P.toFrameData basis) 0 := by
    intro a b
    change G.metric 0 (P.transport 0 (basis a)) (P.transport 0 (basis b)) = _
    rw [P.transport_zero]
    simp only [ContinuousLinearMap.id_apply]
    by_cases hab : a = b
    · subst b
      simpa using hinit a a
    · simpa [hab] using hinit a b
  exact evolvingFrame_isOrthonormal_of_initial (P.toFrameData basis) hT hzero ht

/-! ## A nondegeneracy consequence of metric preservation -/

/-- **Math.**
If the initial bilinear form has no nonzero isotropic vectors, transport is
injective at every time for which the pullback identity is available.
This is stated with the precise algebraic hypothesis needed by the proof, so
it does not hide positive-definiteness behind a certificate.
-/
theorem EvolvingTransportData.injective_of_initial_metric_nondegenerate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G)
    (hnd : ∀ v : V, G.metric 0 v v = 0 → v = 0)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Function.Injective (P.transport t) := by
  intro v w hvw
  have hzero : P.transport t (v - w) = 0 := by
    rw [map_sub, hvw]
    simp
  have hp := evolvingTransport_pullback_metric_constant P hT ht (v - w) (v - w)
  rw [hzero] at hp
  have hmetric : G.metric 0 (v - w) (v - w) = 0 := by
    simpa using hp.symm
  exact sub_eq_zero.mp (hnd (v - w) hmetric)

end MorganTianLib

end
