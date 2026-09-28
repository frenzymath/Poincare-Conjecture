import MorganTianLib.Ch03.RicciFlow.EvolvingTransportOn

/-!
# Morgan--Tian Ch. 3 -- operator regularity of evolving transport

The compact-interval ODE construction initially controls the transported image
of each fixed vector.  Finite dimensionality lets us assemble the solutions of
a basis into one curve of continuous linear maps and upgrade the pointwise ODE
to a derivative in the operator-norm topology.
-/

open Set
open scoped NNReal

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-- **Math.** The continuous equivalence that reconstructs an endomorphism from its
values on the fixed finite basis. -/
private noncomputable def finBasisOperatorEquiv :
    (Fin (Module.finrank ℝ V) → V) ≃L[ℝ] (V →L[ℝ] V) :=
  (((Module.finBasis ℝ V).constr ℝ).trans
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := V))).toContinuousLinearEquiv

omit [CompleteSpace V] in
private theorem finBasisOperatorEquiv_apply_basis
    (f : Fin (Module.finrank ℝ V) → V) (i : Fin (Module.finrank ℝ V)) :
    finBasisOperatorEquiv f ((Module.finBasis ℝ V) i) = f i := by
  simp [finBasisOperatorEquiv]

/-- **Math.** The operator-valued curve obtained by assembling the ODE
solutions starting at a finite basis.  Outside the interval it is only an
auxiliary extension; on the interval it agrees with `evolvingTransportOn`. -/
noncomputable def evolvingTransportCurveOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (t : ℝ) : V →L[ℝ] V :=
  finBasisOperatorEquiv (fun i =>
    Riemannian.LinearODE.solOf hab hcont hK ((Module.finBasis ℝ V) i) t)

/-- **Math.** On the controlled interval, applying the operator-valued curve is exactly
the original solution with the requested initial vector. -/
@[simp] theorem evolvingTransportCurveOn_apply_of_mem
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) (v : V) :
    evolvingTransportCurveOn A hab hcont hK t v =
      Riemannian.LinearODE.solOf hab hcont hK v t := by
  rw [← evolvingTransportOn_apply A hab hcont hK ⟨t, ht⟩ v]
  have hmaps : evolvingTransportCurveOn A hab hcont hK t =
      evolvingTransportOn A hab hcont hK ⟨t, ht⟩ := by
    apply ContinuousLinearMap.coe_injective
    apply (Module.finBasis ℝ V).ext
    intro i
    simp [evolvingTransportCurveOn, finBasisOperatorEquiv_apply_basis]
  exact congrArg (fun T : V →L[ℝ] V => T v) hmaps

/-- **Math.** The compact-interval transport solves the linear ODE as a curve
in the operator-norm space of continuous endomorphisms, not merely after
evaluation on each fixed vector. -/
theorem evolvingTransportCurveOn_hasDerivWithinAt
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt
      (evolvingTransportCurveOn A hab hcont hK)
      ((A t).comp (evolvingTransportCurveOn A hab hcont hK t))
      (Icc a b) t := by
  have hcoord : HasDerivWithinAt
      (fun s : ℝ => fun i : Fin (Module.finrank ℝ V) =>
        Riemannian.LinearODE.solOf hab hcont hK ((Module.finBasis ℝ V) i) s)
      (fun i : Fin (Module.finrank ℝ V) =>
        A t (Riemannian.LinearODE.solOf hab hcont hK ((Module.finBasis ℝ V) i) t))
      (Icc a b) t := by
    rw [hasDerivWithinAt_pi]
    intro i
    exact evolvingTransportOn_hasDerivWithinAt A hab hcont hK _ ht
  have hraw :=
    (finBasisOperatorEquiv (V := V)).hasFDerivAt.comp_hasDerivWithinAt t hcoord
  convert hraw using 1 <;> try rfl
  apply ContinuousLinearMap.coe_injective
  apply (Module.finBasis ℝ V).ext
  intro i
  simp [finBasisOperatorEquiv_apply_basis, evolvingTransportCurveOn]

theorem evolvingTransportCurveOn_continuousWithinAt
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContinuousWithinAt (evolvingTransportCurveOn A hab hcont hK) (Icc a b) t :=
  (evolvingTransportCurveOn_hasDerivWithinAt A hab hcont hK ht).continuousWithinAt

theorem evolvingTransportCurveOn_continuousOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) :
    ContinuousOn (evolvingTransportCurveOn A hab hcont hK) (Icc a b) :=
  fun _ ht => evolvingTransportCurveOn_continuousWithinAt A hab hcont hK ht

theorem evolvingTransportOn_eq_curve_restrict
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) :
    evolvingTransportOn A hab hcont hK =
      fun t : Icc a b => evolvingTransportCurveOn A hab hcont hK t := by
  funext t
  apply ContinuousLinearMap.coe_injective
  ext v
  exact (evolvingTransportCurveOn_apply_of_mem A hab hcont hK t.2 v).symm

/-- **Math.** The original subtype-valued compact-interval transport is continuous in
operator norm. -/
theorem evolvingTransportOn_continuous
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) :
    Continuous (evolvingTransportOn A hab hcont hK) := by
  rw [evolvingTransportOn_eq_curve_restrict]
  exact (evolvingTransportCurveOn_continuousOn A hab hcont hK).restrict

end MorganTianLib

end

#print axioms MorganTianLib.evolvingTransportCurveOn_hasDerivWithinAt
#print axioms MorganTianLib.evolvingTransportOn_continuous
