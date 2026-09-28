import MorganTianLib.Ch03.RicciFlow.EvolvingFrameODE
import MorganTianLib.Ch03.RicciFlow.EvolvingFrame

/-!
# Morgan--Tian Ch. 3 -- compact-interval evolving transport

The linear ODE producer gives a solution for every initial vector on one
compact time interval.  This module packages those solutions as a genuine
time-indexed continuous-linear transport.  The construction is still
interval-local: smooth dependence on the base point and globalization across
all time intervals are separate geometric obligations.
-/

open Set
open scoped NNReal

noncomputable section

namespace MorganTianLib

/-! ## The endpoint transport on a fixed compact interval -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-- **Math.** The solution operator at a time in a fixed compact interval.
It is defined from the one global `solOf` choice, so all times use the same
linear-ODE solution family. -/
noncomputable def evolvingTransportOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (t : Icc a b) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Riemannian.LinearODE.solOf hab hcont hK v (t : ℝ)
      map_add' := by
        intro v w
        have hsum := Riemannian.LinearODE.IsSolOn.eqOn_of_left hK
          (Riemannian.LinearODE.solOf_isSolOn hab hcont hK (v + w))
          ((Riemannian.LinearODE.solOf_isSolOn hab hcont hK v).add
            (Riemannian.LinearODE.solOf_isSolOn hab hcont hK w))
          (by simp [Riemannian.LinearODE.solOf_left hab hcont hK])
          t.2
        simpa only [Pi.add_apply] using hsum
      map_smul' := by
        intro c v
        have hsmul := Riemannian.LinearODE.IsSolOn.eqOn_of_left hK
          (Riemannian.LinearODE.solOf_isSolOn hab hcont hK (c • v))
          ((Riemannian.LinearODE.solOf_isSolOn hab hcont hK v).const_smul c)
          (by simp [Riemannian.LinearODE.solOf_left hab hcont hK])
          t.2
        simpa only [Pi.smul_apply, RingHom.id_apply] using hsmul }

@[simp] theorem evolvingTransportOn_apply
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (t : Icc a b) (v : V) :
    evolvingTransportOn A hab hcont hK t v =
      Riemannian.LinearODE.solOf hab hcont hK v (t : ℝ) := rfl

@[simp] theorem evolvingTransportOn_left
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) :
    evolvingTransportOn A hab hcont hK ⟨a, ⟨le_rfl, hab⟩⟩ =
      ContinuousLinearMap.id ℝ V := by
  ext v
  simp [evolvingTransportOn, Riemannian.LinearODE.solOf_left hab hcont hK]

/-! ## ODE solution and invertibility consequences -/

omit [FiniteDimensional ℝ V] in
theorem evolvingTransportOn_solution
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (v : V) :
    Riemannian.LinearODE.IsSolOn A a b
      (Riemannian.LinearODE.solOf hab hcont hK v) :=
  Riemannian.LinearODE.solOf_isSolOn hab hcont hK v

omit [FiniteDimensional ℝ V] in
theorem evolvingTransportOn_hasDerivWithinAt
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (v : V) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt
      (Riemannian.LinearODE.solOf hab hcont hK v)
      (A t (Riemannian.LinearODE.solOf hab hcont hK v t))
      (Icc a b) t :=
  Riemannian.LinearODE.solOf_isSolOn hab hcont hK v t ht

theorem evolvingTransportOn_injective
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Injective (evolvingTransportOn A hab.le hcont hK ⟨t, ht⟩) := by
  intro v w hvw
  have hEqAt :
      Riemannian.LinearODE.solOf hab.le hcont hK v t =
        Riemannian.LinearODE.solOf hab.le hcont hK w t := by
    simpa only [evolvingTransportOn_apply] using hvw
  have hKt : ∀ s ∈ Icc a t, ‖A s‖₊ ≤ K := by
    intro s hs
    exact hK s ⟨hs.1, hs.2.trans ht.2⟩
  have hV : Riemannian.LinearODE.IsSolOn A a t
      (Riemannian.LinearODE.solOf hab.le hcont hK v) := by
    intro s hs
    exact (Riemannian.LinearODE.solOf_isSolOn hab.le hcont hK v s
      ⟨hs.1, hs.2.trans ht.2⟩).mono (Icc_subset_Icc le_rfl ht.2)
  have hW : Riemannian.LinearODE.IsSolOn A a t
      (Riemannian.LinearODE.solOf hab.le hcont hK w) := by
    intro s hs
    exact (Riemannian.LinearODE.solOf_isSolOn hab.le hcont hK w s
      ⟨hs.1, hs.2.trans ht.2⟩).mono (Icc_subset_Icc le_rfl ht.2)
  have heq := Riemannian.LinearODE.IsSolOn.eqOn_of_right hKt hV hW hEqAt
  have ha := heq (show a ∈ Icc a t from ⟨le_rfl, ht.1⟩)
  simpa only [Riemannian.LinearODE.solOf_left] using ha

theorem evolvingTransportOn_bijective
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Bijective (evolvingTransportOn A hab.le hcont hK ⟨t, ht⟩) := by
  have hinj := evolvingTransportOn_injective A hab hcont hK ht
  have hinjL : Function.Injective
      ((evolvingTransportOn A hab.le hcont hK ⟨t, ht⟩).toLinearMap) := hinj
  have hsurjL : Function.Surjective
      ((evolvingTransportOn A hab.le hcont hK ⟨t, ht⟩).toLinearMap) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinjL
  exact ⟨hinj, hsurjL⟩

end MorganTianLib

end

#print axioms MorganTianLib.evolvingTransportOn_solution
#print axioms MorganTianLib.evolvingTransportOn_bijective
