import DoCarmoLib.Riemannian.Geodesic.LinearODE

/-!
# Morgan--Tian Ch. 3 -- interval existence for the evolving-frame ODE

The moving-frame equation is a linear ODE in each fixed tangent fiber.  The
linear ODE engine in `DoCarmoLib` gives a solution on every compact time
interval when its coefficient is continuous and bounded.  Applying that
producer componentwise supplies the finite family of evolving frame vectors;
the stronger geometric assertions (the metric-dual identification and
orthonormality) are proved separately in `EvolvingFrame.lean`.
-/

open Set
open scoped NNReal

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V]

/-- **Math.** A continuous bounded linear coefficient admits an evolving frame
on any compact interval, with arbitrary prescribed initial vectors.  Each
component is obtained from the global compact-interval linear ODE producer;
no finite-dimensional or metric structure is needed for this analytic step.

This is the local-in-time existence half of Morgan--Tian's evolving-frame
construction (the geometric metric-dual and orthonormality statements are
separate consequences). -/
theorem exists_evolvingFrame_of_continuous_coefficient_Icc
    {ι : Type*} (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    {K : ℝ≥0} (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (basis : ι → V) :
    ∃ frame : ι → ℝ → V,
      (∀ i, frame i a = basis i) ∧
        ∀ i, Riemannian.LinearODE.IsSolOn A a b (frame i) := by
  classical
  have H : ∀ i : ι, ∃ Vcurve : ℝ → V, Vcurve a = basis i ∧
      Riemannian.LinearODE.IsSolOn A a b Vcurve := by
    intro i
    obtain ⟨Vcurve, hV₀, hV⟩ :=
      Riemannian.LinearODE.exists_hasDerivWithinAt_Icc hab A (basis i) hcont hK
    exact ⟨Vcurve, hV₀, hV⟩
  choose frame hframe₀ hframe using H
  exact ⟨frame, hframe₀, hframe⟩

omit [CompleteSpace V] in
/-- **Math.** The evolving-frame ODE has forward uniqueness componentwise on a
compact interval.  Frames with the same initial family and the same bounded
coefficient agree throughout the interval. -/
theorem evolvingFrame_eqOn_of_left
    {ι : Type*} {A : ℝ → V →L[ℝ] V} {a b : ℝ} {K : ℝ≥0}
    {frame frame' : ι → ℝ → V}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hframe : ∀ i, Riemannian.LinearODE.IsSolOn A a b (frame i))
    (hframe' : ∀ i, Riemannian.LinearODE.IsSolOn A a b (frame' i))
    (hinit : ∀ i, frame i a = frame' i a) :
    ∀ i, EqOn (frame i) (frame' i) (Icc a b) := by
  intro i
  exact Riemannian.LinearODE.IsSolOn.eqOn_of_left hK (hframe i) (hframe' i)
    (hinit i)

end MorganTianLib

end

#print axioms MorganTianLib.exists_evolvingFrame_of_continuous_coefficient_Icc
#print axioms MorganTianLib.evolvingFrame_eqOn_of_left
