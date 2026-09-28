import MorganTianLib.Ch04.HamiltonMaximumCore

/-!
# Continuity of compact support scalarizations

The compact-support Hamilton principle takes joint continuity of the support
value and derivative families as explicit inputs.  This file supplies the
finite-dimensional regularity bridge when the support-pair parameterization and
the reaction-diffusion data are continuous.
-/

open Set
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

variable {X E P : Type*} [TopologicalSpace X]
  [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem continuous_support_point
    {Z : Set E} {support : P → ConvexSupportPair Z}
    (hsupport : Continuous support) :
    Continuous (fun p : P => (support p).1.1) := by
  exact continuous_fst.comp (continuous_subtype_val.comp hsupport)

private theorem continuous_support_normal
    {Z : Set E} {support : P → ConvexSupportPair Z}
    (hsupport : Continuous support) :
    Continuous (fun p : P => (support p).1.2) := by
  exact continuous_snd.comp (continuous_subtype_val.comp hsupport)

/-- A continuous support-pair parameterization and a continuous field produce a
continuous value family on the exterior-support branch.  This is the branch
used at active maxima; the constant-zero `Unit` branch is handled separately
by the existing envelope construction.
-/
theorem continuous_hamiltonSupportValueOn_inr
    {Z : Set E} {support : P → ConvexSupportPair Z}
    {u : X → ℝ → E}
    (hsupport : Continuous support)
    (hu : Continuous (fun xt : X × ℝ => u xt.1 xt.2)) :
    Continuous (fun pt : (X × P) × ℝ =>
      ⟪(support pt.1.2).1.2,
        u pt.1.1 pt.2 - (support pt.1.2).1.1⟫_ℝ) := by
  let hpoint : Continuous (fun p : P => (support p).1.1) :=
    continuous_support_point hsupport
  let hnormal : Continuous (fun p : P => (support p).1.2) :=
    continuous_support_normal hsupport
  have hu' : Continuous (fun pt : (X × P) × ℝ => u pt.1.1 pt.2) :=
    hu.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hp : Continuous (fun pt : (X × P) × ℝ => (support pt.1.2).1.1) :=
    hpoint.comp (continuous_snd.comp continuous_fst)
  have hn : Continuous (fun pt : (X × P) × ℝ => (support pt.1.2).1.2) :=
    hnormal.comp (continuous_snd.comp continuous_fst)
  exact hn.inner (hu'.sub hp)

/- The derivative branch has the same support normal factor.  The operator and
reaction terms are intentionally supplied as continuous evaluated fields. -/
theorem continuous_hamiltonSupportDerivativeOn_inr
    {Z : Set E} {support : P → ConvexSupportPair Z}
    {u : X → ℝ → E} {L : ℝ → (X → E) → X → E} {ψ : E → E}
    (hsupport : Continuous support)
    (hLu : Continuous (fun xt : X × ℝ =>
      L xt.2 (fun y : X => u y xt.2) xt.1))
    (hψu : Continuous (fun xt : X × ℝ => ψ (u xt.1 xt.2))) :
    Continuous (fun pt : (X × P) × ℝ =>
      hamiltonSupportDerivativeOn Z support u L ψ pt.1.1 (Sum.inr pt.1.2) pt.2) := by
  have hn : Continuous (fun pt : (X × P) × ℝ => (support pt.1.2).1.2) :=
    continuous_support_normal hsupport |>.comp (continuous_snd.comp continuous_fst)
  have hLu' : Continuous (fun pt : (X × P) × ℝ =>
      L pt.2 (fun y : X => u y pt.2) pt.1.1) :=
    hLu.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hψu' : Continuous (fun pt : (X × P) × ℝ => ψ (u pt.1.1 pt.2)) :=
    hψu.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hsum : Continuous (fun pt : (X × P) × ℝ =>
      L pt.2 (fun y : X => u y pt.2) pt.1.1 + ψ (u pt.1.1 pt.2)) :=
    hLu'.add hψu'
  simpa [hamiltonSupportDerivativeOn] using hn.inner hsum

end MorganTianLib

#print axioms MorganTianLib.continuous_hamiltonSupportValueOn_inr
#print axioms MorganTianLib.continuous_hamiltonSupportDerivativeOn_inr
