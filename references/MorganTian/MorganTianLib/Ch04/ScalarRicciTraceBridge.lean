import MorganTianLib.Ch04.ScalarCurvatureMinimum
import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution
import MorganTianLib.Ch04.HamiltonMaximumLaplacian

/-!
# Morgan--Tian Ch. 4 - scalar minimum bridge

This module instantiates the algebraic scalar minimum estimate with the
intrinsic Ricci endomorphism supplied by Chapter 3. At an interior time of a
Ricci flow, the geometric evolution equation and the Laplacian sign at a local
minimum give the derivative bound without separate evolution or sign inputs.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** At a spatial minimum, the Ricci-flow scalar evolution and the
trace Cauchy--Schwarz inequality imply Hamilton's pointwise lower derivative
bound.  The nonnegative quantity `L` represents the Laplacian contribution.
Blueprint: `claim:scalar-min-derivative-bound`. -/
theorem scalar_min_deriv_bound_of_ricci_flow_data
    (g : RiemannianMetric I M) (p : M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    {F' L : ℝ}
    (hn : 0 < (Module.finrank ℝ (TangentSpace I p) : ℝ))
    (hevol : F' = L + 2 * ricciNormSqAt g p)
    (hL : 0 ≤ L) :
    (2 / (Module.finrank ℝ (TangentSpace I p) : ℝ)) *
        scalarCurvatureAt g g.leviCivitaConnection hLC p ^ 2 ≤ F' := by
  have hnNat : 0 < Module.finrank ℝ (TangentSpace I p) := by
    exact_mod_cast hn
  letI : Nontrivial (TangentSpace I p) := Module.finrank_pos_iff.mp hnNat
  apply scalar_min_deriv_bound_of_evolution
    (F := scalarCurvatureAt g g.leviCivitaConnection hLC p)
    (N := ricciNormSqAt g p)
    (n := Module.finrank ℝ (TangentSpace I p))
  · exact hn
  · exact hevol
  · exact hL
  · exact scalarCurvature_sq_le_finrank_mul_ricciNormSqAt g p hLC

/-- **Math.** At an interior time of a Ricci flow, the time derivative of scalar
curvature at a local spatial minimum is at least `2 R^2 / n`.
Blueprint: `claim:scalar-min-derivative-bound`. -/
theorem scalar_min_deriv_bound_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J) {p : M}
    (hmin : IsLocalMin
      (scalarCurvatureAt (g t) (g t).leviCivitaConnection
        ((g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
          (fun X Y W q => (g t).koszulDualSection_dual X Y W q))) p) :
    (2 / (Module.finrank ℝ E : ℝ)) *
        scalarCurvatureAt (g t) (g t).leviCivitaConnection
          ((g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
            (fun X Y W q => (g t).koszulDualSection_dual X Y W q)) p ^ 2 ≤
      deriv (fun s => scalarCurvatureAt (g s) (g s).leviCivitaConnection
        ((g s).leviCivitaConnection.isLeviCivita_of_koszulDual (g s)
          (fun X Y W q => (g s).koszulDualSection_dual X Y W q)) p) t := by
  have hLC := (g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
    (fun X Y W q => (g t).koszulDualSection_dual X Y W q)
  have hderiv :=
    hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn_eq_laplacian_add_reaction
      hflow p ht ((extChartAt I p).map_source (mem_extChartAt_source p))
  simp only [extChartAt_to_inv] at hderiv
  rw [hderiv.deriv]
  have hn : 0 < (Module.finrank ℝ (TangentSpace I p) : ℝ) := by
    change 0 < (Module.finrank ℝ E : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  exact scalar_min_deriv_bound_of_ricci_flow_data (g t) p hLC hn rfl
    (laplacianAt_nonneg_of_isLocalMin (g t) (g t).leviCivitaConnection
      (scalarCurvatureAt_contMDiff (g t) (g t).leviCivitaConnection hLC) hmin)

end MorganTianLib

end

#print axioms MorganTianLib.scalar_min_deriv_bound_of_ricci_flow_data
#print axioms MorganTianLib.scalar_min_deriv_bound_of_isRicciFlowOn
