import MorganTianLib.Ch03.RicciFlow.CurvatureVariationArbitrary
import MorganTianLib.Ch03.RicciFlow.EvolvingFrameCurvature
import Mathlib.Analysis.ODE.Gronwall

/-!
# Morgan--Tian Ch. 3 -- the curvature equation in an evolving frame

Along a Ricci flow, differentiating a curvature component in a frame satisfying
the Ricci-dual ODE produces four frame-motion terms.  Those terms cancel the
four Ricci contractions in the intrinsic curvature variation, leaving the
rough Laplacian and the pure quadratic `B` reaction.  This module performs that
composition for actual Riemann curvature and sums the resulting component
equations into a finite squared-curvature energy identity.
-/

open scoped BigOperators ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ## Components and the geometric evolution terms -/

/-- **Math.** A component of the Riemann curvature tensor in a time-dependent
frame in one tangent fibre. -/
def ricciFlowFrameCurvatureComponent
    {ι : Type*} [Fintype ι]
    (g : ℝ → RiemannianMetric I M) (p : M)
    (frame : ℝ → ι → TangentSpace I p) (slot : Fin 4 → ι)
    (t : ℝ) : ℝ :=
  curvatureFormAt (g t) (g t).leviCivitaConnection p
    (frame t (slot 0)) (frame t (slot 1))
    (frame t (slot 2)) (frame t (slot 3))

/-- **Math.** The rough-Laplacian component of Riemann curvature in a frame at
one point. -/
def ricciFlowFrameCurvatureLaplacianComponent
    {ι : Type*} [Fintype ι]
    (g : RiemannianMetric I M) (p : M)
    (frame : ι → TangentSpace I p) (slot : Fin 4 → ι) : ℝ :=
  roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
    ![extendVector p (frame (slot 0)), extendVector p (frame (slot 1)),
      extendVector p (frame (slot 2)), extendVector p (frame (slot 3))] p

/-- **Math.** The pure quadratic reaction in the evolving-frame curvature
equation, in Morgan--Tian's slot order. -/
def ricciFlowFrameCurvatureReaction
    {ι : Type*} [Fintype ι]
    (g : RiemannianMetric I M) (p : M)
    (frame : ι → TangentSpace I p) (slot : Fin 4 → ι) : ℝ :=
  2 * (curvatureB g p
        (frame (slot 0)) (frame (slot 1)) (frame (slot 2)) (frame (slot 3))
      - curvatureB g p
        (frame (slot 0)) (frame (slot 1)) (frame (slot 3)) (frame (slot 2))
      - curvatureB g p
        (frame (slot 0)) (frame (slot 3)) (frame (slot 1)) (frame (slot 2))
      + curvatureB g p
        (frame (slot 0)) (frame (slot 2)) (frame (slot 1)) (frame (slot 3)))

/-- **Math.** The exact pointwise curvature-component equation in a frame whose
vectors satisfy the Ricci-dual ODE.  The four moving-slot contributions cancel
the four Ricci traces in the intrinsic variation, leaving the rough Laplacian
and the quadratic `B` reaction. -/
theorem hasDerivAt_ricciFlowFrameCurvatureComponent_of_isRicciFlowOn
    {ι : Type*} [Fintype ι]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hflow : IsRicciFlowOn g J)
    (alpha p : M) (frame : ℝ → ι → TangentSpace I p)
    (slot : Fin 4 → ι) {t : ℝ}
    (hframe : ∀ a, HasDerivAt (fun s ↦ frame s a)
      (ricciEndomorphismAt (g t) p (frame t a)) t)
    (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s ↦ ricciFlowFrameCurvatureComponent (I := I) g p frame slot s)
      (ricciFlowFrameCurvatureLaplacianComponent (I := I)
          (g t) p (frame t) slot
        + ricciFlowFrameCurvatureReaction (I := I) (g t) p (frame t) slot) t := by
  have hderiv :=
    hasDerivAt_curvatureFormAt_along_curves_of_isRicciFlowOn
      hflow alpha p
      (fun s ↦ frame s (slot 0)) (fun s ↦ frame s (slot 1))
      (fun s ↦ frame s (slot 2)) (fun s ↦ frame s (slot 3))
      (hframe (slot 0)) (hframe (slot 1)) (hframe (slot 2)) (hframe (slot 3))
      ht hp
  unfold ricciFlowFrameCurvatureComponent
  refine hderiv.congr_deriv ?_
  let X : SmoothVectorField I M := extendVector p (frame t (slot 0))
  let Y : SmoothVectorField I M := extendVector p (frame t (slot 1))
  let W : SmoothVectorField I M := extendVector p (frame t (slot 2))
  let Z : SmoothVectorField I M := extendVector p (frame t (slot 3))
  have hevol :=
    ricciFlowRiemannVariationIntrinsic_eq_roughLaplacian_add_correction
      (g t) X Y W Z p
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hcancel :=
    curvatureEvolutionCorrection_add_evolvingFrameCurvatureRicciAction
      (g t) X Y W Z p
  unfold ricciFlowFrameCurvatureLaplacianComponent
    ricciFlowFrameCurvatureReaction
  calc
    ricciFlowRiemannVariationIntrinsic (g t)
          ![extendVector p (frame t (slot 0)), extendVector p (frame t (slot 1)),
            extendVector p (frame t (slot 2)), extendVector p (frame t (slot 3))] p
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            (ricciEndomorphismAt (g t) p (frame t (slot 0)))
            (frame t (slot 1)) (frame t (slot 2)) (frame t (slot 3))
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            (frame t (slot 0))
            (ricciEndomorphismAt (g t) p (frame t (slot 1)))
            (frame t (slot 2)) (frame t (slot 3))
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            (frame t (slot 0)) (frame t (slot 1))
            (ricciEndomorphismAt (g t) p (frame t (slot 2)))
            (frame t (slot 3))
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            (frame t (slot 0)) (frame t (slot 1)) (frame t (slot 2))
            (ricciEndomorphismAt (g t) p (frame t (slot 3))) =
      roughLaplacian (g t) (g t).leviCivitaConnection (riemannTensorField (g t))
          ![X, Y, W, Z] p
        + (curvatureEvolutionCorrection (g t) ![X, Y, W, Z] p
          + evolvingFrameCurvatureRicciAction (g t) p
              (X p) (Y p) (W p) (Z p)) := by
        rw [hevol]
        simp only [X, Y, W, Z, extendVector_apply,
          curvatureFormAt_eq_affineCurvatureFormAt,
          evolvingFrameCurvatureRicciAction]
        ac_rfl
    _ = roughLaplacian (g t) (g t).leviCivitaConnection
          (riemannTensorField (g t)) ![X, Y, W, Z] p
        + 2 * (curvatureB (g t) p (X p) (Y p) (W p) (Z p)
          - curvatureB (g t) p (X p) (Y p) (Z p) (W p)
          - curvatureB (g t) p (X p) (Z p) (Y p) (W p)
          + curvatureB (g t) p (X p) (W p) (Y p) (Z p)) := by
        rw [hcancel]
    _ = roughLaplacian (g t) (g t).leviCivitaConnection
          (riemannTensorField (g t))
          ![extendVector p (frame t (slot 0)), extendVector p (frame t (slot 1)),
            extendVector p (frame t (slot 2)), extendVector p (frame t (slot 3))] p
        + 2 * (curvatureB (g t) p
            (frame t (slot 0)) (frame t (slot 1))
            (frame t (slot 2)) (frame t (slot 3))
          - curvatureB (g t) p
            (frame t (slot 0)) (frame t (slot 1))
            (frame t (slot 3)) (frame t (slot 2))
          - curvatureB (g t) p
            (frame t (slot 0)) (frame t (slot 3))
            (frame t (slot 1)) (frame t (slot 2))
          + curvatureB (g t) p
            (frame t (slot 0)) (frame t (slot 2))
            (frame t (slot 1)) (frame t (slot 3))) := by
        simp only [X, Y, W, Z, extendVector_apply]

/-! ## The finite squared-component energy -/

/-- **Math.** The finite sum of squared Riemann components in a time-dependent
frame. -/
def ricciFlowFrameCurvatureEnergy
    {ι : Type*} [Fintype ι]
    (g : ℝ → RiemannianMetric I M) (p : M)
    (frame : ℝ → ι → TangentSpace I p) (t : ℝ) : ℝ :=
  ∑ slot : Fin 4 → ι,
    (ricciFlowFrameCurvatureComponent (I := I) g p frame slot t) ^ 2

omit [I.Boundaryless] in
theorem ricciFlowFrameCurvatureEnergy_nonneg
    {ι : Type*} [Fintype ι]
    (g : ℝ → RiemannianMetric I M) (p : M)
    (frame : ℝ → ι → TangentSpace I p) (t : ℝ) :
    0 ≤ ricciFlowFrameCurvatureEnergy (I := I) g p frame t := by
  classical
  unfold ricciFlowFrameCurvatureEnergy
  exact Finset.sum_nonneg fun slot _ ↦ sq_nonneg _

/-- **Math.** Summing the evolving-frame component equation gives the exact
time derivative of the finite squared-curvature energy. -/
theorem hasDerivAt_ricciFlowFrameCurvatureEnergy_of_isRicciFlowOn
    {ι : Type*} [Fintype ι]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hflow : IsRicciFlowOn g J)
    (alpha p : M) (frame : ℝ → ι → TangentSpace I p) {t : ℝ}
    (hframe : ∀ a, HasDerivAt (fun s ↦ frame s a)
      (ricciEndomorphismAt (g t) p (frame t a)) t)
    (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s ↦ ricciFlowFrameCurvatureEnergy (I := I) g p frame s)
      (2 * ∑ slot : Fin 4 → ι,
        ricciFlowFrameCurvatureComponent (I := I) g p frame slot t *
          (ricciFlowFrameCurvatureLaplacianComponent (I := I)
              (g t) p (frame t) slot
            + ricciFlowFrameCurvatureReaction (I := I)
              (g t) p (frame t) slot)) t := by
  classical
  have hterm (slot : Fin 4 → ι) :
      HasDerivAt
        (fun s ↦
          (ricciFlowFrameCurvatureComponent (I := I) g p frame slot s) ^ 2)
        (2 * ricciFlowFrameCurvatureComponent (I := I) g p frame slot t *
          (ricciFlowFrameCurvatureLaplacianComponent (I := I)
              (g t) p (frame t) slot
            + ricciFlowFrameCurvatureReaction (I := I)
              (g t) p (frame t) slot)) t := by
    have hcomponent :=
      hasDerivAt_ricciFlowFrameCurvatureComponent_of_isRicciFlowOn
        hflow alpha p frame slot hframe ht hp
    have hsq := hcomponent.mul hcomponent
    have heq :
        (fun s ↦
          ricciFlowFrameCurvatureComponent (I := I) g p frame slot s *
            ricciFlowFrameCurvatureComponent (I := I) g p frame slot s) =
          (fun s ↦
            (ricciFlowFrameCurvatureComponent (I := I) g p frame slot s) ^ 2) := by
      funext s
      ring
    have hd :
        (ricciFlowFrameCurvatureLaplacianComponent (I := I)
              (g t) p (frame t) slot
            + ricciFlowFrameCurvatureReaction (I := I)
              (g t) p (frame t) slot) *
            ricciFlowFrameCurvatureComponent (I := I) g p frame slot t
          + ricciFlowFrameCurvatureComponent (I := I) g p frame slot t *
            (ricciFlowFrameCurvatureLaplacianComponent (I := I)
                (g t) p (frame t) slot
              + ricciFlowFrameCurvatureReaction (I := I)
                (g t) p (frame t) slot) =
          2 * ricciFlowFrameCurvatureComponent (I := I) g p frame slot t *
            (ricciFlowFrameCurvatureLaplacianComponent (I := I)
                (g t) p (frame t) slot
              + ricciFlowFrameCurvatureReaction (I := I)
                (g t) p (frame t) slot) := by
      ring
    rw [← heq, ← hd]
    exact hsq
  have hsum := HasDerivAt.fun_sum
    (fun slot (_ : slot ∈ (Finset.univ : Finset (Fin 4 → ι))) ↦ hterm slot)
  simpa only [ricciFlowFrameCurvatureEnergy, Finset.mul_sum, mul_assoc] using hsum

/-! ## Finite-time energy control

The component identity above is the geometric input to the analytic Shi
argument.  The following bridge packages a one-sided bound on its exact
right-hand side into the corresponding finite-time Grönwall estimate.  The
bound is deliberately exposed as a hypothesis: it is where a Laplacian or
reaction estimate from a later Shi induction is supplied.
-/

/-- **Math.** A one-sided bound for the exact evolving-frame curvature energy
derivative gives a finite-time Grönwall bound.  The flow, frame, and chart
hypotheses ensure that the derivative identity is available at every interior
time of the interval.
-/
theorem ricciFlowFrameCurvatureEnergy_le_gronwall_of_deriv_bound
    {ι : Type*} [Fintype ι]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha p : M)
    (frame : ℝ → ι → TangentSpace I p) {a b ε K E₀ : ℝ}
    (hframe : ∀ s c, HasDerivAt (fun u ↦ frame u c)
      (ricciEndomorphismAt (g s) p (frame s c)) s)
    (hinterior : Ico a b ⊆ interior J)
    (hp : p ∈ (chartAt H alpha).source)
    (hcont : ContinuousOn
      (fun s ↦ ricciFlowFrameCurvatureEnergy (I := I) g p frame s)
      (Icc a b))
    (hinit : ricciFlowFrameCurvatureEnergy (I := I) g p frame a ≤ E₀)
    (hbound : ∀ s ∈ Ico a b,
      ‖2 * ∑ slot : Fin 4 → ι,
        ricciFlowFrameCurvatureComponent (I := I) g p frame slot s *
          (ricciFlowFrameCurvatureLaplacianComponent (I := I)
              (g s) p (frame s) slot
            + ricciFlowFrameCurvatureReaction (I := I)
              (g s) p (frame s) slot)‖ ≤
        ε * ‖ricciFlowFrameCurvatureEnergy (I := I) g p frame s‖ + K)
    :
    ∀ t ∈ Icc a b,
      ricciFlowFrameCurvatureEnergy (I := I) g p frame t ≤
        gronwallBound E₀ ε K (t - a) := by
  have hderiv : ∀ s ∈ Ico a b,
      HasDerivWithinAt
        (fun u ↦ ricciFlowFrameCurvatureEnergy (I := I) g p frame u)
        (2 * ∑ slot : Fin 4 → ι,
          ricciFlowFrameCurvatureComponent (I := I) g p frame slot s *
            (ricciFlowFrameCurvatureLaplacianComponent (I := I)
                (g s) p (frame s) slot
              + ricciFlowFrameCurvatureReaction (I := I)
                (g s) p (frame s) slot))
        (Ici s) s := by
    intro s hs
    have hsJ : s ∈ interior J := hinterior hs
    simpa using
      (hasDerivAt_ricciFlowFrameCurvatureEnergy_of_isRicciFlowOn
        hflow alpha p frame (hframe s) hsJ hp).hasDerivWithinAt
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s ↦ ricciFlowFrameCurvatureEnergy (I := I) g p frame s)
    (f' := fun s ↦ 2 * ∑ slot : Fin 4 → ι,
      ricciFlowFrameCurvatureComponent (I := I) g p frame slot s *
        (ricciFlowFrameCurvatureLaplacianComponent (I := I)
            (g s) p (frame s) slot
          + ricciFlowFrameCurvatureReaction (I := I)
            (g s) p (frame s) slot))
    (δ := E₀) (K := ε) (ε := K) hcont hderiv
    (by
      have hnonneg := ricciFlowFrameCurvatureEnergy_nonneg (I := I) g p frame a
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hinit)
    (by
      intro s hs
      simpa only [Real.norm_eq_abs] using hbound s hs)
  intro t ht
  calc
    ricciFlowFrameCurvatureEnergy (I := I) g p frame t ≤
        ‖ricciFlowFrameCurvatureEnergy (I := I) g p frame t‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (ricciFlowFrameCurvatureEnergy (I := I) g p frame t))
    _ ≤ gronwallBound E₀ ε K (t - a) := hgronwall t ht

end MorganTianLib

end

#print axioms
  MorganTianLib.hasDerivAt_ricciFlowFrameCurvatureComponent_of_isRicciFlowOn
#print axioms
  MorganTianLib.hasDerivAt_ricciFlowFrameCurvatureEnergy_of_isRicciFlowOn
