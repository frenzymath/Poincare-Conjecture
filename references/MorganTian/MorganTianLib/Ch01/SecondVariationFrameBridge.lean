import MorganTianLib.Ch01.SecondVariationJacobi
import MorganTianLib.Ch01.FrameIndexBridge
import DoCarmoLib.Riemannian.Jacobi.JacobiSectionalCurvature
import DoCarmoLib.Riemannian.Variation.IndexForm
import DoCarmoLib.Riemannian.Variation.BonnetMyers

/-!
# Poincare Ch. 1 - the manifold/frame index-form bridge

The chart-level second-variation files and the null-index Jacobi theorem use two
different presentations of the same quadratic form.  DoCarmo's manifold index
form is written with the curvature term in the order
`R(gamma', V, gamma', V)`, whereas the frame operator uses the Morgan--Tian
order `R(V, gamma', gamma', V)`.  Antisymmetry in the first pair converts one
to the other.  This file records that conversion for a field lifted from a
parallel orthonormal frame.
-/

open Set Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** Morgan--Tian's field-level curvature form is the same
pointwise `(0,4)` curvature form used by DoCarmoLib. -/
theorem curvatureFormAt_eq_riemannian
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M)
    (v w z t : TangentSpace I p) :
    curvatureFormAt g nabla p v w z t =
      nabla.curvatureFormAt g p v w z t := by
  rw [curvatureFormAt_def,
    nabla.curvatureFormAt_eq g p
      (X := extendVector p v)
      (Y := extendVector p w)
      (Z := extendVector p z)
      (T := extendVector p t)]
  all_goals simp

/-- **Math.** The metric index integral of a frame-lifted pair is the
abstract index form of its coefficient pair.  This is the integrated seam
used by the chart-level second-variation formula; the do Carmo curvature
ordering is converted to this `+ curvatureFormAt V gamma' gamma' V`
normalisation by antisymmetry in the first curvature pair. -/
theorem metricIndexIntegral_frameLift_eq
    (g : RiemannianMetric I M) {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {W DW : ℝ → 𝔼} {a b : ℝ}
    (hab : a ≤ b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0) :
    (∫ t in a..b,
      g.metricInner (γ t)
          (frameLift (I := I) g γ e t (DW t) : TangentSpace I (γ t))
          (frameLift (I := I) g γ e t (DW t))
        + curvatureFormAt g g.leviCivitaConnection (γ t)
            (frameLift (I := I) g γ e t (W t) : TangentSpace I (γ t))
            (mfderivVelocity (I := I) (E := E) γ t)
            (mfderivVelocity (I := I) (E := E) γ t)
            (frameLift (I := I) g γ e t (W t))) =
      indexForm (frameCurvOp (I := I) g γ e) a b W DW W DW := by
  rw [indexForm_def]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : t ∈ Icc a b := by
    simpa [uIcc_of_le hab] using ht
  have hframe := indexIntegrand_frameVec (I := I) (g := g) (γ := γ)
    (e := e)
    (V := fun s => (frameLift (I := I) g γ e s (W s) : E))
    (DV := fun s => (frameLift (I := I) g γ e s (DW s) : E))
    (horth t ht')
  have hW := frameVec_frameLift_apply (I := I) (g := g) (γ := γ) (e := e)
    (horth t ht') W
  have hDW := frameVec_frameLift_apply (I := I) (g := g) (γ := γ) (e := e)
    (horth t ht') DW
  simpa [indexIntegrand, hW, hDW] using hframe

/-- **Math.** DoCarmoLib's intrinsic index form of a field written in a
parallel orthonormal frame is Morgan--Tian's coefficient index form.  The
curvature conventions differ only by antisymmetry in the first pair. -/
theorem riemannianIndexForm_frameLift_eq
    (g : RiemannianMetric I M) {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {W DW : ℝ → 𝔼} {a b : ℝ}
    (hab : a ≤ b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0) :
    Riemannian.Variation.indexForm (I := I) g γ
        (frameFieldOf (I := I) g γ e W)
        (frameFieldOf (I := I) g γ e DW) a b =
      indexForm (frameCurvOp (I := I) g γ e) a b W DW W DW := by
  rw [Riemannian.Variation.indexForm_def]
  simp only [frameFieldOf]
  calc
    (∫ t in a..b,
      g.metricInner (γ t)
          (frameLift (I := I) g γ e t (DW t) : TangentSpace I (γ t))
          (frameLift (I := I) g γ e t (DW t))
        - g.leviCivitaConnection.curvatureFormAt g (γ t)
            (DCVelocity (I := I) γ t)
            (frameLift (I := I) g γ e t (W t) : TangentSpace I (γ t))
            (DCVelocity (I := I) γ t)
            (frameLift (I := I) g γ e t (W t))) =
      (∫ t in a..b,
        g.metricInner (γ t)
            (frameLift (I := I) g γ e t (DW t) : TangentSpace I (γ t))
            (frameLift (I := I) g γ e t (DW t))
          + curvatureFormAt g g.leviCivitaConnection (γ t)
              (frameLift (I := I) g γ e t (W t) : TangentSpace I (γ t))
              (mfderivVelocity (I := I) (E := E) γ t)
              (mfderivVelocity (I := I) (E := E) γ t)
              (frameLift (I := I) g γ e t (W t))) := by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [curvatureFormAt_eq_riemannian]
        have hanti := Riemannian.Jacobi.curvatureFormAt_antisymm_fst (I := I) g (γ t)
          (DCVelocity (I := I) γ t)
          (frameLift (I := I) g γ e t (W t) : TangentSpace I (γ t))
          (DCVelocity (I := I) γ t)
          (frameLift (I := I) g γ e t (W t) : TangentSpace I (γ t))
        change _ - _ = _ +
          g.leviCivitaConnection.curvatureFormAt g (γ t)
            (frameLift (I := I) g γ e t (W t) : TangentSpace I (γ t))
            (DCVelocity (I := I) γ t)
            (DCVelocity (I := I) γ t)
            (frameLift (I := I) g γ e t (W t) : TangentSpace I (γ t))
        rw [← neg_eq_iff_eq_neg.mpr hanti]
        ring
    _ = _ := metricIndexIntegral_frameLift_eq (I := I) g hab horth

/-! ### Fixed-endpoint variation fields -/

/-- **Math.** The variational field of a proper variation vanishes at both endpoints.
Properness makes each endpoint transversal locally constant in the variation parameter, so
its manifold derivative at the base parameter is zero. -/
theorem variationalField_endpoints_eq_zero_of_proper
    {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}
    (hε : 0 < ε)
    (hproper : Riemannian.Variation.IsProperVariation c a ε f) :
    Riemannian.Variation.variationalField I f 0 = 0 ∧
      Riemannian.Variation.variationalField I f a = 0 := by
  constructor
  · change (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ f (s, 0)) 0) 1 = 0
    have heq : (fun s : ℝ ↦ f (s, 0)) =ᶠ[nhds 0] (fun _ ↦ c 0) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by linarith) hε)
        (fun s hs ↦ (hproper s hs).1)
    rw [Filter.EventuallyEq.mfderiv_eq heq, mfderiv_const]
    rfl
  · change (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ f (s, a)) 0) 1 = 0
    have heq : (fun s : ℝ ↦ f (s, a)) =ᶠ[nhds 0] (fun _ ↦ c a) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by linarith) hε)
        (fun s hs ↦ (hproper s hs).2)
    rw [Filter.EventuallyEq.mfderiv_eq heq, mfderiv_const]
    rfl

/-! ### The proper-family energy adapter -/

/-- **Math.** For a regular proper variation whose variation field is written in a parallel
orthonormal frame, vanishing of the actual second derivative of energy is equivalent to the
Jacobi equation along a minimizing geodesic.

This theorem composes three independently verified interfaces:

* `ProperSecondVariationData.deriv_deriv_dcEnergy_eq_indexForm` identifies the second energy
  derivative with the intrinsic index form of the variation field;
* `riemannianIndexForm_frameLift_eq` reads that intrinsic index in frame coefficients; and
* `indexForm_self_eq_zero_iff_isJacobiFieldAlongOn_of_minimizing` identifies the null space of
  the coefficient index form with manifold Jacobi fields.

The explicit `hS` and `hDtS` hypotheses are the remaining family-to-frame interface: an
arbitrary smooth fixed-endpoint family must still be shown to provide
`ProperSecondVariationData` and these two identifications. -/
theorem deriv_deriv_dcEnergy_eq_zero_iff_isJacobiFieldAlongOn_of_minimizing
    [CompleteSpace E] [T2Space (TangentBundle I M)] [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {f : ℝ × ℝ → M} {s₀ a b : ℝ}
    (h : Riemannian.Variation.ProperSecondVariationData (I := I) g f s₀ 0 1)
    {e : Fin (finrank ℝ E) → ℝ → E} {W : ℝ → 𝔼}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g (fun t ↦ f (s₀, t)) (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt (fun r ↦ f (s₀, r)) t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g (fun t ↦ f (s₀, t)) (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (f (s₀, t)) (e i t : TangentSpace I (f (s₀, t))) (e j t) =
        if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g (fun t ↦ f (s₀, t)) 0) ≤
      dist (f (s₀, 0)) (f (s₀, 1)))
    (hW : ContDiff ℝ 3 W) (hW0 : W 0 = 0) (hW1 : W 1 = 0)
    (hS : (fun t ↦ h.S (s₀, t)) =
      frameFieldOf (I := I) g (fun t ↦ f (s₀, t)) e W)
    (hDtS : (fun t ↦ h.DtS (s₀, t)) =
      frameFieldOf (I := I) g (fun t ↦ f (s₀, t)) e (deriv W)) :
    deriv (deriv (fun σ ↦ Riemannian.DCEnergy (I := I) g
        (fun t ↦ f (σ, t)) 0 1)) s₀ = 0 ↔
      IsJacobiFieldAlongOn (I := I) g (fun t ↦ f (s₀, t))
        (frameFieldOf (I := I) g (fun t ↦ f (s₀, t)) e W)
        (frameFieldOf (I := I) g (fun t ↦ f (s₀, t)) e (deriv W)) 0 1 := by
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc a b := fun t ht ↦
    ⟨le_trans ha.le ht.1, le_trans ht.2 hb.le⟩
  have horth01 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j,
      g.metricInner (f (s₀, t)) (e i t : TangentSpace I (f (s₀, t))) (e j t) =
        if i = j then 1 else 0 := fun t ht ↦ horth t (hsub ht)
  have hformula := h.deriv_deriv_dcEnergy_eq_indexForm
  have hframe := riemannianIndexForm_frameLift_eq (I := I) g
    (a := (0 : ℝ)) (b := 1) (W := W) (DW := deriv W) (by norm_num) horth01
  rw [hS, hDtS, hframe] at hformula
  have hnull := indexForm_self_eq_zero_iff_isJacobiFieldAlongOn_of_minimizing
    (I := I) g hg ha hb hgeo hγc hPar horth hmin hW hW0 hW1
  rw [hformula]
  constructor
  · intro hzero
    apply hnull.mp
    nlinarith
  · intro hJac
    rw [hnull.mpr hJac]
    norm_num

/-! ### Actual variational-field facade -/

/-- **Math.** A smooth proper family supplies the endpoint-zero conditions for the
coefficient curve in the frame presentation.  Once the remaining analytic
`ProperSecondVariationData` package is supplied, and its `S` field is identified
with DoCarmo's actual variational field, the second-derivative/Jacobi equivalence
can be stated using that field rather than an abstract frame lift.

This is deliberately an adapter, not a construction of
`ProperSecondVariationData`: the energy differentiation, covariant derivative,
curvature, and integrability witnesses remain explicit in `h`. -/
theorem deriv_deriv_dcEnergy_eq_zero_iff_variationalField_isJacobi_of_smooth_proper
    [CompleteSpace E] [T2Space (TangentBundle I M)] [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {c : ℝ → M} {f : ℝ × ℝ → M} {ε : ℝ}
    (hvariation : Riemannian.Variation.IsSmoothVariation I c 1 ε f)
    (hproper : Riemannian.Variation.IsProperVariation c 1 ε f)
    (h : Riemannian.Variation.ProperSecondVariationData (I := I) g f 0 0 1)
    {a b : ℝ} {e : Fin (finrank ℝ E) → ℝ → E} {W : ℝ → 𝔼}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g (fun t ↦ f (0, t)) (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt (fun r ↦ f (0, r)) t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g (fun t ↦ f (0, t)) (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (f (0, t)) (e i t : TangentSpace I (f (0, t))) (e j t) =
        if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g (fun t ↦ f (0, t)) 0) ≤
      dist (f (0, 0)) (f (0, 1)))
    (hW : ContDiff ℝ 3 W)
    (hS : (fun t ↦ h.S (0, t)) = Riemannian.Variation.variationalField I f)
    (hV : Riemannian.Variation.variationalField I f =
      frameFieldOf (I := I) g (fun t ↦ f (0, t)) e W)
    (hDtS : (fun t ↦ h.DtS (0, t)) =
      frameFieldOf (I := I) g (fun t ↦ f (0, t)) e (deriv W)) :
    deriv (deriv (fun σ ↦ Riemannian.DCEnergy (I := I) g
        (fun t ↦ f (σ, t)) 0 1)) 0 = 0 ↔
      IsJacobiFieldAlongOn (I := I) g (fun t ↦ f (0, t))
        (Riemannian.Variation.variationalField I f)
        (fun t ↦ h.DtS (0, t)) 0 1 := by
  have hends := variationalField_endpoints_eq_zero_of_proper
    (I := I) (c := c) (a := (1 : ℝ)) (ε := ε) (f := f)
    hvariation.epsilon_pos hproper
  have hW0 : W 0 = 0 := by
    calc
      W 0 = frameVec (I := I) g (fun t ↦ f (0, t)) e
          (frameFieldOf (I := I) g (fun t ↦ f (0, t)) e W) 0 := by
            symm
            exact frameVec_frameFieldOf (I := I)
              (horth 0 (by constructor <;> linarith [ha])) W
      _ = frameVec (I := I) g (fun t ↦ f (0, t)) e
          (Riemannian.Variation.variationalField I f) 0 := by rw [← hV]
      _ = 0 := frameVec_eq_zero (I := I) (hV := hends.1)
  have hW1 : W 1 = 0 := by
    calc
      W 1 = frameVec (I := I) g (fun t ↦ f (0, t)) e
          (frameFieldOf (I := I) g (fun t ↦ f (0, t)) e W) 1 := by
            symm
            exact frameVec_frameFieldOf (I := I)
              (horth 1 (by constructor <;> linarith [hb])) W
      _ = frameVec (I := I) g (fun t ↦ f (0, t)) e
          (Riemannian.Variation.variationalField I f) 1 := by rw [← hV]
      _ = 0 := frameVec_eq_zero (I := I) (hV := hends.2)
  have hS_frame : (fun t ↦ h.S (0, t)) =
      frameFieldOf (I := I) g (fun t ↦ f (0, t)) e W := hS.trans hV
  have hiff := deriv_deriv_dcEnergy_eq_zero_iff_isJacobiFieldAlongOn_of_minimizing
    (I := I) g hg h (a := a) (b := b) ha hb hgeo hγc hPar horth hmin hW hW0 hW1
      hS_frame hDtS
  rw [← hV, ← hDtS] at hiff
  exact hiff

end MorganTianLib

#print axioms MorganTianLib.deriv_deriv_dcEnergy_eq_zero_iff_isJacobiFieldAlongOn_of_minimizing
