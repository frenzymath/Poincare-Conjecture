import DoCarmoLib.Riemannian.Connection.CovariantDerivativeAlong
import DoCarmoLib.Riemannian.Connection.ChartCurvature
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The along-curve derivative induced by the Levi-Civita connection

This file identifies `covDerivAlong` with the intrinsic Levi-Civita connection
on restrictions of global smooth vector fields. It then proves the uniqueness
part of do Carmo Ch. 2, Proposition 2.2 from additivity, the scalar Leibniz rule,
and that global-field compatibility.
-/

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff Matrix Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

namespace Tensor

theorem chartBasisVecFiber_self (p : M) (i : Fin (Module.finrank ℝ E)) :
    (chartBasisVecFiber (I := I) p i p : E) = (Module.finBasis ℝ E) i := by
  have h := mfderiv_extChartAt_chartBasisVecFiber (I := I) p i (mem_chart_source H p)
  rw [mfderiv_extChartAt_self] at h
  simpa using! h

end Tensor

/-! Frame-coordinate helpers for decomposing a smooth vector field locally. -/

def chartVectorFieldCoeff (alpha : M) (Z : SmoothVectorField I M)
    (i : Fin (Module.finrank ℝ E)) : M -> ℝ :=
  fun y => (Module.finBasis ℝ E).coord i
    ((trivializationAt E (TangentSpace I) alpha ⟨y, Z y⟩).2)

theorem chartVectorFieldCoeff_eq_repr (alpha : M) (Z : SmoothVectorField I M)
    {y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) alpha).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartVectorFieldCoeff alpha Z i y = (chartBasisFamily (I := I) alpha hy).repr (Z y) i := by
  set triv := trivializationAt E (TangentSpace I) alpha
  have hphi : (triv ⟨y, Z y⟩).2 = triv.continuousLinearEquivAt ℝ y hy (Z y) :=
    congrArg Prod.snd (triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy (Z y))
  show (Module.finBasis ℝ E).coord i ((triv ⟨y, Z y⟩).2) = _
  rw [hphi]
  unfold chartBasisFamily
  rw [Module.Basis.map_repr]
  rfl

theorem chartVectorFieldCoeff_contMDiffOn (alpha : M) (Z : SmoothVectorField I M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartVectorFieldCoeff alpha Z i)
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
  set triv := trivializationAt E (TangentSpace I) alpha
  have hsnd : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun y => (triv ⟨y, Z y⟩).2) triv.baseSet := by
    have hsec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => (TotalSpace.mk' E y (Z y) : TangentBundle I M)) triv.baseSet :=
      Z.smooth.contMDiffOn
    exact (triv.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞) (s := Z)).mp hsec
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)) :=
    (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contMDiff
  exact hL.comp_contMDiffOn hsnd

theorem vectorField_eq_sum_chartCoeff (alpha : M) (Z : SmoothVectorField I M)
    {y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) alpha).baseSet) :
    Z y = ∑ i, chartVectorFieldCoeff alpha Z i y • chartBasisVecFiber (I := I) alpha i y := by
  conv_lhs => rw [← (chartBasisFamily (I := I) alpha hy).sum_repr (Z y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartBasisFamily_apply, chartVectorFieldCoeff_eq_repr]

theorem chartVectorFieldCoeff_self (alpha : M) (W : SmoothVectorField I M)
    (a : Fin (Module.finrank ℝ E)) :
    chartVectorFieldCoeff (I := I) alpha W a alpha = Geodesic.chartCoord (E := E) a (W alpha) := by
  classical
  have hbase : alpha ∈ (trivializationAt E (TangentSpace I) alpha).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' alpha
  have h := vectorField_eq_sum_chartCoeff (I := I) alpha W hbase
  simp only [Tensor.chartBasisVecFiber_self] at h
  rw [Geodesic.chartCoord_def]
  have h2 : W alpha = (Module.finBasis ℝ E).equivFun.symm
      (fun b => chartVectorFieldCoeff (I := I) alpha W b alpha) := by
    rw [h]
    exact (Module.Basis.equivFun_symm_apply _ _).symm
  have h3 : (Module.finBasis ℝ E).equivFun (W alpha)
      = fun b => chartVectorFieldCoeff (I := I) alpha W b alpha := by
    rw [h2, LinearEquiv.apply_symm_apply]
  have h4 := congrFun h3 a
  rw [Module.Basis.equivFun_apply] at h4
  exact h4.symm

/-! Pointwise finite-sum linearity in the direction slot. -/

theorem AffineConnection.cov_smulSum_apply_left (nabla : AffineConnection I M)
    (Z : SmoothVectorField I M) (p : M) {ι : Type*} (s : Finset ι)
    (f : ι -> M -> ℝ) (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
    (V : ι -> SmoothVectorField I M) (X : SmoothVectorField I M)
    (hX : X p = ∑ i ∈ s, f i p • V i p) :
    (nabla.cov X Z) p = ∑ i ∈ s, f i p • (nabla.cov (V i) Z) p := by
  classical
  induction s using Finset.induction_on generalizing X with
  | empty =>
      have hXp : X p = (0 : SmoothVectorField I M) p := by simpa using hX
      rw [nabla.cov_congr_apply_left Z hXp, Finset.sum_empty]
      exact nabla.cov_zero_left Z p
  | @insert a s ha ih =>
      set Xtail : SmoothVectorField I M :=
        X - SmoothVectorField.smul (f a) (hf a) (V a) with hXtail
      have hXtailp : Xtail p = ∑ i ∈ s, f i p • V i p := by
        rw [hXtail, SmoothVectorField.sub_apply, SmoothVectorField.smul_apply,
          hX, Finset.sum_insert ha]
        abel
      have hsplit : X = SmoothVectorField.smul (f a) (hf a) (V a) + Xtail := by
        rw [hXtail]
        ext q
        rw [SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
        abel
      rw [hsplit, nabla.add_left, SmoothVectorField.add_apply,
        nabla.smul_left (f a) (hf a) (V a) Z, SmoothVectorField.smul_apply,
        ih Xtail hXtailp, Finset.sum_insert ha]

/-! Chain-rule helpers for the intrinsic curve velocity. -/

theorem hasMFDerivAt_smulRight_DCVelocity {c : ℝ -> M} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (DCVelocity (I := I) c t)) := by
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) I c t (mfderiv 𝓘(ℝ, ℝ) I c t) := hc.hasMFDerivAt
  convert h1 using 1
  ext
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, DCVelocity,
    ← ContinuousLinearMap.map_smul, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC
    {c : ℝ -> M} {t : ℝ} {p : M} {w : TangentSpace I (c t)}
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) I c t ((1 : ℝ →L[ℝ] ℝ).smulRight w))
    (hsrc : c t ∈ (extChartAt I p).source) :
    HasDerivAt (↑(extChartAt I p) ∘ c) (tangentCoordChange I (c t) p (c t) w) t := by
  replace hsrc := extChartAt_source I p ▸ hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc) hc).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← one_apply_eq_self (F := ℝ →L[ℝ] ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

theorem hasDerivAt_comp_curve_DC {gamma : M -> ℝ} {c : ℝ -> M} {t : ℝ}
    (hgamma : MDifferentiableAt I 𝓘(ℝ, ℝ) gamma (c t))
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    HasDerivAt (fun tau => gamma (c tau))
      (mfderiv I 𝓘(ℝ, ℝ) gamma (c t) (DCVelocity (I := I) c t)) t := by
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun tau => gamma (c tau)) t :=
    hgamma.comp t hc
  have hdiff : DifferentiableAt ℝ (fun tau => gamma (c tau)) t := hcomp.differentiableAt
  have hval : deriv (fun tau => gamma (c tau)) t
      = mfderiv I 𝓘(ℝ, ℝ) gamma (c t) (DCVelocity (I := I) c t) := by
    have h := DCVelocity_comp (I := I) (I' := 𝓘(ℝ, ℝ)) (f := gamma) t hgamma hc
    have hreal : DCVelocity (I := 𝓘(ℝ, ℝ)) (gamma ∘ c) t = deriv (gamma ∘ c) t := by
      unfold DCVelocity
      rw [mfderiv_eq_fderiv]
      rfl
    rw [hreal] at h
    change deriv (gamma ∘ c) t =
      mfderiv I 𝓘(ℝ, ℝ) gamma (c t) (DCVelocity (I := I) c t) at h
    change deriv (gamma ∘ c) t =
      mfderiv I 𝓘(ℝ, ℝ) gamma (c t) (DCVelocity (I := I) c t)
    exact h
  rw [← hval]
  exact hdiff.hasDerivAt

/-! Compatibility with the intrinsic Levi-Civita connection. -/

/-- **Math.** do Carmo Ch. 2, Proposition 2.2(c): restricting a global smooth
field `W` to a differentiable curve and differentiating along the curve agrees
with the Levi-Civita covariant derivative in any smooth direction field whose
value is the curve velocity. -/
theorem covDerivAlong_comp_smoothVectorField (g : RiemannianMetric I M)
    {c : ℝ -> M} {t : ℝ} (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (X W : SmoothVectorField I M) (hX : X (c t) = DCVelocity (I := I) c t) :
    covDerivAlong (I := I) g c (fun s => W (c s)) t
      = (g.leviCivitaConnection.cov X W) (c t) := by
  classical
  let p : M := c t
  let Z : Fin (Module.finrank ℝ E) -> SmoothVectorField I M :=
    fun a => chartFrameField (I := I) p a
  set f : Fin (Module.finrank ℝ E) -> M -> ℝ :=
    fun a => chartVectorFieldCoeff (I := I) p W a with hf
  have hBopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  have hpB : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hf_smooth : ∀ a, ContMDiffOn I 𝓘(ℝ) ∞ (f a)
      (trivializationAt E (TangentSpace I) p).baseSet :=
    fun a => chartVectorFieldCoeff_contMDiffOn (I := I) p W a
  choose gamma hgamma_smooth hgamma_ev using fun a =>
    exists_contMDiff_eventuallyEq (I := I) hBopen (hf_smooth a) hpB

  have hW'smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, ∑ a, gamma a q • Z a q⟩ : TangentBundle I M)) :=
    ContMDiff.sum_section fun a _ =>
      ContMDiff.smul_section (hgamma_smooth a) (Z a).smooth
  set W' : SmoothVectorField I M :=
    ⟨fun q => ∑ a, gamma a q • Z a q, hW'smooth⟩ with hW'def
  have hW'def_apply : ∀ q, W' q = ∑ a, gamma a q • Z a q := fun q => rfl
  have hW'_ev : ⇑W =ᶠ[nhds p] ⇑W' := by
    filter_upwards [eventually_all.mpr fun a => hgamma_ev a,
      eventually_all.mpr fun a => chartFrameField_eventuallyEq (I := I) p a,
      hBopen.eventually_mem hpB] with q hgammaq hZq hqB
    rw [vectorField_eq_sum_chartCoeff (I := I) p W hqB, hW'def_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgammaq a, hZq a]

  have hZp : ∀ a, (Z a p : E) = (Module.finBasis ℝ E a : E) := fun a => by
    rw [show Z a = chartFrameField (I := I) p a from rfl,
      chartFrameField_apply_self, Tensor.chartBasisVecFiber_self]
  have hgammap : ∀ a, gamma a p = Geodesic.chartCoord (E := E) a (W p) := fun a => by
    rw [(hgamma_ev a).self_of_nhds]
    exact chartVectorFieldCoeff_self (I := I) p W a

  have htrans : ∀ q ∈ (chartAt H p).source, ∀ a,
      tangentCoordChange I q p q (chartBasisVecFiber (I := I) p a q)
        = (Module.finBasis ℝ E a : E) := by
    intro q hq a
    have hv := (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) p) hq (chartBasisVecFiber (I := I) p a q)).trans
      (trivializationAt_chartBasisVec_snd (I := I) p a hq)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hq] at hv
    simpa using! hv

  have hu_deriv : deriv (fun s => extChartAt I p (c s)) t = DCVelocity (I := I) c t := by
    have hsrc : c t ∈ (extChartAt I p).source := by
      change p ∈ (extChartAt I p).source
      exact mem_extChartAt_source (I := I) p
    have hd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC
      (hasMFDerivAt_smulRight_DCVelocity (I := I) hc) hsrc
    rw [tangentCoordChange_self hsrc] at hd
    change deriv (↑(extChartAt I p) ∘ c) t = DCVelocity (I := I) c t
    exact hd.deriv

  have hFrep_ev : chartFieldRep (I := I) c p (fun tau => W (c tau))
      =ᶠ[nhds t] fun tau => ∑ a, gamma a (c tau) • (Module.finBasis ℝ E a : E) := by
    have hcont : ContinuousAt c t := hc.continuousAt
    have hev : ∀ᶠ tau in nhds t,
        (∀ a, gamma a (c tau) = f a (c tau)) ∧
          c tau ∈ (trivializationAt E (TangentSpace I) p).baseSet ∧
          c tau ∈ (chartAt H p).source := by
      have h1 : ∀ᶠ tau in nhds t, ∀ a, gamma a (c tau) = f a (c tau) :=
        hcont.eventually (eventually_all.mpr fun a => hgamma_ev a)
      have h2 : ∀ᶠ tau in nhds t,
          c tau ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
        hcont.eventually_mem (hBopen.mem_nhds hpB)
      have h3 : ∀ᶠ tau in nhds t, c tau ∈ (chartAt H p).source := by
        have hpt : c t ∈ (chartAt H p).source := by
          change p ∈ (chartAt H p).source
          exact mem_chart_source H p
        exact hcont.eventually_mem ((chartAt H p).open_source.mem_nhds hpt)
      filter_upwards [h1, h2, h3] with tau htau1 htau2 htau3 using ⟨htau1, htau2, htau3⟩
    filter_upwards [hev] with tau htau
    obtain ⟨hgammatau, htauB, htausrc⟩ := htau
    show tangentCoordChange I (c tau) p (c tau) (W (c tau))
        = ∑ a, gamma a (c tau) • (Module.finBasis ℝ E a : E)
    rw [vectorField_eq_sum_chartCoeff (I := I) p W htauB, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, htrans (c tau) htausrc a, hgammatau a]

  have hderiv_lhs : deriv (chartFieldRep (I := I) c p (fun tau => W (c tau))) t
      = ∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E) := by
    have hHDcomp : ∀ a, HasDerivAt (fun tau => gamma a (c tau)) (X.dir (gamma a) p) t := by
      intro a
      have h := hasDerivAt_comp_curve_DC (I := I)
        ((hgamma_smooth a).mdifferentiableAt (by simp)) hc
      simpa only [SmoothVectorField.dir,
        show X p = DCVelocity (I := I) c t from hX] using h
    have hHD : HasDerivAt (fun tau => ∑ a, gamma a (c tau) • (Module.finBasis ℝ E a : E))
        (∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E)) t :=
      HasDerivAt.fun_sum (fun a _ => (hHDcomp a).smul_const (Module.finBasis ℝ E a : E))
    exact (hHD.congr_of_eventuallyEq hFrep_ev).deriv

  have hXdecomp : X p = ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
      • Z i p := by
    calc
      X p = DCVelocity (I := I) c t := hX
      _ = ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
          • (Module.finBasis ℝ E i : E) := by
            simpa only [Geodesic.chartCoord_def] using
              ((Module.finBasis ℝ E).sum_repr (DCVelocity (I := I) c t)).symm
      _ = ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
          • Z i p := Finset.sum_congr rfl fun i _ => by rw [hZp i]

  have hcovZ : ∀ a, (g.leviCivitaConnection.cov X (Z a)) p
      = ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
          • ∑ m, chartChristoffel (I := I) g p i a m (extChartAt I p p)
              • (Module.finBasis ℝ E m : E) := by
    intro a
    rw [g.leviCivitaConnection.cov_smulSum_apply_left (Z a) p Finset.univ
      (fun i _ => Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t))
      (fun _ => contMDiff_const) Z X (by simpa using hXdecomp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [show Z i = chartFrameField (I := I) p i from rfl,
      show Z a = chartFrameField (I := I) p a from rfl,
      leviCivita_cov_chartFrameField_expansion (I := I) g p i a
        (mem_chart_source H p) (fun b => chartFrameField_eventuallyEq (I := I) p b)]
    exact Finset.sum_congr rfl fun m _ => by rw [Tensor.chartBasisVecFiber_self]

  have hL : covDerivAlong (I := I) g c (fun tau => W (c tau)) t
      = (∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E))
        + ∑ m, (∑ i, ∑ j, chartChristoffel (I := I) g p i j m (extChartAt I p p)
            * Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
            * Geodesic.chartCoord (E := E) j (W p)) • (Module.finBasis ℝ E m : E) := by
    rw [covDerivAlong_def, covariantDerivCoord_def, hderiv_lhs, hu_deriv,
      chartFieldRep_self, Geodesic.chartChristoffelContraction_def]

  have hR : (g.leviCivitaConnection.cov X W) p
      = (∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E))
        + ∑ m, (∑ i, ∑ j, chartChristoffel (I := I) g p i j m (extChartAt I p p)
            * Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
            * Geodesic.chartCoord (E := E) j (W p)) • (Module.finBasis ℝ E m : E) := by
    rw [g.leviCivitaConnection.cov_congr_apply_eventuallyEq_right X hW'_ev,
      g.leviCivitaConnection.cov_smulSum_apply X p Finset.univ gamma hgamma_smooth Z W' hW'def_apply]
    have hstep : ∀ a, X.dir (gamma a) p • Z a p
          + gamma a p • (g.leviCivitaConnection.cov X (Z a)) p
        = X.dir (gamma a) p • (Module.finBasis ℝ E a : E)
          + Geodesic.chartCoord (E := E) a (W p)
              • ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
                  • ∑ m, chartChristoffel (I := I) g p i a m (extChartAt I p p)
                      • (Module.finBasis ℝ E m : E) := by
      intro a
      rw [hZp a, hgammap a, hcovZ a]
    rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_add_distrib]
    congr 1
    have hB : ∀ a, (∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
          • ∑ m, chartChristoffel (I := I) g p i a m (extChartAt I p p)
              • (Module.finBasis ℝ E m : E))
        = ∑ m, (∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
            * chartChristoffel (I := I) g p i a m (extChartAt I p p))
          • (Module.finBasis ℝ E m : E) := by
      intro a
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => (Finset.sum_smul).symm
    calc
      ∑ a, Geodesic.chartCoord (E := E) a (W p)
            • ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
                • ∑ m, chartChristoffel (I := I) g p i a m (extChartAt I p p)
                    • (Module.finBasis ℝ E m : E)
        = ∑ a, ∑ m, (Geodesic.chartCoord (E := E) a (W p)
              * ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
                  * chartChristoffel (I := I) g p i a m (extChartAt I p p))
            • (Module.finBasis ℝ E m : E) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hB a, Finset.smul_sum]
          exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
      _ = ∑ m, (∑ a, Geodesic.chartCoord (E := E) a (W p)
              * ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
                  * chartChristoffel (I := I) g p i a m (extChartAt I p p))
            • (Module.finBasis ℝ E m : E) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => (Finset.sum_smul).symm
      _ = ∑ m, (∑ i, ∑ j, chartChristoffel (I := I) g p i j m (extChartAt I p p)
              * Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
              * Geodesic.chartCoord (E := E) j (W p)) • (Module.finBasis ℝ E m : E) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          congr 1
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
          ring
  change covDerivAlong (I := I) g c (fun tau => W (c tau)) t
      = (g.leviCivitaConnection.cov X W) p
  rw [hL, hR]

/-! Uniqueness from the three axioms of the derivative along a curve. -/

private abbrev AlongField (c : ℝ -> M) := (s : ℝ) -> TangentSpace I (c s)

private theorem candidate_congr_of_eventuallyEq
    {c : ℝ -> M} {t : ℝ} (D : AlongField (I := I) c -> AlongField (I := I) c)
    (hsmul : ∀ (f : ℝ -> ℝ) (V : AlongField (I := I) c),
      DifferentiableAt ℝ f t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      D (fun s => f s • V s) t = deriv f t • V t + f t • D V t)
    {V W : AlongField (I := I) c}
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t)
    (hVW : V =ᶠ[nhds t] W) :
    D V t = D W t := by
  obtain ⟨U, hU_nhds, hU⟩ := hVW.exists_mem
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hU_nhds
  let chi : ContDiffBump t := ⟨eps / 4, eps / 2, by positivity, by linarith⟩
  have hchi_diff : DifferentiableAt ℝ (fun s => chi s) t :=
    (chi.contDiff (n := 1)).differentiable (by norm_num) t
  have hchi_t : chi t = 1 := chi.eventuallyEq_one.self_of_nhds
  have hchi_deriv : deriv (fun s => chi s) t = 0 := by
    rw [chi.eventuallyEq_one.deriv_eq]
    simp
  have hscaled : (fun s => chi s • V s) = (fun s => chi s • W s) := by
    funext s
    by_cases hs : s ∈ ball t eps
    · rw [hU (hball hs)]
    · have hdist : eps ≤ dist s t := by simpa [mem_ball, not_lt] using hs
      have hzero : chi s = 0 := chi.zero_of_le_dist (by
        show eps / 2 ≤ dist s t
        linarith)
      rw [hzero, zero_smul, zero_smul]
  have h := congrArg (fun Z => D Z t) hscaled
  rw [hsmul (fun s => chi s) V hchi_diff hV,
    hsmul (fun s => chi s) W hchi_diff hW, hchi_t, hchi_deriv] at h
  simpa using h

/-- **Math.** The covariant derivative at a time depends only on the germ of the
field along the curve at that time. -/
theorem covDerivAlong_congr (g : RiemannianMetric I M) {c : ℝ -> M}
    {V W : AlongField (I := I) c} {t : ℝ} (h : V =ᶠ[nhds t] W) :
    covDerivAlong (I := I) g c V t = covDerivAlong (I := I) g c W t := by
  have hrep : chartFieldRep (I := I) c (c t) V =ᶠ[nhds t]
      chartFieldRep (I := I) c (c t) W := by
    filter_upwards [h] with s hs
    simp only [chartFieldRep_apply, hs]
  rw [covDerivAlong_def, covDerivAlong_def, covariantDerivCoord_def,
    covariantDerivCoord_def, hrep.deriv_eq, hrep.self_of_nhds]

/-- **Math.** The fixed-chart reading of the restriction of a smooth vector field
to a `C^1` curve is differentiable. -/
theorem differentiableAt_chartFieldRep_comp_smoothVectorField
    {c : ℝ -> M} {t : ℝ} (X : SmoothVectorField I M)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 1 c t) :
    DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) (fun s => X (c s))) t := by
  let e := trivializationAt E (TangentSpace I) (c t)
  have hpbase : c t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (c t)
  have hsnd : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun q => (e ⟨q, X q⟩).2) e.baseSet := by
    have hsec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun q => (TotalSpace.mk' E q (X q) : TangentBundle I M)) e.baseSet :=
      X.smooth.contMDiffOn
    exact (e.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)
      (s := fun q => X q)).mp hsec
  have hsndAt : ContMDiffAt I 𝓘(ℝ, E) 1 (fun q => (e ⟨q, X q⟩).2) (c t) :=
    ((hsnd.contMDiffAt (e.open_baseSet.mem_nhds hpbase)).of_le (by norm_num))
  have hcompM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun s => (e ⟨c s, X (c s)⟩).2) t := hsndAt.comp t hc
  have hcomp : DifferentiableAt ℝ (fun s => (e ⟨c s, X (c s)⟩).2) t :=
    (contMDiffAt_iff_contDiffAt.mp hcompM).differentiableAt (by norm_num)
  have hcbase : ∀ᶠ s in nhds t, c s ∈ e.baseSet :=
    hc.continuousAt.eventually (e.open_baseSet.mem_nhds hpbase)
  have hrep : chartFieldRep (I := I) c (c t) (fun s => X (c s)) =ᶠ[nhds t]
      (fun s => (e ⟨c s, X (c s)⟩).2) := by
    filter_upwards [hcbase] with s hsbase
    have hsrc : c s ∈ (chartAt H (c t)).source := hsbase
    have hself : c s ∈ (extChartAt I (c s)).source := mem_extChartAt_source (c s)
    have hfixed : c s ∈ (extChartAt I (c t)).source := by
      rwa [extChartAt_source]
    let a := chartFieldRep (I := I) c (c t) (fun r => X (c r)) s
    have hread : X (c s) = e.symm (c s) a := by
      rw [trivializationAt_symm_eq_tangentCoordChange (I := I) (c t) hsrc]
      have hcomp := tangentCoordChange_comp (I := I)
        (w := c s) (x := c t) (y := c s) (z := c s) (v := X (c s))
        ⟨⟨hself, hfixed⟩, hself⟩
      rw [tangentCoordChange_self hself] at hcomp
      exact hcomp.symm
    change a = (e ⟨c s, X (c s)⟩).2
    rw [hread]
    exact (congrArg Prod.snd (e.apply_mk_symm hsbase a)).symm
  exact hcomp.congr_of_eventuallyEq hrep

private theorem covDerivAlong_unique_of_global
    (g : RiemannianMetric I M) {c : ℝ -> M} {t : ℝ}
    (hc : ContinuousAt c t)
    (D : AlongField (I := I) c -> AlongField (I := I) c)
    (hadd : ∀ (V W : AlongField (I := I) c),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t ->
      D (fun s => V s + W s) t = D V t + D W t)
    (hsmul : ∀ (f : ℝ -> ℝ) (V : AlongField (I := I) c),
      DifferentiableAt ℝ f t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      D (fun s => f s • V s) t = deriv f t • V t + f t • D V t)
    (hglobal : ∀ X : SmoothVectorField I M,
      D (fun s => X (c s)) t =
        covDerivAlong (I := I) g c (fun s => X (c s)) t)
    (hrestr : ∀ X : SmoothVectorField I M,
      DifferentiableAt ℝ
        (chartFieldRep (I := I) c (c t) (fun s => X (c s))) t)
    (V : AlongField (I := I) c)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    D V t = covDerivAlong (I := I) g c V t := by
  classical
  let e := trivializationAt E (TangentSpace I) (c t)
  have hpbase : c t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (c t)
  choose X hX using fun i : Fin (Module.finrank ℝ E) =>
    exists_smoothVectorField_eventuallyEq (I := I)
      (σ := fun q => Tensor.chartBasisVecFiber (I := I) (c t) i q)
      e.open_baseSet (Tensor.chartBasisVec_contMDiffOn (I := I) (c t) i) hpbase
  have hXc : ∀ i, (fun s => X i (c s)) =ᶠ[nhds t]
      (fun s => Tensor.chartBasisVecFiber (I := I) (c t) i (c s)) := fun i =>
    hc.eventually (hX i)
  have hcbase : ∀ᶠ s in nhds t, c s ∈ e.baseSet :=
    hc.eventually (e.open_baseSet.mem_nhds hpbase)
  let a : Fin (Module.finrank ℝ E) -> ℝ -> ℝ := fun i s =>
    Geodesic.chartCoord (E := E) i (chartFieldRep (I := I) c (c t) V s)
  let R : Fin (Module.finrank ℝ E) -> AlongField (I := I) c := fun i s => X i (c s)
  let F : Fin (Module.finrank ℝ E) -> AlongField (I := I) c :=
    fun i s => a i s • R i s
  let S : AlongField (I := I) c := fun s => ∑ i, F i s
  have ha : ∀ i, DifferentiableAt ℝ (a i) t := by
    intro i
    exact (Geodesic.chartCoordFunctional (E := E) i).differentiableAt.comp t hV
  have hR : ∀ i, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) (R i)) t := fun i => hrestr (X i)
  have hF : ∀ i, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) (F i)) t := by
    intro i
    rw [show F i = fun s => a i s • R i s from rfl,
      chartFieldRep_smul (I := I) c (c t) (a i) (R i)]
    exact (ha i).smul (hR i)
  have hVS : V =ᶠ[nhds t] S := by
    filter_upwards [hcbase, Filter.eventually_all.mpr hXc] with s hsbase hsX
    have hsrc : c s ∈ (chartAt H (c t)).source := hsbase
    have hself : c s ∈ (extChartAt I (c s)).source := mem_extChartAt_source (c s)
    have hfixed : c s ∈ (extChartAt I (c t)).source := by
      rwa [extChartAt_source]
    have hread : V s = e.symm (c s) (chartFieldRep (I := I) c (c t) V s) := by
      rw [trivializationAt_symm_eq_tangentCoordChange (I := I) (c t) hsrc]
      have hcomp := tangentCoordChange_comp (I := I)
        (w := c s) (x := c t) (y := c s) (z := c s) (v := V s)
        ⟨⟨hself, hfixed⟩, hself⟩
      rw [tangentCoordChange_self hself] at hcomp
      exact hcomp.symm
    rw [hread, trivializationAt_symm_eq_sum_chartBasisVecFiber
      (I := I) (c t) (c s) (chartFieldRep (I := I) c (c t) V s) hsrc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show F i s = a i s • R i s from rfl, show R i s = X i (c s) from rfl,
      show a i s = Geodesic.chartCoord (E := E) i
        (chartFieldRep (I := I) c (c t) V s) from rfl, hsX i]
  let sumF : Finset (Fin (Module.finrank ℝ E)) -> AlongField (I := I) c :=
    fun u s => ∑ i ∈ u, F i s
  have hrep_zero : chartFieldRep (I := I) c (c t) (fun _ => 0) = 0 := by
    funext s
    exact map_zero (tangentCoordChange I (c s) (c t) (c s))
  have hrep_sum : ∀ u, chartFieldRep (I := I) c (c t) (sumF u) =
      ∑ i ∈ u, chartFieldRep (I := I) c (c t) (F i) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa [sumF] using hrep_zero
    | @insert i u hi ih =>
        have hsplit : sumF (insert i u) = fun s => F i s + sumF u s := by
          funext s
          simp [sumF, hi]
        rw [hsplit, chartFieldRep_add (I := I) c (c t) (F i) (sumF u), ih,
          Finset.sum_insert hi]
  have hsum_diff : ∀ u, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) (sumF u)) t := by
    intro u
    rw [hrep_sum u]
    exact DifferentiableAt.sum (u := u) fun i _ => hF i
  have hD0 : D (fun _ => 0) t = 0 := by
    have h := hsmul (fun _ => 0) V (differentiableAt_const (c := (0 : ℝ))) hV
    simpa using h
  have hDsum : ∀ u, D (sumF u) t = ∑ i ∈ u, D (F i) t := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa [sumF] using hD0
    | @insert i u hi ih =>
        have hsplit : sumF (insert i u) = fun s => F i s + sumF u s := by
          funext s
          simp [sumF, hi]
        rw [hsplit, hadd (F i) (sumF u) (hF i) (hsum_diff u), ih,
          Finset.sum_insert hi]
  have hC0 : covDerivAlong (I := I) g c (fun _ => 0) t = 0 := by
    have h := covDerivAlong_smul (I := I) g c (fun _ => 0) V
      (differentiableAt_const (c := (0 : ℝ))) hV
    simpa using h
  have hCsum : ∀ u, covDerivAlong (I := I) g c (sumF u) t =
      ∑ i ∈ u, covDerivAlong (I := I) g c (F i) t := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa [sumF] using hC0
    | @insert i u hi ih =>
        have hsplit : sumF (insert i u) = fun s => F i s + sumF u s := by
          funext s
          simp [sumF, hi]
        rw [hsplit, covDerivAlong_add (I := I) g c (F i) (sumF u)
          (hF i) (hsum_diff u), ih, Finset.sum_insert hi]
  have hterm : ∀ i, D (F i) t = covDerivAlong (I := I) g c (F i) t := by
    intro i
    rw [show F i = fun s => a i s • R i s from rfl,
      hsmul (a i) (R i) (ha i) (hR i),
      covDerivAlong_smul (I := I) g c (a i) (R i) (ha i) (hR i)]
    rw [show R i = fun s => X i (c s) from rfl, hglobal (X i)]
  have hDS : D S t = covDerivAlong (I := I) g c S t := by
    have hSuniv : S = sumF Finset.univ := by
      funext s
      simp [S, sumF]
    rw [hSuniv, hDsum Finset.univ, hCsum Finset.univ]
    exact Finset.sum_congr rfl fun i _ => hterm i
  calc
    D V t = D S t := candidate_congr_of_eventuallyEq D hsmul hV (by
      have hrepVS : chartFieldRep (I := I) c (c t) V =ᶠ[nhds t]
          chartFieldRep (I := I) c (c t) S := by
        filter_upwards [hVS] with s hs
        simp only [chartFieldRep_apply, hs]
      exact hV.congr_of_eventuallyEq hrepVS.symm) hVS
    _ = covDerivAlong (I := I) g c S t := hDS
    _ = covDerivAlong (I := I) g c V t :=
      (covDerivAlong_congr (I := I) g hVS).symm

private theorem covDerivAlong_unique_of_contMDiffAt_global
    (g : RiemannianMetric I M) {c : ℝ -> M} {t : ℝ}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 1 c t)
    (D : AlongField (I := I) c -> AlongField (I := I) c)
    (hadd : ∀ (V W : AlongField (I := I) c),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t ->
      D (fun s => V s + W s) t = D V t + D W t)
    (hsmul : ∀ (f : ℝ -> ℝ) (V : AlongField (I := I) c),
      DifferentiableAt ℝ f t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      D (fun s => f s • V s) t = deriv f t • V t + f t • D V t)
    (hglobal : ∀ X : SmoothVectorField I M,
      D (fun s => X (c s)) t =
        covDerivAlong (I := I) g c (fun s => X (c s)) t)
    (V : AlongField (I := I) c)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    D V t = covDerivAlong (I := I) g c V t :=
  covDerivAlong_unique_of_global (I := I) g hc.continuousAt D hadd hsmul hglobal
    (fun X => differentiableAt_chartFieldRep_comp_smoothVectorField (I := I) X hc) V hV

/-- **Math.** Pointwise uniqueness in do Carmo Ch. 2, Proposition 2.2: the
intrinsic covariant derivative along a `C^1` curve is the unique operator
satisfying additivity, the scalar Leibniz rule, and compatibility with the
Levi-Civita derivative of ambient smooth vector fields. -/
theorem covDerivAlong_unique_of_contMDiffAt
    (g : RiemannianMetric I M) {c : ℝ -> M} {t : ℝ}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 1 c t)
    (D : ((s : ℝ) -> TangentSpace I (c s)) ->
      ((s : ℝ) -> TangentSpace I (c s)))
    (hadd : ∀ (V W : (s : ℝ) -> TangentSpace I (c s)),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t ->
      D (fun s => V s + W s) t = D V t + D W t)
    (hsmul : ∀ (f : ℝ -> ℝ) (V : (s : ℝ) -> TangentSpace I (c s)),
      DifferentiableAt ℝ f t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      D (fun s => f s • V s) t = deriv f t • V t + f t • D V t)
    (hcomp : ∀ (X W : SmoothVectorField I M),
      X (c t) = DCVelocity (I := I) c t ->
      D (fun s => W (c s)) t =
        (g.leviCivitaConnection.cov X W) (c t))
    (V : (s : ℝ) -> TangentSpace I (c s))
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    D V t = covDerivAlong (I := I) g c V t := by
  obtain ⟨X, hX⟩ :=
    exists_smoothVectorField_eq (I := I) (c t) (DCVelocity (I := I) c t)
  refine covDerivAlong_unique_of_contMDiffAt_global (I := I) g hc D hadd hsmul ?_ V hV
  intro W
  calc
    D (fun s => W (c s)) t =
        (g.leviCivitaConnection.cov X W) (c t) := hcomp X W hX
    _ = covDerivAlong (I := I) g c (fun s => W (c s)) t :=
      (covDerivAlong_comp_smoothVectorField (I := I) g
        (hc.mdifferentiableAt (by norm_num)) X W hX).symm

/-- **Math.** Global uniqueness in do Carmo Ch. 2, Proposition 2.2: two
derivatives along a `C^1` curve that obey additivity, Leibniz, and the ambient
Levi-Civita compatibility rule agree on every differentiable along-field. -/
theorem covDerivAlong_unique
    (g : RiemannianMetric I M) {c : ℝ -> M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    (D : ((s : ℝ) -> TangentSpace I (c s)) ->
      ((s : ℝ) -> TangentSpace I (c s)))
    (hadd : ∀ (t : ℝ) (V W : (s : ℝ) -> TangentSpace I (c s)),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t ->
      D (fun s => V s + W s) t = D V t + D W t)
    (hsmul : ∀ (t : ℝ) (f : ℝ -> ℝ)
      (V : (s : ℝ) -> TangentSpace I (c s)),
      DifferentiableAt ℝ f t ->
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ->
      D (fun s => f s • V s) t = deriv f t • V t + f t • D V t)
    (hcomp : ∀ (t : ℝ) (X W : SmoothVectorField I M),
      X (c t) = DCVelocity (I := I) c t ->
      D (fun s => W (c s)) t =
        (g.leviCivitaConnection.cov X W) (c t))
    (V : (s : ℝ) -> TangentSpace I (c s))
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    D V = covDerivAlong (I := I) g c V := by
  funext t
  exact covDerivAlong_unique_of_contMDiffAt (I := I) g hc.contMDiffAt D
    (hadd t) (hsmul t) (hcomp t) V (hV t)

end Riemannian

end
