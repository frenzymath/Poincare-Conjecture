import DoCarmoLib.Riemannian.Connection.CovariantDerivativeAlongLeviCivita

/-!
# Covariant derivative along a curve for an affine connection

This file constructs the intrinsic covariant derivative along a curve for an
arbitrary affine connection, proves its characteristic laws and uniqueness,
and identifies its Levi-Civita specialization with the existing Riemannian
operator.
-/

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff Matrix Bundle

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A global smooth extension of the `i`th coordinate vector of the chart at
`alpha`, chosen to agree with that coordinate field near `p` whenever `p` lies
in the chart. -/
noncomputable def chartFrameFieldAt (alpha p : M)
    (i : Fin (Module.finrank ℝ E)) : SmoothVectorField I M :=
  by
    classical
    exact if hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet then
      (exists_smoothVectorField_eventuallyEq (I := I)
        (σ := fun q => Tensor.chartBasisVecFiber (I := I) alpha i q)
        (trivializationAt E (TangentSpace I) alpha).open_baseSet
        (Tensor.chartBasisVec_contMDiffOn (I := I) alpha i) hp).choose
    else 0

theorem chartFrameFieldAt_eventuallyEq (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source) (i : Fin (Module.finrank ℝ E)) :
    ⇑(chartFrameFieldAt (I := I) alpha p i) =ᶠ[nhds p]
      fun q => Tensor.chartBasisVecFiber (I := I) alpha i q := by
  have hpbase : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := hp
  rw [chartFrameFieldAt, dif_pos hpbase]
  exact (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => Tensor.chartBasisVecFiber (I := I) alpha i q)
    (trivializationAt E (TangentSpace I) alpha).open_baseSet
    (Tensor.chartBasisVec_contMDiffOn (I := I) alpha i) hpbase).choose_spec

/-- **Math.** A coordinate frame vector reads as the corresponding standard basis vector
in its own chart. -/
theorem tangentCoordChange_chartBasisVecFiber (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source) (i : Fin (Module.finrank ℝ E)) :
    tangentCoordChange I p alpha p
        (Tensor.chartBasisVecFiber (I := I) alpha i p) =
      (Module.finBasis ℝ E i : E) := by
  have h := (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) alpha) hp
      (Tensor.chartBasisVecFiber (I := I) alpha i p)).trans
    (trivializationAt_chartBasisVec_snd (I := I) alpha i hp)
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hp] at h
  simpa using! h

/-- **Math.** Scalar connection coefficients of a fixed smooth frame in the chart at
`alpha`.  Keeping the frame fixed makes these coefficients smoothly dependent
on the foot. -/
def AffineConnection.chartConnectionCoeff (nabla : AffineConnection I M)
    (alpha : M) (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (i j m : Fin (Module.finrank ℝ E)) : M → ℝ :=
  chartVectorFieldCoeff (I := I) alpha (nabla.cov (Y i) (Y j)) m

theorem AffineConnection.chartConnectionCoeff_contMDiffOn
    (nabla : AffineConnection I M) (alpha : M)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (i j m : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (nabla.chartConnectionCoeff alpha Y i j m)
      (trivializationAt E (TangentSpace I) alpha).baseSet :=
  chartVectorFieldCoeff_contMDiffOn (I := I) alpha (nabla.cov (Y i) (Y j)) m

/-- **Math.** The connection term in the chart at `alpha`, evaluated at the foot `p`. -/
def AffineConnection.chartContractionAt (nabla : AffineConnection I M)
    (alpha p : M) (v w : E) : E :=
  ∑ i, ∑ j,
    (Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w) •
      tangentCoordChange I p alpha p
        ((nabla.cov (chartFrameFieldAt (I := I) alpha p i)
          (chartFrameFieldAt (I := I) alpha p j)) p)

theorem AffineConnection.chartContractionAt_add_right
    (nabla : AffineConnection I M) (alpha p : M) (v w z : E) :
    nabla.chartContractionAt alpha p v (w + z) =
      nabla.chartContractionAt alpha p v w + nabla.chartContractionAt alpha p v z := by
  simp only [AffineConnection.chartContractionAt,
    ← Geodesic.chartCoordFunctional_apply, map_add, mul_add, add_smul,
    Finset.sum_add_distrib]

theorem AffineConnection.chartContractionAt_smul_right
    (nabla : AffineConnection I M) (alpha p : M) (v w : E) (a : ℝ) :
    nabla.chartContractionAt alpha p v (a • w) =
      a • nabla.chartContractionAt alpha p v w := by
  simp only [AffineConnection.chartContractionAt,
    ← Geodesic.chartCoordFunctional_apply, map_smul, smul_eq_mul,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

/-- **Math.** The pointwise connection term may be computed with any fixed smooth frame
that agrees near the foot with the coordinate frame. -/
theorem AffineConnection.chartContractionAt_eq_of_frame
    (nabla : AffineConnection I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (hY : ∀ i, ⇑(Y i) =ᶠ[nhds p]
      fun q => Tensor.chartBasisVecFiber (I := I) alpha i q)
    (v w : E) :
    nabla.chartContractionAt alpha p v w =
      ∑ i, ∑ j,
        (Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w) •
          tangentCoordChange I p alpha p ((nabla.cov (Y i) (Y j)) p) := by
  classical
  rw [AffineConnection.chartContractionAt]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi : ⇑(chartFrameFieldAt (I := I) alpha p i) =ᶠ[nhds p] ⇑(Y i) :=
    (chartFrameFieldAt_eventuallyEq (I := I) alpha hp i).trans (hY i).symm
  have hj : ⇑(chartFrameFieldAt (I := I) alpha p j) =ᶠ[nhds p] ⇑(Y j) :=
    (chartFrameFieldAt_eventuallyEq (I := I) alpha hp j).trans (hY j).symm
  have hcov :
      (nabla.cov (chartFrameFieldAt (I := I) alpha p i)
        (chartFrameFieldAt (I := I) alpha p j)) p =
        (nabla.cov (Y i) (Y j)) p := by
    calc
      _ = (nabla.cov (Y i) (chartFrameFieldAt (I := I) alpha p j)) p :=
        nabla.cov_congr_apply_left _ hi.self_of_nhds
      _ = (nabla.cov (Y i) (Y j)) p :=
        nabla.cov_congr_apply_eventuallyEq_right (Y i) hj
  rw [hcov]

/-- **Math.** Coordinate expansion of the derivative of two fixed smooth frame fields.
Its scalar coefficients are `chartConnectionCoeff`, hence smooth on the chart. -/
theorem AffineConnection.tangentCoordChange_cov_frame_eq_sum_chartConnectionCoeff
    (nabla : AffineConnection I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (i j : Fin (Module.finrank ℝ E)) :
    tangentCoordChange I p alpha p ((nabla.cov (Y i) (Y j)) p) =
      ∑ m, nabla.chartConnectionCoeff alpha Y i j m p •
        (Module.finBasis ℝ E m : E) := by
  classical
  rw [vectorField_eq_sum_chartCoeff (I := I) alpha (nabla.cov (Y i) (Y j)) hp,
    map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, tangentCoordChange_chartBasisVecFiber (I := I) alpha hp]
  rfl

/-- **Math.** Fully scalar fixed-frame formula for the chart connection term. -/
theorem AffineConnection.chartContractionAt_eq_sum_chartConnectionCoeff
    (nabla : AffineConnection I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (hY : ∀ i, ⇑(Y i) =ᶠ[nhds p]
      fun q => Tensor.chartBasisVecFiber (I := I) alpha i q)
    (v w : E) :
    nabla.chartContractionAt alpha p v w =
      ∑ i, ∑ j,
        (Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w) •
          ∑ m, nabla.chartConnectionCoeff alpha Y i j m p •
            (Module.finBasis ℝ E m : E) := by
  rw [nabla.chartContractionAt_eq_of_frame alpha hp Y hY]
  simp_rw [nabla.tangentCoordChange_cov_frame_eq_sum_chartConnectionCoeff alpha hp Y]

/-- **Math.** The coordinate formula for `nabla.covDerivAlong` in an arbitrary chart. -/
def AffineConnection.covDerivAlongInChart (nabla : AffineConnection I M)
    (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (alpha : M) (t : ℝ) : E :=
  deriv (chartFieldRep (I := I) c alpha V) t +
    nabla.chartContractionAt alpha (c t)
      (deriv (fun s => extChartAt I alpha (c s)) t)
      (chartFieldRep (I := I) c alpha V t)

theorem AffineConnection.covDerivAlongInChart_add (nabla : AffineConnection I M)
    (c : ℝ → M) (V W : ∀ t, TangentSpace I (c t)) (alpha : M) {t : ℝ}
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha W) t) :
    nabla.covDerivAlongInChart c (fun s => V s + W s) alpha t =
      nabla.covDerivAlongInChart c V alpha t +
        nabla.covDerivAlongInChart c W alpha t := by
  rw [AffineConnection.covDerivAlongInChart, AffineConnection.covDerivAlongInChart,
    AffineConnection.covDerivAlongInChart, chartFieldRep_add, deriv_add hV hW,
    Pi.add_apply, nabla.chartContractionAt_add_right]
  abel

theorem AffineConnection.covDerivAlongInChart_smul (nabla : AffineConnection I M)
    (c : ℝ → M) (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (c t))
    (alpha : M) {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t) :
    nabla.covDerivAlongInChart c (fun s => f s • V s) alpha t =
      deriv f t • chartFieldRep (I := I) c alpha V t +
        f t • nabla.covDerivAlongInChart c V alpha t := by
  rw [AffineConnection.covDerivAlongInChart, AffineConnection.covDerivAlongInChart,
    chartFieldRep_smul, deriv_smul hf hV, Pi.smul_apply',
    nabla.chartContractionAt_smul_right]
  module

@[simp] theorem AffineConnection.covDerivAlongInChart_zero
    (nabla : AffineConnection I M) (c : ℝ → M) (alpha : M) (t : ℝ) :
    nabla.covDerivAlongInChart c (fun _ => 0) alpha t = 0 := by
  have hrep : chartFieldRep (I := I) c alpha (fun _ => 0) = 0 := by
    funext s
    exact map_zero (tangentCoordChange I (c s) alpha (c s))
  rw [AffineConnection.covDerivAlongInChart, hrep]
  simp only [deriv_zero, Pi.zero_apply, AffineConnection.chartContractionAt,
    ← Geodesic.chartCoordFunctional_apply, map_zero, mul_zero, zero_smul,
    Finset.sum_const_zero, add_zero]

private theorem chartCoord_sum_smul_finBasis
    (f : Fin (Module.finrank ℝ E) → ℝ) (j : Fin (Module.finrank ℝ E)) :
    Geodesic.chartCoord (E := E) j (∑ k, f k • Module.finBasis ℝ E k) = f j := by
  classical
  rw [← Geodesic.chartCoordFunctional_apply, map_sum]
  have hb : ∀ k, Geodesic.chartCoordFunctional (E := E) j (Module.finBasis ℝ E k)
      = (if k = j then (1 : ℝ) else 0) := by
    intro k
    rw [Geodesic.chartCoordFunctional_apply, Geodesic.chartCoord_def,
      Module.Basis.repr_self, Finsupp.single_apply]
  simp only [map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero]
  simp

private theorem tangentCoordChange_injective {alpha p : M}
    (hself : p ∈ (extChartAt I p).source)
    (halpha : p ∈ (extChartAt I alpha).source) :
    Function.Injective (tangentCoordChange I p alpha p) := by
  intro v w hvw
  have hz : tangentCoordChange I p alpha p (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hzero := (tangentCoordChange_eq_zero_iff (I := I) hself halpha (v - w)).mp hz
  exact sub_eq_zero.mp hzero

private theorem AffineConnection.covDerivAlongInChart_comp_smoothVectorField
    (nabla : AffineConnection I M) {c : ℝ → M} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) (alpha : M)
    (hsrc : c t ∈ (chartAt H alpha).source)
    (X W : SmoothVectorField I M) (hX : X (c t) = DCVelocity (I := I) c t) :
    nabla.covDerivAlongInChart c (fun s => W (c s)) alpha t =
      tangentCoordChange I (c t) alpha (c t) ((nabla.cov X W) (c t)) := by
  classical
  let p : M := c t
  let Z : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun a => chartFrameFieldAt (I := I) alpha p a
  let e := trivializationAt E (TangentSpace I) alpha
  have hpB : p ∈ e.baseSet := hsrc
  have hBopen : IsOpen e.baseSet := e.open_baseSet
  set f : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun a => chartVectorFieldCoeff (I := I) alpha W a with hf
  have hf_smooth : ∀ a, ContMDiffOn I 𝓘(ℝ) ∞ (f a) e.baseSet :=
    fun a => chartVectorFieldCoeff_contMDiffOn (I := I) alpha W a
  choose gamma hgamma_smooth hgamma_ev using fun a =>
    exists_contMDiff_eventuallyEq (I := I) hBopen (hf_smooth a) hpB
  have hZev : ∀ a, ⇑(Z a) =ᶠ[nhds p]
      fun q => Tensor.chartBasisVecFiber (I := I) alpha a q := fun a =>
    chartFrameFieldAt_eventuallyEq (I := I) alpha hsrc a

  have hW'smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, ∑ a, gamma a q • Z a q⟩ : TangentBundle I M)) :=
    ContMDiff.sum_section fun a _ =>
      ContMDiff.smul_section (hgamma_smooth a) (Z a).smooth
  set W' : SmoothVectorField I M :=
    ⟨fun q => ∑ a, gamma a q • Z a q, hW'smooth⟩ with hW'def
  have hW'def_apply : ∀ q, W' q = ∑ a, gamma a q • Z a q := fun q => rfl
  have hW'_ev : ⇑W =ᶠ[nhds p] ⇑W' := by
    filter_upwards [eventually_all.mpr fun a => hgamma_ev a,
      eventually_all.mpr hZev, hBopen.eventually_mem hpB]
      with q hgammaq hZq hqB
    rw [vectorField_eq_sum_chartCoeff (I := I) alpha W hqB, hW'def_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgammaq a, hZq a]

  have htrans : ∀ q ∈ (chartAt H alpha).source, ∀ a,
      tangentCoordChange I q alpha q (Tensor.chartBasisVecFiber (I := I) alpha a q)
        = (Module.finBasis ℝ E a : E) := by
    intro q hq a
    have hv := (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) alpha) hq
        (Tensor.chartBasisVecFiber (I := I) alpha a q)).trans
      (trivializationAt_chartBasisVec_snd (I := I) alpha a hq)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hq] at hv
    simpa using! hv
  have hZcoord : ∀ a, tangentCoordChange I p alpha p (Z a p) =
      (Module.finBasis ℝ E a : E) := fun a => by
    rw [(hZev a).self_of_nhds]
    exact htrans p hsrc a
  let L : TangentSpace I p →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) alpha).continuousLinearMapAt ℝ p
  have hL : L = tangentCoordChange I p alpha p := by
    dsimp [L]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hsrc]
  have hZcoord' : ∀ a, L (Z a p) = (Module.finBasis ℝ E a : E) := fun a => by
    rw [hL]
    exact hZcoord a

  have hu_deriv : deriv (fun s => extChartAt I alpha (c s)) t =
      tangentCoordChange I p alpha p (DCVelocity (I := I) c t) := by
    have hsrc' : c t ∈ (extChartAt I alpha).source := by rwa [extChartAt_source]
    have hd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC
      (hasMFDerivAt_smulRight_DCVelocity (I := I) hc) hsrc'
    change deriv (↑(extChartAt I alpha) ∘ c) t = _
    exact hd.deriv

  have hFrep_ev : chartFieldRep (I := I) c alpha (fun tau => W (c tau))
      =ᶠ[nhds t] fun tau => ∑ a, gamma a (c tau) • (Module.finBasis ℝ E a : E) := by
    have hcont : ContinuousAt c t := hc.continuousAt
    have hev : ∀ᶠ tau in nhds t,
        (∀ a, gamma a (c tau) = f a (c tau)) ∧ c tau ∈ e.baseSet ∧
          c tau ∈ (chartAt H alpha).source := by
      have h1 : ∀ᶠ tau in nhds t, ∀ a, gamma a (c tau) = f a (c tau) :=
        hcont.eventually (eventually_all.mpr fun a => hgamma_ev a)
      have h2 : ∀ᶠ tau in nhds t, c tau ∈ e.baseSet :=
        hcont.eventually_mem (hBopen.mem_nhds hpB)
      have h3 : ∀ᶠ tau in nhds t, c tau ∈ (chartAt H alpha).source :=
        hcont.eventually_mem ((chartAt H alpha).open_source.mem_nhds hsrc)
      filter_upwards [h1, h2, h3] with tau h1' h2' h3' using ⟨h1', h2', h3'⟩
    filter_upwards [hev] with tau htau
    obtain ⟨hgammatau, htauB, htausrc⟩ := htau
    show tangentCoordChange I (c tau) alpha (c tau) (W (c tau))
        = ∑ a, gamma a (c tau) • (Module.finBasis ℝ E a : E)
    rw [vectorField_eq_sum_chartCoeff (I := I) alpha W htauB, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, htrans (c tau) htausrc a, hgammatau a]

  have hderiv_lhs : deriv (chartFieldRep (I := I) c alpha (fun tau => W (c tau))) t
      = ∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E) := by
    have hHDcomp : ∀ a, HasDerivAt (fun tau => gamma a (c tau)) (X.dir (gamma a) p) t := by
      intro a
      have h := hasDerivAt_comp_curve_DC (I := I)
        ((hgamma_smooth a).mdifferentiableAt (by simp)) hc
      simpa only [SmoothVectorField.dir,
        show X p = DCVelocity (I := I) c t from hX] using h
    have hHD : HasDerivAt (fun tau => ∑ a, gamma a (c tau) •
        (Module.finBasis ℝ E a : E))
        (∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E)) t :=
      HasDerivAt.fun_sum (fun a _ =>
        (hHDcomp a).smul_const (Module.finBasis ℝ E a : E))
    exact (hHD.congr_of_eventuallyEq hFrep_ev).deriv

  have hWcoord : chartFieldRep (I := I) c alpha (fun tau => W (c tau)) t =
      ∑ a, gamma a p • (Module.finBasis ℝ E a : E) := by
    exact hFrep_ev.self_of_nhds
  have hgammap : ∀ a, gamma a p = Geodesic.chartCoord (E := E) a
      (chartFieldRep (I := I) c alpha (fun tau => W (c tau)) t) := fun a => by
    rw [hWcoord, chartCoord_sum_smul_finBasis]

  have hself : p ∈ (extChartAt I p).source := mem_extChartAt_source (I := I) p
  have halpha : p ∈ (extChartAt I alpha).source := by rwa [extChartAt_source]
  have hXdecomp : X p = ∑ i, Geodesic.chartCoord (E := E) i
      (deriv (fun s => extChartAt I alpha (c s)) t) • Z i p := by
    apply tangentCoordChange_injective (I := I) hself halpha
    rw [map_sum]
    simp_rw [map_smul, hZcoord]
    calc
      tangentCoordChange I p alpha p (X p) =
          deriv (fun s => extChartAt I alpha (c s)) t := by rw [hX, hu_deriv]
      _ = ∑ i, Geodesic.chartCoord (E := E) i
          (deriv (fun s => extChartAt I alpha (c s)) t) •
            (Module.finBasis ℝ E i : E) := by
        simpa only [Geodesic.chartCoord_def] using
          ((Module.finBasis ℝ E).sum_repr
            (deriv (fun s => extChartAt I alpha (c s)) t)).symm

  have hcovZ : ∀ a, (nabla.cov X (Z a)) p =
      ∑ i, Geodesic.chartCoord (E := E) i
        (deriv (fun s => extChartAt I alpha (c s)) t) •
          (nabla.cov (Z i) (Z a)) p := by
    intro a
    rw [nabla.cov_smulSum_apply_left (Z a) p Finset.univ
      (fun i _ => Geodesic.chartCoord (E := E) i
        (deriv (fun s => extChartAt I alpha (c s)) t))
      (fun _ => contMDiff_const) Z X (by simpa using hXdecomp)]

  have hR : (nabla.cov X W) p =
      (∑ a, X.dir (gamma a) p • Z a p) +
        ∑ a, gamma a p • (nabla.cov X (Z a)) p := by
    rw [nabla.cov_congr_apply_eventuallyEq_right X hW'_ev,
      nabla.cov_smulSum_apply X p Finset.univ gamma hgamma_smooth Z W' hW'def_apply,
      Finset.sum_add_distrib]

  have hmain : nabla.covDerivAlongInChart c (fun s => W (c s)) alpha t =
      L ((nabla.cov X W) p) := by
    rw [AffineConnection.covDerivAlongInChart, hderiv_lhs, hR, map_add, map_sum]
    simp_rw [map_smul, hZcoord']
    congr 1
    rw [nabla.chartContractionAt_eq_of_frame alpha hsrc Z hZev]
    change (∑ i, ∑ j,
      (Geodesic.chartCoord (E := E) i
          (deriv (fun s => extChartAt I alpha (c s)) t) *
        Geodesic.chartCoord (E := E) j
          (chartFieldRep (I := I) c alpha (fun s => W (c s)) t)) •
        tangentCoordChange I p alpha p ((nabla.cov (Z i) (Z j)) p)) =
      L (∑ a, gamma a p • (nabla.cov X (Z a)) p)
    rw [← hL]
    rw [map_sum]
    simp_rw [map_smul]
    simp_rw [hcovZ]
    simp_rw [map_sum]
    simp_rw [map_smul]
    simp_rw [hgammap, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    congr 1
    ring
  calc
    nabla.covDerivAlongInChart c (fun s => W (c s)) alpha t =
        L ((nabla.cov X W) p) := hmain
    _ = tangentCoordChange I p alpha p ((nabla.cov X W) p) :=
      congrArg (fun A : TangentSpace I p →L[ℝ] E => A ((nabla.cov X W) p)) hL

/-- **Math.** Differentiability of an along-field's coordinate reading transfers between
two charts containing the foot, assuming the curve has a differentiable reading
in the source chart. -/
theorem differentiableAt_chartFieldRep_change {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (beta alpha : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrcBeta : c t ∈ (chartAt H beta).source)
    (hsrcAlpha : c t ∈ (chartAt H alpha).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I beta (c s)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c beta V) t) :
    DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t := by
  set p : M := c t
  set uBeta : ℝ → E := fun s => extChartAt I beta (c s)
  set VBeta : ℝ → E := chartFieldRep (I := I) c beta V
  set transition : E → E := chartTransition (I := I) beta alpha
  set y : E := extChartAt I beta p
  have hpBeta : p ∈ (extChartAt I beta).source := by rwa [extChartAt_source]
  have hpAlpha : p ∈ (extChartAt I alpha).source := by rwa [extChartAt_source]
  have hev : ∀ᶠ s in nhds t,
      c s ∈ (extChartAt I beta).source ∩ (extChartAt I alpha).source :=
    hc.eventually_mem (((isOpen_extChartAt_source (I := I) beta).inter
      (isOpen_extChartAt_source (I := I) alpha)).mem_nhds ⟨hpBeta, hpAlpha⟩)
  have hdom : y ∈ chartTransitionSource (I := I) (M := M) beta alpha :=
    extChartAt_mem_chartTransitionSource (I := I) hsrcBeta hsrcAlpha
  have htransitionTwo : ContDiffAt ℝ 2 transition y :=
    (contDiffAt_chartTransition hdom).of_le (by decide)
  have htransitionDeriv : DifferentiableAt ℝ (fderiv ℝ transition) y :=
    (htransitionTwo.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have huBeta : HasDerivAt uBeta (deriv uBeta t) t := hu.hasDerivAt
  have hlinear : HasDerivAt (fun s => fderiv ℝ transition (uBeta s))
      (fderiv ℝ (fderiv ℝ transition) y (deriv uBeta t)) t :=
    htransitionDeriv.hasFDerivAt.comp_hasDerivAt t huBeta
  have hreading : chartFieldRep (I := I) c alpha V =ᶠ[nhds t]
      fun s => fderiv ℝ transition (uBeta s) (VBeta s) := by
    filter_upwards [hev] with s hs
    have hsBeta : c s ∈ (chartAt H beta).source := by
      simpa only [extChartAt_source] using hs.1
    have hsAlpha : c s ∈ (chartAt H alpha).source := by
      simpa only [extChartAt_source] using hs.2
    have hsdom : uBeta s ∈ chartTransitionSource (I := I) (M := M) beta alpha :=
      extChartAt_mem_chartTransitionSource (I := I) hsBeta hsAlpha
    have hderiv : fderiv ℝ transition (uBeta s) =
        tangentCoordChange I beta alpha (c s) := by
      rw [show transition = chartTransition (I := I) beta alpha from rfl,
        fderiv_chartTransition (I := I) hsdom, (extChartAt I beta).left_inv hs.1]
    rw [hderiv]
    exact (tangentCoordChange_comp
      ⟨⟨mem_extChartAt_source (I := I) (c s), hs.1⟩, hs.2⟩).symm
  exact ((hlinear.clm_apply hV.hasDerivAt).congr_of_eventuallyEq hreading).differentiableAt

/-- **Math.** The connection term in the chart centered at `p`. -/
def AffineConnection.chartContraction (nabla : AffineConnection I M) (p : M)
    (v w : E) : E :=
  ∑ i, ∑ j, (Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w) •
    (nabla.cov (chartFrameField (I := I) p i) (chartFrameField (I := I) p j)) p

theorem AffineConnection.chartContraction_add_right
    (nabla : AffineConnection I M) (p : M) (v w z : E) :
    nabla.chartContraction p v (w + z) =
      nabla.chartContraction p v w + nabla.chartContraction p v z := by
  simp only [AffineConnection.chartContraction,
    ← Geodesic.chartCoordFunctional_apply, map_add, mul_add, add_smul,
    Finset.sum_add_distrib]

theorem AffineConnection.chartContraction_smul_right
    (nabla : AffineConnection I M) (p : M) (v w : E) (a : ℝ) :
    nabla.chartContraction p v (a • w) = a • nabla.chartContraction p v w := by
  simp only [AffineConnection.chartContraction,
    ← Geodesic.chartCoordFunctional_apply, map_smul, smul_eq_mul,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

@[simp] theorem AffineConnection.chartContraction_zero_right
    (nabla : AffineConnection I M) (p : M) (v : E) :
    nabla.chartContraction p v 0 = 0 := by
  simp only [AffineConnection.chartContraction,
    ← Geodesic.chartCoordFunctional_apply, map_zero, mul_zero, zero_smul,
    Finset.sum_const_zero]

theorem AffineConnection.chartContraction_sub_right
    (nabla : AffineConnection I M) (p : M) (v w z : E) :
    nabla.chartContraction p v (w - z) =
      nabla.chartContraction p v w - nabla.chartContraction p v z := by
  simp only [AffineConnection.chartContraction,
    ← Geodesic.chartCoordFunctional_apply, map_sub, mul_sub, sub_smul,
    Finset.sum_sub_distrib]

/-- **Math.** The covariant derivative along a curve induced by an arbitrary affine connection. -/
def AffineConnection.covDerivAlong (nabla : AffineConnection I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) : TangentSpace I (c t) :=
  deriv (chartFieldRep (I := I) c (c t) V) t +
    nabla.chartContraction (c t)
      (deriv (fun s => extChartAt I (c t) (c s)) t) (V t)

theorem chartFieldRep_sub (c : ℝ → M) (alpha : M)
    (V W : ∀ t, TangentSpace I (c t)) :
    chartFieldRep (I := I) c alpha (fun s => V s - W s) =
      chartFieldRep (I := I) c alpha V - chartFieldRep (I := I) c alpha W := by
  funext t
  exact map_sub (tangentCoordChange I (c t) alpha (c t)) (V t) (W t)

@[simp] theorem AffineConnection.covDerivAlong_zero
    (nabla : AffineConnection I M) (c : ℝ → M) (t : ℝ) :
    nabla.covDerivAlong c (fun _ => 0) t = 0 := by
  have hrep : chartFieldRep (I := I) c (c t) (fun _ => 0) = 0 := by
    funext s
    exact map_zero (tangentCoordChange I (c s) (c t) (c s))
  rw [AffineConnection.covDerivAlong, hrep]
  simp only [deriv_zero, Pi.zero_apply, nabla.chartContraction_zero_right, add_zero]

theorem AffineConnection.covDerivAlong_add (nabla : AffineConnection I M)
    (c : ℝ → M) (V W : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t) :
    nabla.covDerivAlong c (fun s => V s + W s) t =
      nabla.covDerivAlong c V t + nabla.covDerivAlong c W t := by
  rw [AffineConnection.covDerivAlong, AffineConnection.covDerivAlong,
    AffineConnection.covDerivAlong, chartFieldRep_add, deriv_add hV hW,
    nabla.chartContraction_add_right]
  abel

theorem AffineConnection.covDerivAlong_smul (nabla : AffineConnection I M)
    (c : ℝ → M) (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    nabla.covDerivAlong c (fun s => f s • V s) t =
      deriv f t • V t + f t • nabla.covDerivAlong c V t := by
  rw [AffineConnection.covDerivAlong, AffineConnection.covDerivAlong,
    chartFieldRep_smul, deriv_smul hf hV, chartFieldRep_self,
    nabla.chartContraction_smul_right]
  module

theorem AffineConnection.covDerivAlong_sub (nabla : AffineConnection I M)
    (c : ℝ → M) (V W : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t) :
    nabla.covDerivAlong c (fun s => V s - W s) t =
      nabla.covDerivAlong c V t - nabla.covDerivAlong c W t := by
  rw [AffineConnection.covDerivAlong, AffineConnection.covDerivAlong,
    AffineConnection.covDerivAlong, chartFieldRep_sub, deriv_sub hV hW,
    nabla.chartContraction_sub_right]
  abel

/-- **Math.** The connection is irrelevant at a time where the along-field vanishes. -/
theorem AffineConnection.covDerivAlong_eq_of_field_eq_zero
    (nabla nabla' : AffineConnection I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) {t : ℝ} (hV : V t = 0) :
    nabla.covDerivAlong c V t = nabla'.covDerivAlong c V t := by
  rw [AffineConnection.covDerivAlong, AffineConnection.covDerivAlong, hV,
    nabla.chartContraction_zero_right, nabla'.chartContraction_zero_right]

/-- **Math.** Property (c): a restricted global field differentiates by the ambient connection. -/
theorem AffineConnection.covDerivAlong_comp_smoothVectorField
    (nabla : AffineConnection I M) {c : ℝ → M} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (X W : SmoothVectorField I M) (hX : X (c t) = DCVelocity (I := I) c t) :
    nabla.covDerivAlong c (fun s => W (c s)) t = (nabla.cov X W) (c t) := by
  classical
  let p : M := c t
  let Z : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun a => chartFrameField (I := I) p a
  set f : Fin (Module.finrank ℝ E) → M → ℝ :=
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
      tangentCoordChange I q p q (Tensor.chartBasisVecFiber (I := I) p a q)
        = (Module.finBasis ℝ E a : E) := by
    intro q hq a
    have hv := (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) p) hq
        (Tensor.chartBasisVecFiber (I := I) p a q)).trans
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
      filter_upwards [h1, h2, h3] with tau htau1 htau2 htau3 using
        ⟨htau1, htau2, htau3⟩
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
    have hHD : HasDerivAt (fun tau => ∑ a, gamma a (c tau) •
        (Module.finBasis ℝ E a : E))
        (∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E)) t :=
      HasDerivAt.fun_sum (fun a _ =>
        (hHDcomp a).smul_const (Module.finBasis ℝ E a : E))
    exact (hHD.congr_of_eventuallyEq hFrep_ev).deriv

  have hXdecomp : X p = ∑ i, Geodesic.chartCoord (E := E) i
      (DCVelocity (I := I) c t) • Z i p := by
    calc
      X p = DCVelocity (I := I) c t := hX
      _ = ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
          • (Module.finBasis ℝ E i : E) := by
            simpa only [Geodesic.chartCoord_def] using
              ((Module.finBasis ℝ E).sum_repr (DCVelocity (I := I) c t)).symm
      _ = ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t)
          • Z i p := Finset.sum_congr rfl fun i _ => by rw [hZp i]

  have hcovZ : ∀ a, (nabla.cov X (Z a)) p =
      ∑ i, Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t) •
        (nabla.cov (Z i) (Z a)) p := by
    intro a
    rw [nabla.cov_smulSum_apply_left (Z a) p Finset.univ
      (fun i _ => Geodesic.chartCoord (E := E) i (DCVelocity (I := I) c t))
      (fun _ => contMDiff_const) Z X (by simpa using hXdecomp)]

  have hR : (nabla.cov X W) p =
      (∑ a, X.dir (gamma a) p • (Module.finBasis ℝ E a : E)) +
        nabla.chartContraction p (DCVelocity (I := I) c t) (W p) := by
    rw [nabla.cov_congr_apply_eventuallyEq_right X hW'_ev,
      nabla.cov_smulSum_apply X p Finset.univ gamma hgamma_smooth Z W' hW'def_apply,
      AffineConnection.chartContraction, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun a _ => by rw [hZp a]
    · simp_rw [hgammap, hcovZ, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
      congr 1
      ring

  change nabla.covDerivAlong c (fun tau => W (c tau)) t = (nabla.cov X W) p
  rw [AffineConnection.covDerivAlong, hderiv_lhs, hu_deriv, hR]

/-- **Math.** A restricted smooth field has a differentiable chart reading along any
manifold-differentiable curve; no `ContMDiffAt` hypothesis is needed. -/
theorem differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
    {c : ℝ → M} {t : ℝ} (X : SmoothVectorField I M)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
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
  have hsndAt : MDifferentiableAt I 𝓘(ℝ, E) (fun q => (e ⟨q, X q⟩).2) (c t) :=
    (hsnd.contMDiffAt (e.open_baseSet.mem_nhds hpbase)).mdifferentiableAt (by simp)
  have hcomp : DifferentiableAt ℝ (fun s => (e ⟨c s, X (c s)⟩).2) t :=
    (hsndAt.comp t hc).differentiableAt
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
      have hchange := tangentCoordChange_comp (I := I)
        (w := c s) (x := c t) (y := c s) (z := c s) (v := X (c s))
        ⟨⟨hself, hfixed⟩, hself⟩
      rw [tangentCoordChange_self hself] at hchange
      exact hchange.symm
    change a = (e ⟨c s, X (c s)⟩).2
    rw [hread]
    exact (congrArg Prod.snd (e.apply_mk_symm hsbase a)).symm
  exact hcomp.congr_of_eventuallyEq hrep

/-- **Eng.** Internal abbreviation for a dependent tangent field along a curve. -/
private abbrev AffineAlongField (c : ℝ → M) := (s : ℝ) → TangentSpace I (c s)

private theorem alongCandidate_congr_of_eventuallyEq
    {c : ℝ → M} {t : ℝ} (D : AffineAlongField (I := I) c → TangentSpace I (c t))
    (hsmul : ∀ (f : ℝ → ℝ) (V : AffineAlongField (I := I) c),
      DifferentiableAt ℝ f t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      D (fun s => f s • V s) = deriv f t • V t + f t • D V)
    {V W : AffineAlongField (I := I) c}
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t)
    (hVW : V =ᶠ[nhds t] W) : D V = D W := by
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
  have h := congrArg D hscaled
  rw [hsmul (fun s => chi s) V hchi_diff hV,
    hsmul (fun s => chi s) W hchi_diff hW, hchi_t, hchi_deriv] at h
  simpa using h

theorem AffineConnection.covDerivAlong_congr (nabla : AffineConnection I M)
    {c : ℝ → M} {V W : AffineAlongField (I := I) c} {t : ℝ}
    (h : V =ᶠ[nhds t] W) :
    nabla.covDerivAlong c V t = nabla.covDerivAlong c W t := by
  have hrep : chartFieldRep (I := I) c (c t) V =ᶠ[nhds t]
      chartFieldRep (I := I) c (c t) W := by
    filter_upwards [h] with s hs
    simp only [chartFieldRep_apply, hs]
  rw [AffineConnection.covDerivAlong, AffineConnection.covDerivAlong,
    hrep.deriv_eq, h.self_of_nhds]

/-- **Math.** Pointwise uniqueness under exactly the continuity and chart-reading hypotheses used. -/
private theorem AffineConnection.covDerivAlong_unique_of_global
    (nabla : AffineConnection I M) {c : ℝ → M} {t : ℝ}
    (hc : ContinuousAt c t)
    (D : AffineAlongField (I := I) c → TangentSpace I (c t))
    (hadd : ∀ (V W : AffineAlongField (I := I) c),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t →
      D (fun s => V s + W s) = D V + D W)
    (hsmul : ∀ (f : ℝ → ℝ) (V : AffineAlongField (I := I) c),
      DifferentiableAt ℝ f t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      D (fun s => f s • V s) = deriv f t • V t + f t • D V)
    (hglobal : ∀ X : SmoothVectorField I M,
      D (fun s => X (c s)) = nabla.covDerivAlong c (fun s => X (c s)) t)
    (hrestr : ∀ X : SmoothVectorField I M,
      DifferentiableAt ℝ
        (chartFieldRep (I := I) c (c t) (fun s => X (c s))) t)
    (V : AffineAlongField (I := I) c)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    D V = nabla.covDerivAlong c V t := by
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
  let a : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun i s =>
    Geodesic.chartCoord (E := E) i (chartFieldRep (I := I) c (c t) V s)
  let R : Fin (Module.finrank ℝ E) → AffineAlongField (I := I) c := fun i s => X i (c s)
  let F : Fin (Module.finrank ℝ E) → AffineAlongField (I := I) c :=
    fun i s => a i s • R i s
  let S : AffineAlongField (I := I) c := fun s => ∑ i, F i s
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
  let sumF : Finset (Fin (Module.finrank ℝ E)) → AffineAlongField (I := I) c :=
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
  have hD0 : D (fun _ => 0) = 0 := by
    have h := hsmul (fun _ => 0) V (differentiableAt_const (c := (0 : ℝ))) hV
    simpa using h
  have hDsum : ∀ u, D (sumF u) = ∑ i ∈ u, D (F i) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa [sumF] using hD0
    | @insert i u hi ih =>
        have hsplit : sumF (insert i u) = fun s => F i s + sumF u s := by
          funext s
          simp [sumF, hi]
        rw [hsplit, hadd (F i) (sumF u) (hF i) (hsum_diff u), ih,
          Finset.sum_insert hi]
  have hC0 : nabla.covDerivAlong c (fun _ => 0) t = 0 := by
    have h := nabla.covDerivAlong_smul c (fun _ => 0) V
      (differentiableAt_const (c := (0 : ℝ))) hV
    convert h using 1 <;> simp
  have hCsum : ∀ u, nabla.covDerivAlong c (sumF u) t =
      ∑ i ∈ u, nabla.covDerivAlong c (F i) t := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp [sumF, hC0]
    | @insert i u hi ih =>
        have hsplit : sumF (insert i u) = fun s => F i s + sumF u s := by
          funext s
          simp [sumF, hi]
        rw [hsplit, nabla.covDerivAlong_add c (F i) (sumF u)
          (hF i) (hsum_diff u), ih, Finset.sum_insert hi]
  have hterm : ∀ i, D (F i) = nabla.covDerivAlong c (F i) t := by
    intro i
    rw [show F i = fun s => a i s • R i s from rfl,
      hsmul (a i) (R i) (ha i) (hR i),
      nabla.covDerivAlong_smul c (a i) (R i) (ha i) (hR i)]
    rw [show R i = fun s => X i (c s) from rfl, hglobal (X i)]
  have hDS : D S = nabla.covDerivAlong c S t := by
    have hSuniv : S = sumF Finset.univ := by
      funext s
      simp [S, sumF]
    rw [hSuniv, hDsum Finset.univ, hCsum Finset.univ]
    exact Finset.sum_congr rfl fun i _ => hterm i
  calc
    D V = D S := alongCandidate_congr_of_eventuallyEq (I := I) D hsmul hV
      (by
        have hrepVS : chartFieldRep (I := I) c (c t) V =ᶠ[nhds t]
            chartFieldRep (I := I) c (c t) S := by
          filter_upwards [hVS] with s hs
          simp only [chartFieldRep_apply, hs]
        exact hV.congr_of_eventuallyEq hrepVS.symm) hVS
    _ = nabla.covDerivAlong c S t := hDS
    _ = nabla.covDerivAlong c V t := (nabla.covDerivAlong_congr hVS).symm

/-- **Math.** Pointwise uniqueness for the affine covariant derivative along a curve.

The hypotheses state only the local regularity used at `t`: continuity of the
curve, differentiability of its reading in one chart, and differentiability of
the along-fields in that same chart.  The compatibility axiom is the intrinsic
property (c), expressed directly using `nabla.cov`. -/
theorem AffineConnection.covDerivAlong_unique
    (nabla : AffineConnection I M) {c : ℝ → M} {t : ℝ} (alpha : M)
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H alpha).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I alpha (c s)) t)
    (D : ((s : ℝ) → TangentSpace I (c s)) → TangentSpace I (c t))
    (hadd : ∀ (V W : (s : ℝ) → TangentSpace I (c s)),
      DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c alpha W) t →
      D (fun s => V s + W s) = D V + D W)
    (hsmul : ∀ (f : ℝ → ℝ) (V : (s : ℝ) → TangentSpace I (c s)),
      DifferentiableAt ℝ f t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t →
      D (fun s => f s • V s) = deriv f t • V t + f t • D V)
    (hcomp : ∀ (X W : SmoothVectorField I M),
      X (c t) = DCVelocity (I := I) c t →
      D (fun s => W (c s)) = (nabla.cov X W) (c t))
    (V : (s : ℝ) → TangentSpace I (c s))
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t) :
    D V = nabla.covDerivAlong c V t := by
  have hcM : MDifferentiableAt 𝓘(ℝ, ℝ) I c t := by
    apply (mdifferentiableAt_iff_target_of_mem_source hsrc).2
    refine ⟨hc, ?_⟩
    exact hu.mdifferentiableAt
  have hsrcMoving : c t ∈ (chartAt H (c t)).source := mem_chart_source H (c t)
  have huMoving : DifferentiableAt ℝ
      (fun s => extChartAt I (c t) (c s)) t :=
    (hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC
      (hasMFDerivAt_smulRight_DCVelocity (I := I) hcM)
      (mem_extChartAt_source (I := I) (c t))).differentiableAt
  have hVMoving : DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) V) t :=
    differentiableAt_chartFieldRep_change (I := I) alpha (c t) hc hsrc
      hsrcMoving hu hV
  obtain ⟨X, hX⟩ :=
    exists_smoothVectorField_eq (I := I) (c t) (DCVelocity (I := I) c t)
  refine nabla.covDerivAlong_unique_of_global hc D ?_ ?_ ?_ ?_ V hVMoving
  · intro W Z hW hZ
    exact hadd W Z
      (differentiableAt_chartFieldRep_change (I := I) (c t) alpha hc
        hsrcMoving hsrc huMoving hW)
      (differentiableAt_chartFieldRep_change (I := I) (c t) alpha hc
        hsrcMoving hsrc huMoving hZ)
  · intro f W hf hW
    exact hsmul f W hf
      (differentiableAt_chartFieldRep_change (I := I) (c t) alpha hc
        hsrcMoving hsrc huMoving hW)
  · intro W
    calc
      D (fun s => W (c s)) = (nabla.cov X W) (c t) := hcomp X W hX
      _ = nabla.covDerivAlong c (fun s => W (c s)) t :=
        (nabla.covDerivAlong_comp_smoothVectorField hcM X W hX).symm
  · intro W
    exact differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
      (I := I) W hcM

/-- **Math.** Pointwise uniqueness specialized to a `C¹` curve and the canonical chart
at the foot. -/
theorem AffineConnection.covDerivAlong_unique_of_contMDiffAt
    (nabla : AffineConnection I M) {c : ℝ → M} {t : ℝ}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 1 c t)
    (D : ((s : ℝ) → TangentSpace I (c s)) → TangentSpace I (c t))
    (hadd : ∀ (V W : (s : ℝ) → TangentSpace I (c s)),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t →
      D (fun s => V s + W s) = D V + D W)
    (hsmul : ∀ (f : ℝ → ℝ) (V : (s : ℝ) → TangentSpace I (c s)),
      DifferentiableAt ℝ f t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      D (fun s => f s • V s) = deriv f t • V t + f t • D V)
    (hcomp : ∀ (X W : SmoothVectorField I M),
      X (c t) = DCVelocity (I := I) c t →
      D (fun s => W (c s)) = (nabla.cov X W) (c t))
    (V : (s : ℝ) → TangentSpace I (c s))
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    D V = nabla.covDerivAlong c V t := by
  have hcM : MDifferentiableAt 𝓘(ℝ, ℝ) I c t :=
    hc.mdifferentiableAt (by norm_num)
  have hu : DifferentiableAt ℝ (fun s => extChartAt I (c t) (c s)) t :=
    (hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC
      (hasMFDerivAt_smulRight_DCVelocity (I := I) hcM)
      (mem_extChartAt_source (I := I) (c t))).differentiableAt
  exact nabla.covDerivAlong_unique (c t) hc.continuousAt
    (mem_chart_source H (c t)) hu D hadd hsmul hcomp V hV

/-- **Math.** Global uniqueness along a `C¹` curve. -/
theorem AffineConnection.covDerivAlong_unique_global
    (nabla : AffineConnection I M) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    (D : ((s : ℝ) → TangentSpace I (c s)) →
      ((s : ℝ) → TangentSpace I (c s)))
    (hadd : ∀ (t : ℝ) (V W : (s : ℝ) → TangentSpace I (c s)),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t →
      D (fun s => V s + W s) t = D V t + D W t)
    (hsmul : ∀ (t : ℝ) (f : ℝ → ℝ)
      (V : (s : ℝ) → TangentSpace I (c s)),
      DifferentiableAt ℝ f t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      D (fun s => f s • V s) t = deriv f t • V t + f t • D V t)
    (hcomp : ∀ (t : ℝ) (X W : SmoothVectorField I M),
      X (c t) = DCVelocity (I := I) c t →
      D (fun s => W (c s)) t = (nabla.cov X W) (c t))
    (V : (s : ℝ) → TangentSpace I (c s))
    (hV : ∀ t, DifferentiableAt ℝ
      (chartFieldRep (I := I) c (c t) V) t) :
    D V = fun t => nabla.covDerivAlong c V t := by
  funext t
  exact nabla.covDerivAlong_unique_of_contMDiffAt hc.contMDiffAt
    (fun W => D W t) (hadd t) (hsmul t) (hcomp t) V (hV t)

/-- **Math.** Chart independence of the affine covariant derivative along a curve.  The
right side is the direct connection-frame formula in any chart containing the
foot; no auxiliary frame choices appear in the statement. -/
theorem AffineConnection.covDerivAlong_eq_chart
    (nabla : AffineConnection I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (alpha : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H alpha).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I alpha (c s)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t) :
    nabla.covDerivAlong c V t =
      tangentCoordChange I alpha (c t) (c t)
        (nabla.covDerivAlongInChart c V alpha t) := by
  let D : ((s : ℝ) → TangentSpace I (c s)) → TangentSpace I (c t) :=
    fun W => tangentCoordChange I alpha (c t) (c t)
      (nabla.covDerivAlongInChart c W alpha t)
  have halpha : c t ∈ (extChartAt I alpha).source := by rwa [extChartAt_source]
  have hself : c t ∈ (extChartAt I (c t)).source :=
    mem_extChartAt_source (I := I) (c t)
  have hread : ∀ W : (s : ℝ) → TangentSpace I (c s),
      tangentCoordChange I alpha (c t) (c t)
        (chartFieldRep (I := I) c alpha W t) = W t := by
    intro W
    rw [chartFieldRep_apply,
      tangentCoordChange_comp (I := I) (w := c t) (x := alpha) (y := c t)
        (z := c t) ⟨⟨hself, halpha⟩, hself⟩,
      tangentCoordChange_self hself]
  have hcM : MDifferentiableAt 𝓘(ℝ, ℝ) I c t := by
    apply (mdifferentiableAt_iff_target_of_mem_source hsrc).2
    refine ⟨hc, ?_⟩
    exact hu.mdifferentiableAt
  have hunique : D V = nabla.covDerivAlong c V t := by
    refine nabla.covDerivAlong_unique alpha hc hsrc hu D ?_ ?_ ?_ V hV
    · intro W Z hW hZ
      simp only [D]
      change tangentCoordChange I alpha (c t) (c t)
          (nabla.covDerivAlongInChart c (fun s => W s + Z s) alpha t) = _
      rw [nabla.covDerivAlongInChart_add c W Z alpha hW hZ, map_add]
    · intro f W hf hW
      simp only [D]
      change tangentCoordChange I alpha (c t) (c t)
          (nabla.covDerivAlongInChart c (fun s => f s • W s) alpha t) = _
      rw [nabla.covDerivAlongInChart_smul c f W alpha hf hW, map_add,
        map_smul, map_smul, hread W]
    · intro X W hX
      change tangentCoordChange I alpha (c t) (c t)
          (nabla.covDerivAlongInChart c (fun s => W (c s)) alpha t) = _
      rw [nabla.covDerivAlongInChart_comp_smoothVectorField hcM alpha hsrc X W hX,
        tangentCoordChange_comp (I := I) (w := c t) (x := alpha) (y := c t)
          (z := c t) ⟨⟨hself, halpha⟩, hself⟩,
        tangentCoordChange_self hself]
  exact hunique.symm

/-- **Math.** The direct connection coefficients of the Levi-Civita connection are the metric Christoffels. -/
theorem RiemannianMetric.leviCivita_chartContraction_eq
    (g : RiemannianMetric I M) (p : M) (v w : E) :
    g.leviCivitaConnection.chartContraction p v w =
      Geodesic.chartChristoffelContraction (I := I) g p v w (extChartAt I p p) := by
  classical
  rw [AffineConnection.chartContraction, Geodesic.chartChristoffelContraction_def]
  simp_rw [leviCivita_cov_chartFrameField_expansion (I := I) g p _ _
      (mem_chart_source H p) (fun m => chartFrameField_eventuallyEq (I := I) p m),
    Tensor.chartBasisVecFiber_self, Finset.smul_sum, smul_smul]
  have hswap :
      (∑ i, ∑ j, ∑ m,
        (Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w *
          chartChristoffel (I := I) g p i j m (extChartAt I p p)) •
            (Module.finBasis ℝ E m : E)) =
        ∑ m, ∑ i, ∑ j,
          (Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w *
            chartChristoffel (I := I) g p i j m (extChartAt I p p)) •
              (Module.finBasis ℝ E m : E) := by
    calc
      _ = ∑ i, ∑ m, ∑ j,
          (Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w *
            chartChristoffel (I := I) g p i j m (extChartAt I p p)) •
              (Module.finBasis ℝ E m : E) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

/-- **Math.** The arbitrary-connection construction specializes exactly to the existing
Levi-Civita operator, without additional regularity assumptions. -/
theorem RiemannianMetric.leviCivita_covDerivAlong_eq
    (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    g.leviCivitaConnection.covDerivAlong c V t =
      Riemannian.covDerivAlong (I := I) g c V t := by
  rw [AffineConnection.covDerivAlong, Riemannian.covDerivAlong_def,
    covariantDerivCoord_def, chartFieldRep_self,
    g.leviCivita_chartContraction_eq]

end Riemannian

end
