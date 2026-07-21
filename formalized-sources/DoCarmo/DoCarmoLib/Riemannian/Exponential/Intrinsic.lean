import DoCarmoLib.Riemannian.Exponential.Defs
import DoCarmoLib.Riemannian.Geodesic.Completeness
import Shared.Topology.FiberBundleT2

/-!
# The intrinsic exponential map and its maximal domain

The legacy `Exponential.expMap` is built from a single chart-fixed spray and is
therefore only a local chart exponential.  This file constructs the genuine
intrinsic maximal geodesic by gluing continuous moving-chart geodesics.  It is
defined without a completeness assumption; completeness is exactly the
statement that its exponential domain is all of the tangent space.
-/

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A continuous intrinsic geodesic on `s` with initial position `p` and
chart-`p` velocity `v` at time zero. -/
def IsIntrinsicGeodesicOnWithInitial (g : RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) (p : M) (v : TangentSpace I p) : Prop :=
  γ 0 = p ∧ HasDerivAt (chartReading (I := I) p γ) (v : E) 0 ∧
    IsGeodesicCurveOn (I := I) g γ s

/-- **Math.** A time belongs to the intrinsic maximal interval when one continuous
moving-chart geodesic with the prescribed initial data is defined on a
preconnected open set containing zero and that time. -/
def IntrinsicGeodesicWitness (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsIntrinsicGeodesicOnWithInitial (I := I) g γ J p v

/-- **Math.** The chart-independent maximal interval of the geodesic with initial data
`(p,v)`. -/
def intrinsicGeodesicInterval (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : Set ℝ :=
  {t | IntrinsicGeodesicWitness (I := I) g p v t}

@[simp] theorem mem_intrinsicGeodesicInterval_iff
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p} {t : ℝ} :
    t ∈ intrinsicGeodesicInterval (I := I) g p v ↔
      IntrinsicGeodesicWitness (I := I) g p v t :=
  Iff.rfl

theorem intrinsicGeodesicInterval_isOpen (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : IsOpen (intrinsicGeodesicInterval (I := I) g p v) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨γ, J, hJ, hJconn, h0, htJ, hγ⟩ := ht
  refine mem_of_superset (hJ.mem_nhds htJ) ?_
  intro u hu
  exact ⟨γ, J, hJ, hJconn, h0, hu, hγ⟩

theorem zero_mem_intrinsicGeodesicInterval (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    (0 : ℝ) ∈ intrinsicGeodesicInterval (I := I) g p v := by
  obtain ⟨b, hb, γ, h0, hv, hc, hgeo⟩ := exists_seed_geodesic (I := I) g p v
  have hzero : (0 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, hb⟩
  exact ⟨γ, Ioo (-b) b, isOpen_Ioo, isPreconnected_Ioo, hzero, hzero,
    h0, hv, hc, hgeo⟩

/-- **Math.** Two intrinsic witnesses with the same initial data agree wherever their
parameter domains overlap. -/
theorem eqOn_inter_of_isIntrinsicGeodesicOnWithInitial
    (g : RiemannianMetric I M) {p : M} {v : TangentSpace I p}
    {γ₁ γ₂ : ℝ → M} {J₁ J₂ : Set ℝ}
    (hJ₁ : IsOpen J₁) (hcJ₁ : IsPreconnected J₁) (h0J₁ : (0 : ℝ) ∈ J₁)
    (hJ₂ : IsOpen J₂) (hcJ₂ : IsPreconnected J₂) (h0J₂ : (0 : ℝ) ∈ J₂)
    (hγ₁ : IsIntrinsicGeodesicOnWithInitial (I := I) g γ₁ J₁ p v)
    (hγ₂ : IsIntrinsicGeodesicOnWithInitial (I := I) g γ₂ J₂ p v) :
    Set.EqOn γ₁ γ₂ (J₁ ∩ J₂) := by
  have hconn : IsPreconnected (J₁ ∩ J₂) :=
    (hcJ₁.ordConnected.inter hcJ₂.ordConnected).isPreconnected
  refine IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (t₀ := 0) (β := p)
    (hJ₁.inter hJ₂) hconn
    (hγ₁.2.2.2.mono inter_subset_left) (hγ₂.2.2.2.mono inter_subset_right)
    (hγ₁.2.2.1.mono inter_subset_left) (hγ₂.2.2.1.mono inter_subset_right)
    ⟨h0J₁, h0J₂⟩ ?_ ?_ ?_
  · rw [hγ₁.1, hγ₂.1]
  · rw [hγ₁.1]
    exact mem_chart_source H p
  · rw [hγ₁.2.1.deriv, hγ₂.2.1.deriv]

/-- **Math.** The witness curve selected at a time in the intrinsic interval. -/
def intrinsicGeodesicChosenCurve (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) {t : ℝ}
    (h : IntrinsicGeodesicWitness (I := I) g p v t) : ℝ → M :=
  Classical.choose h

theorem intrinsicGeodesicChosenCurve_spec (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) {t : ℝ}
    (h : IntrinsicGeodesicWitness (I := I) g p v t) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsIntrinsicGeodesicOnWithInitial (I := I) g
        (intrinsicGeodesicChosenCurve (I := I) g p v h) J p v :=
  Classical.choose_spec h

/-- **Math.** The canonical intrinsic maximal geodesic, junk-extended by `p` outside its
maximal interval. -/
def intrinsicMaximalGeodesic (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (t : ℝ) : M :=
  letI : Decidable (IntrinsicGeodesicWitness (I := I) g p v t) := Classical.dec _
  if h : IntrinsicGeodesicWitness (I := I) g p v t then
    intrinsicGeodesicChosenCurve (I := I) g p v h t
  else p

theorem intrinsicMaximalGeodesic_eq_of_witness
    (g : RiemannianMetric I M) {p : M} {v : TangentSpace I p}
    {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hcJ : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hγ : IsIntrinsicGeodesicOnWithInitial (I := I) g γ J p v) :
    ∀ t ∈ J, intrinsicMaximalGeodesic (I := I) g p v t = γ t := by
  intro t htJ
  have ht : IntrinsicGeodesicWitness (I := I) g p v t :=
    ⟨γ, J, hJ, hcJ, h0J, htJ, hγ⟩
  rw [intrinsicMaximalGeodesic, dif_pos ht]
  obtain ⟨J', hJ', hcJ', h0J', htJ', hchosen⟩ :=
    intrinsicGeodesicChosenCurve_spec (I := I) g p v ht
  exact eqOn_inter_of_isIntrinsicGeodesicOnWithInitial (I := I) g
    hJ' hcJ' h0J' hJ hcJ h0J hchosen hγ ⟨htJ', htJ⟩

theorem intrinsicMaximalGeodesic_eventuallyEq_of_witness
    (g : RiemannianMetric I M) {p : M} {v : TangentSpace I p}
    {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hcJ : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hγ : IsIntrinsicGeodesicOnWithInitial (I := I) g γ J p v)
    {t : ℝ} (ht : t ∈ J) :
    intrinsicMaximalGeodesic (I := I) g p v =ᶠ[𝓝 t] γ := by
  filter_upwards [hJ.mem_nhds ht] with u hu
  exact intrinsicMaximalGeodesic_eq_of_witness (I := I) g hJ hcJ h0J hγ u hu

@[simp] theorem intrinsicMaximalGeodesic_zero (g : RiemannianMetric I M)
    (p : M) (v : TangentSpace I p) :
    intrinsicMaximalGeodesic (I := I) g p v 0 = p := by
  obtain ⟨b, hb, γ, h0, hv, hc, hgeo⟩ := exists_seed_geodesic (I := I) g p v
  have hz : (0 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, hb⟩
  rw [intrinsicMaximalGeodesic_eq_of_witness (I := I) g isOpen_Ioo
    isPreconnected_Ioo hz ⟨h0, hv, hc, hgeo⟩ 0 hz, h0]

theorem hasDerivAt_chartReading_intrinsicMaximalGeodesic
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    HasDerivAt (chartReading (I := I) p
      (intrinsicMaximalGeodesic (I := I) g p v)) (v : E) 0 := by
  obtain ⟨b, hb, γ, h0, hv, hc, hgeo⟩ := exists_seed_geodesic (I := I) g p v
  have hz : (0 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, hb⟩
  have heq := intrinsicMaximalGeodesic_eventuallyEq_of_witness (I := I) g
    isOpen_Ioo isPreconnected_Ioo hz ⟨h0, hv, hc, hgeo⟩ hz
  exact hv.congr_of_eventuallyEq (heq.fun_comp (extChartAt I p))

theorem continuousOn_intrinsicMaximalGeodesic (g : RiemannianMetric I M)
    (p : M) (v : TangentSpace I p) :
    ContinuousOn (intrinsicMaximalGeodesic (I := I) g p v)
      (intrinsicGeodesicInterval (I := I) g p v) := by
  intro t ht
  obtain ⟨γ, J, hJ, hcJ, h0J, htJ, hγ⟩ := ht
  have heq := intrinsicMaximalGeodesic_eventuallyEq_of_witness (I := I) g
    hJ hcJ h0J hγ htJ
  exact ((hγ.2.2.1 t htJ).continuousAt (hJ.mem_nhds htJ)).congr heq.symm
    |>.continuousWithinAt

theorem isGeodesicOn_intrinsicMaximalGeodesic (g : RiemannianMetric I M)
    (p : M) (v : TangentSpace I p) :
    IsGeodesicOn (I := I) g (intrinsicMaximalGeodesic (I := I) g p v)
      (intrinsicGeodesicInterval (I := I) g p v) := by
  intro t ht
  obtain ⟨γ, J, hJ, hcJ, h0J, htJ, hγ⟩ := ht
  exact hasGeodesicEquationAt_congr_of_eventuallyEq
    (intrinsicMaximalGeodesic_eventuallyEq_of_witness (I := I) g
      hJ hcJ h0J hγ htJ)
    (hγ.2.2.2 t htJ)

theorem intrinsicGeodesicInterval_isPreconnected (g : RiemannianMetric I M)
    (p : M) (v : TangentSpace I p) :
    IsPreconnected (intrinsicGeodesicInterval (I := I) g p v) := by
  apply isPreconnected_of_forall (0 : ℝ)
  intro t ht
  obtain ⟨γ, J, hJ, hcJ, h0J, htJ, hγ⟩ := ht
  refine ⟨J, ?_, h0J, htJ, hcJ⟩
  intro u hu
  exact ⟨γ, J, hJ, hcJ, h0J, hu, hγ⟩

/-- **Math.** Radial rescaling of the intrinsic domain.  If the time-one
geodesic with initial velocity `t • v` exists, then the geodesic with initial
velocity `v` exists at time `t`. -/
theorem mem_intrinsicGeodesicInterval_of_one_mem_smul
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) (t : ℝ)
    (h : (1 : ℝ) ∈ intrinsicGeodesicInterval (I := I) g p (t • v)) :
    t ∈ intrinsicGeodesicInterval (I := I) g p v := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact zero_mem_intrinsicGeodesicInterval (I := I) g p v
  obtain ⟨δ, J, hJ, hcJ, h0J, h1J, hδ⟩ := h
  let A : ℝ → ℝ := fun s ↦ t⁻¹ * s
  let J' : Set ℝ := A ⁻¹' J
  let γ : ℝ → M := fun s ↦ δ (A s)
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hJ' : IsOpen J' := hJ.preimage hAcont
  have hcJ' : IsPreconnected J' := by
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · have hanti : Antitone A := by
        intro a b hab
        dsimp [A]
        exact mul_le_mul_of_nonpos_left hab (le_of_lt ((inv_lt_zero').2 htneg))
      exact (hcJ.ordConnected.preimage_anti hanti).isPreconnected
    · have hmono : Monotone A := by
        intro a b hab
        dsimp [A]
        exact mul_le_mul_of_nonneg_left hab (le_of_lt (inv_pos.mpr htpos))
      exact (hcJ.ordConnected.preimage_mono hmono).isPreconnected
  have h0J' : (0 : ℝ) ∈ J' := by
    simpa [J', A] using h0J
  have htJ' : t ∈ J' := by
    simpa [J', A, ht]
  refine ⟨γ, J', hJ', hcJ', h0J', htJ', ?_, ?_, ?_, ?_⟩
  · simpa [γ, A] using hδ.1
  · have hA : HasDerivAt A t⁻¹ 0 := by
      simpa [A] using (hasDerivAt_id (0 : ℝ)).const_mul t⁻¹
    have hδv : HasDerivAt (chartReading (I := I) p δ) ((t • v : TangentSpace I p) : E)
        (A 0) := by
      simpa [A] using hδ.2.1
    have hcomp := hδv.scomp 0 hA
    have hfun : chartReading (I := I) p γ = chartReading (I := I) p δ ∘ A := by
      rfl
    rw [hfun]
    convert hcomp using 1
    change (v : E) = t⁻¹ • (t • (v : E))
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  · exact hδ.2.2.1.comp hAcont.continuousOn (fun _ hu ↦ hu)
  · exact isGeodesicOn_comp_mul_left (I := I) hδ.2.2.2

/-- **Math.** If the intrinsic maximal interval is all of `ℝ`, its canonical
curve is a continuous global geodesic with the prescribed initial data. -/
theorem intrinsicMaximalGeodesic_spec_of_interval_eq_univ
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hdom : intrinsicGeodesicInterval (I := I) g p v = Set.univ) :
    intrinsicMaximalGeodesic (I := I) g p v 0 = p ∧
      HasDerivAt (chartReading (I := I) p
        (intrinsicMaximalGeodesic (I := I) g p v)) (v : E) 0 ∧
      IsGeodesicCurve (I := I) g (intrinsicMaximalGeodesic (I := I) g p v) := by
  refine ⟨intrinsicMaximalGeodesic_zero (I := I) g p v,
    hasDerivAt_chartReading_intrinsicMaximalGeodesic (I := I) g p v, ?_, ?_⟩
  · have hc := continuousOn_intrinsicMaximalGeodesic (I := I) g p v
    rw [hdom] at hc
    simpa only [continuousOn_univ] using hc
  · intro t
    exact isGeodesicOn_intrinsicMaximalGeodesic (I := I) g p v t
      (by rw [hdom]; exact mem_univ t)

end Geodesic

namespace Exponential

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The genuine intrinsic exponential map, defined at `v` when the
intrinsic geodesic with initial data `(p,v)` reaches time one.  Outside its
natural domain it has the conventional junk value `p`; mathematical statements
must carry membership in `expDomainIntrinsic`. -/
def expMapIntrinsic (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : M :=
  intrinsicMaximalGeodesic (I := I) g p v 1

/-- **Math.** The natural domain of the intrinsic exponential map at `p`. -/
def expDomainIntrinsic (g : RiemannianMetric I M) (p : M) :
    Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ intrinsicGeodesicInterval (I := I) g p v}

@[simp] theorem mem_expDomainIntrinsic_iff
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p} :
    v ∈ expDomainIntrinsic (I := I) g p ↔
      (1 : ℝ) ∈ intrinsicGeodesicInterval (I := I) g p v :=
  Iff.rfl

theorem expMapIntrinsic_eq_of_witness (g : RiemannianMetric I M)
    {p : M} {v : TangentSpace I p} {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hcJ : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (h1J : (1 : ℝ) ∈ J)
    (hγ : IsIntrinsicGeodesicOnWithInitial (I := I) g γ J p v) :
    expMapIntrinsic (I := I) g p v = γ 1 :=
  intrinsicMaximalGeodesic_eq_of_witness (I := I) g hJ hcJ h0J hγ 1 h1J

/-- **Math.** The zero tangent vector belongs to the intrinsic exponential
domain at every base point. -/
theorem zero_mem_expDomainIntrinsic (g : RiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ expDomainIntrinsic (I := I) g p := by
  refine ⟨fun _ : ℝ ↦ p, Set.univ, isOpen_univ, isPreconnected_univ,
    mem_univ 0, mem_univ 1, rfl, ?_, continuous_const.continuousOn,
    (isGeodesic_const (I := I) g p).isGeodesicOn Set.univ⟩
  simpa [chartReading] using
    (hasDerivAt_const (x := (0 : ℝ)) (c := extChartAt I p p))

/-- **Math.** The intrinsic exponential map sends the zero tangent vector to
its base point. -/
@[simp] theorem expMapIntrinsic_zero (g : RiemannianMetric I M) (p : M) :
    expMapIntrinsic (I := I) g p (0 : TangentSpace I p) = p := by
  refine expMapIntrinsic_eq_of_witness (I := I) g (p := p)
    (v := (0 : TangentSpace I p)) (γ := fun _ : ℝ ↦ p) (J := Set.univ)
    isOpen_univ isPreconnected_univ (mem_univ 0) (mem_univ 1) ?_
  refine ⟨rfl, ?_, continuous_const.continuousOn,
    (isGeodesic_const (I := I) g p).isGeodesicOn Set.univ⟩
  simpa [chartReading] using
    (hasDerivAt_const (x := (0 : ℝ)) (c := extChartAt I p p))

/-- **Math.** **Intrinsic radial endpoint identity.** If the intrinsic geodesic with
initial data `(p,v)` is defined at time `t`, then the geodesic with initial data
`(p,t • v)` is defined at time `1`, and its exponential endpoint is the original
geodesic's value at `t`.  The statement is completeness-free and retains the
continuity hypothesis through the intrinsic witness.

This is the chart-independent form of do Carmo's homogeneity lemma (Ch. 3,
Lemma 2.6), used in the blueprint to read `exp_p(t v)` as the radial geodesic.
-/
theorem expMapIntrinsic_smul_eq_intrinsicMaximalGeodesic_of_mem
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) {t : ℝ}
    (ht : t ∈ intrinsicGeodesicInterval (I := I) g p v) :
    t • v ∈ expDomainIntrinsic (I := I) g p ∧
      expMapIntrinsic (I := I) g p (t • v) =
        intrinsicMaximalGeodesic (I := I) g p v t := by
  classical
  rcases eq_or_ne t 0 with rfl | ht0
  · constructor
    · rw [zero_smul]
      exact zero_mem_expDomainIntrinsic (I := I) g p
    · rw [zero_smul, expMapIntrinsic_zero, intrinsicMaximalGeodesic_zero]
  · obtain ⟨γ, J, hJ, hcJ, h0J, htJ, hγ⟩ := ht
    let A : ℝ → ℝ := fun s ↦ t * s
    let J' : Set ℝ := A ⁻¹' J
    let δ : ℝ → M := fun s ↦ γ (A s)
    have hAcont : Continuous A := by
      dsimp [A]
      fun_prop
    have hJ' : IsOpen J' := hJ.preimage hAcont
    have hcJ' : IsPreconnected J' := by
      rcases lt_or_gt_of_ne ht0 with htneg | htpos
      · have hanti : Antitone A := by
          intro a b hab
          dsimp [A]
          exact mul_le_mul_of_nonpos_left hab (le_of_lt htneg)
        exact (hcJ.ordConnected.preimage_anti hanti).isPreconnected
      · have hmono : Monotone A := by
          intro a b hab
          dsimp [A]
          exact mul_le_mul_of_nonneg_left hab (le_of_lt htpos)
        exact (hcJ.ordConnected.preimage_mono hmono).isPreconnected
    have h0J' : (0 : ℝ) ∈ J' := by
      simpa [J', A] using h0J
    have h1J' : (1 : ℝ) ∈ J' := by
      simpa [J', A] using htJ
    have hδ : IsIntrinsicGeodesicOnWithInitial (I := I) g δ J' p (t • v) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [δ, A] using hγ.1
      · have hA : HasDerivAt A t 0 := by
          simpa [A] using (hasDerivAt_id (0 : ℝ)).const_mul t
        have hγv : HasDerivAt (chartReading (I := I) p γ) (v : E)
            (A 0) := by
          simpa [A] using hγ.2.1
        have hcomp := hγv.scomp 0 hA
        have hfun : chartReading (I := I) p δ = chartReading (I := I) p γ ∘ A := by
          rfl
        rw [hfun]
        exact hcomp
      · refine ⟨?_, ?_⟩
        · exact hγ.2.2.1.comp hAcont.continuousOn (fun _ hu ↦ hu)
        · have hgeo := isGeodesicOn_comp_mul_left (I := I) hγ.2.2.2 (a := t)
          simpa [δ, A, J'] using hgeo

    have htime : (1 : ℝ) ∈ intrinsicGeodesicInterval (I := I) g p (t • v) :=
      ⟨δ, J', hJ', hcJ', h0J', h1J', hδ⟩
    have hleft := intrinsicMaximalGeodesic_eq_of_witness (I := I) g
      hJ' hcJ' h0J' hδ 1 h1J'
    have hright := intrinsicMaximalGeodesic_eq_of_witness (I := I) g
      hJ hcJ h0J hγ t htJ
    constructor
    · exact htime
    · change intrinsicMaximalGeodesic (I := I) g p (t • v) 1 =
        intrinsicMaximalGeodesic (I := I) g p v t
      calc
        intrinsicMaximalGeodesic (I := I) g p (t • v) 1 = δ 1 := hleft
        _ = γ t := by simp [δ, A]
        _ = intrinsicMaximalGeodesic (I := I) g p v t := hright.symm

/-- **Math.** On a chart-confined interval, the legacy chart-flow
exponential and the intrinsic exponential have the same endpoint. The
hypotheses state explicitly that the common chart-flow witness is continuous
and satisfies the moving-chart geodesic equation; these are not consequences
of the junk-extended chart equation alone. -/
theorem expMap_eq_expMapIntrinsic_of_chart_witness
    (g : RiemannianMetric I M) {p : M} {v : TangentSpace I p}
    {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hcJ : IsPreconnected J)
    (h0J : (0 : ℝ) ∈ J) (h1J : (1 : ℝ) ∈ J)
    (hchart : IsGeodesicOnWithInitial (I := I) g γ J p v)
    (hsrc : ∀ t ∈ J, γ t ∈ (chartAt H p).source)
    (hcurve : IsGeodesicCurveOn (I := I) g γ J) :
    expMap (I := I) g p v = expMapIntrinsic (I := I) g p v := by
  change maximalGeodesic (I := I) g p v 1 =
    intrinsicMaximalGeodesic (I := I) g p v 1
  calc
    maximalGeodesic (I := I) g p v 1 = γ 1 :=
      maximalGeodesic_eq_witness_of_mem_chart (I := I) hchart hJ hcJ h0J hsrc h1J
    _ = intrinsicMaximalGeodesic (I := I) g p v 1 :=
      (intrinsicMaximalGeodesic_eq_of_witness (I := I) g hJ hcJ h0J
        ⟨hchart.start_eq, hchart.hasDerivAt_extChartAt_zero (hJ.mem_nhds h0J),
          hcurve⟩ 1 h1J).symm

end Exponential

namespace Geodesic

open Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** `(M,g)` is geodesically complete at `p` when every initial
velocity at `p` generates a continuous intrinsic geodesic on all of `ℝ`. -/
def IsGeodesicallyCompleteAt (g : RiemannianMetric I M) (p : M) : Prop :=
  ∀ v : TangentSpace I p, ∃ γ : ℝ → M,
    γ 0 = p ∧ HasDerivAt (chartReading (I := I) p γ) (v : E) 0 ∧
      IsGeodesicCurve (I := I) g γ

/-- **Math.** A Riemannian manifold is geodesically complete when it is
geodesically complete at every base point. -/
def IsGeodesicallyComplete (g : RiemannianMetric I M) : Prop :=
  ∀ p : M, IsGeodesicallyCompleteAt g p

/-- **Math.** The exponential-map and global-geodesic formulations of
geodesic completeness at a point are equivalent. -/
theorem expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt
    (g : RiemannianMetric I M) (p : M) :
    expDomainIntrinsic (I := I) g p = Set.univ ↔ IsGeodesicallyCompleteAt g p := by
  constructor
  · intro htotal v
    have hinterval : intrinsicGeodesicInterval (I := I) g p v = Set.univ := by
      apply Set.eq_univ_of_forall
      intro t
      apply mem_intrinsicGeodesicInterval_of_one_mem_smul (I := I) g p v t
      have : (t • v) ∈ expDomainIntrinsic (I := I) g p := by
        rw [htotal]
        exact mem_univ _
      exact this
    obtain ⟨h0, hv, hc, hgeo⟩ :=
      intrinsicMaximalGeodesic_spec_of_interval_eq_univ (I := I) g p v hinterval
    exact ⟨intrinsicMaximalGeodesic (I := I) g p v, h0, hv, hc, hgeo⟩
  · intro hcomplete
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨γ, h0, hv, hc, hgeo⟩ := hcomplete v
    exact ⟨γ, Set.univ, isOpen_univ, isPreconnected_univ, mem_univ 0, mem_univ 1,
      h0, hv, hc.continuousOn, hgeo.isGeodesicOn Set.univ⟩

end Geodesic
end Riemannian

end
