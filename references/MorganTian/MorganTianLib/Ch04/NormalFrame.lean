import MorganTianLib.Ch01.FrameJacobiSystem
import MorganTianLib.Ch02.FrameBridge

/-!
# Morgan--Tian Ch. 4 -- a normal-frame first-jet producer

For a point of a Riemannian manifold and an orthonormal basis of its tangent
space, this module constructs smooth vector fields with the prescribed values
and vanishing Levi--Civita covariant derivative at that point.  This is the
local first-jet input used by the tensor maximum-principle argument.

The construction is Petersen, *Riemannian Geometry* (3rd ed.), §2.5,
Exercise 2.5.19: extend the basis vectors smoothly and correct their first
jets by a smooth matrix of scalar functions.  The result is intentionally only
a pointwise first-jet statement.  It does not assert a smooth parallel
trivialization on a neighbourhood and does not close the Ch. 4 maximum
principle by itself.

## Main declarations

* `leviCivitaCovariantDerivativeAt` -- covariant differentiation in a tangent direction;
* `IsNormalFrameAt` -- the pointwise normal-frame predicate;
* `exists_contMDiff_prescribed_value_jet` -- a global smooth scalar with a
  prescribed value and differential at one point;
* `exists_isNormalFrameAt_of_orthonormal` and `exists_isNormalFrameAt` -- the
  normal-frame existence results.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.19.
-/

open Bundle Set Function Finset Module Filter
open Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]

/-! ## Pointwise covariant differentiation -/

/-- **Math.** The Levi--Civita covariant derivative of a smooth vector field
`X` at `p` in a tangent direction `v`.  The direction is represented by the
canonical smooth extension `extendVector p v`; tensoriality in the direction
slot makes the resulting value independent of that choice. -/
noncomputable def leviCivitaCovariantDerivativeAt (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (X : SmoothVectorField I M) : TangentSpace I p :=
  (g.leviCivitaConnection.cov (extendVector p v) X) p

/-- **Math.** A frame is normal at `p` when it is `g`-orthonormal at `p` and its
Levi--Civita covariant derivative vanishes there in every tangent direction. -/
def IsNormalFrameAt (g : RiemannianMetric I M) (p : M)
    (F : Fin (Module.finrank ℝ E) → SmoothVectorField I M) : Prop :=
  (∀ i j, g.metricInner p (F i p) (F j p) = (if i = j then (1 : ℝ) else 0)) ∧
  (∀ i, ∀ v : TangentSpace I p, leviCivitaCovariantDerivativeAt g p v (F i) = 0)

private theorem leviCivitaCovariantDerivativeAt_add_direction (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) (X : SmoothVectorField I M) :
    leviCivitaCovariantDerivativeAt g p (v + w) X =
      leviCivitaCovariantDerivativeAt g p v X + leviCivitaCovariantDerivativeAt g p w X := by
  unfold leviCivitaCovariantDerivativeAt
  have h := g.leviCivitaConnection.cov_congr_apply_left
    (X := extendVector p (v + w))
    (X' := extendVector p v + extendVector p w) X (p := p)
    (by simp [extendVector_apply, SmoothVectorField.add_apply])
  rw [g.leviCivitaConnection.add_left] at h
  simpa [SmoothVectorField.add_apply] using h

private theorem leviCivitaCovariantDerivativeAt_smul_direction (g : RiemannianMetric I M) (p : M)
    (a : ℝ) (v : TangentSpace I p) (X : SmoothVectorField I M) :
    leviCivitaCovariantDerivativeAt g p (a • v) X =
      a • leviCivitaCovariantDerivativeAt g p v X := by
  unfold leviCivitaCovariantDerivativeAt
  let hconst : ContMDiff I 𝓘(ℝ) ∞ (fun _ : M => a) := contMDiff_const
  have h := g.leviCivitaConnection.cov_congr_apply_left
    (X := extendVector p (a • v))
    (X' := SmoothVectorField.smul (fun _ : M => a) hconst (extendVector p v))
    X (p := p)
    (by simp [extendVector_apply, SmoothVectorField.smul_apply])
  rw [g.leviCivitaConnection.smul_left] at h
  simpa [SmoothVectorField.smul_apply] using h

/-! ## The finite Leibniz expansion -/

private theorem cov_finsetSumSmul (D : AffineConnection I M)
    (X : SmoothVectorField I M) {ι : Type*} (s : Finset ι)
    (f : ι → M → ℝ) (V : ι → SmoothVectorField I M)
    (hf : ∀ m, ContMDiff I 𝓘(ℝ) ∞ (f m)) {p : M} :
    (D.cov X (∑ m ∈ s, SmoothVectorField.smul (f m) (hf m) (V m))) p =
      ∑ m ∈ s, (f m p • (D.cov X (V m)) p + X.dir (f m) p • V m p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using D.cov_zero_right X p
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, D.add_right]
      simp only [SmoothVectorField.add_apply]
      rw [D.leibniz (f a) (hf a) X (V a) p, ih, Finset.sum_insert ha]

/-! ## Prescribed scalar first jets -/

/-- **Math.** Given `p`, a covector `ξ` on `T_pM`, and a scalar `val`, there
is a globally smooth scalar `u` with `u p = val` and
`dirTangent u v = ξ v` for every `v : T_pM`.  Locally use
`ξ ∘ extChartAt I p` plus a constant; the existing scalar germ-extension
theorem globalizes it. -/
theorem exists_contMDiff_prescribed_value_jet (p : M)
    (ξ : E →L[ℝ] ℝ) (val : ℝ) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧ u p = val ∧
      ∀ v : TangentSpace I p, dirTangent u v = ξ v := by
  set b : ℝ := val - ξ (extChartAt I p p) with hb
  set u₀ : M → ℝ := fun y => ξ (extChartAt I p y) + b with hu₀
  have hu₀on : ContMDiffOn I 𝓘(ℝ) ∞ u₀ (extChartAt I p).source := by
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p) (extChartAt I p).source := by
      rw [extChartAt_source]
      exact contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)
    have hlin : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun w : E => ξ w + b) :=
      (ξ.contMDiff).add contMDiff_const
    exact hlin.comp_contMDiffOn hchart
  obtain ⟨u, hu_smooth, hu_ev⟩ :=
    exists_contMDiff_eventuallyEq (I := I) (isOpen_extChartAt_source (I := I) p)
      hu₀on (mem_extChartAt_source (I := I) p)
  refine ⟨u, hu_smooth, ?_, ?_⟩
  · rw [hu_ev.self_of_nhds]
    show ξ (extChartAt I p p) + b = val
    rw [hb]
    ring
  · intro v
    have hmfd : mfderiv I 𝓘(ℝ) u p = mfderiv I 𝓘(ℝ) u₀ p :=
      Filter.EventuallyEq.mfderiv_eq hu_ev
    show mfderiv I 𝓘(ℝ) u p v = ξ v
    rw [hmfd]
    have hφ : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) :=
      ((contMDiffAt_extChartAt (I := I) (x := p) (n := ∞)).mdifferentiableAt
        (by simp)).hasMFDerivAt
    have hk : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ) (fun w : E => ξ w + b)
        (extChartAt I p p) ξ :=
      (hasMFDerivAt_iff_hasFDerivAt).mpr (ξ.hasFDerivAt.add_const b)
    have hcomp : HasMFDerivAt I 𝓘(ℝ) u₀ p
        (ξ.comp (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p)) := hk.comp p hφ
    have hid : (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) v = v := by
      rw [mfderiv_extChartAt_self]
      rfl
    rw [hcomp.mfderiv]
    show ξ ((mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) v) = ξ v
    rw [hid]

/-! ## The correction covector -/

/-- **Math.** The covector `v ↦ g(∇_v X,w)` used for the first-jet correction. -/
def covMetricLinear (g : RiemannianMetric I M) (p : M)
    (X : SmoothVectorField I M) (w : TangentSpace I p) :
    TangentSpace I p →ₗ[ℝ] ℝ where
  toFun v := g.metricInner p (leviCivitaCovariantDerivativeAt g p v X) w
  map_add' v₁ v₂ := by
    rw [leviCivitaCovariantDerivativeAt_add_direction, g.metricInner_add_left]
  map_smul' a v := by
    rw [leviCivitaCovariantDerivativeAt_smul_direction, g.metricInner_smul_left,
      RingHom.id_apply]
    simp [smul_eq_mul]

@[simp] theorem covMetricLinear_apply (g : RiemannianMetric I M) (p : M)
    (X : SmoothVectorField I M) (w v : TangentSpace I p) :
    covMetricLinear (I := I) g p X w v =
      g.metricInner p (leviCivitaCovariantDerivativeAt g p v X) w := rfl

/-! ## Petersen's normal-frame construction -/

/-- **Math.** **Normal frame at a point (Petersen, Exercise 2.5.19).**  For a
`g`-orthonormal tuple `e` in `T_pM`, there are globally smooth vector fields
`F_i` with `F_i p = e_i` and `IsNormalFrameAt g p F`.  The correcting
coefficients have value `δᵢₘ` and first derivative
`-g(∇_v F_i,e_m)`, so the finite Leibniz rule cancels each derivative at `p`.
-/
theorem exists_isNormalFrameAt_of_orthonormal (g : RiemannianMetric I M) (p : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I p)
    (he : ∀ i j, g.metricInner p (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, F i p = e i) ∧ IsNormalFrameAt g p F := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  choose Z hZ using fun i => exists_smoothVectorField_eq (I := I) p (e i)
  set ξ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (TangentSpace I p →L[ℝ] ℝ) :=
    fun i m => -(covMetricLinear (I := I) g p (Z i) (e m)).toContinuousLinearMap with hξ
  have hjet : ∀ i m, ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      u p = (if i = m then (1 : ℝ) else 0) ∧
      ∀ v : TangentSpace I p, dirTangent u v = ξ i m v :=
    fun i m => exists_contMDiff_prescribed_value_jet (I := I) p (ξ i m) _
  choose c hc_smooth hc_val hc_dir using hjet
  let F : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    ∑ m ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      SmoothVectorField.smul (c i m) (hc_smooth i m) (Z m)
  refine ⟨F, ?_, ?_⟩
  · intro i
    dsimp [F]
    change (∑ m, SmoothVectorField.smul (c i m) (hc_smooth i m) (Z m)) p = e i
    rw [sumField_apply]
    rw [Finset.sum_congr rfl (fun m _ => by
      rw [SmoothVectorField.smul_apply, hc_val i m, hZ m, ite_smul, one_smul, zero_smul])]
    simp
  · constructor
    · intro i j
      have hFi : F i p = e i := by
        dsimp [F]
        change (∑ m, SmoothVectorField.smul (c i m) (hc_smooth i m) (Z m)) p = e i
        rw [sumField_apply]
        rw [Finset.sum_congr rfl (fun m _ => by
          rw [SmoothVectorField.smul_apply, hc_val i m, hZ m, ite_smul,
            one_smul, zero_smul])]
        simp
      have hFj : F j p = e j := by
        dsimp [F]
        change (∑ m, SmoothVectorField.smul (c j m) (hc_smooth j m) (Z m)) p = e j
        rw [sumField_apply]
        rw [Finset.sum_congr rfl (fun m _ => by
          rw [SmoothVectorField.smul_apply, hc_val j m, hZ m, ite_smul,
            one_smul, zero_smul])]
        simp
      calc
        g.metricInner p (F i p) (F j p) = g.metricInner p (e i) (e j) := by
          rw [hFi, hFj]
        _ = if i = j then (1 : ℝ) else 0 := he i j
    · intro i v
      dsimp [F]
      unfold leviCivitaCovariantDerivativeAt
      rw [cov_finsetSumSmul g.leviCivitaConnection (extendVector p v) Finset.univ
        (c i) Z (hc_smooth i)]
      have hdir : ∀ m, (extendVector p v).dir (c i m) p = dirTangent (c i m) v := by
        intro m
        simp [SmoothVectorField.dir, dirTangent, extendVector_apply]
      have hterm : ∀ m,
          c i m p • (g.leviCivitaConnection.cov (extendVector p v) (Z m)) p +
              (extendVector p v).dir (c i m) p • (Z m) p =
            (-(g.metricInner p (leviCivitaCovariantDerivativeAt g p v (Z i)) (e m))) • e m +
              (if i = m then (1 : ℝ) else 0) •
                (g.leviCivitaConnection.cov (extendVector p v) (Z m)) p := by
        intro m
        rw [hdir m, hc_dir i m v, hc_val i m, hZ m, hξ]
        simp [covMetricLinear]
        ac_rfl
      rw [Finset.sum_congr rfl (fun m _ => hterm m)]
      rw [Finset.sum_add_distrib]
      have hsnd : (∑ m, (if i = m then (1 : ℝ) else 0) •
          (g.leviCivitaConnection.cov (extendVector p v) (Z m)) p) =
          (g.leviCivitaConnection.cov (extendVector p v) (Z i)) p := by
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      have hfst : (∑ m, (-(g.metricInner p
          (leviCivitaCovariantDerivativeAt g p v (Z i)) (e m))) • e m) =
            -leviCivitaCovariantDerivativeAt g p v (Z i) := by
        have hexp := metricInner_orthonormal_expansion (I := I) g he
          (leviCivitaCovariantDerivativeAt g p v (Z i))
        simp only [neg_smul]
        rw [Finset.sum_neg_distrib, ← hexp]
      rw [hfst, hsnd]
      change (-(leviCivitaCovariantDerivativeAt g p v (Z i)) +
        leviCivitaCovariantDerivativeAt g p v (Z i)) = 0
      simp

/-! ## A direct pointwise consumer -/

/-- **Math.** Every point admits a smooth normal frame.  The seed tuple is the
standard orthonormal basis of `T_pM` for the fibre metric induced by `g`; the
construction is `exists_isNormalFrameAt_of_orthonormal`. -/
theorem exists_isNormalFrameAt (g : RiemannianMetric I M) (p : M) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      IsNormalFrameAt g p F := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let bas : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    stdOrthonormalBasis ℝ (TangentSpace I p)
  have hbas : ∀ i j, g.metricInner p (bas i) (bas j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    exact orthonormal_iff_ite.mp bas.orthonormal i j
  obtain ⟨F, hval, hnormal⟩ :=
    exists_isNormalFrameAt_of_orthonormal (I := I) g p
      (fun i => (bas i : TangentSpace I p)) hbas
  exact ⟨F, hnormal⟩

end MorganTianLib

end
