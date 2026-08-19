import DoCarmoLib.Riemannian.Manifold.EuclideanOpens
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import MorganTianLib.Ch01.CurvatureOperator
import MorganTianLib.Ch01.LeviCivita

/-!
# Morgan--Tian Ch. 1 -- the open Riemannian cone

For a Riemannian manifold `(N,g)`, the open cone is the product
`N × (0,∞)` equipped with `dr² + r² g`.  The construction below uses the
DoCarmo pullback-form API, so both the radial term and the tangential term are
bundled as continuous bilinear forms on the product tangent space.
-/

open Set Riemannian TopologicalSpace
open exteriorPower
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib

/-! ## The positive radial factor -/

/-- **Math.** The open positive half-line, regarded as an open subset of `ℝ`.
Its subtype is the radial manifold `(0,∞)`. -/
def positiveReal : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩

noncomputable instance positiveRealLocallyCompactSpace :
    LocallyCompactSpace ↥positiveReal :=
  positiveReal.2.locallyCompactSpace

@[simp] theorem positiveReal_mem (r : ↥positiveReal) : 0 < (r : ℝ) := r.property

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- **Math.** The radial coordinate on the open cone. -/
def coneRadius (q : N × ↥positiveReal) : ℝ := q.2

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
/-- **Math.** The cone radius is a smooth scalar function. -/
theorem coneRadius_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (coneRadius (N := N)) :=
  contMDiff_subtype_val_opens.comp contMDiff_snd

/-! ### The cone bilinear form -/

/-- **Math.** The cone form `r² g + dr²` on `N × (0,∞)`, written as the
sum of the pullback of `g` along the first projection, scaled by `r²`, and
the pullback of the Euclidean metric along the radial projection. -/
noncomputable def coneForm (g : RiemannianMetric I N) (p : N × ↥positiveReal) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ :=
  ((p.2 : ℝ) ^ 2) •
      DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) g (Prod.fst : N × ↥positiveReal → N) p +
    DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) (opensEuclideanMetric positiveReal)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) p

omit [FiniteDimensional ℝ E] in
/-- **Math.** Evaluation of the cone form on tangent vectors. -/
@[simp] theorem coneForm_apply (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    coneForm g p u v =
      (p.2 : ℝ) ^ 2 * g.metricInner p.1
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p v) +
      (opensEuclideanMetric positiveReal).metricInner p.2
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p v) := by
  simp only [coneForm, add_apply, smul_apply, smul_eq_mul, DCInducedForm_apply]

omit [FiniteDimensional ℝ E] in
theorem coneForm_symm (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) : coneForm g p u v = coneForm g p v u := by
  rw [coneForm_apply, coneForm_apply, g.metricInner_comm,
    (opensEuclideanMetric positiveReal).metricInner_comm]

omit [FiniteDimensional ℝ E] in
theorem coneForm_self_nonneg (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) : 0 ≤ coneForm g p u u := by
  rw [coneForm_apply]
  have h₁ : 0 ≤ (p.2 : ℝ) ^ 2 * g.metricInner p.1
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u) :=
    mul_nonneg (sq_nonneg _) (g.metricInner_self_nonneg _ _)
  have h₂ : 0 ≤ (opensEuclideanMetric positiveReal).metricInner p.2
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u) :=
    (opensEuclideanMetric positiveReal).metricInner_self_nonneg _ _
  linarith

omit [FiniteDimensional ℝ E] in
theorem coneForm_self_pos (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (hu : u ≠ 0) : 0 < coneForm g p u u := by
  have hfst : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) p u = u.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u = u.2 := by
    rw [mfderiv_snd]
    rfl
  rw [coneForm_apply, hfst, hsnd]
  have hrad : 0 < (p.2 : ℝ) ^ 2 := sq_pos_of_pos p.2.property
  have h₁ : 0 ≤ (p.2 : ℝ) ^ 2 * g.metricInner p.1 u.1 u.1 :=
    mul_nonneg (sq_nonneg _) (g.metricInner_self_nonneg _ _)
  have h₂ : 0 ≤ (opensEuclideanMetric positiveReal).metricInner p.2 u.2 u.2 :=
    (opensEuclideanMetric positiveReal).metricInner_self_nonneg _ _
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]
    exact fun h => hu (Prod.ext h.1 h.2)
  rcases hor with h₁u | h₂u
  · have hp : 0 < (p.2 : ℝ) ^ 2 * g.metricInner p.1 u.1 u.1 :=
      mul_pos hrad (g.metricInner_self_pos _ _ h₁u)
    linarith
  · have hp : 0 < (opensEuclideanMetric positiveReal).metricInner p.2 u.2 u.2 :=
      (opensEuclideanMetric positiveReal).metricInner_self_pos _ _ h₂u
    linarith

omit [FiniteDimensional ℝ E] in
theorem coneForm_contMDiff (g : RiemannianMetric I N) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p, coneForm g p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
  have hrad : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : N × ↥positiveReal ↦ ((p.2 : ℝ) ^ 2)) := by
    exact ((contMDiff_subtype_val_opens.comp contMDiff_snd).pow 2)
  have htan : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p,
        DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) g
          (Prod.fst : N × ↥positiveReal → N) p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
    exact DCInducedForm_contMDiff g contMDiff_fst
  have hradial : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p,
        DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) (opensEuclideanMetric positiveReal)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
    exact DCInducedForm_contMDiff (opensEuclideanMetric positiveReal) contMDiff_snd
  exact (hrad.smul_section htan).add_section hradial

/-! ### The bundled metric -/

/-- **Math.** The open cone metric over `g`, with pointwise inner product
`⟨(u,a),(v,b)⟩ = r²⟨u,v⟩_g + a b`. -/
noncomputable def coneMetric (g : RiemannianMetric I N) :
    RiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) where
  inner p := coneForm g p
  symm p u v := coneForm_symm g p u v
  pos p u hu := coneForm_self_pos g p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E × ℝ) (coneForm g p) (fun u hu => ?_)
    exact coneForm_self_pos g p u hu
  contMDiff := coneForm_contMDiff g

@[simp] theorem coneMetric_apply (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (coneMetric g).metricInner p u v = coneForm g p u v :=
  rfl

/-- **Math.** In the product tangent splitting, the cone metric is exactly
`r²⟨u,v⟩_g + a b`. -/
@[simp] theorem coneMetric_metricInner_mk (g : RiemannianMetric I N)
    (x : N) (r : ↥positiveReal) (u v : TangentSpace I x) (a b : ℝ) :
    (coneMetric g).metricInner (x, r) (u, a) (v, b) =
      (r : ℝ) ^ 2 * g.metricInner x u v + a * b := by
  rw [coneMetric_apply, coneForm_apply]
  have hfst_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) (u, a) = u := by
    rw [mfderiv_fst]
    rfl
  have hfst_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) (v, b) = v := by
    rw [mfderiv_fst]
    rfl
  have hsnd_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) (u, a) = a := by
    rw [mfderiv_snd]
    rfl
  have hsnd_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) (v, b) = b := by
    rw [mfderiv_snd]
    rfl
  rw [hfst_u, hfst_v, hsnd_u, hsnd_v, opensEuclideanMetric_apply]
  rw [show (inner ℝ a b : ℝ) = a * b from by simp [inner, mul_comm]]

/-- **Math.** The cone metric on arbitrary product tangent vectors is
`r² g(u_N,v_N) + u_r v_r`. -/
@[simp] theorem coneMetric_metricInner_prod (g : RiemannianMetric I N)
    (x : N) (r : ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :
    (coneMetric g).metricInner (x, r) u v =
      (r : ℝ) ^ 2 * g.metricInner x u.1 v.1 + u.2 * v.2 := by
  rw [coneMetric_apply, coneForm_apply]
  have hfst_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) u = u.1 := by
    rw [mfderiv_fst]
    rfl
  have hfst_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) v = v.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) u = u.2 := by
    rw [mfderiv_snd]
    rfl
  have hsnd_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) v = v.2 := by
    rw [mfderiv_snd]
    rfl
  rw [hfst_u, hfst_v, hsnd_u, hsnd_v, opensEuclideanMetric_apply]
  rw [show (inner ℝ u.2 v.2 : ℝ) = u.2 * v.2 from by simp [inner, mul_comm]]

/-! ### The canonical cone connection -/

section ConeConnection

variable [CompleteSpace E] [SigmaCompactSpace N] [T2Space N]

/-- **Math.** The Levi-Civita connection of the open cone metric. The generalized
Koszul construction is needed because the standard product model `E × ℝ` has
the max norm and therefore does not carry the product inner-product instance. -/
noncomputable def coneLeviCivitaConnection (g : RiemannianMetric I N) :
    AffineConnection (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) :=
  leviCivitaConnectionGeneral (coneMetric g)

/-- **Math.** The canonical cone connection is symmetric and compatible with
the cone metric. -/
theorem coneLeviCivitaConnection_isLeviCivita (g : RiemannianMetric I N) :
    (coneLeviCivitaConnection g).IsLeviCivita (coneMetric g) :=
  leviCivitaConnectionGeneral_isLeviCivita (coneMetric g)

end ConeConnection

/-! ### Horizontal and radial cone fields -/

/-- **Math.** The horizontal lift of a smooth vector field on the cone base. -/
noncomputable def coneHorizontalLift (X : SmoothVectorField I N) :
    SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) where
  toFun := fun q => (X q.1, 0)
  smooth := by
    have hX : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : N × ↥positiveReal => (⟨q.1, X q.1⟩ : TangentBundle I N)) :=
      X.smooth.comp contMDiff_fst
    have hzero : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : N × ↥positiveReal =>
          (⟨q.2, (0 : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ :
            TangentBundle 𝓘(ℝ, ℝ) ↥positiveReal)) :=
      (SmoothVectorField.zero (I := 𝓘(ℝ, ℝ)) (M := ↥positiveReal)).smooth.comp
        contMDiff_snd
    exact contMDiff_equivTangentBundleProd_symm.comp (hX.prodMk hzero)

/-- **Math.** The unit radial coordinate field `∂r` on the open cone. -/
noncomputable def coneRadialField :
    SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) where
  toFun := fun _ => (0, (1 : ℝ))
  smooth := by
    have hzero : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : N × ↥positiveReal =>
          (⟨q.1, (0 : TangentSpace I q.1)⟩ : TangentBundle I N)) :=
      (SmoothVectorField.zero (I := I) (M := N)).smooth.comp contMDiff_fst
    let R : SmoothVectorField 𝓘(ℝ, ℝ) ↥positiveReal :=
      SmoothVectorField.ofOpens (fun _ => (1 : ℝ)) contMDiff_const
    have hR : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : N × ↥positiveReal =>
          (⟨q.2, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ↥positiveReal)) :=
      R.smooth.comp contMDiff_snd
    exact contMDiff_equivTangentBundleProd_symm.comp (hzero.prodMk hR)

omit [FiniteDimensional ℝ E] in
@[simp] theorem coneHorizontalLift_apply (X : SmoothVectorField I N)
    (q : N × ↥positiveReal) : coneHorizontalLift X q = (X q.1, 0) :=
  rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem coneRadialField_apply (q : N × ↥positiveReal) :
    coneRadialField (I := I) (N := N) q = (0, 1) :=
  rfl

/-- **Math.** Pairing any cone tangent vector with the unit radial field
extracts its radial component. -/
@[simp] theorem coneMetric_any_radial (g : RiemannianMetric I N)
    (x : N) (r : ↥positiveReal)
    (v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) :
    (coneMetric g).metricInner (x, r) v
      (coneRadialField (I := I) (N := N) (x, r)) = v.2 := by
  rw [coneMetric_metricInner_prod]
  change (r : ℝ) ^ 2 * g.metricInner x v.1 0 + v.2 * 1 = v.2
  rw [g.metricInner_zero_right]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Math.** A horizontal lift differentiates a scalar function through its
slice at fixed radius. -/
theorem coneHorizontalLift_dir (X : SmoothVectorField I N)
    {f : N × ↥positiveReal → ℝ}
    (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
    (q : N × ↥positiveReal) :
    (coneHorizontalLift X).dir f q =
      X.dir (fun x => f (x, q.2)) q.1 := by
  rw [SmoothVectorField.dir, SmoothVectorField.dir]
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) f q
      (X q.1, (0 : ℝ)) = _
  rw [mfderiv_prod_eq_add_apply (hf.mdifferentiableAt (by simp))]
  change mfderiv I 𝓘(ℝ, ℝ) (fun x => f (x, q.2)) q.1 (X q.1)
      + mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r => f (q.1, r)) q.2
          (0 : TangentSpace 𝓘(ℝ, ℝ) q.2)
    = mfderiv I 𝓘(ℝ, ℝ) (fun x => f (x, q.2)) q.1 (X q.1)
  rw [map_zero, add_zero]

omit [FiniteDimensional ℝ E] in
/-- **Math.** The radial field differentiates a scalar function in the positive
real factor. -/
theorem coneRadialField_dir {f : N × ↥positiveReal → ℝ}
    (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
    (q : N × ↥positiveReal) :
    (coneRadialField (I := I) (N := N)).dir f q =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r => f (q.1, r)) q.2 (1 : ℝ) := by
  rw [SmoothVectorField.dir]
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) f q
      ((0 : TangentSpace I q.1), (1 : ℝ)) = _
  rw [mfderiv_prod_eq_add_apply (hf.mdifferentiableAt (by simp)),
    map_zero, zero_add]

omit [FiniteDimensional ℝ E] in
/-- **Math.** Horizontal lifts do not change the cone radius. -/
@[simp] theorem coneHorizontalLift_dir_coneRadius (X : SmoothVectorField I N)
    (q : N × ↥positiveReal) :
    (coneHorizontalLift X).dir (coneRadius (N := N)) q = 0 := by
  rw [coneHorizontalLift_dir X coneRadius_contMDiff q]
  change X.dir (fun _ : N => (q.2 : ℝ)) q.1 = 0
  rw [SmoothVectorField.dir, mfderiv_const]
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Math.** The unit radial field differentiates the cone radius to one. -/
@[simp] theorem coneRadialField_dir_coneRadius (q : N × ↥positiveReal) :
    (coneRadialField (I := I) (N := N)).dir (coneRadius (N := N)) q = 1 := by
  rw [coneRadialField_dir coneRadius_contMDiff q]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (Subtype.val : ↥positiveReal → ℝ) q.2 (1 : ℝ) = 1
  rw [mfderiv_subtype_val_opens]
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Math.** The radial field annihilates functions pulled back from the cone base. -/
theorem coneRadialField_dir_comp_fst {h : N → ℝ}
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) (q : N × ↥positiveReal) :
    (coneRadialField (I := I) (N := N)).dir (h ∘ Prod.fst) q = 0 := by
  rw [coneRadialField_dir (hh.comp contMDiff_fst) q]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ↥positiveReal => h q.1)
    q.2 (1 : ℝ) = 0
  rw [mfderiv_const]
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Math.** The radial derivative of the squared cone radius is `2r`. -/
theorem coneRadialField_dir_coneRadius_sq (q : N × ↥positiveReal) :
    (coneRadialField (I := I) (N := N)).dir
        (fun p => coneRadius (N := N) p ^ 2) q =
      2 * coneRadius (N := N) q := by
  have hsquare :
      (fun p : N × ↥positiveReal => coneRadius (N := N) p ^ 2) =
        fun p => coneRadius (N := N) p * coneRadius (N := N) p := by
    funext p
    rw [pow_two]
  rw [hsquare, (coneRadialField (I := I) (N := N)).dir_mul q
    (coneRadius_contMDiff.mdifferentiableAt (by simp))
    (coneRadius_contMDiff.mdifferentiableAt (by simp)),
    coneRadialField_dir_coneRadius]
  ring

/-- **Math.** The bracket of two horizontal lifts is the horizontal lift of
their bracket on the cone base. -/
theorem bracketField_coneHorizontalLift_coneHorizontalLift
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (X Y : SmoothVectorField I N) :
    bracketField (coneHorizontalLift X) (coneHorizontalLift Y) =
      coneHorizontalLift (bracketField X Y) := by
  obtain ⟨Z, -, hunique⟩ :=
    exists_unique_bracketField (coneHorizontalLift X) (coneHorizontalLift Y)
  have hleft : ∀ (f : N × ↥positiveReal → ℝ),
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f →
      ∀ q, (bracketField (coneHorizontalLift X) (coneHorizontalLift Y)).dir f q
        = (coneHorizontalLift X).dir ((coneHorizontalLift Y).dir f) q
          - (coneHorizontalLift Y).dir ((coneHorizontalLift X).dir f) q := by
    intro f hf q
    exact bracketField_dir (coneHorizontalLift X) (coneHorizontalLift Y) hf q
  have hright : ∀ (f : N × ↥positiveReal → ℝ),
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f →
      ∀ q, (coneHorizontalLift (bracketField X Y)).dir f q
        = (coneHorizontalLift X).dir ((coneHorizontalLift Y).dir f) q
          - (coneHorizontalLift Y).dir ((coneHorizontalLift X).dir f) q := by
    intro f hf q
    have hslice : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => f (x, q.2)) :=
      hf.comp (contMDiff_id.prodMk contMDiff_const)
    have hYslice :
        (fun x => (coneHorizontalLift Y).dir f (x, q.2)) =
          Y.dir (fun z => f (z, q.2)) := by
      funext x
      exact coneHorizontalLift_dir Y hf (x, q.2)
    have hXslice :
        (fun x => (coneHorizontalLift X).dir f (x, q.2)) =
          X.dir (fun z => f (z, q.2)) := by
      funext x
      exact coneHorizontalLift_dir X hf (x, q.2)
    rw [coneHorizontalLift_dir (bracketField X Y) hf q,
      coneHorizontalLift_dir X ((coneHorizontalLift Y).dir_contMDiff hf) q,
      coneHorizontalLift_dir Y ((coneHorizontalLift X).dir_contMDiff hf) q,
      hYslice, hXslice, bracketField_dir X Y hslice q.1]
  exact (hunique _ hleft).trans (hunique _ hright).symm

/-! ### The horizontal-radial bracket -/

namespace ConeProductBracket

open Bundle Function Filter VectorField ContinuousLinearMap

section ContinuousLinearMap

variable {𝕜 : Type*} [Semiring 𝕜]
  {F₁ : Type*} [TopologicalSpace F₁] [AddCommMonoid F₁] [Module 𝕜 F₁]
  {F₂ : Type*} [TopologicalSpace F₂] [AddCommMonoid F₂] [Module 𝕜 F₂]
  {G₁ : Type*} [TopologicalSpace G₁] [AddCommMonoid G₁] [Module 𝕜 G₁]
  {G₂ : Type*} [TopologicalSpace G₂] [AddCommMonoid G₂] [Module 𝕜 G₂]

private lemma inverse_prodMap {A : F₁ →L[𝕜] G₁} {B : F₂ →L[𝕜] G₂}
    (hA : A.IsInvertible) (hB : B.IsInvertible) :
    (A.prodMap B).inverse = A.inverse.prodMap B.inverse := by
  apply ContinuousLinearMap.inverse_eq
  · refine ContinuousLinearMap.ext fun x => ?_
    obtain ⟨u, v⟩ := x
    simp [hA.self_apply_inverse, hB.self_apply_inverse]
  · refine ContinuousLinearMap.ext fun x => ?_
    obtain ⟨u, v⟩ := x
    simp [hA.inverse_apply_self, hB.inverse_apply_self]

private lemma inverse_prodMap_apply_right_zero
    {A : F₁ →L[𝕜] G₁} {B : F₂ →L[𝕜] G₂}
    (hA : A.IsInvertible) (hB : B.IsInvertible) (u : G₁) :
    (A.prodMap B).inverse (u, 0) = (A.inverse u, 0) := by
  rw [inverse_prodMap hA hB]
  simp

private lemma inverse_prodMap_apply_left_zero
    {A : F₁ →L[𝕜] G₁} {B : F₂ →L[𝕜] G₂}
    (hA : A.IsInvertible) (hB : B.IsInvertible) (v : G₂) :
    (A.prodMap B).inverse (0, v) = (0, B.inverse v) := by
  rw [inverse_prodMap hA hB]
  simp

end ContinuousLinearMap

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [CompleteSpace E₁]
  {H₁ : Type*} [TopologicalSpace H₁]
  {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [CompleteSpace E₂]
  {H₂ : Type*} [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

omit [CompleteSpace E₁] [I₁.Boundaryless] [IsManifold I₁ ∞ M₁]
    [CompleteSpace E₂] [I₂.Boundaryless] [IsManifold I₂ ∞ M₂] in
private def liftFst (I₂ : ModelWithCorners ℝ E₂ H₂)
    (V : Π x : M₁, TangentSpace I₁ x) :
    Π x : M₁ × M₂, TangentSpace (I₁.prod I₂) x :=
  fun x => (V x.1, (0 : TangentSpace I₂ x.2))

omit [CompleteSpace E₁] [I₁.Boundaryless] [IsManifold I₁ ∞ M₁]
    [CompleteSpace E₂] [I₂.Boundaryless] [IsManifold I₂ ∞ M₂] in
private def liftSnd (I₁ : ModelWithCorners ℝ E₁ H₁)
    (W : Π x : M₂, TangentSpace I₂ x) :
    Π x : M₁ × M₂, TangentSpace (I₁.prod I₂) x :=
  fun x => ((0 : TangentSpace I₁ x.1), W x.2)

omit [CompleteSpace E₁] [I₁.Boundaryless] [IsManifold I₁ ∞ M₁]
    [CompleteSpace E₂] [I₂.Boundaryless] [IsManifold I₂ ∞ M₂] in
private lemma extChartAt_prod_symm_coe (x₀ : M₁ × M₂) :
    ((extChartAt (I₁.prod I₂) x₀).symm : E₁ × E₂ → M₁ × M₂) =
      Prod.map (extChartAt I₁ x₀.1).symm (extChartAt I₂ x₀.2).symm := by
  rw [extChartAt_prod]
  exact PartialEquiv.prod_coe_symm _ _

omit [CompleteSpace E₁] in
private lemma contMDiffAt_extChartAt_symm' {x : M₁} {y : E₁}
    (hy : y ∈ (extChartAt I₁ x).target) :
    ContMDiffAt 𝓘(ℝ, E₁) I₁ ∞ (extChartAt I₁ x).symm y := by
  have h := contMDiffWithinAt_extChartAt_symm_range (I := I₁) (n := ∞) x hy
  rwa [I₁.range_eq_univ, contMDiffWithinAt_univ] at h

omit [CompleteSpace E₁] [CompleteSpace E₂] in
private lemma mfderiv_extChartAt_prod_symm (x₀ : M₁ × M₂) {y : E₁ × E₂}
    (hy₁ : y.1 ∈ (extChartAt I₁ x₀.1).target)
    (hy₂ : y.2 ∈ (extChartAt I₂ x₀.2).target) :
    mfderiv 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂)
        (extChartAt (I₁.prod I₂) x₀).symm y =
      (mfderiv 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm y.1).prodMap
        (mfderiv 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm y.2) := by
  have h1 : MDifferentiableAt 𝓘(ℝ, E₁) I₁
      (extChartAt I₁ x₀.1).symm y.1 :=
    (contMDiffAt_extChartAt_symm' hy₁).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, E₂) I₂
      (extChartAt I₂ x₀.2).symm y.2 :=
    (contMDiffAt_extChartAt_symm' hy₂).mdifferentiableAt (by simp)
  have key := (h1.hasMFDerivAt).prodMap (h2.hasMFDerivAt)
  rw [← modelWithCornersSelf_prod] at key
  rw [extChartAt_prod_symm_coe]
  exact HasMFDerivAt.mfderiv key

omit [CompleteSpace E₁] in
private lemma isInvertible_mfderiv_extChartAt_symm {x : M₁} {y : E₁}
    (hy : y ∈ (extChartAt I₁ x).target) :
    (mfderiv 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm y).IsInvertible := by
  have h := isInvertible_mfderivWithin_extChartAt_symm (I := I₁) (x := x) hy
  rwa [I₁.range_eq_univ, mfderivWithin_univ] at h

omit [CompleteSpace E₁] [CompleteSpace E₂] in
private lemma mpullbackWithin_liftFst_eq (x₀ : M₁ × M₂)
    {V : Π x : M₁, TangentSpace I₁ x} {y : E₁ × E₂}
    (hy₁ : y.1 ∈ (extChartAt I₁ x₀.1).target)
    (hy₂ : y.2 ∈ (extChartAt I₂ x₀.2).target) :
    mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂)
        (extChartAt (I₁.prod I₂) x₀).symm (liftFst I₂ V)
        (Set.range (I₁.prod I₂)) y =
      (mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm V y.1, 0) := by
  rw [mpullbackWithin_apply, (I₁.prod I₂).range_eq_univ, mfderivWithin_univ,
    mfderiv_extChartAt_prod_symm x₀ hy₁ hy₂, extChartAt_prod_symm_coe,
    show liftFst I₂ V
        (Prod.map (⇑(extChartAt I₁ x₀.1).symm)
          (⇑(extChartAt I₂ x₀.2).symm) y) =
      (V ((extChartAt I₁ x₀.1).symm y.1), 0) from rfl]
  exact (inverse_prodMap_apply_right_zero
    (isInvertible_mfderiv_extChartAt_symm hy₁)
    (isInvertible_mfderiv_extChartAt_symm hy₂) _).trans rfl

omit [CompleteSpace E₁] [CompleteSpace E₂] in
private lemma mpullbackWithin_liftSnd_eq (x₀ : M₁ × M₂)
    {W : Π x : M₂, TangentSpace I₂ x} {y : E₁ × E₂}
    (hy₁ : y.1 ∈ (extChartAt I₁ x₀.1).target)
    (hy₂ : y.2 ∈ (extChartAt I₂ x₀.2).target) :
    mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂)
        (extChartAt (I₁.prod I₂) x₀).symm (liftSnd I₁ W)
        (Set.range (I₁.prod I₂)) y =
      (0, mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm W y.2) := by
  rw [mpullbackWithin_apply, (I₁.prod I₂).range_eq_univ, mfderivWithin_univ,
    mfderiv_extChartAt_prod_symm x₀ hy₁ hy₂, extChartAt_prod_symm_coe,
    show liftSnd I₁ W
        (Prod.map (⇑(extChartAt I₁ x₀.1).symm)
          (⇑(extChartAt I₂ x₀.2).symm) y) =
      (0, W ((extChartAt I₂ x₀.2).symm y.2)) from rfl]
  exact (inverse_prodMap_apply_left_zero
    (isInvertible_mfderiv_extChartAt_symm hy₁)
    (isInvertible_mfderiv_extChartAt_symm hy₂) _).trans rfl

omit [CompleteSpace E₁] [CompleteSpace E₂] in
private lemma lieBracket_eq_zero_of_decoupled
    {f : E₁ → E₁} {g : E₂ → E₂}
    {A B : E₁ × E₂ → E₁ × E₂} {z : E₁ × E₂}
    (hA : A =ᶠ[𝓝 z] fun y => (f y.1, 0))
    (hB : B =ᶠ[𝓝 z] fun y => (0, g y.2))
    (hf : DifferentiableAt ℝ f z.1) (hg : DifferentiableAt ℝ g z.2) :
    VectorField.lieBracket ℝ A B z = 0 := by
  have hB' : HasFDerivAt (fun y : E₁ × E₂ => ((0 : E₁), g y.2))
      ((ContinuousLinearMap.inr ℝ E₁ E₂) ∘L (fderiv ℝ g z.2) ∘L
        (ContinuousLinearMap.snd ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inr ℝ E₁ E₂).hasFDerivAt.comp z
      (hg.hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ E₁ E₂).hasFDerivAt)
  have hA' : HasFDerivAt (fun y : E₁ × E₂ => (f y.1, (0 : E₂)))
      ((ContinuousLinearMap.inl ℝ E₁ E₂) ∘L (fderiv ℝ f z.1) ∘L
        (ContinuousLinearMap.fst ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inl ℝ E₁ E₂).hasFDerivAt.comp z
      (hf.hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ E₁ E₂).hasFDerivAt)
  show fderiv ℝ B z (A z) - fderiv ℝ A z (B z) = 0
  rw [hA.fderiv_eq, hB.fderiv_eq, hA.eq_of_nhds, hB.eq_of_nhds,
    hA'.fderiv, hB'.fderiv]
  simp

private lemma differentiableAt_mpullback_extChartAt_symm
    {V : Π x : M₁, TangentSpace I₁ x}
    (hV : ContMDiff I₁ I₁.tangent ∞
      (fun p => (⟨p, V p⟩ : TangentBundle I₁ M₁)))
    (x : M₁) :
    DifferentiableAt ℝ
      (mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm V)
      (extChartAt I₁ x x) := by
  have heq :
      mpullbackWithin 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm V (Set.range I₁) =
        mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm V := by
    funext z
    rw [mpullbackWithin_apply, mpullback_apply, I₁.range_eq_univ,
      mfderivWithin_univ]
  have hmd : MDifferentiableWithinAt I₁ I₁.tangent
      (fun p => (⟨p, V p⟩ : TangentBundle I₁ M₁)) Set.univ x :=
    ((hV x).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  have h := hmd.differentiableWithinAt_mpullbackWithin_vectorField
  rw [heq] at h
  rwa [preimage_univ, I₁.range_eq_univ, univ_inter,
    differentiableWithinAt_univ] at h

private theorem mlieBracket_liftFst_liftSnd
    {V : Π x : M₁, TangentSpace I₁ x}
    {W : Π x : M₂, TangentSpace I₂ x}
    (hV : ContMDiff I₁ I₁.tangent ∞
      (fun p => (⟨p, V p⟩ : TangentBundle I₁ M₁)))
    (hW : ContMDiff I₂ I₂.tangent ∞
      (fun p => (⟨p, W p⟩ : TangentBundle I₂ M₂))) :
    VectorField.mlieBracket (I₁.prod I₂) (liftFst I₂ V) (liftSnd I₁ W) = 0 := by
  funext x₀
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_apply]
  have hset :
      ((extChartAt (I₁.prod I₂) x₀).symm ⁻¹' Set.univ ∩
        Set.range (I₁.prod I₂)) = Set.univ := by
    rw [preimage_univ, (I₁.prod I₂).range_eq_univ, univ_inter]
  rw [hset, VectorField.lieBracketWithin_univ]
  have hnhds : ∀ᶠ y : E₁ × E₂ in 𝓝 (extChartAt (I₁.prod I₂) x₀ x₀),
      y.1 ∈ (extChartAt I₁ x₀.1).target ∧
        y.2 ∈ (extChartAt I₂ x₀.2).target := by
    have h := extChartAt_target_mem_nhds (I := I₁.prod I₂) x₀
    rw [extChartAt_prod, PartialEquiv.prod_target] at h
    filter_upwards [h] with y hy using hy
  have hbr : VectorField.lieBracket ℝ
      (mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂)
        (extChartAt (I₁.prod I₂) x₀).symm (liftFst I₂ V)
        (Set.range (I₁.prod I₂)))
      (mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂)
        (extChartAt (I₁.prod I₂) x₀).symm (liftSnd I₁ W)
        (Set.range (I₁.prod I₂)))
      (extChartAt (I₁.prod I₂) x₀ x₀) = 0 := by
    refine lieBracket_eq_zero_of_decoupled
      (f := mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm V)
      (g := mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm W)
      ?_ ?_ ?_ ?_
    · filter_upwards [hnhds] with y hy using
        mpullbackWithin_liftFst_eq x₀ hy.1 hy.2
    · filter_upwards [hnhds] with y hy using
        mpullbackWithin_liftSnd_eq x₀ hy.1 hy.2
    · exact differentiableAt_mpullback_extChartAt_symm hV x₀.1
    · exact differentiableAt_mpullback_extChartAt_symm hW x₀.2
  rw [hbr]
  exact map_zero _

end ConeProductBracket

omit [FiniteDimensional ℝ E] in
/-- **Math.** A horizontal lift commutes with the unit radial coordinate field. -/
theorem bracketField_coneHorizontalLift_coneRadialField
    [CompleteSpace E] [I.Boundaryless] (X : SmoothVectorField I N) :
    bracketField (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) = 0 := by
  let R : SmoothVectorField 𝓘(ℝ, ℝ) ↥positiveReal :=
    SmoothVectorField.ofOpens (fun _ => (1 : ℝ)) contMDiff_const
  have hraw := ConeProductBracket.mlieBracket_liftFst_liftSnd
    (I₂ := 𝓘(ℝ, ℝ)) (M₂ := ↥positiveReal)
    (V := fun x => X x) (W := fun _ => (1 : ℝ)) X.smooth R.smooth
  apply SmoothVectorField.ext
  intro q
  change VectorField.mlieBracket (I.prod 𝓘(ℝ, ℝ))
      (ConeProductBracket.liftFst 𝓘(ℝ, ℝ) (fun x => X x))
      (ConeProductBracket.liftSnd I (fun _ => (1 : ℝ))) q = 0
  exact congrFun hraw q

omit [FiniteDimensional ℝ E] in
/-- **Math.** The radial-horizontal bracket vanishes in the reverse order as well. -/
theorem bracketField_coneRadialField_coneHorizontalLift
    [CompleteSpace E] [I.Boundaryless] (X : SmoothVectorField I N) :
    bracketField (coneRadialField (I := I) (N := N))
      (coneHorizontalLift X) = 0 := by
  rw [bracketField_antisymm,
    bracketField_coneHorizontalLift_coneRadialField X]
  apply SmoothVectorField.ext
  intro q
  exact neg_zero

/-- **Math.** Horizontal lifts have the base inner product scaled by `r²`. -/
@[simp] theorem coneMetric_horizontal_horizontal (g : RiemannianMetric I N)
    (X Y : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
    (coneMetric g).metricInner (x, r)
        (coneHorizontalLift X (x, r)) (coneHorizontalLift Y (x, r)) =
      (r : ℝ) ^ 2 * g.metricInner x (X x) (Y x) := by
  rw [coneMetric_metricInner_prod]
  simp [coneHorizontalLift]

/-- **Math.** The horizontal and radial cone distributions are orthogonal. -/
@[simp] theorem coneMetric_horizontal_radial (g : RiemannianMetric I N)
    (X : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
    (coneMetric g).metricInner (x, r)
        (coneHorizontalLift X (x, r))
        (coneRadialField (I := I) (N := N) (x, r)) = 0 := by
  rw [coneMetric_metricInner_prod]
  change (r : ℝ) ^ 2 * g.metricInner x (X x) 0 + 0 * 1 = 0
  rw [g.metricInner_zero_right]
  ring

/-- **Math.** The radial coordinate field has unit length in the cone metric. -/
@[simp] theorem coneMetric_radial_radial (g : RiemannianMetric I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).metricInner (x, r)
        (coneRadialField (I := I) (N := N) (x, r))
        (coneRadialField (I := I) (N := N) (x, r)) = 1 := by
  rw [coneMetric_metricInner_prod]
  change (r : ℝ) ^ 2 * g.metricInner x 0 0 + 1 * 1 = 1
  rw [g.metricInner_zero_left]
  ring

/-- **Math.** Along a horizontal lift, the derivative of the horizontal metric
pairing is the lifted base derivative, scaled by `r²`. -/
theorem coneHorizontalLift_dir_metric_horizontal_horizontal
    (g : RiemannianMetric I N) (X Y Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneHorizontalLift X).dir
        (fun q => (coneMetric g).metricInner q
          (coneHorizontalLift Y q) (coneHorizontalLift Z q)) (x, r) =
      (r : ℝ) ^ 2 * X.dir (fun p => g.metricInner p (Y p) (Z p)) x := by
  rw [coneHorizontalLift_dir X
    ((coneMetric g).metricInner_field_contMDiff
      (coneHorizontalLift Y) (coneHorizontalLift Z)) (x, r)]
  simp only [coneMetric_horizontal_horizontal]
  exact X.dir_const_mul ((r : ℝ) ^ 2) x
    (g.metricInner_field_mdifferentiableAt Y Z x)

/-- **Math.** Along the radial field, the derivative of the horizontal metric
pairing is `2r` times the corresponding base pairing. -/
theorem coneRadialField_dir_metric_horizontal_horizontal
    (g : RiemannianMetric I N) (Y Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneRadialField (I := I) (N := N)).dir
        (fun q => (coneMetric g).metricInner q
          (coneHorizontalLift Y q) (coneHorizontalLift Z q)) (x, r) =
      2 * (r : ℝ) * g.metricInner x (Y x) (Z x) := by
  let basePair : N → ℝ := fun p => g.metricInner p (Y p) (Z p)
  have hbase : ContMDiff I 𝓘(ℝ, ℝ) ∞ basePair :=
    g.metricInner_field_contMDiff Y Z
  have hshape :
      (fun q => (coneMetric g).metricInner q
        (coneHorizontalLift Y q) (coneHorizontalLift Z q)) =
      fun q => coneRadius (N := N) q ^ 2 * (basePair ∘ Prod.fst) q := by
    funext q
    exact coneMetric_horizontal_horizontal g Y Z q.1 q.2
  rw [hshape, (coneRadialField (I := I) (N := N)).dir_mul
    (f := fun q => coneRadius (N := N) q ^ 2)
    (h := basePair ∘ Prod.fst) (x, r)
    ((coneRadius_contMDiff.pow 2).mdifferentiableAt (by simp))
    ((hbase.comp contMDiff_fst).mdifferentiableAt (by simp)),
    coneRadialField_dir_comp_fst hbase, coneRadialField_dir_coneRadius_sq]
  change (r : ℝ) ^ 2 * 0 + g.metricInner x (Y x) (Z x) * (2 * (r : ℝ)) =
    2 * (r : ℝ) * g.metricInner x (Y x) (Z x)
  ring

/-- **Math.** Every cone field differentiates a horizontal-radial metric
pairing to zero. -/
theorem coneField_dir_metric_horizontal_radial
    (g : RiemannianMetric I N)
    (A : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal))
    (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
    A.dir (fun p => (coneMetric g).metricInner p
      (coneHorizontalLift X p) (coneRadialField (I := I) (N := N) p)) q = 0 := by
  have hzero :
      (fun p => (coneMetric g).metricInner p
        (coneHorizontalLift X p) (coneRadialField (I := I) (N := N) p)) =
      fun _ => 0 := by
    funext p
    exact coneMetric_horizontal_radial g X p.1 p.2
  rw [hzero, SmoothVectorField.dir, mfderiv_const]
  rfl

/-- **Math.** Every cone field also differentiates the reversed
radial-horizontal pairing to zero. -/
theorem coneField_dir_metric_radial_horizontal
    (g : RiemannianMetric I N)
    (A : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal))
    (X : SmoothVectorField I N) (q : N × ↥positiveReal) :
    A.dir (fun p => (coneMetric g).metricInner p
      (coneRadialField (I := I) (N := N) p) (coneHorizontalLift X p)) q = 0 := by
  have hzero :
      (fun p => (coneMetric g).metricInner p
        (coneRadialField (I := I) (N := N) p) (coneHorizontalLift X p)) =
      fun _ => 0 := by
    funext p
    rw [(coneMetric g).metricInner_comm]
    exact coneMetric_horizontal_radial g X p.1 p.2
  rw [hzero, SmoothVectorField.dir, mfderiv_const]
  rfl

/-- **Math.** Every cone field differentiates the unit radial norm to zero. -/
theorem coneField_dir_metric_radial_radial
    (g : RiemannianMetric I N)
    (A : SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal))
    (q : N × ↥positiveReal) :
    A.dir (fun p => (coneMetric g).metricInner p
      (coneRadialField (I := I) (N := N) p)
      (coneRadialField (I := I) (N := N) p)) q = 0 := by
  have hone :
      (fun p => (coneMetric g).metricInner p
        (coneRadialField (I := I) (N := N) p)
        (coneRadialField (I := I) (N := N) p)) =
      fun _ => 1 := by
    funext p
    exact coneMetric_radial_radial g p.1 p.2
  rw [hone, SmoothVectorField.dir, mfderiv_const]
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Math.** The unit radial coordinate field commutes with itself. -/
theorem bracketField_coneRadialField_self
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N] :
    bracketField (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) = 0 := by
  apply SmoothVectorField.ext
  intro q
  change VectorField.mlieBracket (I.prod 𝓘(ℝ, ℝ))
    (coneRadialField (I := I) (N := N)).toFun
    (coneRadialField (I := I) (N := N)).toFun q = 0
  simp

/-- **Math.** The cone Koszul expression for two horizontal fields tested
against the radial field is `-2r` times their base pairing. -/
theorem coneMetric_koszulRHS_horizontal_horizontal_radial
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X Y : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneHorizontalLift Y) (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (x, r) =
      -2 * (r : ℝ) * g.metricInner x (X x) (Y x) := by
  have hbrYR :
      DCLieBracket (coneHorizontalLift Y)
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneHorizontalLift Y)
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneHorizontalLift_coneRadialField]
    rfl
  have hbrXR :
      DCLieBracket (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneHorizontalLift_coneRadialField]
    rfl
  have hbrYX :
      DCLieBracket (coneHorizontalLift Y) (coneHorizontalLift X) (x, r) =
        coneHorizontalLift (bracketField Y X) (x, r) := by
    change bracketField (coneHorizontalLift Y) (coneHorizontalLift X) (x, r) = _
    rw [bracketField_coneHorizontalLift_coneHorizontalLift]
  unfold RiemannianMetric.koszulRHS
  rw [coneField_dir_metric_horizontal_radial,
    coneField_dir_metric_radial_horizontal,
    coneRadialField_dir_metric_horizontal_horizontal,
    hbrYR, hbrXR, hbrYX,
    (coneMetric g).metricInner_zero_left,
    (coneMetric g).metricInner_zero_left,
    coneMetric_horizontal_radial]
  rw [g.metricInner_comm x (Y x) (X x)]
  ring

/-- **Math.** Testing the Koszul expression for `nabla_X partial_r` against a
horizontal field gives `2r` times the base pairing. -/
theorem coneMetric_koszulRHS_radial_horizontal_horizontal
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneRadialField (I := I) (N := N))
      (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) =
      2 * (r : ℝ) * g.metricInner x (X x) (Z x) := by
  have hbrRZ :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneHorizontalLift Z) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneHorizontalLift Z) (x, r) = 0
    rw [bracketField_coneRadialField_coneHorizontalLift]
    rfl
  have hbrXZ :
      DCLieBracket (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) =
        coneHorizontalLift (bracketField X Z) (x, r) := by
    change bracketField (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) = _
    rw [bracketField_coneHorizontalLift_coneHorizontalLift]
  have hbrRX :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneHorizontalLift X) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneHorizontalLift X) (x, r) = 0
    rw [bracketField_coneRadialField_coneHorizontalLift]
    rfl
  unfold RiemannianMetric.koszulRHS
  rw [coneRadialField_dir_metric_horizontal_horizontal,
    coneField_dir_metric_horizontal_radial,
    coneField_dir_metric_radial_horizontal,
    hbrRZ, hbrXZ, hbrRX,
    (coneMetric g).metricInner_zero_left,
    coneMetric_horizontal_radial,
    (coneMetric g).metricInner_zero_left]
  ring

/-- **Math.** Testing the Koszul expression for `nabla_partial_r X` against a
horizontal field gives the same `2r` base pairing. -/
theorem coneMetric_koszulRHS_horizontal_radial_horizontal
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (coneHorizontalLift Z) (x, r) =
      2 * (r : ℝ) * g.metricInner x (X x) (Z x) := by
  have hbrXZ :
      DCLieBracket (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) =
        coneHorizontalLift (bracketField X Z) (x, r) := by
    change bracketField (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) = _
    rw [bracketField_coneHorizontalLift_coneHorizontalLift]
  have hbrRZ :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneHorizontalLift Z) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneHorizontalLift Z) (x, r) = 0
    rw [bracketField_coneRadialField_coneHorizontalLift]
    rfl
  have hbrXR :
      DCLieBracket (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneHorizontalLift_coneRadialField]
    rfl
  unfold RiemannianMetric.koszulRHS
  rw [coneField_dir_metric_radial_horizontal,
    coneRadialField_dir_metric_horizontal_horizontal,
    coneField_dir_metric_horizontal_radial,
    hbrXZ, hbrRZ, hbrXR,
    coneMetric_horizontal_radial,
    (coneMetric g).metricInner_zero_left,
    (coneMetric g).metricInner_zero_left]
  rw [g.metricInner_comm x (Z x) (X x)]
  ring

/-- **Math.** The radial-radial Koszul expression vanishes against every
horizontal test field. -/
theorem coneMetric_koszulRHS_radial_radial_horizontal
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (coneHorizontalLift Z) (x, r) = 0 := by
  have hbrRZ :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneHorizontalLift Z) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneHorizontalLift Z) (x, r) = 0
    rw [bracketField_coneRadialField_coneHorizontalLift]
    rfl
  have hbrRR :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneRadialField_self]
    rfl
  unfold RiemannianMetric.koszulRHS
  rw [coneField_dir_metric_radial_horizontal,
    coneField_dir_metric_horizontal_radial,
    coneField_dir_metric_radial_radial,
    hbrRZ, hbrRR]
  simp

/-- **Math.** The radial-radial Koszul expression also vanishes against the
radial test field. -/
theorem coneMetric_koszulRHS_radial_radial_radial
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
  have hbrRR :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneRadialField_self]
    rfl
  unfold RiemannianMetric.koszulRHS
  simp_rw [coneField_dir_metric_radial_radial]
  rw [hbrRR]
  simp

/-- **Math.** The Koszul expression for `nabla_X partial_r` has no radial
component. -/
theorem coneMetric_koszulRHS_radial_horizontal_radial
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneRadialField (I := I) (N := N))
      (coneHorizontalLift X) (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
  have hbrRR :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneRadialField_self]
    rfl
  have hbrXR :
      DCLieBracket (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneHorizontalLift_coneRadialField]
    rfl
  have hbrRX :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneHorizontalLift X) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneHorizontalLift X) (x, r) = 0
    rw [bracketField_coneRadialField_coneHorizontalLift]
    rfl
  unfold RiemannianMetric.koszulRHS
  rw [coneField_dir_metric_horizontal_radial,
    coneField_dir_metric_radial_radial,
    coneField_dir_metric_radial_horizontal,
    hbrRR, hbrXR, hbrRX]
  simp

/-- **Math.** The Koszul expression for `nabla_partial_r X` also has no radial
component. -/
theorem coneMetric_koszulRHS_horizontal_radial_radial
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
  have hbrXR :
      DCLieBracket (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneHorizontalLift_coneRadialField]
    rfl
  have hbrRR :
      DCLieBracket (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N)) (x, r) = 0 := by
    change bracketField (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r) = 0
    rw [bracketField_coneRadialField_self]
    rfl
  unfold RiemannianMetric.koszulRHS
  rw [coneField_dir_metric_radial_radial,
    coneField_dir_metric_radial_horizontal,
    coneField_dir_metric_horizontal_radial,
    hbrXR, hbrRR]
  simp

/-- **Math.** The cone Koszul expression on three horizontal lifts is the
base Koszul expression scaled by `r²`. -/
theorem coneMetric_koszulRHS_horizontal_horizontal_horizontal
    [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X Y Z : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    (coneMetric g).koszulRHS (coneHorizontalLift Y) (coneHorizontalLift X)
        (coneHorizontalLift Z) (x, r) =
      (r : ℝ) ^ 2 * g.koszulRHS Y X Z x := by
  have hbrYZ :
      DCLieBracket (coneHorizontalLift Y) (coneHorizontalLift Z) (x, r) =
        coneHorizontalLift (bracketField Y Z) (x, r) := by
    change bracketField (coneHorizontalLift Y) (coneHorizontalLift Z) (x, r) = _
    rw [bracketField_coneHorizontalLift_coneHorizontalLift]
  have hbrXZ :
      DCLieBracket (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) =
        coneHorizontalLift (bracketField X Z) (x, r) := by
    change bracketField (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) = _
    rw [bracketField_coneHorizontalLift_coneHorizontalLift]
  have hbrYX :
      DCLieBracket (coneHorizontalLift Y) (coneHorizontalLift X) (x, r) =
        coneHorizontalLift (bracketField Y X) (x, r) := by
    change bracketField (coneHorizontalLift Y) (coneHorizontalLift X) (x, r) = _
    rw [bracketField_coneHorizontalLift_coneHorizontalLift]
  unfold RiemannianMetric.koszulRHS
  rw [coneHorizontalLift_dir_metric_horizontal_horizontal g Y X Z x r,
    coneHorizontalLift_dir_metric_horizontal_horizontal g X Z Y x r,
    coneHorizontalLift_dir_metric_horizontal_horizontal g Z Y X x r,
    hbrYZ, hbrXZ, hbrYX,
    coneMetric_horizontal_horizontal, coneMetric_horizontal_horizontal,
    coneMetric_horizontal_horizontal]
  simp only [bracketField_apply]
  ring

/-! ### The four cone Levi-Civita formulas -/

/-- **Math.** The covariant derivative of two horizontal lifts has the base
covariant derivative as its horizontal component and `-r g(X,Y)` as its radial
component. -/
theorem coneLeviCivitaConnection_cov_horizontal_horizontal_apply
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X Y : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
      (coneHorizontalLift Y)) (x, r) =
      (((leviCivitaConnectionGeneral g).cov X Y) x,
        -(r : ℝ) * g.metricInner x (X x) (Y x)) := by
  apply Prod.ext
  · apply (g.metricInner_eq_iff_eq x _ _).mp
    intro w
    obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq (I := I) x w
    rw [← hZ]
    have hc := (coneMetric g).koszulDualSection_dual
      (coneHorizontalLift Y) (coneHorizontalLift X)
      (coneHorizontalLift Z) (x, r)
    have hb := g.koszulDualSection_dual Y X Z x
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneHorizontalLift Y)) (x, r))
      (coneHorizontalLift Z (x, r)) =
        (coneMetric g).koszulRHS (coneHorizontalLift Y)
          (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) at hc
    change 2 * g.metricInner x (((leviCivitaConnectionGeneral g).cov X Y) x)
      (Z x) = g.koszulRHS Y X Z x at hb
    rw [coneMetric_koszulRHS_horizontal_horizontal_horizontal,
      coneMetric_metricInner_prod, coneHorizontalLift_apply] at hc
    simp only [mul_zero, add_zero] at hc
    have hr2 : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos r.property
    nlinarith
  · have hc := (coneMetric g).koszulDualSection_dual
      (coneHorizontalLift Y) (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (x, r)
    change
      (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneHorizontalLift Y)) (x, r)).2 =
        -(r : ℝ) * g.metricInner x (X x) (Y x)
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneHorizontalLift Y)) (x, r))
      (coneRadialField (I := I) (N := N) (x, r)) =
        (coneMetric g).koszulRHS (coneHorizontalLift Y)
          (coneHorizontalLift X)
          (coneRadialField (I := I) (N := N)) (x, r) at hc
    rw [coneMetric_koszulRHS_horizontal_horizontal_radial,
      coneMetric_any_radial] at hc
    linarith

/-- **Math.** A horizontal derivative of the unit radial field is the
horizontal field scaled by `r⁻¹`. -/
theorem coneLeviCivitaConnection_cov_horizontal_radial_apply
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    ((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N))) (x, r) =
      ((r : ℝ)⁻¹ • X x, 0) := by
  apply Prod.ext
  · apply (g.metricInner_eq_iff_eq x _ _).mp
    intro w
    obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq (I := I) x w
    rw [← hZ]
    have hc := (coneMetric g).koszulDualSection_dual
      (coneRadialField (I := I) (N := N)) (coneHorizontalLift X)
      (coneHorizontalLift Z) (x, r)
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N))) (x, r))
      (coneHorizontalLift Z (x, r)) =
        (coneMetric g).koszulRHS
          (coneRadialField (I := I) (N := N))
          (coneHorizontalLift X) (coneHorizontalLift Z) (x, r) at hc
    rw [coneMetric_koszulRHS_radial_horizontal_horizontal,
      coneMetric_metricInner_prod, coneHorizontalLift_apply] at hc
    simp only [mul_zero, add_zero] at hc
    rw [g.metricInner_smul_left, ← div_eq_inv_mul]
    apply (eq_div_iff (ne_of_gt r.property)).2
    have hcancel :
        (2 * (r : ℝ)) *
            (g.metricInner x
                (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
                  (coneRadialField (I := I) (N := N))) (x, r)).1
                (Z x) * (r : ℝ)) =
          (2 * (r : ℝ)) * g.metricInner x (X x) (Z x) := by
      calc
        _ = 2 * ((r : ℝ) ^ 2 *
            g.metricInner x
              (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
                (coneRadialField (I := I) (N := N))) (x, r)).1
              (Z x)) := by ring
        _ = _ := hc
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt r.property)) hcancel
  · change
      (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N))) (x, r)).2 = 0
    have hc := (coneMetric g).koszulDualSection_dual
      (coneRadialField (I := I) (N := N)) (coneHorizontalLift X)
      (coneRadialField (I := I) (N := N)) (x, r)
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N))) (x, r))
      (coneRadialField (I := I) (N := N) (x, r)) =
        (coneMetric g).koszulRHS
          (coneRadialField (I := I) (N := N))
          (coneHorizontalLift X)
          (coneRadialField (I := I) (N := N)) (x, r) at hc
    rw [coneMetric_koszulRHS_radial_horizontal_radial,
      coneMetric_any_radial] at hc
    linarith

/-- **Math.** A radial derivative of a horizontal lift is also the horizontal
field scaled by `r⁻¹`. -/
theorem coneLeviCivitaConnection_cov_radial_horizontal_apply
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    ((coneLeviCivitaConnection g).cov
      (coneRadialField (I := I) (N := N)) (coneHorizontalLift X)) (x, r) =
      ((r : ℝ)⁻¹ • X x, 0) := by
  apply Prod.ext
  · apply (g.metricInner_eq_iff_eq x _ _).mp
    intro w
    obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq (I := I) x w
    rw [← hZ]
    have hc := (coneMetric g).koszulDualSection_dual
      (coneHorizontalLift X) (coneRadialField (I := I) (N := N))
      (coneHorizontalLift Z) (x, r)
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneHorizontalLift X)) (x, r))
      (coneHorizontalLift Z (x, r)) =
        (coneMetric g).koszulRHS (coneHorizontalLift X)
          (coneRadialField (I := I) (N := N))
          (coneHorizontalLift Z) (x, r) at hc
    rw [coneMetric_koszulRHS_horizontal_radial_horizontal,
      coneMetric_metricInner_prod, coneHorizontalLift_apply] at hc
    simp only [mul_zero, add_zero] at hc
    rw [g.metricInner_smul_left, ← div_eq_inv_mul]
    apply (eq_div_iff (ne_of_gt r.property)).2
    have hcancel :
        (2 * (r : ℝ)) *
            (g.metricInner x
                (((coneLeviCivitaConnection g).cov
                  (coneRadialField (I := I) (N := N))
                  (coneHorizontalLift X)) (x, r)).1
                (Z x) * (r : ℝ)) =
          (2 * (r : ℝ)) * g.metricInner x (X x) (Z x) := by
      calc
        _ = 2 * ((r : ℝ) ^ 2 *
            g.metricInner x
              (((coneLeviCivitaConnection g).cov
                (coneRadialField (I := I) (N := N))
                (coneHorizontalLift X)) (x, r)).1
              (Z x)) := by ring
        _ = _ := hc
    exact mul_left_cancel₀
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt r.property)) hcancel
  · change
      (((coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneHorizontalLift X)) (x, r)).2 = 0
    have hc := (coneMetric g).koszulDualSection_dual
      (coneHorizontalLift X) (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r)
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneHorizontalLift X)) (x, r))
      (coneRadialField (I := I) (N := N) (x, r)) =
        (coneMetric g).koszulRHS (coneHorizontalLift X)
          (coneRadialField (I := I) (N := N))
          (coneRadialField (I := I) (N := N)) (x, r) at hc
    rw [coneMetric_koszulRHS_horizontal_radial_radial,
      coneMetric_any_radial] at hc
    linarith

/-- **Math.** The unit radial field is parallel in the radial direction. -/
theorem coneLeviCivitaConnection_cov_radial_radial_apply
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (x : N) (r : ↥positiveReal) :
    ((coneLeviCivitaConnection g).cov
      (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N))) (x, r) =
      ((0 : TangentSpace I x), 0) := by
  apply Prod.ext
  · apply (g.metricInner_eq_iff_eq x _ _).mp
    intro w
    obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq (I := I) x w
    rw [← hZ]
    simp only [g.metricInner_zero_left]
    have hc := (coneMetric g).koszulDualSection_dual
      (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N))
      (coneHorizontalLift Z) (x, r)
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N))) (x, r))
      (coneHorizontalLift Z (x, r)) =
        (coneMetric g).koszulRHS
          (coneRadialField (I := I) (N := N))
          (coneRadialField (I := I) (N := N))
          (coneHorizontalLift Z) (x, r) at hc
    rw [coneMetric_koszulRHS_radial_radial_horizontal,
      coneMetric_metricInner_prod, coneHorizontalLift_apply] at hc
    simp only [mul_zero, add_zero] at hc
    have hr2 : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos r.property
    nlinarith
  · change
      (((coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N))) (x, r)).2 = 0
    have hc := (coneMetric g).koszulDualSection_dual
      (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N))
      (coneRadialField (I := I) (N := N)) (x, r)
    change 2 * (coneMetric g).metricInner (x, r)
      (((coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N))) (x, r))
      (coneRadialField (I := I) (N := N) (x, r)) =
        (coneMetric g).koszulRHS
          (coneRadialField (I := I) (N := N))
          (coneRadialField (I := I) (N := N))
          (coneRadialField (I := I) (N := N)) (x, r) at hc
    rw [coneMetric_koszulRHS_radial_radial_radial,
      coneMetric_any_radial] at hc
    linarith

/-! ### Cone connection formulas as identities of smooth fields -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
/-- **Math.** The reciprocal cone radius is smooth on the open cone. -/
theorem coneInvRadius_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : N × ↥positiveReal => (coneRadius (N := N) q)⁻¹) :=
  coneRadius_contMDiff.inv₀ fun q => ne_of_gt q.2.property

omit [FiniteDimensional ℝ E] in
/-- **Math.** The base metric pairing of two fields, pulled back to the cone,
is a smooth scalar function. -/
theorem coneBaseMetricPairing_contMDiff (g : RiemannianMetric I N)
    (X Y : SmoothVectorField I N) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : N × ↥positiveReal => g.metricInner q.1 (X q.1) (Y q.1)) :=
  (g.metricInner_field_contMDiff X Y).comp contMDiff_fst

/-- **Math.** The radial correction in `nabla_X Y` for horizontal lifts is
`-r * <X,Y> * partial_r`. -/
noncomputable def coneRadialCorrection (g : RiemannianMetric I N)
    (X Y : SmoothVectorField I N) :
    SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) :=
  SmoothVectorField.smul
    (fun q => -(coneRadius (N := N) q * g.metricInner q.1 (X q.1) (Y q.1)))
    ((coneRadius_contMDiff.mul (coneBaseMetricPairing_contMDiff g X Y)).neg)
    (coneRadialField (I := I) (N := N))

omit [FiniteDimensional ℝ E] in
@[simp] theorem coneRadialCorrection_apply (g : RiemannianMetric I N)
    (X Y : SmoothVectorField I N) (x : N) (r : ↥positiveReal) :
    coneRadialCorrection g X Y (x, r) =
      ((0 : TangentSpace I x), -((r : ℝ) * g.metricInner x (X x) (Y x))) := by
  simp only [coneRadialCorrection, SmoothVectorField.smul_apply, coneRadius,
    coneRadialField_apply]
  have hsmul (c : ℝ) (u : TangentSpace I x) (a : ℝ) :
      c • ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
        ((c • u, c • a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
    rfl
  change (-((r : ℝ) * g.metricInner x (X x) (Y x))) • ((0, 1) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
      ((0, -((r : ℝ) * g.metricInner x (X x) (Y x))) :
        TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r))
  rw [hsmul]
  have hpair {u v : E} {a b : ℝ}
      (hu : u = v) (ha : a = b) :
      ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
        ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
    subst v
    subst b
    rfl
  apply hpair
  · change (-((r : ℝ) * g.metricInner x (X x) (Y x))) • (0 : E) = (0 : E)
    exact smul_zero _
  · ring

/-- **Math.** The horizontal lift `X/r`, bundled as a smooth cone field. -/
noncomputable def coneInvRadiusHorizontal (X : SmoothVectorField I N) :
    SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) :=
  SmoothVectorField.smul
    (fun q => (coneRadius (N := N) q)⁻¹)
    coneInvRadius_contMDiff (coneHorizontalLift X)

omit [FiniteDimensional ℝ E] in
@[simp] theorem coneInvRadiusHorizontal_apply (X : SmoothVectorField I N)
    (x : N) (r : ↥positiveReal) :
    coneInvRadiusHorizontal X (x, r) = ((r : ℝ)⁻¹ • X x, 0) := by
  simp only [coneInvRadiusHorizontal, SmoothVectorField.smul_apply, coneRadius,
    coneHorizontalLift_apply]
  have hsmul (c : ℝ) (u : TangentSpace I x) (a : ℝ) :
      c • ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
        ((c • u, c • a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
    rfl
  change (r : ℝ)⁻¹ • ((X x, 0) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
      (((r : ℝ)⁻¹ • X x, 0) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r))
  rw [hsmul]
  simp

/-- **Math.** For horizontal lifts,
`nabla_(X^h) Y^h = (nabla^g_X Y)^h - r <X,Y> partial_r`, as an identity of
smooth fields. -/
theorem coneLeviCivitaConnection_cov_horizontal_horizontal
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X Y : SmoothVectorField I N) :
    (coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneHorizontalLift Y) =
      coneHorizontalLift ((leviCivitaConnectionGeneral g).cov X Y) +
        coneRadialCorrection g X Y := by
  apply SmoothVectorField.ext
  intro q
  rw [coneLeviCivitaConnection_cov_horizontal_horizontal_apply]
  rw [SmoothVectorField.add_apply, coneHorizontalLift_apply,
    coneRadialCorrection_apply]
  have hadd (u v : TangentSpace I q.1) (a b : ℝ) :
      ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) +
          ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) =
        ((u + v, a + b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) := by
    rfl
  change ((_, _) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) =
    ((_, 0) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) +
      ((0, _) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)
  rw [hadd]
  have hpair {u v : E} {a b : ℝ}
      (hu : u = v) (ha : a = b) :
      ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) =
        ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) := by
    subst v
    subst b
    rfl
  apply hpair
  · exact (add_zero _).symm
  · ring

/-- **Math.** For a horizontal lift,
`nabla_(X^h) partial_r = X^h/r`, as an identity of smooth fields. -/
theorem coneLeviCivitaConnection_cov_horizontal_radial
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N) :
    (coneLeviCivitaConnection g).cov (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N)) =
      coneInvRadiusHorizontal X := by
  apply SmoothVectorField.ext
  intro q
  rw [coneLeviCivitaConnection_cov_horizontal_radial_apply]
  exact (coneInvRadiusHorizontal_apply X q.1 q.2).symm

/-- **Math.** For a horizontal lift,
`nabla_partial_r X^h = X^h/r`, as an identity of smooth fields. -/
theorem coneLeviCivitaConnection_cov_radial_horizontal
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N) :
    (coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N)) (coneHorizontalLift X) =
      coneInvRadiusHorizontal X := by
  apply SmoothVectorField.ext
  intro q
  rw [coneLeviCivitaConnection_cov_radial_horizontal_apply]
  exact (coneInvRadiusHorizontal_apply X q.1 q.2).symm

/-- **Math.** The unit radial field is parallel in the radial direction, as an
identity of smooth fields. -/
theorem coneLeviCivitaConnection_cov_radial_radial
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) :
    (coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N)) = 0 := by
  apply SmoothVectorField.ext
  intro q
  rw [coneLeviCivitaConnection_cov_radial_radial_apply]
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Math.** The unit radial field differentiates `r⁻¹` to `-r⁻²`. -/
theorem coneRadialField_dir_invRadius (q : N × ↥positiveReal) :
    (coneRadialField (I := I) (N := N)).dir
        (fun p => (coneRadius (N := N) p)⁻¹) q =
      -((coneRadius (N := N) q)⁻¹) ^ 2 := by
  have hprod := (coneRadialField (I := I) (N := N)).dir_mul q
    (coneRadius_contMDiff.mdifferentiableAt (by simp))
    (coneInvRadius_contMDiff.mdifferentiableAt (by simp))
  have hfun :
      (fun p : N × ↥positiveReal =>
        coneRadius (N := N) p * (coneRadius (N := N) p)⁻¹) =
      fun _ => (1 : ℝ) := by
    funext p
    exact mul_inv_cancel₀ (ne_of_gt p.2.property)
  have hzero :
      (coneRadialField (I := I) (N := N)).dir
        (fun p => coneRadius (N := N) p * (coneRadius (N := N) p)⁻¹) q = 0 := by
    rw [hfun, SmoothVectorField.dir, mfderiv_const]
    rfl
  rw [hzero, coneRadialField_dir_coneRadius] at hprod
  let d := (coneRadialField (I := I) (N := N)).dir
    (fun p => (coneRadius (N := N) p)⁻¹) q
  have hprod' : (0 : ℝ) = (q.2 : ℝ) * d + (q.2 : ℝ)⁻¹ := by
    dsimp only [d]
    simpa only [coneRadius, mul_one] using hprod
  have hr0 : (q.2 : ℝ) ≠ 0 := ne_of_gt (positiveReal_mem q.2)
  have hmul : (q.2 : ℝ) * d = -(q.2 : ℝ)⁻¹ := by
    linarith
  change d = -((q.2 : ℝ)⁻¹) ^ 2
  calc
    d = (q.2 : ℝ)⁻¹ * ((q.2 : ℝ) * d) := by
          rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
    _ = (q.2 : ℝ)⁻¹ * (-(q.2 : ℝ)⁻¹) := by rw [hmul]
    _ = -((q.2 : ℝ)⁻¹) ^ 2 := by ring

/-- **Math.** Radially differentiating the horizontal field `X/r` gives zero:
the derivative of `r⁻¹` cancels `nabla_partial_r X^h = X^h/r`. -/
theorem coneLeviCivitaConnection_cov_radial_invRadiusHorizontal
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N) :
    (coneLeviCivitaConnection g).cov
        (coneRadialField (I := I) (N := N))
        (coneInvRadiusHorizontal X) = 0 := by
  rw [coneInvRadiusHorizontal,
    (coneLeviCivitaConnection g).cov_smul_right coneInvRadius_contMDiff,
    coneLeviCivitaConnection_cov_radial_horizontal]
  apply SmoothVectorField.ext
  intro q
  rcases q with ⟨x, r⟩
  simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply,
    coneRadialField_dir_invRadius, SmoothVectorField.zero_apply]
  rw [coneInvRadiusHorizontal_apply, coneHorizontalLift_apply]
  simp only [coneRadius]
  have hsmul (c : ℝ) (u : TangentSpace I x) (a : ℝ) :
      c • ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
        ((c • u, c • a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
    rfl
  have hadd (u v : TangentSpace I x) (a b : ℝ) :
      ((u, a) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
          ((v, b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
        ((u + v, a + b) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) := by
    rfl
  change (r : ℝ)⁻¹ • (((r : ℝ)⁻¹ • X x, 0) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) +
      (-((r : ℝ)⁻¹) ^ 2) • ((X x, 0) :
        TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r)) =
    (0 : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, r))
  rw [hsmul, hsmul, hadd]
  simp only [smul_zero, add_zero]
  change _ = ((0 : TangentSpace I x), (0 : ℝ))
  apply Prod.ext
  · change (r : ℝ)⁻¹ • ((r : ℝ)⁻¹ • X x) +
      (-((r : ℝ)⁻¹) ^ 2) • X x = 0
    rw [smul_smul]
    module
  · simp

/-- **Math.** Every radial two-plane in the open cone has zero curvature:
`R(X^h, partial_r) partial_r = 0`. -/
theorem coneCurvature_horizontal_radial_radial
    [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]
    (g : RiemannianMetric I N) (X : SmoothVectorField I N) :
    (coneLeviCivitaConnection g).curvature (coneHorizontalLift X)
        (coneRadialField (I := I) (N := N))
        (coneRadialField (I := I) (N := N)) = 0 := by
  apply SmoothVectorField.ext
  intro q
  rw [(coneLeviCivitaConnection g).curvature_apply,
    coneLeviCivitaConnection_cov_horizontal_radial,
    coneLeviCivitaConnection_cov_radial_invRadiusHorizontal,
    coneLeviCivitaConnection_cov_radial_radial,
    (coneLeviCivitaConnection g).cov_zero_right,
    bracketField_coneHorizontalLift_coneRadialField,
    (coneLeviCivitaConnection g).cov_zero_left]
  simp

end Cone

/-! ## The exterior-square splitting of a cone tangent space -/

section ConeWedge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** The mixed component of `(x,a) ∧ (y,b)`, namely `b x - a y`. -/
def coneMixedAlternating : (V × ℝ) [⋀^Fin 2]→ₗ[ℝ] V where
  toFun x := (x 1).2 • (x 0).1 - (x 0).2 • (x 1).1
  map_update_add' := by intro _ v i x y; fin_cases i <;> simp <;> module
  map_update_smul' := by intro _ v i c x; fin_cases i <;> simp <;> module
  map_eq_zero_of_eq' := by
    intro x i j hij hne
    have h01 : x 0 = x 1 := by
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hne | exact hij | exact hij.symm
    rw [h01]
    module

/-- **Math.** The `V`-valued mixed projection on `Λ²(V × ℝ)`. -/
def coneWedgeMixedPart : ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] V :=
  alternatingMapLinearEquiv coneMixedAlternating

@[simp] theorem coneWedgeMixedPart_iMulti (x y : V × ℝ) :
    coneWedgeMixedPart (ιMulti ℝ 2 ![x, y]) = y.2 • x.1 - x.2 • y.1 := by
  rw [coneWedgeMixedPart, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- **Math.** The forward map in
`Λ²(V ⊕ ℝ∂r) ≃ Λ²V ⊕ (V ∧ ∂r)`: project to the horizontal
exterior square and record the mixed coefficient. -/
def coneWedgeSplit : ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] (⋀[ℝ]^2 V) × V :=
  (exteriorPower.map 2 (LinearMap.fst ℝ V ℝ)).prod coneWedgeMixedPart

@[simp] theorem coneWedgeSplit_iMulti (x y : V × ℝ) :
    coneWedgeSplit (ιMulti ℝ 2 ![x, y]) =
      (ιMulti ℝ 2 ![x.1, y.1], y.2 • x.1 - x.2 • y.1) := by
  apply Prod.ext
  · simp only [coneWedgeSplit, LinearMap.prod_apply, Function.prod_apply,
      exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  · simp [coneWedgeSplit]

private def coneWedgeWithRadial : (V × ℝ) →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) :=
  (ιMulti ℝ 2).toMultilinearMap.toLinearMap
    ![((0 : V), (0 : ℝ)), ((0 : V), (1 : ℝ))] 0

/-- **Math.** The mixed inclusion `u ↦ (u,0) ∧ (0,1)`. -/
def coneWedgeMixed : V →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) :=
  coneWedgeWithRadial.comp (LinearMap.inl ℝ V ℝ)

@[simp] theorem coneWedgeMixed_apply (u : V) :
    coneWedgeMixed u =
      ιMulti ℝ 2 ![(u, (0 : ℝ)), ((0 : V), (1 : ℝ))] := by
  simp only [coneWedgeMixed, LinearMap.comp_apply, LinearMap.inl_apply,
    coneWedgeWithRadial, MultilinearMap.toLinearMap_apply]
  have h : Function.update
      ![((0 : V), (0 : ℝ)), ((0 : V), (1 : ℝ))] 0 (u, 0) =
        ![(u, (0 : ℝ)), ((0 : V), (1 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  rfl

/-- **Math.** The inverse map sends `(phi,u)` to the horizontal image of `phi` plus
`u ∧ ∂r`. -/
def coneWedgeUnsplit : (⋀[ℝ]^2 V) × V →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) :=
  (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)).comp
      (LinearMap.fst ℝ (⋀[ℝ]^2 V) V) +
    coneWedgeMixed.comp (LinearMap.snd ℝ (⋀[ℝ]^2 V) V)

@[simp] theorem coneWedgeUnsplit_apply (φ : ⋀[ℝ]^2 V) (u : V) :
    coneWedgeUnsplit (φ, u) =
      exteriorPower.map 2 (LinearMap.inl ℝ V ℝ) φ + coneWedgeMixed u := by
  simp [coneWedgeUnsplit]

private lemma exteriorAlgebra_iMulti_two (A B : V × ℝ) :
    ExteriorAlgebra.ιMulti ℝ 2 ![A, B] =
      ExteriorAlgebra.ι ℝ A * ExteriorAlgebra.ι ℝ B := by
  simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

private lemma exteriorPair_expand (X Y R : V × ℝ) (a b : ℝ) :
    ExteriorAlgebra.ιMulti ℝ 2 ![X + a • R, Y + b • R] =
      ExteriorAlgebra.ιMulti ℝ 2 ![X, Y] +
        ExteriorAlgebra.ιMulti ℝ 2 ![b • X - a • Y, R] := by
  simp_rw [exteriorAlgebra_iMulti_two]
  simp only [map_add, map_smul, map_sub, add_mul, mul_add, sub_mul,
    smul_mul_assoc, mul_smul_comm]
  have hswap : ExteriorAlgebra.ι ℝ R * ExteriorAlgebra.ι ℝ Y =
      -(ExteriorAlgebra.ι ℝ Y * ExteriorAlgebra.ι ℝ R) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap R Y)
  have hsq : ExteriorAlgebra.ι ℝ R * ExteriorAlgebra.ι ℝ R = 0 :=
    ExteriorAlgebra.ι_sq_zero R
  rw [hswap, hsq]
  simp
  module

/-- **Math.** Every decomposable cone bivector is the sum of its horizontal and mixed
parts. -/
theorem coneWedge_iMulti_decomp (x y : V × ℝ) :
    ιMulti ℝ 2 ![x, y] =
      exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)
          (ιMulti ℝ 2 ![x.1, y.1]) +
        coneWedgeMixed (y.2 • x.1 - x.2 • y.1) := by
  rw [exteriorPower.map_apply_ιMulti]
  have hc : (LinearMap.inl ℝ V ℝ) ∘ ![x.1, y.1] =
      ![(x.1, (0 : ℝ)), (y.1, (0 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rw [hc, coneWedgeMixed_apply]
  let R : V × ℝ := ((0 : V), (1 : ℝ))
  let X : V × ℝ := (x.1, (0 : ℝ))
  let Y : V × ℝ := (y.1, (0 : ℝ))
  have hx : x = X + x.2 • R := by ext <;> simp [X, R]
  have hy : y = Y + y.2 • R := by ext <;> simp [Y, R]
  have hvec : ![x, y] = ![X + x.2 • R, Y + y.2 • R] := by
    funext i
    fin_cases i
    · exact hx
    · exact hy
  have hm : ((y.2 • x.1 - x.2 • y.1, (0 : ℝ)) : V × ℝ) =
      y.2 • X - x.2 • Y := by
    ext <;> simp [X, Y]
  rw [hvec, hm]
  apply Subtype.ext
  simpa only [exteriorPower.ιMulti_apply_coe, Submodule.coe_add] using
    (exteriorPair_expand X Y R x.2 y.2)

private theorem map_fst_inl :
    (exteriorPower.map 2 (LinearMap.fst ℝ V ℝ)).comp
        (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)) =
      LinearMap.id := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, LinearMap.id_apply]
  congr 1

private theorem mixedPart_map_inl :
    (coneWedgeMixedPart (V := V)).comp
        (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)) = 0 := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, LinearMap.zero_apply]
  have hc : (LinearMap.inl ℝ V ℝ) ∘ ![v 0, v 1] =
      ![((v 0), (0 : ℝ)), ((v 1), (0 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rw [hc, coneWedgeMixedPart_iMulti]
  simp

@[simp] theorem coneWedgeSplit_horizontal (φ : ⋀[ℝ]^2 V) :
    coneWedgeSplit
        (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ) φ) = (φ, 0) := by
  apply Prod.ext
  · change ((exteriorPower.map 2 (LinearMap.fst ℝ V ℝ)).comp
      (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ))) φ = φ
    rw [map_fst_inl]
    rfl
  · change ((coneWedgeMixedPart (V := V)).comp
      (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ))) φ = 0
    rw [mixedPart_map_inl]
    rfl

@[simp] theorem map_fst_coneWedgeMixed (u : V) :
    exteriorPower.map 2 (LinearMap.fst ℝ V ℝ) (coneWedgeMixed u) = 0 := by
  rw [coneWedgeMixed_apply, exteriorPower.map_apply_ιMulti]
  have h : (LinearMap.fst ℝ V ℝ) ∘
      ![(u, (0 : ℝ)), ((0 : V), (1 : ℝ))] = ![u, (0 : V)] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact (ιMulti ℝ 2).map_coord_zero 1 rfl

@[simp] theorem coneWedgeMixedPart_mixed (u : V) :
    coneWedgeMixedPart (coneWedgeMixed u) = u := by
  rw [coneWedgeMixed_apply, coneWedgeMixedPart_iMulti]
  simp

@[simp] theorem coneWedgeSplit_mixed (u : V) :
    coneWedgeSplit (coneWedgeMixed u) = (0, u) := by
  apply Prod.ext
  · exact map_fst_coneWedgeMixed u
  · exact coneWedgeMixedPart_mixed u

theorem coneWedgeUnsplit_split :
    (coneWedgeUnsplit (V := V)).comp (coneWedgeSplit (V := V)) =
      LinearMap.id := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    coneWedgeSplit_iMulti, coneWedgeUnsplit_apply, LinearMap.id_apply]
  exact congrArg Subtype.val (coneWedge_iMulti_decomp (v 0) (v 1)).symm

theorem coneWedgeSplit_unsplit :
    (coneWedgeSplit (V := V)).comp (coneWedgeUnsplit (V := V)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨φ, u⟩
  simp only [LinearMap.comp_apply, coneWedgeUnsplit_apply, map_add,
    coneWedgeSplit_horizontal, coneWedgeSplit_mixed, LinearMap.id_apply]
  ext <;> simp

/-- **Math.** The canonical cone splitting
`Λ²(V ⊕ ℝ∂r) ≃ₗ Λ²V ⊕ (V ∧ ∂r)`. -/
def coneWedgeEquiv : ⋀[ℝ]^2 (V × ℝ) ≃ₗ[ℝ] (⋀[ℝ]^2 V) × V where
  toLinearMap := coneWedgeSplit
  invFun := coneWedgeUnsplit
  left_inv φ := by
    have h := LinearMap.congr_fun (coneWedgeUnsplit_split (V := V)) φ
    simpa using h
  right_inv z := by
    have h := LinearMap.congr_fun (coneWedgeSplit_unsplit (V := V)) z
    simpa using h

@[simp] theorem coneWedgeEquiv_apply (φ : ⋀[ℝ]^2 (V × ℝ)) :
    coneWedgeEquiv φ = coneWedgeSplit φ :=
  rfl

@[simp] theorem coneWedgeEquiv_symm_apply (z : (⋀[ℝ]^2 V) × V) :
    (coneWedgeEquiv (V := V)).symm z = coneWedgeUnsplit z :=
  rfl

/-! ### Block forms in the cone splitting -/

/-- **Math.** The block bilinear form `diag(s² A, 0)` on
`Λ²(V × ℝ) ≃ Λ²V × V`. -/
def coneWedgeBlockForm (s : ℝ)
    (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ) :
    ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun φ ψ => s ^ 2 * A (coneWedgeSplit φ).1 (coneWedgeSplit ψ).1)
    (by intro φ₁ φ₂ ψ; simp; ring)
    (by intro c φ ψ; simp; ring)
    (by intro φ ψ₁ ψ₂; simp; ring)
    (by intro c φ ψ; simp; ring)

@[simp] theorem coneWedgeBlockForm_apply (s : ℝ)
    (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ ψ : ⋀[ℝ]^2 (V × ℝ)) :
    coneWedgeBlockForm s A φ ψ =
      s ^ 2 * A (coneWedgeSplit φ).1 (coneWedgeSplit ψ).1 :=
  rfl

/-- **Math.** In split coordinates, `coneWedgeBlockForm s A` is literally
the matrix `diag(s² A, 0)`. -/
@[simp] theorem coneWedgeBlockForm_equiv (s : ℝ)
    (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ ψ : ⋀[ℝ]^2 V) (u v : V) :
    coneWedgeBlockForm s A
        ((coneWedgeEquiv (V := V)).symm (φ, u))
        ((coneWedgeEquiv (V := V)).symm (ψ, v)) = s ^ 2 * A φ ψ := by
  rw [coneWedgeBlockForm_apply, coneWedgeEquiv_symm_apply,
    coneWedgeEquiv_symm_apply]
  have hφ : coneWedgeSplit (coneWedgeUnsplit (φ, u)) = (φ, u) := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (coneWedgeSplit_unsplit (V := V)) (φ, u)
  have hψ : coneWedgeSplit (coneWedgeUnsplit (ψ, v)) = (ψ, v) := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (coneWedgeSplit_unsplit (V := V)) (ψ, v)
  rw [hφ, hψ]

end ConeWedge

end MorganTianLib
