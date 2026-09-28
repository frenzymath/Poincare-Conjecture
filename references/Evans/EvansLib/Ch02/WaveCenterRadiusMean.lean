import EvansLib.Ch02.WaveSphericalMeanAnalytic

/-!
# Joint center-radius regularity of spherical averages

For spatial data `f`, this file treats its normalized spherical average as a
single function of the center and radius.  Compact-parameter differentiation
gives finite `C^k` regularity and commutes every available center-radius
derivative with the sphere integral.  This is the mixed-derivative input for
the odd-dimensional wave formula.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- A sphere fibre with both its center and radius left as parameters. -/
def centerRadiusSphereIntegrand
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (omega : EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  f (p.1 + p.2 • omega)

/-- Linear center-radius substitution `(x,r) ↦ x + r omega`. -/
def centerRadiusParamLinear (omega : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
    (((ContinuousLinearMap.lsmul ℝ ℝ).flip omega).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ))

@[simp] lemma centerRadiusParamLinear_apply
    (omega : EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    centerRadiusParamLinear omega p = p.1 + p.2 • omega := rfl

/-- Finite-order chain rule for a center-radius sphere fibre. -/
theorem iteratedFDeriv_centerRadiusSphereIntegrand_of_order
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) (omega : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ k)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    iteratedFDeriv ℝ m (centerRadiusSphereIntegrand f omega) p =
      (iteratedFDeriv ℝ m f (p.1 + p.2 • omega)).compContinuousLinearMap
        (fun _ : Fin m => centerRadiusParamLinear omega) := by
  have hfun : centerRadiusSphereIntegrand f omega =
      f ∘ centerRadiusParamLinear omega := by
    funext q
    rfl
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right
    (centerRadiusParamLinear omega) hf p (by exact_mod_cast hm)]
  simp

private def centerRadiusSphereJoint
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (q : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × ℝ)) : ℝ :=
  centerRadiusSphereIntegrand f q.1 q.2

private lemma centerRadiusSphereJoint_contDiff_of_order
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (centerRadiusSphereJoint f) := by
  change ContDiff ℝ k (fun q : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × ℝ) =>
    f (q.2.1 + q.2.2 • q.1))
  exact hf.comp (by fun_prop)

private lemma centerRadiusSphereIntegrand_contDiff_of_order
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f)
    (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ContDiff ℝ k (centerRadiusSphereIntegrand f omega) := by
  change ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
    f (p.1 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
  exact hf.comp (by fun_prop)

private lemma continuous_centerRadiusSphereIntegrand_iteratedFDeriv_of_order
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) (m : ℕ) (hm : m ≤ k) :
    Continuous (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×
      (EuclideanSpace ℝ (Fin n) × ℝ) =>
      iteratedFDeriv ℝ m
        (centerRadiusSphereIntegrand f
          (q.1 : EuclideanSpace ℝ (Fin n))) q.2) := by
  have hpartial := continuous_iteratedFDeriv_partial_of_order
    (centerRadiusSphereJoint_contDiff_of_order hf) m hm
  convert hpartial.comp (continuous_subtype_val.prodMap
    (continuous_id : Continuous
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p))) using 1
  funext q
  rfl

/-- A finite-order smooth spatial function has a jointly smooth unnormalized
spherical profile in its center and radius. -/
theorem unitSphereRadialIntegralAt_joint_contDiff_of_order
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      unitSphereRadialIntegralAt f p.1 p.2) := by
  simpa [unitSphereRadialIntegralAt, centerRadiusSphereIntegrand] using
    (contDiff_parametricIntegral_of_order k
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
      (fun omega => centerRadiusSphereIntegrand_contDiff_of_order hf omega)
      (fun m hm =>
        continuous_centerRadiusSphereIntegrand_iteratedFDeriv_of_order hf m hm))

/-- A finite-order smooth spatial function has a jointly smooth normalized
spherical profile in its center and radius. -/
theorem unitSphereRadialAverageAt_joint_contDiff_of_order
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      unitSphereRadialAverageAt f p.1 p.2) := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹
  have heq : (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      unitSphereRadialAverageAt f p.1 p.2) =
      c • (fun p => unitSphereRadialIntegralAt f p.1 p.2) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, c, unitSphereRadialAverageAt_eq]
  rw [heq]
  exact (unitSphereRadialIntegralAt_joint_contDiff_of_order hf).const_smul c

/-- Every finite center-radius derivative of the unnormalized spherical
profile commutes with the sphere integral. -/
theorem iteratedFDeriv_unitSphereRadialIntegralAt_joint_of_order
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) (m : ℕ) (hm : m ≤ k)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    iteratedFDeriv ℝ m
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
          unitSphereRadialIntegralAt f q.1 q.2) p =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ m
          (centerRadiusSphereIntegrand f
            (omega : EuclideanSpace ℝ (Fin n))) p
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hseries := hasFTaylorSeriesUpTo_parametricIntegral_of_order k
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
    (fun omega => centerRadiusSphereIntegrand_contDiff_of_order hf omega)
    (fun i hi =>
      continuous_centerRadiusSphereIntegrand_iteratedFDeriv_of_order hf i hi)
  have hEq := hseries.eq_iteratedFDeriv (m := m) (by exact_mod_cast hm) p
  simpa [unitSphereRadialIntegralAt, centerRadiusSphereIntegrand,
    parametricIntegralSeries] using hEq.symm

private theorem iteratedFDeriv_unitSphereRadialAverageAt_joint_of_order
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) (m : ℕ) (hm : m ≤ k)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    iteratedFDeriv ℝ m
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
          unitSphereRadialAverageAt f q.1 q.2) p =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹ •
        ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          iteratedFDeriv ℝ m
            (centerRadiusSphereIntegrand f
              (omega : EuclideanSpace ℝ (Fin n))) p
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹
  have heq : (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
      unitSphereRadialAverageAt f q.1 q.2) =
      c • (fun q => unitSphereRadialIntegralAt f q.1 q.2) := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, c, unitSphereRadialAverageAt_eq]
  rw [heq]
  change iteratedFDeriv ℝ m
      (fun q => c • unitSphereRadialIntegralAt f q.1 q.2) p = _
  calc
    _ = c • iteratedFDeriv ℝ m
        (fun q => unitSphereRadialIntegralAt f q.1 q.2) p := by
      exact iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (R := ℝ) (a := c)
        ((unitSphereRadialIntegralAt_joint_contDiff_of_order hf).of_le
          (by exact_mod_cast hm)).contDiffAt
    _ = _ := by
      rw [iteratedFDeriv_unitSphereRadialIntegralAt_joint_of_order hf m hm p]

/-- Evaluated finite center-radius derivatives of the normalized spherical
average are normalized integrals of the corresponding derivatives of `f`. -/
theorem iteratedFDeriv_unitSphereRadialAverageAt_joint_apply_of_order
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) (m : ℕ) (hm : m ≤ k)
    (p : EuclideanSpace ℝ (Fin n) × ℝ)
    (v : Fin m → EuclideanSpace ℝ (Fin n) × ℝ) :
    iteratedFDeriv ℝ m
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
          unitSphereRadialAverageAt f q.1 q.2) p v =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹ *
        ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          iteratedFDeriv ℝ m f
            (p.1 + p.2 • (omega : EuclideanSpace ℝ (Fin n)))
            (fun i => centerRadiusParamLinear
              (omega : EuclideanSpace ℝ (Fin n)) (v i))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  rw [iteratedFDeriv_unitSphereRadialAverageAt_joint_of_order hf m hm p]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousMultilinearMap.integral_apply]
  · apply congrArg
    apply integral_congr_ae
    filter_upwards [] with omega
    rw [iteratedFDeriv_centerRadiusSphereIntegrand_of_order hf
      (omega : EuclideanSpace ℝ (Fin n)) m hm p]
    rfl
  · exact integrable_iteratedFDeriv_apply
      (continuous_centerRadiusSphereIntegrand_iteratedFDeriv_of_order hf m hm) p

/-- Center derivatives at a fixed radius commute with the normalized sphere
integral. -/
theorem iteratedFDeriv_unitSphereRadialAverageAt_center_apply_of_order
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) (m : ℕ) (hm : m ≤ k)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (v : Fin m → EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ m
        (fun y => unitSphereRadialAverageAt f y r) x v =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹ *
        ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          iteratedFDeriv ℝ m f
            (x + r • (omega : EuclideanSpace ℝ (Fin n))) v
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  let J : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun p =>
    unitSphereRadialAverageAt f p.1 p.2
  let a : EuclideanSpace ℝ (Fin n) × ℝ := (0, r)
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × ℝ) :=
    ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ
  have hJ : ContDiff ℝ k J :=
    unitSphereRadialAverageAt_joint_contDiff_of_order hf
  have hfun : (fun y => unitSphereRadialAverageAt f y r) =
      (fun z => J (a + z)) ∘ L := by
    funext y
    simp [J, a, L]
  have htrans : ContDiff ℝ k (fun z => J (a + z)) :=
    hJ.comp (by fun_prop)
  have hslice : iteratedFDeriv ℝ m
        (fun y => unitSphereRadialAverageAt f y r) x =
      (iteratedFDeriv ℝ m J (x, r)).compContinuousLinearMap
        (fun _ : Fin m => L) := by
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L htrans x
      (by exact_mod_cast hm)]
    rw [iteratedFDeriv_comp_add_left]
    simp [a, L]
  have hsliceApply := congrArg
    (fun T => T v) hslice
  have hjoint := iteratedFDeriv_unitSphereRadialAverageAt_joint_apply_of_order
    hf m hm (x, r) (fun i => (v i, (0 : ℝ)))
  calc
    iteratedFDeriv ℝ m
        (fun y => unitSphereRadialAverageAt f y r) x v =
        iteratedFDeriv ℝ m J (x, r)
          (fun i => (v i, (0 : ℝ))) := by
      simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, L]
        using hsliceApply
    _ = _ := by
      simpa [J] using hjoint

/-- The spatial Laplacian commutes with a normalized spherical average. -/
theorem laplacian_unitSphereRadialAverageAt
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 2 f)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Δ (fun y => unitSphereRadialAverageAt f y r) x =
      unitSphereRadialAverageAt (Δ f) x r := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  calc
    (∑ i,
      iteratedFDeriv ℝ 2 (fun y => unitSphereRadialAverageAt f y r) x
        ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
          (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]) =
        ∑ i, c * ∫ omega : sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1,
          iteratedFDeriv ℝ 2 f
            (x + r • (omega : EuclideanSpace ℝ (Fin n)))
            ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
              (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact iteratedFDeriv_unitSphereRadialAverageAt_center_apply_of_order
        hf 2 le_rfl x r _
    _ = c * ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∑ i, iteratedFDeriv ℝ 2 f
          (x + r • (omega : EuclideanSpace ℝ (Fin n)))
          ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
            (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [integral_finsetSum]
      intro i hi
      have hD := hf.continuous_iteratedFDeriv (m := 2) (by norm_num)
      have hc : Continuous (fun omega : sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        iteratedFDeriv ℝ 2 f
          (x + r • (omega : EuclideanSpace ℝ (Fin n)))
          ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
            (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]) := by
        fun_prop
      exact hc.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    _ = c * ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        Δ f (x + r • (omega : EuclideanSpace ℝ (Fin n)))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with omega
      rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    _ = unitSphereRadialAverageAt (Δ f) x r := by
      rw [unitSphereRadialAverageAt_eq]
      rfl

end EvansLib
