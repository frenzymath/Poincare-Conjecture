import EvansLib.Ch02.ParametricIntegral
import EvansLib.Ch02.LaplaceMeanValueFormula

/-!
# Smooth spherical means for the wave equation

For a smooth space-time field `u(y,t)`, this file studies its unit-sphere
average after the affine substitution `y = x + r omega`.  Compact-parameter
differentiation proves smoothness in `(r,t)` and identifies every iterated
derivative with the integral of the corresponding fibrewise derivative.

The remaining geometric input for the Euler--Poisson--Darboux equation is the
radial-Laplacian identity for this average.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff Pointwise
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The nonnegative-time domain for a space-time field. -/
def waveSpaceTimeHalfSpace (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  Set.univ ×ˢ Set.Ici 0

/-- The nonnegative-time domain for the radius-time parameters. -/
def waveParameterHalfSpace : Set (ℝ × ℝ) :=
  Set.univ ×ˢ Set.Ici 0

/-- The fibre of a spherical mean, parametrized by radius and time. -/
def waveSphereIntegrand
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (x omega : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  u (x + p.1 • omega, p.2)

/-- Linear part of the affine substitution `(r,t) ↦ (x + r omega,t)`. -/
def waveSphereParamLinear (omega : EuclideanSpace ℝ (Fin n)) :
    (ℝ × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (((ContinuousLinearMap.lsmul ℝ ℝ).flip omega).comp
    (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] lemma waveSphereParamLinear_apply
    (omega : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) :
    waveSphereParamLinear omega p = (p.1 • omega, p.2) := rfl

private lemma waveSpaceTimeHalfSpace_uniqueDiffOn :
    UniqueDiffOn ℝ (waveSpaceTimeHalfSpace n) := by
  dsimp [waveSpaceTimeHalfSpace]
  exact uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)

private lemma waveParameterHalfSpace_uniqueDiffOn :
    UniqueDiffOn ℝ waveParameterHalfSpace := by
  dsimp [waveParameterHalfSpace]
  exact uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)

private lemma waveSpaceTimeHalfSpace_vadd_center
    (x : EuclideanSpace ℝ (Fin n)) :
    (x, (0 : ℝ)) +ᵥ waveSpaceTimeHalfSpace n =
      waveSpaceTimeHalfSpace n := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨mem_univ _, by simpa using hy.2⟩
  · intro hz
    refine ⟨(z.1 - x, z.2), ?_, ?_⟩
    · exact ⟨mem_univ _, by simpa using hz.2⟩
    · simp [vadd_eq_add]

private lemma waveSphereParamLinear_preimage_halfSpace
    (omega : EuclideanSpace ℝ (Fin n)) :
    (waveSphereParamLinear omega :
        (ℝ × ℝ) → (EuclideanSpace ℝ (Fin n) × ℝ)) ⁻¹'
      waveSpaceTimeHalfSpace n = waveParameterHalfSpace := by
  ext p
  simp [waveSpaceTimeHalfSpace, waveParameterHalfSpace,
    waveSphereParamLinear]

/-- A sphere fibre has the available finite regularity on the nonnegative-time
parameter half-space whenever the field has it on the space-time half-space. -/
theorem waveSphereIntegrand_contDiffOn_of_order
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiffOn ℝ k u (waveSpaceTimeHalfSpace n))
    (x omega : EuclideanSpace ℝ (Fin n)) :
    ContDiffOn ℝ k (waveSphereIntegrand u x omega)
      waveParameterHalfSpace := by
  let f : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin n) × ℝ) :=
    fun p => (x + p.1 • omega, p.2)
  have hf : ContDiff ℝ k f := by
    fun_prop
  have hmap : MapsTo f waveParameterHalfSpace
      (waveSpaceTimeHalfSpace n) := by
    intro p hp
    exact ⟨mem_univ _, hp.2⟩
  have hcomp := hu.comp hf.contDiffOn hmap
  change ContDiffOn ℝ k (u ∘ f) waveParameterHalfSpace
  exact hcomp

/-- Finite-order chain rule for a sphere fibre on the nonnegative-time
half-space, including points on the initial-time boundary. -/
theorem iteratedFDerivWithin_waveSphereIntegrand_of_order
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiffOn ℝ k u (waveSpaceTimeHalfSpace n))
    (x omega : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ k) (p : ℝ × ℝ)
    (hp : p ∈ waveParameterHalfSpace) :
    iteratedFDerivWithin ℝ m (waveSphereIntegrand u x omega)
        waveParameterHalfSpace p =
      (iteratedFDerivWithin ℝ m u (waveSpaceTimeHalfSpace n)
        (x + p.1 • omega, p.2)).compContinuousLinearMap
        (fun _ : Fin m => waveSphereParamLinear omega) := by
  let a : EuclideanSpace ℝ (Fin n) × ℝ := (x, 0)
  let L : (ℝ × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
    waveSphereParamLinear omega
  let f : (EuclideanSpace ℝ (Fin n) × ℝ) → ℝ :=
    fun z => u (a + z)
  have hfa : ContDiffOn ℝ k f (waveSpaceTimeHalfSpace n) := by
    have ha : ContDiff ℝ k
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ => a + z) := by
      fun_prop
    have hmap : MapsTo
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ => a + z)
        (waveSpaceTimeHalfSpace n) (waveSpaceTimeHalfSpace n) := by
      intro z hz
      exact ⟨mem_univ _, by simpa [a] using hz.2⟩
    exact hu.comp ha.contDiffOn hmap
  have hpre :
      (L : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin n) × ℝ)) ⁻¹'
        waveSpaceTimeHalfSpace n = waveParameterHalfSpace :=
    waveSphereParamLinear_preimage_halfSpace omega
  have hpreUnique : UniqueDiffOn ℝ
      ((L : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin n) × ℝ)) ⁻¹'
        waveSpaceTimeHalfSpace n) := by
    rw [hpre]
    exact waveParameterHalfSpace_uniqueDiffOn
  have hpL : L p ∈ waveSpaceTimeHalfSpace n := by
    change p ∈ (L : (ℝ × ℝ) →
      (EuclideanSpace ℝ (Fin n) × ℝ)) ⁻¹' waveSpaceTimeHalfSpace n
    rw [hpre]
    exact hp
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hfa
    waveSpaceTimeHalfSpace_uniqueDiffOn hpreUnique hpL
    (i := m) (by exact_mod_cast hm)
  have htrans := iteratedFDerivWithin_comp_add_left
    (𝕜 := ℝ) (f := u) (s := waveSpaceTimeHalfSpace n) m a (L p)
  rw [show waveSphereIntegrand u x omega = f ∘ L by
    funext q
    simp [waveSphereIntegrand, f, L, a, waveSphereParamLinear]]
  rw [hpre] at hcomp
  rw [hcomp, htrans]
  change (iteratedFDerivWithin ℝ m u
      ((x, (0 : ℝ)) +ᵥ waveSpaceTimeHalfSpace n) (a + L p)
    ).compContinuousLinearMap (fun _ : Fin m => L) = _
  rw [waveSpaceTimeHalfSpace_vadd_center]
  simp [a, L, waveSphereParamLinear]

/-- Chain rule for every iterated derivative of a sphere fibre. -/
theorem iteratedFDeriv_waveSphereIntegrand
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x omega : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ m (waveSphereIntegrand u x omega) p =
      (iteratedFDeriv ℝ m u (x + p.1 • omega, p.2)).compContinuousLinearMap
        (fun _ : Fin m => waveSphereParamLinear omega) := by
  let a : EuclideanSpace ℝ (Fin n) × ℝ := (x, 0)
  have hfun : waveSphereIntegrand u x omega =
      (fun z => u (a + z)) ∘ waveSphereParamLinear omega := by
    funext q
    simp [waveSphereIntegrand, waveSphereParamLinear, a, Function.comp_apply]
  have htrans : ContDiff ℝ ∞ (fun z => u (a + z)) :=
    hu.comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right
    (waveSphereParamLinear omega) htrans p (by exact_mod_cast le_top)]
  rw [iteratedFDeriv_comp_add_left]
  simp [a, waveSphereParamLinear]

/-- Finite-order form of the chain rule for a sphere fibre. -/
theorem iteratedFDeriv_waveSphereIntegrand_of_order
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x omega : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ k) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ m (waveSphereIntegrand u x omega) p =
      (iteratedFDeriv ℝ m u (x + p.1 • omega, p.2)).compContinuousLinearMap
        (fun _ : Fin m => waveSphereParamLinear omega) := by
  let a : EuclideanSpace ℝ (Fin n) × ℝ := (x, 0)
  have hfun : waveSphereIntegrand u x omega =
      (fun z => u (a + z)) ∘ waveSphereParamLinear omega := by
    funext q
    simp [waveSphereIntegrand, waveSphereParamLinear, a, Function.comp_apply]
  have htrans : ContDiff ℝ k (fun z => u (a + z)) :=
    hu.comp (by fun_prop)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right
    (waveSphereParamLinear omega) htrans p (by exact_mod_cast hm)]
  rw [iteratedFDeriv_comp_add_left]
  simp [a, waveSphereParamLinear]

/-- The second fibre derivative in the `(r,t)` time direction is the ambient
second time derivative of `u`. -/
theorem iteratedFDeriv_waveSphereIntegrand_time_two
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x omega : EuclideanSpace ℝ (Fin n))
    (p : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (waveSphereIntegrand u x omega) p
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] =
      iteratedFDeriv ℝ 2 u (x + p.1 • omega, p.2)
        ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
          ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] := by
  rw [iteratedFDeriv_waveSphereIntegrand hu x omega 2 p]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp [waveSphereParamLinear]

/-- The unit-sphere form of Evans's spherical mean.  The fixed parameter is
`p = (r,t)`; integrating on the unit sphere differs from the normalized mean
on `sphere x r` only by the standard constant normalization. -/
def waveSphericalMean [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    waveSphereIntegrand u x
      (omega : EuclideanSpace ℝ (Fin n)) p
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- Evans's normalized spherical average of a space-time field. -/
def waveSphericalAverage [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  unitSphereRadialAverageAt (fun y => u (y, p.2)) x p.1

/-- The normalized spherical average is the unnormalized spherical integral
divided by the total surface mass. -/
lemma waveSphericalAverage_eq [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) :
    waveSphericalAverage u x p =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹ *
        waveSphericalMean u x p := by
  rw [waveSphericalAverage, unitSphereRadialAverageAt_eq]
  rfl

/-- At radius zero, the normalized spherical average recovers the field at
its center. -/
@[simp] lemma waveSphericalAverage_zero [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    waveSphericalAverage u x (0, t) = u (x, t) := by
  rw [waveSphericalAverage]
  exact unitSphereRadialAverageAt_zero (fun y => u (y, t)) x

/-- The space-time mean is the existing arbitrary-center radial integral of
the time slice. -/
lemma waveSphericalMean_eq_unitSphereRadialIntegralAt [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r t : ℝ) :
    waveSphericalMean u x (r, t) =
      unitSphereRadialIntegralAt (fun y => u (y, t)) x r := by
  rfl

private def waveSphereJoint
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (q : EuclideanSpace ℝ (Fin n) × (ℝ × ℝ)) : ℝ :=
  waveSphereIntegrand u x q.1 q.2

private lemma waveSphereJoint_contDiff
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (waveSphereJoint u x) := by
  change ContDiff ℝ ∞ (fun q : EuclideanSpace ℝ (Fin n) × (ℝ × ℝ) =>
    u (x + q.2.1 • q.1, q.2.2))
  exact hu.comp (by fun_prop)

private lemma waveSphereJoint_contDiff_of_order
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ k (waveSphereJoint u x) := by
  change ContDiff ℝ k (fun q : EuclideanSpace ℝ (Fin n) × (ℝ × ℝ) =>
    u (x + q.2.1 • q.1, q.2.2))
  exact hu.comp (by fun_prop)

private lemma waveSphereIntegrand_contDiff
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n))
    (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ContDiff ℝ ∞ (waveSphereIntegrand u x
      (omega : EuclideanSpace ℝ (Fin n))) := by
  have hf := waveSphereJoint_contDiff hu x
  convert hf.comp (contDiff_const.prodMk
    (contDiff_id : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p))) using 1
  funext p
  rfl

private lemma waveSphereIntegrand_contDiff_of_order
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n))
    (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ContDiff ℝ k (waveSphereIntegrand u x
      (omega : EuclideanSpace ℝ (Fin n))) := by
  change ContDiff ℝ k (fun p : ℝ × ℝ =>
    u (x + p.1 • (omega : EuclideanSpace ℝ (Fin n)), p.2))
  exact hu.comp (by fun_prop)

private lemma continuous_waveSphereIntegrand_iteratedFDeriv
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Continuous (fun q :
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × (ℝ × ℝ) =>
      iteratedFDeriv ℝ m
        (waveSphereIntegrand u x
          (q.1 : EuclideanSpace ℝ (Fin n))) q.2) := by
  have hpartial := continuous_iteratedFDeriv_partial
    (waveSphereJoint_contDiff hu x) m
  convert hpartial.comp (continuous_subtype_val.prodMap
    (continuous_id : Continuous (fun p : ℝ × ℝ => p))) using 1
  funext q
  rfl

private lemma continuous_waveSphereIntegrand_iteratedFDeriv_of_order
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ k) :
    Continuous (fun q :
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × (ℝ × ℝ) =>
      iteratedFDeriv ℝ m
        (waveSphereIntegrand u x
          (q.1 : EuclideanSpace ℝ (Fin n))) q.2) := by
  have hpartial := continuous_iteratedFDeriv_partial_of_order
    (waveSphereJoint_contDiff_of_order hu x) m hm
  convert hpartial.comp (continuous_subtype_val.prodMap
    (continuous_id : Continuous (fun p : ℝ × ℝ => p))) using 1
  funext q
  rfl

/-- The fibrewise derivatives form a Taylor series for the spherical mean
through every prescribed finite order. -/
theorem waveSphericalMean_hasFTaylorSeriesUpTo_of_order [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n)) :
    HasFTaylorSeriesUpTo k (waveSphericalMean u x)
      (parametricIntegralSeries
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
        (fun omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          waveSphereIntegrand u x
            (omega : EuclideanSpace ℝ (Fin n)))) := by
  convert hasFTaylorSeriesUpTo_parametricIntegral_of_order k
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
    (fun omega => waveSphereIntegrand_contDiff_of_order hu x omega)
    (fun m hm =>
      continuous_waveSphereIntegrand_iteratedFDeriv_of_order hu x m hm) using 1
  rfl

/-- A `C^k` space-time field has a `C^k` spherical mean in radius and time. -/
theorem waveSphericalMean_contDiff_of_order [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ k (waveSphericalMean u x) :=
  (waveSphericalMean_hasFTaylorSeriesUpTo_of_order hu x).contDiff

/-- Normalizing by the fixed unit-sphere mass preserves every finite
differentiability order. -/
theorem waveSphericalAverage_contDiff_of_order [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ k (waveSphericalAverage u x) := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹
  have heq : waveSphericalAverage u x = c • waveSphericalMean u x := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, c, waveSphericalAverage_eq]
  rw [heq]
  exact (waveSphericalMean_contDiff_of_order hu x).const_smul c

/-- A finite-order smooth spatial function has a normalized spherical radial
profile of the same order around every center. -/
theorem unitSphereRadialAverageAt_contDiff_of_order [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : ℕ}
    (hf : ContDiff ℝ k f) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ k (unitSphereRadialAverageAt f x) := by
  let u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun p => f p.1
  have hu : ContDiff ℝ k u := hf.comp (by fun_prop)
  have hmean := (waveSphericalAverage_contDiff_of_order hu x).comp
    (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ k (fun _ : ℝ => (0 : ℝ))))
  convert hmean using 1
  rfl

/-- Every finite-order derivative of the normalized average is the same fixed
normalization factor times the corresponding derivative of the spherical
integral. -/
theorem iteratedFDeriv_waveSphericalAverage_of_order [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ k) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ m (waveSphericalAverage u x) p =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹ •
        iteratedFDeriv ℝ m (waveSphericalMean u x) p := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹
  have heq : waveSphericalAverage u x = c • waveSphericalMean u x := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, c, waveSphericalAverage_eq]
  rw [heq]
  exact iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (R := ℝ) (a := c)
    ((waveSphericalMean_contDiff_of_order hu x).of_le
      (by exact_mod_cast hm)).contDiffAt

/-- The integrals of the fibrewise derivatives are a Taylor series for the
spherical mean. -/
theorem waveSphericalMean_hasFTaylorSeriesUpTo [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n)) :
    HasFTaylorSeriesUpTo ∞ (waveSphericalMean u x)
      (parametricIntegralSeries
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
        (fun omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          waveSphereIntegrand u x
            (omega : EuclideanSpace ℝ (Fin n)))) := by
  convert hasFTaylorSeriesUpTo_parametricIntegral
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
    (fun omega => waveSphereIntegrand_contDiff hu x omega)
    (fun m => continuous_waveSphereIntegrand_iteratedFDeriv hu x m) using 1
  rfl

/-- A smooth space-time field has a smooth spherical mean in radius and time. -/
theorem waveSphericalMean_contDiff [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (waveSphericalMean u x) :=
  (waveSphericalMean_hasFTaylorSeriesUpTo hu x).contDiff

/-- Every iterated `(r,t)` derivative of a spherical mean is the integral of
the corresponding fibrewise derivative. -/
theorem iteratedFDeriv_waveSphericalMean [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ m (waveSphericalMean u x) p =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ m
          (waveSphereIntegrand u x
            (omega : EuclideanSpace ℝ (Fin n))) p
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hEq := (waveSphericalMean_hasFTaylorSeriesUpTo hu x).eq_iteratedFDeriv
    (m := m) (by exact_mod_cast le_top) p
  simpa [parametricIntegralSeries] using hEq.symm

/-- Every derivative up to the available finite order commutes with the
spherical integral. -/
theorem iteratedFDeriv_waveSphericalMean_of_order [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ k) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ m (waveSphericalMean u x) p =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ m
          (waveSphereIntegrand u x
            (omega : EuclideanSpace ℝ (Fin n))) p
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hEq := (waveSphericalMean_hasFTaylorSeriesUpTo_of_order hu x).eq_iteratedFDeriv
    (m := m) (by exact_mod_cast hm) p
  simpa [parametricIntegralSeries] using hEq.symm

/-- Evaluation of an iterated derivative also commutes with the spherical
integral.  Taking `m = 2` and both directions equal to `(0,1)` is the time
commutation used in the Euler--Poisson--Darboux equation. -/
theorem iteratedFDeriv_waveSphericalMean_apply [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (p : ℝ × ℝ) (v : Fin m → ℝ × ℝ) :
    iteratedFDeriv ℝ m (waveSphericalMean u x) p v =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ m
          (waveSphereIntegrand u x
            (omega : EuclideanSpace ℝ (Fin n))) p v
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  rw [iteratedFDeriv_waveSphericalMean hu x m p]
  apply ContinuousMultilinearMap.integral_apply
  exact integrable_iteratedFDeriv_apply
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
    (continuous_waveSphereIntegrand_iteratedFDeriv hu x m) p

/-- Evaluation of a finite-order derivative also commutes with the spherical
integral. -/
theorem iteratedFDeriv_waveSphericalMean_apply_of_order [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (x : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ k) (p : ℝ × ℝ) (v : Fin m → ℝ × ℝ) :
    iteratedFDeriv ℝ m (waveSphericalMean u x) p v =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ m
          (waveSphereIntegrand u x
            (omega : EuclideanSpace ℝ (Fin n))) p v
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  rw [iteratedFDeriv_waveSphericalMean_of_order hu x m hm p]
  apply ContinuousMultilinearMap.integral_apply
  exact integrable_iteratedFDeriv_apply
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
    (continuous_waveSphereIntegrand_iteratedFDeriv_of_order hu x m hm) p

/-- The second time derivative of the spherical mean is the sphere integral
of the ambient second time derivative. -/
theorem iteratedFDeriv_waveSphericalMean_time_two [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n))
    (p : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) p
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ 2 u
          (x + p.1 • (omega : EuclideanSpace ℝ (Fin n)), p.2)
          ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))]
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  rw [iteratedFDeriv_waveSphericalMean_apply hu x 2 p
    ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]]
  apply integral_congr_ae
  filter_upwards [] with omega
  exact iteratedFDeriv_waveSphereIntegrand_time_two hu x
    (omega : EuclideanSpace ℝ (Fin n)) p

/-- Under finite `C^k` regularity with `k ≥ 2`, the second time derivative of
the spherical mean is the sphere integral of the ambient second time
derivative. -/
theorem iteratedFDeriv_waveSphericalMean_time_two_of_order [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {k : ℕ}
    (hu : ContDiff ℝ k u) (hk : 2 ≤ k)
    (x : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) p
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ 2 u
          (x + p.1 • (omega : EuclideanSpace ℝ (Fin n)), p.2)
          ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))]
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  rw [iteratedFDeriv_waveSphericalMean_apply_of_order hu x 2 hk p
    ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]]
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [iteratedFDeriv_waveSphereIntegrand_of_order hu x
    (omega : EuclideanSpace ℝ (Fin n)) 2 hk p]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp [waveSphereParamLinear]

/-- For a smooth field satisfying `u_tt = Δ_x u`, the second time derivative
of its spherical mean is the spherical mean of the spatial Laplacian. -/
theorem iteratedFDeriv_waveSphericalMean_time_two_eq_laplacian
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) p
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        Δ (fun z => u (z, p.2))
          (x + p.1 • (omega : EuclideanSpace ℝ (Fin n)))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  rw [iteratedFDeriv_waveSphericalMean_time_two hu x p]
  apply integral_congr_ae
  filter_upwards [] with omega
  exact hWave
    (x + p.1 • (omega : EuclideanSpace ℝ (Fin n))) p.2

end EvansLib
