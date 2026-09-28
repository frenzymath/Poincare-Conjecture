import HanLinLectureNotes.Ch02.Alexandroff
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Han--Lin Chapter 2: the operator form of the Alexandroff inequality

The determinant--trace arithmetic--geometric mean estimate and its weighted
contact-integral consequence from Han--Lin Remark 2.34.
-/

open Filter MeasureTheory MeasureTheory.Measure Set Topology
open scoped BigOperators ENNReal MatrixOrder RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- Subtracting a linear functional does not change the Hessian. -/
lemma hessianMatrix_sub_inner
    {n : Nat} {u : Euclidean n -> Real} {x p : Euclidean n}
    (hu : ContDiffAt Real 2 u x) :
    hessianMatrix (fun z => u z - inner Real p z) x = hessianMatrix u x := by
  let L : Euclidean n →L[Real] Real := innerSL Real p
  have hFderivEq :
      fderiv Real (fun z => u z - inner Real p z) =ᶠ[nhds x]
        fun z => fderiv Real u z - L := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    have hlin : HasFDerivAt (fun z : Euclidean n => inner Real p z) L y := by
      convert ContinuousLinearMap.hasFDerivAt L using 1
      funext z
      exact (innerSL_apply_apply Real p z).symm
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.sub hlin).fderiv
  have hdu : DifferentiableAt Real (fderiv Real u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsubDeriv :=
    hdu.hasFDerivAt.sub (hasFDerivAt_const L x)
  have hsecond :
      fderiv Real (fderiv Real (fun z => u z - inner Real p z)) x =
        fderiv Real (fderiv Real u) x := by
    calc
      _ = fderiv Real (fun z => fderiv Real u z - L) x :=
        hFderivEq.fderiv_eq
      _ = fderiv Real (fderiv Real u - fun _ => L) x := by rfl
      _ = fderiv Real (fderiv Real u) x := by
        rw [hsubDeriv.fderiv]
        simp
  unfold hessianMatrix secondDerivativeBilin
  rw [hsecond]

/-- At an upper contact point of a `C^2` function on an open set, the negative
Hessian is positive semidefinite. -/
theorem neg_hessianMatrix_posSemidef_of_mem_upperContactSet
    {n : Nat} {Omega : Set (Euclidean n)}
    {u : Euclidean n -> Real} {x : Euclidean n}
    (hOmegaOpen : IsOpen Omega)
    (hu : ContDiffOn Real 2 u Omega)
    (hx : x ∈ upperContactSet Omega u) :
    (-(hessianMatrix u x)).PosSemidef := by
  rcases hx with ⟨hxOmega, p, hsupport⟩
  have hux : ContDiffAt Real 2 u x :=
    hu.contDiffAt (hOmegaOpen.mem_nhds hxOmega)
  let q : Euclidean n -> Real := fun z => u z - inner Real p z
  have hlinDiff :
      ContDiffAt Real 2 (fun z : Euclidean n => inner Real p z) x := by
    change ContDiffAt Real 2 (innerSL Real (E := Euclidean n) p) x
    exact (ContinuousLinearMap.contDiff _).contDiffAt
  have hqdiff : ContDiffAt Real 2 q x := by
    dsimp only [q]
    exact hux.sub hlinDiff
  have hqmaxOn : IsMaxOn q Omega x := by
    intro z hz
    have h := hsupport z hz
    rw [inner_sub_right] at h
    change u z - inner Real p z <= u x - inner Real p x
    calc
      u z - inner Real p z <=
          u x + (inner Real p z - inner Real p x) - inner Real p z :=
        sub_le_sub_right h _
      _ = u x - inner Real p x := by ring
  have hqmax : IsLocalMax q x :=
    hqmaxOn.isLocalMax (hOmegaOpen.mem_nhds hxOmega)
  have hqHessian := neg_hessianMatrix_posSemidef hqdiff hqmax
  have hessianEq : hessianMatrix q x = hessianMatrix u x := by
    dsimp only [q]
    exact hessianMatrix_sub_inner hux
  rw [hessianEq] at hqHessian
  exact hqHessian

/-- The determinant of a nonzero-dimensional positive semidefinite real matrix
is bounded by the corresponding power of its arithmetic mean eigenvalue. -/
theorem posSemidef_det_le_pow_trace_div_card
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : Matrix ι ι Real} (hM : M.PosSemidef) :
    M.det <= (M.trace / (Fintype.card ι : Real)) ^ Fintype.card ι := by
  let hHerm : M.IsHermitian := hM.isHermitian
  have heig : ∀ i : ι, 0 <= hHerm.eigenvalues i :=
    hM.eigenvalues_nonneg
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hgeom := Real.geom_mean_le_arith_mean
    Finset.univ (fun _ : ι => (1 : Real))
      hHerm.eigenvalues
      (by intros; norm_num)
      (by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact_mod_cast Fintype.card_pos_iff.mpr inferInstance)
      (by simpa using heig)
  simp only [Real.rpow_one, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hgeom
  have hprodNonneg : 0 <= ∏ i : ι, hHerm.eigenvalues i :=
    Finset.prod_nonneg fun i _ => heig i
  have hpow := pow_le_pow_left₀
    (Real.rpow_nonneg hprodNonneg _) hgeom (Fintype.card ι)
  rw [Real.rpow_inv_natCast_pow hprodNonneg hcard] at hpow
  rw [hHerm.det_eq_prod_eigenvalues, hHerm.trace_eq_sum_eigenvalues]
  exact hpow

/-- Determinant--trace AM--GM after conjugating a positive semidefinite matrix
by a square root factor of a positive definite coefficient matrix. -/
theorem posDef_det_le_inv_det_mul_trace_pow
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A B : Matrix ι ι Real} (hA : A.PosDef) (hB : B.PosSemidef) :
    B.det <= (1 / A.det) *
      ((A * B).trace / (Fintype.card ι : Real)) ^ Fintype.card ι := by
  obtain ⟨C, hAeq⟩ :
      ∃ C : Matrix ι ι Real, A = C.conjTranspose * C := by
    obtain ⟨C, hC⟩ :=
      CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
    exact ⟨C, by simpa only [Matrix.star_eq_conjTranspose] using hC⟩
  have hM : (C * B * C.conjTranspose).PosSemidef :=
    hB.mul_mul_conjTranspose_same C
  have hBound := posSemidef_det_le_pow_trace_div_card hM
  have hdet :
      (C * B * C.conjTranspose).det = A.det * B.det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    rw [hAeq, Matrix.det_mul]
    ring
  have htrace :
      (C * B * C.conjTranspose).trace = (A * B).trace := by
    rw [Matrix.trace_mul_cycle]
    rw [hAeq]
  rw [hdet, htrace] at hBound
  have hdetPos : 0 < A.det := hA.det_pos
  have hBound' :
      B.det * A.det <=
        ((A * B).trace / (Fintype.card ι : Real)) ^ Fintype.card ι := by
    simpa only [mul_comm] using hBound
  have hdiv := (le_div_iff₀ hdetPos).2 hBound'
  calc
    B.det <=
        (((A * B).trace / (Fintype.card ι : Real)) ^ Fintype.card ι) /
          A.det := hdiv
    _ = (1 / A.det) *
        ((A * B).trace / (Fintype.card ι : Real)) ^ Fintype.card ι := by
      ring

/-- The pointwise determinant--operator inequality in Han--Lin Remark 2.34. -/
theorem operator_det_hessian_bound
    {n : Nat} (hn : 0 < n)
    {A H : Matrix (Fin n) (Fin n) Real}
    (hA : A.PosDef) (hH : (-H).PosSemidef) :
    (-H).det <= (1 / A.det) *
      ((-(A * H).trace) / (n : Real)) ^ n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  simpa only [Matrix.mul_neg, Matrix.trace_neg, Fintype.card_fin] using
    posDef_det_le_inv_det_mul_trace_pow hA hH

/-- On the upper contact set, the Hessian Jacobian is bounded by the normalized
operator expression from Han--Lin Remark 2.34. -/
theorem alexandroff_weighted_hessian_contact_integral_le_operator
    {n : Nat} (hn : 0 < n)
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n))
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega)
    (hu : ContDiffOn Real 2 u Omega)
    (A : Euclidean n -> Matrix (Fin n) (Fin n) Real)
    (hA : ∀ x ∈ upperContactSet Omega u, (A x).PosDef)
    (Dstar : Euclidean n -> Real)
    (hDstarPos : ∀ x ∈ upperContactSet Omega u, 0 < Dstar x)
    (hDstarPow : ∀ x ∈ upperContactSet Omega u,
      Dstar x ^ n = (A x).det)
    {g : Euclidean n -> Real} (hgNonneg : ∀ p, 0 <= g p) :
    (∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal
          (g (gradient u x) * |(hessianMatrix u x).det|) ∂mu) <=
      ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal
          (g (gradient u x) *
            ((-(A x * hessianMatrix u x).trace) /
              ((n : Real) * Dstar x)) ^ n) ∂mu := by
  have hcontactMeasurable : MeasurableSet (upperContactSet Omega u) :=
    measurableSet_upperContactSet hOmegaOpen hu
  apply MeasureTheory.lintegral_mono_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hcontactMeasurable] with x hx
  apply ENNReal.ofReal_le_ofReal
  let H := hessianMatrix u x
  have hH : (-H).PosSemidef :=
    neg_hessianMatrix_posSemidef_of_mem_upperContactSet hOmegaOpen hu hx
  have hdetAbs : |H.det| = (-H).det := by
    calc
      |H.det| = |(-H).det| := by
        rw [Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ = (-H).det := abs_of_nonneg hH.det_nonneg
  have hdetBound :
      (-H).det <= (1 / (A x).det) *
        ((-(A x * H).trace) / (n : Real)) ^ n :=
    operator_det_hessian_bound hn (hA x hx) hH
  have hscale :
      (1 / (A x).det) * ((-(A x * H).trace) / (n : Real)) ^ n =
        ((-(A x * H).trace) / ((n : Real) * Dstar x)) ^ n := by
    rw [← hDstarPow x hx, div_pow, div_pow, mul_pow]
    have hn0 : (n : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hDstar0 : Dstar x ≠ 0 := ne_of_gt (hDstarPos x hx)
    field_simp
  calc
    g (gradient u x) * |(hessianMatrix u x).det| =
        g (gradient u x) * (-H).det := by
      rw [show hessianMatrix u x = H from rfl, hdetAbs]
    _ <= g (gradient u x) *
        ((1 / (A x).det) * ((-(A x * H).trace) / (n : Real)) ^ n) :=
      mul_le_mul_of_nonneg_left hdetBound (hgNonneg (gradient u x))
    _ = g (gradient u x) *
        ((-(A x * hessianMatrix u x).trace) /
          ((n : Real) * Dstar x)) ^ n := by
      rw [hscale]

/-- The weighted contact-integral consequence in Han--Lin Remark 2.34. Here
`Dstar` is the positive `n`-th root of the determinant of the coefficient
matrix. -/
theorem alexandroff_weighted_operator_contact_integral
    {n : Nat} (hn : 0 < n)
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    (A : Euclidean n -> Matrix (Fin n) (Fin n) Real)
    (hA : ∀ x ∈ upperContactSet Omega u, (A x).PosDef)
    (Dstar : Euclidean n -> Real)
    (hDstarPos : ∀ x ∈ upperContactSet Omega u, 0 < Dstar x)
    (hDstarPow : ∀ x ∈ upperContactSet Omega u,
      Dstar x ^ n = (A x).det)
    {g : Euclidean n -> Real} (hg : Measurable g)
    (hgNonneg : ∀ p, 0 <= g p)
    (hgLocal : LocallyIntegrable g mu) :
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u),
        ENNReal.ofReal (g p) ∂mu) <=
      ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal
          (g (gradient u x) *
            ((-(A x * hessianMatrix u x).trace) /
              ((n : Real) * Dstar x)) ^ n) ∂mu := by
  exact (alexandroff_weighted_contact_integral
    mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu
      hg hgNonneg hgLocal).trans
    (alexandroff_weighted_hessian_contact_integral_le_operator
      hn mu hOmegaOpen hu A hA Dstar hDstarPos hDstarPow hgNonneg)

/-- Han--Lin Remark 2.34, with both the pointwise determinant estimate on the
upper contact set and its weighted integral consequence. -/
theorem alexandroff_operator_contact_inequalities
    {n : Nat} (hn : 0 < n)
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    (A : Euclidean n -> Matrix (Fin n) (Fin n) Real)
    (hA : ∀ x ∈ upperContactSet Omega u, (A x).PosDef)
    (Dstar : Euclidean n -> Real)
    (hDstarPos : ∀ x ∈ upperContactSet Omega u, 0 < Dstar x)
    (hDstarPow : ∀ x ∈ upperContactSet Omega u,
      Dstar x ^ n = (A x).det)
    {g : Euclidean n -> Real} (hg : Measurable g)
    (hgNonneg : ∀ p, 0 <= g p)
    (hgLocal : LocallyIntegrable g mu) :
    (∀ x ∈ upperContactSet Omega u,
      (-(hessianMatrix u x)).det <= (1 / (A x).det) *
        ((-(A x * hessianMatrix u x).trace) / (n : Real)) ^ n) ∧
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u),
        ENNReal.ofReal (g p) ∂mu) <=
      ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal
          (g (gradient u x) *
            ((-(A x * hessianMatrix u x).trace) /
              ((n : Real) * Dstar x)) ^ n) ∂mu := by
  constructor
  · intro x hx
    exact operator_det_hessian_bound hn (hA x hx)
      (neg_hessianMatrix_posSemidef_of_mem_upperContactSet hOmegaOpen hu hx)
  · exact alexandroff_weighted_operator_contact_integral
      hn mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu
        A hA Dstar hDstarPos hDstarPow hg hgNonneg hgLocal

end HanLinLectureNotes.Ch02
