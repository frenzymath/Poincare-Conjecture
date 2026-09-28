import Topping.ParabolicPDE.VectorSmooth

/-!
# Smooth vector exponential test sections

The formal vector jet in `Vector.lean` is now connected to genuine `C²`
coordinate-space sections.  The normalization removes the common exponential
factor, exactly as in the scalar principal-symbol calculation.
-/

namespace Topping
noncomputable section

open scoped BigOperators

variable {n : ℕ} {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace VectorSecondOrderJet

variable {ι : Type*} [Fintype ι]

/-- Scale every component of a vector second-order jet by a scalar. -/
def scale (j : VectorSecondOrderJet ι V) (c : ℝ) :
    VectorSecondOrderJet ι V where
  value := c • j.value
  first := fun i => c • j.first i
  second := fun i k => c • j.second i k

@[simp] theorem scale_value (c : ℝ)
    (j : VectorSecondOrderJet ι V) :
    (j.scale c).value = c • j.value := rfl

@[simp] theorem scale_first (c : ℝ)
    (j : VectorSecondOrderJet ι V) (i : ι) :
    (j.scale c).first i = c • j.first i := rfl

@[simp] theorem scale_second (c : ℝ)
    (j : VectorSecondOrderJet ι V) (i k : ι) :
    (j.scale c).second i k = c • j.second i k := rfl

end VectorSecondOrderJet

namespace VectorSecondOrderCoefficients

theorem applyJet_scale
    {X ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : VectorSecondOrderCoefficients X ι V) (x : X)
    (c : ℝ) (j : VectorSecondOrderJet ι V) :
    A.applyJet x (VectorSecondOrderJet.scale j c) = c • A.applyJet x j := by
  simp only [applyJet, VectorSecondOrderJet.scale, map_smul]
  simp_rw [← Finset.smul_sum]
  simp only [smul_add]

end VectorSecondOrderCoefficients

namespace ParabolicPDE

/-- The actual jet of `exp (s phi) • u`, after removal of its common
exponential factor. -/
def normalizedVectorExponentialJetAt (s : ℝ)
    (phi : ScalarCoordinateSpace n → ℝ)
    (u : ScalarCoordinateSpace n → V)
    (x : ScalarCoordinateSpace n) :
    VectorSecondOrderJet (Fin n) V :=
  (frechetVectorJetAt (vectorExponentialProduct s phi u) x).scale
    (Real.exp (-(s * phi x)))

theorem normalizedVectorExponentialJetAt_eq_exponentialJet
    (s : ℝ) (phi : ScalarCoordinateSpace n → ℝ)
    (u : ScalarCoordinateSpace n → V)
    (x : ScalarCoordinateSpace n)
    (hphi : ContDiff ℝ 2 phi) (hu : ContDiff ℝ 2 u) :
    normalizedVectorExponentialJetAt s phi u x =
      VectorSecondOrderCoefficients.exponentialJet s
        (coordinateFDeriv phi x) (u x)
        (vectorCoordinateFDeriv u x)
        (vectorCoordinateSecondFDeriv u x)
        (coordinateSecondFDeriv phi x) := by
  have hphiDiff : Differentiable ℝ phi :=
    hphi.differentiable (by norm_num)
  have huDiff : Differentiable ℝ u :=
    hu.differentiable (by norm_num)
  have hscaled : ContDiff ℝ 2
      (fun y => s * phi y) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hphi.const_smul s
  have hphase : ContDiff ℝ 2 (exponentialPhase s phi) :=
    hscaled.exp
  have hphaseDiff : Differentiable ℝ (exponentialPhase s phi) :=
    hphase.differentiable (by norm_num)
  have hphasePartial (k : Fin n) : DifferentiableAt ℝ
      (fun y => coordinateFDeriv (exponentialPhase s phi) y k) x :=
    (coordinateFDeriv_differentiable_of_contDiff_two hphase k) x
  have huPartial (k : Fin n) : DifferentiableAt ℝ
      (fun y => vectorCoordinateFDeriv u y k) x :=
    (vectorCoordinateFDeriv_differentiable_of_contDiff_two hu k) x
  have hcancel :
      Real.exp (-(s * phi x)) * Real.exp (s * phi x) = 1 := by
    rw [Real.exp_neg]
    exact inv_mul_cancel₀ (Real.exp_ne_zero _)
  have hphaseFirst (j : Fin n) :
      vectorCoordinateFDeriv (exponentialPhase s phi) x j =
        Real.exp (s * phi x) * (s * coordinateFDeriv phi x j) := by
    change coordinateFDeriv (exponentialPhase s phi) x j = _
    exact coordinateFDeriv_exponentialPhase s j (hphiDiff x)
  have hphaseSecond (j k : Fin n) :
      vectorCoordinateSecondFDeriv (exponentialPhase s phi) x j k =
        Real.exp (s * phi x) *
          (s ^ 2 * coordinateFDeriv phi x j * coordinateFDeriv phi x k +
            s * coordinateSecondFDeriv phi x j k) := by
    change coordinateSecondFDeriv (exponentialPhase s phi) x j k = _
    exact coordinateSecondFDeriv_exponentialPhase s j k hphi
  have hlin (d : ℝ) :
      s * Real.exp (-(s * phi x)) * Real.exp (s * phi x) * d = s * d := by
    calc
      s * Real.exp (-(s * phi x)) * Real.exp (s * phi x) * d =
          s * (Real.exp (-(s * phi x)) * Real.exp (s * phi x)) * d := by ring
      _ = s * d := by rw [hcancel]; ring
  have hquad (di dk d₂ : ℝ) :
      s * Real.exp (-(s * phi x)) * Real.exp (s * phi x) * d₂ +
          s ^ 2 * Real.exp (-(s * phi x)) * Real.exp (s * phi x) * di * dk =
        s ^ 2 * di * dk + s * d₂ := by
    calc
      s * Real.exp (-(s * phi x)) * Real.exp (s * phi x) * d₂ +
          s ^ 2 * Real.exp (-(s * phi x)) * Real.exp (s * phi x) * di * dk =
          s * (Real.exp (-(s * phi x)) * Real.exp (s * phi x)) * d₂ +
            s ^ 2 * (Real.exp (-(s * phi x)) * Real.exp (s * phi x)) * di * dk := by ring
      _ = s ^ 2 * di * dk + s * d₂ := by rw [hcancel]; ring
  apply VectorSecondOrderJet.ext_fields
  · dsimp [normalizedVectorExponentialJetAt, VectorSecondOrderJet.scale,
      VectorSecondOrderCoefficients.exponentialJet]
    change Real.exp (-(s * phi x)) •
      (Real.exp (s * phi x) • u x) = u x
    rw [smul_smul]
    rw [show Real.exp (-(s * phi x)) * Real.exp (s * phi x) = 1 from hcancel]
    simp
  · funext i
    dsimp [normalizedVectorExponentialJetAt, VectorSecondOrderJet.scale,
      VectorSecondOrderCoefficients.exponentialJet]
    change Real.exp (-(s * phi x)) •
      vectorCoordinateFDeriv (vectorExponentialProduct s phi u) x i =
        (s * coordinateFDeriv phi x i) • u x +
          vectorCoordinateFDeriv u x i
    rw [show vectorExponentialProduct s phi u =
        (fun y => exponentialPhase s phi y • u y) by rfl]
    rw [vectorCoordinateFDeriv_smul i (hphaseDiff x) (huDiff x)]
    rw [hphaseFirst i]
    rw [smul_add, smul_smul]
    simp [exponentialPhase, smul_smul]
    ring_nf
    rw [hcancel, hlin]
    simp only [one_smul]
    abel
  · funext i k
    dsimp [normalizedVectorExponentialJetAt, VectorSecondOrderJet.scale,
      VectorSecondOrderCoefficients.exponentialJet]
    change Real.exp (-(s * phi x)) •
      vectorCoordinateSecondFDeriv
        (vectorExponentialProduct s phi u) x i k =
        (s ^ 2 * coordinateFDeriv phi x i * coordinateFDeriv phi x k) • u x +
          s • (coordinateFDeriv phi x i • vectorCoordinateFDeriv u x k +
            coordinateFDeriv phi x k • vectorCoordinateFDeriv u x i +
            coordinateSecondFDeriv phi x i k • u x) +
          vectorCoordinateSecondFDeriv u x i k
    rw [show vectorExponentialProduct s phi u =
        (fun y => exponentialPhase s phi y • u y) by rfl]
    rw [vectorCoordinateSecondFDeriv_smul i k hphaseDiff huDiff
      (hphasePartial k) (huPartial k)]
    rw [hphaseFirst i, hphaseFirst k, hphaseSecond i k]
    simp only [smul_add, smul_smul]
    simp [exponentialPhase]
    ring_nf
    rw [hcancel, hlin, hlin, hquad]
    simp only [one_smul, add_smul]
    abel

theorem normalizedVectorExponentialOperator_eq_exponentialJet
    (A : VectorSecondOrderCoefficients (ScalarCoordinateSpace n) (Fin n) V)
    (s : ℝ) (phi : ScalarCoordinateSpace n → ℝ)
    (u : ScalarCoordinateSpace n → V)
    (x : ScalarCoordinateSpace n)
    (hphi : ContDiff ℝ 2 phi) (hu : ContDiff ℝ 2 u) :
    Real.exp (-(s * phi x)) •
        A.applyJet x (frechetVectorJetAt (vectorExponentialProduct s phi u) x) =
      A.applyJet x
        (VectorSecondOrderCoefficients.exponentialJet s
          (coordinateFDeriv phi x) (u x)
          (vectorCoordinateFDeriv u x)
          (vectorCoordinateSecondFDeriv u x)
          (coordinateSecondFDeriv phi x)) := by
  rw [← VectorSecondOrderCoefficients.applyJet_scale A x
      (Real.exp (-(s * phi x)))
      (frechetVectorJetAt (vectorExponentialProduct s phi u) x)]
  calc
    A.applyJet x
        ((frechetVectorJetAt (vectorExponentialProduct s phi u) x).scale
          (Real.exp (-(s * phi x)))) =
      A.applyJet x (normalizedVectorExponentialJetAt s phi u x) := by rfl
    _ = A.applyJet x
        (VectorSecondOrderCoefficients.exponentialJet s
          (coordinateFDeriv phi x) (u x)
          (vectorCoordinateFDeriv u x)
          (vectorCoordinateSecondFDeriv u x)
          (coordinateSecondFDeriv phi x)) := by
      rw [normalizedVectorExponentialJetAt_eq_exponentialJet
        s phi u x hphi hu]

theorem vectorPrincipalSymbol_limit_of_contDiff_two
    (A : VectorSecondOrderCoefficients (ScalarCoordinateSpace n) (Fin n) V)
    (x : ScalarCoordinateSpace n)
    (phi : ScalarCoordinateSpace n → ℝ)
    (u : ScalarCoordinateSpace n → V)
    (hphi : ContDiff ℝ 2 phi) (hu : ContDiff ℝ 2 u) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 •
        (Real.exp (-(s * phi x)) •
          A.applyJet x
            (frechetVectorJetAt (vectorExponentialProduct s phi u) x)))
      Filter.atTop
      (nhds (A.principalSymbol x (coordinateFDeriv phi x) (u x))) := by
  have hformal := A.vectorPrincipalSymbol_limit x
    (coordinateFDeriv phi x) (u x)
    (vectorCoordinateFDeriv u x)
    (vectorCoordinateSecondFDeriv u x)
    (coordinateSecondFDeriv phi x)
  have heq :
      (fun s : ℝ => s⁻¹ ^ 2 •
        A.applyJet x
          (VectorSecondOrderCoefficients.exponentialJet s
            (coordinateFDeriv phi x) (u x)
            (vectorCoordinateFDeriv u x)
            (vectorCoordinateSecondFDeriv u x)
            (coordinateSecondFDeriv phi x))) =ᶠ[Filter.atTop]
      (fun s : ℝ => s⁻¹ ^ 2 •
        (Real.exp (-(s * phi x)) •
          A.applyJet x
            (frechetVectorJetAt (vectorExponentialProduct s phi u) x))) :=
    Filter.Eventually.of_forall (fun s => by
      exact congrArg (fun z : V => s⁻¹ ^ 2 • z)
        (normalizedVectorExponentialOperator_eq_exponentialJet
          A s phi u x hphi hu).symm)
  exact hformal.congr' heq

end ParabolicPDE
end
end Topping
