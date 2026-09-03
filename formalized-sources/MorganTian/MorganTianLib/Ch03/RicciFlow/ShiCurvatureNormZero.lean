import MorganTianLib.Ch03.RicciFlow.CurvatureEvolution
import MorganTianLib.Ch03.RicciFlow.ShiGeometricLevels
import MorganTianLib.Ch03.RicciFlow.ShiIteratedDirectional
import MorganTianLib.Ch03.RicciFlow.MetricDistortion

/-!
# Morgan--Tian Ch. 3 -- the zeroth curvature norm level

At level `j = 0`, the Shi curvature tower is the all-lowered Riemann tensor.
This file exposes its intrinsic squared norm as the explicit finite sum of
curvature components in the standard orthonormal frame.  The bridge is static:
it uses no flow, regularity, or target-shaped evolution assumptions.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Riemannian
open exteriorPower

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

section Curvature

/-- **Math.** The zeroth Shi curvature energy is the finite sum of squared
curvature-form components in the standard orthonormal basis. -/
theorem riemannCovDerivNormSqAt_zero_eq_curvatureForm_sq_sum
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormSqAt g 0 p =
      ∑ s : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I p)),
        (g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 0))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 1))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 2))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 3))) ^ 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp [riemannCovDerivNormSqAt, riemannCovDerivTower, covTensorNormSqAt,
    covTensorComponentAt, riemannTensorField]

/-- **Math.** The explicit zeroth-level curvature sum is nonnegative. -/
theorem curvatureForm_sq_sum_nonneg
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    0 ≤ ∑ s : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I p)),
      (g.leviCivitaConnection.curvatureFormAt g p
        (stdOrthonormalBasis ℝ (TangentSpace I p) (s 0))
        (stdOrthonormalBasis ℝ (TangentSpace I p) (s 1))
        (stdOrthonormalBasis ℝ (TangentSpace I p) (s 2))
        (stdOrthonormalBasis ℝ (TangentSpace I p) (s 3))) ^ 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Finset.sum_nonneg (fun s _ => sq_nonneg _)

/-- **Math.** The zeroth Shi energy vanishes exactly when every curvature
component in the standard orthonormal frame vanishes.  This is the finite
dimensional flatness interface for arguments that start from a zero
curvature bound. -/
theorem riemannCovDerivNormSqAt_zero_eq_zero_iff
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormSqAt g 0 p = 0 ↔
      ∀ s : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I p)),
        g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 0))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 1))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 2))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 3)) = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change covTensorNormSqAt g (riemannTensorField g) p = 0 ↔ _
  rw [covTensorNormSqAt_eq_zero_iff]
  simp [covTensorComponentAt, riemannTensorField]

/-- **Math.** The zeroth Shi norm vanishes exactly when every curvature
component in the standard orthonormal frame vanishes. -/
theorem riemannCovDerivNormAt_zero_eq_zero_iff
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormAt g 0 p = 0 ↔
      ∀ s : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I p)),
        g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 0))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 1))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 2))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 3)) = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Real.sqrt (riemannCovDerivNormSqAt g 0 p) = 0 ↔ _
  rw [Real.sqrt_eq_zero (riemannCovDerivNormSqAt_nonneg g 0 p)]
  exact riemannCovDerivNormSqAt_zero_eq_zero_iff g p

/-- **Math.** At every curvature-tower level, the square norm vanishes exactly
when all standard-orthonormal components of that level vanish. -/
theorem riemannCovDerivNormSqAt_eq_zero_iff_components
    (g : RiemannianMetric I M) (n : ℕ) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormSqAt g n p = 0 ↔
      ∀ s : Fin (4 + n) → Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorComponentAt g (riemannCovDerivTower g n) p s = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change covTensorNormSqAt g (riemannCovDerivTower g n) p = 0 ↔ _
  exact covTensorNormSqAt_eq_zero_iff g (riemannCovDerivTower g n) p

section DirectionalZero

variable [I.Boundaryless]

/-- **Math.** The square norm of an arbitrary curvature-tower level vanishes
exactly when each ordered iterated directional contraction vanishes.  This is
the zero-energy form of the finite directional decomposition used in higher
order Shi arguments. -/
theorem riemannCovDerivNormSqAt_eq_zero_iff_iteratedDirectional
    (g : RiemannianMetric I M) (n : ℕ) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormSqAt g n p = 0 ↔
      ∀ dirs : Fin n → Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorNormSqAt g
          (iteratedCovTensorDerivAlong g.leviCivitaConnection
            (riemannTensorField g) n
            (fun i => extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) (dirs i)))) p = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change covTensorNormSqAt g
      (iteratedCovTensorDeriv g.leviCivitaConnection
        (riemannTensorField g) n) p = 0 ↔ _
  rw [covTensorNormSqAt_iteratedCovTensorDerivAlong_eq_sum]
  constructor
  · intro h dirs
    let f : (Fin n → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ :=
      fun d => covTensorNormSqAt g
        (iteratedCovTensorDerivAlong g.leviCivitaConnection
          (riemannTensorField g) n
          (fun i => extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) (d i)))) p
    have hnonneg : ∀ d ∈ (Finset.univ :
        Finset (Fin n → Fin (Module.finrank ℝ (TangentSpace I p)))),
        0 ≤ f d := by
      intro d _hd
      exact covTensorNormSqAt_nonneg g _ p
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 h dirs
      (Finset.mem_univ dirs)
    exact hz
  · intro h
    exact Finset.sum_eq_zero fun dirs _ => h dirs

end DirectionalZero

/-! ### The operator bound controls every orthonormal component -/

section OperatorBound

variable [I.Boundaryless]

private theorem abs_curvatureOperator_le_of_unit_wedge
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    {K : ℝ} (h : HasCurvatureOperatorNormLe hB K)
    (u v : ⋀[ℝ]^2 V)
    (hu : wedgeInner u u = 1) (hv : wedgeInner v v = 1) :
    |curvatureOperator hB u v| ≤ K := by
  have hplus := h (u + v)
  have hminus := h (u - v)
  have hsum :
      |curvatureOperator hB (u + v) (u + v)| +
          |curvatureOperator hB (u - v) (u - v)| ≤
        K * (wedgeInner (u + v) (u + v) +
          wedgeInner (u - v) (u - v)) := by
    simpa [mul_add] using (add_le_add hplus hminus)
  have hqsum :
      wedgeInner (u + v) (u + v) + wedgeInner (u - v) (u - v) = 4 := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    linarith
  have hApolar :
      4 * curvatureOperator hB u v =
        curvatureOperator hB (u + v) (u + v) -
          curvatureOperator hB (u - v) (u - v) := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    have hs := curvatureOperator_symm hB u v
    linarith
  have habsdiv :
      |(curvatureOperator hB (u + v) (u + v) -
          curvatureOperator hB (u - v) (u - v)) / 4| ≤ K := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    have hdiff := abs_sub
      (curvatureOperator hB (u + v) (u + v))
      (curvatureOperator hB (u - v) (u - v))
    have hfour : K * (wedgeInner (u + v) (u + v) +
          wedgeInner (u - v) (u - v)) = 4 * K := by
      rw [hqsum]
      ring
    rw [hfour] at hsum
    calc
      |curvatureOperator hB (u + v) (u + v) -
          curvatureOperator hB (u - v) (u - v)| / 4 ≤
          (|curvatureOperator hB (u + v) (u + v)| +
            |curvatureOperator hB (u - v) (u - v)|) / 4 :=
        div_le_div_of_nonneg_right hdiff (by norm_num)
      _ ≤ (4 * K) / 4 := div_le_div_of_nonneg_right hsum (by norm_num)
      _ = K := by ring
  have hAdiv :
      curvatureOperator hB u v =
        (curvatureOperator hB (u + v) (u + v) -
          curvatureOperator hB (u - v) (u - v)) / 4 := by
    linarith [hApolar]
  rw [hAdiv]
  exact habsdiv

private theorem wedgeInner_stdOrthonormalBasis_self
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (e : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    (i j : Fin (Module.finrank ℝ V)) (hij : i ≠ j) :
    wedgeInner (ιMulti ℝ 2 ![e i, e j])
        (ιMulti ℝ 2 ![e i, e j]) = 1 := by
  rw [wedgeInner_wedge_self]
  simp only [Riemannian.wedgeSq]
  have hii : (inner ℝ (e i) (e i) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, e.orthonormal.1 i]
    norm_num
  have hjj : (inner ℝ (e j) (e j) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, e.orthonormal.1 j]
    norm_num
  have hij' : (inner ℝ (e i) (e j) : ℝ) = 0 := e.orthonormal.2 hij
  rw [hii, hjj, hij']
  norm_num

/-- **Math.** A pointwise curvature-operator bound controls every component of
the all-lowered curvature tensor in the standard orthonormal frame.  The
repeated-index cases vanish by antisymmetry; distinct pairs are obtained by
polarizing the diagonal Rayleigh bound on unit decomposable `2`-vectors. -/
theorem abs_curvatureFormAt_stdOrthonormalBasis_le_of_hasCurvatureOperatorNormLeAt
    (g : RiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K) (p : M)
    (hRm : HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita g) p K)
    (i j k l : Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    |g.leviCivitaConnection.curvatureFormAt g p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
        (stdOrthonormalBasis ℝ (TangentSpace I p) j)
        (stdOrthonormalBasis ℝ (TangentSpace I p) k)
        (stdOrthonormalBasis ℝ (TangentSpace I p) l)| ≤ K := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let hLC := canonicalLeviCivita_isLeviCivita g
  have hB : IsAlgCurvatureForm
      (curvatureFormAt g g.leviCivitaConnection p) := by
    exact isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p
  have hOp : HasCurvatureOperatorNormLe hB K := by
    simpa only [HasCurvatureOperatorNormLeAt] using hRm
  by_cases hij : i = j
  · have hz : curvatureFormAt g g.leviCivitaConnection p (e i) (e j)
        (e k) (e l) = 0 := by
      subst j
      have hs := hB.antisymm₁₂ (e i) (e i) (e k) (e l)
      linarith
    have hzero : |curvatureFormAt g g.leviCivitaConnection p
        (e i) (e j) (e k) (e l)| ≤ K := by
      rw [hz, abs_zero]
      exact hK
    rw [curvatureFormAt_eq_affineCurvatureFormAt] at hzero
    simpa [e] using hzero
  · by_cases hkl : k = l
    · have hz : curvatureFormAt g g.leviCivitaConnection p (e i) (e j)
          (e k) (e l) = 0 := by
        subst l
        have hs := hB.antisymm₃₄ (e i) (e j) (e k) (e k)
        linarith
      have hzero : |curvatureFormAt g g.leviCivitaConnection p
          (e i) (e j) (e k) (e l)| ≤ K := by
        rw [hz, abs_zero]
        exact hK
      rw [curvatureFormAt_eq_affineCurvatureFormAt] at hzero
      simpa [e] using hzero
    · have hu := wedgeInner_stdOrthonormalBasis_self e i j hij
      have hv := wedgeInner_stdOrthonormalBasis_self e k l hkl
      have hm := abs_curvatureOperator_le_of_unit_wedge hB hOp
        (ιMulti ℝ 2 ![e i, e j]) (ιMulti ℝ 2 ![e k, e l]) hu hv
      have hm' : |curvatureFormAt g g.leviCivitaConnection p
          (e i) (e j) (e k) (e l)| ≤ K := by
        simpa only [curvatureOperator_ιMulti] using hm
      simpa [e, curvatureFormAt_eq_affineCurvatureFormAt] using hm'

/-- **Math.** If the curvature operator is bounded by `K` at `p`, then the
zeroth Shi energy is at most `(n^2 K)^2`.  There are `n^4` orthonormal
four-slot components, each with square at most `K^2`. -/
theorem riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeAt
    (g : RiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K) (p : M)
    (hRm : HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita g) p K) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormSqAt g 0 p ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * K) ^ 2 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [riemannCovDerivNormSqAt_zero_eq_curvatureForm_sq_sum]
  calc
    (∑ s : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I p)),
        (g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 0))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 1))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 2))
          (stdOrthonormalBasis ℝ (TangentSpace I p) (s 3))) ^ 2) ≤
        ∑ _s : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I p)), K ^ 2 := by
      refine Finset.sum_le_sum fun s _hs => ?_
      rw [sq_le_sq, abs_of_nonneg hK]
      exact
        abs_curvatureFormAt_stdOrthonormalBasis_le_of_hasCurvatureOperatorNormLeAt
          g hK p hRm (s 0) (s 1) (s 2) (s 3)
    _ = ((Module.finrank ℝ (TangentSpace I p) : ℝ) ^ 2 * K) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    _ = ((Module.finrank ℝ E : ℝ) ^ 2 * K) ^ 2 := by
      have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
          Module.finrank ℝ (TangentSpace I p) := Fintype.card_fin _
      have hdim : (Module.finrank ℝ (TangentSpace I p) : ℝ) =
          (Module.finrank ℝ E : ℝ) := by
        have hdimNat : Module.finrank ℝ (TangentSpace I p) =
            Module.finrank ℝ E := by
          simpa only [Fintype.card_fin] using hcard.symm
        exact_mod_cast hdimNat
      rw [hdim]

/-- **Math.** A uniform curvature-operator bound on a time set supplies the
zeroth Shi-energy bound on every time slice in that set. -/
theorem riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hRm : HasCurvatureOperatorNormLeOnTime g J K) :
    ∀ t ∈ J, ∀ p : M,
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      riemannCovDerivNormSqAt (g t) 0 p ≤
        ((Module.finrank ℝ E : ℝ) ^ 2 * K) ^ 2 := by
  intro t ht p
  exact riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeAt
    (g t) hK p (hRm t ht p)

#print axioms riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeAt
#print axioms riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeOnTime
#print axioms riemannCovDerivNormSqAt_zero_eq_zero_iff
#print axioms riemannCovDerivNormAt_zero_eq_zero_iff
#print axioms riemannCovDerivNormSqAt_eq_zero_iff_components
#print axioms riemannCovDerivNormSqAt_eq_zero_iff_iteratedDirectional

end OperatorBound

end Curvature

end MorganTianLib

end
