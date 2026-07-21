import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import LeeSmoothLib.Ch08.Sec08_63.Problem_8_7
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff Manifold Quaternion RealInnerProductSpace

local notation "𝕆" => ℍ × ℍ
local notation "𝕊" => 𝕆 × 𝕆
local notation "unitSedenionSphere" => Metric.sphere (0 : 𝕊) 1

/-- The sedenion multiplication on `𝕆 × 𝕆` is the next Cayley-Dickson doubling of
the octonion multiplication from Problem 8-7. -/
def sedenionMul (P Q : 𝕊) : 𝕊 :=
  (octonionMul P.1 Q.1 - octonionMul Q.2 (octonionStar P.2),
    octonionMul (octonionStar P.1) Q.2 + octonionMul Q.1 P.2)

scoped[Sedenion] infixl:70 " *ₛ " => sedenionMul

open scoped Sedenion

/-- The fifteen standard imaginary unit sedenions, obtained by doubling the standard
imaginary basis of the octonions from Problem 8-7. -/
def problem_8_8_basisVec : Fin 15 → 𝕊 :=
  ![((problem_8_7_basisVec 0), (0 : 𝕆)),
    ((problem_8_7_basisVec 1), (0 : 𝕆)),
    ((problem_8_7_basisVec 2), (0 : 𝕆)),
    ((problem_8_7_basisVec 3), (0 : 𝕆)),
    ((problem_8_7_basisVec 4), (0 : 𝕆)),
    ((problem_8_7_basisVec 5), (0 : 𝕆)),
    ((problem_8_7_basisVec 6), (0 : 𝕆)),
    ((0 : 𝕆), (((1 : ℍ), (0 : ℍ)) : 𝕆)),
    ((0 : 𝕆), (problem_8_7_basisVec 0)),
    ((0 : 𝕆), (problem_8_7_basisVec 1)),
    ((0 : 𝕆), (problem_8_7_basisVec 2)),
    ((0 : 𝕆), (problem_8_7_basisVec 3)),
    ((0 : 𝕆), (problem_8_7_basisVec 4)),
    ((0 : 𝕆), (problem_8_7_basisVec 5)),
    ((0 : 𝕆), (problem_8_7_basisVec 6))]

/-- The sedenionic vector fields are obtained by left multiplication by the standard
imaginary basis vectors. -/
def problem_8_8_vectorField (i : Fin 15) : 𝕊 → 𝕊 :=
  fun Q ↦ problem_8_8_basisVec i *ₛ Q

/-- The sedenionic vector fields are given by left multiplication by the basis vectors. -/
theorem problem_8_8_vectorField_apply (i : Fin 15) (Q : 𝕊) :
    problem_8_8_vectorField i Q = problem_8_8_basisVec i *ₛ Q := rfl

/-- Helper for Problem 8-8: octonion conjugation is additive. -/
theorem octonionStar_add (P₁ P₂ : 𝕆) :
    octonionStar (P₁ + P₂) = octonionStar P₁ + octonionStar P₂ := by
  -- Expand the coordinatewise conjugation formula.
  ext <;> simp [octonionStar]
  all_goals abel

/-- Helper for Problem 8-8: octonion conjugation is `ℝ`-linear. -/
theorem octonionStar_smul (a : ℝ) (P : 𝕆) :
    octonionStar (a • P) = a • octonionStar P := by
  -- Expand the coordinatewise conjugation formula.
  ext <;> simp [octonionStar]

/-- Sedenion multiplication is additive in the left variable. -/
theorem sedenionMul_add_left (P₁ P₂ Q : 𝕊) :
    (P₁ + P₂) *ₛ Q = P₁ *ₛ Q + P₂ *ₛ Q := by
  -- Expand the Cayley-Dickson formula coordinatewise and use octonion bilinearity.
  ext <;>
    simp [sedenionMul, octonionStar_add, sub_eq_add_neg, octonionMul_add_left,
      octonionMul_add_right]
  all_goals abel

/-- Sedenion multiplication is `ℝ`-linear in the left variable. -/
theorem sedenionMul_smul_left (a : ℝ) (P Q : 𝕊) :
    (a • P) *ₛ Q = a • (P *ₛ Q) := by
  -- Expand scalar multiplication in each octonion coordinate and factor out the real scalar.
  ext <;>
    simp [sedenionMul, octonionStar_smul, sub_eq_add_neg, octonionMul_smul_left,
      octonionMul_smul_right]

/-- Sedenion multiplication is additive in the right variable. -/
theorem sedenionMul_add_right (P Q₁ Q₂ : 𝕊) :
    P *ₛ (Q₁ + Q₂) = P *ₛ Q₁ + P *ₛ Q₂ := by
  -- Expand the Cayley-Dickson formula coordinatewise and use octonion bilinearity.
  ext <;>
    simp [sedenionMul, sub_eq_add_neg, octonionMul_add_left, octonionMul_add_right]
  all_goals abel

/-- Sedenion multiplication is `ℝ`-linear in the right variable. -/
theorem sedenionMul_smul_right (a : ℝ) (P Q : 𝕊) :
    P *ₛ (a • Q) = a • (P *ₛ Q) := by
  -- Expand scalar multiplication in each octonion coordinate and factor out the real scalar.
  ext <;>
    simp [sedenionMul, sub_eq_add_neg, octonionMul_smul_left,
      octonionMul_smul_right]

/-- The sedenions form a `16`-dimensional real vector space. -/
theorem problem_8_8_finrank :
    Module.finrank ℝ 𝕊 = 15 + 1 := by
  have hq : Module.finrank ℝ ℍ = 4 := by
    simpa using (Quaternion.finrank_eq_four : Module.finrank ℝ ℍ = 4)
  calc
    Module.finrank ℝ 𝕊 = Module.finrank ℝ 𝕆 + Module.finrank ℝ 𝕆 := by
      exact
        (Module.finrank_prod :
          Module.finrank ℝ (𝕆 × 𝕆) = Module.finrank ℝ 𝕆 + Module.finrank ℝ 𝕆)
    _ = 15 + 1 := by
      norm_num [hq]

local instance problem_8_8_finrank_fact : Fact (Module.finrank ℝ 𝕊 = 15 + 1) :=
  ⟨problem_8_8_finrank⟩

/-- A concrete nonzero left zero divisor for the sedenion algebra. -/
def problem_8_8_leftZeroDivisor : 𝕊 :=
  problem_8_8_basisVec 2 + problem_8_8_basisVec 9

/-- A concrete nonzero right zero divisor for the sedenion algebra. -/
def problem_8_8_rightZeroDivisor : 𝕊 :=
  problem_8_8_basisVec 5 - problem_8_8_basisVec 14

/-- The explicit left zero divisor is nonzero. -/
theorem problem_8_8_leftZeroDivisor_ne_zero :
    problem_8_8_leftZeroDivisor ≠ 0 := by
  intro h
  -- Project to the `imK` coordinate where the first octonion component is visibly nonzero.
  have himK : (0 : ℝ) = 1 := by
    simpa [problem_8_8_leftZeroDivisor, problem_8_8_basisVec, problem_8_7_basisVec] using
      congrArg (fun x : 𝕊 ↦ x.1.1.imK) h
  norm_num at himK

/-- The explicit right zero divisor is nonzero. -/
theorem problem_8_8_rightZeroDivisor_ne_zero :
    problem_8_8_rightZeroDivisor ≠ 0 := by
  intro h
  -- Project to the `imJ` coordinate where the first octonion component is visibly nonzero.
  have himJ : (0 : ℝ) = 1 := by
    simpa [problem_8_8_rightZeroDivisor, problem_8_8_basisVec, problem_8_7_basisVec] using
      congrArg (fun x : 𝕊 ↦ x.1.2.imJ) h
  norm_num at himJ

/-- The standard left-multiplication construction on the sedenions has explicit zero
divisors. -/
theorem problem_8_8_zeroDivisor :
    problem_8_8_leftZeroDivisor *ₛ problem_8_8_rightZeroDivisor = 0 := by
  -- Expand the explicit witnesses all the way down to quaternion coordinates.
  apply Prod.ext
  · apply Prod.ext
    · ext <;>
        simp [problem_8_8_leftZeroDivisor, problem_8_8_rightZeroDivisor, problem_8_8_basisVec,
          problem_8_7_basisVec, sedenionMul, octonionMul, octonionStar, sub_eq_add_neg]
    · ext <;>
        simp [problem_8_8_leftZeroDivisor, problem_8_8_rightZeroDivisor, problem_8_8_basisVec,
          problem_8_7_basisVec, sedenionMul, octonionMul, octonionStar, sub_eq_add_neg]
  · apply Prod.ext
    · ext <;>
        simp [problem_8_8_leftZeroDivisor, problem_8_8_rightZeroDivisor, problem_8_8_basisVec,
          problem_8_7_basisVec, sedenionMul, octonionMul, octonionStar, sub_eq_add_neg]
    · ext <;>
        simp [problem_8_8_leftZeroDivisor, problem_8_8_rightZeroDivisor, problem_8_8_basisVec,
          problem_8_7_basisVec, sedenionMul, octonionMul, octonionStar, sub_eq_add_neg]

/-- Helper for Problem 8-8: the explicit right zero divisor is the octonion basis pair
`(problem_8_7_basisVec 5, -problem_8_7_basisVec 6)`. -/
theorem rightZeroDivisor_eq_basisPair :
    problem_8_8_rightZeroDivisor = (problem_8_7_basisVec 5, -problem_8_7_basisVec 6) := by
  -- Expand the two sedenion basis vectors and simplify the coordinatewise subtraction.
  simp [problem_8_8_rightZeroDivisor, problem_8_8_basisVec, sub_eq_add_neg]

/-- Helper for Problem 8-8: each standard octonion basis vector has norm `1`. -/
theorem octonionBasisVec_norm (i : Fin 7) :
    ‖problem_8_7_basisVec i‖ = 1 := by
  have quaternionNorm_eq_one {q : ℍ} (hq : Quaternion.normSq q = 1) : ‖q‖ = 1 := by
    -- Convert the norm-square computation into a norm computation using nonnegativity.
    have hmul : ‖q‖ * ‖q‖ = 1 := by
      simpa [Quaternion.normSq_eq_norm_mul_self] using hq
    nlinarith [norm_nonneg q]
  -- Split into the seven explicit basis vectors and evaluate the product norm case by case.
  fin_cases i
  · have hq : Quaternion.normSq ((⟨0, 1, 0, 0⟩ : ℍ)) = 1 := by
      -- The quaternion unit `i` has norm-square `1`.
      norm_num [Quaternion.normSq_def']
    simpa [problem_8_7_basisVec, Prod.norm_mk] using quaternionNorm_eq_one hq
  · have hq : Quaternion.normSq ((⟨0, 0, 1, 0⟩ : ℍ)) = 1 := by
      -- The quaternion unit `j` has norm-square `1`.
      norm_num [Quaternion.normSq_def']
    simpa [problem_8_7_basisVec, Prod.norm_mk] using quaternionNorm_eq_one hq
  · have hq : Quaternion.normSq ((⟨0, 0, 0, 1⟩ : ℍ)) = 1 := by
      -- The quaternion unit `k` has norm-square `1`.
      norm_num [Quaternion.normSq_def']
    simpa [problem_8_7_basisVec, Prod.norm_mk] using quaternionNorm_eq_one hq
  · simp [problem_8_7_basisVec, Prod.norm_mk]
  · have hq : Quaternion.normSq ((⟨0, 1, 0, 0⟩ : ℍ)) = 1 := by
      -- The second-copy quaternion unit `i` has norm-square `1`.
      norm_num [Quaternion.normSq_def']
    simpa [problem_8_7_basisVec, Prod.norm_mk] using quaternionNorm_eq_one hq
  · have hq : Quaternion.normSq ((⟨0, 0, 1, 0⟩ : ℍ)) = 1 := by
      -- The second-copy quaternion unit `j` has norm-square `1`.
      norm_num [Quaternion.normSq_def']
    simpa [problem_8_7_basisVec, Prod.norm_mk] using quaternionNorm_eq_one hq
  · have hq : Quaternion.normSq ((⟨0, 0, 0, 1⟩ : ℍ)) = 1 := by
      -- The second-copy quaternion unit `k` has norm-square `1`.
      norm_num [Quaternion.normSq_def']
    simpa [problem_8_7_basisVec, Prod.norm_mk] using quaternionNorm_eq_one hq

/-- Helper for Problem 8-8: the explicit right zero divisor has ambient product norm `1`. -/
theorem problem_8_8_rightZeroDivisor_norm :
    ‖problem_8_8_rightZeroDivisor‖ = 1 := by
  -- Rewrite to the stable basis-pair normal form and compute the product norm componentwise.
  rw [rightZeroDivisor_eq_basisPair, Prod.norm_mk, norm_neg, octonionBasisVec_norm,
    octonionBasisVec_norm]
  norm_num

/-- Under the ambient product norm on `𝕊`, the explicit right zero divisor is
already a unit sedenion. -/
def problem_8_8_obstructionPoint : 𝕊 :=
  problem_8_8_rightZeroDivisor

/-- The obstruction point lies on the unit sedenion sphere. -/
theorem problem_8_8_obstructionPoint_mem_unitSedenionSphere :
    problem_8_8_obstructionPoint ∈ unitSedenionSphere := by
  -- Route correction: `𝕊 = 𝕆 × 𝕆` carries the default product norm, so the explicit right zero
  -- divisor already has norm `1` and no `1 / √2` rescaling is needed here.
  rw [show problem_8_8_obstructionPoint = problem_8_8_rightZeroDivisor by rfl]
  rw [mem_sphere_zero_iff_norm]
  exact problem_8_8_rightZeroDivisor_norm

/-- The explicit unit sedenion at which the left-multiplication family satisfies a nontrivial
linear relation. -/
def problem_8_8_obstructionUnit : unitSedenionSphere :=
  ⟨problem_8_8_obstructionPoint, problem_8_8_obstructionPoint_mem_unitSedenionSphere⟩

/-- The sedenionic left-multiplication family has an explicit nontrivial relation at
the unit sedenion coming from the zero-divisor pair. -/
theorem problem_8_8_linearRelation :
    problem_8_8_vectorField 2 problem_8_8_obstructionPoint +
        problem_8_8_vectorField 9 problem_8_8_obstructionPoint = 0 := by
  -- Combine the two basis vectors into the explicit left zero divisor and evaluate at the
  -- explicit right zero divisor.
  unfold problem_8_8_obstructionPoint
  rw [problem_8_8_vectorField_apply, problem_8_8_vectorField_apply, ← sedenionMul_add_left]
  simpa [problem_8_8_leftZeroDivisor, problem_8_8_rightZeroDivisor] using
    problem_8_8_zeroDivisor

/-- The fifteen left-multiplication fields are not linearly independent at the explicit unit
zero-divisor witness. -/
theorem problem_8_8_vectorField_not_linearIndependent :
    ¬ LinearIndependent ℝ
      (fun i : Fin 15 ↦ problem_8_8_vectorField i (problem_8_8_obstructionUnit : 𝕊)) := by
  -- The explicit relation uses only the fields indexed by `2` and `9`.
  refine not_linearIndependent_iff.mpr ?_
  refine ⟨({2, 9} : Finset (Fin 15)), fun _ ↦ (1 : ℝ), ?_, ?_⟩
  · -- The two-point supported sum is exactly the explicit linear relation.
    simp [problem_8_8_linearRelation, problem_8_8_obstructionUnit]
  · refine ⟨2, by simp, by norm_num⟩

section problem_8_8_sphereFrameObstruction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 15)) M]
variable {f : M → 𝕊} {p₀ : M}
variable {e : Fin 15 → (p : M) → TangentSpace (𝓡 15) p}

/-- Helper for Problem 8-8: an injective differential preserves linear independence of the tangent
family at the chosen point. -/
theorem linearIndependent_mfderiv_of_injective
    (hinj :
      Function.Injective
        (mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀))
    (hlin : LinearIndependent ℝ (fun i : Fin 15 ↦ e i p₀)) :
    LinearIndependent ℝ
      (fun i : Fin 15 ↦ mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀ (e i p₀)) := by
  -- Route correction: alias the differential and the source family before calling `map'`,
  -- so the transport proof stays in the small normal form `L ∘ v`.
  let L := (mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀).toLinearMap
  let v : Fin 15 → TangentSpace (𝓡 15) p₀ := fun i ↦ e i p₀
  have hLinj : Function.Injective L := by
    -- The linear-map alias has the same underlying function as the differential.
    simpa [L] using hinj
  have hker : LinearMap.ker L = ⊥ := by
    -- Injectivity of the differential is exactly the trivial-kernel hypothesis for `map'`.
    exact LinearMap.ker_eq_bot_of_injective hLinj
  have hmap : LinearIndependent ℝ (L ∘ v) := by
    -- Apply the standard linear-independence transport lemma in the aliased spelling.
    exact hlin.map' L hker
  -- Unfold the aliases once to recover the original family.
  simpa [L, v, Function.comp] using hmap

/-- Helper for Problem 8-8: the pushed-forward tangent family agrees with the sedenionic
obstruction family at the obstruction point. -/
theorem mfderivFamily_eq_obstructionFamily
    (hp₀ : f p₀ = problem_8_8_obstructionPoint)
    (he : ∀ i : Fin 15,
      mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀ (e i p₀) = problem_8_8_vectorField i (f p₀)) :
    (fun i : Fin 15 ↦ mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀ (e i p₀)) =
      fun i : Fin 15 ↦ problem_8_8_vectorField i (problem_8_8_obstructionUnit : 𝕊) := by
  -- Rewrite the image family from `f p₀` to the explicit obstruction point.
  funext i
  simpa [hp₀, problem_8_8_obstructionUnit] using he i

/-- Problem 8-8: any tangent-bundle realization of the sedenionic left-multiplication family
fails pointwise linear independence at the explicit obstruction point once its ambient pushforward
agrees there with the sedenionic left-multiplication fields and is injective there. The local-frame
obstruction is the immediate corollary via `IsLocalFrameOn.linearIndependent`. -/
theorem problem_8_8_not_linearIndependent_of_mfderiv_eq
    (hp₀ : f p₀ = problem_8_8_obstructionPoint)
    (hinj :
      Function.Injective
        (mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀))
    (he : ∀ i : Fin 15,
      mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀ (e i p₀) = problem_8_8_vectorField i (f p₀)) :
    ¬ LinearIndependent ℝ (fun i : Fin 15 ↦ e i p₀) := by
  intro hlin
  -- Push linear independence through the injective differential and identify the image family.
  have hmap := linearIndependent_mfderiv_of_injective hinj hlin
  have hfamily := mfderivFamily_eq_obstructionFamily hp₀ he
  rw [hfamily] at hmap
  exact problem_8_8_vectorField_not_linearIndependent hmap

end problem_8_8_sphereFrameObstruction

end
