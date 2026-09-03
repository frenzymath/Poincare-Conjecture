import Topping.ParabolicPDE.Nemytskii
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Section-space lift of the local jet map

The finite-dimensional jet evaluator from `Nemytskii.lean` has a direct lift
to bounded continuous functions when the coefficient point and frame are
fixed.  This is the local section-space boundary needed by a later chartwise
DeTurck construction; it deliberately makes no claim about global bundle
gluing or a variable-coefficient manifold operator.
-/

namespace Topping

open scoped BoundedContinuousFunction BigOperators

noncomputable section

variable {X T ι V : Type*} [Fintype ι] [TopologicalSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace VectorSecondOrderCoefficients

variable (A : VectorSecondOrderCoefficients X ι V) (x : X)

/-- Evaluate a fixed local second-order coefficient package on bounded
continuous value, first-jet, and second-jet sections. -/
def sectionApplyJetArgs
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) : T →ᵇ V :=
  (∑ i, ∑ k, BoundedContinuousFunction.comp (A.a x i k)
      (A.a x i k).lipschitz (second i k)) +
    (∑ i, BoundedContinuousFunction.comp (A.b x i)
      (A.b x i).lipschitz (first i)) +
      BoundedContinuousFunction.comp (A.c x) (A.c x).lipschitz value

@[simp] theorem sectionApplyJetArgs_apply
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) (t : T) :
    A.sectionApplyJetArgs x value first second t =
      A.applyJetArgs x (value t) (fun i => first i t)
        (fun i k => second i k t) := by
  simp [sectionApplyJetArgs, applyJetArgs]

/-- The fixed local jet map is continuous on the product of bounded section
spaces. -/
theorem continuous_sectionApplyJetArgs :
    Continuous (fun z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V) =>
      A.sectionApplyJetArgs x z.1 z.2.1 z.2.2) := by
  simp only [sectionApplyJetArgs]
  fun_prop

@[simp] theorem sectionApplyJetArgs_add
    (value₁ value₂ : T →ᵇ V) (first₁ first₂ : ι → T →ᵇ V)
    (second₁ second₂ : ι → ι → T →ᵇ V) :
    A.sectionApplyJetArgs x (value₁ + value₂) (first₁ + first₂)
        (second₁ + second₂) =
      A.sectionApplyJetArgs x value₁ first₁ second₁ +
        A.sectionApplyJetArgs x value₂ first₂ second₂ := by
  ext t
  simp only [sectionApplyJetArgs_apply, BoundedContinuousFunction.add_apply,
    Pi.add_apply]
  change A.applyJetArgs x (value₁ t + value₂ t)
      ((fun i => first₁ i t) + fun i => first₂ i t)
      ((fun i k => second₁ i k t) + fun i k => second₂ i k t) =
    A.applyJetArgs x (value₁ t) (fun i => first₁ i t)
        (fun i k => second₁ i k t) +
      A.applyJetArgs x (value₂ t) (fun i => first₂ i t)
        (fun i k => second₂ i k t)
  exact A.applyJetArgs_add x (value₁ t) (value₂ t)
    (fun i => first₁ i t) (fun i => first₂ i t)
    (fun i k => second₁ i k t) (fun i k => second₂ i k t)

@[simp] theorem sectionApplyJetArgs_smul
    (c : ℝ) (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) :
    A.sectionApplyJetArgs x (c • value) (c • first) (c • second) =
      c • A.sectionApplyJetArgs x value first second := by
  ext t
  simp only [sectionApplyJetArgs_apply, BoundedContinuousFunction.smul_apply,
    Pi.smul_apply]
  exact A.applyJetArgs_smul x c (value t)
    (fun i => first i t) (fun i k => second i k t)

/-! ## Sup-norm and operator packaging -/

/- A fixed coefficient package acts boundedly on the product of bounded
continuous jet sections.  The estimate below is the concrete sup-norm bridge
used when this local map is inserted into a section-space contraction. -/
theorem sectionApplyJetArgs_norm_le
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) :
    ‖A.sectionApplyJetArgs x value first second‖ ≤
      (∑ i, ∑ k, ‖A.a x i k‖ * ‖second i k‖) +
        (∑ i, ‖A.b x i‖ * ‖first i‖) + ‖A.c x‖ * ‖value‖ := by
  let C : ℝ :=
    (∑ i, ∑ k, ‖A.a x i k‖ * ‖second i k‖) +
      (∑ i, ‖A.b x i‖ * ‖first i‖) + ‖A.c x‖ * ‖value‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  change ‖A.sectionApplyJetArgs x value first second‖ ≤ C
  apply (BoundedContinuousFunction.norm_le hC).2
  intro t
  have hA (i k : ι) :
      ‖A.a x i k (second i k t)‖ ≤ ‖A.a x i k‖ * ‖second i k‖ := by
    exact (A.a x i k).le_opNorm_of_le ((second i k).norm_coe_le_norm t)
  have hB (i : ι) :
      ‖A.b x i (first i t)‖ ≤ ‖A.b x i‖ * ‖first i‖ := by
    exact (A.b x i).le_opNorm_of_le ((first i).norm_coe_le_norm t)
  have hCpoint :
      ‖A.c x (value t)‖ ≤ ‖A.c x‖ * ‖value‖ := by
    exact (A.c x).le_opNorm_of_le (value.norm_coe_le_norm t)
  have hAsum :
      ‖∑ i, ∑ k, A.a x i k (second i k t)‖ ≤
        ∑ i, ∑ k, ‖A.a x i k‖ * ‖second i k‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun i hi => ?_)
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun k hk => hA i k))
  have hBsum :
      ‖∑ i, A.b x i (first i t)‖ ≤
        ∑ i, ‖A.b x i‖ * ‖first i‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum (fun i hi => hB i)
  rw [sectionApplyJetArgs_apply]
  calc
    ‖(∑ i, ∑ k, A.a x i k (second i k t)) +
          (∑ i, A.b x i (first i t)) + A.c x (value t)‖
        ≤ ‖∑ i, ∑ k, A.a x i k (second i k t)‖ +
            ‖∑ i, A.b x i (first i t)‖ + ‖A.c x (value t)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (∑ i, ∑ k, ‖A.a x i k‖ * ‖second i k‖) +
          (∑ i, ‖A.b x i‖ * ‖first i‖) + ‖A.c x (value t)‖ := by
          exact add_le_add (add_le_add hAsum hBsum) le_rfl
    _ ≤ C := by
          dsimp [C]
          exact add_le_add (add_le_add le_rfl le_rfl) hCpoint

/- The coefficient norms alone give a uniform operator bound after using the
sup norm on the product of value and jet sections. -/
def sectionApplyJetArgsBound : ℝ :=
  (∑ i, ∑ k, ‖A.a x i k‖) + (∑ i, ‖A.b x i‖) + ‖A.c x‖

theorem sectionApplyJetArgsBound_nonneg :
    0 ≤ A.sectionApplyJetArgsBound x := by
  simp only [sectionApplyJetArgsBound]
  positivity

theorem sectionApplyJetArgs_norm_le_bound_mul
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    ‖A.sectionApplyJetArgs x z.1 z.2.1 z.2.2‖ ≤
      A.sectionApplyJetArgsBound x * ‖z‖ := by
  have hvalue : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hfirst (i : ι) : ‖z.2.1 i‖ ≤ ‖z‖ :=
    (norm_le_pi_norm z.2.1 i).trans
      ((norm_fst_le z.2).trans (norm_snd_le z))
  have hsecond (i k : ι) : ‖z.2.2 i k‖ ≤ ‖z‖ :=
    (norm_le_pi_norm (z.2.2 i) k).trans
      ((norm_le_pi_norm z.2.2 i).trans
        ((norm_snd_le z.2).trans (norm_snd_le z)))
  calc
    ‖A.sectionApplyJetArgs x z.1 z.2.1 z.2.2‖ ≤
        (∑ i, ∑ k, ‖A.a x i k‖ * ‖z.2.2 i k‖) +
          (∑ i, ‖A.b x i‖ * ‖z.2.1 i‖) + ‖A.c x‖ * ‖z.1‖ :=
      A.sectionApplyJetArgs_norm_le x z.1 z.2.1 z.2.2
    _ ≤ (∑ i, ∑ k, ‖A.a x i k‖ * ‖z‖) +
          (∑ i, ‖A.b x i‖ * ‖z‖) + ‖A.c x‖ * ‖z‖ := by
      refine add_le_add (add_le_add ?_ ?_) ?_
      · refine Finset.sum_le_sum (fun i hi => ?_)
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact mul_le_mul_of_nonneg_left (hsecond i k)
          (norm_nonneg (A.a x i k))
      · refine Finset.sum_le_sum (fun i hi => ?_)
        exact mul_le_mul_of_nonneg_left (hfirst i) (norm_nonneg (A.b x i))
      · exact mul_le_mul_of_nonneg_left hvalue (norm_nonneg (A.c x))
    _ = A.sectionApplyJetArgsBound x * ‖z‖ := by
      simp only [sectionApplyJetArgsBound, add_mul, Finset.sum_mul]

/-! The fixed-coefficient section evaluator is a continuous linear map in its
three section variables. -/
def sectionApplyJetArgsLinearMap :
    ((T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) →ₗ[ℝ] (T →ᵇ V) where
  toFun z := A.sectionApplyJetArgs x z.1 z.2.1 z.2.2
  map_add' z w := by
    ext t
    simp [sectionApplyJetArgs_apply, Pi.add_apply]
  map_smul' r z := by
    ext t
    simp [sectionApplyJetArgs_apply]

def sectionApplyJetArgsCLM :
    ((T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) →L[ℝ] (T →ᵇ V) :=
  (A.sectionApplyJetArgsLinearMap x).mkContinuous
    (A.sectionApplyJetArgsBound x)
    (A.sectionApplyJetArgs_norm_le_bound_mul x)

@[simp] theorem sectionApplyJetArgsCLM_apply
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    A.sectionApplyJetArgsCLM x z =
      A.sectionApplyJetArgs x z.1 z.2.1 z.2.2 := rfl

theorem continuous_sectionApplyJetArgsCLM :
    Continuous (A.sectionApplyJetArgsCLM (T := T) x) :=
  (A.sectionApplyJetArgsCLM (T := T) x).continuous

theorem norm_sectionApplyJetArgsCLM_le :
    ‖A.sectionApplyJetArgsCLM (T := T) x‖ ≤ A.sectionApplyJetArgsBound x := by
  exact LinearMap.mkContinuous_norm_le _
    (A.sectionApplyJetArgsBound_nonneg x)
    (A.sectionApplyJetArgs_norm_le_bound_mul x)

end VectorSecondOrderCoefficients

end
end Topping
