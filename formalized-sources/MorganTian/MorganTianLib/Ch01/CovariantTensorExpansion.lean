import MorganTianLib.Ch01.PointwiseCurvature

/-!
# Morgan--Tian Ch. 1: pointwise finite expansion of covariant four-tensors

This module packages the finite-dimensional basis expansion shared by the
curvature tensor and its Ricci-flow variation.  It uses only tensoriality and
pointwise locality, so no curvature symmetries are required.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Evaluating a covariant four-tensor on four finite linear
combinations of tangent vectors expands quadrilinearly.  This is the generic
pointwise form of the chart-frame expansion used for curvature components.
Blueprint: `def:riemann-curvature-tensor` (tensoriality infrastructure). -/
theorem covariantTensor4At_sum₄
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T) (p : M) {ι : Type*} (s : Finset ι)
    (cv cw cz ct : ι → ℝ) (e : ι → TangentSpace I p) :
    T (extendVector p (∑ a ∈ s, cv a • e a))
        (extendVector p (∑ b ∈ s, cw b • e b))
        (extendVector p (∑ c ∈ s, cz c • e c))
        (extendVector p (∑ d ∈ s, ct d • e d)) p =
      ∑ a ∈ s, cv a * ∑ b ∈ s, cw b * ∑ c ∈ s, cz c * ∑ d ∈ s, ct d *
        T (extendVector p (e a)) (extendVector p (e b))
          (extendVector p (e c)) (extendVector p (e d)) p := by
  classical
  have hzero₁ (y z w : TangentSpace I p) :
      T (extendVector p 0) (extendVector p y) (extendVector p z) (extendVector p w) p = 0 := by
    have hcmp :
        T (extendVector p 0) (extendVector p y) (extendVector p z) (extendVector p w) p =
          T (SmoothVectorField.smul (fun _ : M => (0 : ℝ)) contMDiff_const
              (extendVector p 0))
            (extendVector p y) (extendVector p z) (extendVector p w) p := by
      apply covariantTensor4_congr_apply T hT <;> simp
    rw [hcmp, hT.smul₁]
    simp
  have hzero₂ (x z w : TangentSpace I p) :
      T (extendVector p x) (extendVector p 0) (extendVector p z) (extendVector p w) p = 0 := by
    have hcmp :
        T (extendVector p x) (extendVector p 0) (extendVector p z) (extendVector p w) p =
          T (extendVector p x)
            (SmoothVectorField.smul (fun _ : M => (0 : ℝ)) contMDiff_const
              (extendVector p 0))
            (extendVector p z) (extendVector p w) p := by
      apply covariantTensor4_congr_apply T hT <;> simp
    rw [hcmp, hT.smul₂]
    simp
  have hzero₃ (x y w : TangentSpace I p) :
      T (extendVector p x) (extendVector p y) (extendVector p 0) (extendVector p w) p = 0 := by
    have hcmp :
        T (extendVector p x) (extendVector p y) (extendVector p 0) (extendVector p w) p =
          T (extendVector p x) (extendVector p y)
            (SmoothVectorField.smul (fun _ : M => (0 : ℝ)) contMDiff_const
              (extendVector p 0))
            (extendVector p w) p := by
      apply covariantTensor4_congr_apply T hT <;> simp
    rw [hcmp, hT.smul₃]
    simp
  have hzero₄ (x y z : TangentSpace I p) :
      T (extendVector p x) (extendVector p y) (extendVector p z) (extendVector p 0) p = 0 := by
    have hcmp :
        T (extendVector p x) (extendVector p y) (extendVector p z) (extendVector p 0) p =
          T (extendVector p x) (extendVector p y) (extendVector p z)
            (SmoothVectorField.smul (fun _ : M => (0 : ℝ)) contMDiff_const
              (extendVector p 0)) p := by
      apply covariantTensor4_congr_apply T hT <;> simp
    rw [hcmp, hT.smul₄]
    simp
  have h₁ : ∀ (u : Finset ι) (y z w : TangentSpace I p),
      T (extendVector p (∑ a ∈ u, cv a • e a))
          (extendVector p y) (extendVector p z) (extendVector p w) p =
        ∑ a ∈ u, cv a * T (extendVector p (e a))
          (extendVector p y) (extendVector p z) (extendVector p w) p := by
    intro u y z w
    induction u using Finset.induction_on with
    | empty => simpa using hzero₁ y z w
    | @insert a u' ha ih =>
      rw [Finset.sum_insert ha]
      have hcmp :
          T (extendVector p (cv a • e a + ∑ b ∈ u', cv b • e b))
              (extendVector p y) (extendVector p z) (extendVector p w) p =
            T (SmoothVectorField.smul (fun _ : M => cv a) contMDiff_const
                (extendVector p (e a)) +
                extendVector p (∑ b ∈ u', cv b • e b))
              (extendVector p y) (extendVector p z) (extendVector p w) p := by
        apply covariantTensor4_congr_apply T hT <;> simp
      rw [hcmp, hT.add₁, hT.smul₁, ih, Finset.sum_insert ha]
  have h₂ : ∀ (u : Finset ι) (x z w : TangentSpace I p),
      T (extendVector p x) (extendVector p (∑ b ∈ u, cw b • e b))
          (extendVector p z) (extendVector p w) p =
        ∑ b ∈ u, cw b * T (extendVector p x) (extendVector p (e b))
          (extendVector p z) (extendVector p w) p := by
    intro u x z w
    induction u using Finset.induction_on with
    | empty => simpa using hzero₂ x z w
    | @insert b u' hb ih =>
      rw [Finset.sum_insert hb]
      have hcmp :
          T (extendVector p x)
              (extendVector p (cw b • e b + ∑ c ∈ u', cw c • e c))
              (extendVector p z) (extendVector p w) p =
            T (extendVector p x)
              (SmoothVectorField.smul (fun _ : M => cw b) contMDiff_const
                (extendVector p (e b)) +
                extendVector p (∑ c ∈ u', cw c • e c))
              (extendVector p z) (extendVector p w) p := by
        apply covariantTensor4_congr_apply T hT <;> simp
      rw [hcmp, hT.add₂, hT.smul₂, ih, Finset.sum_insert hb]
  have h₃ : ∀ (u : Finset ι) (x y w : TangentSpace I p),
      T (extendVector p x) (extendVector p y)
          (extendVector p (∑ c ∈ u, cz c • e c)) (extendVector p w) p =
        ∑ c ∈ u, cz c * T (extendVector p x) (extendVector p y)
          (extendVector p (e c)) (extendVector p w) p := by
    intro u x y w
    induction u using Finset.induction_on with
    | empty => simpa using hzero₃ x y w
    | @insert c u' hc ih =>
      rw [Finset.sum_insert hc]
      have hcmp :
          T (extendVector p x) (extendVector p y)
              (extendVector p (cz c • e c + ∑ d ∈ u', cz d • e d))
              (extendVector p w) p =
            T (extendVector p x) (extendVector p y)
              (SmoothVectorField.smul (fun _ : M => cz c) contMDiff_const
                (extendVector p (e c)) +
                extendVector p (∑ d ∈ u', cz d • e d))
              (extendVector p w) p := by
        apply covariantTensor4_congr_apply T hT <;> simp
      rw [hcmp, hT.add₃, hT.smul₃, ih, Finset.sum_insert hc]
  have h₄ : ∀ (u : Finset ι) (x y z : TangentSpace I p),
      T (extendVector p x) (extendVector p y) (extendVector p z)
          (extendVector p (∑ d ∈ u, ct d • e d)) p =
        ∑ d ∈ u, ct d * T (extendVector p x) (extendVector p y)
          (extendVector p z) (extendVector p (e d)) p := by
    intro u x y z
    induction u using Finset.induction_on with
    | empty => simpa using hzero₄ x y z
    | @insert d u' hd ih =>
      rw [Finset.sum_insert hd]
      have hcmp :
          T (extendVector p x) (extendVector p y) (extendVector p z)
              (extendVector p (ct d • e d + ∑ a ∈ u', ct a • e a)) p =
            T (extendVector p x) (extendVector p y) (extendVector p z)
              (SmoothVectorField.smul (fun _ : M => ct d) contMDiff_const
                (extendVector p (e d)) +
                extendVector p (∑ a ∈ u', ct a • e a)) p := by
        apply covariantTensor4_congr_apply T hT <;> simp
      rw [hcmp, hT.add₄, hT.smul₄, ih, Finset.sum_insert hd]
  rw [h₁ s]
  simp_rw [h₂ s, h₃ s, h₄ s]

end MorganTianLib

end

#print axioms MorganTianLib.covariantTensor4At_sum₄
