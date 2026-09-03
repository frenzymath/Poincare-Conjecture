import MorganTianLib.Ch03.RicciFlow.VolumeDistortion

/-!
# Morgan--Tian Ch. 3 - Bianchi identity for the quadratic reaction

This module isolates the finite-index algebra behind the remark that the two
curvature-operator squares need not separately satisfy Bianchi, while their
sum does.  The input is an honest algebraic curvature tensor (all curvature
symmetries are explicit); no target-shaped evolution hypothesis is used.
-/

open scoped BigOperators

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

/-- **Math.** The contraction called `B` in the frame computation. -/
def quadraticCurvatureB {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → ℝ) (a b c d : ι) : ℝ :=
  ∑ e, ∑ f, R a e b f * R c e d f

/-- **Math.** The component tensor represented by the operator square `T²`. -/
def curvatureOperatorSquareTensor {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → ℝ) (a b c d : ι) : ℝ :=
  ∑ e, ∑ f, R a b e f * R c d e f

/-- **Math.** The component tensor represented by the Lie-algebra square `T^sharp`. -/
def curvatureOperatorSharpTensor {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → ℝ) (a b c d : ι) : ℝ :=
  2 * (quadraticCurvatureB R a c b d - quadraticCurvatureB R a d b c)

/-- **Math.** The quadratic reaction tensor in the evolving orthonormal frame. -/
def curvatureOperatorReactionTensor {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → ℝ) (a b c d : ι) : ℝ :=
  curvatureOperatorSquareTensor R a b c d +
    curvatureOperatorSharpTensor R a b c d

theorem curvatureOperatorSquareTensor_eq_two_sub
    {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → ℝ)
    (hanti₃₄ : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0)
    (a b c d : ι) :
    curvatureOperatorSquareTensor R a b c d =
      2 * (quadraticCurvatureB R a b c d - quadraticCurvatureB R a b d c) := by
  classical
  unfold curvatureOperatorSquareTensor quadraticCurvatureB
  calc
    (∑ e, ∑ f, R a b e f * R c d e f) =
        ∑ e, ∑ f, -(R a b e f * (R c e f d + R c f d e)) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      refine Finset.sum_congr rfl ?_
      intro f hf
      have h := hbianchi c d e f
      linear_combination (R a b e f) * h
    _ = 2 * (∑ e, ∑ f, R a b e f * R c e d f) := by
      have sum_neg_two (F : ι → ι → ℝ) :
          (∑ e, ∑ f, -(F e f)) = -(∑ e, ∑ f, F e f) := by
        calc
          (∑ e, ∑ f, -(F e f)) = ∑ e, -(∑ f, F e f) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            exact
              (Finset.sum_neg_distrib (s := (Finset.univ : Finset ι))
                (f := fun f => F e f))
          _ = -(∑ e, ∑ f, F e f) := by
            simpa only using
              (Finset.sum_neg_distrib (s := (Finset.univ : Finset ι))
                (f := fun e => ∑ f, F e f))
      have hswap :
          (∑ e, ∑ f, R a b e f * R c f d e) =
            -(∑ e, ∑ f, R a b e f * R c e d f) := by
        calc
          (∑ e, ∑ f, R a b e f * R c f d e) =
              ∑ f, ∑ e, R a b f e * R c e d f := by
            rw [Finset.sum_comm]
          _ = ∑ f, ∑ e, -(R a b e f * R c e d f) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            refine Finset.sum_congr rfl ?_
            intro e he
            rw [hanti₃₄ a b f e]
            ring
          _ = -(∑ f, ∑ e, R a b e f * R c e d f) := by
            simp only [Finset.sum_neg_distrib]
          _ = -(∑ e, ∑ f, R a b e f * R c e d f) := by
            congr 1
            exact Finset.sum_comm
      simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, mul_add,
        neg_add]
      have hfirst :
          (∑ e, ∑ f, -(R a b e f * R c e f d)) =
            ∑ e, ∑ f, R a b e f * R c e d f := by
        refine Finset.sum_congr rfl ?_
        intro e he
        refine Finset.sum_congr rfl ?_
        intro f hf
        rw [hanti₃₄ c e f d]
        ring
      have hsecond :
          (∑ e, ∑ f, -(R a b e f * R c f d e)) =
            ∑ e, ∑ f, R a b e f * R c e d f := by
        calc
          (∑ e, ∑ f, -(R a b e f * R c f d e)) =
              -(∑ e, ∑ f, R a b e f * R c f d e) := by
            exact sum_neg_two _
          _ = ∑ e, ∑ f, R a b e f * R c e d f := by
            rw [hswap]
            ring
      have hfirst' :
          -(∑ e, ∑ f, R a b e f * R c e f d) =
            ∑ e, ∑ f, R a b e f * R c e d f := by
        rw [← sum_neg_two]
        exact hfirst
      have hsecond' :
          -(∑ e, ∑ f, R a b e f * R c f d e) =
            ∑ e, ∑ f, R a b e f * R c e d f := by
        rw [← sum_neg_two]
        exact hsecond
      rw [hfirst', hsecond']
      ring
    _ = 2 * ((∑ e, ∑ f, R a e b f * R c e d f) -
        ∑ e, ∑ f, R a e b f * R d e c f) := by
      have hdecomp :
          (∑ e, ∑ f, R a b e f * R c e d f) =
            ∑ e, ∑ f, -(R a e f b * R c e d f +
              R a f b e * R c e d f) := by
        refine Finset.sum_congr rfl ?_
        intro e he
        refine Finset.sum_congr rfl ?_
        intro f hf
        have h := hbianchi a b e f
        linear_combination (R c e d f) * h
      have hpart₁ :
          (∑ e, ∑ f, -(R a e f b * R c e d f)) =
            ∑ e, ∑ f, R a e b f * R c e d f := by
        refine Finset.sum_congr rfl ?_
        intro e he
        refine Finset.sum_congr rfl ?_
        intro f hf
        rw [hanti₃₄ a e f b]
        ring
      have hpart₂ :
          (∑ e, ∑ f, -(R a f b e * R c e d f)) =
            -(∑ e, ∑ f, R a e b f * R d e c f) := by
        have sum_neg_two' (F : ι → ι → ℝ) :
            (∑ e, ∑ f, -(F e f)) = -(∑ e, ∑ f, F e f) := by
          calc
            (∑ e, ∑ f, -(F e f)) = ∑ e, -(∑ f, F e f) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              simpa only using
                (Finset.sum_neg_distrib (s := (Finset.univ : Finset ι))
                  (f := fun f => F e f))
            _ = -(∑ e, ∑ f, F e f) := by
              simpa only using
                (Finset.sum_neg_distrib (s := (Finset.univ : Finset ι))
                  (f := fun e => ∑ f, F e f))
        calc
          (∑ e, ∑ f, -(R a f b e * R c e d f)) =
              -(∑ e, ∑ f, R a f b e * R c e d f) := by
            exact sum_neg_two' _
          _ = -(∑ e, ∑ f, R a e b f * R d e c f) := by
            congr 1
            calc
              (∑ e, ∑ f, R a f b e * R c e d f) =
                  ∑ f, ∑ e, R a f b e * R c e d f := by
                exact Finset.sum_comm
              _ = ∑ f, ∑ e, R a f b e * R d f c e := by
                refine Finset.sum_congr rfl ?_
                intro f hf
                refine Finset.sum_congr rfl ?_
                intro e he
                rw [hpair c e d f]
              _ = ∑ e, ∑ f, R a e b f * R d e c f := by
                rw [Finset.sum_comm]
      rw [hdecomp]
      have hsplit :
          (∑ e, ∑ f, -(R a e f b * R c e d f +
            R a f b e * R c e d f)) =
            (∑ e, ∑ f, -(R a e f b * R c e d f)) +
              ∑ e, ∑ f, -(R a f b e * R c e d f) := by
        calc
          (∑ e, ∑ f, -(R a e f b * R c e d f +
              R a f b e * R c e d f)) =
              ∑ e, ∑ f, (-(R a e f b * R c e d f) +
                -(R a f b e * R c e d f)) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            refine Finset.sum_congr rfl ?_
            intro f hf
            ring
          _ = (∑ e, ∑ f, -(R a e f b * R c e d f)) +
              ∑ e, ∑ f, -(R a f b e * R c e d f) := by
            calc
              (∑ e, ∑ f, (-(R a e f b * R c e d f) +
                -(R a f b e * R c e d f))) =
                  ∑ e, ((∑ f, -(R a e f b * R c e d f)) +
                    ∑ f, -(R a f b e * R c e d f)) := by
                refine Finset.sum_congr rfl ?_
                intro e he
                rw [Finset.sum_add_distrib]
              _ = (∑ e, ∑ f, -(R a e f b * R c e d f)) +
                  ∑ e, ∑ f, -(R a f b e * R c e d f) := by
                rw [Finset.sum_add_distrib]
      rw [hsplit, hpart₁, hpart₂]
      ring

/-- **Math.** The curvature-operator reaction is the explicit quadratic
expression used by the finite-index moving-frame computation. -/
theorem curvatureOperatorReactionTensor_eq_shiFrameQuadratic
    {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → ℝ)
    (hanti₃₄ : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0)
    (a b c d : ι) :
    curvatureOperatorReactionTensor R a b c d =
      2 * (quadraticCurvatureB R a b c d + quadraticCurvatureB R a c b d
        - quadraticCurvatureB R a b d c - quadraticCurvatureB R a d b c) := by
  classical
  unfold curvatureOperatorReactionTensor curvatureOperatorSharpTensor
  rw [curvatureOperatorSquareTensor_eq_two_sub R hanti₃₄ hpair hbianchi]
  ring

theorem curvatureOperatorReactionTensor_bianchi
    {ι : Type*} [Fintype ι]
    (R : ι → ι → ι → ι → ℝ)
    (hanti₃₄ : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0)
    (a b c d : ι) :
    curvatureOperatorReactionTensor R a b c d +
        curvatureOperatorReactionTensor R a c d b +
        curvatureOperatorReactionTensor R a d b c = 0 := by
  classical
  unfold curvatureOperatorReactionTensor curvatureOperatorSharpTensor
  rw [curvatureOperatorSquareTensor_eq_two_sub R hanti₃₄ hpair hbianchi]
  rw [curvatureOperatorSquareTensor_eq_two_sub R hanti₃₄ hpair hbianchi]
  rw [curvatureOperatorSquareTensor_eq_two_sub R hanti₃₄ hpair hbianchi]
  unfold quadraticCurvatureB
  ring

#print axioms curvatureOperatorReactionTensor_eq_shiFrameQuadratic

end MorganTianLib
