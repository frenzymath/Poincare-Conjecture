import MorganTianLib.Ch03.RicciFlow.BianchiOperatorSquares

/-!
# Morgan--Tian Ch. 3 - counterexamples for the individual quadratic terms

The chapter remark says that the square and sharp terms need not separately
obey Bianchi.  This file gives a concrete four-dimensional algebraic curvature
tensor witnessing both failures.  The tensor is a sum of two
Kulkarni--Nomizu products of symmetric forms, so its curvature symmetries are
proved structurally rather than assumed.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MorganTianLib

local notation "ι" => Fin 4
local notation "Mat" => Matrix ι ι ℝ

/-- **Math.** The Kulkarni--Nomizu product of two bilinear forms. -/
def kulkarniNomizu (A B : Mat) (a b c d : ι) : ℝ :=
  A a c * B b d + A b d * B a c - A a d * B b c - A b c * B a d

theorem kulkarniNomizu_antisymm₃₄ (A B : Mat) (a b c d : ι) :
    kulkarniNomizu A B a b c d = -kulkarniNomizu A B a b d c := by
  unfold kulkarniNomizu
  ring

theorem kulkarniNomizu_pairSwap (A B : Mat)
    (hA : A.IsSymm) (hB : B.IsSymm) (a b c d : ι) :
    kulkarniNomizu A B a b c d = kulkarniNomizu A B c d a b := by
  unfold kulkarniNomizu
  have hac : A a c = A c a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA a) c).symm
  have hbd : B b d = B d b := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB b) d).symm
  have had : A a d = A d a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA a) d).symm
  have hbc : B b c = B c b := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB b) c).symm
  have hca : A c a = A a c := hac.symm
  have hdb : B d b = B b d := hbd.symm
  have hda : A d a = A a d := had.symm
  have hcb : B c b = B b c := hbc.symm
  have hdb' : A d b = A b d := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA d) b).symm
  have hca' : B c a = B a c := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB c) a).symm
  have hda' : B d a = B a d := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB d) a).symm
  have hcb' : A c b = A b c := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA c) b).symm
  rw [hac, hbd, had, hbc, hca, hdb, hda, hcb, hdb', hca', hda', hcb']
  ring

theorem kulkarniNomizu_bianchi (A B : Mat)
    (hA : A.IsSymm) (hB : B.IsSymm) (a b c d : ι) :
    kulkarniNomizu A B a b c d +
        kulkarniNomizu A B a c d b +
        kulkarniNomizu A B a d b c = 0 := by
  unfold kulkarniNomizu
  have hac : A a c = A c a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA a) c).symm
  have hab : A a b = A b a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA a) b).symm
  have had : A a d = A d a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA a) d).symm
  have hbc : B b c = B c b := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB b) c).symm
  have hbd : B b d = B d b := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB b) d).symm
  have hcd : B c d = B d c := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB c) d).symm
  have hdb : A d b = A b d := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA d) b).symm
  have hcb : A c b = A b c := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA c) b).symm
  have hdc : A d c = A c d := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hA d) c).symm
  have hca : B a c = B c a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB a) c).symm
  have hda : B a d = B d a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB a) d).symm
  have hba : B a b = B b a := by
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hB a) b).symm
  rw [hac, hab, had, hbc, hbd, hcd, hdb, hcb, hdc, hca, hda, hba]
  ring

def D0 : Mat := !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def D1 : Mat := !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def O02 : Mat := !![0, 0, 1, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0]
def O13 : Mat := !![0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 1, 0, 0]

/-- **Math.** A sparse four-dimensional algebraic curvature tensor. -/
def bianchiCounterexample (a b c d : ι) : ℝ :=
  -kulkarniNomizu D0 D1 a b c d - kulkarniNomizu O02 O13 a b c d

theorem D0_isSymm : D0.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem D1_isSymm : D1.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem O02_isSymm : O02.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem O13_isSymm : O13.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem bianchiCounterexample_antisymm₃₄ (a b c d : ι) :
    bianchiCounterexample a b c d = -bianchiCounterexample a b d c := by
  have h1 := kulkarniNomizu_antisymm₃₄ D0 D1 a b c d
  have h2 := kulkarniNomizu_antisymm₃₄ O02 O13 a b c d
  unfold bianchiCounterexample
  linear_combination -h1 -h2

theorem bianchiCounterexample_pairSwap (a b c d : ι) :
    bianchiCounterexample a b c d = bianchiCounterexample c d a b := by
  unfold bianchiCounterexample
  rw [kulkarniNomizu_pairSwap D0 D1 D0_isSymm D1_isSymm,
    kulkarniNomizu_pairSwap O02 O13 O02_isSymm O13_isSymm]

theorem bianchiCounterexample_bianchi (a b c d : ι) :
    bianchiCounterexample a b c d + bianchiCounterexample a c d b +
        bianchiCounterexample a d b c = 0 := by
  unfold bianchiCounterexample
  have h1 := kulkarniNomizu_bianchi D0 D1 D0_isSymm D1_isSymm a b c d
  have h2 := kulkarniNomizu_bianchi O02 O13 O02_isSymm O13_isSymm a b c d
  linear_combination -h1 -h2

theorem bianchiCounterexample_square_defect :
    curvatureOperatorSquareTensor bianchiCounterexample 0 1 2 3 +
        curvatureOperatorSquareTensor bianchiCounterexample 0 2 3 1 +
        curvatureOperatorSquareTensor bianchiCounterexample 0 3 1 2 = 2 := by
  unfold curvatureOperatorSquareTensor bianchiCounterexample kulkarniNomizu
  norm_num [Fin.sum_univ_four, D0, D1, O02, O13,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem bianchiCounterexample_sharp_defect :
    curvatureOperatorSharpTensor bianchiCounterexample 0 1 2 3 +
        curvatureOperatorSharpTensor bianchiCounterexample 0 2 3 1 +
        curvatureOperatorSharpTensor bianchiCounterexample 0 3 1 2 = -2 := by
  unfold curvatureOperatorSharpTensor quadraticCurvatureB
  unfold bianchiCounterexample kulkarniNomizu
  norm_num [Fin.sum_univ_four, D0, D1, O02, O13,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

end MorganTianLib
