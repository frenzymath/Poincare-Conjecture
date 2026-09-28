import HanLinLectureNotes.Basic

/-!
# Chapter 2: elementary counterexamples

Explicit planar examples showing why boundedness and the sign condition on the
zeroth-order coefficient matter in the Dirichlet maximum principle.
-/

open Set Topology

namespace HanLinLectureNotes

noncomputable section

/-- The coordinate Laplacian on functions of two real variables. -/
def laplacianTwo (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => deriv (fun x' => u (x', p.2)) x) p.1 +
    deriv (fun y => deriv (fun y' => u (p.1, y')) y) p.2

/-- The open square `(0, pi)^2`. -/
def openPiSquare : Set (ℝ × ℝ) :=
  Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 Real.pi

/-- The product of the two sine coordinates. -/
def sineProduct (p : ℝ × ℝ) : ℝ :=
  Real.sin p.1 * Real.sin p.2

/-- The upper half-plane, written as a product. -/
def upperHalfPlane : Set (ℝ × ℝ) :=
  Set.univ ×ˢ Set.Ioi 0

/-- The height coordinate on the upper half-plane. -/
def heightFunction (p : ℝ × ℝ) : ℝ :=
  p.2

theorem laplacianTwo_sineProduct (p : ℝ × ℝ) :
    laplacianTwo sineProduct p = -2 * sineProduct p := by
  have hdx : (fun x => deriv (fun x' => sineProduct (x', p.2)) x) =
      fun x => Real.cos x * Real.sin p.2 := by
    funext x
    exact (Real.hasDerivAt_sin x).mul_const (Real.sin p.2) |>.deriv
  have hdy : (fun y => deriv (fun y' => sineProduct (p.1, y')) y) =
      fun y => Real.sin p.1 * Real.cos y := by
    funext y
    exact (Real.hasDerivAt_sin y).const_mul (Real.sin p.1) |>.deriv
  rw [laplacianTwo, hdx, hdy]
  rw [((Real.hasDerivAt_cos p.1).mul_const (Real.sin p.2)).deriv]
  rw [((Real.hasDerivAt_cos p.2).const_mul (Real.sin p.1)).deriv]
  simp only [sineProduct]
  ring

theorem sineProduct_ne_zero : sineProduct ≠ 0 := by
  intro h
  have hp := congrFun h (Real.pi / 2, Real.pi / 2)
  simp [sineProduct, Real.sin_pi_div_two] at hp

theorem sineProduct_eq_zero_on_frontier :
    Set.EqOn sineProduct 0 (frontier openPiSquare) := by
  rw [openPiSquare, frontier_prod_eq, closure_Ioo (ne_of_lt Real.pi_pos),
    frontier_Ioo Real.pi_pos]
  rintro ⟨x, y⟩ (hp | hp)
  · rcases hp.2 with (rfl | rfl)
    · simp [sineProduct]
    · simp [sineProduct, Real.sin_pi]
  · rcases hp.1 with (rfl | rfl)
    · simp [sineProduct]
    · simp [sineProduct, Real.sin_pi]

/-- On `(0, pi)^2`, `sin x * sin y` is a nonzero solution of
`Delta u + 2u = 0` with zero boundary values. -/
theorem sineProduct_square_counterexample :
    sineProduct ≠ 0 ∧
      (∀ p ∈ openPiSquare, laplacianTwo sineProduct p + 2 * sineProduct p = 0) ∧
      Set.EqOn sineProduct 0 (frontier openPiSquare) := by
  refine ⟨sineProduct_ne_zero, ?_, sineProduct_eq_zero_on_frontier⟩
  intro p hp
  rw [laplacianTwo_sineProduct]
  ring

theorem laplacianTwo_heightFunction (p : ℝ × ℝ) :
    laplacianTwo heightFunction p = 0 := by
  have hx : (fun x => deriv (fun x' => heightFunction (x', p.2)) x) = 0 := by
    funext x
    exact (hasDerivAt_const x (c := p.2)).deriv
  have hy : (fun y => deriv (fun y' => heightFunction (p.1, y')) y) =
      fun _ => 1 := by
    funext y
    exact (hasDerivAt_id y).deriv
  rw [laplacianTwo, hx, hy]
  simp

theorem heightFunction_ne_zero : heightFunction ≠ 0 := by
  intro h
  have hp := congrFun h (0, 1)
  norm_num [heightFunction] at hp

theorem heightFunction_eq_zero_on_frontier :
    Set.EqOn heightFunction 0 (frontier upperHalfPlane) := by
  rw [upperHalfPlane, frontier_prod_eq, closure_univ, frontier_univ,
    frontier_Ioi, Set.empty_prod, Set.union_empty]
  rintro ⟨x, y⟩ hp
  simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_singleton_iff] at hp
  simp [heightFunction, hp]

theorem isOpen_upperHalfPlane : IsOpen upperHalfPlane :=
  isOpen_univ.prod isOpen_Ioi

theorem upperHalfPlane_not_isBounded :
    ¬ Bornology.IsBounded upperHalfPlane := by
  intro h
  rcases isBounded_iff_forall_norm_le.mp h with ⟨C, hC⟩
  have hp : (0, |C| + 1) ∈ upperHalfPlane := by
    refine ⟨Set.mem_univ 0, ?_⟩
    change 0 < |C| + 1
    positivity
  have hle := hC (0, |C| + 1) hp
  rw [Prod.norm_def] at hle
  norm_num [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ |C| + 1)] at hle
  linarith [le_abs_self C]

theorem isOpen_openPiSquare : IsOpen openPiSquare :=
  isOpen_Ioo.prod isOpen_Ioo

theorem isBounded_openPiSquare : Bornology.IsBounded openPiSquare :=
  (Metric.isBounded_Ioo 0 Real.pi).prod (Metric.isBounded_Ioo 0 Real.pi)

/-- Dirichlet uniqueness can fail on an unbounded domain even when `c = 0`,
and on a bounded domain when the zeroth-order coefficient is positive. -/
theorem dirichlet_uniqueness_counterexamples :
    (IsOpen upperHalfPlane ∧ ¬ Bornology.IsBounded upperHalfPlane ∧
      heightFunction ≠ 0 ∧
      (∀ p ∈ upperHalfPlane, laplacianTwo heightFunction p = 0) ∧
      Set.EqOn heightFunction 0 (frontier upperHalfPlane)) ∧
    (IsOpen openPiSquare ∧ Bornology.IsBounded openPiSquare ∧ (0 : ℝ) < 2 ∧
      sineProduct ≠ 0 ∧
      (∀ p ∈ openPiSquare, laplacianTwo sineProduct p + 2 * sineProduct p = 0) ∧
      Set.EqOn sineProduct 0 (frontier openPiSquare)) := by
  refine ⟨⟨isOpen_upperHalfPlane, upperHalfPlane_not_isBounded,
    heightFunction_ne_zero, ?_, heightFunction_eq_zero_on_frontier⟩,
    isOpen_openPiSquare, isBounded_openPiSquare, by norm_num,
    sineProduct_square_counterexample⟩
  exact fun p _ => laplacianTwo_heightFunction p

/-- The open unit interval used for the homogeneous Neumann counterexample. -/
def openUnitInterval : Set Real :=
  Set.Ioo 0 1

/-- The one-dimensional Laplacian. -/
def intervalLaplacian (u : Real -> Real) (x : Real) : Real :=
  deriv (deriv u) x

/-- The outward normal derivative at the endpoints of the unit interval. -/
def intervalOutwardNormalDerivative (u : Real -> Real) (x : Real) : Real :=
  if x = 0 then -deriv u x else deriv u x

/-- Han--Lin Remark 2.26. A merely nonnegative Robin coefficient does not give
uniqueness or a zero-data a priori estimate: for `alpha = 0`, both constant
functions solve the same homogeneous Neumann problem, and one is nonzero. -/
theorem zero_robin_coefficient_nonunique :
    IsOpen openUnitInterval ∧
      IsConnected openUnitInterval ∧
      Bornology.IsBounded openUnitInterval ∧
      ∃ (alpha : Real) (u v : Real -> Real),
        alpha = 0 ∧ 0 <= alpha ∧ u ≠ v ∧
        ContDiff Real 2 u ∧ ContDiff Real 2 v ∧
        (∀ x ∈ openUnitInterval, intervalLaplacian u x = 0) ∧
        (∀ x ∈ openUnitInterval, intervalLaplacian v x = 0) ∧
        (∀ x ∈ frontier openUnitInterval,
          intervalOutwardNormalDerivative u x + alpha * u x = 0) ∧
        (∀ x ∈ frontier openUnitInterval,
          intervalOutwardNormalDerivative v x + alpha * v x = 0) ∧
        ∃ x ∈ openUnitInterval, 0 < |v x| := by
  refine ⟨isOpen_Ioo, isConnected_Ioo (by norm_num), Metric.isBounded_Ioo 0 1, ?_⟩
  refine ⟨0, (fun _ => 0), (fun _ => 1), rfl, le_rfl, ?_, contDiff_const,
    contDiff_const, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · intro x hx
    simp [intervalLaplacian]
  · intro x hx
    simp [intervalLaplacian]
  · intro x hx
    simp [intervalOutwardNormalDerivative]
  · intro x hx
    simp [intervalOutwardNormalDerivative]
  · exact ⟨1 / 2, by norm_num [openUnitInterval], by norm_num⟩

end

end HanLinLectureNotes
