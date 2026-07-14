import PetersenLib.Ch03.CurvaturePointwise

/-!
# Petersen Ch. 3, §3.2.1 — Curvature equations by dimension

The remark `rem:pet-ch3-curvature-equations-by-dimension`: the three fundamental
curvature equations compute curvature by induction on dimension. The base case
is that a one-dimensional Riemannian manifold is flat: if `dim M ≤ 1` then the
curvature tensor vanishes identically (`curvatureEquationsByDimension`), because
its first two arguments are then always linearly dependent, and the curvature
tensor is alternating in that pair
(`curvatureTensorAt_eq_zero_of_not_linearIndependent`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2.1.
-/

open scoped ContDiff Manifold

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** The curvature tensor vanishes as soon as its first two arguments
are linearly dependent: `R(u,v)w = 0` whenever `u, v` are linearly dependent.
Immediate from the alternating property `R(u,u)w = 0` and homogeneity in the
first two slots. -/
theorem curvatureTensorAt_eq_zero_of_not_linearIndependent
    (D : AffineConnection I M) (p : M) {u v : TangentSpace I p}
    (h : ¬ LinearIndependent ℝ ![u, v]) (w : TangentSpace I p) :
    curvatureTensorAt D p u v w = 0 := by
  -- `R(x,x)w = 0` from antisymmetry in the first pair.
  have hself : ∀ x : TangentSpace I p, curvatureTensorAt D p x x w = 0 := by
    intro x
    have h := curvatureTensorAt_antisymm_first D p x x w
    have h2 : (2 : ℝ) • curvatureTensorAt D p x x w = 0 := by
      have e : (2 : ℝ) • curvatureTensorAt D p x x w
          = curvatureTensorAt D p x x w + curvatureTensorAt D p x x w := by module
      rw [e, add_eq_zero_iff_eq_neg]; exact h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  -- `R(0,v)w = 0` from homogeneity.
  have hzero : curvatureTensorAt D p (0 : TangentSpace I p) v w = 0 := by
    have h := curvatureTensorAt_smul_first D p (0 : ℝ) v v w
    rw [zero_smul, zero_smul] at h
    exact h
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, hst, hnz⟩ := h
  rcases eq_or_ne t 0 with ht | ht
  · -- `t = 0` forces `s ≠ 0` and `u = 0`.
    subst ht
    rw [zero_smul, add_zero] at hst
    have hs : s ≠ 0 := fun hs0 => hnz hs0 rfl
    have hu : u = 0 := by
      rcases smul_eq_zero.mp hst with h1 | h1
      · exact absurd h1 hs
      · exact h1
    rw [hu, hzero]
  · -- `t ≠ 0` forces `v = (-s / t) • u`.
    have hv : v = (-s / t) • u := by
      have h1 : t • v = (-s) • u := by
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hst
      have h2 : v = t⁻¹ • (t • v) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, h1, smul_smul]
      congr 1
      ring
    rw [hv, curvatureTensorAt_smul_middle, hself, smul_zero]

/-- **Math.** Petersen §3.2.1, remark `rem:pet-ch3-curvature-equations-by-dimension`
(the base case of computing curvature by dimension): a Riemannian manifold of
dimension at most one is flat — its curvature tensor vanishes identically.
Indeed, in dimension `≤ 1` any two tangent vectors are linearly dependent, so
`curvatureTensorAt_eq_zero_of_not_linearIndependent` applies. -/
theorem curvatureEquationsByDimension
    (D : AffineConnection I M) (p : M)
    (hdim : Module.finrank ℝ E ≤ 1) (u v w : TangentSpace I p) :
    curvatureTensorAt D p u v w = 0 := by
  refine curvatureTensorAt_eq_zero_of_not_linearIndependent D p (fun hind => ?_) w
  have hcard : Fintype.card (Fin 2) ≤ Module.finrank ℝ (TangentSpace I p) :=
    hind.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  have : (2 : ℕ) ≤ Module.finrank ℝ E := hcard
  omega

end PetersenLib
