import PoincareLib.Ch01.JacobiRiccati

/-!
# Poincaré Ch. 1, §1.4 — producing a radial Jacobi datum, and reading its columns

`JacobiRiccati` *consumes* the datum `IsRadialJacobi ℛ 𝒥 𝒥' b C` — the matrix
Jacobi field `𝒥'' + ℛ𝒥 = 0` with `𝒥(0) = 0`, `𝒥'(0) = 1` — and derives from it
the Riccati equation for the shape operator, the Wronskian symmetry and the
small-time asymptotics.  Nothing so far *produces* one.  This file supplies the
two missing structural lemmas:

* `exists_isRadialJacobi` — **the producer**: a symmetric, continuous, bounded
  curvature curve `ℛ` on `[0, b]` already determines the datum.  There is no
  geometry here: the matrix Jacobi equation is a linear ODE in the Banach algebra
  `E →L[ℝ] E`, so `exists_isJacobiSolOn_Icc` with `F := E →L[ℝ] E` and initial
  data `(0, 1)` gives `𝒥, 𝒥'` on the whole of `[0, b]` (linear ⇒ no blow-up);
  `jacobiOpCoeff` is exactly the left-multiplication coefficient of that ODE, and
  its continuity is `continuousOn_jacobiOpCoeff`.

* `IsJacobiSolOn.apply` — **the columns**: `𝒥` is the *matrix* solution, so for
  each `w : E` the curve `t ↦ 𝒥 t w` is the *vector* Jacobi field with initial
  data `(0, w)`.  This is the statement that makes the matrix picture equivalent
  to the classical one ("the columns of `𝒥` are the Jacobi fields vanishing at
  the centre"), and it is what lets ODE uniqueness identify `𝒥 t w` with a
  geometric Jacobi field along a geodesic.  It is post-composition with the
  evaluation map `ContinuousLinearMap.apply ℝ E w`, which is continuous linear.

Blueprint: `lem:second-order-linear-ode`, `lem:radial-shape-riccati`,
`lem:jacobi-matrix-inverse`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Filter
open scoped RealInnerProductSpace Topology

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The columns of a matrix solution -/

/-- **Math.** **The columns of the matrix Jacobi field are Jacobi fields.**  If
the operator-valued pair `(𝒥, 𝒥')` solves the matrix equation `𝒥'' + ℛ𝒥 = 0`
(i.e. `IsJacobiSolOn (jacobiOpCoeff ℛ)`, with `jacobiOpCoeff ℛ t = ℛ t · —` the
left multiplication), then for every `w : E` the vector-valued pair
`(t ↦ 𝒥 t w, t ↦ 𝒥' t w)` solves the vector equation `y'' + ℛ y = 0`.

Evaluation at `w` is the continuous linear map `ContinuousLinearMap.apply ℝ E w`,
so it commutes with the derivative; and `(ℛ t * 𝒥 t) w = ℛ t (𝒥 t w)` is
composition unfolded.  Together with `IsJacobiSolOn.eqOn_of_left` this is what
identifies `𝒥 t w` with *the* Jacobi field with initial data `(0, w)`. -/
theorem IsJacobiSolOn.apply {ℛ : ℝ → E →L[ℝ] E} {a b : ℝ} {𝒥 𝒥' : ℝ → E →L[ℝ] E}
    (h : IsJacobiSolOn (jacobiOpCoeff ℛ) a b 𝒥 𝒥') (w : E) :
    IsJacobiSolOn ℛ a b (fun t => 𝒥 t w) (fun t => 𝒥' t w) where
  hasDerivWithinAt_fst t ht := by
    have := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivWithinAt t
      (h.hasDerivWithinAt_fst t ht)
    simpa using this
  hasDerivWithinAt_snd t ht := by
    have := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivWithinAt t
      (h.hasDerivWithinAt_snd t ht)
    simpa using this

/-! ### Existence of the radial Jacobi datum -/

/-- **Math.** **Existence of the matrix Jacobi field with `𝒥(0) = 0`,
`𝒥'(0) = 1`.**  A curvature curve `ℛ` that is symmetric, continuous and bounded
by `C` on `[0, b]` already determines a radial Jacobi datum: the matrix equation
`𝒥'' + ℛ𝒥 = 0` is a *linear* ODE in the Banach algebra `E →L[ℝ] E`, so it has a
solution on the whole interval (no blow-up), with any prescribed initial pair.

This is the missing producer for `IsRadialJacobi`: geometry enters only through
`ℛ`, and every hypothesis of the structure other than `sol` is passed through
unchanged.

Blueprint: `lem:second-order-linear-ode`, `lem:radial-shape-riccati`. -/
theorem exists_isRadialJacobi {ℛ : ℝ → E →L[ℝ] E} {b C : ℝ} (hb : 0 ≤ b)
    (hsymm : ∀ t ∈ Icc (0 : ℝ) b, ∀ X Y : E, ⟪ℛ t X, Y⟫ = ⟪X, ℛ t Y⟫)
    (hcont : ContinuousOn ℛ (Icc (0 : ℝ) b))
    (hC : ∀ t ∈ Icc (0 : ℝ) b, ‖ℛ t‖ ≤ C) :
    ∃ 𝒥 𝒥' : ℝ → E →L[ℝ] E, IsRadialJacobi ℛ 𝒥 𝒥' b C := by
  obtain ⟨y, v, hy0, hv0, hsol⟩ :=
    exists_isJacobiSolOn_Icc (F := E →L[ℝ] E) hb (jacobiOpCoeff ℛ)
      (continuousOn_jacobiOpCoeff hcont) 0 1
  exact ⟨y, v, ⟨hsol, hy0, hv0, hsymm, hcont, hC⟩⟩

/-- **Math.** The same, with the bound `C` extracted from continuity: a
symmetric, continuous curvature curve on the compact interval `[0, b]` is
automatically bounded there, so it needs no bound hypothesis at all. -/
theorem exists_isRadialJacobi_of_continuousOn {ℛ : ℝ → E →L[ℝ] E} {b : ℝ} (hb : 0 ≤ b)
    (hsymm : ∀ t ∈ Icc (0 : ℝ) b, ∀ X Y : E, ⟪ℛ t X, Y⟫ = ⟪X, ℛ t Y⟫)
    (hcont : ContinuousOn ℛ (Icc (0 : ℝ) b)) :
    ∃ (𝒥 𝒥' : ℝ → E →L[ℝ] E) (C : ℝ), IsRadialJacobi ℛ 𝒥 𝒥' b C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨𝒥, 𝒥', h⟩ := exists_isRadialJacobi hb hsymm hcont hC
  exact ⟨𝒥, 𝒥', C, h⟩

end PoincareLib

end
