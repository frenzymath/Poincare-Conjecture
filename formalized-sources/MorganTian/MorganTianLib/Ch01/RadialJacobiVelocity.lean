import MorganTianLib.Ch01.RicciFrameTrace

/-!
# Poincaré Ch. 1, §1.6 — the radial Jacobi datum in the **velocity frame**

`FrameRadialBridge.exists_isRadialJacobi_of_geodesic` produces, from a geodesic on
`M`, the abstract datum `IsRadialJacobi ℛ 𝒥 𝒥' B C` in *some* parallel
`g`-orthonormal frame.  For the **Ricci** and **volume** comparisons that is not
quite enough: those arguments have to know *which* direction of the coefficient
space is the radial one, because the Jacobi operator annihilates it
(`R(γ', γ')γ' = 0`) and the model comparison therefore carries an `n − 1`.

This file re-runs the producer with the frame supplied by
`RicciFrameTrace.exists_orthonormalParallelFrameAlong_velocity`, whose `0`-th
vector **is** the unit velocity `γ'`.  The radial direction of the coefficient
space is then the *constant* standard basis vector `b₀`, and the datum comes with
two extra facts recorded:

* `e 0 t = γ'(t)` for all `t ∈ [a, b]` — the frame is the velocity frame; and
* `ℛ(t) b₀ = 0` for all `t ∈ [0, B]` — the radial direction is in the kernel of
  the frame Jacobi operator (`frameCurvOp_radial_eq_zero`).

Main result:

* `exists_isRadialJacobi_of_geodesic_velocity` — the velocity-frame radial Jacobi
  datum of a **unit-speed** geodesic, with the column identity
  `frameVec J t = 𝒥 t (frameVec ∇J 0)` of the template, plus the two clauses
  above.

Blueprint: `lem:geodesic-polar-form`, `lem:jacobi-frame-reduction`,
`thm:ricci-curvature-comparison`, `lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.6.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- The coefficient space of the parallel frame (see `FrameRadialBridge`). -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The standard orthonormal basis of the coefficient space. -/
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-- **Math.** **The radial Jacobi datum of a unit-speed geodesic, in the velocity
frame.**  This is `exists_isRadialJacobi_of_geodesic` with the frame pinned down:
along a **unit-speed** geodesic `γ : [a, b] → M` (crossing arbitrarily many
charts), with `0` and `B` interior to `[a, b]`, there are

* a parallel `g`-orthonormal frame `e` along `γ` whose `0`-th vector *is* the
  velocity, `E₀(t) = γ'(t)` — the frame of
  `exists_orthonormalParallelFrameAlong_velocity`; and
* a matrix Jacobi field `(𝒥, 𝒥')` with `𝒥(0) = 0`, `𝒥'(0) = 1` solving
  `𝒥'' + ℛ𝒥 = 0` for the frame Jacobi operator `ℛ = frameCurvOp g γ e`, i.e. an
  honest `IsRadialJacobi ℛ 𝒥 𝒥' B C`,

such that

* `ℛ(t) b₀ = 0` on `[0, B]` — **the radial direction of the coefficient space is
  in the kernel of the Jacobi operator**, since `ℛ(γ', γ')γ' = 0`
  (`frameCurvOp_radial_eq_zero`); and
* every Jacobi field `J` along `γ` vanishing at the centre is the column of `𝒥`
  through its initial covariant derivative:
  `frameVec J t = 𝒥 t (frameVec ∇J 0)` on `[0, B]`.

The proof is the template `exists_isRadialJacobi_of_geodesic` verbatim, with
`exists_orthonormalParallelFrameAlong` replaced by its velocity refinement; the
new radial clause is `frameCurvOp_radial_eq_zero` fed with `E₀(t) = γ'(t)`.

This is the datum the trace-Riccati comparison consumes: knowing that `b₀` is
killed by `ℛ` is what lets the trace be taken over the `(n−1)`-dimensional normal
complement, which is where the `n − 1` of `Ric ≥ −(n−1)k` comes from.

Blueprint: `thm:ricci-curvature-comparison`, `lem:volume-element-comparison`. -/
theorem exists_isRadialJacobi_of_geodesic_velocity {g : RiemannianMetric I M} {γ : ℝ → M}
    {a b B : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1)
    (ha : a < 0) (hB0 : 0 ≤ B) (hBb : B < b) :
    ∃ (e : Fin (Module.finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ (∀ t ∈ Icc a b,
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t)
        ∧ IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C
        ∧ (∀ t ∈ Icc (0 : ℝ) B, frameCurvOp (I := I) g γ e t (𝔟 0 : 𝔼) = 0)
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) B,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0)) := by
  classical
  obtain ⟨e, hPar, horth, hvel⟩ :=
    exists_orthonormalParallelFrameAlong_velocity (I := I) hab hgeo hγc hunit
  have hIcc : Icc (0 : ℝ) B ⊆ Icc a b := Icc_subset_Icc ha.le hBb.le
  have hcont : ContinuousOn (frameCurvOp (I := I) g γ e) (Icc (0 : ℝ) B) :=
    (continuousOn_frameCurvOp hPar hgeo hγc).mono hIcc
  have hsymm : ∀ t ∈ Icc (0 : ℝ) B, ∀ X Y : 𝔼,
      ⟪frameCurvOp (I := I) g γ e t X, Y⟫ = ⟪X, frameCurvOp (I := I) g γ e t Y⟫ :=
    fun t _ X Y => frameCurvOp_symm (I := I) g γ e t X Y
  obtain ⟨𝒥, 𝒥', C, hRJ⟩ := exists_isRadialJacobi_of_continuousOn hB0 hsymm hcont
  -- the radial direction is in the kernel of the frame Jacobi operator
  have hrad : ∀ t ∈ Icc (0 : ℝ) B, frameCurvOp (I := I) g γ e t (𝔟 0 : 𝔼) = 0 :=
    fun t ht => frameCurvOp_radial_eq_zero (I := I) g γ e t (hvel t (hIcc ht))
  refine ⟨e, 𝒥, 𝒥', C, hPar, horth, hvel, hRJ, hrad, fun J DJ hJac hJ0 => ?_⟩
  -- the two solutions of the same linear system with the same initial data
  set w : 𝔼 := frameVec (I := I) g γ e DJ 0 with hw
  have hsol₁ : IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 B
      (frameVec (I := I) g γ e J) (frameVec (I := I) g γ e DJ) :=
    isJacobiSolOn_frameVec hJac hPar hgeo hγc horth ha hBb
  have hsol₂ : IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 B
      (fun t => 𝒥 t w) (fun t => 𝒥' t w) := hRJ.sol.apply w
  have hy : frameVec (I := I) g γ e J 0 = 𝒥 0 w := by
    rw [frameVec_eq_zero hJ0, hRJ.fst_zero]
    simp
  have hv : frameVec (I := I) g γ e DJ 0 = 𝒥' 0 w := by
    rw [hRJ.snd_one]
    simp [hw]
  exact fun t ht => (IsJacobiSolOn.eqOn_of_left hcont hsol₁ hsol₂ hy hv).1 ht

end MorganTianLib

end
