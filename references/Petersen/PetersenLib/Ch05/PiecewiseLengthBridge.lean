import PetersenLib.Ch05.DistanceEDistBridge

/-!
# Petersen Ch. 5 — the length bridge for **piecewise**-`C^∞` curves

`DistanceEDistBridge.lean` proves the length bridge
`Manifold.pathELength I γ a b = ENNReal.ofReal (curveLength g γ a b)` for a
globally-`C^∞` curve (`pathELength_eq_ofReal_curveLength`), and separately
telescopes a *piecewise*-`C^∞` curve into the one-directional competitor bound
`riemannianEDist I (γ a) (γ b) ≤ ofReal (curveLength g γ a b)`.

This file upgrades the telescope from an inequality to the **equality** bridge in
the piecewise class:

* `pathELength_eq_ofReal_curveLength_of_isPiecewiseSmoothCurve` — for `γ`
  piecewise `C^∞` on `[a, b]` with `a ≤ b`,
  `Manifold.pathELength I γ a b = ENNReal.ofReal (curveLength g γ a b)`.

Both sides are additive over the partition — `Manifold.pathELength_add` on the
mathlib side, `IsPiecewiseSmoothCurve.curveLength_add` on the Petersen side — and
on each `C^∞` piece the smooth bridge applies verbatim.  No new analysis: the
Petersen lengths are finite and nonnegative, so `ENNReal.ofReal` is additive on
them.

This is exactly the glue needed to feed a Petersen piecewise-`C^∞` competitor
(`IsPiecewiseSmoothCurve`, the regularity class of `IsSegment` and of the
Petersen distance infimum) into the vendored do Carmo minimizing-equality engine
`PetersenLib.Exponential.exists_gauss_equality_manifold_piecewise`, which speaks
in `pathELength`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **The length bridge for a piecewise-`C^∞` curve.**  If `γ` is
piecewise `C^∞` on `[a, b]` (`a ≤ b`) then the mathlib path length equals the
Petersen curve length up to `ENNReal.ofReal`:
`Manifold.pathELength I γ a b = ENNReal.ofReal (curveLength g γ a b)`.

Telescoping over the partition `a = u 0 ≤ ⋯ ≤ u n = b`: on each closed piece the
curve is `C^∞`, so the smooth bridge `pathELength_eq_ofReal_curveLength` applies;
`Manifold.pathELength_add` and `curveLength_additive` add the pieces, and
`ENNReal.ofReal` is additive on the (nonnegative, finite) piece lengths. -/
theorem pathELength_eq_ofReal_curveLength_of_isPiecewiseSmoothCurve
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I γ a b
      = ENNReal.ofReal (curveLength (I := I) g γ a b) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hγint := hγ.intervalIntegrable_sqrt_curveSpeedSq g
  obtain ⟨-, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  subst hu0; subst hun
  -- accumulate over the partition prefix `[u 0, u k]`
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      Manifold.pathELength I γ (u 0) (u ⟨k, hk⟩)
        = ENNReal.ofReal (curveLength (I := I) g γ (u 0) (u ⟨k, hk⟩)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, curveLength_self, Manifold.pathELength_self]
      simp
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hk1 : k < n + 1 := by omega
      have hcast : (⟨k, hk1⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).castSucc := rfl
      have hsucc : (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).succ := rfl
      have hle_prefix : u 0 ≤ u ⟨k, hk1⟩ := hmono (Fin.zero_le _)
      have hle_piece : u ⟨k, hk1⟩ ≤ u ⟨k + 1, hk⟩ := by
        rw [hcast, hsucc]; exact hmono Fin.castSucc_lt_succ.le
      have hle_last : u ⟨k + 1, hk⟩ ≤ u (Fin.last n) := hmono (Fin.le_last _)
      -- the smooth piece `[u k, u (k+1)]`
      have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) := by
        rw [hcast, hsucc]; exact hsmooth ⟨k, hkn⟩
      -- length additivity on the Petersen side
      have hsubL : Set.uIcc (u 0) (u ⟨k, hk1⟩) ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_prefix,
          Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc_right (hle_piece.trans hle_last)
      have hsubR : Set.uIcc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)
          ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_piece,
          Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc hle_prefix hle_last
      have hsplit : curveLength (I := I) g γ (u 0) (u ⟨k + 1, hk⟩)
          = curveLength (I := I) g γ (u 0) (u ⟨k, hk1⟩)
            + curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
        curveLength_additive (I := I) g γ (hγint.mono_set hsubL) (hγint.mono_set hsubR)
      -- single-piece bridge
      have hpiece : Manifold.pathELength I γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)
          = ENNReal.ofReal (curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) :=
        pathELength_eq_ofReal_curveLength (I := I) g hle_piece hsm
      have hnn1 : 0 ≤ curveLength (I := I) g γ (u 0) (u ⟨k, hk1⟩) :=
        curveLength_nonneg (I := I) g γ hle_prefix
      have hnn2 : 0 ≤ curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
        curveLength_nonneg (I := I) g γ hle_piece
      calc Manifold.pathELength I γ (u 0) (u ⟨k + 1, hk⟩)
          = Manifold.pathELength I γ (u 0) (u ⟨k, hk1⟩)
              + Manifold.pathELength I γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
            (Manifold.pathELength_add hle_prefix hle_piece).symm
        _ = ENNReal.ofReal (curveLength (I := I) g γ (u 0) (u ⟨k, hk1⟩))
              + ENNReal.ofReal (curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) := by
            rw [ih hk1, hpiece]
        _ = ENNReal.ofReal (curveLength (I := I) g γ (u 0) (u ⟨k + 1, hk⟩)) := by
            rw [hsplit, ENNReal.ofReal_add hnn1 hnn2]
  have hfin := key n n.lt_succ_self
  have hlast : (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = Fin.last n := rfl
  rwa [hlast] at hfin

end PetersenLib

end
