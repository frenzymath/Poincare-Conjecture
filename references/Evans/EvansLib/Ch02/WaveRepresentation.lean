import EvansLib.Ch02.WaveEnergy

/-!
# Evans, Ch. 2 section 2.4.1 - representation of one-dimensional waves

This file proves the converse to `waveGeneralSol_isPDESolution`: every globally
`C^2` solution of the one-dimensional wave equation is a sum of a left-moving
and a right-moving profile.  The profiles are reconstructed from the Cauchy
data at `t = 0`, and inherit `C^2` regularity.
-/

noncomputable section

namespace EvansLib

/-! ## Cauchy traces -/

/-- The continuous linear embedding of the initial line into space-time,
`x |-> (x, 0)`. -/
def waveInitialLineLinear : ℝ →L[ℝ] SpaceTime 1 :=
  { toFun := fun x => x • spaceDir 1 0
    map_add' := fun x y => by simp [add_smul]
    map_smul' := fun c x => by simp [mul_smul] }

@[simp] lemma waveInitialLineLinear_apply (x : ℝ) :
    waveInitialLineLinear x = wavePoint x 0 := by
  simp [waveInitialLineLinear, wavePoint]

/-- Initial displacement `x |-> u(x,0)` of a one-dimensional wave. -/
def waveInitialDisplacement (u : SpaceTime 1 → ℝ) : ℝ → ℝ :=
  fun x => u (wavePoint x 0)

/-- Initial velocity `x |-> u_t(x,0)` of a one-dimensional wave. -/
def waveInitialVelocity (u : SpaceTime 1 → ℝ) : ℝ → ℝ :=
  fun x => waveTimeDeriv u (wavePoint x 0)

/-- A `C^2` wave has `C^2` initial displacement. -/
lemma waveInitialDisplacement_contDiff {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 2 (waveInitialDisplacement u) := by
  change ContDiff ℝ 2 (fun x => u (wavePoint x 0))
  have hline : ContDiff ℝ 2 (fun x => wavePoint x 0) := by
    convert waveInitialLineLinear.contDiff using 1
    funext x
    exact (waveInitialLineLinear_apply x).symm
  exact hu.comp hline

/-- A `C^2` wave has `C^1` initial velocity. -/
lemma waveInitialVelocity_contDiff {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (waveInitialVelocity u) := by
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  have hut : ContDiff ℝ 1 (waveTimeDeriv u) := by
    exact hDu.clm_apply contDiff_const
  change ContDiff ℝ 1 (fun x => waveTimeDeriv u (wavePoint x 0))
  have hline : ContDiff ℝ 1 (fun x => wavePoint x 0) := by
    convert waveInitialLineLinear.contDiff using 1
    funext x
    exact (waveInitialLineLinear_apply x).symm
  exact hut.comp hline

/-! ## Profiles reconstructed from Cauchy data -/

/-- The left-moving profile reconstructed from displacement `g` and velocity
`h`: `F = (g + integral_0^. h) / 2`. -/
def waveLeftProfile (g h : ℝ → ℝ) : ℝ → ℝ :=
  fun y => 2⁻¹ * g y + 2⁻¹ * daAntideriv h y

/-- The right-moving profile reconstructed from displacement `g` and velocity
`h`: `G = (g - integral_0^. h) / 2`. -/
def waveRightProfile (g h : ℝ → ℝ) : ℝ → ℝ :=
  fun y => 2⁻¹ * g y - 2⁻¹ * daAntideriv h y

lemma waveLeftProfile_contDiff {g h : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) : ContDiff ℝ 2 (waveLeftProfile g h) := by
  exact (hg.const_smul (2⁻¹ : ℝ)).add
    ((daAntideriv_contDiff hh).const_smul (2⁻¹ : ℝ))

lemma waveRightProfile_contDiff {g h : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) : ContDiff ℝ 2 (waveRightProfile g h) := by
  exact (hg.const_smul (2⁻¹ : ℝ)).sub
    ((daAntideriv_contDiff hh).const_smul (2⁻¹ : ℝ))

/-- D'Alembert's formula is the general wave built from the two profiles
reconstructed from its Cauchy data. -/
lemma dAlembert_eq_waveGeneralSol_profiles {g h : ℝ → ℝ} (hh : Continuous h) :
    dAlembert g h = waveGeneralSol (waveLeftProfile g h) (waveRightProfile g h) := by
  funext p
  rw [dAlembert, waveGeneralSol, ← daAntideriv_sub hh (p 1 - p 0) (p 1 + p 0)]
  simp only [waveLeftProfile, waveRightProfile]
  ring

/-! ## Converse representation theorem -/

/-- A global `C^2` one-dimensional wave agrees with the d'Alembert solution
formed from its own initial displacement and velocity. -/
theorem wave_eq_dAlembert_initial {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) :
    u = dAlembert (waveInitialDisplacement u) (waveInitialVelocity u) := by
  have hg : ContDiff ℝ 2 (waveInitialDisplacement u) :=
    waveInitialDisplacement_contDiff hu
  have hh : ContDiff ℝ 1 (waveInitialVelocity u) :=
    waveInitialVelocity_contDiff hu
  apply wave_cauchy_unique_1d hu (dAlembert_contDiff hg hh) hsol
    (dAlembert_isPDESolution hg hh)
  · intro x
    symm
    calc
      dAlembert (waveInitialDisplacement u) (waveInitialVelocity u) (wavePoint x 0) =
          waveInitialDisplacement u ((wavePoint x 0) 1) :=
        dAlembert_init (wavePoint x 0) (wavePoint_apply_zero x 0)
      _ = u (wavePoint x 0) := by rw [wavePoint_apply_one]; rfl
  · intro x
    symm
    change fderiv ℝ
        (dAlembert (waveInitialDisplacement u) (waveInitialVelocity u))
          (wavePoint x 0) (timeDir 1) =
      fderiv ℝ u (wavePoint x 0) (timeDir 1)
    calc
      fderiv ℝ (dAlembert (waveInitialDisplacement u) (waveInitialVelocity u))
          (wavePoint x 0) (timeDir 1) =
          waveInitialVelocity u ((wavePoint x 0) 1) :=
        dAlembert_init_time hg hh (wavePoint x 0) (wavePoint_apply_zero x 0)
      _ = fderiv ℝ u (wavePoint x 0) (timeDir 1) := by
        rw [wavePoint_apply_one]
        rfl

/-- **Converse general-solution theorem for the one-dimensional wave equation.**
Every global `C^2` solution of `u_tt - u_xx = 0` has the form
`u(x,t) = F(x+t) + G(x-t)` for `C^2` profiles `F` and `G`. -/
theorem wave_exists_general_representation_1d {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) :
    ∃ F G : ℝ → ℝ,
      ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧ u = waveGeneralSol F G := by
  let g := waveInitialDisplacement u
  let h := waveInitialVelocity u
  refine ⟨waveLeftProfile g h, waveRightProfile g h, ?_, ?_, ?_⟩
  · exact waveLeftProfile_contDiff
      (waveInitialDisplacement_contDiff hu) (waveInitialVelocity_contDiff hu)
  · exact waveRightProfile_contDiff
      (waveInitialDisplacement_contDiff hu) (waveInitialVelocity_contDiff hu)
  · rw [wave_eq_dAlembert_initial hu hsol]
    exact dAlembert_eq_waveGeneralSol_profiles
      (waveInitialVelocity_contDiff hu).continuous

end EvansLib
