import EvansLib.Ch02.HeatBall
import EvansLib.Ch02.Harmonic
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Evans, Ch. 2 §2.3.3 — weak maximum principle and uniqueness for the heat equation

Evans, *Partial Differential Equations* (2nd ed.), §2.3.3: on a bounded open
`U ⊆ ℝⁿ` and time interval `(0, T]`, a solution of the heat equation on the parabolic
cylinder `U_T` attains its maximum over `Ū_T` on the parabolic boundary `Γ_T`
(Theorem 8's weak form), and solutions of the initial/boundary-value problem are
unique (Theorem 4 — `thm:uniqueness-heat-bounded-domain`).

Evans derives the *strong* maximum principle from the mean-value property over heat
balls, which is gated on the divergence theorem. The **weak** version proved here
suffices for uniqueness and has an elementary proof: perturb `v := u - ε t`; at an
interior maximum of `v` the spatial pure second derivatives are `≤ 0`
(second-derivative test) and the time derivative (one-sided, from the left) is `≥ 0`,
so `0 ≤ v_t = Δv + (Δu - u_t) - ε ≤ -ε < 0` — contradiction. Two limits
(`ε → 0` and a shrink `T' ↑ T`, so that the equation is only ever used at interior
times) finish.

Space–time conventions follow `EvansLib.Ch02.Heat`/`HeatBall`: `SpaceTime n = ℝ^{n+1}`
with coordinate `0` the time and `1, …, n` the space slots; `u_t = partialDeriv 0` and
`Δu = ∑ⱼ (partialDeriv j.succ)^[2]`.

Main results:

* `EvansLib.deriv_deriv_nonpos_of_isLocalMax` — converse second-derivative test.
* `EvansLib.partialDeriv_iterate_two_nonpos_of_section_max`,
  `EvansLib.partialDeriv_nonneg_of_section_eventually_le_left` — coordinate-section
  versions at a constrained maximum.
* `EvansLib.exists_parabolicBoundary_isMaxOn` — the weak maximum principle.
* `EvansLib.eqOn_closure_of_eqOn_parabolicBoundary` — **uniqueness**
  (`thm:uniqueness-heat-bounded-domain`).

Regularity caveat: the solutions here are assumed jointly `C²` in `(t,x)` at interior
times, which is stronger than Evans's class `C²₁(U_T)` (continuity of `u, Du, D²u`
in `x` and `u_t` only); see inbox I-0313.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.3.
-/

open Metric Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace EvansLib

/-! ## One-dimensional lemmas -/

/-- **Converse second-derivative test.** At a local maximum of `g : ℝ → ℝ`, the second
derivative (if meaningful — junk values are `0`) is nonpositive. Complements mathlib's
`isLocalMin_of_deriv_deriv_pos`. -/
lemma deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {a : ℝ}
    (h : IsLocalMax g a) (hg : ContinuousAt g a) :
    deriv (deriv g) a ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hmin : IsLocalMin g a :=
    isLocalMin_of_deriv_deriv_pos hpos h.deriv_eq_zero hg
  -- a simultaneous local max and min is locally constant, killing the second derivative
  have hconst : g =ᶠ[𝓝 a] fun _ => g a := by
    filter_upwards [h, hmin] with s h1 h2
    exact le_antisymm h1 h2
  have h2 : deriv (deriv g) a = deriv (deriv fun _ => g a) a := hconst.deriv.deriv_eq
  rw [h2] at hpos
  simp [deriv_const'] at hpos

/-- If `g` has derivative `c` at `a` and `g ≤ g a` on a left neighbourhood of `a`,
then `c ≥ 0` (maximum at the right end of a time interval). -/
lemma deriv_nonneg_of_eventually_le_left {g : ℝ → ℝ} {a c : ℝ}
    (hg : HasDerivAt g c a) (h : ∀ᶠ s in 𝓝[<] a, g s ≤ g a) : 0 ≤ c := by
  have hslope : Tendsto (slope g a) (𝓝[<] a) (𝓝 c) :=
    hg.tendsto_slope.mono_left (nhdsWithin_mono a fun s hs => ne_of_lt hs)
  refine ge_of_tendsto hslope ?_
  filter_upwards [h, self_mem_nhdsWithin] with s hs hslt
  rw [slope_def_field]
  rw [mem_Iio] at hslt
  exact div_nonneg_iff.2 (Or.inr ⟨by linarith, by linarith⟩)

/-! ## Coordinate sections -/

/-- The section of `u` along the `i`-th coordinate direction through `p` is
differentiable wherever `u` is, with derivative the `i`-th partial. -/
lemma hasDerivAt_comp_single_line {m : ℕ} {u : EuclideanSpace ℝ (Fin m) → ℝ}
    {i : Fin m} {p : EuclideanSpace ℝ (Fin m)} {s₀ : ℝ}
    (hu : DifferentiableAt ℝ u (p + s₀ • EuclideanSpace.single i 1)) :
    HasDerivAt (fun s => u (p + s • EuclideanSpace.single i 1))
      (fderiv ℝ u (p + s₀ • EuclideanSpace.single i 1) (EuclideanSpace.single i 1))
      s₀ := by
  have hline : HasDerivAt (fun s : ℝ => p + s • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) s₀ := by
    simpa using ((hasDerivAt_id s₀).smul_const (EuclideanSpace.single i 1)).const_add p
  simpa using hu.hasFDerivAt.comp_hasDerivAt s₀ hline

/-- **One-sided first-derivative test in a coordinate direction.** If `u` is
differentiable at `p` and `u(p + s eᵢ) ≤ u(p)` for `s` in a left neighbourhood of `0`,
then `∂ᵢu(p) ≥ 0`. (Applied to the time slot at the top of the parabolic cylinder.) -/
lemma partialDeriv_nonneg_of_section_eventually_le_left {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m) → ℝ} {p : EuclideanSpace ℝ (Fin m)} {i : Fin m}
    (hu : DifferentiableAt ℝ u p)
    (h : ∀ᶠ s in 𝓝[<] (0 : ℝ), u (p + s • EuclideanSpace.single i 1) ≤ u p) :
    0 ≤ partialDeriv i u p := by
  have hg : HasDerivAt (fun s : ℝ => u (p + s • EuclideanSpace.single i 1))
      (partialDeriv i u p) (0 : ℝ) := by
    have h0 : DifferentiableAt ℝ u
        (p + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
      simpa using hu
    simpa [partialDeriv_apply] using hasDerivAt_comp_single_line h0
  refine deriv_nonneg_of_eventually_le_left hg ?_
  simpa using h

/-- **Second-derivative test in a coordinate direction.** If `u` is `C²` at `p` and the
section `s ↦ u (p + s eᵢ)` has a local maximum at `0`, then `(∂ᵢ)²u(p) ≤ 0`. -/
lemma partialDeriv_iterate_two_nonpos_of_section_max {m : ℕ}
    {u : EuclideanSpace ℝ (Fin m) → ℝ} {p : EuclideanSpace ℝ (Fin m)} {i : Fin m}
    (hu : ContDiffAt ℝ 2 u p)
    (h : ∀ᶠ s in 𝓝 (0 : ℝ), u (p + s • EuclideanSpace.single i 1) ≤ u p) :
    (partialDeriv i)^[2] u p ≤ 0 := by
  set e : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i (1 : ℝ) with he
  set g : ℝ → ℝ := fun s => u (p + s • e) with hgdef
  have hA : Continuous fun s : ℝ => p + s • e := by fun_prop
  have hA0 : p + (0 : ℝ) • e = p := by simp
  -- `u` is `C²` at every point of the section near `0`
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 u (p + s • e) := by
    have h1 : Tendsto (fun s : ℝ => p + s • e) (𝓝 0) (𝓝 (p + (0 : ℝ) • e)) :=
      hA.continuousAt
    rw [hA0] at h1
    exact h1.eventually (hu.eventually (by simp))
  -- the first derivative of the section is the partial derivative along the section
  have hderiv_g : deriv g =ᶠ[𝓝 (0 : ℝ)] fun s => fderiv ℝ u (p + s • e) e := by
    filter_upwards [hev] with s hs
    exact (hasDerivAt_comp_single_line (hs.differentiableAt (by norm_num))).deriv
  -- the second derivative of the section at `0` is the pure second partial
  have hF : HasDerivAt (fun s : ℝ => fderiv ℝ u (p + s • e) e)
      (fderiv ℝ (fderiv ℝ u) p e e) (0 : ℝ) := by
    have hline : HasDerivAt (fun s : ℝ => p + s • e) e (0 : ℝ) := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p
    have hFd : DifferentiableAt ℝ (fderiv ℝ u) p :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hFd' : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) p)
        (p + (0 : ℝ) • e) := by
      rw [hA0]; exact hFd.hasFDerivAt
    have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ u (p + s • e))
        (fderiv ℝ (fderiv ℝ u) p e) (0 : ℝ) := hFd'.comp_hasDerivAt (0 : ℝ) hline
    simpa using hcomp.clm_apply (hasDerivAt_const (0 : ℝ) e)
  have hgg : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ u) p e e := by
    rw [hderiv_g.deriv_eq]
    exact hF.deriv
  -- apply the 1-D test to the section
  have hgmax : IsLocalMax g 0 := by
    filter_upwards [h] with s hs
    simpa [hgdef] using hs
  have hgcont : ContinuousAt g 0 := by
    have hup : ContinuousAt u (p + (0 : ℝ) • e) := by rw [hA0]; exact hu.continuousAt
    exact ContinuousAt.comp (g := u) (f := fun s : ℝ => p + s • e) hup hA.continuousAt
  have hfin := deriv_deriv_nonpos_of_isLocalMax hgmax hgcont
  rw [hgg] at hfin
  rwa [partialDeriv_iterate_two_eq_fderiv_fderiv hu i]

/-! ## Partial derivatives of differences -/

/-- First partials of a pointwise difference. -/
lemma partialDeriv_fun_sub {m : ℕ} {f g : EuclideanSpace ℝ (Fin m) → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin m) :
    partialDeriv i (fun y => f y - g y) x = partialDeriv i f x - partialDeriv i g x := by
  simp only [partialDeriv_apply]
  rw [fderiv_fun_sub hf hg]
  simp

/-- Pure second partials of a pointwise difference, from eventual differentiability of
the two pieces and differentiability of their first partials. -/
lemma partialDeriv_iterate_two_fun_sub {m : ℕ} {f g : EuclideanSpace ℝ (Fin m) → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} (i : Fin m)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y)
    (hf' : DifferentiableAt ℝ (partialDeriv i f) x)
    (hg' : DifferentiableAt ℝ (partialDeriv i g) x) :
    (partialDeriv i)^[2] (fun y => f y - g y) x =
      (partialDeriv i)^[2] f x - (partialDeriv i)^[2] g x := by
  have hev : partialDeriv i (fun y => f y - g y) =ᶠ[𝓝 x]
      fun y => partialDeriv i f y - partialDeriv i g y := by
    filter_upwards [hf, hg] with y hfy hgy
    exact partialDeriv_fun_sub hfy hgy i
  show partialDeriv i (partialDeriv i (fun y => f y - g y)) x = _
  rw [partialDeriv_apply, hev.fderiv_eq, fderiv_fun_sub hf' hg']
  simp only [ContinuousLinearMap.sub_apply]
  rfl

/-- The first partials of a `C²` function are differentiable. -/
lemma differentiableAt_partialDeriv_of_contDiffAt {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hf : ContDiffAt ℝ 2 f x) (i : Fin m) :
    DifferentiableAt ℝ (partialDeriv i f) x := by
  have hFd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold partialDeriv
  exact hFd.clm_apply (differentiableAt_const _)

/-! ## Space–time geometry: coordinates, boundedness, boundary -/

variable {n : ℕ}

/-- The spatial projection of space–time, as a linear map. -/
def spacePartₗ : SpaceTime n →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := spacePart
  map_add' p q := by ext i; simp [spacePart]
  map_smul' c p := by ext i; simp [spacePart]

lemma continuous_spacePart : Continuous (spacePart (n := n)) :=
  (spacePartₗ (n := n)).continuous_of_finiteDimensional

lemma continuous_timeCoord : Continuous fun p : SpaceTime n => p 0 := by fun_prop

/-- Building a space–time point from a time and a spatial point. -/
def toSpaceTime (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : SpaceTime n :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (Fin.cons t fun i => x i)

@[simp] lemma toSpaceTime_timeCoord (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (toSpaceTime t x) 0 = t := by
  simp [toSpaceTime]

@[simp] lemma spacePart_toSpaceTime (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    spacePart (toSpaceTime t x) = x := by
  ext i
  simp [toSpaceTime, spacePart]

/-- The Pythagoras split of the space–time norm into time and space contributions. -/
lemma norm_sq_spaceTime (p : SpaceTime n) : ‖p‖ ^ 2 = (p 0) ^ 2 + ‖spacePart p‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Fin.sum_univ_succ]
  simp [spacePart, sq_abs]

/-- Coordinate arithmetic: shifting time. -/
lemma timeCoord_add_smul_single_zero (p : SpaceTime n) (s : ℝ) :
    (p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0 = p 0 + s := by
  simp

lemma spacePart_add_smul_single_zero (p : SpaceTime n) (s : ℝ) :
    spacePart (p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = spacePart p := by
  ext i
  simp [spacePart, Fin.succ_ne_zero]

/-- Coordinate arithmetic: shifting a spatial slot. -/
lemma timeCoord_add_smul_single_succ (p : SpaceTime n) (s : ℝ) (j : Fin n) :
    (p + s • EuclideanSpace.single j.succ (1 : ℝ)) 0 = p 0 := by
  simp [(Fin.succ_ne_zero j).symm]

lemma spacePart_add_smul_single_succ (p : SpaceTime n) (s : ℝ) (j : Fin n) :
    spacePart (p + s • EuclideanSpace.single j.succ (1 : ℝ)) =
      spacePart p + s • EuclideanSpace.single j (1 : ℝ) := by
  ext i
  simp [spacePart, Fin.succ_inj]

/-- Membership in the parabolic cylinder, unfolded. -/
lemma mem_parabolicCylinder {U : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ} {p : SpaceTime n} :
    p ∈ parabolicCylinder U T ↔ spacePart p ∈ U ∧ p 0 ∈ Ioc 0 T :=
  Iff.rfl

/-- The closure of the parabolic cylinder lies in the closed slab over `closure U`. -/
lemma closure_parabolicCylinder_subset (U : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) :
    closure (parabolicCylinder U T) ⊆
      {p : SpaceTime n | spacePart p ∈ closure U ∧ p 0 ∈ Icc 0 T} := by
  refine closure_minimal (fun p hp => ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩) ?_
  exact (isClosed_closure.preimage continuous_spacePart).inter
    (isClosed_Icc.preimage continuous_timeCoord)

/-- The parabolic cylinder over a bounded base is bounded. -/
lemma isBounded_parabolicCylinder {U : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}
    (hUbdd : Bornology.IsBounded U) (hT : 0 < T) :
    Bornology.IsBounded (parabolicCylinder U T) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hUbdd
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (T ^ 2 + R ^ 2), fun p hp => ?_⟩
  rw [show ‖p‖ = Real.sqrt (‖p‖ ^ 2) from (Real.sqrt_sq (norm_nonneg p)).symm,
    norm_sq_spaceTime]
  refine Real.sqrt_le_sqrt ?_
  have h1 : (p 0) ^ 2 ≤ T ^ 2 := by nlinarith [hp.2.1, hp.2.2]
  have h2 : ‖spacePart p‖ ^ 2 ≤ R ^ 2 := by nlinarith [hR _ hp.1, norm_nonneg (spacePart p)]
  linarith

/-- Growing the time horizon grows the cylinder. -/
lemma parabolicCylinder_subset {U : Set (EuclideanSpace ℝ (Fin n))} {T' T : ℝ}
    (h : T' ≤ T) : parabolicCylinder U T' ⊆ parabolicCylinder U T :=
  fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.trans h⟩

/-- The parabolic boundary of a shorter cylinder is contained in that of a longer one. -/
lemma parabolicBoundary_subset {U : Set (EuclideanSpace ℝ (Fin n))} {T' T : ℝ}
    (h : T' ≤ T) : parabolicBoundary U T' ⊆ parabolicBoundary U T := by
  rintro q ⟨hqcl, hqnot⟩
  refine ⟨closure_mono (parabolicCylinder_subset h) hqcl, fun hqC => hqnot ?_⟩
  exact ⟨hqC.1, hqC.2.1, (closure_parabolicCylinder_subset U T' hqcl).2.2⟩

/-- The parabolic boundary is closed (for open `U`). -/
lemma isClosed_parabolicBoundary {U : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}
    (hU : IsOpen U) : IsClosed (parabolicBoundary U T) := by
  refine isClosed_of_closure_subset fun q hq => ?_
  have hqcl : q ∈ closure (parabolicCylinder U T) := by
    have hsub : closure (parabolicBoundary U T) ⊆
        closure (closure (parabolicCylinder U T)) := closure_mono diff_subset
    simpa [closure_closure] using hsub hq
  refine ⟨hqcl, fun hqC => ?_⟩
  -- if `q` lay in the cylinder, the open set `W` around it would meet the boundary in a
  -- point that is itself forced into the cylinder — impossible
  set W : Set (SpaceTime n) := {p | spacePart p ∈ U ∧ 0 < p 0} with hW
  have hWopen : IsOpen W :=
    (hU.preimage continuous_spacePart).inter (isOpen_Ioi.preimage continuous_timeCoord)
  have hqW : q ∈ W := ⟨hqC.1, hqC.2.1⟩
  obtain ⟨r, hrW, hrΓ⟩ := mem_closure_iff.1 hq W hWopen hqW
  exact hrΓ.2 ⟨hrW.1, hrW.2, (closure_parabolicCylinder_subset U T hrΓ.1).2.2⟩

/-- The parabolic boundary is nonempty (bottom points belong to it). -/
lemma parabolicBoundary_nonempty {U : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}
    (hUne : U.Nonempty) (hT : 0 < T) : (parabolicBoundary U T).Nonempty := by
  obtain ⟨x, hx⟩ := hUne
  refine ⟨toSpaceTime 0 x, ?_, ?_⟩
  · -- the bottom point is a limit of interior points `toSpaceTime s x`
    have htends : Tendsto (fun s : ℝ => toSpaceTime 0 x +
        s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) (𝓝[>] 0)
        (𝓝 (toSpaceTime 0 x)) := by
      have hc : Continuous fun s : ℝ => toSpaceTime 0 x +
          s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) := by fun_prop
      have := hc.continuousAt (x := (0 : ℝ))
      rw [ContinuousAt] at this
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htends ?_
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    refine ⟨?_, ?_⟩
    · rw [spacePart_add_smul_single_zero]; simpa using hx
    · rw [timeCoord_add_smul_single_zero]
      simpa using ⟨hs.1, hs.2.le⟩
  · intro hmem
    have := hmem.2.1
    simp at this

/-- The time coordinate of space–time, as a continuous linear map. -/
def timeCoordL : SpaceTime n →L[ℝ] ℝ :=
  { toFun := fun p => p 0
    map_add' := fun p q => by simp
    map_smul' := fun c p => by simp
    cont := continuous_timeCoord }

lemma contDiff_timeCoord {k : WithTop ℕ∞} :
    ContDiff ℝ k fun p : SpaceTime n => p 0 :=
  (timeCoordL (n := n)).contDiff

/-- Partial derivatives of the linear function `p ↦ ε p₀`. -/
lemma partialDeriv_const_mul_timeCoord (ε : ℝ) (x : SpaceTime n) (i : Fin (n + 1)) :
    partialDeriv i (fun p : SpaceTime n => ε * p 0) x =
      ε * (EuclideanSpace.single i (1 : ℝ) : SpaceTime n) 0 := by
  rw [partialDeriv_apply]
  have hL : HasFDerivAt (fun p : SpaceTime n => ε * p 0)
      (ε • timeCoordL (n := n)) x := ((timeCoordL (n := n)).hasFDerivAt).const_mul ε
  rw [hL.fderiv]
  simp [timeCoordL]

/-- Pure second partials of the linear function `p ↦ ε p₀` vanish. -/
lemma partialDeriv_iterate_two_const_mul_timeCoord (ε : ℝ) (x : SpaceTime n)
    (i : Fin (n + 1)) :
    (partialDeriv i)^[2] (fun p : SpaceTime n => ε * p 0) x = 0 := by
  have hconst : partialDeriv i (fun p : SpaceTime n => ε * p 0) =
      fun _ => ε * (EuclideanSpace.single i (1 : ℝ) : SpaceTime n) 0 := by
    funext y
    exact partialDeriv_const_mul_timeCoord ε y i
  show partialDeriv i (partialDeriv i fun p : SpaceTime n => ε * p 0) x = 0
  rw [hconst, partialDeriv_apply]
  simp

/-! ## The weak maximum principle -/

variable {U : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ} {u : SpaceTime n → ℝ}

/-- **Core step of the weak parabolic maximum principle.** For `ε > 0` and an interior
time horizon `T' < T`, the perturbed function `v = u - ε t` attains its maximum over
the closed shorter cylinder on the parabolic boundary `Γ_{T'}`. At an interior maximum
`v_t ≥ 0` (one-sided in time) while `Δv ≤ 0` (second-derivative test in each spatial
direction), so the heat equation would force `0 ≤ v_t = Δv - ε ≤ -ε < 0`. -/
lemma exists_parabolicBoundary_isMaxOn_sub_mul_time {T' : ℝ}
    (hU : IsOpen U) (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hT' : 0 < T') (hT'T : T' < T)
    (hcont : ContinuousOn u (closure (parabolicCylinder U T)))
    (hC2 : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hheat : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      partialDeriv 0 u p = ∑ j : Fin n, (partialDeriv j.succ)^[2] u p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ parabolicBoundary U T', ∀ p ∈ closure (parabolicCylinder U T'),
      u p - ε * p 0 ≤ u z - ε * z 0 := by
  set v : SpaceTime n → ℝ := fun p => u p - ε * p 0 with hv
  have hsubcl : closure (parabolicCylinder U T') ⊆ closure (parabolicCylinder U T) :=
    closure_mono (parabolicCylinder_subset hT'T.le)
  have hcomp : IsCompact (closure (parabolicCylinder U T')) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_parabolicCylinder hUbdd hT').closure
  have hne : (closure (parabolicCylinder U T')).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    refine ⟨toSpaceTime T' x, subset_closure ⟨?_, ?_⟩⟩
    · rw [spacePart_toSpaceTime]; exact hx
    · rw [toSpaceTime_timeCoord]; exact ⟨hT', le_rfl⟩
  have hvcont : ContinuousOn v (closure (parabolicCylinder U T')) :=
    (hcont.mono hsubcl).sub (Continuous.continuousOn (by fun_prop))
  obtain ⟨q, hqmem, hqmax⟩ := hcomp.exists_isMaxOn hne hvcont
  rw [isMaxOn_iff] at hqmax
  by_cases hqC : q ∈ parabolicCylinder U T'
  swap
  · exact ⟨q, ⟨hqmem, hqC⟩, fun p hp => hqmax p hp⟩
  exfalso
  obtain ⟨hqU, hqt⟩ := hqC
  have hqtT : q 0 ∈ Ioo 0 T := ⟨hqt.1, hqt.2.trans_lt hT'T⟩
  have hC2q : ContDiffAt ℝ 2 u q := hC2 q hqU hqtT
  have hheatq := hheat q hqU hqtT
  have hvC2 : ContDiffAt ℝ 2 v q :=
    hC2q.sub (contDiff_const.mul contDiff_timeCoord).contDiffAt
  -- spatial second-derivative test at the maximum
  have hspatial : ∀ j : Fin n, (partialDeriv j.succ)^[2] v q ≤ 0 := by
    intro j
    refine partialDeriv_iterate_two_nonpos_of_section_max hvC2 ?_
    have hcs : Continuous fun s : ℝ =>
        spacePart q + s • EuclideanSpace.single j (1 : ℝ) := by fun_prop
    have h0 : spacePart q + (0 : ℝ) • EuclideanSpace.single j (1 : ℝ) ∈ U := by
      simpa using hqU
    have hopen : ∀ᶠ s in 𝓝 (0 : ℝ),
        spacePart q + s • EuclideanSpace.single j (1 : ℝ) ∈ U :=
      hcs.continuousAt.eventually_mem (hU.mem_nhds h0)
    filter_upwards [hopen] with s hs
    refine hqmax _ (subset_closure ⟨?_, ?_⟩)
    · rwa [spacePart_add_smul_single_succ]
    · rwa [timeCoord_add_smul_single_succ]
  -- one-sided time derivative at the maximum
  have htime : 0 ≤ partialDeriv 0 v q := by
    refine partialDeriv_nonneg_of_section_eventually_le_left
      (hvC2.differentiableAt (by norm_num)) ?_
    have hIoo : Ioo (-(q 0)) 0 ∈ 𝓝[<] (0 : ℝ) := by
      refine mem_nhdsWithin.2 ⟨Ioi (-(q 0)), isOpen_Ioi, by simpa using hqt.1, ?_⟩
      rintro s ⟨hs1, hs2⟩
      exact ⟨hs1, hs2⟩
    filter_upwards [hIoo] with s hs
    refine hqmax _ (subset_closure ⟨?_, ?_⟩)
    · rwa [spacePart_add_smul_single_zero]
    · rw [timeCoord_add_smul_single_zero]
      have hs1 : -(q 0) < s := hs.1
      have hs2 : s < 0 := hs.2
      exact ⟨by linarith, by linarith [hqt.2]⟩
  -- rewrite the perturbed partials in terms of `u`
  have hudiff : DifferentiableAt ℝ u q := hC2q.differentiableAt (by norm_num)
  have htdiff : DifferentiableAt ℝ (fun p : SpaceTime n => ε * p 0) q :=
    ((contDiff_const.mul (contDiff_timeCoord (k := 1))).differentiable
      one_ne_zero).differentiableAt
  have h0t : partialDeriv 0 v q = partialDeriv 0 u q - ε := by
    rw [hv]
    rw [partialDeriv_fun_sub hudiff htdiff 0, partialDeriv_const_mul_timeCoord]
    simp
  have hjt : ∀ j : Fin n, (partialDeriv j.succ)^[2] v q = (partialDeriv j.succ)^[2] u q := by
    intro j
    rw [hv]
    rw [partialDeriv_iterate_two_fun_sub j.succ
      ((hC2q.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num))
      (Eventually.of_forall fun y =>
        ((contDiff_const.mul (contDiff_timeCoord (k := 1))).differentiable
          one_ne_zero).differentiableAt)
      (differentiableAt_partialDeriv_of_contDiffAt hC2q j.succ)
      ?_]
    · rw [partialDeriv_iterate_two_const_mul_timeCoord]
      ring
    · refine differentiableAt_partialDeriv_of_contDiffAt ?_ j.succ
      exact (contDiff_const.mul contDiff_timeCoord).contDiffAt
  -- assemble the contradiction with the heat equation
  have hsum : ∑ j : Fin n, (partialDeriv j.succ)^[2] u q ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    rw [← hjt j]
    exact hspatial j
  rw [h0t] at htime
  linarith [hheatq, hsum, htime, hε]

/-- **Weak maximum principle for the heat equation** (Evans §2.3.3): a continuous
function on the closed parabolic cylinder that is `C²` and solves the heat equation
`u_t = Δu` at interior times attains its maximum over `closure U_T` on the parabolic
boundary `Γ_T`. -/
theorem exists_parabolicBoundary_isMaxOn
    (hU : IsOpen U) (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty) (hT : 0 < T)
    (hcont : ContinuousOn u (closure (parabolicCylinder U T)))
    (hC2 : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hheat : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      partialDeriv 0 u p = ∑ j : Fin n, (partialDeriv j.succ)^[2] u p) :
    ∃ z ∈ parabolicBoundary U T, ∀ p ∈ closure (parabolicCylinder U T), u p ≤ u z := by
  -- the maximum of `u` over the compact parabolic boundary
  have hΓcomp : IsCompact (parabolicBoundary U T) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_parabolicBoundary hU)
      (((isBounded_parabolicCylinder hUbdd hT).closure).subset diff_subset)
  have hΓne := parabolicBoundary_nonempty (U := U) hUne hT
  obtain ⟨zb, hzbΓ, hzbmax⟩ :=
    hΓcomp.exists_isMaxOn hΓne (hcont.mono diff_subset)
  rw [isMaxOn_iff] at hzbmax
  refine ⟨zb, hzbΓ, ?_⟩
  -- Step 1: the bound holds below every interior time horizon
  have hstep1 : ∀ T', 0 < T' → T' < T →
      ∀ p ∈ closure (parabolicCylinder U T'), u p ≤ u zb := by
    intro T' hT'0 hT'T p hp
    have hp0 : 0 ≤ p 0 ∧ p 0 ≤ T' := by
      have := closure_parabolicCylinder_subset U T' hp
      exact ⟨this.2.1, this.2.2⟩
    -- for every ε > 0 the perturbed bound holds; let ε → 0
    have hbound : ∀ ε > (0 : ℝ), u p ≤ u zb + ε * T := by
      intro ε hε
      obtain ⟨z, hzΓ', hzmax⟩ := exists_parabolicBoundary_isMaxOn_sub_mul_time
        hU hUbdd hUne hT'0 hT'T hcont hC2 hheat hε
      have hz0 : 0 ≤ z 0 :=
        (closure_parabolicCylinder_subset U T' hzΓ'.1).2.1
      have hzΓ : z ∈ parabolicBoundary U T := parabolicBoundary_subset hT'T.le hzΓ'
      have h1 : u p - ε * p 0 ≤ u z - ε * z 0 := hzmax p hp
      have h2 : u z ≤ u zb := hzbmax z hzΓ
      nlinarith [hp0.1, hp0.2, hT'T, hz0]
    by_contra hlt
    rw [not_le] at hlt
    have hεT : (0 : ℝ) < (u p - u zb) / (2 * T) := by positivity
    have := hbound _ hεT
    have hT2 : (u p - u zb) / (2 * T) * T = (u p - u zb) / 2 := by
      field_simp
    rw [hT2] at this
    linarith
  -- Step 2a: the bound at every point of the closed cylinder with interior time
  have hintcase : ∀ r ∈ closure (parabolicCylinder U T), r 0 < T → u r ≤ u zb := by
    intro r hr hrlt
    have hrIcc := closure_parabolicCylinder_subset U T hr
    set T' : ℝ := (r 0 + T) / 2 with hT'def
    have hr0 : 0 ≤ r 0 := hrIcc.2.1
    have hT'0 : 0 < T' := by rw [hT'def]; linarith
    have hT'T : T' < T := by rw [hT'def]; linarith
    have hrT' : r 0 < T' := by rw [hT'def]; linarith
    refine hstep1 T' hT'0 hT'T r ?_
    -- `r` is approached by cylinder points of time `< T'`, hence lies in the
    -- closure of the shorter cylinder
    rw [mem_closure_iff_nhds]
    intro V hV
    have hW : V ∩ {q : SpaceTime n | q 0 < T'} ∈ 𝓝 r :=
      Filter.inter_mem hV
        ((isOpen_Iio.preimage continuous_timeCoord).mem_nhds hrT')
    obtain ⟨w, hwVW, hwC⟩ := mem_closure_iff_nhds.1 hr _ hW
    exact ⟨w, hwVW.1, hwC.1, hwC.2.1, (hwVW.2 : w 0 < T').le⟩
  -- Step 2b: extend to top-time points by approaching from below in time
  intro p hp
  have hpIcc := closure_parabolicCylinder_subset U T hp
  rcases lt_or_eq_of_le hpIcc.2.2 with hplt | hpeq
  · exact hintcase p hp hplt
  · -- the downward time translates of `p` stay in the closure at interior times
    have hkey : ∀ s : ℝ, -(T / 2) < s → s < 0 →
        p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) ∈
          closure (parabolicCylinder U T) := by
      intro s hs1 hs2
      rw [mem_closure_iff_nhds]
      intro V hV
      have hcshift : Continuous fun r : SpaceTime n =>
          r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) := by fun_prop
      have hVpre : (fun r : SpaceTime n =>
          r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) ⁻¹' V ∈ 𝓝 p :=
        hcshift.continuousAt.preimage_mem_nhds hV
      have hW : ((fun r : SpaceTime n =>
          r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) ⁻¹' V) ∩
          {r : SpaceTime n | -s < r 0} ∈ 𝓝 p := by
        refine Filter.inter_mem hVpre
          ((isOpen_Ioi.preimage continuous_timeCoord).mem_nhds ?_)
        show -s < p 0
        rw [hpeq]
        linarith
      obtain ⟨r, ⟨hrV, hrW⟩, hrC⟩ := mem_closure_iff_nhds.1 hp _ hW
      refine ⟨r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ), hrV, ?_, ?_⟩
      · rw [spacePart_add_smul_single_zero]; exact hrC.1
      · rw [timeCoord_add_smul_single_zero]
        have h1 : -s < r 0 := hrW
        have h2 : r 0 ≤ T := hrC.2.2
        exact ⟨by linarith, by linarith⟩
    -- take the limit `s → 0⁻` along the path, inside the closed cylinder
    have hpathC : Continuous fun s : ℝ =>
        p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) := by fun_prop
    have hIooT : Ioo (-(T / 2)) 0 ∈ 𝓝[<] (0 : ℝ) := by
      refine mem_nhdsWithin.2 ⟨Ioi (-(T / 2)), isOpen_Ioi, by simpa using by linarith, ?_⟩
      rintro s ⟨hs1, hs2⟩
      exact ⟨hs1, hs2⟩
    have hpath : Tendsto (fun s : ℝ =>
        p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) (𝓝[<] (0 : ℝ))
        (𝓝[closure (parabolicCylinder U T)] p) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 : Tendsto (fun s : ℝ =>
            p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) (𝓝 0)
            (𝓝 (p + (0 : ℝ) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) :=
          hpathC.continuousAt
        simp only [zero_smul, add_zero] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [hIooT] with s hs
        exact hkey s hs.1 hs.2
    have hulim : Tendsto (fun s : ℝ =>
        u (p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) (𝓝[<] (0 : ℝ))
        (𝓝 (u p)) := (hcont p hp).tendsto.comp hpath
    refine le_of_tendsto hulim ?_
    filter_upwards [hIooT] with s hs
    refine hintcase _ (hkey s hs.1 hs.2) ?_
    rw [timeCoord_add_smul_single_zero, hpeq]
    linarith [hs.2]

/-! ## Uniqueness -/

/-- **Uniqueness for the heat equation on a bounded domain** (Evans §2.3.3 Thm 4,
`thm:uniqueness-heat-bounded-domain`). Two solutions of the nonhomogeneous heat
equation `u_t = Δu + f` on the parabolic cylinder, continuous on its closure, that
agree on the parabolic boundary `Γ_T` (initial and lateral boundary data) agree on the
whole closed cylinder. Evans deduces this from the strong maximum principle; the weak
one proved above suffices, applied to the differences `±(u - v)` (which solve the
homogeneous equation — the source cancels). -/
theorem eqOn_closure_of_eqOn_parabolicBoundary {v f : SpaceTime n → ℝ}
    (hU : IsOpen U) (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty) (hT : 0 < T)
    (hcu : ContinuousOn u (closure (parabolicCylinder U T)))
    (hcv : ContinuousOn v (closure (parabolicCylinder U T)))
    (hC2u : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hC2v : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 v p)
    (hheatu : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      partialDeriv 0 u p = (∑ j : Fin n, (partialDeriv j.succ)^[2] u p) + f p)
    (hheatv : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      partialDeriv 0 v p = (∑ j : Fin n, (partialDeriv j.succ)^[2] v p) + f p)
    (hbdry : EqOn u v (parabolicBoundary U T)) :
    EqOn u v (closure (parabolicCylinder U T)) := by
  -- one-sided comparison for a difference of two solutions vanishing on the boundary
  have key : ∀ u₁ u₂ : SpaceTime n → ℝ,
      ContinuousOn u₁ (closure (parabolicCylinder U T)) →
      ContinuousOn u₂ (closure (parabolicCylinder U T)) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u₁ p) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u₂ p) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        partialDeriv 0 u₁ p = (∑ j : Fin n, (partialDeriv j.succ)^[2] u₁ p) + f p) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        partialDeriv 0 u₂ p = (∑ j : Fin n, (partialDeriv j.succ)^[2] u₂ p) + f p) →
      (∀ z ∈ parabolicBoundary U T, u₁ z = u₂ z) →
      ∀ p ∈ closure (parabolicCylinder U T), u₁ p - u₂ p ≤ 0 := by
    intro u₁ u₂ hc₁ hc₂ hC2₁ hC2₂ hheat₁ hheat₂ h₁₂
    set w : SpaceTime n → ℝ := fun q => u₁ q - u₂ q with hw
    have hwcont : ContinuousOn w (closure (parabolicCylinder U T)) := hc₁.sub hc₂
    have hwC2 : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        ContDiffAt ℝ 2 w p := fun p h1 h2 => (hC2₁ p h1 h2).sub (hC2₂ p h1 h2)
    have hwheat : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        partialDeriv 0 w p = ∑ j : Fin n, (partialDeriv j.succ)^[2] w p := by
      intro p h1 h2
      have hd₁ : DifferentiableAt ℝ u₁ p := (hC2₁ p h1 h2).differentiableAt (by norm_num)
      have hd₂ : DifferentiableAt ℝ u₂ p := (hC2₂ p h1 h2).differentiableAt (by norm_num)
      rw [hw, partialDeriv_fun_sub hd₁ hd₂ 0, hheat₁ p h1 h2, hheat₂ p h1 h2,
        show ((∑ j : Fin n, (partialDeriv j.succ)^[2] u₁ p) + f p) -
            ((∑ j : Fin n, (partialDeriv j.succ)^[2] u₂ p) + f p) =
            (∑ j : Fin n, (partialDeriv j.succ)^[2] u₁ p) -
            (∑ j : Fin n, (partialDeriv j.succ)^[2] u₂ p) from by ring,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (partialDeriv_iterate_two_fun_sub j.succ
        (((hC2₁ p h1 h2).eventually (by simp)).mono fun y hy =>
          hy.differentiableAt (by norm_num))
        (((hC2₂ p h1 h2).eventually (by simp)).mono fun y hy =>
          hy.differentiableAt (by norm_num))
        (differentiableAt_partialDeriv_of_contDiffAt (hC2₁ p h1 h2) j.succ)
        (differentiableAt_partialDeriv_of_contDiffAt (hC2₂ p h1 h2) j.succ)).symm
    obtain ⟨z, hzΓ, hzmax⟩ :=
      exists_parabolicBoundary_isMaxOn hU hUbdd hUne hT hwcont hwC2 hwheat
    intro p hp
    have h0 : w z = 0 := by rw [hw]; simp only; rw [h₁₂ z hzΓ, sub_self]
    exact (hzmax p hp).trans_eq h0
  intro p hp
  have h1 := key u v hcu hcv hC2u hC2v hheatu hheatv (fun z hz => hbdry hz) p hp
  have h2 := key v u hcv hcu hC2v hC2u hheatv hheatu (fun z hz => (hbdry hz).symm) p hp
  simp only [sub_nonpos] at h1 h2
  exact le_antisymm h1 h2

end EvansLib
