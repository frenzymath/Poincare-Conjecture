import PoincareLib.Ch02.FlowBox
import PoincareLib.Ch02.GradientFlow

/-!
# Morgan–Tian Ch. 2 — joint continuity of the global flow

Blueprint `lem:parallel-gradient-flow`(2), regularity of the flow. The global
flow `θ` of a smooth vector field with global integral curves
(`smoothVectorFieldFlow`, `GradientFlow.lean`) is **jointly continuous** in
`(t, x)`, and hence each time-`t` map `θ_t` is a **homeomorphism** of `M`
with inverse `θ_{-t}`:

* `smoothVectorFieldFlow_eqOn_localFlow` — on a flow box (`FlowBox.lean`) the
  global flow agrees with the local flow, by uniqueness of integral curves.
* `continuous_smoothVectorFieldFlow_comp` — continuity of `x ↦ θ_t x`: cover
  the compact trajectory arc `{θ_u x₀ : |u| ≤ |t|}` by one flow box, split
  `θ_t` into `n` steps `θ_{t/n}` of size `< η` (group law), and compose the
  local-flow continuity of the steps.
* `continuous_smoothVectorFieldFlow` — joint continuity of `(t, x) ↦ θ_t x`:
  near `(t₀, x₀)` write `θ_t x = Φ (θ_{t₀} x) (t - t₀)` with `Φ` the local
  flow of a box around `θ_{t₀} x₀`.
* `smoothVectorFieldFlowHomeomorph` — `θ_t` as a homeomorphism of `M`.

The blueprint claims `θ` is jointly *smooth*; smoothness in `x` requires
`C¹`-dependence of integral curves on initial conditions at manifold level
(not yet formalized — per-chart versions exist in DoCarmo
`FlowC1Dependence.lean`). Joint continuity is the part needed for the
level-set and splitting arguments that consume the flow topologically.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Function Riemannian
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M]

variable (X : SmoothVectorField I M)
  (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ (fun q => X q))

/-- **Math.** On a flow box of `X`, the global flow agrees with the local
flow: `θ_s y = Φ y s` for `y ∈ U` and `|s| < η`. Both `s ↦ θ_s y` and `Φ y`
are integral curves of `X` on `(-η, η)` through `y`, so they coincide by
uniqueness of integral curves. -/
theorem smoothVectorFieldFlow_eqOn_localFlow {η : ℝ} {U : Set M} {Φ : M → ℝ → M}
    (hη : 0 < η) (h0 : ∀ x ∈ U, Φ x 0 = x)
    (hIC : ∀ x ∈ U, IsMIntegralCurveOn (Φ x) (fun q => X q) (Ioo (-η) η))
    {y : M} (hy : y ∈ U) {s : ℝ} (hs : s ∈ Ioo (-η) η) :
    smoothVectorFieldFlow X hex s y = Φ y s := by
  have hX1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, X x⟩ : TangentBundle I M)) := fun p =>
    (X.smooth p).of_le (by norm_num)
  refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (mem_Ioo.mpr ⟨neg_neg_iff_pos.mpr hη, hη⟩) hX1
    ((isMIntegralCurve_smoothVectorFieldFlow X hex y).isMIntegralCurveOn _)
    (hIC y hy) ?_ hs
  rw [smoothVectorFieldFlow_zero, h0 y hy]

/-- **Math.** The `n`-step iteration bound: if the first `n` points
`θ_{j·s} x`, `j < n`, of the discrete orbit with step `s`, `|s| < η`, lie in
the domain `U` of a flow box, then `x ↦ θ_{n·s} x` is continuous at `x`.
Induction on `n` via the group law `θ_{(j+1)s} = θ_s ∘ θ_{js}` and the joint
continuity of the local flow. -/
theorem continuousAt_smoothVectorFieldFlow_nsmul {η : ℝ} {U : Set M}
    {Φ : M → ℝ → M} (hη : 0 < η) (hUopen : IsOpen U)
    (h0 : ∀ x ∈ U, Φ x 0 = x)
    (hIC : ∀ x ∈ U, IsMIntegralCurveOn (Φ x) (fun q => X q) (Ioo (-η) η))
    (hcont : ContinuousOn ↿Φ (U ×ˢ Ioo (-η) η))
    {s : ℝ} (hs : s ∈ Ioo (-η) η) :
    ∀ (n : ℕ) (x : M), (∀ j : ℕ, j < n → smoothVectorFieldFlow X hex (j * s) x ∈ U) →
      ContinuousAt (smoothVectorFieldFlow X hex (n * s)) x := by
  intro n
  induction n with
  | zero =>
    intro x _
    have : smoothVectorFieldFlow X hex ((0 : ℕ) * s) = id := by
      funext y
      simp [smoothVectorFieldFlow_zero]
    rw [this]
    exact continuousAt_id
  | succ n ih =>
    intro x hx
    have hgroup : smoothVectorFieldFlow X hex ((n + 1 : ℕ) * s) =
        fun y => smoothVectorFieldFlow X hex s
          (smoothVectorFieldFlow X hex (n * s) y) := by
      funext y
      rw [← smoothVectorFieldFlow_add]
      congr 1
      push_cast
      ring
    rw [hgroup]
    have hxn : smoothVectorFieldFlow X hex (n * s) x ∈ U :=
      hx n (Nat.lt_succ_self n)
    -- continuity of the single step `θ_s` at the `n`-th orbit point
    have hstep : ContinuousAt (smoothVectorFieldFlow X hex s)
        (smoothVectorFieldFlow X hex (n * s) x) := by
      have hΦs : ContinuousAt (fun y => Φ y s)
          (smoothVectorFieldFlow X hex (n * s) x) := by
        have hjoint : ContinuousAt ↿Φ (smoothVectorFieldFlow X hex (n * s) x, s) :=
          hcont.continuousAt ((hUopen.prod isOpen_Ioo).mem_nhds ⟨hxn, hs⟩)
        exact ContinuousAt.comp (f := fun y : M => ((y, s) : M × ℝ)) hjoint
          ((continuous_id.prodMk continuous_const).continuousAt)
      refine hΦs.congr ?_
      filter_upwards [hUopen.mem_nhds hxn] with y hy
      exact (smoothVectorFieldFlow_eqOn_localFlow X hex hη h0 hIC hy hs).symm
    exact hstep.comp (ih x fun j hj => hx j (hj.trans (Nat.lt_succ_self n)))

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2), continuity in the
initial point: each time-`t` flow map `θ_t : M → M` is continuous. The
compact trajectory arc `{θ_u x₀ : |u| ≤ |t|}` is covered by one flow box
(`exists_localFlow_of_isCompact`); splitting `θ_t` into `n` equal steps of
size `< η` reduces to `continuousAt_smoothVectorFieldFlow_nsmul`. -/
theorem continuous_smoothVectorFieldFlow_comp (t : ℝ) :
    Continuous (smoothVectorFieldFlow X hex t) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  -- the compact trajectory arc through `x₀`
  have harc : IsCompact ((fun u => smoothVectorFieldFlow X hex u x₀) ''
      Icc (-|t|) |t|) :=
    isCompact_Icc.image (continuous_smoothVectorFieldFlow_apply X hex x₀)
  obtain ⟨η, U, Φ, hη, hUopen, hKU, h0, hIC, hcont⟩ :=
    exists_localFlow_of_isCompact X harc
  -- split `t` into `n` steps of size `< η`
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / η)
  have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
  have hn0 : n ≠ 0 := by exact_mod_cast hnpos.ne'
  set s : ℝ := t / n with hs_def
  have htn : |t| < n * η := by
    rw [div_lt_iff₀ hη] at hn
    linarith
  have hsabs : |s| < η := by
    rw [hs_def, abs_div, Nat.abs_cast, div_lt_iff₀ hnpos]
    linarith [htn]
  have hsmem : s ∈ Ioo (-η) η := mem_Ioo.mpr (abs_lt.mp hsabs)
  have hts : t = n * s := by
    rw [hs_def, mul_div_cancel₀ _ hnpos.ne']
  rw [hts]
  refine continuousAt_smoothVectorFieldFlow_nsmul X hex hη hUopen h0 hIC hcont
    hsmem n x₀ fun j hj => hKU ⟨j * s, ?_, rfl⟩
  -- `j·s` lies in the arc window `[-|t|, |t|]`
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj.le
  have hjs : |(j : ℝ) * s| ≤ |t| := by
    calc |(j : ℝ) * s| = j * (|t| / n) := by
          rw [abs_mul, Nat.abs_cast, hs_def, abs_div, Nat.abs_cast]
      _ ≤ n * (|t| / n) := by gcongr
      _ = |t| := mul_div_cancel₀ _ hnpos.ne'
  exact mem_Icc.mpr (abs_le.mp hjs)

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2), regularity of the
flow: the global flow `θ : ℝ × M → M` of a smooth vector field with global
integral curves is **jointly continuous**. Near `(t₀, x₀)` one has
`θ_t x = Φ (θ_{t₀} x) (t - t₀)` with `Φ` the local flow of a box around
`θ_{t₀} x₀`, a composition of continuous maps. (Joint smoothness — the full
blueprint claim — additionally requires smooth dependence of integral curves
on initial conditions, not yet available at manifold level.) -/
theorem continuous_smoothVectorFieldFlow :
    Continuous fun p : ℝ × M => smoothVectorFieldFlow X hex p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  set y₀ : M := smoothVectorFieldFlow X hex t₀ x₀ with hy₀_def
  obtain ⟨η, U, Φ, hη, hUopen, hKU, h0, hIC, hcont⟩ :=
    exists_localFlow_of_isCompact X (isCompact_singleton : IsCompact {y₀})
  have hy₀U : y₀ ∈ U := hKU rfl
  -- the reparametrized flow through the box
  have hkey : ∀ᶠ p : ℝ × M in 𝓝 (t₀, x₀),
      smoothVectorFieldFlow X hex p.1 p.2 =
        Φ (smoothVectorFieldFlow X hex t₀ p.2) (p.1 - t₀) := by
    have h1 : ∀ᶠ p : ℝ × M in 𝓝 (t₀, x₀),
        smoothVectorFieldFlow X hex t₀ p.2 ∈ U := by
      have hc : ContinuousAt (fun p : ℝ × M => smoothVectorFieldFlow X hex t₀ p.2)
          (t₀, x₀) :=
        ((continuous_smoothVectorFieldFlow_comp X hex t₀).comp continuous_snd)
          |>.continuousAt
      exact hc.eventually_mem (hUopen.mem_nhds hy₀U)
    have h2 : ∀ᶠ p : ℝ × M in 𝓝 (t₀, x₀), p.1 - t₀ ∈ Ioo (-η) η := by
      have hc : ContinuousAt (fun p : ℝ × M => p.1 - t₀) (t₀, x₀) :=
        (continuous_fst.sub continuous_const).continuousAt
      apply hc.eventually_mem
      rw [show t₀ - t₀ = (0 : ℝ) by ring]
      exact isOpen_Ioo.mem_nhds ⟨neg_neg_iff_pos.mpr hη, hη⟩
    filter_upwards [h1, h2] with p hp1 hp2
    rw [← smoothVectorFieldFlow_eqOn_localFlow X hex hη h0 hIC hp1 hp2,
      ← smoothVectorFieldFlow_add]
    congr 1
    ring
  refine ContinuousAt.congr ?_ (hkey.mono fun p hp => hp.symm)
  -- continuity of the reparametrized composition
  have hΦjoint : ContinuousAt ↿Φ (y₀, 0) :=
    hcont.continuousAt ((hUopen.prod isOpen_Ioo).mem_nhds
      ⟨hy₀U, ⟨neg_neg_iff_pos.mpr hη, hη⟩⟩)
  have hinner : ContinuousAt
      (fun p : ℝ × M => ((smoothVectorFieldFlow X hex t₀ p.2 : M), p.1 - t₀))
      (t₀, x₀) := by
    apply ContinuousAt.prodMk
    · exact ((continuous_smoothVectorFieldFlow_comp X hex t₀).comp
        continuous_snd).continuousAt
    · exact (continuous_fst.sub continuous_const).continuousAt
  have : ContinuousAt (↿Φ ∘ fun p : ℝ × M =>
      ((smoothVectorFieldFlow X hex t₀ p.2 : M), p.1 - t₀)) (t₀, x₀) := by
    apply ContinuousAt.comp _ hinner
    simpa [hy₀_def, sub_self] using hΦjoint
  exact this

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2): each time-`t` flow
map `θ_t` is a **homeomorphism** of `M`, with inverse `θ_{-t}`. (The
blueprint's "diffeomorphism" claim, at the level of homeomorphisms;
smoothness of `θ_t` awaits manifold-level smooth dependence on initial
conditions.) -/
def smoothVectorFieldFlowHomeomorph (t : ℝ) : M ≃ₜ M where
  toFun := smoothVectorFieldFlow X hex t
  invFun := smoothVectorFieldFlow X hex (-t)
  left_inv x := smoothVectorFieldFlow_neg_apply X hex t x
  right_inv x := by
    simpa using smoothVectorFieldFlow_neg_apply X hex (-t) x
  continuous_toFun := continuous_smoothVectorFieldFlow_comp X hex t
  continuous_invFun := continuous_smoothVectorFieldFlow_comp X hex (-t)

@[simp] lemma smoothVectorFieldFlowHomeomorph_apply (t : ℝ) (x : M) :
    smoothVectorFieldFlowHomeomorph X hex t x = smoothVectorFieldFlow X hex t x :=
  rfl

end PoincareLib

end
