import PoincareConjecture
import PoincareConjectureTopologyTests
import PoincareConjectureOrientabilityTests
import Lean.Util.CollectAxioms

/-!
# Regression tests for the primary comparison layer

These proofs exercise the terminal-endpoint counterexample, a genuine
discontinuous downward step at an interior partition point, the degenerate
partition, and the scalar barrier's initial value. This is a default Lake
target, so `lake build` checks the regression statements as well as the library.
-/

open Set Filter
open scoped Topology
open PoincareConjecture

namespace PoincareConjectureTests

/-- The value at the terminal endpoint cannot be left unconstrained. -/
noncomputable def terminalJump (t : ℝ) : ℝ := if t < 1 then 0 else 1

theorem terminalJump_continuousOn : ContinuousOn terminalJump (Ico 0 1) := by
  apply (show ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ico 0 1) from continuousOn_const).congr
  intro t ht
  simp [terminalJump, ht.2]

theorem terminalJump_dini : ∀ t ∈ Ico (0 : ℝ) 1, UpperRightDiniLE terminalJump t 0 := by
  intro t ht r hr
  have hnear : ∀ᶠ z in 𝓝[>] t, z < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds ht.2)
  filter_upwards [hnear] with z hz
  simpa [slope_def_field, terminalJump, ht.2, hz] using hr

/-- A checked counterexample to the original closed-interval conclusion when
only interior jump times are controlled (there are none in this partition). -/
theorem endpoint_control_is_necessary :
    ∃ f : ℝ → ℝ, ContinuousOn f (Ico 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, UpperRightDiniLE f t 0) ∧
      f 0 = 0 ∧ ¬ f 1 ≤ 0 := by
  exact ⟨terminalJump, terminalJump_continuousOn, terminalJump_dini,
    by norm_num [terminalJump], by norm_num [terminalJump]⟩

/-- The repaired endpoint assumption really rejects the counterexample. -/
theorem terminalJump_not_lowerSemicontinuous :
    ¬ LowerSemicontinuousWithinAt terminalJump (Iio 1) 1 := by
  intro h
  have hle := le_at_endpoint_of_no_upward_jump (a := 0) (G := fun _ => 0)
    (by norm_num) continuousOn_const h (fun t ht => by simp [terminalJump, ht.2])
  norm_num [terminalJump] at hle

/-- A genuine downward jump at time `1`; right-continuity, not two-sided
continuity, is what permits a Dini bound at the jump. -/
noncomputable def downwardStep (t : ℝ) : ℝ := if t < 1 then 0 else -1

theorem downwardStep_dini (t : ℝ) : UpperRightDiniLE downwardStep t 0 := by
  intro r hr
  by_cases ht : t < 1
  · have hnear : ∀ᶠ z in 𝓝[>] t, z < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds ht)
    filter_upwards [hnear] with z hz
    simpa [slope_def_field, downwardStep, ht, hz] using hr
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : ¬ z < 1 := not_lt.mpr ((le_of_not_gt ht).trans (le_of_lt hz))
    simpa [slope_def_field, downwardStep, ht, hz'] using hr

theorem downwardStep_lowerSemicontinuous {t : ℝ} (ht : 1 ≤ t) :
    LowerSemicontinuousWithinAt downwardStep (Iio t) t := by
  intro r hr
  have hr' : r < -1 := by simpa [downwardStep, not_lt.mpr ht] using hr
  exact Eventually.of_forall fun z => by
    change r < (if z < 1 then (0 : ℝ) else -1)
    split_ifs <;> linarith

/-- The downward-jump test genuinely lies outside ordinary differentiable ODE
comparison: its width is not even continuous at the interior jump. -/
theorem downwardStep_not_continuousAt : ¬ ContinuousAt downwardStep 1 := by
  intro h
  have hleft : Tendsto downwardStep (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[<] (1 : ℝ)) (𝓝 0)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t < 1 at ht
    simp [downwardStep, ht]
  have heq := tendsto_nhds_unique hleft (h.mono_left nhdsWithin_le_nhds)
  norm_num [downwardStep] at heq

/-- Exercise the full finite-jump theorem with an interior discontinuity and a
controlled final endpoint. The proof does not assume a left derivative at `1`. -/
theorem downwardStep_comparison : ∀ t ∈ Icc (0 : ℝ) 2, downwardStep t ≤ 0 := by
  suffices h : ∀ t ∈ Icc ((0 : ℕ) : ℝ) ((2 : ℕ) : ℝ), downwardStep t ≤ 0 by
    simpa only [Nat.cast_zero, Nat.cast_ofNat] using h
  apply dini_le_of_finite_jumps (τ := fun j : ℕ => (j : ℝ)) (n := 2)
    (f := downwardStep) (G := fun _ => 0) (ψ := fun _ _ => 0)
  · intro i hi j hj hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
  · intro j hj
    interval_cases j
    · apply (show ContinuousOn (fun _ : ℝ => (0 : ℝ)) _ from continuousOn_const).congr
      intro t ht
      simp only [Nat.cast_zero, Nat.cast_one, zero_add] at ht
      simp [downwardStep, ht.2]
    · apply (show ContinuousOn (fun _ : ℝ => (-1 : ℝ)) _ from continuousOn_const).congr
      intro t ht
      have ht' : 1 ≤ t := by simpa using ht.1
      simp [downwardStep, not_lt.mpr ht']
  · exact continuousOn_const
  · fun_prop
  · intro t _
    exact downwardStep_dini t
  · intro t _
    exact (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt
  · intro j _
    apply downwardStep_lowerSemicontinuous
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  · norm_num [downwardStep]

/-- The empty partition requires no artificial positive-time assumption. -/
example (f G : ℝ → ℝ) (s : ℝ) (h : f s ≤ G s) :
    ∀ t ∈ Icc s s, f t ≤ G t := by
  apply dini_le_of_finite_jumps (τ := fun _ => s) (n := 0) (ψ := fun _ _ => 0)
  · intro i hi j hj hij
    simp only [mem_Iic] at hi hj
    omega
  · simp
  · simp
  · fun_prop
  · simp
  · simp
  · simp
  · exact h

/-- The initial condition is exact for arbitrary initial width, not just for a
single numerical example. -/
example (s A : ℝ) (hs : 0 ≤ s) : extinctionBarrier s A s = A :=
  extinctionBarrier_initial hs A

end PoincareConjectureTests

/-!
Audit every declaration in the production and regression-test namespaces.
This checks transitive kernel dependencies, not just a textual placeholder
count. In particular, a theorem depending on `sorryAx`, `Lean.ofReduceBool`,
or a newly introduced project axiom makes the default build fail.
-/
run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareConjecture).isPrefixOf name || (`PoincareConjectureTests).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on non-whitelisted axiom {axiomName}"
      count := count + 1
  if count == 0 then
    throwError "The project axiom audit unexpectedly checked no declarations"
