/-
Appendix A, "Review of Smooth Manifolds", §"Vector Bundles": the non-vanishing
locus of a continuous section is open.
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic

namespace LeeLib.AppendixA

open Bundle Set
open scoped Manifold Topology

section

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **The non-vanishing locus of a continuous section of a vector bundle is open.** -/
theorem isOpen_setOf_section_ne_zero {s : ∀ x, V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x)) :
    IsOpen {x : B | s x ≠ 0} := by
  set σ : B → TotalSpace F V := fun x ↦ TotalSpace.mk' F x (s x) with hσ
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  set e := trivializationAt F V x₀ with he
  have hx₀e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  -- Through a trivialization, vanishing of the section is vanishing of its principal part.
  have key : ∀ x ∈ e.baseSet, ((e (σ x)).2 = 0 ↔ s x = 0) := by
    intro x hx
    have h := (e.continuousLinearEquivAt ℝ x hx).map_eq_zero_iff (x := s x)
    simpa [hσ, Trivialization.continuousLinearEquivAt_apply] using h
  have hsrc : σ x₀ ∈ e.source := by rw [Trivialization.mem_source]; exact hx₀e
  have h_e : ContinuousAt (e : TotalSpace F V → B × F) (σ x₀) :=
    e.continuousOn.continuousAt (e.open_source.mem_nhds hsrc)
  have hcont : ContinuousAt (fun x ↦ (e (σ x)).2) x₀ := (h_e.comp hs.continuousAt).snd
  have hne : (e (σ x₀)).2 ≠ 0 := fun h ↦ hx₀ ((key x₀ hx₀e).mp h)
  filter_upwards [hcont (isOpen_ne.mem_nhds hne), e.open_baseSet.mem_nhds hx₀e] with x hx hxe
  exact fun h0 ↦ hx ((key x hxe).mpr h0)

end

end LeeLib.AppendixA
