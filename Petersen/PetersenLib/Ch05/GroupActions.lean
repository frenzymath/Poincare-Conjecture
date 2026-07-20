import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Petersen Ch. 5, §5.6 — proper isometric actions, orbits, isotropy groups

The group-action scaffolding of Petersen §5.6.3 (the Slice Theorem), stated at
the level of a topological group `H` acting on a space `M`.

* `orbit H p` (`def:pet-ch5-proper-action`) — the **orbit** `Hp = {h·p | h ∈ H}`.
* `actionIsotropyGroup H p` (`def:pet-ch5-proper-action`) — the **isotropy
  group** (stabilizer) `H_p = {h ∈ H | h·p = p}`, a subgroup of `H`.
* `IsProperAction H M` (`def:pet-ch5-proper-action`) — the action is **proper**
  when `H × M → M × M`, `(h, p) ↦ (h·p, p)`, is a proper map.

These wrap the mathlib group-action / proper-map library so Petersen's later
Slice-Theorem statements have named hooks; the accompanying lemmas record the
basic facts quoted in the definition (`p ∈ Hp`; `H_p` membership; freeness).

Reference: Petersen, *Riemannian Geometry*, 3rd ed., §5.6.
-/

noncomputable section

namespace PetersenLib

variable (H : Type*) {M : Type*}

/-! ## Orbits -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-proper-action`): the **orbit**
`Hp = {h·p | h ∈ H}` of the point `p` under an action of `H` on `M`. -/
def orbit [SMul H M] (p : M) : Set M := Set.range fun h : H => h • p

@[simp] theorem mem_orbit_iff [SMul H M] {p q : M} :
    q ∈ orbit H p ↔ ∃ h : H, h • p = q := Iff.rfl

/-- **Math.** `p` lies on its own orbit, witnessed by the identity `1 · p = p`. -/
theorem self_mem_orbit [Monoid H] [MulAction H M] (p : M) : p ∈ orbit H p :=
  ⟨1, one_smul H p⟩

/-! ## Isotropy groups -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-proper-action`): the **isotropy
group** (stabilizer) `H_p = {h ∈ H | h·p = p}` at `p`, a subgroup of `H`. -/
def actionIsotropyGroup [Group H] [MulAction H M] (p : M) : Subgroup H :=
  MulAction.stabilizer H p

@[simp] theorem mem_actionIsotropyGroup [Group H] [MulAction H M] {p : M} {h : H} :
    h ∈ actionIsotropyGroup H p ↔ h • p = p :=
  MulAction.mem_stabilizer_iff

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-proper-action`): the isotropy group
**transforms by conjugation along an orbit**, `H_{h·p} = h H_p h⁻¹` (here as the
image of `H_p` under the conjugation automorphism `MulAut.conj h`). -/
theorem actionIsotropyGroup_smul [Group H] [MulAction H M] (h : H) (p : M) :
    actionIsotropyGroup H (h • p)
      = (actionIsotropyGroup H p).map (MulAut.conj h).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj h p

/-- **Math.** The action is **free** at `p` exactly when the isotropy group is
trivial, `H_p = {e}` — the definition of a free action, pointwise. -/
theorem actionIsotropyGroup_eq_bot_iff [Group H] [MulAction H M] {p : M} :
    actionIsotropyGroup H p = ⊥ ↔ ∀ h : H, h • p = p → h = 1 := by
  rw [actionIsotropyGroup, eq_bot_iff, SetLike.le_def]
  constructor
  · intro hsub h hh
    simpa using hsub (MulAction.mem_stabilizer_iff.mpr hh)
  · intro hall h hh
    simpa using hall h (MulAction.mem_stabilizer_iff.mp hh)

/-! ## Proper actions -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-proper-action`): an action of a
topological group `H` on `M` is **proper** if the map `H × M → M × M`,
`(h, p) ↦ (h·p, p)`, is a proper map (in the closed / Bourbaki-proper form
`IsProperMap`: universally closed with compact fibres). -/
def IsProperAction (H M : Type*) [SMul H M] [TopologicalSpace H] [TopologicalSpace M] :
    Prop :=
  IsProperMap fun hp : H × M => (hp.1 • hp.2, hp.2)

end PetersenLib

end
