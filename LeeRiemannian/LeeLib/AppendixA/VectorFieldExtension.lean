/-
Appendix A, "Review of Smooth Manifolds": the **extension lemma for vector
fields**, in the pointwise form used by Chapter 2.

Lee states the general extension lemma (his Lemma A.23) for a smooth vector field
defined on a closed subset.  What Chapter 2 actually consumes is the special case
of a *single point*:

> every tangent vector `v ∈ T_p M` is the value at `p` of some global smooth
> vector field `Z ∈ 𝔛(M)`.

## Why this is not immediate

`TangentSpace I p` is a fibre of a bundle, and a vector in it carries no
information about neighbouring fibres, so producing a *global* field requires
gluing.  The two ingredients are:

* **locally**, a vector extends: near `p` the constant section of a local
  trivialization `e` — `x ↦ e.symm x c`, where `c` is the fibre coordinate of `v`
  — is smooth and takes the value `v` at `p`.  Away from `p`, the zero section
  works.
* **globally**, these are glued by mathlib's
  `exists_contMDiffSection_forall_mem_convex_of_local`, whose hypothesis is a
  *convex* fibrewise constraint set.  Taking `t p = {v}` and `t x = univ` for
  `x ≠ p` makes the constraint convex (a singleton and the whole fibre both are),
  and the glued section then satisfies `s p ∈ {v}`, i.e. `s p = v`.

The convexity is what makes a partition of unity legitimate here: a convex
combination of local sections each lying in `t x` still lies in `t x`.  This is
the same mechanism by which a Riemannian metric is built in
`LeeLib.Ch02.exists_riemannianMetric` (there `t x` is the set of positive
definite forms, convex for the same reason).

## Provenance

The construction is the one vendored throughout this workspace (`OpenGALib`,
`PetersenLib.Vendored.OpenGA.Manifold.DoCarmoCh2.exists_smoothVectorField_eq`).
Cross-project `lake` dependencies are banned in this workspace, so each project
vendors its own copy; this is Lee's.
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace LeeLib.AppendixA

open Bundle Set
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **The extension lemma for vector fields, at a point** (Lee, the case of
Lemma A.23 used in Chapter 2): *every tangent vector is the value of a global
smooth vector field.*

Given `p : M` and `v : T_p M`, there is a smooth vector field `Z` on `M` with
`Z p = v`.

The σ-compactness and Hausdorff hypotheses are Lee's standing assumptions on
manifolds; they are what make smooth partitions of unity available, and the
statement is false without some such assumption. -/
theorem exists_contMDiffVectorField_eq (p : M) (v : TangentSpace I p) :
    ∃ Z : ∀ x : M, TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => TotalSpace.mk' E x (Z x)) ∧ Z p = v := by
  classical
  -- Constrain the section to be `v` at `p`, and unconstrained elsewhere.  Both
  -- constraint sets are convex, which is what the gluing lemma needs.
  set t : (x : M) → Set (TangentSpace I x) := fun x => if x = p then {v} else univ with ht
  have hconv : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases h : x = p
    · simp only [ht, if_pos h]; exact convex_singleton v
    · simp only [ht, if_neg h]; exact convex_univ
  have hlocal : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ s_loc : (x : M) → TangentSpace I x,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, s_loc x⟩ : TangentBundle I M)) U ∧
        ∀ y ∈ U, s_loc y ∈ t y := by
    intro x₀
    by_cases hx : x₀ = p
    · -- Near `p`: the section that is constant in the trivialization at `p`.
      subst hx
      set e := trivializationAt E (TangentSpace I) x₀ with he
      refine ⟨e.baseSet,
        e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀),
        fun x => e.symm x (e ⟨x₀, v⟩).2, ?_, ?_⟩
      · rw [Trivialization.contMDiffOn_section_baseSet_iff e]
        refine ContMDiffOn.congr (contMDiffOn_const (c := (e ⟨x₀, v⟩).2)) ?_
        intro x hx
        simp only [Trivialization.apply_mk_symm e hx]
      · intro y hy
        by_cases hyp : y = x₀
        · subst hyp
          simp only [ht, if_pos rfl, mem_singleton_iff]
          exact Trivialization.symm_apply_apply_mk e hy v
        · simp only [ht, if_neg hyp]; exact mem_univ _
    · -- Away from `p`: the zero section, which is unconstrained there.
      refine ⟨{p}ᶜ, (isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hx),
        fun x => (0 : TangentSpace I x), ?_, ?_⟩
      · exact (contMDiff_zeroSection ℝ (TangentSpace I)).contMDiffOn
      · intro y hy
        have hyne : y ≠ p := by simpa using hy
        simp only [ht, if_neg hyne]; exact mem_univ _
  obtain ⟨s, hs⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local I (n := (⊤ : ℕ∞))
      (TangentSpace I) t hconv hlocal
  have hsp : s p = v := by
    have := hs p; simpa only [ht, if_pos rfl, mem_singleton_iff] using this
  exact ⟨fun x => s x, s.contMDiff, hsp⟩

end LeeLib.AppendixA
