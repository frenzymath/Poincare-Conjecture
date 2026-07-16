import OpenGALib.Riemannian.Jacobi.FlowGluing

/-!
# Poincaré Ch. 1, §1.4 — composition engine for the geodesic-flow derivative

The differential of the exponential map (`cor:dc-ch5-2-5`)
is computed by chaining, along a compact geodesic `γ = γ_v : [0,1] → M`, an
alternating sequence of

* **within-chart flow steps** — the time-`τ` geodesic-flow endpoint map of the
  coordinate spray, strictly differentiable in its initial condition, whose
  derivative transports the chart Jacobi variational pair
  (`IsJacobiFieldAlongOn.variational_transport`), and
* **chart junctions** — the state transition `stateTransition β β'`, strictly
  differentiable, whose derivative carries the chart-`β` variational pair to the
  chart-`β'` variational pair of the same field
  (`stateTransition_jacobiVarPair`).

Both kinds of link are maps `E × E → E × E` (a *state* is a chart position
paired with a chart velocity) with a known strict derivative, and both *carry
one marked vector to the next* — the marked vector being the Jacobi variational
pair of the field at the boundary time/chart. This file supplies the two
context-free ingredients of the assembly:

* `hasStrictFDerivAt_comp_chain` — the **composition engine**: a finite chain of
  strictly differentiable maps `f 0, …, f (n-1)`, each sending its base point to
  the next (`f i (x i) = x (i+1)`) and its derivative sending a marked vector to
  the next (`L i (p i) = p (i+1)`), composes to a strictly differentiable map at
  `x 0` whose derivative sends `p 0` to `p n`. This is the inductive backbone of
  the flow-derivative gluing: instantiate `f i` with the alternating flow-step /
  junction maps, `x i` with the flow state at boundary `i`, and `p i` with the
  Jacobi variational pair there.

* `jacobiVarPair_of_left_eq_zero` — the **initial datum**: where the field
  vanishes (`J c = 0`), the variational pair reduces to `(0, DJ^α c)`; at the
  start of `γ = γ_v` in the chart at `p` this is exactly `(0, Z)`, the value the
  composed derivative must be evaluated on to read off `d(exp_p)_v(Z)`.

Blueprint: `cor:dc-ch5-2-5`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic

/-! ### The abstract composition engine -/

section CompChain

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Eng.** The `k`-fold left composite `f (k-1) ∘ ⋯ ∘ f 0` of a family of maps
`f : ℕ → F → F`, defined by `comp 0 = id`, `comp (k+1) = f k ∘ comp k`. -/
private def compChain (f : ℕ → F → F) : ℕ → F → F
  | 0 => id
  | k + 1 => f k ∘ compChain f k

/-- **Eng.** The `k`-fold left composite of the derivatives `L (k-1) ∘ ⋯ ∘ L 0`. -/
private def compChainDeriv (L : ℕ → F →L[ℝ] F) : ℕ → F →L[ℝ] F
  | 0 => ContinuousLinearMap.id ℝ F
  | k + 1 => (L k).comp (compChainDeriv L k)

/-- **Math.** **The composition engine for the flow-derivative gluing.** Let
`f 0, …, f (n-1) : F → F` be maps, each strictly differentiable at a base point
`x i` with derivative `L i`, and suppose the base points chain
(`f i (x i) = x (i+1)`) and a family of marked vectors chains along the
derivatives (`L i (p i) = p (i+1)`). Then there are a map `F₀ : F → F` and a
continuous linear map `D₀` such that `F₀` is strictly differentiable at `x 0`
with derivative `D₀`, `F₀` sends `x 0` to `x n`, and `D₀` sends the initial
marked vector `p 0` to the terminal one `p n`.

Instantiated with the alternating within-chart flow-step and chart-junction maps
of a compact geodesic `γ`, with `p i` the chart Jacobi variational pair of a
manifold Jacobi field at boundary `i`, this glues the one-chart derivative
identities into a single strict derivative sending the initial variational pair
`(0, Z)` to the variational pair of `Y_Z` at time `1` — the coordinate content
of `d(exp_p)_v(Z) = Y_Z(1)`.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem hasStrictFDerivAt_comp_chain {n : ℕ} (f : ℕ → F → F)
    (L : ℕ → F →L[ℝ] F) (x p : ℕ → F)
    (hf : ∀ i < n, HasStrictFDerivAt (f i) (L i) (x i))
    (hstep : ∀ i < n, f i (x i) = x (i + 1))
    (hp : ∀ i < n, L i (p i) = p (i + 1)) :
    ∃ (F₀ : F → F) (D₀ : F →L[ℝ] F),
      HasStrictFDerivAt F₀ D₀ (x 0) ∧ F₀ (x 0) = x n ∧ D₀ (p 0) = p n := by
  -- induction on the prefix length `k ≤ n`
  suffices h : ∀ k, k ≤ n →
      HasStrictFDerivAt (compChain f k) (compChainDeriv L k) (x 0) ∧
        compChain f k (x 0) = x k ∧ compChainDeriv L k (p 0) = p k by
    obtain ⟨hderiv, hbase, hmark⟩ := h n le_rfl
    exact ⟨compChain f n, compChainDeriv L n, hderiv, hbase, hmark⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, rfl, rfl⟩
    exact hasStrictFDerivAt_id (x 0)
  | succ k ih =>
    intro hk
    have hk' : k < n := hk
    obtain ⟨hderiv, hbase, hmark⟩ := ih (Nat.le_of_succ_le hk)
    -- the outer map `f k` is strictly differentiable at `x k = compChain f k (x 0)`
    have houter : HasStrictFDerivAt (f k) (L k) (compChain f k (x 0)) := by
      rw [hbase]; exact hf k hk'
    refine ⟨houter.comp (x 0) hderiv, ?_, ?_⟩
    · show f k (compChain f k (x 0)) = x (k + 1)
      rw [hbase]; exact hstep k hk'
    · show (L k).comp (compChainDeriv L k) (p 0) = p (k + 1)
      simp only [ContinuousLinearMap.comp_apply, hmark]
      exact hp k hk'

/-- **Math.** **Composition engine, marked-chain factored form.** Same hypotheses
as `hasStrictFDerivAt_comp_chain` on the maps `f i` and their base points `x i`,
but the marked-vector chaining is factored *out* of the existential: the single
composed map `F₀` and derivative `D₀` obtained from `f, L, x` transport *every*
family `p : ℕ → F` that chains along the derivatives (`L i (p i) = p (i+1)`),
sending `p 0` to `p n`.

This is the form the flow-derivative gluing needs: one composed flow derivative
`D₀`, built from the geodesic's flow-step and chart-junction links alone, must
transport the Jacobi variational pair of *every* manifold Jacobi field along `γ`
simultaneously — the pair family `p` varies with the field while `f, L, x` (hence
`D₀`) do not.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem hasStrictFDerivAt_comp_chain' {n : ℕ} (f : ℕ → F → F)
    (L : ℕ → F →L[ℝ] F) (x : ℕ → F)
    (hf : ∀ i < n, HasStrictFDerivAt (f i) (L i) (x i))
    (hstep : ∀ i < n, f i (x i) = x (i + 1)) :
    ∃ (F₀ : F → F) (D₀ : F →L[ℝ] F),
      HasStrictFDerivAt F₀ D₀ (x 0) ∧ F₀ (x 0) = x n ∧
      ∀ p : ℕ → F, (∀ i < n, L i (p i) = p (i + 1)) → D₀ (p 0) = p n := by
  have hcore : ∀ k, k ≤ n →
      HasStrictFDerivAt (compChain f k) (compChainDeriv L k) (x 0) ∧
        compChain f k (x 0) = x k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hasStrictFDerivAt_id (x 0), rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨hderiv, hbase⟩ := ih (Nat.le_of_succ_le hk)
      have houter : HasStrictFDerivAt (f k) (L k) (compChain f k (x 0)) := by
        rw [hbase]; exact hf k hk
      refine ⟨houter.comp (x 0) hderiv, ?_⟩
      show f k (compChain f k (x 0)) = x (k + 1)
      rw [hbase]; exact hstep k hk
  refine ⟨compChain f n, compChainDeriv L n, (hcore n le_rfl).1, (hcore n le_rfl).2, ?_⟩
  intro p hp
  have hmark : ∀ k, k ≤ n → compChainDeriv L k (p 0) = p k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      show (L k).comp (compChainDeriv L k) (p 0) = p (k + 1)
      simp only [ContinuousLinearMap.comp_apply, ih (Nat.le_of_succ_le hk)]
      exact hp k hk
  exact hmark n le_rfl

/-- **Math.** **Composition engine with neighbourhood semantics.** Same data as
`hasStrictFDerivAt_comp_chain'` (maps `f i` strictly differentiable at chaining
base points `x i`), together with a neighbourhood `W i` of each base point. Then
the composed map `F₀` comes with a neighbourhood `W₀` of `x 0` on which it is
computed by *iterating the links*: every `z ∈ W₀` has an orbit `orb` with
`orb 0 = z` and `orb (i+1) = f i (orb i)`, whose `i`-th state still lies in `W i`
for `i < n`, and `F₀ z = orb n`.

`W₀` is the intersection of the finitely many preimages `(f (i-1) ∘ ⋯ ∘ f 0)⁻¹(W i)`;
it is a neighbourhood of `x 0` because each partial composite is continuous at
`x 0` (being strictly differentiable there) and sends `x 0` to `x i`.

This is the missing engine step for rung 4 of the exponential differential: the
base-point-only conclusion of `hasStrictFDerivAt_comp_chain'` pins the chain down
at the single state of `γ`, whereas `d(exp_p)_v` is a derivative *in `v`* and so
needs the chain to compute the geodesic endpoint for all *nearby* initial states.
Fed the per-piece neighbourhood data of `exists_geodesic_flowstep_partition`, the
orbit `orb i` is the chart-`β i` state, at the partition time `τ i`, of the
geodesic emanating from the initial state `z`.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem hasStrictFDerivAt_comp_chain_nbhd {n : ℕ} (f : ℕ → F → F)
    (L : ℕ → F →L[ℝ] F) (x : ℕ → F) (W : ℕ → Set F)
    (hf : ∀ i < n, HasStrictFDerivAt (f i) (L i) (x i))
    (hstep : ∀ i < n, f i (x i) = x (i + 1))
    (hW : ∀ i < n, W i ∈ 𝓝 (x i)) :
    ∃ (F₀ : F → F) (D₀ : F →L[ℝ] F) (W₀ : Set F),
      HasStrictFDerivAt F₀ D₀ (x 0) ∧ F₀ (x 0) = x n ∧ W₀ ∈ 𝓝 (x 0) ∧
      (∀ p : ℕ → F, (∀ i < n, L i (p i) = p (i + 1)) → D₀ (p 0) = p n) ∧
      (∀ z ∈ W₀, ∃ orb : ℕ → F, orb 0 = z ∧
        (∀ i < n, orb i ∈ W i ∧ f i (orb i) = orb (i + 1)) ∧ F₀ z = orb n) := by
  classical
  have hcore : ∀ k, k ≤ n →
      HasStrictFDerivAt (compChain f k) (compChainDeriv L k) (x 0) ∧
        compChain f k (x 0) = x k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hasStrictFDerivAt_id (x 0), rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨hderiv, hbase⟩ := ih (Nat.le_of_succ_le hk)
      have houter : HasStrictFDerivAt (f k) (L k) (compChain f k (x 0)) := by
        rw [hbase]; exact hf k hk
      refine ⟨houter.comp (x 0) hderiv, ?_⟩
      show f k (compChain f k (x 0)) = x (k + 1)
      rw [hbase]; exact hstep k hk
  -- the composed neighbourhood: states whose first `n` iterates stay in the `W i`
  set W₀ : Set F := ⋂ i : Fin n, (compChain f (i : ℕ)) ⁻¹' (W (i : ℕ)) with hW₀def
  have hW₀ : W₀ ∈ 𝓝 (x 0) := by
    rw [hW₀def]
    refine Filter.iInter_mem.2 (fun i => ?_)
    have hi : (i : ℕ) < n := i.2
    have hcont : ContinuousAt (compChain f (i : ℕ)) (x 0) :=
      ((hcore (i : ℕ) hi.le).1).continuousAt
    exact hcont.preimage_mem_nhds (by rw [(hcore (i : ℕ) hi.le).2]; exact hW (i : ℕ) hi)
  refine ⟨compChain f n, compChainDeriv L n, W₀, (hcore n le_rfl).1, (hcore n le_rfl).2,
    hW₀, ?_, ?_⟩
  · -- the marked-vector transport, as in `hasStrictFDerivAt_comp_chain'`
    intro p hp
    have hmark : ∀ k, k ≤ n → compChainDeriv L k (p 0) = p k := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        show (L k).comp (compChainDeriv L k) (p 0) = p (k + 1)
        simp only [ContinuousLinearMap.comp_apply, ih (Nat.le_of_succ_le hk)]
        exact hp k hk
    exact hmark n le_rfl
  · -- the orbit semantics: the orbit of `z` is its family of partial composites
    intro z hz
    refine ⟨fun i => compChain f i z, rfl, fun i hi => ⟨?_, rfl⟩, rfl⟩
    have hz' : z ∈ ⋂ i : Fin n, (compChain f (i : ℕ)) ⁻¹' (W (i : ℕ)) := by
      rw [hW₀def] at hz; exact hz
    exact Set.mem_iInter.1 hz' ⟨i, hi⟩

end CompChain

/-! ### The initial variational pair -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **The variational pair where the field vanishes.** If the chart
reading `J^α` of the field vanishes at time `c`
(`chartVectorRep γ α J c = 0`, in particular whenever `J c = 0`), then the
chart-`α` Jacobi variational pair reduces to `(0, DJ^α c)`: the Christoffel
corrector `Γ^α(u̇^α, J^α)` is bilinear in `J^α` and so vanishes.

At the start of the radial geodesic `γ = γ_v` read in the chart at `p`, where
`Y_Z(0) = 0`, this is the initial datum `(0, Z)` on which the composed flow
derivative is evaluated to read off `d(exp_p)_v(Z)`.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem jacobiVarPair_of_left_eq_zero (g : RiemannianMetric I M) (α : M)
    (γ : ℝ → M) (J DJ : ℝ → E) (c : ℝ)
    (hJ : chartVectorRep (I := I) γ α J c = 0) :
    jacobiVarPair (I := I) g α γ J DJ c
      = (0, chartVectorRep (I := I) γ α DJ c) := by
  have hz : chartChristoffelContraction (I := I) g α
      (deriv (fun t => extChartAt I α (γ t)) c) (0 : E)
      (extChartAt I α (γ c)) = 0 := by
    rw [chartChristoffelContraction_symm, chartChristoffelContraction_zero_left]
  simp only [jacobiVarPair, hJ, hz, sub_zero]

end Riemannian.Jacobi

end
