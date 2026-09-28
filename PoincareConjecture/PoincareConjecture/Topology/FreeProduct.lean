import Mathlib.GroupTheory.CoprodI
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Factor elimination for the topological endgame

We use Mathlib's actual indexed free product, not an abstract structure with
injective factor maps assumed. The factor injections come from its universal
property. The results apply to arbitrary index types, including the finite
index sets produced by connected-sum reconstruction.

This file does not prove the geometric Seifert--van Kampen connected-sum
calculation. The theorem using a fundamental-group isomorphism leaves that
specific geometric input explicit.
-/

namespace PoincareConjecture

/-- For a path-connected space, triviality of the actual fundamental group
at one basepoint implies simple connectivity. Basepoint change is supplied
by the path groupoid, not an extra assumption for each loop. -/
theorem simplyConnected_of_fundamentalGroup_subsingleton
    {M : Type*} [TopologicalSpace M] [PathConnectedSpace M] (x : M)
    [Subsingleton (FundamentalGroup M x)] : SimplyConnectedSpace M := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro y γ
  letI : Subsingleton (FundamentalGroup M y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y).surjective.subsingleton
  have hγ : (FundamentalGroup.fromPath ⟦γ⟧ : FundamentalGroup M y) =
      FundamentalGroup.fromPath ⟦Path.refl y⟧ := Subsingleton.elim _ _
  exact Quotient.eq.mp (congrArg FundamentalGroup.toPath hγ)

variable {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]

/-- Triviality of an actual free product implies triviality of each factor. -/
theorem freeProduct_factor_subsingleton [Subsingleton (Monoid.CoprodI G)] (i : ι) :
    Subsingleton (G i) :=
  (Monoid.CoprodI.of_injective (M := G) i).subsingleton

/-- Conversely, a free product all of whose factors are trivial is trivial. -/
theorem freeProduct_subsingleton [∀ i, Subsingleton (G i)] :
    Subsingleton (Monoid.CoprodI G) := by
  have hone : ∀ x : Monoid.CoprodI G, x = 1 := by
    intro x
    induction x using Monoid.CoprodI.induction_on with
    | one => rfl
    | of i g =>
        have : g = 1 := Subsingleton.elim _ _
        simp [this]
    | mul x y hx hy => simp [hx, hy]
  exact ⟨fun x y => (hone x).trans (hone y).symm⟩

/-- Exact triviality criterion for the indexed free product. -/
theorem freeProduct_subsingleton_iff :
    Subsingleton (Monoid.CoprodI G) ↔ ∀ i, Subsingleton (G i) := by
  constructor
  · intro h
    letI := h
    exact freeProduct_factor_subsingleton G
  · intro h
    letI := h
    exact freeProduct_subsingleton G

/-- A simply connected space whose fundamental group has a given free-product
decomposition has trivial factor groups. The isomorphism, not injectivity of
unrelated proxy maps, is the explicit geometric input. -/
theorem fundamentalGroup_freeProduct_factors
    {M : Type*} [TopologicalSpace M] [SimplyConnectedSpace M] (x : M)
    (e : FundamentalGroup M x ≃* Monoid.CoprodI G) : ∀ i, Subsingleton (G i) := by
  letI : Subsingleton (Monoid.CoprodI G) := e.surjective.subsingleton
  exact freeProduct_factor_subsingleton G

/-- A trivial free product has no factor isomorphic to the infinite cyclic
group. `Multiplicative ℤ` records the intended group law explicitly. -/
theorem freeProduct_no_infiniteCyclic_factor [Subsingleton (Monoid.CoprodI G)] (i : ι) :
    IsEmpty (G i ≃* Multiplicative ℤ) := by
  letI := freeProduct_factor_subsingleton G i
  constructor
  intro e
  have h : Subsingleton (Multiplicative ℤ) := e.surjective.subsingleton
  exact (zero_ne_one : (0 : ℤ) ≠ 1)
    (congrArg Multiplicative.toAdd (h.elim (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 1)))

/-- Given the actual van Kampen isomorphism, path-connected manifold factors
of a simply connected total space are simply connected. The geometric
construction of that isomorphism remains explicit, not hidden in a definition. -/
theorem simplyConnected_factors_of_fundamentalGroup_coprod
    {M : Type*} [TopologicalSpace M] [SimplyConnectedSpace M] (x : M)
    (N : ι → Type*) [∀ i, TopologicalSpace (N i)] [∀ i, PathConnectedSpace (N i)]
    (b : ∀ i, N i)
    (e : FundamentalGroup M x ≃* Monoid.CoprodI (fun i => FundamentalGroup (N i) (b i))) :
    ∀ i, SimplyConnectedSpace (N i) := by
  intro i
  letI : Subsingleton (FundamentalGroup (N i) (b i)) :=
    fundamentalGroup_freeProduct_factors (fun i => FundamentalGroup (N i) (b i)) x e i
  exact simplyConnected_of_fundamentalGroup_subsingleton (b i)

end PoincareConjecture
