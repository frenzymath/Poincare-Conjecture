import HatcherLib.Ch0.AttachingSpace
import HatcherLib.Ch0.CellBoundaryHEP
import HatcherLib.Ch0.HomotopyExtensionRel
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Chapter 0 — HEP under cell attachment

This file develops the pushout step in Hatcher's proof that CW pairs have the
homotopy extension property.  The boundary inclusion of a cell has the HEP by
`hasHEP_cellBoundary`; the results below show that this property passes to the
canonical inclusion after attaching the cell, and that successive HEP maps
compose.

The remaining passage from these finite attachment steps to an arbitrary CW
pair is the skeletal/weak-topology argument.
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

/-! ## Composition -/

/-- HEP maps are closed under composition.  First extend across `i`, regarding
the original map as a map on `X` via `j`; then extend the resulting homotopy
across `j`. -/
theorem HasHEPMap.comp {A X Y : Type u} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] {i : C(A, X)} {j : C(X, Y)}
    (hj : HasHEPMap j) (hi : HasHEPMap i) : HasHEPMap (j.comp i) := by
  intro Z _ phi h hcompat
  obtain ⟨G, hG0, hGi⟩ := hi (phi.comp j) h hcompat
  obtain ⟨F, hF0, hFj⟩ := hj phi G hG0
  exact ⟨F, hF0, fun a t => (hFj (i a) t).trans (hGi a t)⟩

/-! ## Disjoint unions -/

/-- The componentwise subspace of a topological disjoint union. -/
def sigmaSet {J : Type u} {X : J → Type u} (A : ∀ j, Set (X j)) :
    Set (Σ j, X j) :=
  {x | x.2 ∈ A x.1}

/-- An arbitrary topological disjoint union of HEP pairs again has the HEP. -/
theorem HasHEP.sigma {J : Type u} {X : J → Type u}
    [∀ j, TopologicalSpace (X j)] (A : ∀ j, Set (X j))
    (hA : ∀ j, HasHEP.{u, u} (A j)) : HasHEP.{u, u} (sigmaSet A) := by
  intro Y _ phi h hcompat
  classical
  let incl (j : J) : C(↥(A j), ↥(sigmaSet A)) :=
    ⟨fun a => ⟨⟨j, (a : X j)⟩, a.2⟩,
      (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk (fun a => a.2)⟩
  let phiJ (j : J) : C(X j, Y) := phi.comp (ContinuousMap.sigmaMk j)
  let hJ (j : J) : C(↥(A j) × I, Y) :=
    h.comp ((incl j).prodMap (ContinuousMap.id I))
  have hcompatJ (j : J) : ∀ a : ↥(A j), hJ j (a, 0) = phiJ j (a : X j) := by
    intro a
    exact hcompat (incl j a)
  have hex (j : J) : ∃ K : C(X j × I, Y),
      (∀ x : X j, K (x, 0) = phiJ j x) ∧
        ∀ (a : ↥(A j)) (t : I), K ((a : X j), t) = hJ j (a, t) :=
    hA j (phiJ j) (hJ j) (hcompatJ j)
  let K (j : J) : C(X j × I, Y) := Classical.choose (hex j)
  have hK0 (j : J) : ∀ x : X j, K j (x, 0) = phiJ j x :=
    (Classical.choose_spec (hex j)).1
  have hKA (j : J) : ∀ (a : ↥(A j)) (t : I),
      K j ((a : X j), t) = hJ j (a, t) :=
    (Classical.choose_spec (hex j)).2
  let G : (Σ j, X j × I) → Y := fun q => K q.1 q.2
  have hG : Continuous G := continuous_sigma fun j => map_continuous (K j)
  let F : C((Σ j, X j) × I, Y) :=
    ⟨fun p => G ((Homeomorph.sigmaProdDistrib (X := X) (Y := I)) p),
      hG.comp (Homeomorph.sigmaProdDistrib (X := X) (Y := I)).continuous⟩
  refine ⟨F, ?_, ?_⟩
  · rintro ⟨j, x⟩
    exact hK0 j x
  · rintro ⟨⟨j, x⟩, hx⟩ t
    exact hKA j ⟨x, hx⟩ t

/-! ## Pushout along an attaching map -/

variable {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]

/-- **HEP is preserved by attaching spaces.**  If `(X1, A)` has the homotopy
extension property and `f : A -> X0` is any attaching map, then the canonical
map `X0 -> X0 ⊔_f X1` has the map-form HEP.

This is the pushout stability needed in the cell-by-cell proof for CW pairs. -/
theorem HasHEP.attachInclBase {A : Set X1} (hA : HasHEP.{u, u} A)
    (f : C(↥A, X0)) : HasHEPMap (attachInclBase A f) := by
  intro Z _ phi h hcompat
  -- Along `A`, the requested homotopy on the base supplies the boundary data
  -- for extending over `X1`.
  let af : C(↥A × I, X0 × I) :=
    ⟨fun p => (f p.1, p.2),
      ((map_continuous f).comp continuous_fst).prodMk continuous_snd⟩
  let phi1 : C(X1, Z) := phi.comp (attachInclTop A f)
  let h1 : C(↥A × I, Z) := h.comp af
  have hcompat1 : ∀ a : ↥A, h1 (a, 0) = phi1 (a : X1) := by
    intro a
    exact (hcompat (f a)).trans (congrArg phi (attachIncl_glue A f a).symm)
  obtain ⟨K, hK0, hKA⟩ := hA phi1 h1 hcompat1

  -- Put the homotopy `h` on the base summand and its extension `K` on the top
  -- summand.  It is continuous before taking the attaching quotient.
  let G : C((X0 ⊕ X1) × I, Z) :=
    ⟨fun p => p.1.elim (fun x0 => h (x0, p.2)) (fun x1 => K (x1, p.2)), by
      apply continuous_sumProd
      · exact (map_continuous h).comp (continuous_fst.prodMk continuous_snd)
      · exact (map_continuous K).comp (continuous_fst.prodMk continuous_snd)⟩
  let Gtil : C(I × (X0 ⊕ X1), Z) :=
    G.comp ⟨fun p => (p.2, p.1), by fun_prop⟩

  -- The boundary equation from the HEP says precisely that `Gtil` is constant
  -- on the attaching equivalence relation at every time.
  have hnorm : ∀ (t : I) (p : X0 ⊕ X1),
      Gtil (t, attachNorm A f p) = Gtil (t, p) := by
    intro t p
    cases p with
    | inl x0 => rfl
    | inr x1 =>
        by_cases hx : x1 ∈ A
        · rw [attachNorm_inr_of_mem A f hx]
          exact (hKA ⟨x1, hx⟩ t).symm
        · rw [attachNorm_inr_of_not_mem A f hx]
  have hdesc : ∀ (t : I) (a b : X0 ⊕ X1),
      attachNorm A f a = attachNorm A f b -> Gtil (t, a) = Gtil (t, b) := by
    intro t a b hab
    rw [← hnorm t a, ← hnorm t b, hab]

  -- Descend simultaneously in the time parameter.  Compactness of `I` makes
  -- the product of the attaching quotient map with `I` a quotient map.
  let Ftime : C(I × AttachingSpace A f, Z) :=
    ⟨fun p => Quotient.liftOn p.2 (fun q => Gtil (p.1, q))
        (fun a b hab => hdesc p.1 a b hab), by
      apply (isQuotientMap_quotient_mk').continuous_lift_prod_right
      exact map_continuous Gtil⟩
  let F : C(AttachingSpace A f × I, Z) :=
    Ftime.comp ⟨fun p => (p.2, p.1), by fun_prop⟩
  refine ⟨F, ?_, ?_⟩
  · intro q
    induction q using Quotient.ind with
    | _ p =>
        cases p with
        | inl x0 => exact hcompat x0
        | inr x1 => exact hK0 x1
  · intro x0 t
    rfl

/-- Attaching one closed ball along its boundary produces an HEP inclusion of
the old space into the adjunction space. -/
theorem hasHEPMap_attachCell {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : C(↥(CellBoundary E), X0)) :
    HasHEPMap (attachInclBase (CellBoundary E) f) :=
  hasHEP_cellBoundary.attachInclBase f

/-- Simultaneously attaching an arbitrary family of closed balls along their
componentwise boundaries produces an HEP inclusion of the old space. -/
theorem hasHEPMap_attachCells {J E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (f : C(↥(sigmaSet (fun _ : J => CellBoundary E)), X0)) :
    HasHEPMap (attachInclBase (sigmaSet (fun _ : J => CellBoundary E)) f) :=
  HasHEP.attachInclBase
    (HasHEP.sigma (fun _ : J => CellBoundary E) (fun _ => hasHEP_cellBoundary)) f

end HatcherLib
