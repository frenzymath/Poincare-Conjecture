# Incompressible Surface Euler Zero

## Informal proof

Identify the surface group with its image in the integer three-lattice.
A basis of that subgroup gives at most three loops detecting all mod-two
characters. Path lifting in the actual cocycle double covers evaluates closed
edge cochains on those loops. A cochain with zero evaluations has trivial
covering character, and hence an actual vertex potential. Thus the first
cochain rank is at most the vertex-coboundary rank plus three.

The connected primal and dual incidence graphs give the finite rank identity
Euler count plus closed-cochain rank equals vertex-coboundary rank plus two.
Coherent all-edge triangle signs give even Euler count. The finite boundary
count gives Euler count at most two. Euler count two would make the carrier
simply connected by the proved zero-residual tree-cotree cut construction,
contrary to the original nontrivial group. These facts force Euler count zero.
This uses the constructed zero-residual sphere case, not an assumed
classification of surfaces or a source-surface supplier.

For the original frontier, the parent constructs its connected oriented
finite model and whole-carrier homeomorphism. Transport the prescribed based
injection through that homeomorphism. The three literal circle coordinates
of the fixed ambient torus and their proved winding equivalences give an
injective map to the integer three-lattice. Apply the finite theorem.
Original-atlas PL Euler invariance transfers the result to any supplied
original residual model of the same component. Its stored, constructed
tree-cotree count equation then gives residual count two and constructs the
previously assumed numerical field of the torus candidate.

## Proposed formal statements

The following are the complete two acceptance endpoints. The namespace is
`PoincareMT.M76`; the open namespaces are `Set`, `Geometry`,
`AbstractSimplicialComplex`, and
`PreAbstractSimplicialComplex.ModTwoCochains`.

```lean
theorem surfaceEulerCount_eq_zero_of_injective_integer_three_and_signs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 3)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.faceLink {v}).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : K.vertices ↪ ℕ)
    (sign : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2)
    (hcancel : ∀ t u : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      t ≠ u → ∀ s : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      s.val ⊆ t.val → s.val ⊆ u.val →
        (sign t + boundaryFaceParity number t.val s.val) +
          (sign u + boundaryFaceParity number u.val s.val) = 1)
    (x : K.space) [Nontrivial (FundamentalGroup K.space x)]
    (f : FundamentalGroup K.space x →* Multiplicative (Fin 3 → ℤ))
    (hf : Function.Injective f) : K.surfaceEulerCount = 0

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem FrontierResidualModel.residual_eq_two_of_ambient_injective
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D N B F : Set X0} (he : PLDomain e D) (hD : IsCompact D)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier D = B ∪ F)
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (x : M.components i) (hnt : Nontrivial (FundamentalGroup (M.components i) x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(M.components i, X0)) x)) :
    M.residual i = 2
```

## Independent alignment

The statement-only translator read the complete declarations without their
proofs or target description. It translated the first as a finite connected
pure closed triangulated surface, with connected vertex links and coherent
triangle signs, whose nontrivial based group embeds into the additive group
of the integer three-lattice; its conclusion is Euler count zero. It translated
the second as residual count two for any component of a supplied original
finite frontier model, at any basepoint with nontrivial group and injective
ambient inclusion, for a compact PL domain in a covering compatible atlas
whose frontier is partitioned into two closed disjoint phases.

The independent reviewer, given only that translation and the informal
target, accepted the alignment under the canonical definitions. It noted
that purity, two cofaces per edge, and connected vertex links describe a
closed PL surface, and that the sign equation describes orientability.
Neither declaration assumes a rank bound, Euler equality, classification,
parametrization, or residual count two. The residual theorem includes the
whole frontier by taking the other phase empty.

The definition checks are explicit in the source: `surfaceEulerCount` is the
alternating face count; the fixed ambient coordinates identify `X0` with
three positive-period circles; `FrontierResidualModel` retains original
component images and their tree-cotree Euler equation.

## Verification

`Audit.lean` recursively checks the actual generic, original-component,
residual, and candidate endpoints, rejecting direct admissions and any
axiom other than `propext`, `Classical.choice`, and `Quot.sound`.
Build and publication results are recorded in the Horizon report.
