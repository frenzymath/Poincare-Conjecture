# Original Frontier Recognition Alignment

## Informal Proof

Construct the actual finite oriented frontier component in the original atlas, retaining its coordinate inverse on the entire carrier. Transport the given based injection to this finite surface and compose with the three ambient winding coordinates. The finite surface rank theorem gives Euler characteristic zero, so the primal and dual spanning trees leave exactly two residual edges.

Build the cut disk from separated sheets, retaining the primal sides until the primal sectors are attached. A marked square parametrizes this actual disk. Refine its finite affine maps along the original faces. Injectivity on adjacent refined triangles transports the original coherent orientation to the refinement. All counterclockwise square-side edges have one boundary sign. At an interior point of each copied residual bridge, the original half-band germ identifies its actual coface; convex-face extremality puts both refined-edge endpoint images on the original edge. The resulting scalar direction extends to the complete bridge interval. Original coface cancellation excludes endpoint preservation, proving literal reversal.

Match the paired long arcs, compose the square chart with the complete source projection, and use the proved cut-disk fibers to obtain exactly the periodic identifications. Rescale to period 64. Quotient descent gives the torus homeomorphism, and the existing local finite PL inverse construction gives its inverse on the whole finite carrier. Compose with the retained original coordinate inverse. The phase-installation theorem constructs its parametrizations by this argument and invokes the existing phase-covering consumer.

## Proposed Formal Statements

The statement-only proof placeholder below is solely for semantic review. The compilable declaration in `OriginalFrontier.lean` has a complete proof.

```lean
open Set Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "T0" => C0 × C0
open Classical in
theorem PLDomain.exists_original_frontier_torus_parametrization
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N)
    (x : X0) (hx : x ∈ frontier N)
    (hnt : Nontrivial (FundamentalGroup (connectedComponentIn (frontier N) x)
      ⟨x, mem_connectedComponentIn hx⟩))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier N) x, X0)) ⟨x, mem_connectedComponentIn hx⟩)) :
    ∃ d : ((Fin 0 → ℝ) × V3) → OpenPartialHomeomorph X0 V3,
      StandardLatticeHandleAtlas (Fin 0) (Fin 3) hamiltonZeroPeriodLattice d ∧
    ∃ (s : Finset N) (phi : X0 → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X0)
      (H : J.space ≃ₜ connectedComponentIn (frontier N) x)
      (T : T0 ≃ₜ connectedComponentIn (frontier N) x)
      (u : ℝ × ℝ → (s → ℝ × V3)),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, (H z : X0) = g z) ∧
      (∀ y : connectedComponentIn (frontier N) x, (H.symm y : (s → ℝ × V3)) = phi y) ∧
      FinitePiecewiseAffineOn u (PeriodicSquare.squareCarrier p) ∧
      u '' PeriodicSquare.squareCarrier p = J.space ∧
      PolyhedralPLInCharts e (g ∘ u) (PeriodicSquare.squareCarrier p) ∧
      (g ∘ u) '' PeriodicSquare.squareCarrier p = connectedComponentIn (frontier N) x ∧
      (∀ z : PeriodicSquare.Square p,
        (T (PeriodicSquare.projection p z) : X0) = g (u (z.1, z.2))) ∧
      (∀ z w : PeriodicSquare.Square p,
        g (u (z.1, z.2)) = g (u (w.1, w.2)) ↔
          PeriodicSquare.projection p z = PeriodicSquare.projection p w) ∧
      ∀ theta : C0, PolyhedralPLInCharts d
        (hamiltonZeroCollarPhaseTarget J
          ⟨H.trans T.symm, (H.trans T.symm).continuous⟩ theta) J.space := by
  sorry
end PoincareMT.M76
```

## Informal Translation

Let X be the fixed lattice three-torus, p=64, C=R/(pZ), and T2=C x C. Let Q0 identify X with T2 x C in its standard lattice coordinates. A covering family e of open charts to R3 has piecewise-affine transitions. Let N be a compact PL domain in e, x a point of its frontier, and B the frontier component containing x. Assume that pi1(B,x) is nontrivial and its inclusion into pi1(X,x) is injective.

There exist a standard lattice atlas d, a finite subset s of N, W=(R x R3)^s, a finite geometric simplicial complex J in W, maps phi:X->W and g:W->X, homeomorphisms H:|J|->B and T:T2->B, and u:R2->W with the following properties. The map phi is continuous and locally piecewise affine in every original e chart; g is polyhedral PL in e on |J|, equals H there, and phi restricted to B equals H inverse. The map u is finite piecewise affine on the closed period-p square, maps that square exactly onto |J|, and g composed with u is polyhedral PL in e with exact image B. It agrees with T composed with the periodic projection, and two square points have equal images exactly when their periodic projections agree.

For every theta in C, the map from W to X which equals Q0 inverse applied to (T inverse(H(z)),theta) on |J|, and Q0 inverse applied to (0,theta) outside |J|, is polyhedral PL in d on all |J|. Its tangential coordinates give the inverse on |J|; composition with phi gives the inverse on B in the original charts.

## Alignment Review

The independent translator received only the complete statement and the formal definition of the phase-target map. A separate reviewer received only the informal claim and its translation. The reviewer accepted the hypotheses and finite parametrization and verified the whole-carrier inverse after the phase-target map was expanded: its standard tangential coordinates give T inverse composed with H, and phi equals H inverse on B. No classification or parametrization hypothesis occurs.

The reviewed declaration, including its complete proof and the trailing blank line before the namespace closes, has SHA-256 `bc89fe978cf13aeeb9a4b73ed61c4c07695e4b72728d71b47b814c3b899aa262`. The declaration begins at `theorem PLDomain.exists_original_frontier_torus_parametrization` in `OriginalFrontier.lean`. The graph claim is `incompressible-torus-surface-recognition`, unchanged informal statement from revision 4.

## References

This construction supplies the surface recognition used in Waldhausen (1968), pp. 59--60, and Hamilton (1976), Lemma 3, pp. 65--67. The corrected primal/dual-tree cut retains the separate triangle sheets and the primal sides before contraction, as required by the workspace correction `references/topology/mapher/smoothing/corrections/dual-tree-cut-boundary.md`.

```bibtex
@article{Waldhausen1968,
  author = {Waldhausen, F.},
  title = {On irreducible 3-manifolds which are sufficiently large},
  journal = {Annals of Mathematics},
  volume = {87}, pages = {56--88}, year = {1968}
}
@article{Hamilton1976,
  author = {Hamilton, A. J. S.},
  title = {The Triangulation of 3-Manifolds},
  journal = {The Quarterly Journal of Mathematics},
  volume = {27}, number = {1}, pages = {63--70}, year = {1976},
  doi = {10.1093/qmath/27.1.63}
}
```
