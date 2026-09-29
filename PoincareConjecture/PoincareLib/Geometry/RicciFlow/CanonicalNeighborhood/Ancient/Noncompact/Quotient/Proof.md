# Strong capped tubes on twisted cylinders

## Informal proof

Use the fixed two-sheeted product cover of the original ancient flow. The
symmetric slab descends to a compact projective core. Above a sufficiently
large positive height the cover is injective on each scalar-normalized neck
slab. The fixed round sphere parametrization and affine line normalization
give the exact evolving cylinder on the entire backward time interval,
including time zero.

At a fixed time let $R>0$ be the spatially constant scalar curvature, put
$\rho=R^{-1/2}$ and $L=\varepsilon^{-1}\rho$. Take the closed cap core to
be the image of $S^2\times[-L,L]$ and its carrier to be the image of
$S^2\times(-3L,3L)$. The end neck is centered at height $2L$, and the
boundary neck at height $L$. Odd compression of the line identifies the cap
carrier with the punctured projective model, preserving the quotient fibers.

The cap has intrinsic diameter at most
$(6\varepsilon^{-1}+\sqrt2(\pi+1))\rho$. With
$A=6\varepsilon^{-1}+\sqrt2(\pi+1)+1$, it lies in a ball of radius
$A\rho$. Bishop--Gromov therefore bounds its volume by
$\omega_3 A^3R^{-3/2}$. Universal noncollapsing gives a constant
$\kappa>0$, chosen before the solution, and volume at least
$\kappa\rho^3$ for every core ball of radius $\rho$. Those closed balls
remain inside the cap. The scalar ratio is one, the scalar gradient vanishes,
and the absolute scalar evolution expression is at most $2R^2$. Choosing
one constant strictly above $3$, $A$, $\omega_3 A^3$, and $\kappa^{-1}$
supplies all the strict cap estimates.

Necks centered at heights $(i+2)L$, for integers $i\geq0$, form a
balanced chain covering the complement of the closed core. The coordinates
$(q,s)\mapsto\operatorname{cover}(q,L+s/(1-s))$ identify that end with
$S^2\times(0,1)$, and translation of positive slices supplies the central
sphere isotopies. The cap's end neck is exactly the cap-tube overlap; both
attachment tails lie in it. The union is the entire original carrier.
The static cap estimates and strong-neck coverage then give the strong
capped tube, retaining the actual flow connection and fixed coordinates.

Reference: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Corollary
9.88, pp. 239--240; cap estimates are Definition 9.72, pp. 230--231.

## Proposed formal statements

```lean
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.WholeTube
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Products

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

theorem twistedCylinder_strongCappedTube
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              M27TwistedSphereLineFlowCertificate K →
              Nonempty (M26StrongCappedTube K 0 epsilon C₀) := by
  sorry

end PoincareMT
```

The normalization and slab-coordinate lemmas are intermediate constructions
with direct comparison to the definitions; they do not replace this target.
The implementation is `twistedCylinder_strongCappedTube` in `Producer.lean`.
Its auxiliary `M27TwistedSphereLineFlowCertificate.exists_strongCappedTube`
also gives the same constant at every nonpositive terminal time.

## Informal translation

Assume the frozen M26 canonical-neighborhood predecessor services. There is
a positive threshold at most 1/200 such that, for every positive accuracy
below it, there is a positive constant uniform over all connected smooth
three-dimensional ancient kappa-solutions with their Borel measurable
structures. Suppose a fixed surjective local diffeomorphism from a round
sphere times the line pulls back every nonpositive-time metric to its round
product metric and has exactly antipodal-reflection fibers. Suppose also
that the carrier has its punctured projective-space topology and a standard
smooth punctured-projective double cover. Then its entire time-zero slice
is a strong capped tube of the prescribed accuracy and constant. The tube
has a balanced neck chain and every tube point centers a strong evolving
neck in fixed spatial coordinates through zero. The cap uses the actual
flow connection and satisfies all scalar, derivative, diameter, volume and
core-ball estimates with that same uniform constant.

## Alignment review

Independent native translation and comparison accepted the statement. The
extra topology data are consequences of the quotient presentation: polar
coordinates identify the sphere-line cover equivariantly with the three-sphere
minus its antipodal poles. The threshold bound only shrinks the permitted
accuracy. The constants precede all carriers and solutions, and the retained
connection is the actual flow connection.
