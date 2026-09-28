# Localized rounded ball attachment

## Informal proof

Normalize the attaching ball and its marked boundary disk by an ambient
diffeomorphism. In orthogonal-plane and height coordinates, the rational map

$$
\Phi(x,k)=\left(\frac{1+k^2}{1+k^2\|x\|^2}x,
  \frac{k(1-\|x\|^2)}{1+k^2\|x\|^2}\right),\qquad \|x\|<1,
$$

has a smooth explicit inverse on the complement of the exterior planar disk.
An affine height change, scaling and translation identify the marked unit
ball, with its edge removed, with the closed slab $0\le t\le1$. The marked
open disk is its zero slice. Pull these coordinates back through the ball
normalization.

The common disk has separate smooth extensions into the two boundary spheres,
agreeing on the closed disk. Their local openness identifies the boundaries
near every interior disk point. Connected local filled sides then show that
$A$ occupies the lower side in the attachment case and the upper side in the
nested case. Away from the common disk the given intersection conditions
identify the side directly. Thus the same side identification holds on an
open neighborhood of the whole slab in the sweep chart.

The projection of the compact set $B\setminus U$ to the base of the chart is
compact. Choose a compactly supported smooth function $b$ with values in
$[0,1]$, equal to one on that projection. The vertical field, cut off to a
compact subset of $O$ inside the side-identification neighborhood, sends
$(x,0)$ to $(x,b(x))$. Its flow preserves each vertical fiber and its order,
so it identifies both entire closed sides. Outside $U$ this gives $A\cup B$
in the attachment case and $\overline{A\setminus B}$ in the nested case.
For the latter, the closure is computed locally in an open chart and then
patched with the unchanged closed region outside the support neighborhood.

The source is Hatcher, *Notes on Basic 3-Manifold Topology* (2014), Theorem 1.1,
printed pp. 4-5, and Lemma 1.3 with its following corner paragraph, printed p. 5.
The explicit sweep and localized cutoff implement the rounding and support
control for both operations.

## Proposed formal statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Attachment.MarkedBallFlattening

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

abbrev E2 := EuclideanSpace Real (Fin 2)
abbrev E3 := EuclideanSpace Real (Fin 3)
abbrev S2 := sphere (0 : E3) 1

theorem exists_rounded_attachment
    (a b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (f g : E2 → S2)
    (hfi : InjOn f (closedBall 0 1))
    (hgi : InjOn g (closedBall 0 1))
    (hfl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x)
    (hgl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (hag : ∀ x ∈ closedBall (0 : E2) 1, a (f x) = b (g x))
    (hmeet : (a '' closedBall 0 1) ∩ (b '' closedBall 0 1) =
      (fun x => a (f x)) '' closedBall (0 : E2) 1)
    (U O : Set E3) (hU : IsOpen U) (hO : IsOpen O)
    (hedge : (fun x => a (f x)) '' sphere (0 : E2) 1 ⊆ U)
    (hBO : b '' closedBall 0 1 ⊆ O) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ O ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x ∉ K, F x = x) ∧
        (F '' (a '' closedBall 0 1)) \ U =
          ((a '' closedBall 0 1) ∪ (b '' closedBall 0 1)) \ U := by
  sorry

theorem exists_rounded_removal
    (a b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (f g : E2 → S2)
    (hfi : InjOn f (closedBall 0 1))
    (hgi : InjOn g (closedBall 0 1))
    (hfl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x)
    (hgl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (hag : ∀ x ∈ closedBall (0 : E2) 1, a (f x) = b (g x))
    (hsub : b '' closedBall 0 1 ⊆ a '' closedBall 0 1)
    (hmeet : (a '' sphere 0 1) ∩ (b '' sphere 0 1) =
      (fun x => a (f x)) '' closedBall (0 : E2) 1)
    (U O : Set E3) (hU : IsOpen U) (hO : IsOpen O)
    (hedge : (fun x => a (f x)) '' sphere (0 : E2) 1 ⊆ U)
    (hBO : b '' closedBall 0 1 ⊆ O) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ O ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x ∉ K, F x = x) ∧
        (F '' (a '' closedBall 0 1)) \ U =
          closure ((a '' closedBall 0 1) \ (b '' closedBall 0 1)) \ U := by
  sorry

end Poincare.Manifold.Schoenflies.Rounding
```

## Informal translation

**Proposition 1 (Rounded attachment).** Let $\overline D$ be the closed unit
disk in $\mathbb R^2$, $\overline B$ the closed unit ball in $\mathbb R^3$,
and $S^2=\partial\overline B$. Let $a,b:\mathbb R^3\to\mathbb R^3$ be smooth
diffeomorphisms, and let $f,g:\mathbb R^2\to S^2$ restrict injectively to
$\overline D$. Assume that at every point of $\overline D$ each map restricts
on an open neighborhood to a smooth diffeomorphism onto an open subset of
$S^2$. Set $A=a(\overline B)$, $B=b(\overline B)$,
$P=\{a(f(x)):x\in\overline D\}$ and
$C=\{a(f(x)):x\in\partial\overline D\}$. Suppose
$a(f(x))=b(g(x))$ for all $x\in\overline D$ and $A\cap B=P$.
For every pair of open sets $U,O\subseteq\mathbb R^3$ with $C\subseteq U$
and $B\subseteq O$, there are a compact $K\subseteq O$ and a smooth
diffeomorphism $F:\mathbb R^3\to\mathbb R^3$ equal to the identity outside
$K$ such that $F(A)\setminus U=(A\cup B)\setminus U$.

**Proposition 2 (Rounded removal).** Let $\overline D$ be the closed unit
disk in $\mathbb R^2$, $\overline B$ the closed unit ball in $\mathbb R^3$,
and $S^2=\partial\overline B$. Let $a,b:\mathbb R^3\to\mathbb R^3$ be smooth
diffeomorphisms, and let $f,g:\mathbb R^2\to S^2$ restrict injectively to
$\overline D$. Assume that at every point of $\overline D$ each map restricts
on an open neighborhood to a smooth diffeomorphism onto an open subset of
$S^2$. Set $A=a(\overline B)$, $B=b(\overline B)$,
$P=\{a(f(x)):x\in\overline D\}$ and
$C=\{a(f(x)):x\in\partial\overline D\}$. Suppose
$a(f(x))=b(g(x))$ for all $x\in\overline D$, $B\subseteq A$, and
$a(S^2)\cap b(S^2)=P$.
For every pair of open sets $U,O\subseteq\mathbb R^3$ with $C\subseteq U$
and $B\subseteq O$, there are a compact $K\subseteq O$ and a smooth
diffeomorphism $F:\mathbb R^3\to\mathbb R^3$ equal to the identity outside
$K$ such that $F(A)\setminus U=\overline{A\setminus B}\setminus U$,
with closure taken in $\mathbb R^3$.

## Alignment review

The independent translator stated the two propositions using
`A = a(closedBall 0 1)`, `B = b(closedBall 0 1)`, the common disk
`a(f(closedBall 0 1))`, and its parametrized edge. The independent reviewer
accepted correspondence with the current informal description in Roadmap
PR #582: every hypothesis and both localized conclusions agree. Defining `f`
and `g` on the whole plane imposes no global regularity requirement; maps
defined near the disk can be extended arbitrarily elsewhere.

The review covered statement correspondence, not the geometric proof.
The implemented proofs retain these exact binders and conclusions. An
independent review of the assembled argument found no additional hypotheses,
statement drift or circular dependency. The admitted candidate bodies belong only
to the archived statement candidates; `Statements.lean` contains the proofs.

Declaration SHA-256 values (complete theorem text, including the explicit
admission and its final newline):

| Declaration | SHA-256 |
| --- | --- |
| `exists_rounded_attachment` | `f9aabb6d01fe0197895ca225c76d8a35dc9461898eaea3d1eb93d5e6f196ac5e` |
| `exists_rounded_removal` | `8f9112e466b2ac1789077aa2f592841ebd0a2fcd461639cd1e3806f513ad4557` |

## Verification and consumer boundary

The focused target
`PoincareLib.Topology.Manifold.Schoenflies.Attachment.Rounding.Checks` builds
with Lean 4.33.1. Both final operations have axiom closures exactly
`propext`, `Classical.choice`, and `Quot.sound`. Their proof bodies and all
new supporting Lean modules contain no admissions or added axioms.

The sphere-filling consumer imports `Rounding.Statements` and applies
`exists_rounded_attachment` or `exists_rounded_removal` with the actual ball
parametrizations and separate disk maps. The resulting ball parametrization
is `a.trans F`. The same focused check confirms that
`SmoothDomain.exists_ball_neighborhood` still contains `sorryAx` from its
separately owned sphere-filling construction; this result does not complete
that parent theorem.
