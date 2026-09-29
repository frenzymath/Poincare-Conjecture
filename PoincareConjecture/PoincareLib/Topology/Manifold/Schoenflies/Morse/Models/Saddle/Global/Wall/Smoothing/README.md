# Local smoothing of a saddle wall

## Informal description

For every positive number $\delta$, there are a smooth function
$\varphi:\mathbb R\to\mathbb R$, a number $0<a\leq\delta$, and two smooth
diffeomorphisms $L,R$ of $\mathbb R^3$ preserving the third coordinate.
The function is nonpositive and vanishes precisely on $[a,\infty)$.
The image under $L$ of $\{x\leq0\}$ is
$\{x\leq\varphi(z-y^2)\}$; the image under $R$ of $\{x\geq0\}$ is
$\{x\geq-\varphi(z-y^2)\}$. These two images intersect exactly in
$\{x=0,\ z\geq y^2+a\}$. On the open set $z>y^2+a$, the images agree,
respectively, with the two original closed halfspaces.

Each image is contained in the corresponding half of the saddle epigraph
$z\geq y^2-x^2$. The left image equals that half outside
$U^-_\delta=\{x>-\delta,\ z-y^2<\delta\}$, and the right image equals its
half outside $U^+_\delta=\{x<\delta,\ z-y^2<\delta\}$.

## Informal proof

Choose a smooth, 1-Lipschitz majorant $\rho$ of absolute value which equals
absolute value outside $(-\delta,\delta)$. Put
$X(s)=(s-\rho(s))/2$, $W(s)=(s+\rho(s))/2$, and
$H(s)=W(s)-X(s)^2$. The function $X$ is nonpositive and monotone, and $W$
is nonnegative. Its derivative satisfies
$H'=(1+\rho')/2-X(1-\rho')>0$. At a zero of $X$, the minimum principle
applied to $\rho(s)-s$ gives $\rho'=1$; away from the zero set, positivity
follows from $X<0$ and $|\rho'|\leq1$. The exact tails make $H$ a smooth
diffeomorphism of the line.

The zero set of $X$ is a closed ray beginning at a positive number $a$ at
most $\delta$. Positivity follows because a smooth majorant cannot touch
absolute value at its corner. Moreover $H(a)=a$. Thus
$\varphi=X\circ H^{-1}$ vanishes exactly on $[a,\infty)$. The two shears
$(x,y,z)\mapsto(x\mathbin{\pm}\varphi(z-y^2),y,z)$ have explicit smooth
inverses. Their image formulas give the intersection and germ assertions.
The exact tails $X(s)=s$, $H(s)=-s^2$ for $s\leq-\delta$ and
$X(s)=0$, $H(s)=s$ for $s\geq\delta$ give the two localization identities.

## Proposed formal statements

Here `E3` abbreviates `EuclideanSpace Real (Fin 3)`.

```lean
namespace Corner
def leftBody : Set E3 := {p | p 0 ≤ 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2}
def rightBody : Set E3 := {p | 0 ≤ p 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2}
end Corner

def edgeNeighborhood (δ : Real) : Set E3 :=
  {p | -δ < p 0 ∧ p 2 - (p 1)^2 < δ}
def reflectedEdgeNeighborhood (δ : Real) : Set E3 :=
  {p | p 0 < δ ∧ p 2 - (p 1)^2 < δ}

theorem exists_rounded_sides {δ : Real} (hδ : 0 < δ) :
    ∃ (φ : Real → Real) (a : Real)
      (L R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      ContDiff Real ∞ φ ∧ 0 < a ∧ a ≤ δ ∧
      (∀ q, φ q ≤ 0) ∧ (∀ q, φ q = 0 ↔ a ≤ q) ∧
      (∀ p, L p 2 = p 2) ∧ (∀ p, R p 2 = p 2) ∧
      L '' {p : E3 | p 0 ≤ 0} = {p : E3 | p 0 ≤ φ (p 2 - (p 1)^2)} ∧
      R '' {p : E3 | 0 ≤ p 0} = {p : E3 | -φ (p 2 - (p 1)^2) ≤ p 0} ∧
      L '' {p : E3 | p 0 ≤ 0} ⊆ Corner.leftBody ∧
      R '' {p : E3 | 0 ≤ p 0} ⊆ Corner.rightBody ∧
      ((L '' {p : E3 | p 0 ≤ 0}) \ edgeNeighborhood δ =
        Corner.leftBody \ edgeNeighborhood δ) ∧
      ((R '' {p : E3 | 0 ≤ p 0}) \ reflectedEdgeNeighborhood δ =
        Corner.rightBody \ reflectedEdgeNeighborhood δ) ∧
      (L '' {p : E3 | p 0 ≤ 0}) ∩ (R '' {p : E3 | 0 ≤ p 0}) =
        {p : E3 | p 0 = 0 ∧ (p 1)^2 + a ≤ p 2} ∧
      ((L '' {p : E3 | p 0 ≤ 0}) ∩ {p : E3 | a < p 2 - (p 1)^2} =
        {p : E3 | p 0 ≤ 0} ∩ {p : E3 | a < p 2 - (p 1)^2}) ∧
      ((R '' {p : E3 | 0 ≤ p 0}) ∩ {p : E3 | a < p 2 - (p 1)^2} =
        {p : E3 | 0 ≤ p 0} ∩ {p : E3 | a < p 2 - (p 1)^2})
```

These local statements do not assert compactness, a terminal-surface
identification, or that the frontier of the union is smooth at its new edge.

## Alignment and checks

A native translator received only the complete formal statement. A separate
native reviewer compared its mathematical translation with the informal
description above and accepted the alignment. `Wall.Checks` audits the
construction using only `propext`, `Classical.choice`, and `Quot.sound`.
