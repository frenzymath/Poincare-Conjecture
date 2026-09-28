# Balls along capped annular ends

Claim: `capped-annular-ends-bound-balls`, revision adopted by Roadmap PR #626.
Source: Hatcher, *Notes on Basic 3-Manifold Topology* (2014), Theorem 1.1,
printed pp. 2-5; marked disk normalization, Lemma 1.3, printed p. 5.

## Informal proof

The closed union of the original cap and its annulus has frontier precisely
the terminal circle. Its rim is interior to the union: the annular collar
below the rim lies in the cap, since its opposite side has physical height
strictly above every point of the cap. The union is a proper closed region
with nonempty interior. Smooth circle separation on the parameter sphere
therefore constructs a smooth disk chart for this exact union.

Take an ambient collar of the embedded sphere. Compress the standard ball
toward the constructed disk, fixing an open neighborhood of that disk, until
the compressed ball lies in the collar domain and its collar image lies in
the prescribed neighborhood. Extend the resulting local ball embedding to
a global ambient diffeomorphism. Its boundary agrees with the original
surface on an open neighborhood of the complete closed end.

The complementary-disk construction supplies global plane coordinates on
the complement of a point of the standard sphere, with open unit disk image
exactly complementary to the marked closed disk. Composing with the ambient
diffeomorphism gives the closing disk, including every finite enlargement.
Compactness of the terminal circle places a uniform two-sided annular collar
inside the surface-agreement neighborhood. The cut lies strictly inside the
recorded physical-height interval. Reverse the height coordinate for the
upper end, keeping the original ambient embedding.

This proof uses intrinsic disk construction, ambient collars, and marked-ball
compression in place of the suggested regular-band/truncated-cap filling
route. It constructs the disk structure and the ball; neither is an input.
It supplies an existential closing disk. A prescribed canonical terminal cap
and its comparison with the model remain the parent's additional obligation.

## Proposed formal statements

```lean
noncomputable section
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.LowerAnnularEnd
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
theorem exists_ball_with_closing_disk
    {v : E3} {g : S2 → E3} {P : Set Real}
    {D : SphereSurgeryCoreCap v g P} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) {c : Real} (hDc : D.center < c) (hcb : c < b)
    {W : Set E3} (hW : IsOpen W)
    (hEW : g '' ((D.chart '' closedBall 0 1) ∪
      A.chart '' (univ ×ˢ Icc D.center c)) ⊆ W) :
    ∃ (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (r : Real)
      (d : E2 → E3) (U : Set E3) (ε : Real),
      1 < r ∧ _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ d ∧
      (∀ x, Injective (fderiv Real d x)) ∧ IsOpen U ∧
      g '' ((D.chart '' closedBall 0 1) ∪
        A.chart '' (univ ×ˢ Icc D.center c)) ⊆ U ∧
      F '' closedBall (0 : E3) 1 ⊆ W ∧
      d '' closedBall (0 : E2) r ⊆ F '' sphere (0 : E3) 1 ∧
      g '' ((D.chart '' closedBall 0 1) ∪ A.chart '' (univ ×ˢ Icc D.center c)) =
        (F '' sphere (0 : E3) 1) \ d '' ball (0 : E2) 1 ∧
      (F '' sphere (0 : E3) 1) ∩ U = range g ∩ U ∧
      0 < ε ∧ Icc (c - ε) (c + ε) ⊆ Ioo D.center b ∧
      A.chart '' (univ ×ˢ Icc (c - ε) (c + ε)) ⊆ _root_.interior C ∧
      g '' (A.chart '' (univ ×ˢ Icc (c - ε) (c + ε))) ⊆ U ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) →
        inner Real v (g (A.chart (q, t))) = t := by sorry
end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.LowerAnnularEnd
```

```lean
noncomputable section
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.UpperAnnularEnd
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
theorem exists_ball_with_closing_disk
    {v : E3} {g : S2 → E3} {P : Set Real}
    {D : SphereSurgeryCoreCap v g P} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : UpperAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hDb : D.center ≤ b) {c : Real} (hac : a < c) (hcD : c < D.center)
    {W : Set E3} (hW : IsOpen W)
    (hEW : g '' ((D.chart '' closedBall 0 1) ∪
      A.chart '' (univ ×ˢ Icc c D.center)) ⊆ W) :
    ∃ (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (r : Real)
      (d : E2 → E3) (U : Set E3) (ε : Real),
      1 < r ∧ _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ d ∧
      (∀ x, Injective (fderiv Real d x)) ∧ IsOpen U ∧
      g '' ((D.chart '' closedBall 0 1) ∪
        A.chart '' (univ ×ˢ Icc c D.center)) ⊆ U ∧
      F '' closedBall (0 : E3) 1 ⊆ W ∧
      d '' closedBall (0 : E2) r ⊆ F '' sphere (0 : E3) 1 ∧
      g '' ((D.chart '' closedBall 0 1) ∪ A.chart '' (univ ×ˢ Icc c D.center)) =
        (F '' sphere (0 : E3) 1) \ d '' ball (0 : E2) 1 ∧
      (F '' sphere (0 : E3) 1) ∩ U = range g ∩ U ∧
      0 < ε ∧ Icc (c - ε) (c + ε) ⊆ Ioo a D.center ∧
      A.chart '' (univ ×ˢ Icc (c - ε) (c + ε)) ⊆ _root_.interior C ∧
      g '' (A.chart '' (univ ×ˢ Icc (c - ε) (c + ε))) ⊆ U ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) →
        inner Real v (g (A.chart (q, t))) = t := by sorry
end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.UpperAnnularEnd
```

## Informal translation

Write $B_r^n$ and $\overline B_r^n$ for origin-centered open and closed balls,
and $S^{n-1}=\partial B_1^n$. All smoothness is $C^\infty$.

**Common data.** Let $v$ be a unit vector in $\mathbb R^3$, let
$g:S^2\to\mathbb R^3$ be a smooth embedding, and let $P\subset\mathbb R$,
$C\subset S^2$, $h:S^2\to\mathbb R$, and $a,b\in\mathbb R$ be arbitrary.
A rounded core cap has a smooth partial diffeomorphism
$\kappa:\mathbb R^2\rightharpoonup S^2$ defined on a neighborhood of
$\overline B_1^2$, center $s$, nonzero signed scale $\lambda$, a smooth
diffeomorphism $\phi:v^\perp\to v^\perp$, and a smooth injective immersion
$p:\mathbb R^2\to\mathbb R^3$. They satisfy $p=g\circ\kappa$ on
$\overline B_1^2$, $p(\overline B_1^2)=L(K_v^+)$, and
$\langle v,p(x)\rangle=s$ on $S^1$, where $K_v^+$ is the specified rounded
northern cap and $L(tv+y)=(s+\lambda t)v+\phi(y)$. All heights of
$p(\overline B_1^2)$ avoid $P$.

The annular chart $\chi:S^1\times\mathbb R\rightharpoonup S^2$ is a smooth
partial diffeomorphism with source $S^1\times(a-\delta,b+\delta)$ for some
$\delta>0$. On this source $h(\chi(q,t))=t$, its circle at $s$ is
$\kappa(S^1)$, and for every $z\in\kappa(S^1)$ the image
$\chi(S^1\times[a,b])$ is the connected component of $h^{-1}([a,b])$
containing $z$.

**Lower proposition.** Suppose $\lambda<0$, $a\le s$, the image of
$S^1\times[s,b]$ lies in $C$, the image of $S^1\times(s,b)$ lies in
$\operatorname{int}C$, and $\langle v,g(\chi(q,t))\rangle=t$ for
$t\in[s,b]$. For every $s<c<b$, set
$E_-=g(\kappa(\overline B_1^2)\cup\chi(S^1\times[s,c]))$.
For every open neighborhood $W$ of $E_-$ there are a smooth diffeomorphism
$F:\mathbb R^3\to\mathbb R^3$, a number $r>1$, a smooth embedding
$d:\mathbb R^2\to\mathbb R^3$ with injective differential everywhere,
an open set $U$, and $\varepsilon>0$, such that
$$
E_-\subset U,\quad F(\overline B_1^3)\subset W,\quad
d(\overline B_r^2)\subset F(S^2),\quad
E_-=F(S^2)\setminus d(B_1^2),\quad F(S^2)\cap U=g(S^2)\cap U.
$$
Moreover $[c-\varepsilon,c+\varepsilon]\subset(s,b)$, the image of this
closed annular strip lies in $\operatorname{int}C$, its image under $g$
lies in $U$, and physical height equals $t$ throughout the strip.

**Upper proposition.** Suppose $\lambda>0$, $s\le b$, the image of
$S^1\times[a,s]$ lies in $C$, the image of $S^1\times(a,s)$ lies in
$\operatorname{int}C$, and $\langle v,g(\chi(q,t))\rangle=t$ for
$t\in[a,s]$. For every $a<c<s$, set
$E_+=g(\kappa(\overline B_1^2)\cup\chi(S^1\times[c,s]))$.
For every open neighborhood $W$ of $E_+$ there are a smooth diffeomorphism
$F:\mathbb R^3\to\mathbb R^3$, a number $r>1$, a smooth embedding
$d:\mathbb R^2\to\mathbb R^3$ with injective differential everywhere,
an open set $U$, and $\varepsilon>0$, such that
$$
E_+\subset U,\quad F(\overline B_1^3)\subset W,\quad
d(\overline B_r^2)\subset F(S^2),\quad
E_+=F(S^2)\setminus d(B_1^2),\quad F(S^2)\cap U=g(S^2)\cap U.
$$
Moreover $[c-\varepsilon,c+\varepsilon]\subset(a,s)$, the image of this
closed annular strip lies in $\operatorname{int}C$, its image under $g$
lies in $U$, and physical height equals $t$ throughout the strip.

## Alignment review

On 2026-09-23, native translator `translate_end_ball` read the complete formal
statements and their defining data. Native reviewer `review_end_ball_alignment`
received only the adopted informal claim and the resulting propositions. The
review accepted both statements within the stipulated rounded-cap and annular
coordinate setting. For the lower end the source's rim, cut, and additional
height margin are $s$, $c$, and $b-c>0$. The upper inequalities reverse them.
Both statements retain the closed terminal slice, construct the ball and the
whole-end disk, and give every principal conclusion. Global disk coordinates
and the explicit terminal collar strengthen the requested output.

The translator disclosed that a definition extraction also printed adjacent
private lemmas about the fixed cap profile. Those lemmas were not used in its
translation; the public end-ball proofs and informal claim were not exposed.
The semantic reviewer had no source or proof context.

Declaration SHA-256 values below include the complete proved declaration and
the following blank line, excluding namespace commands:

- `LowerAnnularEnd.exists_ball_with_closing_disk`:
  `c81bfdd38c685612c8eaa69f1698f0b7a2ed292388860c1dca8924a170b06a4e`.
- `UpperAnnularEnd.exists_ball_with_closing_disk`:
  `1e0e66a1738752e168a536773a3b9f12afaedae9a0f96387a3ce79158b8d918f`.

The disk/chart, collar, and marking helpers are local construction steps;
their statements were compared directly with the definitions. The public
lower and upper producers receive the full independent statement review.

## Verification

With `leanprover/lean4:v4.33.1`, the focused build of
`PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.Checks`
passed on 2026-09-23. Its two `#print axioms` commands report only `propext`,
`Classical.choice`, and `Quot.sound`. The source scan found no admission or
new axiom in the implemented Lean modules. Both public files also passed LSP
diagnostics. `make check` passed, including all 12 frozen-contract hashes and
the workspace's default Lean build.

The implementation reuses the parent's global complementary disk chart from
`Caps/ClosingDisk.lean`. The regular-band filling and truncated-cap
normalization remain available for the parent's prescribed canonical capping
route; this existential ball proof does not settle that comparison. No
contract, existing cap definition, or consumer theorem was changed.
