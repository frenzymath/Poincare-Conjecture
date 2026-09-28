# Parametric height-cutoff lift

## Informal description

Let $\Phi(t,z)$ be planar diffeomorphisms whose evaluation and inverse
evaluation are jointly smooth in $(t,z,p)$, with $\Phi(0,z)=\mathrm{id}$.
Suppose every map fixes the complement of a set $K$. For every smooth real
function $\chi$, the map $H(p,z)=(\Phi(\chi(z),z)(p),z)$ is a smooth
diffeomorphism of three-space. Its inverse uses the inverse planar maps;
it preserves height, maps each horizontal slice to the corresponding planar
image, and fixes every point whose planar coordinate is outside $K$ or whose
height has $\chi(z)=0$.

## Informal proof

The forward and inverse formulas are mutually inverse because their height
coordinate is unchanged. Joint smoothness follows by composition with the
smooth map $(z,p)\mapsto(\chi(z),z,p)$. Conjugate the product diffeomorphism
by the linear coordinate identification with Euclidean three-space.
The slice and fixed-point conclusions follow from these formulas.

## Proposed formal statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.Cutoff

noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.Manifold.Schoenflies.Saddle

theorem exists_parametric_height_cutoff_lift
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2)
      (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞)
    (h0 : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × EuclideanSpace Real (Fin 2) =>
      Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × EuclideanSpace Real (Fin 2) =>
      (Φ q.1 q.2.1).symm q.2.2))
    {K : Set (EuclideanSpace Real (Fin 2))}
    (hsupp : ∀ t z x, x ∉ K → Φ t z x = x)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace Real (Fin 3)) (EuclideanSpace Real (Fin 3)) ∞,
      (∀ y, H y = toE3 (Φ (χ (y 2)) (y 2) (toE2 y)) (y 2)) ∧
      (∀ y, H.symm y = toE3 ((Φ (χ (y 2)) (y 2)).symm (toE2 y)) (y 2)) ∧
      (∀ y, (H y) 2 = y 2) ∧
      (∀ (S : Set (EuclideanSpace Real (Fin 2))) (c : Real),
        H '' slice S c = slice (Φ (χ c) c '' S) c) ∧
      (∀ y, toE2 y ∉ K → H y = y) ∧
      (∀ y, χ (y 2) = 0 → H y = y) := by
  sorry

end Poincare.Manifold.Schoenflies.Saddle
```

## Informal translation

Let $\Phi_{t,z}$ be smooth diffeomorphisms of the plane, with
$\Phi_{0,z}(x)=x$ for every $z,x$, with smooth forward and inverse evaluation
in $(t,z,x)$, and fixing the complement of a set $K$ for all parameters.
For any smooth $\chi:\mathbb R\to\mathbb R$, there is a smooth diffeomorphism
$H$ of three-space given by
$H(x,z)=(\Phi_{\chi(z),z}(x),z)$ and
$H^{-1}(x,z)=(\Phi_{\chi(z),z}^{-1}(x),z)$.
It preserves the last coordinate and maps $S\times\{c\}$ onto
$\Phi_{\chi(c),c}(S)\times\{c\}$ for every planar set $S$ and real $c$.
It fixes $(x,z)$ whenever $x\notin K$ or $\chi(z)=0$.

## Alignment review

The independent formal-only translator and prose-only reviewer accepted the
correspondence on 2026-09-23. The set $K$ need not be compact for the lift
itself; compact support is addressed by the interval extension theorem.
The implementation abbreviates the two Euclidean spaces without changing
the types of the reviewed declaration.
The full candidate declaration from `theorem` through its candidate proof has
SHA-256 `dc06e2a970417c0c614fd807a5f019a38941e1d441adccf15cd521e31b3dc1bd`.

The routine common product construction and image-of-union corollaries are
compared directly with their formulas; they do not change the geometric claim.

## Interval Extension

### Informal Description

Let $U$ be an open neighborhood of $[a,b]$ and let $\Phi(t,z)$ be a
family of planar diffeomorphisms with smooth forward and inverse evaluations
on $\mathbb R\times U\times\mathbb R^2$. Suppose $\Phi(0,z)$ is the
identity on $U$, and the maps for $t\in[0,1]$, $z\in U$ fix the complement
of one compact set $K$. For every $\varepsilon>0$, the terminal family on
$[a,b]$ extends to a global smooth planar family with smooth inverse, fixing
the complement of $K$, and equal to the identity at heights at most
$a-\varepsilon$ or at least $b+\varepsilon$. Both displacement maps have
compact support.

Its height-preserving lift has compact forward and inverse displacement
support, agrees with the terminal planar family and inverse on $[a,b]$,
and has exact slice and union-of-slices images there. It fixes points with
planar coordinate outside $K$, and all heights in the two exterior tails.

### Informal Proof

Choose a smooth scalar cutoff equal to one on $[a,b]$, with closed support
inside $U\cap(a-\varepsilon,b+\varepsilon)$. Evaluate the isotopy at
this cutoff parameter and use the identity outside $U$. Off its closed
support the cutoff vanishes on a neighborhood, so forward and inverse
families are locally the identity there. Their displacement supports lie
in $[a-\varepsilon,b+\varepsilon]\times K$. Apply the common height lift
and transport this compact set by the linear coordinate identification.

### Proposed Formal Statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.Cutoff

open Set Function
open scoped Manifold ContDiff
namespace Poincare.Manifold.Schoenflies.Saddle
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_interval_supported_planar_family
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a b : Real} {U : Set Real} (hU : IsOpen U) (hI : Icc a b ⊆ U)
    (hΦ : ContDiffOn Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hΦinv : ContDiffOn Real ∞
      (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hzero : ∀ z ∈ U, ∀ x, Φ 0 z x = x)
    {K : Set E2} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : Real) 1, ∀ z ∈ U, ∀ x ∉ K, Φ t z x = x)
    {ε : Real} (hε : 0 < ε) :
    ∃ Ψ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun q : Real × E2 => Ψ q.1 q.2) ∧
      ContDiff Real ∞ (fun q : Real × E2 => (Ψ q.1).symm q.2) ∧
      (∀ z ∈ Icc a b, Ψ z = Φ 1 z) ∧
      (∀ z x, x ∉ K → Ψ z x = x) ∧
      (∀ z, z ≤ a - ε ∨ b + ε ≤ z → ∀ x, Ψ z x = x) ∧
      HasCompactSupport (fun q : Real × E2 => Ψ q.1 q.2 - q.2) ∧
      HasCompactSupport (fun q : Real × E2 => (Ψ q.1).symm q.2 - q.2) := by sorry

theorem exists_interval_supported_height_lift
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a b : Real} {U : Set Real} (hU : IsOpen U) (hI : Icc a b ⊆ U)
    (hΦ : ContDiffOn Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hΦinv : ContDiffOn Real ∞
      (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hzero : ∀ z ∈ U, ∀ x, Φ 0 z x = x)
    {K : Set E2} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : Real) 1, ∀ z ∈ U, ∀ x ∉ K, Φ t z x = x)
    {ε : Real} (hε : 0 < ε) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, (H y) 2 = y 2) ∧
      (∀ y, y 2 ∈ Icc a b → H y = toE3 (Φ 1 (y 2) (toE2 y)) (y 2)) ∧
      (∀ y, y 2 ∈ Icc a b →
        H.symm y = toE3 ((Φ 1 (y 2)).symm (toE2 y)) (y 2)) ∧
      (∀ c ∈ Icc a b, ∀ S : Set E2, H '' slice S c = slice (Φ 1 c '' S) c) ∧
      (∀ L : Real → Set E2, H '' (⋃ c ∈ Icc a b, slice (L c) c) =
        ⋃ c ∈ Icc a b, slice (Φ 1 c '' L c) c) ∧
      (∀ y, toE2 y ∉ K → H y = y) ∧
      (∀ y, y 2 ≤ a - ε ∨ b + ε ≤ y 2 → H y = y) ∧
      HasCompactSupport (fun y => H y - y) ∧
      HasCompactSupport (fun y => H.symm y - y) := by sorry

end Poincare.Manifold.Schoenflies.Saddle
```

### Informal Translation

Let $a,b$ be real, $U$ open containing $[a,b]$, and $K$ compact in the
plane. For all real $t,z$, let $\Phi_{t,z}$ be a smooth planar
diffeomorphism; assume forward and inverse evaluations are smooth on
$\mathbb R\times U\times\mathbb R^2$, $\Phi_{0,z}=\mathrm{id}$ for
$z\in U$, and $\Phi_{t,z}$ fixes the complement of $K$ whenever
$t\in[0,1]$ and $z\in U$. For every $\varepsilon>0$ there is a planar
family $\Psi_z$ for all real $z$, with jointly smooth forward and inverse
evaluations, equal to $\Phi_{1,z}$ for $z\in[a,b]$, fixing all points
outside $K$, and equal to the identity for $z\le a-\varepsilon$ or
$z\ge b+\varepsilon$. Both $(z,x)\mapsto\Psi_z(x)-x$ and
$(z,x)\mapsto\Psi_z^{-1}(x)-x$ have compact support.

Under the same assumptions there is a smooth height-preserving
diffeomorphism $H$ of three-space with compact forward and inverse
displacement support. On heights $z\in[a,b]$ it and its inverse act by
$\Phi_{1,z}$ and $\Phi_{1,z}^{-1}$, respectively. For each such $c$ it
sends $S\times\{c\}$ to $\Phi_{1,c}(S)\times\{c\}$ for every planar
set $S$, and for every family $L(c)$ it sends their union over $[a,b]$ to
the union of the corresponding planar images. It fixes $(x,z)$ when
$x\notin K$, $z\le a-\varepsilon$, or $z\ge b+\varepsilon$.

### Alignment Review

The same independent formal-only translator and prose-only reviewer accepted
both extension propositions on 2026-09-23. Neither statement needs $a\le b$;
when the interval is empty the identity family is valid. The open neighborhood
hypothesis is explicit, and no endpoint-flatness assumption is used.

Candidate declaration SHA-256 values, each including its final newline:

- `exists_interval_supported_planar_family`: `7b2700da3303a17c61a77bf114b610056fbd805c5791e51530f2f5a45c2ff5f2`.
- `exists_interval_supported_height_lift`: `d089d8869f4b7f64fd371b73ea40fadf60b59e0f1a5ae93ea380f73a6697abd7`.

## References

This elementary suspension construction supports Hatcher, *Notes on Basic
3-Manifold Topology* (2014), Theorem 1.1, proof on printed pp. 2-5.
The source and locators are archived in
`references/topology/hatcher-basic-3-manifolds/`.
