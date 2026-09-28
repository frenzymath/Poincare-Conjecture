---
title: Smooth disks from width profiles
label: smooth-width-profile-disks
type: theorem
labels: [informal_stated, informal_proved, formally_stated, formally_proved, kernel_checked]
children: []
workspace_commit: 52f01faeb69d3a6d4ec04aa2ace2f5b22de60936
workspace_file: PoincareLib/Topology/Manifold/Schoenflies/Morse/Models/Saddle/Global/Wall/Attachment/WallDisk/HeightProfile.lean
lean_declaration: Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_smooth_wall_disk_of_height_profile
references:
  - "Hatcher3M2014: auxiliary disk marking for the corner paragraph following Lemma 1.3, p. 5"
---

## Informal Description

Let a < b and let r, l, u be smooth real functions. Suppose r is positive
on (a,b), agrees with l(t)(t-a) near a and with u(t)(b-t) near b, with
l(a)>0 and u(b)>0. Then the region
W = {(0,y,t) : a <= t <= b and y^2 <= r(t)} is the image of the closed
unit disk under a smooth injective map from R^2 to R^3 whose differential
is injective everywhere.

## Informal Proof

Normalize the height interval to [-1,1]. Dividing the normalized squared
width by 1-t^2 has removable singularities at both endpoints and gives a
smooth positive function on a neighborhood of the interval. Extend its
logarithm smoothly to the line, then exponentiate half that extension to
obtain a globally positive scale s. The map (x,t) to (0,s(t)x,H(t)), where
H restores the original height, maps the unit disk exactly onto W. Its
explicit smooth left inverse proves injectivity and injectivity of its
differential everywhere.

## Proposed Formal Statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.WallDisk.HeightProfile

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

example
    {a b : Real} (hab : a < b) {r l u : Real → Real}
    (hr : ContDiff Real ∞ r) (hl : ContDiff Real ∞ l) (hu : ContDiff Real ∞ u)
    (hleft : r =ᶠ[𝓝 a] (fun t => l t * (t-a)))
    (hright : r =ᶠ[𝓝 b] (fun t => u t * (b-t)))
    (hlpos : 0 < l a) (hupos : 0 < u b)
    (hrpos : ∀ t ∈ Ioo a b, 0 < r t) :
    ∃ d : EuclideanSpace Real (Fin 2) → EuclideanSpace Real (Fin 3),
      ContDiff Real ∞ d ∧ Injective d ∧ (∀ q, Injective (fderiv Real d q)) ∧
      d '' closedBall 0 1 =
        {p | p 0 = 0 ∧ p 2 ∈ Icc a b ∧ (p 1)^2 ≤ r (p 2)} := by
  exact Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_smooth_wall_disk_of_height_profile
    hab hr hl hu hleft hright hlpos hupos hrpos
```

## Formal-To-Informal Translation

Let a and b be real numbers with a<b, and let r,l,u:R to R be smooth.
Assume that on some neighborhood of a, r(t)=l(t)(t-a), and on some
neighborhood of b, r(t)=u(t)(b-t). Assume l(a)>0, u(b)>0, and r(t)>0
for every a<t<b. There exists a smooth globally injective map d:R^2 to
R^3, with injective differential at every point of R^2, whose image of the
closed unit disk is precisely {(x,y,t): x=0, a<=t<=b, y^2<=r(t)}.

## Alignment Review

The separate local comparison accepts the translation: the three functions
are smooth on the whole line, the endpoint identities hold on neighborhoods,
and the conclusion requires global injectivity and full differential rank,
not merely properties on the disk. Native translation was attempted and
failed with `agent thread limit reached`; the local passes are the documented
fallback. These were intermediate geometric lemmas during implementation;
the direct statement comparison was proportionate before this reusable node
was selected for recording.

## Formalization

The [published theorem](/api/v2/forge/web/poincare-conjecture/workspace-poincare-conjecture/src/commit/52f01faeb69d3a6d4ec04aa2ace2f5b22de60936/PoincareLib/Topology/Manifold/Schoenflies/Morse/Models/Saddle/Global/Wall/Attachment/WallDisk/HeightProfile.lean)
uses RadiusFactor and Weighted. JoinedWidth applies it to the saddle
continuation and corrected upper cap. Lean 4.33.1: Wall.Checks passed 11305
jobs, make check passed 20327 jobs and all 12 frozen contracts. Recursive
audits contain only propext, Classical.choice, and Quot.sound. This result
does not identify the final terminal-sphere boundary.

## References

This auxiliary width-profile lemma is proved directly; it is not a numbered
source theorem. It supplies the marked disk used in the corner attachment
following Hatcher, Lemma 1.3, p. 5.

```bibtex
@misc{Hatcher3M2014,
  author = {Hatcher, Allen},
  title = {Notes on Basic 3-Manifold Topology},
  year = {2014},
  note = {Theorem 1.1, pp. 1--5; Lemma 1.3 and corner paragraph, p. 5},
  url = {https://pi.math.cornell.edu/~hatcher/3M/3Mfds2014.pdf}
}
```
