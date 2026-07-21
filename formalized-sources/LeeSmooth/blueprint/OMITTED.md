# Items omitted from the LeeSmooth blueprint

The blueprint carries only items whose Lean is verified. This file records
every book item that was **left out**, so the gap is documented rather than
silent. Generated alongside the blueprint — do not edit by hand.

**Absence of a node in the blueprint does not mean Lee lacks the result.**
It almost always means the result is unproved or broken in the upstream Lean
(see `../UPSTREAM_LEAN_AUDIT.md`).

Total book items (Chapters 1–8): **599**. Carried: **310**. Omitted: **289**.

## Proof is `sorry` (81)

The upstream Lean states the result but does not prove it.

```
  Definition 1-extra-1
  Definition 1.6-extra-1
  Proposition 1.38
  Definition 2.11-extra-2
  Lemma 2.26
  Problem 2-10
  Problem 2-11
  Problem 2-5
  Proposition 2.15
  Theorem 2.18
  Corollary 3.22
  Definition 3.18-extra-2
  Definition 3.18-extra-3
  Problem 3-1
  Problem 3-6
  Problem 3-7
  Proposition 3.2
  Corollary 4.13
  Corollary 4.43
  Definition 4.21-extra-1
  Example 4.17
  Example 4.2
  Exercise 4.16
  Exercise 4.45
  Problem 4-10
  Problem 4-11
  Problem 4-13
  Problem 4-3
  Problem 4-7
  Problem 4-8
  Proposition 4.1
  Proposition 4.22
  Proposition 4.33
  Proposition 4.6
  Theorem 4.15
  Theorem 4.25
  Theorem 4.26
  Theorem 4.29
  Theorem 4.30
  Theorem 4.31
  Corollary 5.14
  Definition 5.30-extra-2
  Definition 5.30-extra-3
  Definition 5.31-extra-2
  Definition 5.36-extra-3
  Example 5.17
  Example 5.9
  Exercise 5.40
  Problem 5-23
  Problem 5-6
  Problem 5-7
  Problem 5-8
  Problem 5-9
  Proposition 5.1
  Proposition 5.18
  Proposition 5.22
  Proposition 5.37
  Proposition 5.38
  Proposition 5.41
  Proposition 5.43
  Proposition 5.46
  Proposition 5.7
  Remark 5.29-extra-2
  Theorem 5.12
  Theorem 5.29
  Theorem 5.31
  Theorem 5.51
  Corollary 6.33
  Lemma 6.13
  Theorem 6.30
  Definition 7.46-extra-3
  Example 7.10
  Example 7.19
  Remark 7.50-extra-5
  Theorem 7.35
  Example 8.47
  Problem 8-14
  Problem 8-15
  Problem 8-29
  Problem 8-30
  Theorem 8.49
```

## Depends on a sorried module (117)

Compiles, but its module imports a module containing `sorry`. This test is *conservative*: it disqualifies an item whose own principal declaration may well be sorry-free. A per-declaration axiom check would likely restore a substantial share of these.

```
  Example 1.21
  Example 1.32
  Example 1.4
  Exercise 1.1
  Exercise 1.39
  Exercise 1.41
  Exercise 1.42
  Lemma 1.10
  Problem 1-3
  Proposition 1.11
  Proposition 1.12
  Proposition 1.40
  Theorem 1.15
  Theorem 1.2
  Exercise 2.16
  Exercise 2.19
  Exercise 2.2
  Exercise 2.27
  Problem 2-12
  Corollary 3.3
  Proposition 3.20
  Example 4.11
  Example 4.18
  Example 4.23
  Example 4.35
  Exercise 4.3
  Exercise 4.32
  Exercise 4.34
  Exercise 4.37
  Exercise 4.38
  Exercise 4.42
  Exercise 4.44
  Exercise 4.7
  Exercise 4.9
  Problem 4-12
  Problem 4-5
  Problem 4-6
  Problem 4-9
  Proposition 4.28
  Proposition 4.36
  Proposition 4.40
  Proposition 4.41
  Proposition 4.8
  Corollary 5.39
  Definition 5.36-extra-1
  Example 5.15
  Example 5.25
  Exercise 5.24
  Exercise 5.36
  Exercise 5.42
  Exercise 5.50
  Exercise 5.52
  Problem 5-11
  Problem 5-16
  Problem 5-17
  Problem 5-18
  Problem 5-22
  Problem 5-3
  Proposition 5.21
  Proposition 5.23
  Proposition 5.35
  Proposition 5.49
  Remark 5.29-extra-3
  Theorem 5.33
  Theorem 5.48
  Theorem 5.8
  Corollary 6.11
  Corollary 6.12
  Corollary 6.17
  Corollary 6.31
  Definition 6.42-extra-2
  Definition 6.44-extra-1
  Problem 6-1
  Problem 6-10
  Problem 6-11
  Problem 6-12
  Problem 6-14
  Problem 6-15
  Problem 6-16
  Problem 6-17
  Problem 6-7
  Problem 6-9
  Proposition 6.25
  Proposition 6.5
  Theorem 6.10
  Theorem 6.21
  Theorem 6.32
  Theorem 6.35
  Corollary 7.6
  Definition 7.51-extra-2
  Lemma 7.12
  Problem 7-10
  Problem 7-19
  Problem 7-7
  Proposition 7.15
  Proposition 7.16
  Proposition 7.17
  Proposition 7.26
  Theorem 7.21
  Theorem 7.25
  Theorem 7.5
  Theorem 7.7
  Corollary 8.32
  Definition 8.54-extra-1
  Example 8.10
  Example 8.20
  Example 8.24
  Example 8.5
  Notation 8.56-extra-3
  Problem 8-10
  Problem 8-12
  Problem 8-18
  Proposition 8.1
  Proposition 8.14
  Proposition 8.15
  Proposition 8.22
  Proposition 8.23
```

## Module does not compile (63)

Excluded from the Lean library entirely; upstream does not build.

```
  Proposition 1.16
  Problem 3-8
  Example 4.20
  Problem 4-4
  Corollary 5.13
  Example 5.19
  Example 5.26
  Example 5.28
  Example 5.45
  Problem 5-1
  Problem 5-10
  Problem 5-13
  Problem 5-15
  Problem 5-2
  Problem 5-21
  Problem 5-5
  Proposition 5.16
  Proposition 5.47
  Theorem 5.11
  Corollary 6.16
  Corollary 6.27
  Lemma 6.14
  Problem 6-13
  Problem 6-2
  Problem 6-4
  Problem 6-5
  Problem 6-6
  Problem 6-8
  Theorem 6.15
  Theorem 6.18
  Theorem 6.19
  Theorem 6.20
  Theorem 6.23
  Theorem 6.24
  Theorem 6.26
  Theorem 6.29
  Theorem 6.36
  Example 7.24
  Example 7.28
  Exercise 7.20
  Problem 7-1
  Problem 7-13
  Problem 7-14
  Problem 7-15
  Problem 7-16
  Problem 7-18
  Problem 7-20
  Problem 7-21
  Corollary 8.42
  Corollary 8.50
  Definition 8.54-extra-2
  Definition 8.61-extra-1
  Example 8.40
  Exercise 8.43
  Problem 8-13
  Problem 8-17
  Problem 8-26
  Problem 8-27
  Problem 8-28
  Problem 8-4
  Proposition 8.45
  Theorem 8.44
  Theorem 8.46
```

## No principal declaration (19)

The item file declares nothing identifiable as the item (facade or scaffolding only).

```
  Example 1.25
  Example 1.26
  Example 1.29
  Example 1.31
  Example 1.34
  Definition 2.11-extra-3
  Definition 4.24-extra-2
  Definition 4.25-extra-2
  Exercise 4.27
  Theorem 4.12
  Theorem 4.14
  Definition 5.35-extra-2
  Exercise 5.44
  Problem 5-12
  Proposition 5.2
  Proposition 5.3
  Proposition 5.4
  Remark 5.32-extra-1
  Example 7.36
```

## Lean declaration unidentifiable (9)

A `#check`/`recall` facade whose named token is not a resolvable declaration (e.g. `inferInstance`).

```
  Exercise 1.43
  Definition 2.8-extra-2
  Definition 3.19-extra-5
  Problem 3-3
  Proposition 5.5
  Definition 7.50-extra-1
  Definition 8.56-extra-2
  Lemma 8.25
  Notation 8.54-extra-3
```

