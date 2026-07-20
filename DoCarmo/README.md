<h1 align="center">Riemannian Geometry Challenge</h1>

<p align="center"><em>In progress.</em></p>

<p align="center">
A public, open initiative to build Riemannian geometry into a living,<br/>
machine-verified textbook — a shared foundation anyone can learn from,<br/>
contribute to, reuse, and build on. Made for everyone.
</p>

<p align="center">
  <a href="https://lehengchen.github.io/OpenGA/"><strong>Browse the project online →</strong></a>
</p>

## Explore online

A read-only web view of the project — the blueprint, its dependency graph, and
progress — is published at **[lehengchen.github.io/OpenGA](https://lehengchen.github.io/OpenGA/)**.
It is rebuilt automatically on every push to `main`.

## Use the Lean library

Add the dependency to your `lakefile.lean`:

```
require OpenGALib from git "https://github.com/MathNetwork/OpenGA.git" @ "main"
```

Build:

```
lake exe cache get
lake build
```

Requires Mathlib at the SHA pinned in `lake-manifest.json`.

## Quality checks

Run the same build, test, declaration-lint, and text-style checks used by CI:

```bash
lake build
lake test
lake lint
lake exe lint-style DoCarmoLib
```

`DoCarmoLibTest/Axioms.lean` guards the axiom sets of the Hopf–Rinow facade theorems. Each
test fails if its theorem acquires an axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.

## Status

Pre-`v0.1.0`, experimental. PRE-PAPER `sorry`'d statements and narrow structural
axioms are tracked with explicit repair plans in module docstrings (search for
`**Sorry status**:` / `axiom`).

## Contributing

Issues and PRs welcome.

## License

Released under the Apache 2.0 License. See the LICENSE file for details.

---

<p align="center">
  <a href="https://github.com/MathNetwork/Astrolabe"><img src="https://img.shields.io/badge/Powered_by-Astrolabe-669aba?style=flat-square&labelColor=11111b" alt="Powered by Astrolabe"></a>
  <a href="https://events.astrolabe.network/"><img src="https://img.shields.io/badge/Website-events.astrolabe.network-be1420?style=flat-square&labelColor=11111b" alt="Website"></a>
  <a href="https://discord.gg/nQdU4q3u9"><img src="https://img.shields.io/badge/Discord-Join-5865F2?style=flat-square&logo=discord&logoColor=white&labelColor=11111b" alt="Discord"></a>
</p>
