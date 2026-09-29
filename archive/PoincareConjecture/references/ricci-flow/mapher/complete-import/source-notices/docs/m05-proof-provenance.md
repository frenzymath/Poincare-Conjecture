---
document_status: ACTIVE
updated: 2026-09-17
---

# M05 Proof Provenance

The auditable local export is commit `85da5fa7`, integrated from remote main
`859eafe3`. Its file headers identify Archon Horizon workspace revision
`bdc557369304b0ef899f8c31d3d5fece41eabcb1`; that upstream object is not present
in this repository. The exported Lean files, not an external package, are
the local build inputs. Header provenance is not a semantic acceptance claim.

The ODE files retain their DifferentialGeometry contributor copyright,
Apache-2.0 notice, original source path, revision
`1b535dd102b94cc42b107cca27059687888f08b3` and original-file SHA-256 where
supplied by the export. Preserve these notices when reorganizing the files.
The local integration splits oversized files without changing theorem
statements or proof bodies; its review record identifies the moved modules.

The two original module paths remain import-compatible. The earlier part of
`HigherRegularity/VariationalMapContDiffOnK.lean` moves to its
`VariationalMapContDiffOnK/Foundations.lean` submodule. The earlier parts of
`LocalFlow/ParametricLinearODE.lean` move to its `ParametricLinearODE/Variational.lean`
and `ParametricLinearODE/ParameterDerivative.lean` submodules. Original source
blocks reconstruct byte-for-byte against `62ddd9fe`; only import and section
scaffolding is added. Public names are preserved. Moving the private
`variationalW_norm_bound_on_Icc` changes its generated module-qualified name.

The imported metric-compatibility helper is renamed from `mvfderiv_inner`
to `mvfderiv_inner_on_fields` because the former name already belongs to
`Proofs/Ch01/Koszul.lean`. Only the new M05 helper and its three-module call
sites change; its statement and proof are otherwise identical. This collision
was detected by the aggregate build, beyond the focused M05 audit.

`Analysis/Calculus/WithinProduct.lean` retains A Tucker's copyright and
identifies the adapted Mathlib private mean-value estimate. The Apache-2.0
license text is available in the pinned dependency at
`.lake/packages/mathlib/LICENSE` and in
[that exact Mathlib revision](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/LICENSE).
This reference concerns the attributed third-party material, not a new
license grant for the whole project; see [licensing.md](licensing.md).

All newly imported helper declarations remain `UNREVIEWED` in the declaration
register. Kernel checking, unchanged public contracts, and independent
mathematical review of each helper are separate gates. See the
[bounded integration review](../reviews/declarations/2026-09-17-m05-proof-import-compatibility.md).
