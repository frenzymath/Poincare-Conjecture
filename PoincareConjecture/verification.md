# Proof verification

- **Lean build and endpoint axiom audits: passed**, at
  [516badd1](https://github.com/frenzymath/Poincare-Conjecture/commit/516badd1).
- **Comparator: passed for both smooth and topological targets**, with Nanoda
  and Lean's default kernel, at
  [1876d7dc](https://github.com/frenzymath/Poincare-Conjecture/commit/1876d7dc2c85325a3f62ce9776af98f910c5db04).

Comparator permitted only `propext`, `Classical.choice`, and `Quot.sound`.
The production proof tree was unchanged between these two checks. The build
and Comparator logs, configuration, tool hashes, and exact source revisions
are preserved in the
[verification evidence](../archive/PoincareConjecture/references/ricci-flow/mapher/integration-verification/README.md).
These are recorded local checks of the cited revisions, not new CI results
for later documentation changes.

Blueprint source annotations provide navigation between the exposition and
Lean declarations. Their coverage is separate from proof verification and
from mathematical review of the exposition. Seventeen of the eighteen imported
chapters have accepted Horizon reviews; smoothing and whole-book publication
review remain pending in this snapshot.
