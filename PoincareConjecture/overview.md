# The Poincare Conjecture

The completed Lean formalization proves the smooth and topological Poincare
theorems. Its proof library has passed a full Lean build, endpoint axiom audits,
and Comparator verification with Nanoda and Lean's default kernel.

## The blueprint

Archon Horizon's eighteen-chapter exposition follows the implemented proof:
three-manifold foundations, Ricci flow, reduced geometry, ancient models,
necks and caps, singular limits, surgery and global continuation, filling width,
ramps, annular comparison, finite extinction, reverse surgery, sphere reduction,
protected Dehn surfaces, compact cores, relative rigidity, and smoothing.

This snapshot is pinned to Horizon workspace revision `fbdf7e1493ed`.
Seventeen chapters have passed Horizon's source and readability review.
The smoothing chapter and whole-book publication review remain pending;
the exposition's review status is separate from verification of the Lean proof.

The main blueprint links mathematical statements to the current proof library.
The Source links view records annotation coverage without treating it as proof
completion. Some explanatory statements lack annotations, and three historical
surgery adapters refer to removed auxiliary declarations. The Verification tab
records the separate, revision-pinned build and Comparator results. The sixteen
reference projects contain only reading blueprints, without formalization progress.

## Sources

- [FrenzyMath announcement](https://frenzymath.com/news/poincare-formalization/)
- [Companion proof repository](https://github.com/frenzymath/PoincareConjecture)
- [Blueprint source and review records](https://github.com/frenzymath/Poincare-Conjecture/tree/import/poincare-subject-library/PoincareConjecture/blueprint/horizon-import)
- [Verification evidence](https://github.com/frenzymath/Poincare-Conjecture/tree/import/poincare-subject-library/PoincareConjecture/references/ricci-flow/mapher/integration-verification)
