# The Poincare Conjecture

The completed Lean formalization proves the smooth and topological Poincare
theorems. Its proof library has passed a full Lean build, endpoint axiom audits,
and Comparator verification with Nanoda and Lean's default kernel.

## The blueprint

The eighteen-chapter blueprint was developed with Archon Horizon from the
definitions, theorem statements, and proofs in
[PoincareLib](https://github.com/frenzymath/Poincare-Conjecture/tree/main/PoincareConjecture/PoincareLib).
It follows the implemented argument:
three-manifold foundations, Ricci flow, reduced geometry, ancient models,
necks and caps, singular limits, surgery and global continuation, filling width,
ramps, annular comparison, finite extinction, reverse surgery, sphere reduction,
protected Dehn surfaces, compact cores, relative rigidity, and smoothing.

The introduction explains the selection of mathematical nodes, the chapter
structure, notation, and revision-specific verification evidence. The smooth
theorem concludes Chapter 14. The **Poincare conjecture**, for topological
three-manifolds, is the final theorem of Chapter 18.

The companion reference projects contain reading blueprints for the books
and articles used as mathematical background. Their source references are
distinct from the main blueprint's links to Lean declarations.

## Sources

- [FrenzyMath announcement](https://frenzymath.com/news/poincare-formalization/)
- [Companion proof repository](https://github.com/frenzymath/PoincareConjecture)
- [Blueprint source](https://github.com/frenzymath/Poincare-Conjecture/tree/main/PoincareConjecture/blueprint)
- [Verification evidence and reproduction](https://github.com/frenzymath/Poincare-Conjecture/blob/main/site/verification.md)
