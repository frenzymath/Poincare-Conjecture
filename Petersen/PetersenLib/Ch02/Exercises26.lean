import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.26 (normal connection, Weingarten relation)

For an isometric immersion `M ↪ M̃` and the ambient Levi-Civita connection
`∇̃`, a tangent field `X` and a normal field `V` give `∇̃_X V`, which decomposes
into a normal part `∇^⊥_X V` (the **normal connection**) and a tangential part
`T_X V` (the shape operator).  Exercise 2.5.26(2) asks to show the shape operator
and the second fundamental form are adjoint,
`g_M(T_X Y, V) = −g_M(Y, T_X V)`.

The reachable algebraic heart is the underlying **Weingarten orthogonality
relation**: for a tangent field `Y` and a normal field `V` (so `g(Y, V) ≡ 0`),
differentiating the vanishing pairing along any `X` and using
metric-compatibility of `∇̃` gives
`g(∇̃_X Y, V) = −g(Y, ∇̃_X V)`.  Since `V` is normal this is `g(II(X, Y), V)`
(the normal part of `∇̃_X Y`, i.e. `T_X Y`) on the left and `−g(Y, T_X V)` (the
tangential part of `∇̃_X V`) on the right — exactly the required adjointness once
the tangent–normal projections are named.

## Design notes

* The formalization states orthogonality as the pointwise hypothesis
  `g(Y q, V q) = 0` for all `q` (`Y` tangent, `V` normal), and derives the
  relation from `RiemannianConnection.metric_compat` and the vanishing of the
  directional derivative of a constant, exactly as Exercise 2.5.17.
* The tangent–normal decomposition `∇̃_X V = ∇^⊥_X V + T_X V`, the definition of
  the normal connection, and its linearity/derivation/tensoriality (parts 1, 3)
  need the immersion / normal-bundle projection infrastructure, not built here.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.26.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Exercise 2.5.26(2)** (Petersen §2.5), Weingarten orthogonality
relation.  For the ambient Levi-Civita connection `∇̃`, a tangent field `Y` and a
normal field `V` — orthogonal everywhere, `g(Y, V) ≡ 0` — one has
`g(∇̃_X Y, V) = −g(Y, ∇̃_X V)` for every direction field `X`.  This is the
adjointness `g(T_X Y, V) = −g(Y, T_X V)` of the second fundamental form and the
shape operator, once `∇̃_X Y`, `∇̃_X V` are split into tangential and normal
parts.

Proof (Petersen's): differentiate the constant pairing `g(Y, V) = 0` along `X`;
metric-compatibility of `∇̃` splits the (vanishing) derivative as
`g(∇̃_X Y, V) + g(Y, ∇̃_X V) = 0`. -/
theorem exercise2_5_26 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y V : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hV : IsSmoothVectorField V)
    (hYV : ∀ q, g.metricInner q (Y q) (V q) = 0) (p : M) :
    g.metricInner p (D.cov p (X p) Y) (V p)
      = - g.metricInner p (Y p) (D.cov p (X p) V) := by
  have hcompat := D.metric_compat hY hV p (X p)
  rw [show (fun q => g.metricInner q (Y q) (V q)) = fun _ => (0 : ℝ) from funext hYV]
    at hcompat
  have h0 : dirTangent (fun _ : M => (0 : ℝ)) (X p) = 0 := by
    show mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) p (X p) = 0
    rw [mfderiv_const]; rfl
  rw [h0] at hcompat
  linarith [hcompat]

end PetersenLib
