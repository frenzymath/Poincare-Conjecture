import PetersenLib.Ch06.CurvatureChartBridge

/-!
# Petersen Ch. 6, §6.1 — higher-order partials and Lemma 6.1.2

Petersen's §6.1 (pp. 249–251): for a map `c(u, s, t)` into `M`, the mixed covariant
partials of `∂c/∂t` in the two remaining parameters do **not** commute, and their
commutator is exactly the curvature:
$$
\frac{\partial^3c}{\partial u\,\partial s\,\partial t}
  - \frac{\partial^3c}{\partial s\,\partial u\,\partial t}
  = R\Big(\frac{\partial c}{\partial u}, \frac{\partial c}{\partial s}\Big)\frac{\partial c}{\partial t}.
$$
Blueprint nodes `def:pet-ch6-higher-order-partials` and
`lem:pet-ch6-third-partial-commutator`.

## What this file does

The identity is *do Carmo's Ch. 4 Lemma 4.1* — the same statement with `(s,t)` for
Petersen's `(u,s)` and `V = ∂c/∂t` — and its coordinate engine is already available as
`PetersenLib.Jacobi.surface_covariant_commutator_of_eventually`
(`Riemannian/Jacobi/SurfaceCurvatureCommutation.lean`). That engine states its
right-hand side as the **coordinate** curvature `chartCurvatureContraction2`;
`Ch06/CurvatureChartBridge.lean` identifies that with Ch. 3's Koszul `curvatureTensorAt`.
This file combines the two, and packages the iterated derivative under Petersen's name.

## Conventions and scope

* **The parameters are indexed by `Fin 2`**, `0 = u` (the first surface parameter) and
  `1 = s` (the second). `thirdPartialDerivative g α f V a b` is `D/∂x_a D/∂x_b V`;
  Petersen's `∂³c/∂u∂s∂t` is `thirdPartialDerivative g α f (∂c/∂t) 0 1`, and his
  `∂³c/∂s∂u∂t` is the same with `0` and `1` swapped. This is the "recursive" reading of
  the higher-partials definition node: an `n`-th partial is a first partial of an
  `(n−1)`-st one, and the `t`-slot enters only through the field `V`.
* **Fixed chart, general field.** The surface is a `C²` map `f : ℝ × ℝ → E` — the chart
  reading `φ_α ∘ c` — and the field `V : ℝ × ℝ → E` is arbitrary, so the lemma is stated
  in the generality of do Carmo's Lemma 4.1 rather than only for `V = ∂c/∂t`. Petersen's
  literal statement is the specialization; the general form is what the Jacobi-equation
  derivation actually consumes (there `V = ∂c/∂t` and the geodesic hypothesis kills one
  side).
* **The chart is centred at the base point** (`hbase : f x₀ = extChartAt I p p`). Ch. 3's
  coordinate curvature formula `curvatureTensor_coordinates`, and hence the bridge, is
  diagonal — chart centre = evaluation point. This costs no generality for Lemma 6.1.2,
  whose conclusion is pointwise at `p = c(u₀,s₀,t₀)`: read the surface in the chart at
  that very point.
* **Regularity is explicit**, in the `HasFDerivAt`-with-supplied-derivative style of the
  vendored engine: `f` and `V` are differentiable near `x₀` with a second derivative at
  `x₀`. Petersen leaves smoothness implicit.

## The two sign conventions cancel

do Carmo's curvature convention is the negative of Petersen's (see
`Ch06/CurvatureChartBridge.lean`), and do Carmo's commutator runs in the opposite
parameter order to Petersen's. Composing the two flips gives back Petersen's identity
with Petersen's `R` — which is why `thirdPartialCurvatureFormula` below has no stray sign.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### Higher-order partials -/

/-- **Math.** Petersen §6.1 (p. 249), `def:pet-ch6-higher-order-partials`: the **covariant
partial derivative of a field `V` along a chart-read surface `f` in the parameter `x_a`**,
`a : Fin 2` selecting `u` (`a = 0`) or `s` (`a = 1`). Each is the coordinate covariant
derivative `D/dt` of Ch. 5 applied to the corresponding slice curve of `f`. -/
def surfaceCovariantDeriv (g : RiemannianMetric I M) (α : M) (f : ℝ × ℝ → E)
    (a : Fin 2) (V : ℝ × ℝ → E) : ℝ × ℝ → E :=
  match a with
  | 0 => Jacobi.surfaceCovariantDerivS (I := I) g α f V
  | 1 => Jacobi.surfaceCovariantDerivT (I := I) g α f V

@[simp] theorem surfaceCovariantDeriv_zero (g : RiemannianMetric I M) (α : M)
    (f V : ℝ × ℝ → E) :
    surfaceCovariantDeriv (I := I) g α f 0 V
      = Jacobi.surfaceCovariantDerivS (I := I) g α f V := rfl

@[simp] theorem surfaceCovariantDeriv_one (g : RiemannianMetric I M) (α : M)
    (f V : ℝ × ℝ → E) :
    surfaceCovariantDeriv (I := I) g α f 1 V
      = Jacobi.surfaceCovariantDerivT (I := I) g α f V := rfl

/-- **Math.** Petersen §6.1 (p. 249), `def:pet-ch6-higher-order-partials`: the **third
partial** `∂³c/∂x_a ∂x_b ∂t`, defined *recursively* as the `x_a`-partial of the
`x_b`-partial of the field `V`. Petersen's `∂³c/∂u∂s∂t` is the case `a = 0`, `b = 1`,
`V = ∂c/∂t`; his `∂³c/∂s∂u∂t` swaps `a` and `b`. Lemma 6.1.2
(`thirdPartialCurvatureFormula`) says the two differ by the curvature — in particular
third partials are **not** symmetric, unlike the second partials of Ch. 5's symmetry
lemma. -/
def thirdPartialDerivative (g : RiemannianMetric I M) (α : M) (f : ℝ × ℝ → E)
    (V : ℝ × ℝ → E) (a b : Fin 2) : ℝ × ℝ → E :=
  surfaceCovariantDeriv (I := I) g α f a (surfaceCovariantDeriv (I := I) g α f b V)

/-! ### Lemma 6.1.2 -/

/-- **Math.** **Petersen Lemma 6.1.2** (`lem:pet-ch6-third-partial-commutator`, p. 250) —
*third partials and curvature*. For a map `c(u,s,t)` into `M`,
$$
\frac{\partial^3c}{\partial u\,\partial s\,\partial t}
  - \frac{\partial^3c}{\partial s\,\partial u\,\partial t}
  = R\Big(\frac{\partial c}{\partial u}, \frac{\partial c}{\partial s}\Big)\frac{\partial c}{\partial t},
$$
here in the form: for a `C²` surface `f` read in the chart at the base point `p` and a
`C²` field `V` along it (Petersen's `V = ∂c/∂t`),
`D/∂u D/∂s V − D/∂s D/∂u V = R(∂f/∂u, ∂f/∂s)V`, with `R` Ch. 3's `curvatureTensorAt`.

**Proof.** Petersen computes in coordinates; so do we, but the computation is do Carmo's
Ch. 4 Lemma 4.1, already available as
`Jacobi.surface_covariant_commutator_of_eventually`. It delivers the commutator in the
*opposite* parameter order and against do Carmo's curvature convention; negating both —
`neg_sub` on the left and `chartCurvatureContraction2_eq_neg_curvatureTensorAt` on the
right — is exactly Petersen's statement. The side condition that the base point is
interior to the chart target is automatic at the chart centre for a boundaryless model
(`extChartAt_target_subset_interior_of_boundaryless`). -/
theorem thirdPartialCurvatureFormula (g : RiemannianMetric I M) (p : M)
    (f V : ℝ × ℝ → E) (Df DV : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E))
    (D2f D2V : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E) (u₀ s₀ : ℝ)
    (hf : ∀ᶠ q in nhds (u₀, s₀), HasFDerivAt f (Df q) q)
    (hf2 : HasFDerivAt Df D2f (u₀, s₀))
    (hV : ∀ᶠ q in nhds (u₀, s₀), HasFDerivAt V (DV q) q)
    (hV2 : HasFDerivAt DV D2V (u₀, s₀))
    (hbase : f (u₀, s₀) = extChartAt I p p) :
    thirdPartialDerivative (I := I) g p f V 0 1 (u₀, s₀)
        - thirdPartialDerivative (I := I) g p f V 1 0 (u₀, s₀)
      = curvatureTensorAt (g.leviCivita).toAffineConnection p
          (Df (u₀, s₀) (1, 0)) (Df (u₀, s₀) (0, 1)) (V (u₀, s₀)) := by
  have hmem : f (u₀, s₀) ∈ interior (extChartAt I p).target := by
    rw [hbase]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p
      (mem_extChartAt_target (I := I) p)
  have h := Jacobi.surface_covariant_commutator_of_eventually (I := I) g p f V Df DV
    D2f D2V u₀ s₀ hf hf2 hV hV2 hmem
  -- `h` is do Carmo's order `D/∂s D/∂u − D/∂u D/∂s`; Petersen's is the negative
  have hswap : thirdPartialDerivative (I := I) g p f V 0 1 (u₀, s₀)
      - thirdPartialDerivative (I := I) g p f V 1 0 (u₀, s₀)
      = -(Jacobi.surfaceCovariantDerivT (I := I) g p f
            (Jacobi.surfaceCovariantDerivS (I := I) g p f V) (u₀, s₀)
          - Jacobi.surfaceCovariantDerivS (I := I) g p f
            (Jacobi.surfaceCovariantDerivT (I := I) g p f V) (u₀, s₀)) := by
    rw [neg_sub]
    rfl
  rw [hswap, h, hbase, chartCurvatureContraction2_eq_neg_curvatureTensorAt, neg_neg]

end PetersenLib

end
