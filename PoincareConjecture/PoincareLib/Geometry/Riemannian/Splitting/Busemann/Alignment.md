# Busemann functions of a minimizing line

## Informal proof

For a minimizing line, the functions $t-d_g(\gamma(t),x)$ increase with $t$
and are bounded above by $d_g(\gamma(0),x)$. Their supremum over $t\geq0$
is therefore their finite limit. The reverse triangle inequality makes this
limit 1-Lipschitz. Applying this construction to the reversed line gives the
second limit. The triangle inequality gives $b_++b_-\leq0$, with equality
on the line. Distance Laplacian comparison gives weak subharmonicity of
both limits. The strong maximum principle forces their sum to vanish,
and weak harmonic regularity gives smoothness. Compact balls supply a
calibrated point on every sphere, which gives unit gradient. Bochner's
identity then forces the Hessian to vanish.

The sign here is opposite to Morgan--Tian, Proposition 2.3, pp. 21--23;
the line argument is in the proof of Lemma 2.14, pp. 28--29.

## Proposed formal statements

```lean
noncomputable section
open Filter
open scoped Manifold ContDiff Topology
namespace PoincareMT.RiemannianMetric

def busemannApprox {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (γ : ℝ → M) (t : ℝ) (x : M) : ℝ :=
  t - (g.edist (γ t) x).toReal

def busemann {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (γ : ℝ → M) (x : M) : ℝ :=
  ⨆ t : Set.Ici (0 : ℝ), g.busemannApprox γ t x

theorem busemann_minimizing_line
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    (∀ x : M, Tendsto (fun t => g.busemannApprox γ t x) atTop
      (𝓝 (g.busemann γ x))) ∧
    (∀ x : M, Tendsto (fun t => g.busemannApprox (fun s => γ (-s)) t x) atTop
      (𝓝 (g.busemann (fun s => γ (-s)) x))) ∧
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ) ∧
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann (fun s => γ (-s))) ∧
    (∀ x : M, g.busemann (fun s => γ (-s)) x = -g.busemann γ x) ∧
    (∀ s : ℝ, g.busemann γ (γ s) = s) ∧
    (∀ x : M, D.laplacian (g.busemann γ) x = 0) ∧
    (∀ x : M, g.inner x (D.gradient (g.busemann γ) x)
      (D.gradient (g.busemann γ) x) = 1) ∧
    (∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      D.hessian (g.busemann γ) x v w = 0) := by
  sorry

end PoincareMT.RiemannianMetric
```

## Alignment review

Independent translation and mathematical comparison accepted the statement.
The translator received only the complete formal statements; the reviewer
received only the informal claim and the translation. The translation states:

Let $M$ be a connected smooth manifold with a complete smooth Riemannian
metric $g$ and its Levi-Civita connection, with nonnegative Ricci curvature.
Let $\gamma:\mathbb R\to M$ preserve distance. Define $b_+$ and $b_-$ as the
suprema over $t\geq0$ of $t-d_g(\gamma(t),x)$ and
$t-d_g(\gamma(-t),x)$. Then both expressions tend to their respective
suprema as $t\to+\infty$; both functions are smooth, $b_-=-b_+$,
$b_+(\gamma(s))=s$, and $b_+$ has zero Laplacian, squared gradient length
one, and zero Hessian at every point.

Connectedness makes all intrinsic distances finite. The distance-preserving
line hypothesis expresses unit speed and global minimization, and squared
gradient length one is equivalent to unit length. The full statement above
is implemented by `busemann_minimizing_line` in `Main.lean`. Its analytic
steps are constructed from the metric and line hypotheses. Local coordinate
regularity and Bochner lemmas are intermediate propositions, checked directly
against the corresponding steps of this fixed target.

## Reusable prerequisites

The weak distance inequality follows by the actual Lipschitz Green identity,
signed polar integration, and integration by parts on each nonterminal radial
interval. Nonnegative Ricci curvature bounds the radial density derivative;
the nonnegative terminal contribution has the favorable sign. A distance
lower bound on the test support bounds the coefficient by `(n - 1) / A`.

For harmonic regularity, local intrinsic Lipschitz estimates construct weak
coordinate derivatives. The retained metric density converts the distribution
equation into the weak divergence equation. Elliptic regularity gives a smooth
representative, and continuity identifies it with the original function.

The complete statements used for independent translation were:

```lean
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
namespace PoincareMT.LeviCivitaData

theorem integral_distance_mul_laplacian_le
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {g : RiemannianMetric (m + 1) M}
    (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature)
    (p : M) (A : ℝ) (hA : 0 < A) (φ : M → ℝ)
    (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hAdist : ∀ x ∈ tsupport φ, A ≤ (g.edist p x).toReal) :
    (∫ x, (g.edist p x).toReal * D.laplacian φ x ∂g.volumeMeasure) ≤
      (m : ℝ) / A * ∫ x, φ x ∂g.volumeMeasure

theorem smooth_harmonic_of_distance_lipschitz_of_weak_harmonic
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hn : 0 < n) {f : M → ℝ} (hf : Continuous f)
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    (hweak : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∫ y, f y * D.laplacian ψ y ∂g.volumeMeasure) = 0) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧ ∀ x, D.laplacian f x = 0

end PoincareMT.LeviCivitaData
```

The independent translation states that on a complete connected Riemannian
manifold of dimension `n >= 2` and nonnegative Ricci curvature, a nonnegative
compact smooth test supported at distance at least `A > 0` from `p` satisfies
the displayed distance inequality. On a connected Riemannian manifold of
positive dimension, a continuous intrinsically 1-Lipschitz function annihilating
all compact smooth Laplacian tests is itself smooth and harmonic.

The reviewer accepted both claims. The regularity theorem permits a broader
possibly disconnected setting, with the exact `toReal` hypothesis displayed
above. Its connected specialization has finite intrinsic distances. Compact
support, continuity and local finiteness of volume give ordinary finite
integrals in both intended claims; totalized integration introduces no extra
interpretation of these hypotheses.

## Verification

The full managed `lake build` and `make check` passed, including all 12 frozen
contract hashes and the root import of `Splitting.Busemann`. Running the
following audit with `lake env lean` reports only `propext`, `Classical.choice`,
and `Quot.sound` for each declaration:

```lean
import PoincareLib.Geometry.Riemannian.Splitting.Busemann

#print axioms PoincareMT.RiemannianMetric.busemann_minimizing_line
#print axioms PoincareMT.RiemannianMetric.busemann_parallel_unit_gradient
#print axioms PoincareMT.RiemannianMetric.busemann_distributional_subharmonic
#print axioms PoincareMT.LeviCivitaData.integral_distance_mul_laplacian_le
#print axioms PoincareMT.LeviCivitaData.smooth_harmonic_of_distance_lipschitz_of_weak_harmonic
#print axioms PoincareMT.LeviCivitaData.integral_distance_mul_laplacian
#print axioms PoincareMT.RiemannianMetric.ae_mDifferentiableAt_distance
```
