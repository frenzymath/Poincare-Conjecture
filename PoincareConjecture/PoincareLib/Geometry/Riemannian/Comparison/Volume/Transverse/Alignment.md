# Radial density comparison

## Informal proof

Normalize the radial exponential by an orthonormal frame at the center.
Along a ray, parallel transport expresses its radial variation fields as a
Jacobi matrix. The radial column splits off, and the absolute transverse
determinant equals the radial power times the pullback metric density.
The curvature operator is symmetric, annihilates the radial direction, and
its transverse trace is the retained Ricci curvature. The Riccati trace
estimate therefore bounds the second derivative of the density root by its
hyperbolic model equation. The signed density root is smooth at the center,
so the scalar Wronskian argument gives comparison on every regular segment.
Before a terminal minimizing vector, a longer minimizing segment provides
nonsingularity by the checked second variation theorem. The nonterminal
minimizing support is downward closed, so extension by zero preserves
comparison. In dimension one, constant radial speed gives density one.

Reference: Morgan--Tian, Theorem 1.34, p. 19. The original precompact-ball
hypothesis is retained. Routine matrix, scalar, and ray lemmas are internal
steps and were compared directly against this argument.

## Proposed formal statements

```lean
namespace PoincareMT.RiemannianMetric

theorem exists_radial_density_comparison_of_precompact_ball
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareMT.RiemannianMetric n M) (D : PoincareMT.LeviCivitaData g)
    (p : M) (hn : 1 ≤ n) {R κ : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ e : EuclideanSpace ℝ (Fin n) → M,
        (∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) ∧
        ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
        HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0 ∧
        (∀ v ∈ Metric.ball 0 R,
          g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            g.tangentNorm (e (t • v))
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖ ∧
            g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t) ∧
        ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          AntitoneOn (fun t : ℝ =>
            (t ^ (n - 1) *
              (Poincare.VolumeComparison.localMinimizingSet (fun v => g.edist p (e v)) R \
                Poincare.VolumeComparison.terminalRadialPoints
                  (Poincare.VolumeComparison.localMinimizingSet
                    (fun v => g.edist p (e v)) R) R).indicator
                (g.pullbackVolumeDensity e) (t • (θ : EuclideanSpace ℝ (Fin n)))) /
              PoincareMT.RiemannianMetric.modelS κ t ^ (n - 1)) (Set.Ioo 0 R) := by
  sorry

end PoincareMT.RiemannianMetric
```

## Informal translation

**Proposition.** Let $n\geq1$, let $M$ be a Hausdorff smooth $n$-dimensional
manifold with smooth Riemannian metric $g$, and let $\nabla$ be a smooth,
torsion-free, metric-compatible connection. Suppose $R>0$, $\kappa\geq0$,
$\overline{B_g(p,R)}$ is compact, and
$\operatorname{Ric}_{\nabla,x}(v,v)\geq-(n-1)\kappa g_x(v,v)$ for every
$x\in B_g(p,R)$ and $v\in T_xM$. Write $d_g$ for the possibly extended-valued
Riemannian distance. Set $s_0(t)=t$ and
$s_\kappa(t)=\sinh(\sqrt\kappa t)/\sqrt\kappa$ when $\kappa>0$.

For the selected chart $\varphi$ at $p$, there exist an invertible real linear
map $L:\mathbb R^n\to\mathbb R^n$ and a map $e:\mathbb R^n\to M$ such that
$g_p(d\varphi^{-1}Lv,d\varphi^{-1}Lw)=\langle v,w\rangle$, $e$ is smooth on
$B(0,R)$, $e(0)=p$, and $d(\varphi\circ e)_0=L$. Each curve
$\gamma_v(t)=e(tv)$ is a geodesic wherever $\|tv\|<R$; for $v\in B(0,R)$
and $0\leq t\leq1$ it has speed $\|v\|$ and satisfies
$d_g(p,e(tv))\leq t\|v\|$.

Define $A=\{v:\|v\|<R,\ d_g(p,e(v))=\|v\|\}$ and let $T$ consist of
nonzero $v\in A$ for which no rational $q>1$ satisfies $q\|v\|<R$ and
$qv\in A$. Let
$\rho_e(x)=\sqrt{\det[g_{e(x)}(de_x(u_i),de_x(u_j))]_{i,j=1}^n}$ for the
standard orthonormal basis $u_i$. For every unit vector $\theta$, the function
$t\mapsto t^{n-1}\mathbf1_{A\setminus T}(t\theta)\rho_e(t\theta)/s_\kappa(t)^{n-1}$
is nonincreasing on $(0,R)$.

## Alignment review

Accepted by the independent `statement_alignment_review` agent after the
`statement_translation` agent received only the complete declaration and
the supporting definitions. The reviewer received only the mission's
revision-1 informal statement and the standalone translation.

The smooth torsion-free metric-compatible connection is the Levi-Civita
connection. The initial isometry and geodesic rays identify the exponential;
changing the orthonormal identification preserves the conclusion by an
orthogonal change of variables. Rational extensions detect the same terminal
vectors because radial minimizing segments remain minimizing when shortened.
Thus no additional geometric hypothesis or weaker conclusion was introduced.

The accepted declaration header, from `theorem` through `:= by` including
the final newline, has SHA-256
`af235cf9b9aa27ba7702871936c5da0e43204e0629c0113ace4f48672589fd61`.
