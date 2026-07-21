---
author: agent
created: '2026-07-16T19:47:17'
date: '2026-07-16T19:47:17'
updated: '2026-07-16T19:47:17'
---
ROUTE DECIDED + first step landed (run: manual session, 2026-07-16). This node is the keystone of §2.2: MeanValue.lean proves the strong maximum principle, maximum principle, Dirichlet uniqueness and Harnack FROM HasBallMeanValueProperty, but nothing discharges that hypothesis, so none of it applies to a harmonic function yet.

DEAD ENDS (verified, do not re-derive):
* mathlib has NO n-dim mean-value property. Loogle constant-search on InnerProductSpace.HarmonicOnNhd returns exactly 24 decls: 16 general-E algebra/regularity only, 8 with domain ℂ. Cross-searches (HarmonicOnNhd + average), (Laplacian.laplacian + average), ("ubharmonic") are all EMPTY. No subharmonic API in any dimension.
* HarmonicOnNhd.circleAverage_eq is 2D-only (proved via harmonic conjugate/holomorphy), is the CIRCLE not the BALL average, and its domain is ℂ not EuclideanSpace ℝ (Fin 2). Not generalizable.
* mathlib's divergence theorem is BOX-only (Set.Icc products). Box exhaustion of a ball CANNOT work: the staircase normal only takes the 2n coordinate directions and staircase surface measure does not converge to the sphere's (classical staircase paradox). Cube->ball radial map is bi-Lipschitz but NOT C¹.
* d/dr(sphere average)=0 IS the divergence theorem on the ball. Circular.
* CORRECTION, four scouts hit this: harmonicOnNhd_comp_CLE_iff is POST-composition on the CODOMAIN. It gives NO rotation invariance. Every mathlib Laplacian comp lemma is _comp_left. Δ(u∘R)=(Δu)∘R for R : E ≃ₗᵢ[ℝ] E does NOT exist; must be built (~120-150 lines) and must be stated for a linear ISOMETRY, not a general CLE. Route C′ does NOT need it.
* integral_fun_norm_addHaar is RADIAL-ONLY (f : ℝ → F). It cannot integrate a general u over a ball. Do not plan a route around it; the general polar tool is measurePreserving_homeomorphUnitSphereProd.

CHOSEN ROUTE (C′) — no surface measure, no polar coords, no Stokes:
mathlib's integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (Analysis/Calculus/LineDeriv/IntegrationByParts.lean:226) is a LINE-derivative IBP on any fin-dim real normed space with Haar measure. It imports only LineDeriv.Basic + IntegralEqImproper (NOT DivergenceTheorem/BoxIntegral) and is axiom-clean, so it does not smuggle in the missing theorem. Confirmed present at pin c5ea0035 and instantiates at EuclideanSpace/volume.
Plan: §0 Green's 2nd identity ∫u·Δw=∫(Δu)·w for w ∈ C_c^∞, tsupport w ⊆ U. Then take w := g(‖·-x‖²) with g solving the SQUARED-radius ODE 4σg''+2ng' = P(σ) for P smooth, supported in an ANNULUS [α,β] ⊂ (0,r²), with ZERO weighted mass ∫τ^{n/2-1}P = 0. Two tricks are load-bearing: P vanishing near 0 makes g locally CONSTANT at the centre (smoothness at x is free, dodges Whitney's radial-smoothness lemma), and zero mass makes g'≡0 past β (compact support = Newton's theorem, free from the ODE). Gives (★) ∫u·P(‖y-x‖²)=0 for every mass-zero annular P => all shell averages equal => u x by continuity => ball average.

LANDED THIS SESSION (commit 5da2207a11, EvansLib/Ch02/GreensIdentity.lean, axiom-clean, 0 sorries):
* integral_mul_partialDeriv_eq_neg : ∫ f·∂ᵢg = -∫ (∂ᵢf)·g
* integral_mul_partialDeriv_iterate_two_comm : ∫ f·∂ᵢ²g = ∫ (∂ᵢ²f)·g
Both are near-trivial because partialDeriv i f x is DEFEQ to fderiv ℝ f x (single i 1) (partialDeriv_apply := rfl), so the mathlib keystone applies as a bare term with no unfold/show/simp.

NEXT: §0b, the integrability/differentiability infra (the real bulk, ~150-250 lines). Set up ONE reusable helper first or it gets re-derived 8x: {U, (tsupport w)ᶜ} is an OPEN COVER of the whole space precisely because tsupport w ⊆ U, so every product is globally continuous even though u is junk outside U (x ∉ U => x ∉ tsupport w => w ≡ 0 near x => product ≡ 0 near x). Also need tsupport (partialDeriv i w) ⊆ tsupport w. Then §0d sum over i via laplacian_eq_sum_partialDeriv_iterate_two.

SCOPE — state honestly in the blueprint: this route provably CANNOT produce the SPHERE average ⨍_{∂B}u dS, the other half of Evans Thm 2. MeanValue.lean's header already pre-commits to ball-only. Mark the sphere half DEFERRED; do not claim Thm 2 entire. Keep (★) as a STANDALONE lemma: the sphere MVP hangs off the SAME (★) once polar coords are added (τ=s² turns zero-mass into ∫s^{n-1}P(s²)ds=0), and §2.4 (Euler-Poisson-Darboux) will need exactly that.