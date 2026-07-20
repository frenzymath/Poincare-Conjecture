import MorganTianLib.Ch01.RadialJacobiVelocity
import MorganTianLib.Ch01.FrameRadialBridge

/-!
# Morgan–Tian Ch. 1, §1.4 — the sectional curvature comparison theorem

This file assembles `thm:sectional-curvature-comparison` (`SCC`) on the manifold, in the
same shape as the manifold-level `MorganTianLib.ricci_curvature_comparison`: along a
**unit-speed** geodesic `γ` issuing from `p = γ(0)` that is free of conjugate points on
`(0, r₀)`, and along which **every** sectional curvature satisfies `K(P) ≥ −k` (`k ≥ 0`),
both halves of Morgan–Tian's conclusion hold:

* **the metric half** — every Jacobi field `J` along `γ` with `J(0) = 0` satisfies
  `|J(r)|²_g ≤ sn_k(r)² · |∇J(0)|²_g` on `(0, r₀)`;
* **the shape-operator half** — the shape operator `A(r) = 𝒥'(r)𝒥(r)⁻¹` of the geodesic
  spheres satisfies `⟪A(r)Y, Y⟫ ≤ (sn_k'(r)/sn_k(r))·‖Y‖² = √k·ct_k(r)·‖Y‖²`.

## What is proved, and what is *not* claimed

Morgan–Tian state `SCC` in **Gaussian polar coordinates**: `g_{ij}(r, θ) ≤ sn_k²(r)` and
`S_{ij}(r, θ) ≤ √k·ct_k(r)·g_{ij}(r, θ)`, as inequalities of matrices/bilinear forms.

What is proved here is the **parallel velocity frame / Jacobi field formulation** of those
two statements: the estimates are on the matrix Jacobi field `𝒥` along `γ` and on the
Jacobi fields vanishing at the centre.  The two formulations are equivalent *only* through
the polar-coordinate reading — the coordinate fields `∂_{θⁱ}` of geodesic polar coordinates
**are** exactly the Jacobi fields along `γ` vanishing at `p`, and `g_{ij}`, `S_{ij}` are
their Gram matrix and its radial derivative (blueprint `lem:geodesic-polar-form`(1)
together with `lem:exponential-differential-jacobi`).  **`lem:geodesic-polar-form` is not
yet formalized**, so the identification of the quantities below with the literal
coordinate matrices `g_{ij}(r, θ)`, `S_{ij}(r, θ)` is *not* part of this file and is not
claimed by it.  What is claimed is exactly what the statements say.

## How it is assembled

Nothing here is new mathematics; the two halves already exist:

* the metric half is `metricInner_jacobi_le_snK_of_sectionalCurvature`
  (`FrameRadialBridge`), which is the abstract Riccati comparison
  `RadialComparison.norm_jacobi_sq_le` transported through the frame isometry;
* the shape-operator half is `RadialComparison.shapeOp_inner_le`, stated in the frame; its
  frame curvature hypothesis `−k‖X‖² ≤ ⟪ℛ(r)X, X⟫` is supplied from the manifold
  sectional-curvature hypothesis by `curvatureFormAt_jacobi_le_of_sectionalCurvatureAt_ge`
  together with `inner_frameCurvOp_self` and `metricInner_frameLift` — the frame lift is a
  `g`-isometry, and `⟪ℛ(r)x, x⟫` is minus the unnormalized sectional curvature of the plane
  spanned by the lift of `x` and `γ'`.

Both are fed the velocity-frame radial Jacobi datum of
`exists_isRadialJacobi_of_geodesic_velocity`.

## The conjugate-point hypothesis

Absence of conjugate points on `(0, r₀)` enters as `IsUnit (𝒥 r)`.  Morgan–Tian derive it
from *minimality* of `γ` via `prop:minimal-geodesic-no-conjugate`; that node is not yet
formalized, so — exactly as in `ricci_curvature_comparison` — it is carried here as an
explicit hypothesis on the conclusion.

Blueprint: `thm:sectional-curvature-comparison` (`SCC`), `lem:radial-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Riemannian Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-- **Math.** **The sectional curvature comparison theorem** (`thm:sectional-curvature-comparison`,
`SCC`), in the parallel velocity frame.

Fix `k ≥ 0` and let `γ : [a,b] → M` be a **unit-speed** geodesic with `γ(0) = p`, free of
conjugate points on `(0, r₀)`, along which **every** sectional curvature satisfies
`−k ≤ K(P)`.  Then, in the velocity frame `e` (a parallel `g`-orthonormal frame with
`e₀ = γ'`), with `𝒥` the matrix Jacobi field and `A = 𝒥'𝒥⁻¹` the shape operator of the
geodesic spheres:

1. **metric half** — every Jacobi field `J` along `γ` with `J(0) = 0` satisfies
   `|J(r)|²_g ≤ sn_k(r)² · |∇J(0)|²_g` for `0 < r < r₀`.  This is Morgan–Tian's
   `g_{ij}(r, θ) ≤ sn_k²(r)`, read on the coordinate fields `∂_{θⁱ}` (which are precisely
   the Jacobi fields vanishing at `p`);
2. **shape-operator half** — `⟪A(r)Y, Y⟫ ≤ (cs_k(r)/sn_k(r))·‖Y‖²` for `0 < r < r₀` and
   every `Y`.  This is Morgan–Tian's `S_{ij}(r, θ) ≤ √k·ct_k(r)·g_{ij}(r, θ)`.

The identification of (1) and (2) with the *literal* polar-coordinate matrices `g_{ij}`,
`S_{ij}` needs `lem:geodesic-polar-form`, which is not yet formalized; see the module
docstring.  As in `ricci_curvature_comparison`, the absence of conjugate points is carried
as the hypothesis `IsUnit (𝒥 r)` on `(0, r₀)`.

Unlike `ricci_curvature_comparison`, no dimension hypothesis `2 ≤ n` and no explicit
Levi-Civita hypothesis are needed: the sectional bound is a *pointwise, full-dimensional*
hypothesis (no `n − 1` trace normalization enters), and the metric compatibility of
`g.leviCivitaConnection` is derived internally by
`curvatureFormAt_jacobi_le_of_sectionalCurvatureAt_ge`.

Blueprint: `thm:sectional-curvature-comparison`. -/
theorem sectional_curvature_comparison {g : RiemannianMetric I M} {γ : ℝ → M}
    {a b B r₀ k : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1)
    (ha : a < 0) (hB0 : 0 < B) (hBb : B < b)
    (hk : 0 ≤ k) (hr₀ : r₀ ≤ B)
    (hsec : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ v w : TangentSpace I (γ r),
      -k ≤ sectionalCurvatureAt g g.leviCivitaConnection (γ r) v w) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C
        -- the frame `e` is parallel along `γ` and `g`-orthonormal, with `e₀ = γ'`:
        -- without these two clauses the shape-operator estimate (2) below would be a
        -- statement about `𝒥` in an *unspecified* basis, hence unusable downstream.
        ∧ (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ (∀ t ∈ Icc a b,
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t)
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) B,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
        ∧ ((∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r)) →
            -- (1) the metric half: `|J(r)|²_g ≤ sn_k²(r)·|∇J(0)|²_g`, i.e. `g_{ij} ≤ sn_k²`
            (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
              ∀ r ∈ Ioo (0 : ℝ) r₀,
                g.metricInner (γ r) (J r : TangentSpace I (γ r)) (J r)
                  ≤ snK k r ^ 2 * g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0))
            -- (2) the shape-operator half: `⟪A(r)Y, Y⟫ ≤ (cs_k/sn_k)(r)·‖Y‖²`
            ∧ (∀ r ∈ Ioo (0 : ℝ) r₀, ∀ Y : 𝔼,
                ⟪shapeOp 𝒥 𝒥' r Y, Y⟫ ≤ csK k r / snK k r * ‖Y‖ ^ 2)) := by
  classical
  -- the coefficient space is nontrivial: `n = finrank ℝ E ≥ 1` by the `NeZero` instance
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne _))
  haveI : Nontrivial 𝔼 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin (Module.finrank ℝ E))›
    refine nontrivial_of_ne (𝔟 i : 𝔼) 0 fun h => ?_
    have h1 : ‖(𝔟 i : 𝔼)‖ = 1 :=
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).orthonormal.1 i
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  -- the velocity-frame radial Jacobi datum
  obtain ⟨e, 𝒥, 𝒥', C, hPar, horth, hvel, hRJ, hrad, hcol⟩ :=
    exists_isRadialJacobi_of_geodesic_velocity (I := I) hab hgeo hγc hspeed ha hB0.le hBb
  refine ⟨e, 𝒥, 𝒥', C, hRJ, hPar, horth, hvel, hcol, fun hunit => ?_⟩
  have hIcc : Icc (0 : ℝ) B ⊆ Icc a b := Icc_subset_Icc ha.le hBb.le
  -- `(0, r₀) ⊆ [0, B] ⊆ [a, b]`
  have hsub : ∀ r ∈ Ioo (0 : ℝ) r₀, r ∈ Icc (0 : ℝ) B := fun r hr =>
    ⟨hr.1.le, hr.2.le.trans hr₀⟩
  -- the unit-speed hypothesis, restricted to `(0, r₀)`
  have hspeed' : ∀ r ∈ Ioo (0 : ℝ) r₀,
      g.metricInner (γ r) (mfderivVelocity (I := I) (E := E) γ r)
        (mfderivVelocity (I := I) (E := E) γ r) = 1 :=
    fun r hr => hspeed r (hIcc (hsub r hr))
  refine ⟨fun J DJ hJac hJ0 => ?_, ?_⟩
  · -- (1) the metric half is already proved on the manifold
    exact metricInner_jacobi_le_snK_of_sectionalCurvature (I := I) hRJ hB0 horth hIcc
      (hcol J DJ hJac hJ0) hk hr₀ hunit hspeed' hsec
  · -- (2) the shape-operator half: convert the sectional hypothesis into the frame
    have hcurv : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ x : 𝔼,
        -(k * ‖x‖ ^ 2) ≤ ⟪frameCurvOp (I := I) g γ e r x, x⟫ := by
      intro r hr x
      have hnorm : g.metricInner (γ r) (frameLift (I := I) g γ e r x)
          (frameLift (I := I) g γ e r x) = ‖x‖ ^ 2 := by
        rw [metricInner_frameLift (I := I) (horth r (hIcc (hsub r hr))) x x,
          real_inner_self_eq_norm_sq]
      rw [inner_frameCurvOp_self (I := I) g γ e r x, neg_le_neg_iff, ← hnorm]
      exact curvatureFormAt_jacobi_le_of_sectionalCurvatureAt_ge (I := I) g (γ r) hk
        (hsec r hr) (hspeed' r hr) _
    exact shapeOp_inner_le hRJ hB0 hk hr₀ hunit hcurv

end MorganTianLib

end
