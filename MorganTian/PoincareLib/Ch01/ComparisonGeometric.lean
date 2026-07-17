import PoincareLib.Ch01.ConjugateUnit
import PoincareLib.Ch01.SectionalComparison
import PoincareLib.Ch01.RicciComparison

/-!
# Poincaré Ch. 1, §1.4 — the comparison theorems, with the conjugate-point hypothesis geometric

`sectional_curvature_comparison` and `ricci_curvature_comparison` state their conclusions under

  `∀ r ∈ (0, r₀), IsUnit (𝒥 r)`,

a hypothesis about the **matrix Jacobi field `𝒥` that they themselves bind existentially**. No
caller can supply such a thing: `𝒥` does not exist until the theorem has been applied. In that
form both flagship results were unusable in practice — a fact their own module docstrings record.

This file restates both with that hypothesis replaced by the *geometric* condition Morgan–Tian
actually assume,

  `∀ r ∈ (0, r₀), ¬ IsConjugatePointAt g γ r`   —   "`γ` has no conjugate point of `γ(0)`
  before `r₀`",

which is a statement about `γ` alone and can be checked by the caller. The bridge is
`isUnit_of_not_isConjugatePointAt`; the orthonormal-frame and column clauses it needs are exactly
the ones the two comparison theorems hand out.

## What this unlocks

`thm:sectional-curvature-comparison` (`SCC`) and `thm:ricci-curvature-comparison` become
theorems with checkable hypotheses, and with them the volume comparison
(`thm:bishop-gromov`, whose radial core `bishop_gromov_radial` is reached through
`ricci_curvature_comparison`'s density clauses). Together with `ExpLocalDiffeo`, which already
proves *absence* of conjugate points from an upper curvature bound
(`not_isConjugatePointAt_one_of_sectionalCurvatureAt_le`), the no-conjugate-point hypothesis is
itself now dischargeable from curvature, not merely assumed.

Blueprint: `thm:sectional-curvature-comparison`, `thm:ricci-curvature-comparison`,
`def:conjugate-point`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Riemannian Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-- **Math.** **The sectional-curvature comparison theorem** (`thm:sectional-curvature-comparison`,
`SCC`), with a geometric conjugate-point hypothesis.

Let `γ` be a unit-speed geodesic with `γ(0) = p`, along which every sectional curvature satisfies
`−k ≤ K(P)`, and which has **no conjugate point of `p` on `(0, r₀)`**. Then, in the velocity frame:

1. **metric half** — every Jacobi field `J` along `γ` with `J(0) = 0` satisfies
   `|J(r)|²_g ≤ sn_k(r)²·|∇J(0)|²_g` for `0 < r < r₀`. This is Morgan–Tian's
   `g_{ij}(r, θ) ≤ sn_k²(r)`, read on the coordinate fields `∂_{θⁱ}` of geodesic polar
   coordinates, which are precisely the Jacobi fields vanishing at `p`;
2. **shape-operator half** — `⟪A(r)Y, Y⟫ ≤ (cs_k(r)/sn_k(r))·‖Y‖²`, i.e. Morgan–Tian's
   `S_{ij}(r, θ) ≤ √k·ct_k(r)·g_{ij}(r, θ)`.

This is `sectional_curvature_comparison` with its `IsUnit (𝒥 r)` hypothesis discharged by
`isUnit_of_not_isConjugatePointAt`. -/
theorem sectional_curvature_comparison_of_not_conjugate {g : RiemannianMetric I M} {γ : ℝ → M}
    {a b B r₀ k : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1)
    (ha : a < 0) (hB0 : 0 < B) (hBb : B < b)
    (hk : 0 ≤ k) (hr₀ : r₀ ≤ B)
    (hnc : ∀ r ∈ Ioo (0 : ℝ) r₀, ¬ IsConjugatePointAt (I := I) g γ r)
    (hsec : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ v w : TangentSpace I (γ r),
      -k ≤ sectionalCurvatureAt g g.leviCivitaConnection (γ r) v w) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ (∀ t ∈ Icc a b,
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t)
        -- the **column clause**: `𝒥` is bound existentially, so without this the caller has no
        -- way to connect it to any actual Jacobi field, and every statement about `𝒥` below is
        -- a statement about an unidentifiable object. It is what lets `PolarMetricComparison`
        -- read `d(exp_p)` off `𝒥`.
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) B,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
        -- (1) `g_{ij}(r, θ) ≤ sn_k²(r)`
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
            ∀ r ∈ Ioo (0 : ℝ) r₀,
              g.metricInner (γ r) (J r : TangentSpace I (γ r)) (J r)
                ≤ snK k r ^ 2 * g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0))
        -- (2) `S_{ij}(r, θ) ≤ √k · ct_k(r) · g_{ij}(r, θ)`
        ∧ (∀ r ∈ Ioo (0 : ℝ) r₀, ∀ Y : 𝔼,
            ⟪shapeOp 𝒥 𝒥' r Y, Y⟫ ≤ csK k r / snK k r * ‖Y‖ ^ 2) := by
  classical
  obtain ⟨e, 𝒥, 𝒥', C, hRJ, hPar, horth, hvel, hcol, himp⟩ :=
    sectional_curvature_comparison (I := I) hab hgeo hγc hspeed ha hB0 hBb hk hr₀ hsec
  -- the geometric hypothesis discharges `IsUnit (𝒥 r)`
  have hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r) := fun r hr =>
    isUnit_of_not_isConjugatePointAt (I := I) hab hgeo hγc horth hcol ha hBb hr.1
      (hr.2.le.trans hr₀) (hnc r hr)
  obtain ⟨h1, h2⟩ := himp hunit
  exact ⟨e, 𝒥, 𝒥', C, hRJ, horth, hvel, hcol, h1, h2⟩

/-- **Math.** **The Ricci comparison theorem** (`thm:ricci-curvature-comparison`), with a
geometric conjugate-point hypothesis.

Let `γ` be a unit-speed geodesic with `Ric(γ', γ') ≥ −(n−1)k` along it and **no conjugate point
of `γ(0)` on `(0, r₀)`**. Then, with `λ = det 𝒥` the polar volume density:

1. `Tr(S)(r, θ) ≤ (n−1)·sn_k'(r)/sn_k(r)`;
2. `λ(r)/sn_k(r)^{n−1}` is non-increasing on `(0, r₀)` and tends to `1` as `r → 0⁺` — the
   monotone quotient that integrates to Bishop–Gromov;
3. `√(det g(r, θ)) ≤ sn_k(r)^{n−1}`.

This is `ricci_curvature_comparison` with its `IsUnit (𝒥 r)` hypothesis discharged by
`isUnit_of_not_isConjugatePointAt`. -/
theorem ricci_curvature_comparison_of_not_conjugate {g : RiemannianMetric I M} {γ : ℝ → M}
    {a b B r₀ k : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1)
    (ha : a < 0) (hB0 : 0 < B) (hBb : B < b)
    (hk : 0 ≤ k) (hr₀ : r₀ ≤ B) (hdim : 2 ≤ finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hnc : ∀ r ∈ Ioo (0 : ℝ) r₀, ¬ IsConjugatePointAt (I := I) g γ r)
    (hric : ∀ t ∈ Icc (0 : ℝ) B,
      -(((finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC (γ t)
            (mfderivVelocity (I := I) (E := E) γ t)
            (mfderivVelocity (I := I) (E := E) γ t)) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ (∀ t ∈ Icc a b,
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t)
        -- the **column clause** — see `sectional_curvature_comparison_of_not_conjugate`. Without
        -- it the density clauses below speak about an existentially bound `𝒥` that the caller
        -- cannot identify with anything geometric, so the volume comparison could never be
        -- transported to `exp_p`. This is what `thm:bishop-gromov` will consume.
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) B,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
        -- (1) `Tr(S) ≤ (n−1)·sn_k'/sn_k`
        ∧ (∀ r ∈ Ioo (0 : ℝ) r₀,
            LinearMap.trace ℝ 𝔼 ↑(shapeOp 𝒥 𝒥' r) - 1 / r
              ≤ ((finrank ℝ E : ℝ) - 1) * (csK k r / snK k r))
        -- (2) the relative volume density is non-increasing, with limit `1` at `0⁺`
        ∧ AntitoneOn (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1)) (Ioo 0 r₀)
        ∧ Tendsto (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1))
            (𝓝[>] (0 : ℝ)) (𝓝 1)
        -- (3) the volume element `√(det g) ≤ sn_k^{n−1}`
        ∧ (∀ r ∈ Ioo (0 : ℝ) r₀,
            polarDensity 𝒥 r ≤ snK k r ^ (finrank ℝ E - 1)) := by
  classical
  obtain ⟨e, 𝒥, 𝒥', C, hRJ, horth, hvel, hcol, himp⟩ :=
    ricci_curvature_comparison (I := I) hab hgeo hγc hspeed ha hB0 hBb hk hr₀ hdim hLC hric
  have hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r) := fun r hr =>
    isUnit_of_not_isConjugatePointAt (I := I) hab hgeo hγc horth hcol ha hBb hr.1
      (hr.2.le.trans hr₀) (hnc r hr)
  obtain ⟨h1, h2, h3, h4⟩ := himp hunit
  exact ⟨e, 𝒥, 𝒥', C, hRJ, horth, hvel, hcol, h1, h2, h3, h4⟩

end PoincareLib

end
