import PoincareLib.Ch01.RadialJacobiVelocity
import PoincareLib.Ch01.VolumeComparison

/-!
# Morgan–Tian Ch. 1, §1.4 — the Ricci curvature comparison theorem

This file proves `thm:ricci-curvature-comparison` on the manifold: along a unit-speed
geodesic `γ` issuing from `p` that is free of conjugate points on `(0, r₀)`, and along
which `Ric ≥ −(n−1)k`, both halves of Morgan–Tian's conclusion hold:

* **the trace of the shape operator** (the Laplacian of the distance function):

    `Tr(S)(r) = Tr A(r) − 1/r ≤ (n − 1)·sn_k'(r)/sn_k(r)`,

* **the volume element**:

    `√(det g(r,θ)) = det 𝒥(r)/r ≤ sn_k(r)^{n−1}`,

and the *relative* volume density `(det 𝒥(r)/r)/sn_k(r)^{n−1}` is non-increasing with
limit `1` at `r = 0⁺` — which is exactly the pointwise input to Bishop–Gromov
(`thm:bishop-gromov`).

## How it is assembled

Everything happens in the **velocity frame** along `γ` (`RadialJacobiVelocity.lean`), a
parallel `g`-orthonormal frame whose `0`-th vector is `γ'`. In that frame:

* the matrix Jacobi field `𝒥` satisfies `IsRadialJacobi`, and its radial column is
  `𝒥(r)b₀ = r·b₀` — so `det 𝒥(r)` carries a spurious factor `r`, removed by
  `polarDensity 𝒥 r = det 𝒥(r)/r`;
* the frame Jacobi operator annihilates the radial direction,
  `ℛ(t) b₀ = 0` (`frameCurvOp_radial_eq_zero`), because `R(γ', γ')γ' = 0`;
* its trace is exactly the Ricci curvature in the radial direction,
  `Tr ℛ(t) = Ric(γ'(t), γ'(t))` (`trace_frameCurvOp_eq_ricciAt`).

The last two facts are what convert Morgan–Tian's geometric hypothesis
`Ric ≥ −(n−1)k` into the algebraic hypothesis of the *sharp* trace Riccati comparison
`trace_shapeOp_le_perp`, whose constant is `n − 1` and not `n`.

## The conjugate-point hypothesis

Absence of conjugate points on `(0, r₀)` enters as `IsUnit (𝒥 r)` — the matrix Jacobi
field is invertible. Morgan–Tian derive it from *minimality* of `γ` via
`prop:minimal-geodesic-no-conjugate`; that node is not yet formalized, so it is carried
here as an explicit hypothesis, exactly as in `lem:volume-element-comparison`, which
also hypothesises "free of conjugate points on `[0, r₀)`".

Blueprint: `thm:ricci-curvature-comparison`, `lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Riemannian Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-- **Math.** The coefficient space of the parallel frame has the same dimension as the
model space: `dim (EuclideanSpace ℝ (Fin n)) = n`. -/
theorem finrank_coeffSpace :
    finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E))) = finrank ℝ E := by
  simp

/-- **Math.** **The Ricci curvature comparison theorem** (`thm:ricci-curvature-comparison`).

Let `γ : [a,b] → M` be a **unit-speed** geodesic with `γ(0) = p`, free of conjugate points
on `(0, r₀)`, and suppose `Ric(γ', γ') ≥ −(n−1)k` along it (`k ≥ 0`, `n = dim M ≥ 2`).
Then, in the velocity frame, with `𝒥` the matrix Jacobi field and `A = 𝒥'𝒥⁻¹` the shape
operator:

1. `Tr A(r) − 1/r ≤ (n−1)·cs_k(r)/sn_k(r)` — Morgan–Tian's `Tr(S) ≤ (n−1) sn_k'/sn_k`;
2. `r ↦ (det 𝒥(r)/r)/sn_k(r)^{n−1}` is non-increasing on `(0, r₀)` with limit `1` at `0⁺`;
3. `det 𝒥(r)/r ≤ sn_k(r)^{n−1}` — Morgan–Tian's `√(det g(r,θ)) ≤ sn_k^{n−1}(r)`.

Item (2) is the pointwise monotonicity that integrates, via the coarea formula, to the
Bishop–Gromov relative volume comparison `thm:bishop-gromov`.

Blueprint: `thm:ricci-curvature-comparison`. -/
theorem ricci_curvature_comparison {g : RiemannianMetric I M} {γ : ℝ → M}
    {a b B r₀ k : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1)
    (ha : a < 0) (hB0 : 0 < B) (hBb : B < b)
    (hk : 0 ≤ k) (hr₀ : r₀ ≤ B) (hdim : 2 ≤ finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ t ∈ Icc (0 : ℝ) B,
      -(((finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC (γ t)
            (mfderivVelocity (I := I) (E := E) γ t)
            (mfderivVelocity (I := I) (E := E) γ t)) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C
        -- the frame is `g`-orthonormal: without this clause the `IsUnit (𝒥 r)` hypothesis below
        -- could not be discharged geometrically (`isUnit_of_not_isConjugatePointAt` needs it)
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ (∀ t ∈ Icc a b,
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t)
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) B,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
        ∧ ((∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r)) →
            -- (1) the trace of the shape operator: `Tr(S) ≤ (n−1)·sn_k'/sn_k`
            (∀ r ∈ Ioo (0 : ℝ) r₀,
              LinearMap.trace ℝ 𝔼 ↑(shapeOp 𝒥 𝒥' r) - 1 / r
                ≤ ((finrank ℝ E : ℝ) - 1) * (csK k r / snK k r))
            -- (2) relative volume density is non-increasing, with limit 1 at 0⁺
            ∧ AntitoneOn (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1))
                (Ioo 0 r₀)
            ∧ Tendsto (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1))
                (𝓝[>] (0 : ℝ)) (𝓝 1)
            -- (3) the volume element: `√(det g) ≤ sn_k^{n−1}`
            ∧ (∀ r ∈ Ioo (0 : ℝ) r₀,
                polarDensity 𝒥 r ≤ snK k r ^ (finrank ℝ E - 1))) := by
  classical
  -- the velocity-frame radial Jacobi datum
  obtain ⟨e, 𝒥, 𝒥', C, hPar, horth, hvel, hRJ, hrad, hcol⟩ :=
    exists_isRadialJacobi_of_geodesic_velocity (I := I) hab hgeo hγc hspeed ha hB0.le hBb
  refine ⟨e, 𝒥, 𝒥', C, hRJ, horth, hvel, hcol, fun hunit => ?_⟩
  -- the dimension of the coefficient space
  have hdim' : 2 ≤ finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
    rw [finrank_coeffSpace (E := E)]; exact hdim
  -- the radial direction of the coefficient space is a unit vector
  have hu : ‖(𝔟 0 : 𝔼)‖ = 1 := by
    simp
  -- `Ric ≥ −(n−1)k` becomes `Tr ℛ ≥ −(n−1)k` in the frame
  have hIcc : Icc (0 : ℝ) B ⊆ Icc a b := Icc_subset_Icc ha.le hBb.le
  have hric' : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E))) : ℝ)) - 1) * k
        ≤ LinearMap.trace ℝ 𝔼 ↑(frameCurvOp (I := I) g γ e r) := by
    intro r hr
    have hrB : r ∈ Icc (0 : ℝ) B := ⟨hr.1.le, le_trans hr.2.le hr₀⟩
    have := le_trace_frameCurvOp_of_ricci_ge (I := I) (g := g) (γ := γ) (e := e) (t := r)
      (k := k) hLC (fun i j => horth r (hIcc hrB) i j) (hric r hrB)
    rw [finrank_coeffSpace (E := E)]
    linarith [this]
  -- the sharp trace comparison wants the hypothesis in `-(( n - 1) * k)` shape
  have hric'' : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E))) : ℝ) - 1) * k)
        ≤ LinearMap.trace ℝ 𝔼 ↑(frameCurvOp (I := I) g γ e r) := by
    intro r hr; have := hric' r hr; linarith [this]
  have hr₀b : r₀ ≤ B := hr₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the sharp trace bound on the shape operator
    intro r hr
    have := trace_shapeOp_le_perp hRJ hB0 hk hr₀b hdim' hu hrad hunit hric'' r hr
    rw [finrank_coeffSpace (E := E)] at this
    exact this
  · -- (2a) monotonicity of the relative volume density
    have := antitoneOn_polarDensity_div_snK_pow hRJ hB0 hk hr₀b hdim' hu hrad hunit hric''
    rw [finrank_coeffSpace (E := E)] at this
    exact this
  · -- (2b) the limit at the centre
    have := tendsto_polarDensity_div_snK_pow (k := k) hRJ hB0 hk hdim'
    rw [finrank_coeffSpace (E := E)] at this
    exact this
  · -- (3) the volume element comparison
    have := polarDensity_le_snK_pow hRJ hB0 hk hr₀b hdim' hu hrad hunit hric''
    rw [finrank_coeffSpace (E := E)] at this
    exact this

end PoincareLib
