import EvansLib.Ch02.LaplaceMeanValueAux
import Mathlib.MeasureTheory.Integral.Average

/-!
# Evans, Ch. 2 §2.2.2 — Laplace mean-value identities at an arbitrary center

This file transports the centered weak radial ODE to an arbitrary center.  The
translation is kept explicit: the translated preimage domain is open, harmonicity
is transported through the Laplacian using the iterated Fréchet derivative formula,
and the centered closed-ball hypothesis is checked directly.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Translation of the domain and harmonicity -/

/-- The preimage of `U` under translation by `x`. -/
def translatedPreimage (x : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | x + z ∈ U}

/-- Translation preserves openness of a domain. -/
lemma isOpen_translatedPreimage {x : EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    IsOpen (translatedPreimage x U) := by
  exact hU.preimage (continuous_const.add continuous_id)

/-- Translation preserves local harmonicity. -/
lemma harmonicOnNhd_translatedPreimage
    {x : EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HarmonicOnNhd u U) :
    HarmonicOnNhd (fun z => u (x + z)) (translatedPreimage x U) := by
  intro z hz
  have hzU : x + z ∈ U := hz
  have hpoint := hu (x + z) hzU
  refine ⟨hpoint.1.comp z (by fun_prop), ?_⟩
  have hlap : Δ (fun w : EuclideanSpace ℝ (Fin n) => u (x + w)) =
      fun w => Δ u (x + w) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    funext w
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedFDeriv_comp_add_left]
  rw [hlap]
  convert hpoint.2.comp_tendsto
    (continuous_const.add continuous_id).continuousAt using 1
  · rfl
  · rfl

/-! ## Arbitrary-center spherical shells -/

/-- The integral of `u` on the unit sphere after radial scaling, centered at `x`. -/
def unitSphereRadialIntegralAt [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    u (x + r • (omega : EuclideanSpace ℝ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- The normalized average of `u` on the unit sphere after radial scaling,
centered at `x`. -/
def unitSphereRadialAverageAt [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  ⨍ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    u (x + r • (omega : EuclideanSpace ℝ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- The normalized spherical average is the spherical integral divided by
the total surface mass. -/
lemma unitSphereRadialAverageAt_eq [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    unitSphereRadialAverageAt u x r =
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹ *
        unitSphereRadialIntegralAt u x r := by
  rw [unitSphereRadialAverageAt, MeasureTheory.average_eq]
  rfl

/-! ## Radius-outer weak radial ODE at an arbitrary center -/

/-- The translated centered ball is contained in the translated preimage domain. -/
lemma closedBall_zero_subset_translatedPreimage
    {x : EuclideanSpace ℝ (Fin n)} {U : Set (EuclideanSpace ℝ (Fin n))}
    {R : ℝ} (hball : closedBall x R ⊆ U) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ translatedPreimage x U := by
  intro z hz
  apply hball
  rw [mem_closedBall, dist_self_add_left]
  rw [mem_closedBall, dist_zero_right] at hz
  exact hz

/-- **Arbitrary-center weak radial ODE.** If `u` is harmonic on an open set
containing `closedBall x R`, then every smooth compactly supported squared-radius
profile satisfies the radius-outer radial identity centered at `x`. -/
theorem integral_radius_unitSphereRadialIntegralAt_radialODE_eq_zero
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {x : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hR : 0 ≤ R) (hball : closedBall x R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg'' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ)
    (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
    ∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
        unitSphereRadialIntegralAt u x r *
          (4 * r ^ 2 * g'' (r ^ 2) + 2 * n * g' (r ^ 2)) = 0 := by
  let V := translatedPreimage x U
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun z => u (x + z)
  have hV : IsOpen V := isOpen_translatedPreimage hU
  have hv : HarmonicOnNhd v V := by
    simpa [V, v] using (harmonicOnNhd_translatedPreimage (x := x) hu)
  have hVball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ V :=
    closedBall_zero_subset_translatedPreimage hball
  have hcenter := integral_radius_unitSphereRadialIntegral_radialODE_eq_zero
    hV hv hR hVball hg hg' hg'' hzero
  simpa [unitSphereRadialIntegralAt, unitSphereRadialIntegral, V, v,
    add_assoc] using hcenter

end EvansLib
