import MorganTianLib.Ch04.ConvexInvariant
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Morgan--Tian Ch. 4 - transport of convex-set preservation

This file records the coordinate-change facts needed to pass Hamilton's
fiberwise reaction condition through an isometric bundle trivialization.  The
positive tangent cone is transported directly from its defining convergent
families, so the result applies without an interior or nonempty-carrier
assumption.
-/

open Filter Set
open scoped Topology NNReal

noncomputable section

namespace MorganTianLib

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Conjugate a vector field by a continuous linear equivalence. -/
def transportedVectorField (e : E ≃L[ℝ] G) (ψ : E → E) : G → G :=
  fun v => e (ψ (e.symm v))

/-- A continuous linear equivalence maps the positive tangent cone into the
positive tangent cone of the image set. -/
theorem mapsTo_posTangentConeAt_image
    (e : E ≃L[ℝ] G) {Z : Set E} {z : E} :
    MapsTo e (posTangentConeAt Z z)
      (posTangentConeAt (e '' Z) (e z)) := by
  intro v hv
  obtain ⟨α, l, hl, c, d, hd, hmem, hlim⟩ :=
    exists_fun_of_mem_tangentConeAt hv
  apply mem_tangentConeAt_of_seq l c (fun i => e (d i))
  · have hd' : Tendsto (e ∘ d) l (𝓝 (e 0)) :=
      e.continuous.continuousAt.tendsto.comp hd
    simpa [Function.comp_def] using hd'
  · filter_upwards [hmem] with i hi
    refine ⟨z + d i, hi, ?_⟩
    exact e.map_add z (d i)
  · have hlim' : Tendsto (e ∘ fun i => c i • d i) l (𝓝 (e v)) :=
      e.continuous.continuousAt.tendsto.comp hlim
    convert hlim' using 1
    funext i
    exact (map_smul e (c i : ℝ) (d i)).symm

/-- Tangent-cone preservation is invariant under continuous linear coordinate
changes. -/
theorem vectorFieldPreservesConvexSet_image
    (e : E ≃L[ℝ] G) {Z : Set E} {ψ : E → E}
    (hψ : vectorFieldPreservesConvexSet Z ψ) :
    vectorFieldPreservesConvexSet (e '' Z) (transportedVectorField e ψ) := by
  rintro _ ⟨z, hz, rfl⟩
  simpa [transportedVectorField] using
    mapsTo_posTangentConeAt_image e (hψ hz)

/-- Isometric conjugation preserves a Lipschitz constant. -/
theorem lipschitzWith_transportedVectorField
    (e : E ≃ₗᵢ[ℝ] G) {ψ : E → E} {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) :
    LipschitzWith K (transportedVectorField e.toContinuousLinearEquiv ψ) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change dist (e (ψ (e.symm v))) (e (ψ (e.symm w))) ≤ (K : ℝ) * dist v w
  rw [e.isometry.dist_eq]
  calc
    dist (ψ (e.symm v)) (ψ (e.symm w)) ≤
        (K : ℝ) * dist (e.symm v) (e.symm w) := hψ.dist_le_mul _ _
    _ = (K : ℝ) * dist v w := by rw [e.symm.isometry.dist_eq]

end MorganTianLib
