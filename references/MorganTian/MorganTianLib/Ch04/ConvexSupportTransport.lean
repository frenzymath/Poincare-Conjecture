import MorganTianLib.Ch04.ConvexSupport
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Isometric transport of convex support pairs

An isometry carrying one convex carrier onto another carries its contact
points and unit supporting normals onto support pairs of the second carrier.
Both support evaluations and derivative pairings are preserved.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set
open scoped InnerProductSpace

namespace MorganTianLib.ConvexSupportPair

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {Z : Set E} {W : Set F}

/-- **Math.** Transport the contact point and unit supporting normal by a
linear isometry preserving the carrier. -/
def map (e : E ≃ₗᵢ[ℝ] F) (he : e '' Z = W) (q : ConvexSupportPair Z) :
    ConvexSupportPair W := by
  refine ⟨(e q.1.1, e q.1.2), ?_, ?_, ?_⟩
  · rw [← he]
    exact mem_image_of_mem e q.2.1
  · exact (e.norm_map q.1.2).trans q.2.2.1
  · intro z hz
    rw [← he] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [← e.map_sub, e.inner_map_map]
    exact q.2.2.2 y hy

@[simp] theorem map_point (e : E ≃ₗᵢ[ℝ] F) (he : e '' Z = W)
    (q : ConvexSupportPair Z) : (map e he q).1.1 = e q.1.1 := rfl

@[simp] theorem map_normal (e : E ≃ₗᵢ[ℝ] F) (he : e '' Z = W)
    (q : ConvexSupportPair Z) : (map e he q).1.2 = e q.1.2 := rfl

/-- **Math.** The supporting functional has the same value on a transported
vector. -/
@[simp] theorem map_eval (e : E ≃ₗᵢ[ℝ] F) (he : e '' Z = W)
    (q : ConvexSupportPair Z) (v : E) :
    ⟪(map e he q).1.2, e v - (map e he q).1.1⟫_ℝ =
      ⟪q.1.2, v - q.1.1⟫_ℝ := by
  simp only [map_point, map_normal, ← e.map_sub, e.inner_map_map]

/-- **Math.** Pairing a support normal with a tensor derivative is invariant
under the same isometry. -/
@[simp] theorem map_inner (e : E ≃ₗᵢ[ℝ] F) (he : e '' Z = W)
    (q : ConvexSupportPair Z) (v : E) :
    ⟪(map e he q).1.2, e v⟫_ℝ = ⟪q.1.2, v⟫_ℝ :=
  e.inner_map_map q.1.2 v

end MorganTianLib.ConvexSupportPair

#print axioms MorganTianLib.ConvexSupportPair.map
#print axioms MorganTianLib.ConvexSupportPair.map_eval
#print axioms MorganTianLib.ConvexSupportPair.map_inner
