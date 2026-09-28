import MorganTianLib.Ch03.RicciFlow.GeneralizedParabolicNeighborhood
import MorganTianLib.Ch03.RicciFlow.GeneralizedClosure

/-!
# Morgan--Tian Ch. 3 - parabolic-neighborhood consequences

The compatible time-slice embedding is unique on a closed slab once its
central time is interior.  This file records the resulting image bridge, and
the endpoint and central-slice witness-independence facts available for the
one-sided forward and backward parabolic slabs.  The latter slabs place their
central time at an endpoint, so the interior-time uniqueness theorem is not
silently applied to them.
-/

open scoped ContDiff ENNReal Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** A closed-slab equality of compatible embeddings gives equality of their
images.  In particular, this can be fed the output of
`eqOn_Icc_of_closure` or `eqOn_Icc_of_embedding` whenever their hypotheses
apply. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_eqOn_Icc
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (heq : Set.EqOn e₁.toFun e₂.toFun (C ×ˢ Icc a b)) :
    e₁.toCompatibleEmbedding.image n = e₂.toCompatibleEmbedding.image n := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    exact (heq hz).symm
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    exact heq hz

/-- **Math.** The closure-based closed-slab uniqueness theorem lifts directly
from equality of maps to equality of images. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_closure
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (ht : t ∈ Ioo a b)
    (hcont₁ : Continuous e₁.toFun) (hcont₂ : Continuous e₂.toFun)
    (hclosure : closure (C ×ˢ Ioo a b) = C ×ˢ Icc a b) :
    e₁.toCompatibleEmbedding.image n = e₂.toCompatibleEmbedding.image n := by
  apply GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_eqOn_Icc
    n e₁ e₂
  exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Icc_of_closure
    n e₁ e₂ ht hcont₁ hcont₂ hclosure

/-- **Math.** The closed-source version of closed-slab uniqueness lifts from
equality of maps to equality of images. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_isClosed
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (hab : a < b) (ht : t ∈ Ioo a b) (hC : IsClosed C)
    (hcont₁ : Continuous e₁.toFun) (hcont₂ : Continuous e₂.toFun) :
    e₁.toCompatibleEmbedding.image n = e₂.toCompatibleEmbedding.image n := by
  apply GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_closure
    n e₁ e₂ ht hcont₁ hcont₂
  rw [closure_prod_eq, hC.closure_eq, closure_Ioo hab.ne]

/-- **Math.** The restricted-source closed-slab uniqueness theorem lifts from
equality of maps to equality of images without a closedness assumption on the
spatial source. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_embedding
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (hab : a < b) (ht : t ∈ Ioo a b) :
    e₁.toCompatibleEmbedding.image n = e₂.toCompatibleEmbedding.image n := by
  apply GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_eqOn_Icc
    n e₁ e₂
  exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Icc_of_embedding
    n e₁ e₂ hab ht

/-- **Math.** Two forward witnesses agree at the central endpoint on every point of
their common metric-ball source. -/
theorem GeneralizedRicciFlow.ForwardParabolicNeighborhood.embedding_center_eq
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P₁ P₂ : F.ForwardParabolicNeighborhood n x r deltaT) :
    ∀ z ∈ F.timeSliceBall n x r,
      P₁.embedding.toFun (z, F.spaceTime.time x) =
        P₂.embedding.toFun (z, F.spaceTime.time x) := by
  intro z hz
  rw [P₁.embedding.center_eq z hz, P₂.embedding.center_eq z hz]

/-- **Math.** Two backward witnesses agree at the central endpoint on every point of
their common metric-ball source. -/
theorem GeneralizedRicciFlow.BackwardParabolicNeighborhood.embedding_center_eq
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P₁ P₂ : F.BackwardParabolicNeighborhood n x r deltaT) :
    ∀ z ∈ F.timeSliceBall n x r,
      P₁.embedding.toFun (z, F.spaceTime.time x) =
        P₂.embedding.toFun (z, F.spaceTime.time x) := by
  intro z hz
  rw [P₁.embedding.center_eq z hz, P₂.embedding.center_eq z hz]

/-- **Math.** The central slice of a forward parabolic-neighborhood image is
witness-independent. -/
theorem GeneralizedRicciFlow.ForwardParabolicNeighborhood.image_inter_centerSlice_eq
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P₁ P₂ : F.ForwardParabolicNeighborhood n x r deltaT) :
    P₁.image n ∩ F.spaceTime.timeSlice n (F.spaceTime.time x) =
      P₂.image n ∩ F.spaceTime.timeSlice n (F.spaceTime.time x) := by
  rw [P₁.image_inter_centerSlice n, P₂.image_inter_centerSlice n]

/-- **Math.** The central slice of a backward parabolic-neighborhood image is
witness-independent. -/
theorem GeneralizedRicciFlow.BackwardParabolicNeighborhood.image_inter_centerSlice_eq
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P₁ P₂ : F.BackwardParabolicNeighborhood n x r deltaT) :
    P₁.image n ∩ F.spaceTime.timeSlice n (F.spaceTime.time x) =
      P₂.image n ∩ F.spaceTime.timeSlice n (F.spaceTime.time x) := by
  rw [P₁.image_inter_centerSlice n, P₂.image_inter_centerSlice n]

/-- **Math.** If two forward witnesses satisfy a closed-slab equality supplied by an
applicable uniqueness theorem, their full images coincide. -/
theorem GeneralizedRicciFlow.ForwardParabolicNeighborhood.image_eq_of_eqOn_Icc
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P₁ P₂ : F.ForwardParabolicNeighborhood n x r deltaT)
    (heq : Set.EqOn P₁.embedding.toFun P₂.embedding.toFun
      (F.timeSliceBall n x r ×ˢ
        Icc (F.spaceTime.time x) (F.spaceTime.time x + deltaT))) :
    P₁.image n = P₂.image n := by
  change P₁.embedding.toCompatibleEmbedding.image n =
    P₂.embedding.toCompatibleEmbedding.image n
  exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_eqOn_Icc
    n P₁.embedding P₂.embedding heq

/-- **Math.** If two backward witnesses satisfy a closed-slab equality supplied by an
applicable uniqueness theorem, their full images coincide. -/
theorem GeneralizedRicciFlow.BackwardParabolicNeighborhood.image_eq_of_eqOn_Icc
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P₁ P₂ : F.BackwardParabolicNeighborhood n x r deltaT)
    (heq : Set.EqOn P₁.embedding.toFun P₂.embedding.toFun
      (F.timeSliceBall n x r ×ˢ
        Icc (F.spaceTime.time x - deltaT) (F.spaceTime.time x))) :
    P₁.image n = P₂.image n := by
  change P₁.embedding.toCompatibleEmbedding.image n =
    P₂.embedding.toCompatibleEmbedding.image n
  exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_eq_of_eqOn_Icc
    n P₁.embedding P₂.embedding heq

end MorganTianLib

end
