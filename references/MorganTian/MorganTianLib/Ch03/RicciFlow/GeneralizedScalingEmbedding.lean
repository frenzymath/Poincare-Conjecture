import MorganTianLib.Ch03.RicciFlow.GeneralizedScalingNeighborhood
import MorganTianLib.Ch03.RicciFlow.GeneralizedClosure

/-!
# Morgan--Tian Ch. 3 - affine transport of compatible flow neighborhoods

Positive affine changes of time preserve compatible space-time embeddings after
reparameterizing their time variable.  Consequently, existing forward and
backward parabolic neighborhoods transport to the parabolically rescaled
generalized Ricci flow with the expected square-root spatial scale and linear
time scale.
-/

open scoped ContDiff ENNReal Manifold Topology Bundle
open Set

noncomputable section


namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** A compatible embedding transports through a positive affine
change of time.  Its ambient image is unchanged; only the parameter interval
and time vector are rescaled. -/
noncomputable def GeneralizedSpaceTime.CompatibleEmbedding.affineTimeChange
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (S.affineTimeChange n Q hQ a).CompatibleEmbedding n C
      (parabolicTimeOrderIso Q hQ a '' J) where
  toFun := e.affineTimeReparam n Q hQ a
  isEmbedding :=
    GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam_isEmbedding
      n e Q hQ a
  time_eq := by
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    simpa only [GeneralizedSpaceTime.affineTimeChange_time] using
      e.affineTimeReparam_time n Q hQ a hx hs
  isIntegralCurveOn := by
    intro x hx
    simpa only [GeneralizedSpaceTime.affineTimeChange_timeVector,
      GeneralizedSpaceTime.scaledTimeVector_apply,
      smul_apply] using
      e.isIntegralCurveOn_affineTimeReparam n Q hQ a hx

@[simp]
theorem GeneralizedSpaceTime.CompatibleEmbedding.affineTimeChange_toFun
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (z : N × ℝ) :
    (e.affineTimeChange n Q hQ a).toFun z =
      e.affineTimeReparam n Q hQ a z :=
  rfl

/-- **Math.** Transporting a compatible embedding by affine time change does
not change its subset of space-time. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.affineTimeChange_image
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (e.affineTimeChange n Q hQ a).image n = e.image n := by
  exact e.affineTimeReparam_image n Q hQ a

/-- **Math.** A based compatible embedding transports through affine time
change, retaining the same spatial source and the same central points. -/
noncomputable def
    GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.affineTimeChange
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t : ℝ} {J : Set ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t J)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (S.affineTimeChange n Q hQ a).CompatibleTimeSliceEmbedding n C
      (parabolicTimeOrderIso Q hQ a t)
      (parabolicTimeOrderIso Q hQ a '' J) where
  toCompatibleEmbedding := e.toCompatibleEmbedding.affineTimeChange n Q hQ a
  center_mem := ⟨t, e.center_mem, rfl⟩
  source_subset := by
    intro x hx
    apply (S.affineTimeChange n Q hQ a).mem_timeSlice_iff.mpr
    rw [GeneralizedSpaceTime.affineTimeChange_time]
    have hxt := (S.mem_timeSlice_iff (n := n)).mp (e.source_subset hx)
    simp only [parabolicTimeOrderIso_apply, hxt]
  center_eq := by
    intro x hx
    change e.affineTimeReparam n Q hQ a
        (x, parabolicTimeOrderIso Q hQ a t) = x
    rw [e.toCompatibleEmbedding.affineTimeReparam_parabolicTimeOrderIso
      Q hQ a x t]
    exact e.center_eq x hx

@[simp]
theorem
    GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.affineTimeChange_image
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t : ℝ} {J : Set ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t J)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (e.affineTimeChange n Q hQ a).toCompatibleEmbedding.image n =
      e.toCompatibleEmbedding.image n := by
  exact e.toCompatibleEmbedding.affineTimeChange_image n Q hQ a

/- The image is unchanged by the explicit dependent transports used below.
This is stated with named intermediate terms so the proof does not rely on
unfolding an opaque `Eq.rec` motive. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_of_casts
    {S₁ S₂ : GeneralizedSpaceTime n (N := N)}
    {C₁ C₂ : Set N} {t₁ t₂ : ℝ} {J₁ J₂ : Set ℝ}
    (hS : S₁ = S₂) (hC : C₁ = C₂) (ht : t₁ = t₂) (hJ : J₁ = J₂)
    (e : S₁.CompatibleTimeSliceEmbedding n C₁ t₁ J₁) :
    let e₁ : S₂.CompatibleTimeSliceEmbedding n C₁ t₁ J₁ := hS ▸ e
    let e₂ : S₂.CompatibleTimeSliceEmbedding n C₂ t₁ J₁ := hC ▸ e₁
    let e₃ : S₂.CompatibleTimeSliceEmbedding n C₂ t₂ J₁ := ht ▸ e₂
    let e₄ : S₂.CompatibleTimeSliceEmbedding n C₂ t₂ J₂ := hJ ▸ e₃
    e₄.toCompatibleEmbedding.image n = e.toCompatibleEmbedding.image n := by
  dsimp
  cases hS
  cases hC
  cases ht
  cases hJ
  rfl

/-- **Math.** A forward parabolic neighborhood rescales from radius `r` and
time length `deltaT` to radius `sqrt Q * r` and time length `Q * deltaT`. -/
noncomputable def
    GeneralizedRicciFlow.ForwardParabolicNeighborhood.affineTimeChange
    [NeZero n] {F : GeneralizedRicciFlow n (N := N)}
    {x : N} {r deltaT : ℝ}
    (P : F.ForwardParabolicNeighborhood n x r deltaT)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (F.affineTimeChange n Q hQ a).ForwardParabolicNeighborhood n x
      (Real.sqrt Q * r) (Q * deltaT) where
  radius_pos := mul_pos (Real.sqrt_pos.2 hQ) P.radius_pos
  timeLength_pos := mul_pos hQ P.timeLength_pos
  embedding := by
    have hS :
        (F.affineTimeChange n Q hQ a).spaceTime =
          F.spaceTime.affineTimeChange n Q hQ a := by
      rfl
    have e₀ := P.embedding.affineTimeChange n Q hQ a
    have hball := F.timeSliceBall_affineTimeChange n Q hQ a x r
    have htime :
        (F.affineTimeChange n Q hQ a).spaceTime.time x =
          parabolicTimeOrderIso Q hQ a (F.spaceTime.time x) := by
      simp only [GeneralizedRicciFlow.affineTimeChange,
        GeneralizedSpaceTime.affineTimeChange_time,
        parabolicTimeOrderIso_apply]
    have hinterval :
        parabolicTimeOrderIso Q hQ a ''
            Icc (F.spaceTime.time x) (F.spaceTime.time x + deltaT) =
            Icc (parabolicTimeOrderIso Q hQ a (F.spaceTime.time x))
              (parabolicTimeOrderIso Q hQ a (F.spaceTime.time x) + Q * deltaT) := by
      rw [parabolicTimeOrderIso_image_Icc]
      congr 1
      simp only [parabolicTimeOrderIso_apply]
      ring
    have e₁ :
        (F.affineTimeChange n Q hQ a).spaceTime.CompatibleTimeSliceEmbedding n
          (F.timeSliceBall n x r)
          (parabolicTimeOrderIso Q hQ a (F.spaceTime.time x))
          (parabolicTimeOrderIso Q hQ a ''
            Icc (F.spaceTime.time x) (F.spaceTime.time x + deltaT)) := by
      exact hS.symm ▸ e₀
    have e₂ := hball.symm ▸ e₁
    have e₃ := htime.symm ▸ e₂
    exact hinterval ▸ e₃

/-- **Math.** A backward parabolic neighborhood rescales from radius `r` and
time length `deltaT` to radius `sqrt Q * r` and time length `Q * deltaT`. -/
noncomputable def
    GeneralizedRicciFlow.BackwardParabolicNeighborhood.affineTimeChange
    [NeZero n] {F : GeneralizedRicciFlow n (N := N)}
    {x : N} {r deltaT : ℝ}
    (P : F.BackwardParabolicNeighborhood n x r deltaT)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (F.affineTimeChange n Q hQ a).BackwardParabolicNeighborhood n x
      (Real.sqrt Q * r) (Q * deltaT) where
  radius_pos := mul_pos (Real.sqrt_pos.2 hQ) P.radius_pos
  timeLength_pos := mul_pos hQ P.timeLength_pos
  embedding := by
    have hS :
        (F.affineTimeChange n Q hQ a).spaceTime =
          F.spaceTime.affineTimeChange n Q hQ a := by
      rfl
    have e₀ := P.embedding.affineTimeChange n Q hQ a
    have hball := F.timeSliceBall_affineTimeChange n Q hQ a x r
    have htime :
        (F.affineTimeChange n Q hQ a).spaceTime.time x =
          parabolicTimeOrderIso Q hQ a (F.spaceTime.time x) := by
      simp only [GeneralizedRicciFlow.affineTimeChange,
        GeneralizedSpaceTime.affineTimeChange_time,
        parabolicTimeOrderIso_apply]
    have hinterval :
        parabolicTimeOrderIso Q hQ a ''
            Icc (F.spaceTime.time x - deltaT) (F.spaceTime.time x) =
            Icc (parabolicTimeOrderIso Q hQ a (F.spaceTime.time x) - Q * deltaT)
              (parabolicTimeOrderIso Q hQ a (F.spaceTime.time x)) := by
      rw [parabolicTimeOrderIso_image_Icc]
      congr 1
      simp only [parabolicTimeOrderIso_apply]
      ring
    have e₁ :
        (F.affineTimeChange n Q hQ a).spaceTime.CompatibleTimeSliceEmbedding n
          (F.timeSliceBall n x r)
          (parabolicTimeOrderIso Q hQ a (F.spaceTime.time x))
          (parabolicTimeOrderIso Q hQ a ''
            Icc (F.spaceTime.time x - deltaT) (F.spaceTime.time x)) := by
      exact hS.symm ▸ e₀
    have e₂ := hball.symm ▸ e₁
    have e₃ := htime.symm ▸ e₂
    exact hinterval ▸ e₃

/-- **Math.** The rescaled forward parabolic-neighborhood witness has exactly
the same ambient image as the original witness. -/
theorem
    GeneralizedRicciFlow.ForwardParabolicNeighborhood.affineTimeChange_image
    [NeZero n] {F : GeneralizedRicciFlow n (N := N)}
    {x : N} {r deltaT : ℝ}
    (P : F.ForwardParabolicNeighborhood n x r deltaT)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (P.affineTimeChange n Q hQ a).image n = P.image n := by
  change (P.affineTimeChange n Q hQ a).embedding.toCompatibleEmbedding.image n =
    P.embedding.toCompatibleEmbedding.image n
  convert P.embedding.toCompatibleEmbedding.affineTimeChange_image n Q hQ a using 1
  simp only [GeneralizedRicciFlow.ForwardParabolicNeighborhood.affineTimeChange]
  have hS :
      (F.affineTimeChange n Q hQ a).spaceTime =
        F.spaceTime.affineTimeChange n Q hQ a := by rfl
  have hball := F.timeSliceBall_affineTimeChange n Q hQ a x r
  have htime :
      (F.affineTimeChange n Q hQ a).spaceTime.time x =
        parabolicTimeOrderIso Q hQ a (F.spaceTime.time x) := by
    simp only [GeneralizedRicciFlow.affineTimeChange,
      GeneralizedSpaceTime.affineTimeChange_time,
      parabolicTimeOrderIso_apply]
  have hinterval :
      parabolicTimeOrderIso Q hQ a ''
          Icc (F.spaceTime.time x) (F.spaceTime.time x + deltaT) =
        Icc ((F.affineTimeChange n Q hQ a).spaceTime.time x)
          ((F.affineTimeChange n Q hQ a).spaceTime.time x + Q * deltaT) := by
    rw [parabolicTimeOrderIso_image_Icc]
    congr 1
    rw [htime]
    simp only [parabolicTimeOrderIso_apply]
    ring
  exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_of_casts
    n hS.symm hball.symm htime.symm hinterval
    (P.embedding.affineTimeChange n Q hQ a)

/-- **Math.** The rescaled backward parabolic-neighborhood witness has exactly
the same ambient image as the original witness. -/
theorem
    GeneralizedRicciFlow.BackwardParabolicNeighborhood.affineTimeChange_image
    [NeZero n] {F : GeneralizedRicciFlow n (N := N)}
    {x : N} {r deltaT : ℝ}
    (P : F.BackwardParabolicNeighborhood n x r deltaT)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (P.affineTimeChange n Q hQ a).image n = P.image n := by
  change (P.affineTimeChange n Q hQ a).embedding.toCompatibleEmbedding.image n =
    P.embedding.toCompatibleEmbedding.image n
  convert P.embedding.toCompatibleEmbedding.affineTimeChange_image n Q hQ a using 1
  simp only [GeneralizedRicciFlow.BackwardParabolicNeighborhood.affineTimeChange]
  have hS :
      (F.affineTimeChange n Q hQ a).spaceTime =
        F.spaceTime.affineTimeChange n Q hQ a := by rfl
  have hball := F.timeSliceBall_affineTimeChange n Q hQ a x r
  have htime :
      (F.affineTimeChange n Q hQ a).spaceTime.time x =
        parabolicTimeOrderIso Q hQ a (F.spaceTime.time x) := by
    simp only [GeneralizedRicciFlow.affineTimeChange,
      GeneralizedSpaceTime.affineTimeChange_time,
      parabolicTimeOrderIso_apply]
  have hinterval :
      parabolicTimeOrderIso Q hQ a ''
          Icc (F.spaceTime.time x - deltaT) (F.spaceTime.time x) =
        Icc ((F.affineTimeChange n Q hQ a).spaceTime.time x - Q * deltaT)
          ((F.affineTimeChange n Q hQ a).spaceTime.time x) := by
    rw [parabolicTimeOrderIso_image_Icc]
    congr 1
    rw [htime]
    simp only [parabolicTimeOrderIso_apply]
    ring
  exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_of_casts
    n hS.symm hball.symm htime.symm hinterval
    (P.embedding.affineTimeChange n Q hQ a)

end MorganTianLib

end

#print axioms MorganTianLib.GeneralizedSpaceTime.CompatibleEmbedding.affineTimeChange
#print axioms MorganTianLib.GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.affineTimeChange
#print axioms MorganTianLib.GeneralizedRicciFlow.ForwardParabolicNeighborhood.affineTimeChange
#print axioms MorganTianLib.GeneralizedRicciFlow.BackwardParabolicNeighborhood.affineTimeChange
