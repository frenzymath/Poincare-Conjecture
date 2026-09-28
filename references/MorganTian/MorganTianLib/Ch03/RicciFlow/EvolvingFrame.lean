import MorganTianLib.Ch03.RicciFlow.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Morgan--Tian Ch. 3 - preservation of an evolving orthonormal frame

The frame equation in the book is pointwise in the base point.  This module
records the corresponding finite-dimensional calculus statement: if the
metric evolves by `-2 Ric` and each frame vector evolves by the metric-dual
Ricci endomorphism, then all pairings are constant in time.
-/

open Set

noncomputable section

namespace MorganTianLib

/-! The hypotheses below are the coordinate-free form of the frame equation. -/

/-- **Math.** A time-dependent symmetric bilinear form and its Ricci form. -/
structure EvolvingMetricData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (J : Set ℝ) where
  metric : ℝ → V →L[ℝ] V →L[ℝ] ℝ
  ricci : ℝ → V →L[ℝ] V →L[ℝ] ℝ
  metric_deriv : ∀ (t : ℝ),
    HasDerivAt metric (-2 • ricci t) t
  ricci_symm : ∀ (t : ℝ) (v w : V), ricci t v w = ricci t w v

/-- **Math.** The frame ODE uses the metric-dual Ricci endomorphism `A`. -/
structure EvolvingFrameData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (ι : Type*) [Fintype ι] (J : Set ℝ)
    (G : EvolvingMetricData V J) where
  frame : ℝ → ι → V
  dualRicci : ℝ → V →L[ℝ] V
  frame_deriv : ∀ (t : ℝ) (a : ι),
    HasDerivAt (fun s => frame s a) (dualRicci t (frame t a)) t
  dualRicci_left : ∀ (t : ℝ) (v w : V),
    G.metric t (dualRicci t v) w = G.ricci t v w
  dualRicci_right : ∀ (t : ℝ) (v w : V),
    G.metric t v (dualRicci t w) = G.ricci t v w

/-- **Math.** A time-dependent linear identification satisfying the evolving-frame
ODE.  This is the fiberwise data of the bundle map `Phi_t` in the text. -/
structure EvolvingTransportData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (J : Set ℝ) (G : EvolvingMetricData V J) where
  transport : ℝ → V →L[ℝ] V
  dualRicci : ℝ → V →L[ℝ] V
  transport_deriv : ∀ (t : ℝ) (v : V),
    HasDerivAt (fun s => transport s v)
      (dualRicci t (transport t v)) t
  dualRicci_left : ∀ (t : ℝ) (v w : V),
    G.metric t (dualRicci t v) w = G.ricci t v w
  dualRicci_right : ∀ (t : ℝ) (v w : V),
    G.metric t v (dualRicci t w) = G.ricci t v w
  transport_zero : transport 0 = ContinuousLinearMap.id ℝ V

/-! The same cancellation as for a finite frame, now for arbitrary vectors. -/

theorem evolvingTransport_pairing_hasDerivAt_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G) (t : ℝ) (v w : V) :
    HasDerivAt
      (fun s => G.metric s (P.transport s v) (P.transport s w)) 0 t := by
  have h₁ := (G.metric_deriv t).clm_apply
    (P.transport_deriv t v)
  have h₂ := h₁.clm_apply (P.transport_deriv t w)
  apply h₂.congr_deriv
  simp only [smul_apply, add_apply]
  rw [P.dualRicci_left, P.dualRicci_right]
  ring

theorem evolvingTransport_pairing_eq_initial
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G) {a₀ b₀ : ℝ} (hab : a₀ < b₀)
    (v w : V) (t : ℝ) (ht : t ∈ Icc a₀ b₀) :
    G.metric t (P.transport t v) (P.transport t w) =
      G.metric a₀ (P.transport a₀ v) (P.transport a₀ w) := by
  let f : ℝ → ℝ := fun s => G.metric s (P.transport s v) (P.transport s w)
  have hdiff : DifferentiableOn ℝ f (Icc a₀ b₀) := by
    intro s hs
    exact (evolvingTransport_pairing_hasDerivAt_zero P s v w).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ Ico a₀ b₀, derivWithin f (Icc a₀ b₀) s = 0 := by
    intro s hs
    exact (evolvingTransport_pairing_hasDerivAt_zero P s v w).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hab) s ⟨hs.1, hs.2.le⟩)
  exact constant_of_derivWithin_zero hdiff hderiv t ht

/-- **Math.** The evolving bundle identification pulls the time-dependent metric
back to its initial value. -/
theorem evolvingTransport_pullback_metric_constant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G) {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (v w : V) :
    G.metric t (P.transport t v) (P.transport t w) = G.metric 0 v w := by
  rw [evolvingTransport_pairing_eq_initial P hT v w t ht]
  rw [P.transport_zero]
  simp only [ContinuousLinearMap.id_apply]

/-! ## Pairing derivative and orthonormality -/

theorem evolvingFrame_pairing_hasDerivAt_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (t : ℝ) (a b : ι) :
    HasDerivAt
      (fun s => G.metric s (F.frame s a) (F.frame s b)) 0 t := by
  have h₁ := (G.metric_deriv t).clm_apply
    (F.frame_deriv t a)
  have h₂ := h₁.clm_apply (F.frame_deriv t b)
  apply h₂.congr_deriv
  simp only [smul_apply, add_apply]
  rw [F.dualRicci_left, F.dualRicci_right]
  ring

theorem evolvingFrame_pairing_eq_initial
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) {a₀ b₀ : ℝ} (hab : a₀ < b₀)
    (a b : ι) (t : ℝ) (ht : t ∈ Icc a₀ b₀) :
    G.metric t (F.frame t a) (F.frame t b) =
      G.metric a₀ (F.frame a₀ a) (F.frame a₀ b) := by
  let f : ℝ → ℝ := fun s => G.metric s (F.frame s a) (F.frame s b)
  have hdiff : DifferentiableOn ℝ f (Icc a₀ b₀) := by
    intro s hs
    exact ((evolvingFrame_pairing_hasDerivAt_zero F s a b).differentiableAt).differentiableWithinAt
  have hderiv : ∀ s ∈ Ico a₀ b₀, derivWithin f (Icc a₀ b₀) s = 0 := by
    intro s hs
    exact (evolvingFrame_pairing_hasDerivAt_zero F s a b).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hab) s ⟨hs.1, hs.2.le⟩)
  have hconst := constant_of_derivWithin_zero hdiff hderiv t ht
  exact hconst

/-- **Math.** Orthonormality of a frame for an evolving bilinear form. -/
def IsOrthonormalEvolvingFrame
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (t : ℝ) : Prop :=
  by
    classical
    exact ∀ a b, G.metric t (F.frame t a) (F.frame t b) = if a = b then 1 else 0

/-- **Math.** A frame satisfying the Ricci-dual ODE remains orthonormal. -/
theorem evolvingFrame_isOrthonormal_of_initial
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) {a₀ b₀ : ℝ} (hab : a₀ < b₀)
    (hinit : IsOrthonormalEvolvingFrame (V := V) (ι := ι) F a₀)
    {t : ℝ} (ht : t ∈ Icc a₀ b₀) :
    IsOrthonormalEvolvingFrame (V := V) (ι := ι) F t := by
  intro a b
  rw [evolvingFrame_pairing_eq_initial F hab a b t ht]
  exact hinit a b

end MorganTianLib

end
