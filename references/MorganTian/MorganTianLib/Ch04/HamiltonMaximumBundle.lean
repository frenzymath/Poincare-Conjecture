import MorganTianLib.Ch04.HamiltonMaximumBounded

/-!
# Morgan--Tian Ch. 4 - a parallel-frame tensor maximum principle

This module isolates the bundle step in Hamilton's argument.  A family of
finite-dimensional inner-product fibers is compared with one model fiber by a
specified family of linear isometries.  The induced transport is the canonical
frame-induced transport (the Levi--Civita connection is not encoded here), and
a carrier described in model coordinates is proved invariant under it.  The
parabolic and reaction equations are then
transported explicitly to the checked finite-dimensional maximum principle.

The fixed-frame scalarized maximum property is an explicit special-case
hypothesis. It does not follow from a general curved Levi--Civita connection:
it would force the operator to annihilate every frame-constant section. The
general geometric argument instead requires locally transported active supports.
-/

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

section Frame

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : X → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℝ (F x)]
  [∀ x, FiniteDimensional ℝ (F x)]

/-! ### Canonical transport in a chosen orthonormal frame -/

/-- A model-fiber frame for each fiber. -/
abbrev FiberFrame := ∀ x, F x ≃ₗᵢ[ℝ] E

/-- The linear isometry obtained by reading a vector in the `x`-frame and
writing it in the `y`-frame. -/
def frameTransport (e : FiberFrame (X := X) (E := E) (F := F)) (x y : X) :
    F x ≃ₗᵢ[ℝ] F y :=
  (e x).trans (e y).symm

@[simp] theorem frameTransport_apply
    (e : FiberFrame (X := X) (E := E) (F := F)) (x y : X) (v : F x) :
    frameTransport e x y v = (e y).symm (e x v) :=
  by simp [frameTransport]

@[simp] theorem frameTransport_refl
    (e : FiberFrame (X := X) (E := E) (F := F)) (x : X) :
    frameTransport e x x = LinearIsometryEquiv.refl ℝ (F x) := by
  ext v
  simp [frameTransport]

@[simp] theorem frameTransport_trans
    (e : FiberFrame (X := X) (E := E) (F := F)) (x y z : X) :
    (frameTransport e x y).trans (frameTransport e y z) =
      frameTransport e x z := by
  ext v
  simp [frameTransport]

/-- The canonical transport family, viewed through the linear-equivalence
interface used by `parallelInvariantFiberSet`. -/
def frameLinearTransportFamily
    (e : FiberFrame (X := X) (E := E) (F := F)) : LinearTransportFamily F :=
  fun x y => { (frameTransport e x y).toLinearEquiv }

/-! ### Coordinate carriers -/

/-- Pull a subset of the model fiber back to each fiber. -/
def frameCarrier (e : FiberFrame (X := X) (E := E) (F := F))
    (Z₀ : Set E) : FiberSet X F :=
  fun x => (e x) ⁻¹' Z₀

@[simp] theorem mem_frameCarrier_iff
    (e : FiberFrame (X := X) (E := E) (F := F)) (Z₀ : Set E)
    (x : X) (v : F x) :
    v ∈ frameCarrier e Z₀ x ↔ e x v ∈ Z₀ :=
  by simp [frameCarrier]

theorem fiberwiseClosed_frameCarrier
    (e : FiberFrame (X := X) (E := E) (F := F)) {Z₀ : Set E}
    (hZ₀ : IsClosed Z₀) : fiberwiseClosed (frameCarrier e Z₀) := by
  intro x
  exact hZ₀.preimage (e x).continuous

theorem fiberwiseConvex_frameCarrier
    (e : FiberFrame (X := X) (E := E) (F := F)) {Z₀ : Set E}
    (hZ₀ : Convex ℝ Z₀) : fiberwiseConvex (frameCarrier e Z₀) := by
  intro x
  exact hZ₀.linear_preimage (e x).toLinearMap

theorem frameCarrier_parallelInvariant
    (e : FiberFrame (X := X) (E := E) (F := F)) (Z₀ : Set E) :
    parallelInvariantFiberSet (frameCarrier e Z₀)
      (frameLinearTransportFamily e) := by
  intro x y p hp
  have hp_eq : p = (frameTransport e x y).toLinearEquiv := by
    simpa [frameLinearTransportFamily] using hp
  rw [hp_eq]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change e y ((frameTransport e x y) w) ∈ Z₀
    simpa [frameTransport] using (mem_frameCarrier_iff e Z₀ x w).mp hw
  · intro hv
    refine ⟨(frameTransport e x y).symm v, ?_, ?_⟩
    · change e x ((frameTransport e x y).symm v) ∈ Z₀
      simpa [frameTransport] using (mem_frameCarrier_iff e Z₀ y v).mp hv
    · simp

end Frame

section Reaction

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : X → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℝ (F x)]
  [∀ x, FiniteDimensional ℝ (F x)]

/-- A fiberwise reaction written in model coordinates. -/
def frameReaction (e : FiberFrame (X := X) (E := E) (F := F))
    (ψ : FiberwiseVectorField F) : X → E → E :=
  fun x v => e x (ψ x ((e x).symm v))

/-- A fiberwise spatial operator written in model coordinates. -/
def frameOperator (e : FiberFrame (X := X) (E := E) (F := F))
    (L : ℝ → (∀ x, F x) → ∀ x, F x) :
    ℝ → (X → E) → X → E :=
  fun t f x => e x (L t (fun y => (e y).symm (f y)) x)

@[simp] theorem frameReaction_apply
    (e : FiberFrame (X := X) (E := E) (F := F))
    (ψ : FiberwiseVectorField F) (x : X) (v : E) :
    frameReaction e ψ x v = e x (ψ x ((e x).symm v)) :=
  rfl

@[simp] theorem frameOperator_apply
    (e : FiberFrame (X := X) (E := E) (F := F))
    (L : ℝ → (∀ x, F x) → ∀ x, F x)
    (t : ℝ) (f : X → E) (x : X) :
    frameOperator e L t f x = e x (L t (fun y => (e y).symm (f y)) x) :=
  rfl

end Reaction

section BundlePrinciple

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : X → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℝ (F x)]
  [∀ x, FiniteDimensional ℝ (F x)]

/-!
The theorem below is the explicit parallel-frame bridge.  `hψcoord` and
`hLcoord` identify the fiberwise reaction and spatial operator with model
expressions; `hpde` then transports the section evolution through the frame.
The hypotheses `hbound`, `hF`, and `hF'` are the bounded-range and
scalarized-regularity facts needed by the finite barrier argument. The
universal fixed-frame maximum property `hLmax` is a special-case assumption,
not a consequence of the rough-Laplacian formula for a general connection.
-/
theorem hamilton_tensor_maximum_principle_of_parallel_frame
    (e : FiberFrame (X := X) (E := E) (F := F))
    {Z₀ : Set E} (hZ₀ne : Z₀.Nonempty) (hZ₀closed : IsClosed Z₀)
    (hZ₀conv : Convex ℝ Z₀)
    {ψ₀ : E → E} {K : ℝ≥0}
    (hψ₀pres : vectorFieldPreservesConvexSet Z₀ ψ₀)
    (hψ₀lip : LipschitzWith K ψ₀)
    (ψ : FiberwiseVectorField F)
    (hψcoord : ∀ x v, frameReaction e ψ x v = ψ₀ v)
    (L : ℝ → (∀ x, F x) → ∀ x, F x)
    (L₀ : ℝ → (X → E) → X → E)
    (hLcoord : ∀ t f x, frameOperator e L t f x = L₀ t f x)
    (hLmax : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L₀ t f x⟫_ℝ ≤ 0)
    (u : ∀ x, ℝ → F x) {a b : ℝ}
    (hpde : ∀ x s,
      HasDerivAt (u x)
        (L s (fun y => u y s) x + ψ x (u x s)) s)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧
      ∀ x t, t ∈ Icc a b → ‖e x (u x t)‖ ≤ B)
    (hF : Continuous ↿(hamiltonSupportValueFamily
      (X := X) Z₀ (fun x t => e x (u x t))))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamily
      (X := X) Z₀ (fun x t => e x (u x t)) L₀ ψ₀))
    (hinit : ∀ x, e x (u x a) ∈ Z₀) :
    ∀ x t, t ∈ Icc a b → u x t ∈ frameCarrier e Z₀ x := by
  obtain ⟨B, hB0, hB⟩ := hbound
  have hcoord : ∀ x s,
      HasDerivAt (fun t => e x (u x t))
        (L₀ s (fun y => e y (u y s)) x + ψ₀ (e x (u x s))) s :=
    by
      intro x s
      have hLcoord' : e x (L s (fun y => u y s) x) =
          L₀ s (fun y => e y (u y s)) x := by
        have hh := hLcoord s (fun y => e y (u y s)) x
        simpa [frameOperator] using hh
      have hψcoord' : e x (ψ x (u x s)) = ψ₀ (e x (u x s)) := by
        have hh := hψcoord x (e x (u x s))
        simpa [frameReaction] using hh
      have hc : HasDerivAt
          (fun _ : ℝ => (e x).toContinuousLinearEquiv.toContinuousLinearMap)
          0 s :=
        hasDerivAt_const (x := s)
          (c := (e x).toContinuousLinearEquiv.toContinuousLinearMap)
      have hh := hc.clm_apply (hpde x s)
      convert hh using 1
      · rfl
      · simp only [zero_apply, zero_add]
        calc
          L₀ s (fun y => e y (u y s)) x + ψ₀ (e x (u x s)) =
              e x (L s (fun y => u y s) x) + e x (ψ x (u x s)) := by
            rw [hLcoord', hψcoord']
          _ = (e x).toContinuousLinearEquiv.toContinuousLinearMap
              (L s (fun y => u y s) x + ψ x (u x s)) := by
            simp
  have hmodel := hamilton_tensor_maximum_principle_bounded
    (X := X) (Z := Z₀) hZ₀ne hZ₀closed hZ₀conv hψ₀pres hψ₀lip L₀ hLmax
    (fun x t => e x (u x t)) hcoord hB hB0 hF hF' hinit
  intro x t ht
  exact (mem_frameCarrier_iff e Z₀ x (u x t)).mpr (hmodel x t ht)

end BundlePrinciple

end MorganTianLib
