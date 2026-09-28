import HanLinLectureNotes.Ch01.MeanValue

/-!
# Han--Lin Chapter 1: harmonic functions
-/

open Filter InnerProductSpace Laplacian Set
open scoped ContDiff

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- A function is harmonic on `Omega` when it is twice continuously
differentiable there and its Laplacian vanishes at every point of `Omega`. -/
def IsHarmonicOn (u : EuclideanSpace Real (Fin n) -> Real)
    (Omega : Set (EuclideanSpace Real (Fin n))) : Prop :=
  ContDiffOn Real 2 u Omega ∧ forall x, x ∈ Omega -> Δ u x = 0

lemma IsHarmonicOn.contDiffOn
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))} (hu : IsHarmonicOn u Omega) :
    ContDiffOn Real 2 u Omega :=
  hu.1

lemma IsHarmonicOn.continuousOn
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))} (hu : IsHarmonicOn u Omega) :
    ContinuousOn u Omega :=
  hu.1.continuousOn

/-- On open sets, the pointwise book definition is equivalent to mathlib's
neighborhood-based harmonicity predicate. -/
theorem harmonicOnNhd_iff_isHarmonicOn
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))} (hopen : IsOpen Omega) :
    HarmonicOnNhd u Omega ↔ IsHarmonicOn u Omega := by
  constructor
  · intro hu
    refine ⟨hu.contDiffOn, ?_⟩
    intro x hx
    have hlap := (hu x hx).2.self_of_nhds
    simpa using hlap
  · rintro ⟨hsmooth, hlap⟩ x hx
    refine ⟨(hsmooth x hx).contDiffAt (hopen.mem_nhds hx), ?_⟩
    filter_upwards [hopen.mem_nhds hx] with y hy
    simpa using hlap y hy

end HanLinLectureNotes.Ch01
