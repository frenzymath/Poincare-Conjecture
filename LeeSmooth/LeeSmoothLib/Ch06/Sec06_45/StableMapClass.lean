import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_2
open scoped ContDiff Manifold

universe uE uE' uH uH' uN uM uS uES uHS

section StableMapClasses

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ N]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ M]

-- Domain sampling pass: the chapter-level owner for smooth parameter families is
-- `IsSmoothFamily`, and this file keeps the stability owner independent from later proofs.

/-- A class `C` of smooth maps `N → M` between smooth manifolds is stable when membership
persists locally in any smooth family `F : S → N → M` parametrized by a finite-dimensional
smooth manifold after it holds at one parameter value. -/
def IsStableMapClass
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H') (C : Set (N → M)) : Prop :=
  ∀ {S : Type uS} {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
      [FiniteDimensional ℝ ES]
      {HS : Type uHS} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
      {IS : ModelWithCorners ℝ ES HS} [IsManifold IS ∞ S]
      {F : S → N → M},
    IsSmoothFamily J IS I F →
    ∀ {s0 : S}, F s0 ∈ C →
      ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, F s ∈ C

end StableMapClasses
