import LeeSmoothLib.Ch01.Sec01_05.Definition_1_5_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

noncomputable section

universe u

/-- Definition 1.6-extra-2 (source-facing): an `n`-dimensional smooth manifold with boundary is
an `n`-dimensional topological manifold with boundary together with the smooth `IsManifold`
structure for Lee's boundary model `leeBoundaryModelWithCorners n`. The topological manifold with
boundary data are owned by `TopologicalManifoldWithBoundary`; smoothness is the only additional
primitive datum here. This keeps the chapter's `n = 0` model `ℍ^0 = ℝ^0` and the
positive-dimensional half-space model in one owner. -/
class SmoothManifoldWithBoundary (n : ℕ) (M : Type u) [TopologicalSpace M] extends
    TopologicalManifoldWithBoundary n M where
  smooth :
    IsManifold (leeBoundaryModelWithCorners n) (⊤ : WithTop ℕ∞) M

attribute [instance] SmoothManifoldWithBoundary.smooth

/-- A smooth manifold with boundary carries the canonical underlying `C^0` manifold-with-boundary
structure. -/
instance instTopologicalManifoldWithBoundaryOfSmoothManifoldWithBoundary (n : ℕ) (M : Type u)
    [TopologicalSpace M] [SmoothManifoldWithBoundary n M] :
    TopologicalManifoldWithBoundary n M :=
  SmoothManifoldWithBoundary.toTopologicalManifoldWithBoundary

/-- Lee's boundary model space is itself a smooth manifold with boundary. -/
noncomputable instance instSmoothManifoldWithBoundaryLeeBoundaryModelSpace (n : ℕ) :
    SmoothManifoldWithBoundary n (ℍ^{n}) where
  toTopologicalManifoldWithBoundary := inferInstance
  smooth := inferInstance

instance instChartedSpaceEuclideanHalfSpaceOfSmoothManifoldWithBoundary {n : ℕ} {M : Type u}
    [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M] :
    ChartedSpace (EuclideanHalfSpace (n + 1)) M := by
  let h : SmoothManifoldWithBoundary (n + 1) M := inferInstance
  simpa [LeeBoundaryModelSpace] using
    h.toTopologicalManifoldWithBoundary.toChartedSpace

instance instIsManifoldEuclideanHalfSpaceOfSmoothManifoldWithBoundary {n : ℕ} {M : Type u}
    [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M] :
    IsManifold (𝓡∂ (n + 1)) (⊤ : WithTop ℕ∞) M := by
  let h : SmoothManifoldWithBoundary (n + 1) M := inferInstance
  simpa [leeBoundaryModelWithCorners] using
    h.smooth

/- Definition 1.6-extra-2 (core/canonical bridge): a smooth manifold with boundary carries the
canonical smooth structure `IsManifold (leeBoundaryModelWithCorners n) ∞ M`. -/
section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]

#synth IsManifold (leeBoundaryModelWithCorners n) (⊤ : WithTop ℕ∞) M

end

/- In positive dimensions, Lee's boundary model agrees with mathlib's standard half-space model,
so a smooth manifold with boundary of dimension `n + 1` is canonically an
`IsManifold (𝓡∂ (n + 1)) ∞` manifold. -/
section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary (n + 1) M]

#synth IsManifold (𝓡∂ (n + 1)) (⊤ : WithTop ℕ∞) M

end
