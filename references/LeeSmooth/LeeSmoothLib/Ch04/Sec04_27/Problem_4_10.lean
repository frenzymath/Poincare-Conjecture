import Mathlib.Geometry.Manifold.IsManifold.Basic
import LeeSmoothLib.Ch04.Sec04_26.Example_4_35
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

-- Local API note: semantic `lean_leansearch` was unavailable in this session, so this item
-- follows the established repository names `sphereToRealProjectiveSpace` and
-- `IsSmoothCoveringMap`.

/-- Problem 4-10: the quotient map `q : Sⁿ → ℝPⁿ` defined in Example 2.13(f) is a smooth covering
map. -/
theorem sphere_to_realProjectiveSpace_isSmoothCoveringMap (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (RealProjectiveSpace n)]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (RealProjectiveSpace n)] :
    Manifold.IsSmoothCoveringMap (𝓡 n) (𝓡 n) (sphereToRealProjectiveSpace n) := sorry
