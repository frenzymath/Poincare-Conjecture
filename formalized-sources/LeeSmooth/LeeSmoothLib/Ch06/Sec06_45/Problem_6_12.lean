import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.Bases
import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_10
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_24.Proposition_4_22
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_2
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_6
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch06.Sec06_38.Proposition_6_8
import LeeSmoothLib.Ch06.Sec06_40.Lemma_6_13
import LeeSmoothLib.Ch06.Sec06_39.Corollary_6_11
-- Declarations for this item will be appended below by the statement pipeline.

open Bundle MeasureTheory Set
open scoped ContDiff Manifold

-- Semantic search note: the `lean_leansearch` tool requested by the statement policy was
-- unavailable in this session, so the statement surface below was chosen by checking the nearby
-- immersion precedent in Chapter 6 together with mathlib's manifold immersion and approximation
-- APIs directly.

namespace Manifold

section

universe uM

section ZeroDimensional

variable {N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold 0 M]
  [IsManifold (𝓡 0) ∞ M]

/-- Helper for Problem 6-12: on a `0`-dimensional smooth manifold, every manifold derivative has
trivial source tangent space, so it is automatically injective. -/
lemma injective_mfderiv_zero_dimensional
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    Function.Injective (mfderiv (𝓡 0) (𝓡 N) f x) := by
  -- The source tangent space of a `0`-manifold has dimension `0`.
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 0) x) = 0 :=
    tangentSpace_finrank_eq_of_n_dimensional_manifold x
  -- Therefore every tangent vector is zero, so any linear map out of it is injective.
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 0) x) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 0))
    infer_instance
  have hzero : ∀ v : TangentSpace (𝓡 0) x, v = 0 :=
    finrank_zero_iff_forall_zero.mp hfin
  intro v w hvw
  rw [hzero v, hzero w]

end ZeroDimensional

/-- Helper for Problem 6-12: pack `ℝ^N × ℝ^m` into `ℝ^(N + m)` by placing the `ℝ^N`
coordinates first and the `ℝ^m` coordinates last. -/
noncomputable def packEuclideanCoordinates (N m : ℕ) :
    (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + m)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)).symm

/-- Helper for Problem 6-12: forget the last `m` coordinates of `ℝ^(N + m)`. -/
noncomputable def truncateTailCoordinates (N m : ℕ) :
    EuclideanSpace ℝ (Fin (N + m)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearMap.fst ℝ
    (EuclideanSpace ℝ (Fin N))
    (EuclideanSpace ℝ (Fin m)) |>.comp
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)) : _ →L[ℝ] _)

/-- Helper for Problem 6-12: packing followed by truncation recovers the original `ℝ^N`
component. -/
lemma truncateTailCoordinates_packEuclideanCoordinates
    {N m : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin m)) :
    truncateTailCoordinates N m (packEuclideanCoordinates N m (x, y)) = x := by
  -- The first `N` packed coordinates are exactly the original `ℝ^N` coordinates.
  simpa [truncateTailCoordinates, packEuclideanCoordinates] using
    congrArg Prod.fst
      (ContinuousLinearEquiv.apply_symm_apply
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m))
        (x, y))

/-- Helper for Problem 6-12: forget the first `N` packed coordinates of `ℝ^(N + m)`. -/
noncomputable def tailCoordinates (N m : ℕ) :
    EuclideanSpace ℝ (Fin (N + m)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ContinuousLinearMap.snd ℝ
    (EuclideanSpace ℝ (Fin N))
    (EuclideanSpace ℝ (Fin m)) |>.comp
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m)) : _ →L[ℝ] _)

/-- Helper for Problem 6-12: packing followed by tail-coordinate recovery recovers the original
`ℝ^m` component. -/
lemma tailCoordinates_packEuclideanCoordinates
    {N m : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin m)) :
    tailCoordinates N m (packEuclideanCoordinates N m (x, y)) = y := by
  -- The last `m` packed coordinates are exactly the original `ℝ^m` coordinates.
  simpa [tailCoordinates, packEuclideanCoordinates] using
    congrArg Prod.snd
      (ContinuousLinearEquiv.apply_symm_apply
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m))
        (x, y))

/-- Helper for Problem 6-12: splitting a packed vector into its head and tail coordinates and
packing again recovers the original vector. -/
lemma packEuclideanCoordinates_truncateTailCoordinates_tailCoordinates
    {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin (N + m))) :
    packEuclideanCoordinates N m
        (truncateTailCoordinates N m z, tailCoordinates N m z) = z := by
  -- Transport to the product model, where the statement is the inverse-equivalence identity.
  simpa [packEuclideanCoordinates, truncateTailCoordinates, tailCoordinates] using
    (ContinuousLinearEquiv.symm_apply_apply
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := m))
      z)

/-- Helper for Problem 6-12: dropping exactly one tail coordinate keeps the first `K`
coordinates unchanged. -/
lemma truncateTailCoordinates_one_apply {K : ℕ}
    (x : EuclideanSpace ℝ (Fin (K + 1))) (i : Fin K) :
    truncateTailCoordinates K 1 x i = x (Fin.castAdd 1 i) := by
  -- Unfold the packed-coordinate truncation and read off the retained coordinate.
  simp [truncateTailCoordinates]

/-- Helper for Problem 6-12: identify `ℝ^(2 * n + 1)` with its coordinate functions. -/
noncomputable def ambientCoordinateCLM :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] (Fin (2 * n + 1) → ℝ) :=
  ↑(EuclideanSpace.equiv (Fin (2 * n + 1)) ℝ)

/-- Helper for Problem 6-12: drop the last coordinate of `ℝ^(2 * n + 1)` as a continuous linear
map into `ℝ^(2 * n)`. -/
noncomputable def dropLastCoordinatesCLM :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  ((↑(EuclideanSpace.equiv (Fin (2 * n)) ℝ).symm :
      (Fin (2 * n) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).comp
    ((ContinuousLinearMap.pi
      (fun i : Fin (2 * n) ↦
        ContinuousLinearMap.proj (Fin.castSucc i))).comp
      ambientCoordinateCLM))

/-- Helper for Problem 6-12: evaluate the last coordinate of `ℝ^(2 * n + 1)` as a continuous
linear functional. -/
noncomputable def lastCoordinateCLM :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (Fin.last (2 * n))).comp
    ambientCoordinateCLM

/-- Helper for Problem 6-12: the standard last-axis direction in `ℝ^(K + 1)` has zero first
`K` coordinates and last coordinate `1`. -/
noncomputable def lastAxisVector (K : ℕ) : EuclideanSpace ℝ (Fin (K + 1)) :=
  PiLp.single 2 (Fin.last K) (1 : ℝ)

/-- Helper for Problem 6-12: the standard last-axis vector truncates to zero. -/
lemma truncateTailCoordinates_lastAxisVector (K : ℕ) :
    truncateTailCoordinates K 1 (lastAxisVector K) = 0 := by
  -- All retained coordinates of the last-axis vector vanish.
  ext i
  have hlt : Fin.castAdd 1 i < Fin.last K := by
    simp only [Fin.lt_def]
    exact i.2
  have hne : Fin.castAdd 1 i ≠ Fin.last K := Fin.ne_last_of_lt hlt
  simp [lastAxisVector, truncateTailCoordinates_one_apply, hne]

/-- Helper for Problem 6-12: dropping the last coordinate is `1`-Lipschitz on `ℝ^(K + 1)`. -/
lemma truncateTailCoordinates_dist_le {K : ℕ}
    (x y : EuclideanSpace ℝ (Fin (K + 1))) :
    dist (truncateTailCoordinates K 1 x)
        (truncateTailCoordinates K 1 y) ≤
      dist x y := by
  let z : EuclideanSpace ℝ (Fin (K + 1)) := x - y
  have hTruncSq :
      ‖truncateTailCoordinates K 1 z‖ ^ (2 : ℕ) =
        ∑ i : Fin K, z (Fin.castAdd 1 i) ^ (2 : ℕ) := by
    -- Expanding the Euclidean norm square of the truncated vector leaves exactly the first `K`
    -- coordinate squares.
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [truncateTailCoordinates_one_apply, z]
  have hFullSq :
      ‖z‖ ^ (2 : ℕ) =
        (∑ i : Fin K, z (Fin.castAdd 1 i) ^ (2 : ℕ)) +
          ∑ i : Fin 1, z (Fin.natAdd K i) ^ (2 : ℕ) := by
    -- Splitting the full Euclidean norm square at the last coordinate isolates the truncated
    -- contribution plus one extra nonnegative square.
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [z] using
      (Fin.sum_univ_add (f := fun i : Fin (K + 1) ↦ z i ^ (2 : ℕ)))
  have hSqLe :
      ‖truncateTailCoordinates K 1 z‖ ^ (2 : ℕ) ≤ ‖z‖ ^ (2 : ℕ) := by
    -- The dropped last-coordinate square is nonnegative.
    rw [hTruncSq, hFullSq]
    exact le_add_of_nonneg_right (by positivity)
  have hNormLe : ‖truncateTailCoordinates K 1 z‖ ≤ ‖z‖ := by
    -- Nonnegative norms are ordered by their squares.
    nlinarith [hSqLe, norm_nonneg (truncateTailCoordinates K 1 z), norm_nonneg z]
  -- Compare norms by comparing their squares.
  rw [dist_eq_norm, dist_eq_norm]
  have hMapSub :
      truncateTailCoordinates K 1 x - truncateTailCoordinates K 1 y =
        truncateTailCoordinates K 1 z := by
    simp [z, map_sub]
  rw [hMapSub]
  simpa [z] using hNormLe

variable {n N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold n M] [CompactSpace M]
  [IsManifold (𝓡 n) ∞ M]

/-- Helper for Problem 6-12: if the first packed component is immersive, then keeping any smooth
tail coordinates unchanged preserves immersion in the larger Euclidean target. -/
lemma isImmersion_packEuclideanCoordinates_of_left
    {m : ℕ}
    {g : M → EuclideanSpace ℝ (Fin (2 * n))}
    {h : M → EuclideanSpace ℝ (Fin m)}
    (hg : IsImmersion (𝓡 n) (𝓡 (2 * n)) ∞ g)
    (hh : ContMDiff (𝓡 n) (𝓡 m) ∞ h) :
    IsImmersion
      (𝓡 n)
      (𝓡 (2 * n + m))
      ∞
      (fun x ↦ packEuclideanCoordinates (2 * n) m (g x, h x)) := by
  let F : M → EuclideanSpace ℝ (Fin (2 * n + m)) :=
    fun x ↦ packEuclideanCoordinates (2 * n) m (g x, h x)
  have hProd :
      ContMDiff
        (𝓡 n)
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)) × EuclideanSpace ℝ (Fin m)))
        ∞
        (fun x : M ↦ (g x, h x)) := by
    -- Build the packed source map directly in the product model.
    simpa using hg.contMDiff.prodMk_space hh
  have hFCont : ContMDiff (𝓡 n) (𝓡 (2 * n + m)) ∞ F := by
    -- Packing is a continuous linear equivalence, so the combined map is smooth.
    simpa [F, Function.comp] using
      (packEuclideanCoordinates (2 * n) m).toContinuousLinearMap.contMDiff.comp hProd
  have hgInj :
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv hg.contMDiff).1 hg
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFCont).2 ?_
  intro x u w huw
  have hHeadComp :
      mfderiv (𝓡 n) (𝓡 (2 * n)) g x =
        (truncateTailCoordinates (2 * n) m).comp
          (mfderiv (𝓡 n) (𝓡 (2 * n + m)) F x) := by
    -- Differentiating the packed map and then forgetting the tail recovers the original head map.
    have hCompRaw :
        mfderiv (𝓡 n) (𝓡 (2 * n))
            (fun y : M ↦ truncateTailCoordinates (2 * n) m (F y)) x =
          (truncateTailCoordinates (2 * n) m).comp
            (mfderiv (𝓡 n) (𝓡 (2 * n + m)) F x) := by
      simpa [Function.comp] using
        (mfderiv_comp
          (x := x)
          (g := truncateTailCoordinates (2 * n) m)
          (f := F)
          ((truncateTailCoordinates (2 * n) m).contMDiffAt.mdifferentiableAt
            (by simp : (∞ : ℕ∞ω) ≠ 0))
          (hFCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hHeadEq :
        (fun y : M ↦ truncateTailCoordinates (2 * n) m (F y)) = g := by
      funext y
      simp [F, truncateTailCoordinates_packEuclideanCoordinates]
    rw [← hHeadEq]
    exact hCompRaw
  have hHeadU :
      mfderiv (𝓡 n) (𝓡 (2 * n)) g x u =
        truncateTailCoordinates (2 * n) m
          (mfderiv (𝓡 n) (𝓡 (2 * n + m)) F x u) := by
    -- Evaluate the recovered derivative identity on the first tangent vector.
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L u) hHeadComp
  have hHeadW :
      mfderiv (𝓡 n) (𝓡 (2 * n)) g x w =
        truncateTailCoordinates (2 * n) m
          (mfderiv (𝓡 n) (𝓡 (2 * n + m)) F x w) := by
    -- Evaluate the same identity on the second tangent vector.
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w) hHeadComp
  apply hgInj x
  rw [hHeadU, hHeadW, huw]

/-! Low-level route note: the above-critical approximation owner from Section 6.40 is not currently
importable in this workspace, so this file keeps the original local frontier theorem below. -/

/-- Helper for Problem 6-12: unpack the induced manifold structure and range diffeomorphism
attached to the range of a smooth embedding `F : M → ℝ^k`. -/
theorem smoothEmbeddingRangeData {k : ℕ} {F : M → EuclideanSpace ℝ (Fin k)}
    (hF : IsSmoothEmbedding (𝓡 n) (𝓡 k) ∞ F) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F),
      ∃ hs : IsManifold (𝓡 n) ∞ (Set.range F),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) := cs
        let _ : IsManifold (𝓡 n) ∞ (Set.range F) := hs
        IsSmoothEmbedding (𝓡 n) (𝓡 k) ∞
          (Subtype.val : Set.range F → EuclideanSpace ℝ (Fin k)) ∧
          ∃ Φ : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Set.range F, ∀ x, (Φ x : EuclideanSpace ℝ (Fin k)) = F x := by
  -- Route correction: reuse the Chapter 5 induced-image owner directly instead of rebuilding the
  -- transported range manifold structure and diffeomorphism by hand in this file.
  rcases smooth_embedding_range_has_induced_manifold_structure hF with ⟨cs, hcs⟩
  have hRange :
      ∃ hs : IsManifold (𝓡 n) ∞ (Set.range F),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range F) := cs
        let _ : IsManifold (𝓡 n) ∞ (Set.range F) := hs
        IsSmoothEmbedding (𝓡 n) (𝓡 k) ∞
          (Subtype.val : Set.range F → EuclideanSpace ℝ (Fin k)) ∧
          ∃ Φ : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Set.range F, ∀ x, (Φ x : EuclideanSpace ℝ (Fin k)) = F x := by
    -- Unfold the owner predicate exactly into the concrete tuple consumed by the compression step.
    simpa [IsInducedImageManifoldStructure] using hcs
  rcases hRange with ⟨hs, hSubtype, Φ, hΦ⟩
  exact ⟨cs, hs, hSubtype, Φ, hΦ⟩

/-- Helper for Problem 6-12: a continuous Euclidean-valued map on a compact source manifold has a
uniform norm bound on its range. -/
lemma existsUniformNormBound {m : ℕ} {F : M → EuclideanSpace ℝ (Fin m)}
    (hF : Continuous F) :
    ∃ C : ℝ, ∀ x : M, ‖F x‖ ≤ C := by
  -- Compactness turns the Euclidean image into a bounded subset of the ambient normed space.
  have hBddAbove :
      BddAbove ((fun y : EuclideanSpace ℝ (Fin m) ↦ ‖y‖) '' Set.range F) :=
    ((isCompact_range hF).image
      (continuous_norm : Continuous fun y : EuclideanSpace ℝ (Fin m) ↦ ‖y‖)).bddAbove
  rcases hBddAbove with ⟨C, hC⟩
  refine ⟨max C 0, ?_⟩
  intro x
  have hx :
      ‖F x‖ ∈ (fun y : EuclideanSpace ℝ (Fin m) ↦ ‖y‖) '' Set.range F :=
    ⟨F x, Set.mem_range_self x, rfl⟩
  exact (hC hx).trans (le_max_left _ _)

/-- Helper for Problem 6-12: repeated truncation can be normalized by first dropping one
coordinate and then truncating the remaining tail. -/
lemma truncateTailCoordinates_comp_one (N m : ℕ) :
    truncateTailCoordinates N (m + 1) =
      (truncateTailCoordinates N m).comp (truncateTailCoordinates (N + m) 1) := by
  -- Both sides keep exactly the first `N` coordinates, so coordinatewise simplification finishes.
  ext x i
  simp [truncateTailCoordinates, Fin.castAdd_castAdd]

/-- Helper for Problem 6-12: forgetting zero tail coordinates does nothing. -/
lemma truncateTailCoordinates_zero_apply
    (x : EuclideanSpace ℝ (Fin N)) :
    truncateTailCoordinates N 0 x = x := by
  -- With no tail coordinates to forget, the Euclidean splitting is the identity.
  ext i
  change x (Fin.castAdd 0 i) = x i
  simp

/-- Helper for Problem 6-12: the packed codimension-one oblique projection written as a
continuous linear map. The positivity hypothesis is kept only to mirror Lemma 6.13's API. -/
private noncomputable def obliqueProjectionToLastHyperplaneLinearMap {K : ℕ} (_hK : 0 < K + 1)
    (v : EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin K) where
  toFun x :=
    (EuclideanSpace.equiv (Fin K) ℝ).symm fun i ↦
      x (Fin.castAdd 1 i) -
        (x (Fin.last K) / v (Fin.last K)) * v (Fin.castAdd 1 i)
  map_add' x y := by
    -- The coordinate formula is affine-linear in `x`.
    ext i
    simp [sub_eq_add_neg, add_mul, div_eq_mul_inv]
    ring
  map_smul' a x := by
    -- Scalar multiplication distributes through the same coordinate formula.
    ext i
    simp [sub_eq_add_neg, div_eq_mul_inv]
    ring

/-- Helper for Problem 6-12: the packed oblique projection is continuous because its source and
target are finite-dimensional. -/
private noncomputable def obliqueProjectionToLastHyperplaneCLM {K : ℕ} (hK : 0 < K + 1)
    (v : EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin K) where
  toLinearMap := obliqueProjectionToLastHyperplaneLinearMap hK v
  cont := by
    exact
      (obliqueProjectionToLastHyperplaneLinearMap hK v).continuous_of_finiteDimensional

/-- Helper for Problem 6-12: the packed oblique projection subtracts the unique multiple of `v`
that kills the last coordinate. -/
private lemma obliqueProjectionToLastHyperplaneCLM_apply {K : ℕ} (hK : 0 < K + 1)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) (i : Fin K) :
    obliqueProjectionToLastHyperplaneCLM hK v x i =
      x (Fin.castAdd 1 i) -
        (x (Fin.last K) / v (Fin.last K)) * v (Fin.castAdd 1 i) := by
  -- The continuous linear map is defined from this coordinate formula.
  rfl

/-- Helper for Problem 6-12: the packed oblique projection is the standard tail truncation plus
one rank-one correction term. -/
lemma obliqueProjectionToLastHyperplaneCLM_sub_truncateTail {K : ℕ} (hK : 0 < K + 1)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) :
    obliqueProjectionToLastHyperplaneCLM hK v x =
      truncateTailCoordinates K 1 x -
        ((x (Fin.last K) / v (Fin.last K)) • truncateTailCoordinates K 1 v) := by
  -- Compare the retained coordinates on both sides after rewriting the truncation map.
  ext i
  simp [obliqueProjectionToLastHyperplaneCLM_apply, truncateTailCoordinates_one_apply, smul_eq_mul]

/-- Helper for Problem 6-12: the packed oblique projection error is controlled by the size of its
rank-one correction term. -/
lemma obliqueProjectionToLastHyperplaneCLM_dist_le_scale {K : ℕ} (hK : 0 < K + 1)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) :
    dist (obliqueProjectionToLastHyperplaneCLM hK v x) (truncateTailCoordinates K 1 x) ≤
      ‖x (Fin.last K) / v (Fin.last K)‖ * ‖truncateTailCoordinates K 1 v‖ := by
  -- Rewrite the difference as exactly one scalar multiple of the truncated direction.
  simpa [dist_eq_norm, obliqueProjectionToLastHyperplaneCLM_sub_truncateTail, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc, norm_neg] using
    (norm_smul (x (Fin.last K) / v (Fin.last K)) (truncateTailCoordinates K 1 v)).le

/-- Helper for Problem 6-12: the public oblique projection from Lemma 6.13 agrees with the local
continuous-linear-map spelling used for the quantitative estimates in this file. -/
lemma obliqueProjectionToLastHyperplane_eq_clm {K : ℕ}
    (v x : EuclideanSpace ℝ (Fin (K + 1))) :
    obliqueProjectionToLastHyperplane (Nat.succ_pos K) v x =
      obliqueProjectionToLastHyperplaneCLM (K := K) (Nat.succ_pos K) v x := by
  -- Compare the two projection spellings coordinatewise through the public formula from
  -- Lemma 6.13.
  ext i
  simpa [obliqueProjectionToLastHyperplaneCLM, obliqueProjectionToLastHyperplaneLinearMap] using
    (obliqueProjectionToLastHyperplane_apply (hN := Nat.succ_pos K) v x i)

/-- Helper for Problem 6-12: if a direction lies within distance `δ` of the last axis, then the
retained first `K` coordinates have norm `< δ`. -/
lemma truncateTailCoordinates_norm_lt_of_mem_ball_general {K : ℕ} {δ : ℝ}
    {v : EuclideanSpace ℝ (Fin (K + 1))}
    (hv : v ∈ Metric.ball (lastAxisVector K) δ) :
    ‖truncateTailCoordinates K 1 v‖ < δ := by
  -- Truncation is `1`-Lipschitz, and the last-axis vector truncates to zero.
  have hvdist : dist v (lastAxisVector K) < δ := by
    simpa [Metric.mem_ball] using hv
  have htruncdist :
      dist (truncateTailCoordinates K 1 v) 0 ≤
        dist v (lastAxisVector K) := by
    simpa [truncateTailCoordinates_lastAxisVector] using
      (truncateTailCoordinates_dist_le (K := K) v (lastAxisVector K))
  exact lt_of_le_of_lt (by simpa [dist_eq_norm] using htruncdist) hvdist

/-- Helper for Problem 6-12: a direction within distance `1 / 2` of the last axis has last
coordinate strictly bigger than `1 / 2`. -/
lemma lastCoordinate_gt_half_of_mem_ball_general {K : ℕ}
    {v : EuclideanSpace ℝ (Fin (K + 1))}
    (hv : v ∈ Metric.ball (lastAxisVector K) ((1 : ℝ) / 2)) :
    (1 : ℝ) / 2 < v (Fin.last K) := by
  -- The last coordinate differs from the last-axis value `1` by at most the ambient norm.
  have hvnorm : ‖v - lastAxisVector K‖ < (1 : ℝ) / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hcoord :
      |v (Fin.last K) - 1| ≤ ‖v - lastAxisVector K‖ := by
    simpa [Real.norm_eq_abs, lastAxisVector, Pi.sub_apply, PiLp.single_apply] using
      (PiLp.norm_apply_le (v - lastAxisVector K) (Fin.last K))
  have hleft : -((1 : ℝ) / 2) < v (Fin.last K) - 1 :=
    (abs_lt.mp (lt_of_le_of_lt hcoord hvnorm)).1
  nlinarith

/-- Helper for Problem 6-12: on a bounded set, any oblique projection whose direction is close to
the last axis is uniformly close to standard truncation. -/
lemma obliqueProjectionNearLastAxis_dist_lt_truncateTail {K : ℕ}
    {C η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃v x : EuclideanSpace ℝ (Fin (K + 1))⦄,
        v ∈ Metric.ball (lastAxisVector K) δ →
        ‖x‖ ≤ C →
        dist (obliqueProjectionToLastHyperplaneCLM (Nat.succ_pos K) v x)
          (truncateTailCoordinates K 1 x) < η := by
  let R : ℝ := max C 0 + 1
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨min ((1 : ℝ) / 2) (η / (4 * R)), ?_, ?_⟩
  · -- The working radius is positive because both the geometric and quantitative constraints are.
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  · intro v x hv hx
    have hδhalf : min ((1 : ℝ) / 2) (η / (4 * R)) ≤ (1 : ℝ) / 2 := min_le_left _ _
    have hδeta : min ((1 : ℝ) / 2) (η / (4 * R)) ≤ η / (4 * R) := min_le_right _ _
    have hvHalf :
        v ∈ Metric.ball (lastAxisVector K) ((1 : ℝ) / 2) := by
      -- Shrinking the ball radius preserves the denominator control from the geometric estimate.
      rcases hv with hv
      simpa [Metric.mem_ball, dist_eq_norm] using lt_of_lt_of_le
        (by simpa [Metric.mem_ball, dist_eq_norm] using hv)
        hδhalf
    have htrunc :
        ‖truncateTailCoordinates K 1 v‖ < min ((1 : ℝ) / 2) (η / (4 * R)) :=
      truncateTailCoordinates_norm_lt_of_mem_ball_general hv
    have hlast : (1 : ℝ) / 2 < v (Fin.last K) :=
      lastCoordinate_gt_half_of_mem_ball_general hvHalf
    have hvpos : 0 < v (Fin.last K) := by
      nlinarith
    have hcoordLe :
        ‖x (Fin.last K)‖ ≤ C := by
      exact (PiLp.norm_apply_le x (Fin.last K)).trans hx
    have hcoordR : ‖x (Fin.last K)‖ ≤ R := by
      have hCLeR : C ≤ R := by
        dsimp [R]
        have hCLeMax : C ≤ max C 0 := le_max_left _ _
        linarith
      exact hcoordLe.trans hCLeR
    have hdistLe :
        dist (obliqueProjectionToLastHyperplaneCLM (Nat.succ_pos K) v x)
            (truncateTailCoordinates K 1 x) ≤
          ‖x (Fin.last K) / v (Fin.last K)‖ * ‖truncateTailCoordinates K 1 v‖ :=
      obliqueProjectionToLastHyperplaneCLM_dist_le_scale (Nat.succ_pos K) v x
    have hcancel :
        ‖x (Fin.last K) / v (Fin.last K)‖ * v (Fin.last K) =
          ‖x (Fin.last K)‖ := by
      calc
        ‖x (Fin.last K) / v (Fin.last K)‖ * v (Fin.last K) =
            (‖x (Fin.last K)‖ / ‖v (Fin.last K)‖) * v (Fin.last K) := by
              rw [norm_div]
        _ = (‖x (Fin.last K)‖ / v (Fin.last K)) * v (Fin.last K) := by
              simp [Real.norm_eq_abs, abs_of_pos hvpos]
        _ = ‖x (Fin.last K)‖ := by
              field_simp [ne_of_gt hvpos]
    have hquotLe : ‖x (Fin.last K) / v (Fin.last K)‖ ≤ 2 * R := by
      have hhalfLe :
          ‖x (Fin.last K) / v (Fin.last K)‖ * ((1 : ℝ) / 2) ≤ ‖x (Fin.last K)‖ := by
        calc
          ‖x (Fin.last K) / v (Fin.last K)‖ * ((1 : ℝ) / 2) ≤
              ‖x (Fin.last K) / v (Fin.last K)‖ * v (Fin.last K) := by
                exact mul_le_mul_of_nonneg_left (le_of_lt hlast) (norm_nonneg _)
          _ = ‖x (Fin.last K)‖ := hcancel
      nlinarith
    have hprodLe :
        ‖x (Fin.last K) / v (Fin.last K)‖ * ‖truncateTailCoordinates K 1 v‖ ≤
          ‖x (Fin.last K) / v (Fin.last K)‖ * min ((1 : ℝ) / 2) (η / (4 * R)) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt htrunc) (norm_nonneg _)
    have hprodLt :
        ‖x (Fin.last K) / v (Fin.last K)‖ * min ((1 : ℝ) / 2) (η / (4 * R)) < η := by
      have hmain :
          ‖x (Fin.last K) / v (Fin.last K)‖ * min ((1 : ℝ) / 2) (η / (4 * R)) ≤ η / 2 := by
        calc
          ‖x (Fin.last K) / v (Fin.last K)‖ * min ((1 : ℝ) / 2) (η / (4 * R)) ≤
              (2 * R) * min ((1 : ℝ) / 2) (η / (4 * R)) := by
                exact mul_le_mul_of_nonneg_right hquotLe (by positivity)
          _ ≤ (2 * R) * (η / (4 * R)) := by
                exact mul_le_mul_of_nonneg_left hδeta (by positivity)
          _ = η / 2 := by
                field_simp [ne_of_gt hRpos]
                ring
      linarith
    exact lt_of_le_of_lt (le_trans hdistLe hprodLe) hprodLt

/-- Helper for Problem 6-12: Lemma 6.13 lets us choose a good oblique-projection direction inside
any prescribed ball around the last axis. -/
lemma existsGoodObliqueDirectionNearLastAxis {K : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (K + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    (hSubtype :
      IsSmoothEmbedding (𝓡 n) (𝓡 (K + 1)) ∞
        (Subtype.val : S → EuclideanSpace ℝ (Fin (K + 1))))
    (hK : 2 * n + 1 ≤ K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : EuclideanSpace ℝ (Fin (K + 1)),
      v ∈ Metric.ball (lastAxisVector K) δ ∧
        ObliqueProjectionDirectionRestrictsToInjectiveImmersion
          (J := 𝓡 n) (M := S) (Nat.succ_pos K) v := by
  have hDense :
      Dense
        {v : EuclideanSpace ℝ (Fin (K + 1)) |
          ObliqueProjectionDirectionRestrictsToInjectiveImmersion
            (J := 𝓡 n) (M := S) (Nat.succ_pos K) v} := by
    have hdim :
        2 * Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1 < K + 1 := by
      simpa using Nat.lt_succ_of_le hK
    simpa using
      dense_oblique_projection_directions_restrict_to_injective_immersion
        (J := 𝓡 n)
        (M := S)
        (Nat.succ_pos K)
        hSubtype
        hdim
  have hBallNonempty :
      (Metric.ball (lastAxisVector K) δ :
        Set (EuclideanSpace ℝ (Fin (K + 1)))).Nonempty := by
    -- The center point lies in every positive-radius ball around itself.
    refine ⟨lastAxisVector K, ?_⟩
    simpa [Metric.mem_ball] using hδ
  obtain ⟨v, hvBall, hvGood⟩ :=
    hDense.inter_open_nonempty
      (Metric.ball (lastAxisVector K) δ)
      Metric.isOpen_ball
      hBallNonempty
  exact ⟨v, hvBall, hvGood⟩

/-- Helper for Problem 6-12: tail truncation is `1`-Lipschitz for any number of discarded
coordinates. -/
lemma truncateTailCoordinates_dist_le_iterated {m : ℕ}
    (x y : EuclideanSpace ℝ (Fin (N + m))) :
    dist (truncateTailCoordinates N m x)
        (truncateTailCoordinates N m y) ≤
      dist x y := by
  induction m with
  | zero =>
      -- The zero-tail truncation is the identity.
      rw [truncateTailCoordinates_zero_apply, truncateTailCoordinates_zero_apply]
  | succ m ihm =>
      -- First drop one coordinate, then apply the inductive `1`-Lipschitz estimate to the rest.
      rw [truncateTailCoordinates_comp_one]
      exact
        (ihm _ _).trans
          (truncateTailCoordinates_dist_le
            (K := N + m)
            x
            y)

/-- Helper for Problem 6-12: one compact codimension-drop step replaces a smooth embedding into
`ℝ^(K + 1)` by a nearby smooth embedding into `ℝ^K`. -/
lemma existsApproximateCodimensionDropStep {K : ℕ}
    {G : M → EuclideanSpace ℝ (Fin (K + 1))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (K + 1)) ∞ G)
    (hK : 2 * n + 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ g : M → EuclideanSpace ℝ (Fin K),
      IsSmoothEmbedding (𝓡 n) (𝓡 K) ∞ g ∧
        ∀ x : M, dist (g x) (truncateTailCoordinates K 1 (G x)) < η := by
  let S : Set (EuclideanSpace ℝ (Fin (K + 1))) := Set.range G
  obtain ⟨cs, hs, hSubtype, Φ, hΦ_apply⟩ :=
    smoothEmbeddingRangeData (n := n) (F := G) hG
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) S := cs
  let _ : IsManifold (𝓡 n) ∞ S := hs
  let _ : CompactSpace S := Homeomorph.compactSpace Φ.toHomeomorph
  obtain ⟨C, hC⟩ :=
    existsUniformNormBound
      (M := S)
      (F := (Subtype.val : S → EuclideanSpace ℝ (Fin (K + 1))))
      hSubtype.isEmbedding.continuous
  obtain ⟨δ, hδ, hApproximateProjection⟩ :=
    obliqueProjectionNearLastAxis_dist_lt_truncateTail
      (K := K)
      (C := C)
      (η := η)
      hη
  obtain ⟨v, hvBall, hvGood⟩ :=
    existsGoodObliqueDirectionNearLastAxis
      (n := n)
      (K := K)
      (S := S)
      hSubtype
      hK
      hδ
  let ψ : S → EuclideanSpace ℝ (Fin K) :=
    fun p ↦ obliqueProjectionToLastHyperplane (Nat.succ_pos K) v p.1
  have hψImmersion :
      IsImmersion (𝓡 n) (𝓡 K) ∞ ψ := by
    -- Lemma 6.13 gives the projected range map as an injective immersion.
    simpa [ψ] using hvGood.isImmersion
  have hψ :
      IsSmoothEmbedding (𝓡 n) (𝓡 K) ∞ ψ := by
    -- Compactness of the range upgrades the injective immersion to a smooth embedding.
    exact
      smooth_embedding_of_compact_source_injective_isImmersion
        (I := 𝓡 n)
        (J := 𝓡 K)
        (F := ψ)
        hvGood.injective
        hψImmersion
  have hΦ :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 n)
        ∞
        Φ := by
    -- The source-to-range diffeomorphism is already a smooth embedding.
    exact ⟨IsLocalDiffeomorph.isImmersion (Φ.isLocalDiffeomorph), Φ.toHomeomorph.isEmbedding⟩
  refine ⟨ψ ∘ Φ, ?_, ?_⟩
  · -- Compose the range embedding with the range diffeomorphism to return to `M`.
    simpa [Function.comp] using Manifold.IsSmoothEmbedding.comp hψ hΦ
  · intro x
    -- The chosen oblique projection is uniformly close to standard truncation on the compact
    -- embedded range.
    simpa [Function.comp, ψ, hΦ_apply x, obliqueProjectionToLastHyperplane_eq_clm] using
      hApproximateProjection
        (v := v)
        (x := (Φ x : EuclideanSpace ℝ (Fin (K + 1))))
        hvBall
        (hC (Φ x))

/-- Helper for Problem 6-12: iterating the compact codimension-drop step compresses a smooth
embedding in `ℝ^(N + m)` to a nearby smooth embedding in `ℝ^N`. -/
lemma existsApproximateCompressionToBase {m : ℕ}
    {G : M → EuclideanSpace ℝ (Fin (N + m))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (N + m)) ∞ G)
    (hN : 2 * n + 1 ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → EuclideanSpace ℝ (Fin N),
      IsSmoothEmbedding (𝓡 n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (truncateTailCoordinates N m (G x)) < ε := by
  induction m generalizing ε with
  | zero =>
      refine ⟨G, ?_, ?_⟩
      · -- With no tail coordinates, the original embedding already lands in the target space.
        simpa using hG
      · intro x
        -- The approximation error is zero in the base case.
        simpa [truncateTailCoordinates_zero_apply] using hε
  | succ m ih =>
      have hHalf : 0 < ε / 2 := by
        positivity
      obtain ⟨g₁, hg₁, hg₁Approx⟩ :=
        existsApproximateCodimensionDropStep
          (n := n)
          (M := M)
          (K := N + m)
          (G := G)
          hG
          (le_trans hN (Nat.le_add_right N m))
          hHalf
      obtain ⟨g, hg, hgApprox⟩ :=
        ih
          (G := g₁)
          hg₁
          hHalf
      refine ⟨g, hg, ?_⟩
      intro x
      have hCompress :
          dist
            (truncateTailCoordinates N m (g₁ x))
            (truncateTailCoordinates N m (truncateTailCoordinates (N + m) 1 (G x))) <
          ε / 2 := by
        -- Further truncation does not enlarge the one-step codimension-drop error.
        exact
          lt_of_le_of_lt
            (truncateTailCoordinates_dist_le_iterated
              (N := N)
              (m := m)
              (x := g₁ x)
              (y := truncateTailCoordinates (N + m) 1 (G x)))
            (hg₁Approx x)
      have hCompApply :
          truncateTailCoordinates N (m + 1) (G x) =
            truncateTailCoordinates N m (truncateTailCoordinates (N + m) 1 (G x)) := by
        -- Normalize the repeated truncation into the recursive shape used by the induction.
        simpa [ContinuousLinearMap.comp_apply] using
          congrArg (fun L ↦ L (G x)) (truncateTailCoordinates_comp_one N m)
      -- Combine the recursive approximation with the new codimension-drop estimate.
      calc
        dist (g x) (truncateTailCoordinates N (m + 1) (G x)) ≤
            dist (g x) (truncateTailCoordinates N m (g₁ x)) +
              dist
                (truncateTailCoordinates N m (g₁ x))
                (truncateTailCoordinates N (m + 1) (G x)) := by
                  exact dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
          refine add_lt_add (hgApprox x) ?_
          simpa [hCompApply] using hCompress
        _ = ε := by ring

/-- Helper for Problem 6-12: after packing the graph of `(f, e)`, the result is a smooth
embedding into a single Euclidean target. -/
lemma packedGraph_isSmoothEmbedding
    {m : ℕ}
    (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (he : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ e) :
    IsSmoothEmbedding
      (𝓡 n)
      (𝓡 (N + m))
      ∞
      (fun x ↦ packEuclideanCoordinates N m (f x, e x)) := by
  let G : M → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) := fun x ↦ (f x, e x)
  let F : M → EuclideanSpace ℝ (Fin (N + m)) := fun x ↦ packEuclideanCoordinates N m (G x)
  have hGContSelf :
      ContMDiff
        (𝓡 n)
        (𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)))
        ∞
        G := by
    -- Build the graph directly in the ambient product space to avoid product-model transport.
    simpa [G] using f.contMDiff.prodMk_space he.isImmersion.contMDiff
  have hFCont : ContMDiff (𝓡 n) (𝓡 (N + m)) ∞ F := by
    -- Packing is a continuous linear equivalence, so the graph map is smooth.
    simpa [F, G, Function.comp] using
      (packEuclideanCoordinates N m).toContinuousLinearMap.contMDiff.comp
        hGContSelf
  have hTailCompEq : (fun x : M ↦ tailCoordinates N m (F x)) = e := by
    -- Tail coordinates recover the embedding component of the packed graph pointwise.
    funext x
    simp [F, G, tailCoordinates_packEuclideanCoordinates]
  have heDerivInj :
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 m) e x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv he.isImmersion.contMDiff).1
      he.isImmersion
  have hFInj : Function.Injective F := by
    intro x y hxy
    have hTail :
        e x = e y := by
      -- Tail coordinates recover the embedding component of the packed graph.
      simpa [F, G, tailCoordinates_packEuclideanCoordinates] using
        congrArg (tailCoordinates N m) hxy
    exact he.isEmbedding.injective hTail
  have hFImm : IsImmersion (𝓡 n) (𝓡 (N + m)) ∞ F := by
    -- Recover derivative injectivity by postcomposing with the tail-coordinate projection.
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFCont).2 ?_
    intro x u w huw
    have hCompRaw :
        mfderiv (𝓡 n) (𝓡 m) (fun y : M ↦ tailCoordinates N m (F y)) x =
          (tailCoordinates N m).comp (mfderiv (𝓡 n) (𝓡 (N + m)) F x) := by
      -- The chain rule differentiates `tailCoordinates ∘ F = e`.
      simpa [Function.comp] using
        (mfderiv_comp
          (x := x)
          (g := tailCoordinates N m)
          (f := F)
          ((tailCoordinates N m).contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (hFCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hComp :
        mfderiv (𝓡 n) (𝓡 m) e x =
          (tailCoordinates N m).comp (mfderiv (𝓡 n) (𝓡 (N + m)) F x) := by
      -- Rewrite the recovered tail-coordinate map to the original embedding.
      rw [← hTailCompEq]
      exact hCompRaw
    have hCompU :
        mfderiv (𝓡 n) (𝓡 m) e x u =
          tailCoordinates N m (mfderiv (𝓡 n) (𝓡 (N + m)) F x u) := by
      -- Evaluate the chain-rule identity on the first tangent vector.
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L u) hComp
    have hCompW :
        mfderiv (𝓡 n) (𝓡 m) e x w =
          tailCoordinates N m (mfderiv (𝓡 n) (𝓡 (N + m)) F x w) := by
      -- Evaluate the same identity on the second tangent vector.
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w) hComp
    exact heDerivInj x <| by
      rw [hCompU, hCompW, huw]
  -- Compactness of the source upgrades the injective immersion to a smooth embedding.
  simpa [F] using
    (smooth_embedding_of_compact_source_injective_isImmersion
      (I := 𝓡 n)
      (J := 𝓡 (N + m))
      (F := F)
      hFInj
      hFImm)

/-- Helper for Problem 6-12: above the critical dimension, a compact boundaryless smooth map into
`ℝ^N` can be uniformly approximated by smooth embeddings. This is the theorem-local replacement
for the unavailable Section 6.40 owner used by the easy branch and by the lifted critical branch.
-/
lemma approximateByEmbeddingsAboveCritical
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding (𝓡 n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  -- Route correction: instead of importing the collision-heavy Corollary 6.17 file, rebuild the
  -- same graph-plus-codimension-drop argument locally inside this item.
  obtain ⟨m, e, he⟩ :
      ∃ m : ℕ, ∃ e : M → EuclideanSpace ℝ (Fin m),
        IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ e := by
    -- Start from mathlib's compact Whitney embedding theorem and repackage it as a smooth
    -- embedding.
    obtain ⟨m, e, heCont, heClosed, heInj⟩ :=
      exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
    refine ⟨m, e, ?_⟩
    refine ⟨?_, heClosed.isEmbedding⟩
    exact (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).2 heInj
  let G₀ : M → EuclideanSpace ℝ (Fin (N + m)) :=
    fun x ↦ packEuclideanCoordinates N m (f x, e x)
  have hGraph :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 (N + m))
        ∞
        G₀ := by
    -- The packed graph of `(f, e)` is itself a smooth embedding into one Euclidean space.
    simpa [G₀] using
      packedGraph_isSmoothEmbedding
        (n := n)
        (N := N)
        (M := M)
        f
        he
  obtain ⟨g, hg, hgApprox⟩ :=
    existsApproximateCompressionToBase
      (n := n)
      (N := N)
      (M := M)
      (m := m)
      (G := G₀)
      hGraph
      hN
      hε
  refine ⟨⟨g, hg.isImmersion.contMDiff⟩, ?_, ?_⟩
  · -- Package the function-valued embedding as a smooth map.
    simpa using hg
  · intro x
    have hProjection :
        truncateTailCoordinates N m (G₀ x) = f x := by
      -- Standard coordinate truncation on the packed graph recovers the original map.
      simpa [G₀] using
        truncateTailCoordinates_packEuclideanCoordinates
          (N := N)
          (m := m)
          (x := f x)
          (y := e x)
    -- The compression theorem approximates the graph by an embedding while preserving the head
    -- coordinates.
    simpa [hProjection] using hgApprox x

/-- Helper for Problem 6-12: above the critical dimension, the existing embedding-approximation
theorem immediately gives an immersion approximation. -/
lemma embeddingApproximationGivesImmersionApproximation
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsImmersion (𝓡 n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  -- Forget the embedding field from the local above-critical owner.
  obtain ⟨g, hgEmb, hgClose⟩ :=
    approximateByEmbeddingsAboveCritical
      (n := n)
      (N := N)
      (M := M)
      hN
      f
      hε
  exact ⟨g, hgEmb.isImmersion, hgClose⟩

/-- Helper for Problem 6-12: the ambient tangent-vector map of an embedding into `ℝ^(2n + 1)`,
viewed as a smooth map on the full tangent bundle. -/
noncomputable def ambientTangentVector
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))} :
    TangentBundle (𝓡 n) M → EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  fun u ↦ (tangentMap (𝓡 n) (𝓡 (2 * n + 1)) G u).2

/-- Helper for Problem 6-12: evaluating `ambientTangentVector` at a concrete tangent vector gives
the corresponding manifold derivative value. -/
  lemma ambientTangentVector_apply
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (x : M) (u : TangentSpace (𝓡 n) x) :
    ambientTangentVector (n := n) (G := G) ⟨x, u⟩ =
      mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u := by
  -- The second component of `tangentMap` is exactly the manifold derivative.
  simpa [ambientTangentVector] using
    (tangentMap_snd
      (I := 𝓡 n)
      (I' := 𝓡 (2 * n + 1))
      (f := G)
      (x := x)
      (X := u))

/-- Helper for Problem 6-12: the ambient tangent-vector map is smooth whenever the original map is
smooth. -/
lemma ambientTangentVector_contMDiff
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ G) :
    ContMDiff
      (𝓡 n).tangent
      (𝓡 (2 * n + 1))
      ∞
      (ambientTangentVector (n := n) (G := G)) := by
  -- Compose the smooth tangent map with the smooth bundle projection to the ambient tangent fiber.
  simpa [ambientTangentVector, Function.comp] using
    (contMDiff_snd_tangentBundle_modelSpace
      (EuclideanSpace ℝ (Fin (2 * n + 1)))
      (𝓡 (2 * n + 1))).comp
      ((hG.contMDiff_tangentMap (m := ∞) le_rfl))

/-- Helper for Problem 6-12: if `M` is Hausdorff, then its tangent bundle is Hausdorff as well.
-/
lemma t2Space_tangentBundleBoundaryless [T2Space M] :
    T2Space (TangentBundle (𝓡 n) M) := by
  let E := EuclideanSpace ℝ (Fin n)
  let TM := TangentBundle (𝓡 n) M
  refine ⟨?_⟩
  intro p q hpq
  by_cases hproj : p.1 = q.1
  · let e := trivializationAt E (TangentSpace (𝓡 n)) p.1
    have hpSource : p ∈ e.source := by
      simpa [e] using
        (mem_trivializationAt_proj_source
          (F := E)
          (E := TangentSpace (𝓡 n))
          (x := p))
    have hqSource : q ∈ e.source := by
      simpa [e, hproj] using
        (mem_trivializationAt_proj_source
          (F := E)
          (E := TangentSpace (𝓡 n))
          (x := q))
    let ps : e.source := ⟨p, hpSource⟩
    let qs : e.source := ⟨q, hqSource⟩
    have hpsq : ps ≠ qs := by
      intro h
      apply hpq
      exact congrArg Subtype.val h
    -- Inside one trivialization source, the tangent bundle is homeomorphic to a product of
    -- Hausdorff spaces.
    let _ : T2Space e.baseSet := inferInstance
    let _ : T2Space E := inferInstance
    let _ : T2Space (e.baseSet × E) := inferInstance
    let _ : T2Space e.source := e.sourceHomeomorphBaseSetProd.symm.t2Space
    simpa [ps, qs] using
      (separated_by_isOpenEmbedding
        (f := ((↑) : e.source → TM))
        e.open_source.isOpenEmbedding_subtypeVal
        hpsq)
  · -- Distinct base points are already separated by the bundle projection to the Hausdorff base.
    exact
      separated_by_continuous
        (f := fun z : TM ↦ z.1)
        (FiberBundle.continuous_proj E (TangentSpace (𝓡 n)))
        hproj

/-- Helper for Problem 6-12: if `M` is second countable, then its tangent bundle is second
countable. -/
lemma secondCountableTopology_tangentBundleBoundaryless [SecondCountableTopology M] :
    SecondCountableTopology (TangentBundle (𝓡 n) M) := by
  let E := EuclideanSpace ℝ (Fin n)
  let TM := TangentBundle (𝓡 n) M
  obtain ⟨s, hsCountable, hsCover⟩ :=
    countable_cover_nhds
      (fun x : M ↦ chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) x)
  let U : s → Set TM :=
    fun x ↦ (trivializationAt E (TangentSpace (𝓡 n)) (x : M)).source
  have hUOpen : ∀ x : s, IsOpen (U x) := by
    intro x
    exact (trivializationAt E (TangentSpace (𝓡 n)) (x : M)).open_source
  have hUCover : ⋃ x : s, U x = univ := by
    ext p
    constructor
    · intro hp
      simp
    · intro hp
      rcases Set.mem_iUnion.1 (by
          simpa [hsCover] using hp :
            p.1 ∈ ⋃ x : s, (chartAt (EuclideanSpace ℝ (Fin n)) (x : M)).source) with ⟨x, hx⟩
      refine Set.mem_iUnion.2 ⟨x, ?_⟩
      change p ∈ (trivializationAt E (TangentSpace (𝓡 n)) (x : M)).source
      exact (Trivialization.mem_source _).2 hx
  have hUSecondCountable : ∀ x : s, SecondCountableTopology (U x) := by
    intro x
    let e := trivializationAt E (TangentSpace (𝓡 n)) (x : M)
    let _ : SecondCountableTopology e.baseSet := inferInstance
    let _ : SecondCountableTopology E := inferInstance
    let _ : SecondCountableTopology (e.baseSet × E) := inferInstance
    exact e.sourceHomeomorphBaseSetProd.secondCountableTopology
  let _ : Countable s := hsCountable.to_subtype
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hUOpen hUCover

/-- Helper for Problem 6-12: an immersion sends every nonzero tangent vector to a nonzero ambient
derivative vector. -/
lemma mfderiv_ne_zero_of_isImmersion
    {m : ℕ}
    {G : M → EuclideanSpace ℝ (Fin m)}
    (hG : IsImmersion (𝓡 n) (𝓡 m) ∞ G)
    {x : M} {u : TangentSpace (𝓡 n) x}
    (hu : u ≠ 0) :
    mfderiv (𝓡 n) (𝓡 m) G x u ≠ 0 := by
  -- Pointwise injectivity of the manifold derivative rules out nonzero kernel vectors.
  have hGCont : ContMDiff (𝓡 n) (𝓡 m) ∞ G := hG.contMDiff
  have hInj :
      Function.Injective (mfderiv (𝓡 n) (𝓡 m) G x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv hGCont).1 hG x
  intro hImageZero
  apply hu
  apply hInj
  simpa using hImageZero

/-- Helper for Problem 6-12: on a nonzero tangent vector, `ambientTangentVector` for a smooth
embedding is itself nonzero. -/
lemma ambientTangentVector_ne_zero_of_isSmoothEmbedding
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G)
    {x : M} {u : TangentSpace (𝓡 n) x}
    (hu : u ≠ 0) :
    ambientTangentVector (n := n) (G := G) ⟨x, u⟩ ≠ 0 := by
  -- Rewrite the ambient tangent vector as the manifold derivative and apply the previous lemma.
  rw [ambientTangentVector_apply]
  exact mfderiv_ne_zero_of_isImmersion (n := n) hG.isImmersion hu

/-- Helper for Problem 6-12: once the tangent bundle carries the needed separation/countability
instances, the full ambient tangent range has measure zero in `ℝ^(2n + 1)`, so every ball around
the last axis contains a vector outside that range. -/
lemma existsNearVerticalDirectionOutsideAmbientTangentRange_of_tangentBundleTopology
    [T2Space (TangentBundle (𝓡 n) M)]
    [SecondCountableTopology (TangentBundle (𝓡 n) M)]
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G) :
    ∃ v : EuclideanSpace ℝ (Fin (2 * n + 1)),
      v ∈ Metric.ball (lastAxisVector (2 * n)) ((1 : ℝ) / 2) ∧
        v ∉ Set.range (ambientTangentVector (n := n) (G := G)) := by
  -- The tangent-bundle derivative image has codimension one in the Euclidean target.
  have hRangeZero :
      has_measure_zero_in_manifold
        (𝓡 (2 * n + 1))
        (Set.range (ambientTangentVector (n := n) (G := G))) := by
    have hdim :
        Module.finrank ℝ
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) <
          Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n + 1))) := by
      -- The tangent bundle model has dimension `2n`, strictly smaller than `2n + 1`.
      simpa [Module.finrank_prod, two_mul] using Nat.lt_succ_self (2 * n)
    exact
      range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt
        (I := (𝓡 n).tangent)
        (J := 𝓡 (2 * n + 1))
        (M := TangentBundle (𝓡 n) M)
        (N := EuclideanSpace ℝ (Fin (2 * n + 1)))
        (F := ambientTangentVector (n := n) (G := G))
        (ambientTangentVector_contMDiff (n := n) hG.isImmersion.contMDiff)
        hdim
  have hDense :
      Dense
        ((Set.range (ambientTangentVector (n := n) (G := G)))ᶜ :
          Set (EuclideanSpace ℝ (Fin (2 * n + 1)))) :=
    has_measure_zero_in_manifold.dense_compl hRangeZero
  have hBallNonempty :
      (Metric.ball (lastAxisVector (2 * n)) ((1 : ℝ) / 2) :
        Set (EuclideanSpace ℝ (Fin (2 * n + 1)))).Nonempty := by
    -- The center point lies in every positive-radius ball around itself.
    have hHalf : (0 : ℝ) < (1 : ℝ) / 2 := by
      norm_num
    refine ⟨lastAxisVector (2 * n), ?_⟩
    simpa [Metric.mem_ball] using hHalf
  obtain ⟨v, hvBall, hvCompl⟩ :=
    hDense.inter_open_nonempty
      (Metric.ball (lastAxisVector (2 * n)) ((1 : ℝ) / 2))
      Metric.isOpen_ball
      hBallNonempty
  exact ⟨v, hvBall, hvCompl⟩

/-- Helper for Problem 6-12: a near-vertical ambient direction can be chosen outside the full
tangent-image range of a smooth embedding `G : M → ℝ^(2n + 1)`. -/
lemma existsNearVerticalDirectionOutsideAmbientTangentRange
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G) :
    ∃ v : EuclideanSpace ℝ (Fin (2 * n + 1)),
      v ∈ Metric.ball (lastAxisVector (2 * n)) ((1 : ℝ) / 2) ∧
        v ∉ Set.range (ambientTangentVector (n := n) (G := G)) := by
  -- The source embedding already gives the needed separation and countability on `M`, and the
  -- tangent-bundle instances are then recovered from the explicit boundaryless bundle lemmas
  -- above.
  let _ : T2Space M := hG.isEmbedding.t2Space
  let _ : SecondCountableTopology M := hG.isEmbedding.secondCountableTopology
  let _ : T2Space (TangentBundle (𝓡 n) M) :=
    t2Space_tangentBundleBoundaryless (n := n) (M := M)
  let _ : SecondCountableTopology (TangentBundle (𝓡 n) M) :=
    secondCountableTopology_tangentBundleBoundaryless (n := n) (M := M)
  simpa using
    existsNearVerticalDirectionOutsideAmbientTangentRange_of_tangentBundleTopology
      (n := n)
      (M := M)
      hG

/-- Helper for Problem 6-12: if a direction lies within distance `1 / 2` of the last axis, then
its retained first `2n` coordinates have norm `< 1 / 2`. -/
lemma truncateTailCoordinates_norm_lt_half_of_mem_ball
    {v : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hv :
      v ∈ Metric.ball (lastAxisVector (2 * n)) ((1 : ℝ) / 2)) :
    ‖truncateTailCoordinates (2 * n) 1 v‖ < (1 : ℝ) / 2 := by
  -- Truncation is `1`-Lipschitz, and the last-axis vector truncates to `0`.
  have hvdist : dist v (lastAxisVector (2 * n)) < (1 : ℝ) / 2 := by
    simpa [Metric.mem_ball] using hv
  have htruncdist :
      dist (truncateTailCoordinates (2 * n) 1 v) 0 ≤
        dist v (lastAxisVector (2 * n)) := by
    simpa [truncateTailCoordinates_lastAxisVector] using
      (truncateTailCoordinates_dist_le (K := 2 * n) v (lastAxisVector (2 * n)))
  exact lt_of_le_of_lt (by simpa [dist_eq_norm] using htruncdist) hvdist

/-- Helper for Problem 6-12: a direction within distance `1 / 2` of the last axis has positive
last coordinate, hence nonzero last coordinate. -/
lemma lastCoordinate_gt_half_of_mem_ball
    {v : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hv :
      v ∈ Metric.ball (lastAxisVector (2 * n)) ((1 : ℝ) / 2)) :
    (1 : ℝ) / 2 < v (Fin.last (2 * n)) := by
  -- The last coordinate differs from the last-axis value `1` by at most the ambient norm.
  have hvnorm : ‖v - lastAxisVector (2 * n)‖ < (1 : ℝ) / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hcoord :
      |v (Fin.last (2 * n)) - 1| ≤ ‖v - lastAxisVector (2 * n)‖ := by
    simpa [Real.norm_eq_abs, lastAxisVector, Pi.sub_apply, PiLp.single_apply] using
      (PiLp.norm_apply_le (v - lastAxisVector (2 * n)) (Fin.last (2 * n)))
  have habs : |v (Fin.last (2 * n)) - 1| < (1 : ℝ) / 2 :=
    lt_of_le_of_lt hcoord hvnorm
  have hleft : -((1 : ℝ) / 2) < v (Fin.last (2 * n)) - 1 :=
    (abs_lt.mp habs).1
  nlinarith

/-- Helper for Problem 6-12: record the first `2 * n` coordinates of a direction
`v ∈ ℝ^(2 * n + 1)`. -/
noncomputable def truncatedDirection
    (v : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  (EuclideanSpace.equiv (Fin (2 * n)) ℝ).symm fun i ↦ v (Fin.castSucc i)

/-- Helper for Problem 6-12: the codimension-one oblique projection along the line `ℝ v` onto the
last-coordinate hyperplane, written as a continuous linear map. -/
noncomputable def projectionAlongLastHyperplaneCLM
    (v : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  dropLastCoordinatesCLM -
    lastCoordinateCLM.smulRight ((v (Fin.last (2 * n)))⁻¹ • truncatedDirection v)

/-- Helper for Problem 6-12: the projection along `v` subtracts the unique multiple of `v` that
kills the last coordinate. -/
lemma projectionAlongLastHyperplaneCLM_apply
    (v x : EuclideanSpace ℝ (Fin (2 * n + 1))) (i : Fin (2 * n)) :
    projectionAlongLastHyperplaneCLM v x i =
      x (Fin.castSucc i) -
        (x (Fin.last (2 * n)) / v (Fin.last (2 * n))) * v (Fin.castSucc i) := by
  -- Expanding the linear map shows the coordinatewise projection formula directly.
  simp [projectionAlongLastHyperplaneCLM, dropLastCoordinatesCLM, lastCoordinateCLM,
    ambientCoordinateCLM, truncatedDirection, div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_assoc]

/-- Helper for Problem 6-12: the kernel of the oblique projection along `v` is exactly the line
spanned by `v`, provided the last coordinate of `v` is nonzero. -/
lemma projectionAlongLastHyperplaneCLM_eq_zero_iff_smul
    (v : EuclideanSpace ℝ (Fin (2 * n + 1)))
    (hv : v (Fin.last (2 * n)) ≠ 0)
    {x : EuclideanSpace ℝ (Fin (2 * n + 1))} :
    projectionAlongLastHyperplaneCLM v x = 0 ↔ ∃ a : ℝ, x = a • v := by
  constructor
  · intro hx
    refine ⟨x (Fin.last (2 * n)) / v (Fin.last (2 * n)), ?_⟩
    ext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hcoord : projectionAlongLastHyperplaneCLM v x i = 0 := by
        simpa using congrArg (fun y ↦ y i) hx
      rw [projectionAlongLastHyperplaneCLM_apply] at hcoord
      exact (sub_eq_zero.mp hcoord).trans (by simp [smul_eq_mul, mul_comm])
    · -- The chosen scalar matches the last coordinate by construction.
      simp [smul_eq_mul]
      field_simp [hv]
  · rintro ⟨a, rfl⟩
    ext i
    -- A vector on the line `ℝ v` is killed by the projection by a direct coordinate computation.
    rw [projectionAlongLastHyperplaneCLM_apply]
    simp [smul_eq_mul, hv]

/-- Helper for Problem 6-12: the oblique projection along `v` differs from standard truncation by
one explicit rank-one correction term. -/
lemma projectionAlongLastHyperplaneCLM_sub_truncateTail
    (v x : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    projectionAlongLastHyperplaneCLM (n := n) v x =
      truncateTailCoordinates (2 * n) 1 x -
        ((x (Fin.last (2 * n)) / v (Fin.last (2 * n))) •
          truncateTailCoordinates (2 * n) 1 v) := by
  -- Compare the retained coordinates on both sides after rewriting the truncation map.
  ext i
  have hcast : (i.castSucc : Fin (2 * n + 1)) = Fin.castAdd 1 i := by
    ext
    rfl
  simp [projectionAlongLastHyperplaneCLM_apply, truncateTailCoordinates_one_apply, hcast,
    smul_eq_mul]

/-- Helper for Problem 6-12: for a direction near the last axis, the corresponding oblique
projection is uniformly close to standard truncation once the last coordinate of the source point
is small. -/
lemma projectionAlongLastHyperplaneCLM_closeToTruncation_of_mem_ball
    {η : ℝ} (_hη : 0 < η)
    {v x : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hv :
      v ∈ Metric.ball (lastAxisVector (2 * n)) ((1 : ℝ) / 2))
    (hx : ‖x (Fin.last (2 * n))‖ < η) :
    dist (projectionAlongLastHyperplaneCLM (n := n) v x)
        (truncateTailCoordinates (2 * n) 1 x) < η := by
  -- Rewrite the projection error as one rank-one correction term.
  have hdist_le :
      dist (projectionAlongLastHyperplaneCLM (n := n) v x)
          (truncateTailCoordinates (2 * n) 1 x) ≤
        ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ *
          ‖truncateTailCoordinates (2 * n) 1 v‖ := by
    simpa [dist_eq_norm, projectionAlongLastHyperplaneCLM_sub_truncateTail, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc, norm_neg] using
      (norm_smul (x (Fin.last (2 * n)) / v (Fin.last (2 * n)))
        (truncateTailCoordinates (2 * n) 1 v)).le
  have htrunc : ‖truncateTailCoordinates (2 * n) 1 v‖ < (1 : ℝ) / 2 :=
    truncateTailCoordinates_norm_lt_half_of_mem_ball (n := n) hv
  have hlast : (1 : ℝ) / 2 < v (Fin.last (2 * n)) :=
    lastCoordinate_gt_half_of_mem_ball (n := n) hv
  have hvpos : 0 < v (Fin.last (2 * n)) := by
    linarith
  have hmul_le :
      ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ *
          ‖truncateTailCoordinates (2 * n) 1 v‖ ≤
        ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ * v (Fin.last (2 * n)) := by
    exact mul_le_mul_of_nonneg_left (htrunc.le.trans (le_of_lt hlast)) (norm_nonneg _)
  have hcancel :
      ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ * v (Fin.last (2 * n)) =
        ‖x (Fin.last (2 * n))‖ := by
    calc
      ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ * v (Fin.last (2 * n)) =
          (‖x (Fin.last (2 * n))‖ / ‖v (Fin.last (2 * n))‖) * v (Fin.last (2 * n)) := by
            rw [norm_div]
      _ = (‖x (Fin.last (2 * n))‖ / v (Fin.last (2 * n))) * v (Fin.last (2 * n)) := by
            simp [Real.norm_eq_abs, abs_of_pos hvpos]
      _ = ‖x (Fin.last (2 * n))‖ := by
            field_simp [ne_of_gt hvpos]
  have hcoord : ‖x (Fin.last (2 * n))‖ < η := by
    simpa using hx
  have hbound :
      ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ *
          ‖truncateTailCoordinates (2 * n) 1 v‖ ≤
        ‖x (Fin.last (2 * n))‖ := by
    calc
      ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ *
          ‖truncateTailCoordinates (2 * n) 1 v‖ ≤
        ‖x (Fin.last (2 * n)) / v (Fin.last (2 * n))‖ * v (Fin.last (2 * n)) := hmul_le
      _ = ‖x (Fin.last (2 * n))‖ := hcancel
  exact lt_of_le_of_lt (le_trans hdist_le hbound) hcoord

/-- Helper for Problem 6-12: if a direction lies outside the full ambient tangent-image range of
an embedding into `ℝ^(2n + 1)`, then projecting along that direction still yields an immersion
into `ℝ^(2n)`. -/
lemma isImmersion_compProjection_of_not_mem_ambientTangentRange
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G)
    {v : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hvNotRange : v ∉ Set.range (ambientTangentVector (n := n) (G := G)))
    (hvlast : v (Fin.last (2 * n)) ≠ 0) :
    IsImmersion
      (𝓡 n)
      (𝓡 (2 * n))
      ∞
      (fun x ↦ projectionAlongLastHyperplaneCLM (n := n) v (G x)) := by
  -- Route correction: reuse the chain-rule kernel computation from Theorem 6.19, but close the
  -- kernel line directly by contradicting `hvNotRange`.
  let P : EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    projectionAlongLastHyperplaneCLM (n := n) v
  let F : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x ↦ P (G x)
  have hGCont : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ G := hG.isImmersion.contMDiff
  have hFCont : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ F := by
    -- The projected map is smooth because it is the composition of `G` with a continuous linear
    -- map.
    simpa [F, P, Function.comp] using P.contMDiff.comp hGCont
  have hGInj :
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv hGCont).1 hG.isImmersion
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFCont).2 ?_
  intro x u w huw
  have hComp :
      mfderiv (𝓡 n) (𝓡 (2 * n)) F x = P.comp (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x) := by
    -- The chain rule identifies the derivative of the projected map.
    simpa [F, P, Function.comp] using
      (mfderiv_comp (x := x)
        (g := P)
        (f := G)
        (P.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
        (hGCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
  have hCompU :
      mfderiv (𝓡 n) (𝓡 (2 * n)) F x u =
        P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u) := by
    -- Evaluate the chain-rule identity on the first tangent vector.
    simpa [P] using congrArg (fun L ↦ L u) hComp
  have hCompW :
      mfderiv (𝓡 n) (𝓡 (2 * n)) F x w =
        P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) := by
    -- Evaluate the same identity on the second tangent vector.
    simpa [P] using congrArg (fun L ↦ L w) hComp
  have hKernelEq :
      P
        (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
          mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) = 0 := by
    -- Equality of projected derivative values forces the derivative of the tangent difference into
    -- the kernel of the projection.
    have hsub :
        mfderiv (𝓡 n) (𝓡 (2 * n)) F x u -
            mfderiv (𝓡 n) (𝓡 (2 * n)) F x w = 0 := by
      simp [huw]
    calc
      P
          (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) =
          P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u) -
            P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) := by
            exact
              P.map_sub
                (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u)
                (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w)
      _ =
          mfderiv (𝓡 n) (𝓡 (2 * n)) F x u -
            mfderiv (𝓡 n) (𝓡 (2 * n)) F x w := by
            rw [← hCompU, ← hCompW]
            rfl
      _ = 0 := hsub
  have hKernelDiff :
      P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x (u - w)) = 0 := by
    simpa [map_sub] using hKernelEq
  rcases (projectionAlongLastHyperplaneCLM_eq_zero_iff_smul (n := n) v hvlast).1 hKernelDiff with
    ⟨a, ha⟩
  have hAmbientZero : mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x (u - w) = 0 := by
    by_cases ha0 : a = 0
    · simpa [ha0] using ha
    · have hvInRange : v ∈ Set.range (ambientTangentVector (n := n) (G := G)) := by
        refine ⟨⟨x, a⁻¹ • (u - w)⟩, ?_⟩
        -- Rescale the tangent difference so that its image is exactly `v`.
        have hscale :
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x (a⁻¹ • (u - w)) = v := by
          calc
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x (a⁻¹ • (u - w)) =
                a⁻¹ • mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x (u - w) := by
                  rw [map_smul]
            _ = a⁻¹ • (a • v) := by
                  simpa using congrArg (fun z ↦ a⁻¹ • z) ha
            _ = v := by
                  have hmul : a⁻¹ * a = (1 : ℝ) := inv_mul_cancel₀ ha0
                  simp [smul_smul, hmul]
        simpa [ambientTangentVector_apply] using hscale
      exact False.elim (hvNotRange hvInRange)
  have hDiffZero : u - w = 0 := by
    -- Injectivity of the original embedding derivative kills the tangent difference itself.
    apply hGInj x
    simpa using hAmbientZero
  exact sub_eq_zero.mp hDiffZero

/-- Helper for Problem 6-12: dropping the last coordinate is `1`-Lipschitz on
`ℝ^(2n + 1)`. -/
lemma dist_truncateTailCoordinates_le
    (x y : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    dist (truncateTailCoordinates (2 * n) 1 x)
        (truncateTailCoordinates (2 * n) 1 y) ≤
      dist x y := by
  -- This is the codimension-one instance of the earlier truncation Lipschitz estimate.
  simpa using truncateTailCoordinates_dist_le (K := 2 * n) x y

/-- Helper for Problem 6-12: packing `(x, 0)` into `ℝ^(2n + 1)` gives a vector with zero last
coordinate. -/
lemma lastCoordinate_packEuclideanCoordinates_zero
    (x : EuclideanSpace ℝ (Fin (2 * n))) :
    packEuclideanCoordinates (2 * n) 1 (x, (0 : EuclideanSpace ℝ (Fin 1)))
      (Fin.last (2 * n)) = 0 := by
  -- Apply the inverse product equivalence and read off the one-dimensional second factor.
  have hsnd :
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := 1))
          (packEuclideanCoordinates (2 * n) 1 (x, (0 : EuclideanSpace ℝ (Fin 1))))).2 = 0 := by
    simpa [packEuclideanCoordinates] using
      congrArg Prod.snd
        (ContinuousLinearEquiv.apply_symm_apply
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := 1))
          (x, (0 : EuclideanSpace ℝ (Fin 1))))
  -- The unique coordinate on `Fin 1` is exactly the last coordinate in the packed model.
  have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin 1) ↦ y 0) hsnd
  simpa using h0

/-- Helper for Problem 6-12: in the critical dimension `N = 2n`, lift `f` to `ℝ^(2n + 1)`,
approximate by an embedding there, and project back along a near-vertical tangent-avoiding
direction. -/
lemma criticalDimensionUniformApproximationByImmersions
    (hpos : 0 < n)
    (f : C^∞⟮𝓡 n, M; 𝓡 (2 * n), EuclideanSpace ℝ (Fin (2 * n))⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮𝓡 n, M; 𝓡 (2 * n), EuclideanSpace ℝ (Fin (2 * n))⟯,
      IsImmersion (𝓡 n) (𝓡 (2 * n)) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  -- Route correction: instead of chasing tangent-bundle infrastructure, finish the sharp branch
  -- by one explicit lift-project argument around the existing embedding approximation owner.
  have hε4 : 0 < ε / 4 := by
    nlinarith
  have hLiftProdSelf :
      ContMDiff
        (𝓡 n)
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)) × EuclideanSpace ℝ (Fin 1)))
        ∞
        (fun x : M ↦ (f x, (0 : EuclideanSpace ℝ (Fin 1)))) := by
    simpa using
      f.contMDiff.prodMk_space
        (contMDiff_const :
          ContMDiff
            (𝓡 n)
            𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
            ∞
            (fun _ : M ↦ (0 : EuclideanSpace ℝ (Fin 1))))
  let fLift :
      C^∞⟮𝓡 n, M; 𝓡 (2 * n + 1), EuclideanSpace ℝ (Fin (2 * n + 1))⟯ :=
    ⟨fun x ↦ packEuclideanCoordinates (2 * n) 1 (f x, (0 : EuclideanSpace ℝ (Fin 1))), by
      simpa [Function.comp] using
        (packEuclideanCoordinates (2 * n) 1).toContinuousLinearMap.contMDiff.comp
          hLiftProdSelf⟩
  obtain ⟨G, hGEmb, hGClose⟩ :=
    approximateByEmbeddingsAboveCritical
      (n := n)
      (N := 2 * n + 1)
      (M := M)
      (by simp)
      fLift
      hε4
  obtain ⟨v, hvBall, hvNotRange⟩ :=
    existsNearVerticalDirectionOutsideAmbientTangentRange
      (n := n)
      (M := M)
      hGEmb
  have hvlast : v (Fin.last (2 * n)) ≠ 0 := by
    -- A vector in the chosen ball has strictly positive last coordinate.
    have hvpos : 0 < v (Fin.last (2 * n)) := by
      linarith [lastCoordinate_gt_half_of_mem_ball (n := n) hvBall]
    exact ne_of_gt hvpos
  let g : C^∞⟮𝓡 n, M; 𝓡 (2 * n), EuclideanSpace ℝ (Fin (2 * n))⟯ :=
    ⟨fun x ↦ projectionAlongLastHyperplaneCLM (n := n) v (G x), by
      simpa [Function.comp] using
        (projectionAlongLastHyperplaneCLM (n := n) v).contMDiff.comp G.contMDiff⟩
  refine ⟨g, ?_, ?_⟩
  · -- The chosen direction misses the entire ambient tangent range, so the projected map is an
    -- immersion by the kernel-line argument proved above.
    simpa [g] using
      isImmersion_compProjection_of_not_mem_ambientTangentRange
        (n := n)
        (M := M)
        hGEmb
        hvNotRange
        hvlast
  · intro x
    have hLiftTrunc :
        truncateTailCoordinates (2 * n) 1 (fLift x) = f x := by
      -- Truncating the lifted map simply discards the appended zero coordinate.
      change
        truncateTailCoordinates (2 * n) 1
            (packEuclideanCoordinates (2 * n) 1
              (f x, (0 : EuclideanSpace ℝ (Fin 1)))) =
          f x
      simpa using
        truncateTailCoordinates_packEuclideanCoordinates
          (N := 2 * n)
          (m := 1)
          (x := f x)
          (y := (0 : EuclideanSpace ℝ (Fin 1)))
    have hLiftLastZero :
        fLift x (Fin.last (2 * n)) = 0 := by
      -- The lifted map lands in the hyperplane with zero last coordinate.
      change
        packEuclideanCoordinates (2 * n) 1
            (f x, (0 : EuclideanSpace ℝ (Fin 1)))
            (Fin.last (2 * n)) = 0
      simpa using lastCoordinate_packEuclideanCoordinates_zero (n := n) (x := f x)
    have hLastClose :
        ‖G x (Fin.last (2 * n))‖ < ε / 4 := by
      -- The last coordinate of `G x` stays small because `G` is uniformly close to the zero-lift.
      have hcoord :
          ‖G x (Fin.last (2 * n)) - fLift x (Fin.last (2 * n))‖ ≤ dist (G x) (fLift x) := by
        simpa [dist_eq_norm] using
          (PiLp.norm_apply_le (G x - fLift x) (Fin.last (2 * n)))
      have hcoord' : ‖G x (Fin.last (2 * n))‖ ≤ dist (G x) (fLift x) := by
        simpa [hLiftLastZero] using hcoord
      exact lt_of_le_of_lt hcoord' (hGClose x)
    have hProjClose :
        dist (g x) (truncateTailCoordinates (2 * n) 1 (G x)) < ε / 4 := by
      -- The near-vertical projection stays close to standard truncation whenever the last
      -- coordinate is small.
      simpa [g] using
        projectionAlongLastHyperplaneCLM_closeToTruncation_of_mem_ball
          (n := n)
          hε4
          hvBall
          hLastClose
    have hTruncClose :
        dist (truncateTailCoordinates (2 * n) 1 (G x)) (f x) < ε / 4 := by
      -- Truncation is `1`-Lipschitz, and the truncated lift is exactly `f`.
      calc
        dist (truncateTailCoordinates (2 * n) 1 (G x)) (f x) =
            dist (truncateTailCoordinates (2 * n) 1 (G x))
              (truncateTailCoordinates (2 * n) 1 (fLift x)) := by
                rw [hLiftTrunc]
        _ ≤ dist (G x) (fLift x) :=
              dist_truncateTailCoordinates_le (n := n) (G x) (fLift x)
        _ < ε / 4 := hGClose x
    -- Combine the projection error and the truncation error by the triangle inequality.
    calc
      dist (g x) (f x) ≤
          dist (g x) (truncateTailCoordinates (2 * n) 1 (G x)) +
            dist (truncateTailCoordinates (2 * n) 1 (G x)) (f x) :=
        dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := add_lt_add hProjClose hTruncClose
      _ < ε := by
        nlinarith

/-- Problem 6-12: if `M` is a compact smooth `n`-manifold and `N ≥ 2n`, then every smooth map
`M → ℝ^N` can be uniformly approximated, to any prescribed positive constant error, by smooth
immersions. -/
theorem smooth_map_to_euclidean_can_be_uniformly_approximated_by_immersions
    (hN : 2 * n ≤ N) (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsImmersion (𝓡 n) (𝓡 N) ∞ g ∧ ∀ x : M, dist (g x) (f x) < ε := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨f, ?_, ?_⟩
    -- In dimension `0`, the immersion criterion reduces to injectivity on trivial tangent spaces.
    · exact (Manifold.is_immersion_iff_forall_injective_mfderiv f.contMDiff).2
        (fun x ↦ injective_mfderiv_zero_dimensional f x)
    · intro x
      simpa using hε
  · -- Route correction: split the positive-dimensional case into the easy branch `N ≥ 2n + 1`
    -- handled by the earlier embedding approximation owner, and the sharp branch `N = 2n`
    -- handled by a single codimension-one projection from an embedding in `ℝ^(2n + 1)`.
    have hPositive : 0 < n := Nat.pos_of_ne_zero hn
    rcases Nat.eq_or_lt_of_le hN with hEq | hLt
    · subst hEq
      -- In the critical branch, lift to `ℝ^(2n + 1)`, approximate by an embedding, and project
      -- back down along a near-vertical direction that avoids all tangent directions.
      exact criticalDimensionUniformApproximationByImmersions
        (n := n)
        (M := M)
        hPositive
        f
        hε
    · -- Above the critical dimension, a uniformly close embedding is already an immersion.
      exact embeddingApproximationGivesImmersionApproximation
        (n := n)
        (N := N)
        (M := M)
        (Nat.succ_le_of_lt hLt)
        f
        hε

end

end Manifold
