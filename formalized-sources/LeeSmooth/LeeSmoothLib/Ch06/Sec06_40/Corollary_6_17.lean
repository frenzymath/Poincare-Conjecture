import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch04.Sec04_24.Proposition_4_22
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_2
import LeeSmoothLib.Ch06.Sec06_40.Lemma_6_13
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Semantic recall note: `lean_leansearch` returned the canonical embedding owner
-- `exists_embedding_euclidean_of_compact` together with `Manifold.IsSmoothEmbedding`; the
-- source-facing approximation surface follows the local constant-`ε` Euclidean pattern from
-- Problem 6-12, split into boundaryless and with-boundary owners to match Lee's
-- "with or without boundary" statement in this repo.

namespace Manifold

noncomputable section

universe uM

section GraphHelpers

universe uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N m : ℕ}

/-- Helper for Corollary 6.17: if `e : M → ℝ^m` is a smooth embedding and
`f : M → ℝ^N` is smooth, then the graph map `x ↦ (e x, f x)` is a smooth embedding into the
product Euclidean target. -/
lemma smoothEmbedding_pair_of_leftEmbedding
    (f : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (he : IsSmoothEmbedding I (𝓡 m) ∞ e) :
    IsSmoothEmbedding I ((𝓡 m).prod (𝓡 N)) ∞ (fun x ↦ (e x, f x)) := by
  let Φ : M → EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) := fun x ↦ (e x, f x)
  have heCont : ContMDiff I (𝓡 m) ∞ e := he.isImmersion.contMDiff
  have hΦcont : ContMDiff I ((𝓡 m).prod (𝓡 N)) ∞ Φ := by
    -- The graph map is smooth because both components are smooth.
    simpa [Φ] using heCont.prodMk f.contMDiff
  have he_mfderiv :
      ∀ x : M, Function.Injective (mfderiv I (𝓡 m) e x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).1 he.isImmersion
  have hImm : IsImmersion I ((𝓡 m).prod (𝓡 N)) ∞ Φ := by
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hΦcont).2 ?_
    intro x v w hvw
    have hDeriv :
        mfderiv I ((𝓡 m).prod (𝓡 N)) Φ x =
          (mfderiv I (𝓡 m) e x).prod (mfderiv I (𝓡 N) (fun y : M ↦ f y) x) := by
      -- The derivative of a product map splits componentwise.
      simpa [Φ] using
        (mfderiv_prodMk
          (heCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          ((f.contMDiff x).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hFirst :
        ((mfderiv I ((𝓡 m).prod (𝓡 N)) Φ x) v).1 =
          ((mfderiv I ((𝓡 m).prod (𝓡 N)) Φ x) w).1 := by
      exact congrArg Prod.fst hvw
    -- Injectivity of the first derivative component already forces `v = w`.
    exact he_mfderiv x <| by
      simpa [hDeriv] using hFirst
  have hGraphEmb : Topology.IsEmbedding (fun x : M ↦ (x, f x)) :=
    isEmbedding_graph f.contMDiff.continuous
  have hProdEmb :
      Topology.IsEmbedding
        (Prod.map e (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))) :=
    he.isEmbedding.prodMap Topology.IsEmbedding.id
  have hEmb : Topology.IsEmbedding Φ := by
    -- Factor the graph through the known embedding `e` in the first coordinate.
    simpa [Φ, Function.comp] using hProdEmb.comp hGraphEmb
  exact ⟨hImm, hEmb⟩

/-- Helper for Corollary 6.17: if `e : M → ℝ^m` is a smooth embedding and
`f : M → ℝ^N` is smooth, then the graph map `x ↦ (f x, e x)` is a smooth embedding into the
product Euclidean target. -/
lemma smoothEmbedding_pair_of_rightEmbedding
    (f : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (he : IsSmoothEmbedding I (𝓡 m) ∞ e) :
    IsSmoothEmbedding I ((𝓡 N).prod (𝓡 m)) ∞ (fun x ↦ (f x, e x)) := by
  let σ :
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N)) ≃ₘ^∞⟮
        ((𝓡 m).prod (𝓡 N)),
        ((𝓡 N).prod (𝓡 m))⟯
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)) :=
    Diffeomorph.prodComm
      (𝓡 m)
      (𝓡 N)
      (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin N))
      ∞
  have hLeft :
      IsSmoothEmbedding
        I
        ((𝓡 m).prod (𝓡 N))
        ∞
        (fun x ↦ (e x, f x)) :=
    smoothEmbedding_pair_of_leftEmbedding f he
  have hSwapImm :
      IsImmersion
        ((𝓡 m).prod (𝓡 N))
        ((𝓡 N).prod (𝓡 m))
        ∞
        (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) ↦ (p.2, p.1)) := by
    -- Route correction: use the canonical product-commuting diffeomorphism instead of a
    -- theorem-local product-model linear-equivalence proof.
    have hSwapCont :
        ContMDiff
          ((𝓡 m).prod (𝓡 N))
          ((𝓡 N).prod (𝓡 m))
          ∞
          (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) ↦ (p.2, p.1)) := by
      simpa using
        (contMDiff_snd.prodMk contMDiff_fst :
          ContMDiff
            ((𝓡 m).prod (𝓡 N))
            ((𝓡 N).prod (𝓡 m))
            ∞
            (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) ↦ (p.2, p.1)))
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hSwapCont).2 ?_
    intro x v w hvw
    have hDeriv :
        mfderiv
          ((𝓡 m).prod (𝓡 N))
          ((𝓡 N).prod (𝓡 m))
          (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) ↦ (p.2, p.1))
          x =
        (mfderiv
          ((𝓡 m).prod (𝓡 N))
          (𝓡 N)
          (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) ↦ p.2)
          x).prod
        (mfderiv
          ((𝓡 m).prod (𝓡 N))
          (𝓡 m)
          (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) ↦ p.1)
          x) := by
      simpa using
        (mfderiv_prodMk
          ((contMDiff_snd x).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          ((contMDiff_fst x).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hFirst : v.1 = w.1 := by
      have hSecondComponent := congrArg Prod.snd hvw
      simpa [hDeriv, mfderiv_fst] using hSecondComponent
    have hSecond : v.2 = w.2 := by
      have hFirstComponent := congrArg Prod.fst hvw
      simpa [hDeriv, mfderiv_snd] using hFirstComponent
    exact Prod.ext hFirst hSecond
  have hSwapEmb :
      Topology.IsEmbedding
        (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin N) ↦ (p.2, p.1)) := by
    -- The same diffeomorphism is a homeomorphism, hence a topological embedding.
    simpa [σ] using σ.toHomeomorph.isEmbedding
  have hImm :
      IsImmersion
        I
        ((𝓡 N).prod (𝓡 m))
        ∞
        (fun x ↦ (f x, e x)) := by
    -- Compose the left graph embedding with the product-factor swap.
    simpa [Function.comp] using IsImmersion.ex416_comp hSwapImm hLeft.isImmersion
  have hEmb : Topology.IsEmbedding (fun x ↦ (f x, e x)) := by
    -- Topological embedding is preserved by composition with the swap homeomorphism.
    simpa [Function.comp] using hSwapEmb.comp hLeft.isEmbedding
  exact ⟨hImm, hEmb⟩

end GraphHelpers

section CompactApproximation

universe uH

variable {n N : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [CompactSpace M]
variable [ChartedSpace H M] [IsManifold I ∞ M]

/-- Helper for Corollary 6.17: unpack the induced manifold structure and source-to-range
diffeomorphism attached to the range of a smooth embedding. -/
theorem smoothEmbeddingRangeData {k : ℕ} {F : M → EuclideanSpace ℝ (Fin k)}
    (hF : IsSmoothEmbedding I (𝓡 k) ∞ F) :
    ∃ cs : ChartedSpace H (Set.range F),
      ∃ hs : IsManifold I ∞ (Set.range F),
        let _ : ChartedSpace H (Set.range F) := cs
        let _ : IsManifold I ∞ (Set.range F) := hs
        IsSmoothEmbedding I (𝓡 k) ∞
          (Subtype.val : Set.range F → EuclideanSpace ℝ (Fin k)) ∧
          ∃ Φ : M ≃ₘ⟮I, I⟯ Set.range F, ∀ x, (Φ x : EuclideanSpace ℝ (Fin k)) = F x := by
  -- Proposition 5.2 already constructs the induced range manifold structure, so only its
  -- existential packaging needs to be normalized to the tuple used below.
  rcases smooth_embedding_range_has_induced_manifold_structure hF with ⟨cs, hcs⟩
  have hRange :
      ∃ hs : IsManifold I ∞ (Set.range F),
        let _ : ChartedSpace H (Set.range F) := cs
        let _ : IsManifold I ∞ (Set.range F) := hs
        IsSmoothEmbedding I (𝓡 k) ∞
          (Subtype.val : Set.range F → EuclideanSpace ℝ (Fin k)) ∧
          ∃ Φ : M ≃ₘ⟮I, I⟯ Set.range F, ∀ x, (Φ x : EuclideanSpace ℝ (Fin k)) = F x := by
    -- The induced-image owner unfolds exactly to the concrete range data needed here.
    simpa [IsInducedImageManifoldStructure] using hcs
  rcases hRange with ⟨hs, hSubtype, Φ, hΦ⟩
  exact ⟨cs, hs, hSubtype, Φ, hΦ⟩

/-- Helper for Corollary 6.17: a continuous Euclidean-valued map on a compact source manifold has
a uniform norm bound on its range. -/
lemma existsUniformNormBound {m : ℕ} {F : M → EuclideanSpace ℝ (Fin m)}
    (hF : Continuous F) :
    ∃ C : ℝ, ∀ x : M, ‖F x‖ ≤ C := by
  -- Compactness turns the Euclidean image into a bounded set.
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

/-- Helper for Corollary 6.17: pack `ℝ^N × ℝ^m` into `ℝ^(N + m)` by placing the `ℝ^N`
coordinates first and the `ℝ^m` coordinates last. -/
noncomputable def packEuclideanCoordinates (N m : ℕ)
    : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + m)) :=
  EuclideanSpace.finAddEquivProd.symm

/-- Helper for Corollary 6.17: forget the last `m` coordinates of `ℝ^(N + m)`. -/
noncomputable def truncateTailCoordinates (N m : ℕ)
    : EuclideanSpace ℝ (Fin (N + m)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearMap.fst ℝ
    (EuclideanSpace ℝ (Fin N))
    (EuclideanSpace ℝ (Fin m)) |>.comp
      EuclideanSpace.finAddEquivProd.toContinuousLinearMap

/-- Helper for Corollary 6.17: packing followed by truncation recovers the original `ℝ^N`
component. -/
lemma truncateTailCoordinates_packEuclideanCoordinates
    {m : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin m)) :
    truncateTailCoordinates N m (packEuclideanCoordinates N m (x, y)) = x := by
  -- The first `N` packed coordinates are exactly the original `ℝ^N` coordinates.
  let e :
      EuclideanSpace ℝ (Fin (N + m)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  simpa [truncateTailCoordinates, packEuclideanCoordinates, e] using
    congrArg Prod.fst
      (ContinuousLinearEquiv.apply_symm_apply e (x, y))

/-- Helper for Corollary 6.17: forget the first `N` packed coordinates of `ℝ^(N + m)`. -/
noncomputable def tailCoordinates (N m : ℕ)
    : EuclideanSpace ℝ (Fin (N + m)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ContinuousLinearMap.snd ℝ
    (EuclideanSpace ℝ (Fin N))
    (EuclideanSpace ℝ (Fin m)) |>.comp
      EuclideanSpace.finAddEquivProd.toContinuousLinearMap

/-- Helper for Corollary 6.17: packing followed by tail-coordinate recovery recovers the original
`ℝ^m` component. -/
lemma tailCoordinates_packEuclideanCoordinates
    {m : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin m)) :
    tailCoordinates N m (packEuclideanCoordinates N m (x, y)) = y := by
  -- The last `m` packed coordinates are exactly the original `ℝ^m` coordinates.
  let e :
      EuclideanSpace ℝ (Fin (N + m)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  simpa [tailCoordinates, packEuclideanCoordinates, e] using
    congrArg Prod.snd
      (ContinuousLinearEquiv.apply_symm_apply e (x, y))

/-- Helper for Corollary 6.17: dropping exactly one tail coordinate keeps the first `K`
coordinates unchanged. -/
lemma truncateTailCoordinates_one_apply {K : ℕ}
    (x : EuclideanSpace ℝ (Fin (K + 1))) (i : Fin K) :
    truncateTailCoordinates K 1 x i = x (Fin.castAdd 1 i) := by
  -- Unfold the packed-coordinate truncation and read off the retained coordinate.
  simp [truncateTailCoordinates]

/-- Helper for Corollary 6.17: repeated tail truncation can be normalized by first dropping one
coordinate and then dropping the remaining `m` tail coordinates. -/
lemma truncateTailCoordinates_comp_one (N m : ℕ) :
    truncateTailCoordinates N (m + 1) =
      (truncateTailCoordinates N m).comp (truncateTailCoordinates (N + m) 1) := by
  -- Both truncation operators keep exactly the first `N` coordinates, so extensionality reduces
  -- the comparison to coordinatewise simplification.
  ext x i
  simp [truncateTailCoordinates, Fin.castAdd_castAdd]

/-- Helper for Corollary 6.17: the standard last-axis direction in `ℝ^(K + 1)` has zero first
`K` coordinates and last coordinate `1`. -/
noncomputable def lastAxisVector (K : ℕ) : EuclideanSpace ℝ (Fin (K + 1)) :=
  EuclideanSpace.single (Fin.last K) (1 : ℝ)

/-- Helper for Corollary 6.17: the standard last-axis vector truncates to zero. -/
lemma truncateTailCoordinates_lastAxisVector (K : ℕ) :
    truncateTailCoordinates K 1 (lastAxisVector K) = 0 := by
  -- All retained coordinates of the last-axis vector vanish.
  ext i
  have hlt : Fin.castAdd 1 i < Fin.last K := by
    simpa [Fin.lt_iff_val_lt_val] using i.2
  have hne : Fin.castAdd 1 i ≠ Fin.last K := Fin.ne_last_of_lt hlt
  simp [lastAxisVector, truncateTailCoordinates_one_apply, EuclideanSpace.single_apply, hne]

/-- Helper for Corollary 6.17: the packed codimension-one oblique projection written as a
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

/-- Helper for Corollary 6.17: the packed oblique projection is continuous because its source and
target are finite-dimensional. -/
private noncomputable def obliqueProjectionToLastHyperplaneCLM {K : ℕ} (hK : 0 < K + 1)
    (v : EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin K) where
  toLinearMap := obliqueProjectionToLastHyperplaneLinearMap hK v
  cont := by
    exact
      (obliqueProjectionToLastHyperplaneLinearMap hK v).continuous_of_finiteDimensional

/-- Helper for Corollary 6.17: the packed oblique projection subtracts the unique multiple of
`v` that kills the last coordinate. -/
private lemma obliqueProjectionToLastHyperplaneCLM_apply {K : ℕ} (hK : 0 < K + 1)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) (i : Fin K) :
    obliqueProjectionToLastHyperplaneCLM hK v x i =
      x (Fin.castAdd 1 i) -
        (x (Fin.last K) / v (Fin.last K)) * v (Fin.castAdd 1 i) := by
  -- The continuous linear map is defined from this coordinate formula.
  rfl

/-- Helper for Corollary 6.17: the packed oblique projection is the standard tail truncation plus
one rank-one correction term. -/
lemma obliqueProjectionToLastHyperplaneCLM_sub_truncateTail {K : ℕ} (hK : 0 < K + 1)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) :
    obliqueProjectionToLastHyperplaneCLM hK v x =
      truncateTailCoordinates K 1 x -
        ((x (Fin.last K) / v (Fin.last K)) • truncateTailCoordinates K 1 v) := by
  -- Compare the retained coordinates on both sides after rewriting the truncation map.
  ext i
  simp [obliqueProjectionToLastHyperplaneCLM_apply, truncateTailCoordinates_one_apply, smul_eq_mul]

/-- Helper for Corollary 6.17: the packed oblique projection error is controlled by the size of
its rank-one correction term. -/
lemma obliqueProjectionToLastHyperplaneCLM_dist_le_scale {K : ℕ} (hK : 0 < K + 1)
    (v x : EuclideanSpace ℝ (Fin (K + 1))) :
    dist (obliqueProjectionToLastHyperplaneCLM hK v x) (truncateTailCoordinates K 1 x) ≤
      ‖x (Fin.last K) / v (Fin.last K)‖ * ‖truncateTailCoordinates K 1 v‖ := by
  -- Rewrite the difference as exactly one scalar multiple of the truncated direction.
  simpa [dist_eq_norm, obliqueProjectionToLastHyperplaneCLM_sub_truncateTail, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc, norm_neg] using
    (norm_smul (x (Fin.last K) / v (Fin.last K)) (truncateTailCoordinates K 1 v)).le

/-- Helper for Corollary 6.17: the public oblique projection from Lemma 6.13 agrees with the
local continuous-linear-map spelling used for the quantitative estimates in this file. -/
lemma obliqueProjectionToLastHyperplane_eq_clm {K : ℕ}
    (v x : EuclideanSpace ℝ (Fin (K + 1))) :
    obliqueProjectionToLastHyperplane (Nat.succ_pos K) v x =
      obliqueProjectionToLastHyperplaneCLM (Nat.succ_pos K) v x := by
  -- Both projection spellings are definitionally the same coordinate formula after unfolding.
  ext i
  simpa [obliqueProjectionToLastHyperplaneCLM, obliqueProjectionToLastHyperplaneLinearMap] using
    (obliqueProjectionToLastHyperplane_apply (Nat.succ_pos K) v x i)

/-- Helper for Corollary 6.17: dropping a single last coordinate is `1`-Lipschitz on
`ℝ^(K + 1)`. -/
private lemma truncateTailCoordinates_dist_le_one {K : ℕ}
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
      (Fin.sum_univ_add fun i : Fin (K + 1) ↦ z i ^ (2 : ℕ))
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

/-- Helper for Corollary 6.17: if a direction lies within distance `δ` of the last axis, then the
retained first `K` coordinates have norm `< δ`. -/
lemma truncateTailCoordinates_norm_lt_of_mem_ball {K : ℕ} {δ : ℝ}
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
      (truncateTailCoordinates_dist_le_one v (lastAxisVector K))
  exact lt_of_le_of_lt (by simpa [dist_eq_norm] using htruncdist) hvdist

/-- Helper for Corollary 6.17: a direction within distance `1 / 2` of the last axis has last
coordinate strictly bigger than `1 / 2`. -/
lemma lastCoordinate_gt_half_of_mem_ball {K : ℕ}
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
  have hlower : 1 - ‖v - lastAxisVector K‖ ≤ v (Fin.last K) := by
    have hcoordLower : -‖v - lastAxisVector K‖ ≤ v (Fin.last K) - 1 :=
      (abs_le.mp hcoord).1
    nlinarith
  have hhalf : (1 : ℝ) / 2 < 1 - ‖v - lastAxisVector K‖ := by
    nlinarith
  exact lt_of_lt_of_le hhalf hlower

/-- Helper for Corollary 6.17: on a bounded set, any oblique projection whose direction is close
to the last axis is uniformly close to the standard coordinate truncation. -/
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
      -- Shrinking the ball radius preserves the near-last-axis control needed for the
      -- denominator estimate.
      rcases hv with hv
      simpa [Metric.mem_ball, dist_eq_norm] using lt_of_lt_of_le
        (by simpa [Metric.mem_ball, dist_eq_norm] using hv)
        hδhalf
    have htrunc :
        ‖truncateTailCoordinates K 1 v‖ < min ((1 : ℝ) / 2) (η / (4 * R)) :=
      truncateTailCoordinates_norm_lt_of_mem_ball hv
    have hlast : (1 : ℝ) / 2 < v (Fin.last K) :=
      lastCoordinate_gt_half_of_mem_ball hvHalf
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

/-- Helper for Corollary 6.17: Lemma 6.13 lets us pick a good oblique-projection direction inside
any prescribed ball around the last axis. -/
lemma existsGoodObliqueDirectionNearLastAxis {K : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (K + 1)))}
    [ChartedSpace H S]
    [IsManifold I ∞ S]
    (hSubtype :
      IsSmoothEmbedding I (𝓡 (K + 1)) ∞ (Subtype.val : S → EuclideanSpace ℝ (Fin (K + 1))))
    (hK : 2 * n + 1 ≤ K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : EuclideanSpace ℝ (Fin (K + 1)),
      v ∈ Metric.ball (lastAxisVector K) δ ∧
        @ObliqueProjectionDirectionRestrictsToInjectiveImmersion
          (K + 1)
          (EuclideanSpace ℝ (Fin n))
          inferInstance
          inferInstance
          H
          inferInstance
          I
          S
          inferInstance
          (Nat.succ_pos K)
          v := by
  have hDense :
      Dense
        {v : EuclideanSpace ℝ (Fin (K + 1)) |
          @ObliqueProjectionDirectionRestrictsToInjectiveImmersion
            (K + 1)
            (EuclideanSpace ℝ (Fin n))
            inferInstance
            inferInstance
            H
            inferInstance
            I
            S
            inferInstance
            (Nat.succ_pos K)
            v} := by
    have hdim :
        2 * Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1 < K + 1 := by
      simpa using Nat.lt_succ_of_le hK
    simpa using
      dense_oblique_projection_directions_restrict_to_injective_immersion
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

/-- Helper for Corollary 6.17: forgetting zero tail coordinates does nothing. -/
lemma truncateTailCoordinates_zero_apply
    (x : EuclideanSpace ℝ (Fin N)) :
    truncateTailCoordinates N 0 x = x := by
  -- With no tail coordinates to forget, the Euclidean splitting is the identity.
  ext i
  change x (Fin.castAdd 0 i) = x i
  simp

/-- Helper for Corollary 6.17: tail truncation is `1`-Lipschitz for any number of discarded
coordinates. -/
lemma truncateTailCoordinates_dist_le {m : ℕ}
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
      have hDrop :
          dist (truncateTailCoordinates (N + m) 1 x)
              (truncateTailCoordinates (N + m) 1 y) ≤
            dist x y :=
        truncateTailCoordinates_dist_le_one x y
      exact
        (ihm _ _).trans hDrop

/-- Helper for Corollary 6.17: one compact codimension-drop step replaces a smooth embedding into
`ℝ^(K + 1)` by a nearby smooth embedding into `ℝ^K`. -/
lemma existsApproximateCodimensionDropStep {K : ℕ}
    {G : M → EuclideanSpace ℝ (Fin (K + 1))}
    (hG : IsSmoothEmbedding I (𝓡 (K + 1)) ∞ G)
    (hK : 2 * n + 1 ≤ K)
    {η : ℝ} (hη : 0 < η) :
    ∃ g : M → EuclideanSpace ℝ (Fin K),
      IsSmoothEmbedding I (𝓡 K) ∞ g ∧
        ∀ x : M, dist (g x) (truncateTailCoordinates K 1 (G x)) < η := by
  let S : Set (EuclideanSpace ℝ (Fin (K + 1))) := Set.range G
  obtain ⟨cs, hs, hSubtype, Φ, hΦ_apply⟩ :=
    smoothEmbeddingRangeData hG
  let _ : ChartedSpace H S := cs
  let _ : IsManifold I ∞ S := hs
  let _ : CompactSpace S := Homeomorph.compactSpace Φ.toHomeomorph
  obtain ⟨C, hC⟩ :=
    existsUniformNormBound hSubtype.isEmbedding.continuous
  obtain ⟨δ, hδ, hApproximateProjection⟩ :=
    obliqueProjectionNearLastAxis_dist_lt_truncateTail hη
  obtain ⟨v, hvBall, hvGood⟩ :=
    existsGoodObliqueDirectionNearLastAxis hSubtype hK hδ
  let ψ : S → EuclideanSpace ℝ (Fin K) :=
    fun p ↦ obliqueProjectionToLastHyperplane (Nat.succ_pos K) v p.1
  have hψImmersion :
      IsImmersion I (𝓡 K) ∞ ψ := by
    -- Lemma 6.13 gives the projected range map as an injective immersion.
    simpa [ψ] using hvGood.isImmersion
  have hψ :
      IsSmoothEmbedding I (𝓡 K) ∞ ψ := by
    -- Compactness of the range upgrades the injective immersion to a smooth embedding.
    exact smooth_embedding_of_compact_source_injective_isImmersion hvGood.injective hψImmersion
  have hΦ :
      IsSmoothEmbedding
        I
        I
        ∞
        Φ := by
    -- The source-to-range diffeomorphism is already a smooth embedding.
    exact ⟨IsLocalDiffeomorph.isImmersion Φ.isLocalDiffeomorph, Φ.toHomeomorph.isEmbedding⟩
  refine ⟨ψ ∘ Φ, ?_, ?_⟩
  · -- Compose the range embedding with the range diffeomorphism to return to `M`.
    simpa [Function.comp] using Manifold.IsSmoothEmbedding.comp hψ hΦ
  · intro x
    -- The chosen oblique projection is uniformly close to standard truncation on the compact
    -- embedded range.
    simpa [Function.comp, ψ, hΦ_apply x, obliqueProjectionToLastHyperplane_eq_clm] using
      hApproximateProjection hvBall (hC (Φ x))

/-- Helper for Corollary 6.17: iterating the compact codimension-drop step compresses a smooth
embedding in `ℝ^(N + m)` to a nearby smooth embedding in `ℝ^N`. -/
lemma existsApproximateCompressionToBase {m : ℕ}
    {G : M → EuclideanSpace ℝ (Fin (N + m))}
    (hG : IsSmoothEmbedding I (𝓡 (N + m)) ∞ G)
    (hN : 2 * n + 1 ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → EuclideanSpace ℝ (Fin N),
      IsSmoothEmbedding I (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (truncateTailCoordinates N m (G x)) < ε := by
  induction m generalizing ε with
  | zero =>
      refine ⟨G, ?_, ?_⟩
      · -- With no tail coordinates, the original embedding is already the target one.
        simpa using hG
      · intro x
        -- The approximation error is zero in the base case.
        simpa [truncateTailCoordinates_zero_apply] using hε
  | succ m ih =>
      have hHalf : 0 < ε / 2 := by
        positivity
      obtain ⟨g₁, hg₁, hg₁Approx⟩ :=
        existsApproximateCodimensionDropStep
          hG
          (le_trans hN (Nat.le_add_right N m))
          hHalf
      obtain ⟨g, hg, hgApprox⟩ :=
        ih hg₁ hHalf
      refine ⟨g, hg, ?_⟩
      intro x
      have hCompress :
          dist
            (truncateTailCoordinates N m (g₁ x))
            (truncateTailCoordinates N m (truncateTailCoordinates (N + m) 1 (G x))) <
          ε / 2 := by
        -- The remaining truncation is `1`-Lipschitz, so the first approximation error does not
        -- grow under further coordinate drops.
        exact
          lt_of_le_of_lt
            (truncateTailCoordinates_dist_le
              (g₁ x)
              (truncateTailCoordinates (N + m) 1 (G x)))
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

/-- Helper for Corollary 6.17: after swapping the graph factors and packing coordinates, the map
`x ↦ (f x, e x)` becomes a smooth embedding into one Euclidean target. -/
lemma packedGraph_isSmoothEmbedding
    {m : ℕ}
    (f : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {e : M → EuclideanSpace ℝ (Fin m)}
    (he : IsSmoothEmbedding I (𝓡 m) ∞ e) :
    IsSmoothEmbedding
      I
      (𝓡 (N + m))
      ∞
      (fun x ↦ packEuclideanCoordinates N m (f x, e x)) := by
  let G : M → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) := fun x ↦ (f x, e x)
  let F : M → EuclideanSpace ℝ (Fin (N + m)) := fun x ↦ packEuclideanCoordinates N m (G x)
  have hGContSelf :
      ContMDiff
        I
        (𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)))
        ∞
        G := by
    -- Build the graph directly in the ambient product space to avoid product-model transport.
    simpa [G] using f.contMDiff.prodMk_space he.isImmersion.contMDiff
  have hFCont : ContMDiff I (𝓡 (N + m)) ∞ F := by
    -- The packed graph is smooth because packing is a continuous linear equivalence.
    simpa [F, G, Function.comp] using
      (packEuclideanCoordinates N m).toContinuousLinearMap.contMDiff.comp
        hGContSelf
  have hTailCompEq : (fun x : M ↦ tailCoordinates N m (F x)) = e := by
    -- Tail coordinates recover the embedding component of the packed graph pointwise.
    funext x
    simp [F, G, tailCoordinates_packEuclideanCoordinates]
  have heDerivInj :
      ∀ x : M, Function.Injective (mfderiv I (𝓡 m) e x) :=
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
  have hFImm : IsImmersion I (𝓡 (N + m)) ∞ F := by
    -- Route correction: recover derivative injectivity by postcomposing with `tailCoordinates`,
    -- instead of proving an ambient smooth-embedding theorem for `packEuclideanCoordinates`.
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFCont).2 ?_
    intro x u w huw
    have hCompRaw :
        mfderiv I (𝓡 m) (fun y : M ↦ tailCoordinates N m (F y)) x =
          (tailCoordinates N m).comp (mfderiv I (𝓡 (N + m)) F x) := by
      -- The chain rule differentiates `tailCoordinates ∘ F = e`.
      simpa [Function.comp] using
        (mfderiv_comp
          x
          ((tailCoordinates N m).contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (hFCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hComp :
        mfderiv I (𝓡 m) e x =
          (tailCoordinates N m).comp (mfderiv I (𝓡 (N + m)) F x) := by
      -- Rewrite the recovered tail-coordinate map to the original embedding.
      rw [← hTailCompEq]
      exact hCompRaw
    have hCompU :
        mfderiv I (𝓡 m) e x u =
          tailCoordinates N m (mfderiv I (𝓡 (N + m)) F x u) := by
      -- Evaluate the chain-rule identity on the first tangent vector.
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L u) hComp
    have hCompW :
        mfderiv I (𝓡 m) e x w =
          tailCoordinates N m (mfderiv I (𝓡 (N + m)) F x w) := by
      -- Evaluate the same identity on the second tangent vector.
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w) hComp
    exact heDerivInj x <| by
      rw [hCompU, hCompW, huw]
  -- Compactness of the source upgrades the injective immersion to a smooth embedding.
  simpa [F] using
    (smooth_embedding_of_compact_source_injective_isImmersion hFInj hFImm)

/-- Helper for Corollary 6.17: once a compact source manifold is smoothly embedded in some
Euclidean space `ℝ^m`, the remaining approximation problem is exactly the compact
codimension-drop step for the packed graph embedding into `ℝ^(N + m)`. -/
lemma existsUniformApproximationByEmbeddings_ofSmoothEmbedding
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {m : ℕ}
    {e : M → EuclideanSpace ℝ (Fin m)}
    (he : IsSmoothEmbedding I (𝓡 m) ∞ e)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮I, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding I (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  let G₀ : M → EuclideanSpace ℝ (Fin (N + m)) :=
    fun x ↦ packEuclideanCoordinates N m (f x, e x)
  have hGraph :
      IsSmoothEmbedding
        I
        (𝓡 (N + m))
        ∞
        G₀ := by
    -- The graph of `(f, e)` is a smooth embedding after swapping and packing coordinates.
    simpa [G₀] using packedGraph_isSmoothEmbedding f he
  have hProjection :
      ∀ x : M, truncateTailCoordinates N m (G₀ x) = f x := by
    intro x
    -- The standard coordinate truncation on the packed graph already recovers `f`.
    simpa [G₀] using
      truncateTailCoordinates_packEuclideanCoordinates (f x) (e x)
  -- Route correction: the graph front end is now entirely in the packed ambient
  -- `ℝ^(N + m)`, and the compact range bound is attached to that packed graph itself.
  -- The remaining step is exactly the iterated compact codimension-drop lemma on the packed graph.
  have hCompression :
      ∃ g : M → EuclideanSpace ℝ (Fin N),
        IsSmoothEmbedding I (𝓡 N) ∞ g ∧
          ∀ x : M, dist (g x) (truncateTailCoordinates N m (G₀ x)) < ε :=
    existsApproximateCompressionToBase hGraph hN hε
  obtain ⟨g, hg, hgApprox⟩ := hCompression
  refine ⟨⟨g, hg.isImmersion.contMDiff⟩, ?_, ?_⟩
  · -- Package the resulting function-valued embedding as a smooth map.
    simpa using hg
  · intro x
    -- The final truncation of the packed graph is exactly the original map `f`.
    simpa [hProjection x] using hgApprox x

end CompactApproximation

section Boundaryless

variable {n N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [CompactSpace M]
variable [TopologicalManifold n M] [IsManifold (𝓡 n) ∞ M]

/-- Boundaryless companion to Corollary 6.17: if `M` is a compact smooth boundaryless
`n`-manifold and `N ≥ 2 * n + 1`, then every smooth map from `M` to `ℝ^N` can be uniformly
approximated, to any prescribed positive constant error, by smooth embeddings. -/
theorem smooth_map_to_euclidean_can_be_uniformly_approximated_by_embeddings_boundaryless
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding (𝓡 n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  obtain ⟨m, e, heCont, heClosed, heInj⟩ :=
    by
      have hEmbedding :
          ∃ m : ℕ, ∃ e : M → EuclideanSpace ℝ (Fin m),
            ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧
              Topology.IsClosedEmbedding e ∧
                ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 m) e x) := by
        simpa using exists_embedding_euclidean_of_compact
      exact hEmbedding
  have he : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ e := by
    -- Repackage mathlib's compact Whitney theorem into the local smooth-embedding API.
    refine ⟨?_, heClosed.isEmbedding⟩
    exact (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).2 heInj
  -- Feed the arbitrary compact Euclidean embedding into the theorem-local compression result.
  have hApprox :
      ∃ g : C^∞⟮𝓡 n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
        IsSmoothEmbedding (𝓡 n) (𝓡 N) ∞ g ∧
          ∀ x : M, dist (g x) (f x) < ε :=
    existsUniformApproximationByEmbeddings_ofSmoothEmbedding hN f he hε
  exact hApprox

end Boundaryless

section WithBoundary

variable {n N : ℕ}
variable {M : Type uM} [TopologicalSpace M] [CompactSpace M] [SmoothManifoldWithBoundary n M]

/-- Corollary 6.17: suppose `M` is a compact smooth `n`-manifold with or without boundary. If
`N ≥ 2 * n + 1`, then every smooth map from `M` to `ℝ^N` can be uniformly approximated, to any
prescribed positive constant error, by smooth embeddings. The boundaryless case is recorded
separately in `smooth_map_to_euclidean_can_be_uniformly_approximated_by_embeddings_boundaryless`,
while this theorem is the repo's with-boundary owner. -/
theorem smoothMapToEuclideanCanBeUniformlyApproximatedByEmbeddings_ofWhitneyEmbedding
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮leeBoundaryModelWithCorners n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮leeBoundaryModelWithCorners n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε := by
  obtain ⟨m, e, heCont, heClosed, heInj⟩ :=
    by
      have hEmbedding :
          ∃ m : ℕ, ∃ e : M → EuclideanSpace ℝ (Fin m),
            ContMDiff (leeBoundaryModelWithCorners n) (𝓡 m) ∞ e ∧
              Topology.IsClosedEmbedding e ∧
                ∀ x : M,
                  Function.Injective
                    (mfderiv (leeBoundaryModelWithCorners n) (𝓡 m) e x) := by
        simpa using exists_embedding_euclidean_of_compact
      exact hEmbedding
  have he : IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 m) ∞ e := by
    -- Repackage mathlib's compact Whitney theorem into the local smooth-embedding API.
    refine ⟨?_, heClosed.isEmbedding⟩
    exact (Manifold.is_immersion_iff_forall_injective_mfderiv heCont).2 heInj
  -- Feed the arbitrary compact Euclidean embedding into the theorem-local compression result.
  have hApprox :
      ∃ g : C^∞⟮leeBoundaryModelWithCorners n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
        IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ g ∧
          ∀ x : M, dist (g x) (f x) < ε :=
    existsUniformApproximationByEmbeddings_ofSmoothEmbedding hN f he hε
  exact hApprox

theorem smooth_map_to_euclidean_can_be_uniformly_approximated_by_embeddings
    (hN : 2 * n + 1 ≤ N)
    (f : C^∞⟮leeBoundaryModelWithCorners n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C^∞⟮leeBoundaryModelWithCorners n, M; 𝓡 N, EuclideanSpace ℝ (Fin N)⟯,
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ g ∧
        ∀ x : M, dist (g x) (f x) < ε :=
  smoothMapToEuclideanCanBeUniformlyApproximatedByEmbeddings_ofWhitneyEmbedding hN f hε

end WithBoundary

end
end Manifold
