import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch06.Sec06_38.Definition_6_38_extra_2
import LeeSmoothLib.Ch06.Sec06_38.Lemma_6_2
import LeeSmoothLib.Ch06.Sec06_38.Lemma_6_6
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_2
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

open MeasureTheory
open scoped ContDiff Manifold Topology

universe uE uE' uH

section

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasurableSpace E'] [BorelSpace E']
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}

/-- Helper for Theorem 6.10: postcomposing a linear map with a codomain linear equivalence
preserves surjectivity failure. -/
private theorem notSurjective_comp_codomainLinearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E' ≃L[ℝ] F) {A : E →L[ℝ] E'} :
    ¬ Function.Surjective (L.toContinuousLinearMap.comp A) ↔ ¬ Function.Surjective A := by
  constructor
  · intro hcomp hA
    -- A surjective original map stays surjective after composing with a surjective codomain
    -- equivalence, contradicting the transported rank-drop hypothesis.
    exact hcomp (L.surjective.comp hA)
  · intro hA hcomp
    -- Recover surjectivity of the original map by solving the transported equation at `L y` and
    -- cancelling the codomain equivalence.
    apply hA
    intro y
    rcases hcomp (L y) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact L.injective hx

/-- Helper for Theorem 6.10: precomposing a linear map with a domain linear equivalence preserves
surjectivity failure. -/
private theorem notSurjective_comp_domainLinearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F ≃L[ℝ] E) {A : E →L[ℝ] E'} :
    ¬ Function.Surjective (A.comp L.toContinuousLinearMap) ↔ ¬ Function.Surjective A := by
  constructor
  · intro hcomp hA
    -- A surjective original map stays surjective after precomposing with a surjective domain
    -- equivalence.
    exact hcomp (hA.comp L.surjective)
  · intro hA hcomp
    -- Any witness for the precomposed map gives a witness for the original map after applying `L`.
    apply hA
    intro y
    rcases hcomp y with ⟨x, hx⟩
    exact ⟨L x, hx⟩

/-- Helper for Theorem 6.10: conjugating by domain and codomain linear equivalences preserves the
surjectivity failure used in Sard's strict Euclidean branch. -/
private theorem notSurjective_conj_linearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ldom : F ≃L[ℝ] E) (Lcod : E' ≃L[ℝ] G) {A : E →L[ℝ] E'} :
    ¬ Function.Surjective
        (Lcod.toContinuousLinearMap.comp (A.comp Ldom.toContinuousLinearMap)) ↔
      ¬ Function.Surjective A := by
  constructor
  · intro hconj hA
    -- A surjective original map stays surjective after both transport equivalences.
    exact hconj <| Lcod.surjective.comp <| hA.comp Ldom.surjective
  · intro hA hconj
    -- Any witness for the transported map gives a witness for the original map after canceling
    -- both linear equivalences.
    apply hA
    intro y
    rcases hconj (Lcod y) with ⟨x, hx⟩
    exact ⟨Ldom x, Lcod.injective hx⟩

/-- Helper for Theorem 6.10: for a block linear map whose first coordinate is already the scalar
projection, surjectivity of the vertical tail map forces surjectivity of the whole block map. -/
private theorem surjective_of_surjective_verticalTail_of_fst_eq_fst
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {L : ℝ × F →L[ℝ] ℝ × G}
    (hfst :
      (ContinuousLinearMap.fst ℝ ℝ G).comp L = ContinuousLinearMap.fst ℝ ℝ F)
    (htail :
      Function.Surjective
        (((ContinuousLinearMap.snd ℝ ℝ G).comp L).comp
          (ContinuousLinearMap.inr ℝ ℝ F))) :
    Function.Surjective L := by
  intro y
  let base : ℝ × F := (y.1, 0)
  let correction : G := y.2 - ((ContinuousLinearMap.snd ℝ ℝ G).comp L) base
  rcases htail correction with ⟨v, hv⟩
  refine ⟨(y.1, v), ?_⟩
  apply Prod.ext
  · -- The first coordinate is fixed by hypothesis, so choosing the same scalar already hits it.
    change ((ContinuousLinearMap.fst ℝ ℝ G).comp L) (y.1, v) = y.1
    rw [hfst]
    simp
  · -- The vertical correction solves the remaining target equation in the second coordinate.
    change ((ContinuousLinearMap.snd ℝ ℝ G).comp L) (y.1, v) = y.2
    have hsplit : (y.1, v) = base + (0, v) := by
      ext <;> simp [base]
    rw [hsplit, map_add]
    have hv' : ((ContinuousLinearMap.snd ℝ ℝ G).comp L) (0, v) = correction := by
      simpa [correction] using hv
    rw [hv']
    simp [base, correction, sub_eq_add_neg, add_left_comm]

/-- Helper for Theorem 6.10: in the same block form, failure of surjectivity for the full
derivative already forces failure of surjectivity for the vertical tail derivative. -/
private theorem notSurjective_verticalTail_of_notSurjective_of_fst_eq_fst
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {L : ℝ × F →L[ℝ] ℝ × G}
    (hfst :
      (ContinuousLinearMap.fst ℝ ℝ G).comp L = ContinuousLinearMap.fst ℝ ℝ F)
    (hL : ¬ Function.Surjective L) :
    ¬ Function.Surjective
        (((ContinuousLinearMap.snd ℝ ℝ G).comp L).comp
          (ContinuousLinearMap.inr ℝ ℝ F)) := by
  intro htail
  -- Contrapose through the block-surjectivity lemma instead of redoing the coordinate algebra.
  exact hL <|
    surjective_of_surjective_verticalTail_of_fst_eq_fst hfst htail

/-- Helper for Theorem 6.10: a nonzero continuous linear functional on a real vector space is
surjective. -/
private theorem surjective_of_nonzero_continuousLinearMap_toReal
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : F →L[ℝ] ℝ} (hL : L ≠ 0) :
    Function.Surjective L := by
  by_contra hsurj
  have hzero : ∀ x, L x = 0 := by
    intro x
    by_contra hx
    -- A single point where the functional is nonzero already lets us solve `L y = r` by scaling.
    exact hsurj <| by
      intro r
      refine ⟨(r / L x) • x, ?_⟩
      calc
        L ((r / L x) • x) = (r / L x) * L x := by simp
        _ = r := by field_simp [hx]
  -- If every value vanishes, then the functional itself is zero, contradicting the hypothesis.
  exact hL <| ContinuousLinearMap.ext hzero

/-- Helper for Theorem 6.10: pointwise `C^∞` smoothness on a marked subset supplies the explicit
within-derivative data needed by Jacobian-style image estimates. -/
private theorem hasFDerivWithinAt_of_contDiffWithinAt_on_markedSubset
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x) :
    ∀ x ∈ s,
      HasFDerivWithinAt f (fderivWithin ℝ f (Set.range IFin) x) (Set.range IFin) x := by
  intro x hx
  -- Downgrade the pointwise smoothness hypothesis to the concrete within-derivative used by the
  -- Jacobian null-image theorem.
  exact
    ((hsmooth x hx).differentiableWithinAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasFDerivWithinAt

/-- Helper for Theorem 6.10: when the source coordinate dimension is strictly smaller than the
target one, the image of any smooth marked subset has additive Haar measure zero. -/
private theorem euclideanFinImage_measureZero_of_sourceFinrank_lt_targetFinrank
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hlt : m < n) :
    μ (f '' s) = 0 := by
  have hlocLip :
      ∀ x ∈ s, ∃ C : NNReal, ∃ t ∈ nhdsWithin x s, LipschitzOnWith C f t := by
    intro x hx
    have hsmoothOne : ContDiffWithinAt ℝ 1 f (Set.range IFin) x :=
      (hsmooth x hx).of_le (by simp)
    obtain ⟨C, u, hu, hLip⟩ := hsmoothOne.exists_lipschitzOnWith IFin.convex_range
    have hu' : u ∩ s ∈ nhdsWithin x s := by
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hu with ⟨v, hv, hvsub⟩
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
      refine ⟨v, hv, ?_⟩
      intro y hy
      refine ⟨?_, hy.2⟩
      exact hvsub ⟨hy.1, hst hy.2⟩
    -- Restrict the ambient Lipschitz neighborhood back to the marked subset.
    refine ⟨C, u ∩ s, hu', hLip.mono ?_⟩
    intro y hy
    exact hy.1
  have hdimImage :
      dimH (f '' s) < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    calc
      dimH (f '' s) ≤ dimH s := dimH_image_le_of_locally_lipschitzOn hlocLip
      _ ≤ dimH (Set.range IFin) := dimH_mono hst
      _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
        rw [← Real.dimH_univ_eq_finrank (EuclideanSpace ℝ (Fin m))]
        exact dimH_mono (Set.subset_univ _)
      _ < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
        simpa using Nat.cast_lt.2 hlt
  have hhausdorff :
      Measure.hausdorffMeasure
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) (f '' s) = 0 := by
    -- Top-dimensional Hausdorff measure vanishes once the image dimension is strictly smaller than
    -- the target Euclidean dimension.
    simpa using hausdorffMeasure_of_dimH_lt hdimImage
  -- Compare additive Haar measure to the canonical top-dimensional Hausdorff measure.
  rw [Measure.isAddLeftInvariant_eq_smul μ
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ))]
  -- The target set already has zero top-dimensional Hausdorff measure, so the scalar multiple
  -- measure vanishes on it as well.
  rw [Measure.smul_apply, hhausdorff]
  simp

/-- Helper for Theorem 6.10: in equal Euclidean dimensions, pointwise non-surjectivity forces the
Jacobian determinant to vanish, so the fixed-dimension Jacobian theorem closes the image-nullity
claim. -/
private theorem euclideanFinCriticalImage_measureZero_of_equalFinrank
    {n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
    {s : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    μ (f '' s) = 0 := by
  have hfderivRange :
      ∀ x ∈ s,
        HasFDerivWithinAt f (fderivWithin ℝ f (Set.range IFin) x) (Set.range IFin) x :=
    hasFDerivWithinAt_of_contDiffWithinAt_on_markedSubset hsmooth
  have hfderiv :
      ∀ x ∈ s,
        HasFDerivWithinAt f (fderivWithin ℝ f (Set.range IFin) x) s x := by
    intro x hx
    -- Restrict the ambient model-range derivative to the actual marked subset.
    exact (hfderivRange x hx).mono hst
  have hdet :
      ∀ x ∈ s, (fderivWithin ℝ f (Set.range IFin) x).det = 0 := by
    intro x hx
    by_contra hdet
    have hsurj : Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) := by
      -- A nonzero determinant upgrades the within-derivative to a continuous linear equivalence.
      exact
        (fderivWithin ℝ f (Set.range IFin) x).toContinuousLinearEquivOfDetNeZero hdet |>.surjective
    exact hcrit x hx hsurj
  -- Apply the fixed-dimension Jacobian Sard lemma once the determinant has been normalized to
  -- zero everywhere on the marked subset.
  exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hfderiv hdet

/-- Helper for Theorem 6.10: pointwise null-image neighborhoods on a marked subset assemble to a
global null-image statement by Lindelof. -/
private theorem image_measure_zero_of_lindelof_nullNeighborhoods
    {m n : ℕ} {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hlocal : ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    μ (f '' s) = 0 := by
  classical
  let u : s → Set (EuclideanSpace ℝ (Fin m)) := fun x ↦ Classical.choose (hlocal x.1 x.2)
  let V : s → Set s := fun x ↦ Subtype.val ⁻¹' u x
  have hu_nhds : ∀ x : s, u x ∈ nhdsWithin x.1 s := by
    intro x
    -- Record the chosen source neighborhood as a neighborhood in the ambient marked subset.
    exact (Classical.choose_spec (hlocal x.1 x.2)).1
  have hu_zero : ∀ x : s, μ (f '' u x) = 0 := by
    intro x
    -- Record the corresponding null-image statement on the same chosen neighborhood.
    exact (Classical.choose_spec (hlocal x.1 x.2)).2
  have hV_nhds : ∀ x : s, V x ∈ nhds x := by
    intro x
    -- Convert the ambient within-neighborhood into an actual neighborhood in the subtype.
    exact preimage_coe_mem_nhds_subtype.2 (hu_nhds x)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  have hsubset : f '' s ⊆ ⋃ x ∈ t, f '' u x := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    let xs : s := ⟨x, hx⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨x, ?_, rfl⟩
    -- Membership in the chosen subtype neighborhood is exactly membership in the ambient set.
    simpa [V] using hxp
  -- Assemble the pointwise null-image neighborhoods into a countable union.
  exact
    measure_mono_null hsubset <|
      (measure_biUnion_null_iff ht_countable).2 fun x hx ↦ hu_zero x

/-- Helper for Theorem 6.10: once the strict finite-coordinate branch produces pointwise null-image
neighborhoods, Lindelof turns them into the desired global image-nullity statement. -/
private theorem euclideanFinCriticalImage_measureZero_of_localNullNeighborhoods
    {m n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hlocal : ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    μ (f '' s) = 0 := by
  -- The ambient marked-subset inclusion is already fixed; the remaining work is purely the
  -- Lindelof assembly of pointwise null-image neighborhoods.
  exact image_measure_zero_of_lindelof_nullNeighborhoods μ hlocal

/-- Helper for Theorem 6.10: a positive local Hölder exponent on a subset of
`EuclideanSpace ℝ (Fin m)` forces additive Haar null image once the resulting Hausdorff-dimension
bound lies strictly below the target Euclidean dimension. -/
private theorem measure_zero_image_of_locallyHolderOn_of_finrank_div_lt
    {m n : ℕ} {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    {r : NNReal} (hr : 0 < r)
    (hholder :
      ∀ x ∈ s, ∃ C : NNReal, ∃ t ∈ nhdsWithin x s, HolderOnWith C r f t)
    (hdim :
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / r <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    μ (f '' s) = 0 := by
  have hsourceDim :
      dimH s ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
    -- The marked source lives in the ambient `m`-dimensional Euclidean space.
    rw [← Real.dimH_univ_eq_finrank (EuclideanSpace ℝ (Fin m))]
    exact dimH_mono (Set.subset_univ _)
  have hdimImage :
      dimH (f '' s) < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      -- A local Hölder exponent divides the Hausdorff dimension of the source image.
    calc
      dimH (f '' s) ≤ dimH s / r :=
        dimH_image_le_of_locally_holder_on hr hholder
      _ ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / r := by
        simpa using ENNReal.div_le_div_right hsourceDim r
      _ < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := hdim
  have hhausdorff :
      Measure.hausdorffMeasure
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) (f '' s) = 0 := by
    -- Top-dimensional Hausdorff measure vanishes once the image dimension is too small.
    simpa using hausdorffMeasure_of_dimH_lt hdimImage
  -- Compare additive Haar measure to the canonical top-dimensional Hausdorff measure.
  rw [Measure.isAddLeftInvariant_eq_smul μ
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ))]
  rw [Measure.smul_apply, hhausdorff]
  simp

/-- Helper for Theorem 6.10: the strict Euclidean Sard induction on the source dimension should
be allowed to reuse any already-proved lower-dimensional marked-subset instance, with the target
dimension left arbitrary because Step 1 and Step 2 need different codimensions. -/
private abbrev StrictSardLowerDimensionalHypothesis (m : ℕ) : Prop :=
  ∀ {k : ℕ}, k < m →
    ∀ {n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin k)) H}
      {s : Set (EuclideanSpace ℝ (Fin k))}
      {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
      (μ : Measure (EuclideanSpace ℝ (Fin n))),
      μ.IsAddHaarMeasure →
        s ⊆ Set.range IFin →
          (∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x) →
            n < k →
              (∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) →
                μ (f '' s) = 0

/-- Helper for Theorem 6.10: once the target dimension `n` is positive, the Hölder exponent
`m + 1` already forces the Hausdorff-dimension ratio `m / (m + 1)` to lie below the target
finrank. This is the numeric side condition consumed by Lee's Step 3 closure. -/
private theorem finrankDivSucc_lt_targetFinrank_of_ne_zero
    {m n : ℕ} (hn : n ≠ 0) :
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / (m + 1 : NNReal) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hratio_lt_one :
      ((m : ENNReal) / (m + 1 : NNReal)) < 1 := by
    -- Rewrite the ratio in finite-dimensional Euclidean coordinates and compare `m` with `m + 1`.
    rw [ENNReal.div_lt_iff
      (Or.inl (by exact_mod_cast Nat.succ_ne_zero m))
      (Or.inl (by simp))]
    simpa [Nat.succ_eq_add_one, one_mul] using
      (show (m : ENNReal) < m + 1 by exact_mod_cast Nat.lt_succ_self m)
  have hone_le_target :
      (1 : ENNReal) ≤ n := by
    -- A positive finite target dimension is at least `1`.
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  -- Combine the universal ratio bound with positivity of the target dimension.
  simpa using hratio_lt_one.trans_le hone_le_target

/-- Helper for Theorem 6.10: if the Euclidean target dimension is `0`, then the rank-drop
hypothesis is impossible at every marked point, so the marked subset must be empty. -/
private theorem markedSubset_eq_empty_of_zeroTarget_rankDrop
    {m : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 0)}
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    s = ∅ := by
  ext x
  constructor
  · intro hx
    have hsurj : Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) := by
      -- Every map into the zero-dimensional Euclidean space is surjective because the codomain is
      -- subsingleton.
      intro y
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _
    exact (hcrit x hx hsurj).elim
  · simp

/-- Helper for Theorem 6.10: when the Euclidean target dimension is `0`, pointwise rank drop
forces the whole marked subset to be empty, so its image has additive Haar measure zero. -/
private theorem euclideanFinCriticalImage_measureZero_of_zeroTarget_rankDrop
    {m : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 0)}
    (μ : Measure (EuclideanSpace ℝ (Fin 0))) [μ.IsAddHaarMeasure]
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    μ (f '' s) = 0 := by
  have hs_empty :
      s = ∅ :=
    markedSubset_eq_empty_of_zeroTarget_rankDrop (IFin := IFin) (f := f) hcrit
  -- Once the marked subset is empty, the image is empty as well.
  simp [hs_empty]

/-- Helper for Theorem 6.10: restricting the marked subset to a closed ball preserves the ambient
model-range condition needed by the strict Euclidean Sard core. -/
private theorem closedBallPiece_subset_modelRange
    {m : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))} {x₀ : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hst : s ⊆ Set.range IFin) :
    s ∩ Metric.closedBall x₀ r ⊆ Set.range IFin := by
  intro x hx
  -- Restricting to the closed ball keeps the original marked-subset membership in the model
  -- range.
  exact hst hx.1

/-- Helper for Theorem 6.10: the pointwise smoothness hypothesis restricts unchanged to a closed
ball piece of the marked subset. -/
private theorem contDiffWithinAt_on_closedBallPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x₀ : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x) :
    ∀ x ∈ s ∩ Metric.closedBall x₀ r, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x := by
  intro x hx
  -- The compact-piece theorem only needs the original smoothness on the smaller source set.
  exact hsmooth x hx.1

/-- Helper for Theorem 6.10: the pointwise rank-drop hypothesis also restricts unchanged to a
closed ball piece of the marked subset. -/
private theorem notSurjective_fderivWithin_on_closedBallPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x₀ : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x ∈ s ∩ Metric.closedBall x₀ r,
      ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) := by
  intro x hx
  -- The compact-piece owner uses the same within-derivative non-surjectivity on the restricted
  -- source.
  exact hcrit x hx.1

/-- Helper for Theorem 6.10: if the compact closed-ball piece maps into a zero-dimensional target,
pointwise rank drop forces that piece to be empty, so its image has additive Haar measure zero. -/
private theorem closedBallPiece_measureZero_of_zeroTarget_rankDrop
    {m : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 0)}
    (μ : Measure (EuclideanSpace ℝ (Fin 0))) [μ.IsAddHaarMeasure]
    {x₀ : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    μ (f '' (s ∩ Metric.closedBall x₀ r)) = 0 := by
  have hpiece_rankDrop :
      ∀ x ∈ s ∩ Metric.closedBall x₀ r,
        ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) :=
    notSurjective_fderivWithin_on_closedBallPiece (f := f) (x₀ := x₀) (r := r) hcrit
  have hpiece_empty :
      s ∩ Metric.closedBall x₀ r = ∅ :=
    markedSubset_eq_empty_of_zeroTarget_rankDrop (IFin := IFin)
      (s := s ∩ Metric.closedBall x₀ r) (f := f) hpiece_rankDrop
  -- Once the compact source piece is empty, its image is empty as well.
  simp [hpiece_empty]

/-- Helper for Theorem 6.10: a compact closed-ball nullity result yields the pointwise null-image
neighborhoods needed for the Lindelof assembly. -/
private theorem localNullImageNeighborhood_of_closedBallPieceNullity
    {m n : ℕ} {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) {x : EuclideanSpace ℝ (Fin m)}
    (hclosed :
      μ (f '' (s ∩ Metric.closedBall x 1)) = 0) :
    ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  let u : Set (EuclideanSpace ℝ (Fin m)) := Metric.ball x 1 ∩ s
  have hu_nhds : u ∈ nhdsWithin x s := by
    -- Use an honest metric ball in the ambient Euclidean space, then restrict back to the marked
    -- subset.
    rw [Metric.mem_nhdsWithin_iff]
    exact ⟨1, zero_lt_one, by intro y hy; exact hy⟩
  have hu_subset : u ⊆ s ∩ Metric.closedBall x 1 := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    exact Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hy.1))
  refine ⟨u, hu_nhds, ?_⟩
  -- The open-ball image sits inside the closed-ball image handled by the compact-piece theorem.
  exact measure_mono_null (Set.image_mono hu_subset) hclosed

/-- Helper for Theorem 6.10: once every centered unit closed-ball piece has null image, Lindelof
assembles the global nullity statement on the whole marked subset. -/
private theorem image_measureZero_of_centeredClosedBallNullity
    {m n : ℕ} {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hclosed : ∀ x ∈ s, μ (f '' (s ∩ Metric.closedBall x 1)) = 0) :
    μ (f '' s) = 0 := by
  have hlocal :
      ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
    intro x hx
    -- Convert the compact unit-ball nullity centered at `x` into the local neighborhood required
    -- by the Lindelof assembly theorem.
    exact
      localNullImageNeighborhood_of_closedBallPieceNullity μ (x := x) (hclosed x hx)
  -- Route correction: after isolating the compact closed-ball owner, the remaining global step is
  -- exactly the same Lindelof assembly already used elsewhere in this file.
  exact
    euclideanFinCriticalImage_measureZero_of_localNullNeighborhoods
      (f := f) μ hlocal

/-- Helper for Theorem 6.10: if a marked subset is covered by countably many source pieces and
each piece has pointwise null-image neighborhoods, then the whole image has additive Haar measure
zero. -/
private theorem image_measure_zero_of_countableCover_nullNeighborhoods
    {m n : ℕ} {ι : Type} [Countable ι]
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {pieces : ι → Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hcover : s ⊆ ⋃ i, pieces i)
    (hlocal :
      ∀ i x, x ∈ pieces i → ∃ u ∈ nhdsWithin x (pieces i), μ (f '' u) = 0) :
    μ (f '' s) = 0 := by
  have hpiece_zero : ∀ i, μ (f '' pieces i) = 0 := by
    intro i
    -- Each source piece is handled by the existing Lindelof assembly theorem.
    exact
      image_measure_zero_of_lindelof_nullNeighborhoods μ
        (fun x hx ↦ hlocal i x hx)
  have hcover_zero : μ (⋃ i, f '' pieces i) = 0 := by
    -- Countable unions of null target pieces remain null.
    exact measure_iUnion_null hpiece_zero
  have himage_subset : f '' s ⊆ ⋃ i, f '' pieces i := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.1 (hcover hx) with ⟨i, hix⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_image_of_mem f hix⟩
  -- The whole image sits inside the countable union of null target pieces.
  exact measure_mono_null himage_subset hcover_zero

/-- Helper for Theorem 6.10: a countable cover by source pieces with already-null images is enough
for the final union step in the strict Euclidean Sard branch. -/
private theorem image_measure_zero_of_countableCover_imageZero
    {m n : ℕ} {ι : Type} [Countable ι]
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {pieces : ι → Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hcover : s ⊆ ⋃ i, pieces i)
    (hzero : ∀ i, μ (f '' pieces i) = 0) :
    μ (f '' s) = 0 := by
  have hcover_zero : μ (⋃ i, f '' pieces i) = 0 := by
    -- Countable unions of target pieces of measure zero remain null.
    exact measure_iUnion_null hzero
  have himage_subset : f '' s ⊆ ⋃ i, f '' pieces i := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.1 (hcover hx) with ⟨i, hix⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_image_of_mem f hix⟩
  -- The whole source image is contained in the countable union of the null target pieces.
  exact measure_mono_null himage_subset hcover_zero

/-- Helper for Theorem 6.10: data for Lee's Step 1 local straightening branch, recorded as a
nonzero coordinate of the first derivative at the marked point. -/
private structure FirstOrderCoordinateWitness
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (x : EuclideanSpace ℝ (Fin m)) where
  output : Fin n
  input : Fin m
  nonzero :
    ((fderivWithin ℝ f (Set.range IFin) x)
        (EuclideanSpace.basisFun (Fin m) ℝ input)) output ≠ 0

/-- Helper for Theorem 6.10: data for Lee's Step 2 branch, where the marked subset near `x` lies
inside a smooth hypersurface cut out by a scalar function with nonzero derivative. -/
private structure HigherOrderScalarWitness
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    (s : Set (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (x : EuclideanSpace ℝ (Fin m)) where
  order : ℕ
  order_lt : order < m
  scalar : EuclideanSpace ℝ (Fin m) → ℝ
  contDiff : ContDiffWithinAt ℝ ∞ scalar (Set.range IFin) x
  zero_at : scalar x = 0
  deriv_nonzero : fderivWithin ℝ scalar (Set.range IFin) x ≠ 0
  zero_on_source :
    ∃ u ∈ nhdsWithin x s, ∀ y ∈ u, scalar y = 0

/-- Helper for Theorem 6.10: the local Step 1 source piece consists of marked points carrying an
explicit first-derivative coordinate witness. -/
private def firstOrderWitnessPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    (s : Set (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ s ∧ Nonempty (FirstOrderCoordinateWitness (IFin := IFin) (f := f) x)}

/-- Helper for Theorem 6.10: the local Step 2 source piece consists of marked points carrying a
higher-order scalar witness whose zero set contains the source near the point. -/
private def higherOrderWitnessPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    (s : Set (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ s ∧ Nonempty (HigherOrderScalarWitness (IFin := IFin) s (f := f) x)}

/-- Helper for Theorem 6.10: the residual zero-derivative piece consists of marked points where
the first derivative vanishes and no higher-order scalar witness has yet been chosen. -/
private def deepVanishingRemainderPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    (s : Set (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x |
    x ∈ s ∧
      fderivWithin ℝ f (Set.range IFin) x = 0 ∧
        ¬ Nonempty (HigherOrderScalarWitness (IFin := IFin) s (f := f) x)}

/-- Helper for Theorem 6.10: Lee's first vanishing-order piece is the marked locus where the
first derivative already vanishes. -/
private def criticalVanishingPieceOne
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    (s : Set (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ s ∧ fderivWithin ℝ f (Set.range IFin) x = 0}

/-- Helper for Theorem 6.10: the first-order witness piece is a genuine piece of the marked
source set. -/
private theorem firstOrderWitnessPiece_subset
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    firstOrderWitnessPiece (IFin := IFin) (f := f) s ⊆ s := by
  intro x hx
  exact hx.1

/-- Helper for Theorem 6.10: the higher-order witness piece is a genuine piece of the marked
source set. -/
private theorem higherOrderWitnessPiece_subset
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    higherOrderWitnessPiece (IFin := IFin) (f := f) s ⊆ s := by
  intro x hx
  exact hx.1

/-- Helper for Theorem 6.10: the residual zero-derivative piece is also a genuine piece of the
marked source set. -/
private theorem deepVanishingRemainderPiece_subset
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    deepVanishingRemainderPiece (IFin := IFin) (f := f) s ⊆ s := by
  intro x hx
  exact hx.1

/-- Helper for Theorem 6.10: membership in the first vanishing-order piece is just source
membership together with vanishing first derivative. -/
private theorem mem_criticalVanishingPieceOne_iff
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ criticalVanishingPieceOne (IFin := IFin) (f := f) s ↔
      x ∈ s ∧ fderivWithin ℝ f (Set.range IFin) x = 0 := by
  -- The first vanishing-order piece is defined exactly by adjoining the vanishing derivative to
  -- the source membership.
  rfl

/-- Helper for Theorem 6.10: on the marked subset, leaving the first vanishing-order piece is
equivalent to having nonzero first derivative. -/
private theorem not_mem_criticalVanishingPieceOne_iff
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ s) :
    x ∉ criticalVanishingPieceOne (IFin := IFin) (f := f) s ↔
      fderivWithin ℝ f (Set.range IFin) x ≠ 0 := by
  constructor
  · intro hnot hzero
    -- A vanishing first derivative would put `x` back into `C₁`, contradicting the assumption.
    exact hnot <| (mem_criticalVanishingPieceOne_iff (IFin := IFin) (s := s) (f := f)).2
      ⟨hx, hzero⟩
  · intro hzero hxC1
    -- Conversely, any point of `C₁` carries exactly the vanishing derivative forbidden here.
    exact hzero <|
      (mem_criticalVanishingPieceOne_iff (IFin := IFin) (s := s) (f := f)).1 hxC1 |>.2

/-- Helper for Theorem 6.10: the residual deep-vanishing piece is contained in Lee's first
vanishing-order piece. -/
private theorem deepVanishingRemainderPiece_subset_criticalVanishingPieceOne
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    deepVanishingRemainderPiece (IFin := IFin) (f := f) s ⊆
      criticalVanishingPieceOne (IFin := IFin) (f := f) s := by
  intro x hx
  -- The residual piece remembers exactly the same first-derivative vanishing required for `C₁`.
  exact (mem_criticalVanishingPieceOne_iff (IFin := IFin) (s := s) (f := f)).2 ⟨hx.1, hx.2.1⟩

/-- Helper for Theorem 6.10: membership in the Step 1 witness piece recovers the chosen
first-derivative coordinate witness. -/
private theorem firstOrderCoordinateWitness_of_mem_firstOrderWitnessPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s) :
    Nonempty (FirstOrderCoordinateWitness (IFin := IFin) (f := f) x) := by
  -- The Step 1 piece was defined exactly by adjoining a coordinate witness to the source
  -- membership.
  exact hx.2

/-- Helper for Theorem 6.10: membership in the Step 2 witness piece recovers the chosen
higher-order scalar witness. -/
private theorem higherOrderScalarWitness_of_mem_higherOrderWitnessPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s) :
    Nonempty (HigherOrderScalarWitness (IFin := IFin) s (f := f) x) := by
  -- The Step 2 piece likewise stores the witness as part of its definition.
  exact hx.2

/-- Helper for Theorem 6.10: points in the residual deep-vanishing piece still carry vanishing
first derivative. -/
private theorem deepVanishingRemainderPiece_fderivWithin_eq_zero
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s) :
    fderivWithin ℝ f (Set.range IFin) x = 0 := by
  -- This is the first half of the residual-piece definition.
  exact hx.2.1

/-- Helper for Theorem 6.10: points in the residual deep-vanishing piece currently carry no chosen
higher-order scalar witness. -/
private theorem deepVanishingRemainderPiece_noHigherOrderWitness
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s) :
    ¬ Nonempty (HigherOrderScalarWitness (IFin := IFin) s (f := f) x) := by
  -- This is the second half of the residual-piece definition.
  exact hx.2.2

/-- Helper for Theorem 6.10: the residual deep-vanishing piece records exactly the vanishing first
derivative and the absence of any chosen higher-order witness. -/
private theorem deepVanishingRemainderPiece_data
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s) :
    fderivWithin ℝ f (Set.range IFin) x = 0 ∧
      ¬ Nonempty (HigherOrderScalarWitness (IFin := IFin) s (f := f) x) := by
  -- Bundle the residual facts once so the Step 3 branch can consume them without repeating the
  -- definition-level projections.
  exact
    ⟨deepVanishingRemainderPiece_fderivWithin_eq_zero
        (IFin := IFin) (s := s) (f := f) hx,
      deepVanishingRemainderPiece_noHigherOrderWitness
        (IFin := IFin) (s := s) (f := f) hx⟩

/-- Helper for Theorem 6.10: a nonzero first derivative at `x` already determines an explicit
coordinate witness for Lee's Step 1 branch. -/
private theorem firstOrderCoordinateWitness_of_fderivWithin_ne_zero
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hderiv : fderivWithin ℝ f (Set.range IFin) x ≠ 0) :
    Nonempty (FirstOrderCoordinateWitness (IFin := IFin) (f := f) x) := by
  classical
  let A := fderivWithin ℝ f (Set.range IFin) x
  by_contra hno
  have hzeroCoord :
      ∀ (output : Fin n) (input : Fin m),
        (A (EuclideanSpace.basisFun (Fin m) ℝ input)) output = 0 := by
    intro output input
    by_contra hcoord
    apply hno
    exact ⟨⟨output, input, hcoord⟩⟩
  have hzeroCoord' :
      ∀ (output : Fin n) (input : Fin m),
        (A (EuclideanSpace.single input (1 : ℝ))) output = 0 := by
    intro output input
    simpa [EuclideanSpace.basisFun_apply] using hzeroCoord output input
  have hA_zero : A = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hsum :
        ∑ i, v i • EuclideanSpace.basisFun (Fin m) ℝ i = v := by
      simpa using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
    calc
      A v = A (∑ i, v i • EuclideanSpace.basisFun (Fin m) ℝ i) := by
        rw [hsum]
      _ = ∑ i, v i • A (EuclideanSpace.basisFun (Fin m) ℝ i) := by
        rw [map_sum]
        simp [map_smul]
      _ = 0 := by
        ext output
        simp [hzeroCoord']
  exact hderiv hA_zero

/-- Helper for Theorem 6.10: Lee's Step 1 witness data is equivalent to the first derivative being
nonzero at the marked point. -/
private theorem firstOrderCoordinateWitness_nonempty_iff_fderivWithin_ne_zero
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} :
    Nonempty (FirstOrderCoordinateWitness (IFin := IFin) (f := f) x) ↔
      fderivWithin ℝ f (Set.range IFin) x ≠ 0 := by
  constructor
  · rintro ⟨hw⟩ hderiv
    -- A genuinely nonzero derivative coordinate cannot survive if the whole derivative vanishes.
    have hcoord :
        ((fderivWithin ℝ f (Set.range IFin) x)
            (EuclideanSpace.basisFun (Fin m) ℝ hw.input)) hw.output = 0 := by
      simp [hderiv]
    exact hw.nonzero hcoord
  · intro hderiv
    -- Conversely, the previously proved linear-algebra lemma extracts an explicit coordinate
    -- witness from any nonzero first derivative.
    exact
      firstOrderCoordinateWitness_of_fderivWithin_ne_zero
        (IFin := IFin) (f := f) hderiv

/-- Helper for Theorem 6.10: the Step 1 witness piece is exactly the marked locus where the first
derivative does not vanish. -/
private theorem mem_firstOrderWitnessPiece_iff
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s ↔
      x ∈ s ∧ fderivWithin ℝ f (Set.range IFin) x ≠ 0 := by
  constructor
  · intro hx
    -- Unpack the witness-piece membership into source membership plus the nonvanishing derivative.
    refine ⟨hx.1, ?_⟩
    exact
      (firstOrderCoordinateWitness_nonempty_iff_fderivWithin_ne_zero
        (IFin := IFin) (f := f)).1 hx.2
  · intro hx
    -- Repackage the derivative-nonvanishing condition as the witness stored by the Step 1 piece.
    refine ⟨hx.1, ?_⟩
    exact
      (firstOrderCoordinateWitness_nonempty_iff_fderivWithin_ne_zero
        (IFin := IFin) (f := f)).2 hx.2

/-- Helper for Theorem 6.10: a Step 1 coordinate witness makes the chosen scalar output direction
regular at the marked point. -/
private theorem surjective_outputCoordinateDerivative_of_firstOrderCoordinateWitness
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hw : FirstOrderCoordinateWitness (IFin := IFin) (f := f) x) :
    Function.Surjective
      (((EuclideanSpace.proj hw.output : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).comp
        (fderivWithin ℝ f (Set.range IFin) x)) := by
  apply surjective_of_nonzero_continuousLinearMap_toReal
  intro hzero
  -- Evaluating the zero functional on the witness basis vector contradicts the chosen nonzero
  -- derivative coordinate.
  have hcoord :
      (((EuclideanSpace.proj hw.output : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).comp
          (fderivWithin ℝ f (Set.range IFin) x))
        (EuclideanSpace.basisFun (Fin m) ℝ hw.input) = 0 := by
    simpa using DFunLike.congr_fun hzero (EuclideanSpace.basisFun (Fin m) ℝ hw.input)
  exact hw.nonzero (by simpa using hcoord)

/-- Helper for Theorem 6.10: a higher-order scalar witness is already a regular scalar direction at
the marked point. -/
private theorem surjective_fderivWithin_scalar_of_higherOrderScalarWitness
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hw : HigherOrderScalarWitness (IFin := IFin) s (f := f) x) :
    Function.Surjective (fderivWithin ℝ hw.scalar (Set.range IFin) x) := by
  -- The witness stores a nonzero scalar derivative, so the previous one-dimensional linear algebra
  -- bridge applies directly.
  exact surjective_of_nonzero_continuousLinearMap_toReal hw.deriv_nonzero

/-- Helper for Theorem 6.10: a higher-order witness packages the exact local zero-set data and
scalar regularity needed by the Step 2 dispatcher branch. -/
private theorem higherOrderScalarWitness_localZeroSetAndSurjectiveScalar
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hw : HigherOrderScalarWitness (IFin := IFin) s (f := f) x) :
    ∃ u ∈ nhdsWithin x s,
      (∀ y ∈ u, hw.scalar y = 0) ∧
        Function.Surjective (fderivWithin ℝ hw.scalar (Set.range IFin) x) := by
  rcases hw.zero_on_source with ⟨u, hu, hzero⟩
  refine ⟨u, hu, ?_⟩
  -- Keep the local zero-set containment and scalar surjectivity together, so the eventual
  -- regular-level-set reduction can consume one stable witness package.
  refine ⟨hzero, ?_⟩
  exact
    surjective_fderivWithin_scalar_of_higherOrderScalarWitness
      (IFin := IFin) (s := s) (f := f) hw

/-- Helper for Theorem 6.10: pointwise smoothness within `Set.range IFin` gives an open ambient
neighborhood on which the same map is `C¹` on the restricted model-range piece. -/
private theorem contDiffOn_modelRange_inter_open_of_contDiffWithinAt
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {g : EuclideanSpace ℝ (Fin m) → F}
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ Set.range IFin)
    (hg : ContDiffWithinAt ℝ ∞ g (Set.range IFin) x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn ℝ 1 g (Set.range IFin ∩ u) := by
  -- Convert the pointwise `C^∞` hypothesis into an honest open neighborhood where the ordinary
  -- Euclidean restriction is at least `C¹`, which is the level used by the straightening step.
  obtain ⟨u, huOpen, hxu, hdiff⟩ :=
    hg.contDiffOn' (m := (1 : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞))
      (by simp) (by intro h; cases h)
  refine ⟨u, huOpen, hxu, ?_⟩
  simpa [Set.insert_eq_of_mem hx, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
    hdiff

/-- Helper for Theorem 6.10: composing a smooth marked-subset map with one fixed output coordinate
keeps the same pointwise `C^∞` regularity on `Set.range IFin`. -/
private theorem contDiffWithinAt_outputCoordinate_of_contDiffWithinAt
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (i : Fin n)
    (hf : ContDiffWithinAt ℝ ∞ f (Set.range IFin) x) :
    ContDiffWithinAt ℝ ∞ (fun y ↦ (f y) i) (Set.range IFin) x := by
  -- The fixed coordinate projection is linear, so the chain rule preserves `C^∞`.
  simpa using
    (EuclideanSpace.proj i).contDiff.comp_contDiffWithinAt hf

/-- Helper for Theorem 6.10: a Step 1 witness packages the actual scalar local data available
before any straightening argument is attempted. -/
private theorem firstOrderCoordinateWitness_localScalarData
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s) :
    ∃ hw : FirstOrderCoordinateWitness (IFin := IFin) (f := f) x,
      ∃ u, IsOpen u ∧ x ∈ u ∧
        ContDiffOn ℝ 1 (fun y ↦ (f y) hw.output) (Set.range IFin ∩ u) ∧
          Function.Surjective
            (((EuclideanSpace.proj hw.output : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).comp
              (fderivWithin ℝ f (Set.range IFin) x)) := by
  rcases
      firstOrderCoordinateWitness_of_mem_firstOrderWitnessPiece
        (IFin := IFin) (s := s) (f := f) hx with
    ⟨hw⟩
  have hxRange : x ∈ Set.range IFin := hst hx.1
  have hcoordSmooth :
      ContDiffWithinAt ℝ ∞ (fun y ↦ (f y) hw.output) (Set.range IFin) x := by
    -- Pass the marked-subset smoothness to the scalar component chosen by the witness.
    exact
      contDiffWithinAt_outputCoordinate_of_contDiffWithinAt
        (IFin := IFin) hw.output (hsmooth x hx.1)
  obtain ⟨u, huOpen, hxu, hcoordOn⟩ :=
    contDiffOn_modelRange_inter_open_of_contDiffWithinAt
      (IFin := IFin) hxRange hcoordSmooth
  refine ⟨hw, u, huOpen, hxu, hcoordOn, ?_⟩
  -- Keep the linear-algebra part explicit so the eventual straightening theorem only has to solve
  -- the geometric normalization.
  exact
    surjective_outputCoordinateDerivative_of_firstOrderCoordinateWitness
      (IFin := IFin) hw

/-- Helper for Theorem 6.10: a Step 2 witness already supplies the local scalar smoothness,
regularity, and zero-set containment needed before the codimension-one reduction. -/
private theorem higherOrderScalarWitness_localScalarData
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hst : s ⊆ Set.range IFin)
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s) :
    ∃ hw : HigherOrderScalarWitness (IFin := IFin) s (f := f) x,
      ∃ v, IsOpen v ∧ x ∈ v ∧
        ContDiffOn ℝ 1 hw.scalar (Set.range IFin ∩ v) ∧
          ∃ u ∈ nhdsWithin x s,
            (∀ y ∈ u, hw.scalar y = 0) ∧
              Function.Surjective (fderivWithin ℝ hw.scalar (Set.range IFin) x) := by
  rcases
      higherOrderScalarWitness_of_mem_higherOrderWitnessPiece
        (IFin := IFin) (s := s) (f := f) hx with
    ⟨hw⟩
  have hxRange : x ∈ Set.range IFin := hst hx.1
  obtain ⟨v, hvOpen, hxv, hscalarOn⟩ :=
    contDiffOn_modelRange_inter_open_of_contDiffWithinAt
      (IFin := IFin) hxRange hw.contDiff
  obtain ⟨u, hu, hzero, hsurj⟩ :=
    higherOrderScalarWitness_localZeroSetAndSurjectiveScalar
      (IFin := IFin) (s := s) (f := f) hw
  refine ⟨hw, v, hvOpen, hxv, hscalarOn, u, hu, hzero, hsurj⟩

/-- Helper for Theorem 6.10: the Step 1 witness already gives a local `C¹` scalar coordinate on
the model-range piece, separated from the later straightening argument. -/
private theorem firstOrderCoordinateWitness_localScalarNeighborhood
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s) :
    ∃ hw : FirstOrderCoordinateWitness (IFin := IFin) (f := f) x,
      ∃ u, IsOpen u ∧ x ∈ u ∧
        ContDiffOn ℝ 1 (fun y ↦ (f y) hw.output) (Set.range IFin ∩ u) := by
  rcases
      firstOrderCoordinateWitness_localScalarData
        (IFin := IFin) (s := s) (f := f) hst hsmooth hx with
    ⟨hw, u, huOpen, hxu, hcoordOn, -⟩
  -- Separate the neighborhood smoothness package from the derivative-surjectivity package so the
  -- straightening step can consume the geometric data directly.
  exact ⟨hw, u, huOpen, hxu, hcoordOn⟩

/-- Helper for Theorem 6.10: the Step 2 witness already gives a local `C¹` scalar coordinate on
the model-range piece, separated from the later zero-set reduction argument. -/
private theorem higherOrderScalarWitness_localScalarNeighborhood
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hst : s ⊆ Set.range IFin)
    {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s) :
    ∃ hw : HigherOrderScalarWitness (IFin := IFin) s (f := f) x,
      ∃ v, IsOpen v ∧ x ∈ v ∧ ContDiffOn ℝ 1 hw.scalar (Set.range IFin ∩ v) := by
  rcases
      higherOrderScalarWitness_localScalarData
        (IFin := IFin) (s := s) (f := f) hst hx with
    ⟨hw, v, hvOpen, hxv, hscalarOn, -, -, -, -⟩
  -- Keep the ambient smooth scalar neighborhood available as a standalone helper before the
  -- codimension-one zero-set transport is introduced.
  exact ⟨hw, v, hvOpen, hxv, hscalarOn⟩

/-- Helper for Theorem 6.10: Step 2 witness existence is unchanged after intersecting the source
with any ambient neighborhood of the marked point. -/
private theorem higherOrderScalarWitness_nonempty_inter_nhds_iff
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s t : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (ht : t ∈ 𝓝 x) :
    Nonempty (HigherOrderScalarWitness (IFin := IFin) (s ∩ t) (f := f) x) ↔
      Nonempty (HigherOrderScalarWitness (IFin := IFin) s (f := f) x) := by
  constructor
  · rintro ⟨hw⟩
    rcases hw.zero_on_source with ⟨u, hu, hzero⟩
    -- Promote the restricted witness back to the ambient source by rewriting the source
    -- neighborhood filter once.
    refine ⟨⟨hw.order, hw.order_lt, hw.scalar, hw.contDiff, hw.zero_at, hw.deriv_nonzero, ?_⟩⟩
    refine ⟨u, ?_, hzero⟩
    rw [← nhdsWithin_restrict' s ht] at hu
    exact hu
  · rintro ⟨hw⟩
    rcases hw.zero_on_source with ⟨u, hu, hzero⟩
    -- Conversely, restrict the ambient witness along the same neighborhood factor.
    refine ⟨⟨hw.order, hw.order_lt, hw.scalar, hw.contDiff, hw.zero_at, hw.deriv_nonzero, ?_⟩⟩
    refine ⟨u, ?_, hzero⟩
    rw [← nhdsWithin_restrict' s ht]
    exact hu

/-- Helper for Theorem 6.10: centering the unit closed ball at the marked point does not change
Step 2 branch membership at that point. -/
private theorem mem_higherOrderWitnessPiece_inter_closedBall_self_iff
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x 1) ↔
      x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s := by
  have hball : Metric.closedBall x 1 ∈ 𝓝 x := Metric.closedBall_mem_nhds x zero_lt_one
  constructor
  · intro hx
    -- Drop the self-centered closed-ball factor using the neighborhood transport lemma above.
    refine ⟨hx.1.1, ?_⟩
    exact
      (higherOrderScalarWitness_nonempty_inter_nhds_iff
        (IFin := IFin) (s := s) (t := Metric.closedBall x 1) (f := f) (x := x) hball).1 hx.2
  · intro hx
    -- Reinsert the centered closed ball and transport the Step 2 witness across it.
    refine ⟨⟨hx.1, by simpa using Metric.mem_closedBall_self (x := x) (r := (1 : ℝ))⟩, ?_⟩
    exact
      (higherOrderScalarWitness_nonempty_inter_nhds_iff
        (IFin := IFin) (s := s) (t := Metric.closedBall x 1) (f := f) (x := x) hball).2 hx.2

/-- Helper for Theorem 6.10: centering the unit closed ball at the marked point also preserves
residual deep-vanishing branch membership at that point. -/
private theorem mem_deepVanishingRemainderPiece_inter_closedBall_self_iff
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x 1) ↔
      x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s := by
  have hball : Metric.closedBall x 1 ∈ 𝓝 x := Metric.closedBall_mem_nhds x zero_lt_one
  constructor
  · intro hx
    -- Push the restricted no-witness clause back to the ambient source using the same
    -- neighborhood transport API.
    refine ⟨hx.1.1, hx.2.1, ?_⟩
    intro hw
    exact
      hx.2.2 <|
        (higherOrderScalarWitness_nonempty_inter_nhds_iff
          (IFin := IFin) (s := s) (t := Metric.closedBall x 1) (f := f) (x := x) hball).2 hw
  · intro hx
    -- Reinsert the self-centered closed ball and transport the no-witness clause in the reverse
    -- direction.
    refine ⟨⟨hx.1, by simpa using Metric.mem_closedBall_self (x := x) (r := (1 : ℝ))⟩, hx.2.1, ?_⟩
    intro hw
    exact
      hx.2.2 <|
        (higherOrderScalarWitness_nonempty_inter_nhds_iff
          (IFin := IFin) (s := s) (t := Metric.closedBall x 1) (f := f) (x := x) hball).1 hw

/-- Helper for Theorem 6.10: at a marked point, either Lee's Step 1 coordinate witness already
exists or the first derivative vanishes. -/
private theorem firstOrderWitnessOrFderivWithinEqZeroAtPoint
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (_hx : x ∈ s) :
    Nonempty (FirstOrderCoordinateWitness (IFin := IFin) (f := f) x) ∨
      fderivWithin ℝ f (Set.range IFin) x = 0 := by
    -- Route correction: the earlier pointwise trichotomy asked for Step 2/3 witness data that is
    -- not derivable from the current hypotheses alone. The only sound pointwise split available
    -- here is between an explicit Step 1 coordinate witness and vanishing first derivative.
    by_cases hderiv : fderivWithin ℝ f (Set.range IFin) x = 0
    · exact Or.inr hderiv
    · exact Or.inl <|
        firstOrderCoordinateWitness_of_fderivWithin_ne_zero
          (IFin := IFin) (f := f) hderiv

/-- Helper for Theorem 6.10: at a marked point, either Lee's Step 1 witness already exists or the
point lies in the first vanishing-order piece `C₁`. -/
private theorem firstOrderWitnessOrMem_criticalVanishingPieceOneAtPoint
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ s) :
    Nonempty (FirstOrderCoordinateWitness (IFin := IFin) (f := f) x) ∨
      x ∈ criticalVanishingPieceOne (IFin := IFin) (f := f) s := by
  -- Route correction: this is the truthful level-one `C₁` split available from the current API,
  -- and it keeps the remaining frontier attached to an actual vanishing-order invariant.
  rcases firstOrderWitnessOrFderivWithinEqZeroAtPoint
      (IFin := IFin) (s := s) (f := f) hx with hfirst | hderiv
  · exact Or.inl hfirst
  · exact Or.inr <|
      (mem_criticalVanishingPieceOne_iff (IFin := IFin) (s := s) (f := f)).2 ⟨hx, hderiv⟩

/-- Helper for Theorem 6.10: globally, the marked subset splits into the Step 1 witness piece and
Lee's first vanishing-order piece `C₁`. -/
private theorem markedSubset_subset_firstOrderWitnessPiece_union_criticalVanishingPieceOne
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    s ⊆
      firstOrderWitnessPiece (IFin := IFin) (f := f) s ∪
        criticalVanishingPieceOne (IFin := IFin) (f := f) s := by
  intro x hx
  -- Package the pointwise Step 1-versus-`C₁` split as the global first-stage cover of the marked
  -- subset.
  rcases firstOrderWitnessOrMem_criticalVanishingPieceOneAtPoint
      (IFin := IFin) (s := s) (f := f) hx with hfirst | hC1
  · exact Or.inl ⟨hx, hfirst⟩
  · exact Or.inr hC1

/-- Helper for Theorem 6.10: once the first derivative vanishes at `x`, the current witness-piece
split still separates the higher-order witness branch from the residual deep-vanishing branch. -/
private theorem higherOrderWitness_or_deepVanishingRemainder_of_zeroFderivWithin
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ s)
    (hderiv : fderivWithin ℝ f (Set.range IFin) x = 0) :
    x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s ∨
      x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s := by
  -- Route correction: the zero-derivative branch must first be split by whether a truthful
  -- higher-order witness has already been chosen, instead of trying to manufacture Lee Step 2 or
  -- Step 3 directly from `hderiv`.
  by_cases hhigher :
      Nonempty (HigherOrderScalarWitness (IFin := IFin) s (f := f) x)
  · exact Or.inl ⟨hx, hhigher⟩
  · exact Or.inr ⟨hx, hderiv, hhigher⟩

/-- Helper for Theorem 6.10: inside Lee's first vanishing-order piece `C₁`, the current witness
shell splits the point into the Step 2 higher-order witness branch or the residual deep-vanishing
branch. -/
private theorem criticalVanishingPieceOne_subset_higherOrderOrDeepPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    criticalVanishingPieceOne (IFin := IFin) (f := f) s ⊆
      higherOrderWitnessPiece (IFin := IFin) (f := f) s ∪
        deepVanishingRemainderPiece (IFin := IFin) (f := f) s := by
  intro x hx
  rcases (mem_criticalVanishingPieceOne_iff (IFin := IFin) (s := s) (f := f)).1 hx with
    ⟨hsx, hderiv⟩
  -- The `C₁` condition gives exactly the vanishing first derivative needed to invoke the
  -- higher-order-versus-residual branch split.
  exact
    higherOrderWitness_or_deepVanishingRemainder_of_zeroFderivWithin
      (IFin := IFin) (s := s) (f := f) hsx hderiv

/-- Helper for Theorem 6.10: every marked point lies either in the Step 1 witness piece, in the
Step 2 witness piece, or in the residual zero-derivative piece that still needs the deep
vanishing analysis. -/
private theorem witnessPieceCasesAtPoint
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ s) :
    x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s ∨
      x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s ∨
        x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s := by
  -- First split by the sound pointwise dichotomy already available from the first derivative.
  rcases firstOrderWitnessOrFderivWithinEqZeroAtPoint
      (IFin := IFin) (s := s) (f := f) hx with hfirst | hderiv
  · exact Or.inl ⟨hx, hfirst⟩
  · -- Then hand the zero-derivative branch to the dedicated higher-order-versus-residual split.
    exact
      Or.inr <|
        higherOrderWitness_or_deepVanishingRemainder_of_zeroFderivWithin
          (IFin := IFin) (s := s) (f := f) hx hderiv

/-- Helper for Theorem 6.10: the current witness pieces cover the whole marked subset. This is the
available shell-style global decomposition before the honest Step 2 and Step 3 local theorems are
proved. -/
private theorem witnessPieces_cover
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)} :
    s ⊆
      firstOrderWitnessPiece (IFin := IFin) (f := f) s ∪
        higherOrderWitnessPiece (IFin := IFin) (f := f) s ∪
          deepVanishingRemainderPiece (IFin := IFin) (f := f) s := by
  intro x hx
  -- First isolate Lee's Step 1 branch from the first vanishing-order piece `C₁`.
  rcases markedSubset_subset_firstOrderWitnessPiece_union_criticalVanishingPieceOne
      (IFin := IFin) (s := s) (f := f) hx with hfirst | hC1
  · exact Or.inl <| Or.inl hfirst
  · -- Then split the remaining `C₁` branch into the current Step 2 witness shell and the
    -- residual deep-vanishing shell.
    rcases
        criticalVanishingPieceOne_subset_higherOrderOrDeepPiece
          (IFin := IFin) (s := s) (f := f) hC1 with hhigher | hdeep
    · exact Or.inl <| Or.inr hhigher
    · exact Or.inr hdeep

/-- Helper for Theorem 6.10: once each Lee witness branch gives a null-image neighborhood inside
the marked subset, the trichotomy of witness pieces upgrades to the full pointwise local-null
statement needed by Lindelof. -/
private theorem localNullNeighborhoods_of_witnessPieceLocalNullity
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hfirst :
      ∀ x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hhigher :
      ∀ x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hdeep :
      ∀ x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  intro x hx
  -- Split the marked point into Lee's three witness branches and dispatch to the corresponding
  -- local null-image theorem on that branch.
  rcases witnessPieceCasesAtPoint (IFin := IFin) (s := s) (f := f) hx with
      hfirstx | hhigherx | hdeepx
  · exact hfirst x hfirstx
  · exact hhigher x hhigherx
  · exact hdeep x hdeepx

/-- Helper for Theorem 6.10: the strict Euclidean marked-subset theorem is reduced to the three
local Lee branches once the witness-piece trichotomy is available. -/
private theorem image_measure_zero_of_witnessPieceLocalNullity
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hfirst :
      ∀ x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hhigher :
      ∀ x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hdeep :
      ∀ x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    μ (f '' s) = 0 := by
  -- Package the three branchwise local theorems into the single local-null hypothesis consumed by
  -- the existing Lindelof assembly.
  exact
    euclideanFinCriticalImage_measureZero_of_localNullNeighborhoods
      (f := f) μ <|
        localNullNeighborhoods_of_witnessPieceLocalNullity
          (IFin := IFin) (s := s) (f := f) μ hfirst hhigher hdeep

/-- Helper for Theorem 6.10: if the three Lee witness pieces on one centered closed-ball source
piece already have null image, then the whole closed-ball piece has null image as well. -/
private theorem closedBallPiece_measureZero_of_witnessPieceImageZero
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    {x₀ : EuclideanSpace ℝ (Fin m)}
    (hfirst :
      μ (f '' firstOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x₀ 1)) = 0)
    (hhigher :
      μ (f '' higherOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x₀ 1)) = 0)
    (hdeep :
      μ (f '' deepVanishingRemainderPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x₀ 1)) = 0) :
    μ (f '' (s ∩ Metric.closedBall x₀ 1)) = 0 := by
  let sBall : Set (EuclideanSpace ℝ (Fin m)) := s ∩ Metric.closedBall x₀ 1
  let pieces : Fin 3 → Set (EuclideanSpace ℝ (Fin m))
    | 0 => firstOrderWitnessPiece (IFin := IFin) (f := f) sBall
    | 1 => higherOrderWitnessPiece (IFin := IFin) (f := f) sBall
    | _ => deepVanishingRemainderPiece (IFin := IFin) (f := f) sBall
  have hcover : sBall ⊆ ⋃ i, pieces i := by
    intro x hx
    -- Cover the compact closed-ball piece by the same three Lee witness branches, but now formed
    -- for the restricted source `sBall`.
    have hxcover :
        x ∈
          firstOrderWitnessPiece (IFin := IFin) (f := f) sBall ∪
            higherOrderWitnessPiece (IFin := IFin) (f := f) sBall ∪
              deepVanishingRemainderPiece (IFin := IFin) (f := f) sBall :=
      witnessPieces_cover (IFin := IFin) (s := sBall) (f := f) hx
    rcases hxcover with hfront | hdeepx
    · rcases hfront with hfirstx | hhigherx
      · exact Set.mem_iUnion.2 ⟨(0 : Fin 3), by simpa [pieces] using hfirstx⟩
      · exact Set.mem_iUnion.2 ⟨(1 : Fin 3), by simpa [pieces] using hhigherx⟩
    · exact Set.mem_iUnion.2 ⟨(2 : Fin 3), by simpa [pieces] using hdeepx⟩
  have hzero : ∀ i, μ (f '' pieces i) = 0 := by
    intro i
    -- Dispatch each index to the corresponding closed-ball branch nullity hypothesis.
    fin_cases i
    · simpa [pieces, sBall] using hfirst
    · simpa [pieces, sBall] using hhigher
    · simpa [pieces, sBall] using hdeep
  -- Assemble the compact-piece cover from the three already-null branch images.
  simpa [sBall] using
    image_measure_zero_of_countableCover_imageZero
      (s := sBall) (pieces := pieces) (f := f) μ hcover hzero

/-- Helper for Theorem 6.10: once each Lee witness branch is null on every centered unit
closed-ball piece, the whole marked subset is null by the existing closed-ball globalization API.
-/
private theorem centeredClosedBallNullity_of_witnessPieceImageZero
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hfirst :
      ∀ x ∈ s,
        μ (f '' firstOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x 1)) = 0)
    (hhigher :
      ∀ x ∈ s,
        μ (f '' higherOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x 1)) = 0)
    (hdeep :
      ∀ x ∈ s,
        μ (f '' deepVanishingRemainderPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x 1)) = 0) :
    ∀ x ∈ s, μ (f '' (s ∩ Metric.closedBall x 1)) = 0 := by
  intro x hx
  -- Apply the fixed compact-piece union theorem to the three witness branches on the same
  -- centered unit closed ball.
  exact
    closedBallPiece_measureZero_of_witnessPieceImageZero
      (IFin := IFin) (s := s) (f := f) μ
      (hfirst x hx) (hhigher x hx) (hdeep x hx)

/-- Helper for Theorem 6.10: the compact Step 1/2/3 branch theorems all start from the same
closed-ball restriction of the marked-subset hypotheses, so package that restricted context once.
-/
private theorem strictHypotheses_on_closedBallPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x₀ : EuclideanSpace ℝ (Fin m)}
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    (s ∩ Metric.closedBall x₀ 1 ⊆ Set.range IFin) ∧
      (∀ x ∈ s ∩ Metric.closedBall x₀ 1, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x) ∧
      (∀ x ∈ s ∩ Metric.closedBall x₀ 1,
        ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) := by
  -- Reuse the existing closed-ball restriction lemmas so the remaining frontier is only the
  -- genuine Step 1/2/3 compact branch arguments.
  refine ⟨?_, ?_, ?_⟩
  · exact closedBallPiece_subset_modelRange (IFin := IFin) (x₀ := x₀) (r := 1) hst
  · exact contDiffWithinAt_on_closedBallPiece (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hsmooth
  · exact
      notSurjective_fderivWithin_on_closedBallPiece
        (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hcrit

/-- Helper for Theorem 6.10: any subset of a centered closed-ball source piece inherits the same
model-range, smoothness, and rank-drop hypotheses as that ambient closed-ball piece. -/
private theorem subset_of_closedBallPiece_inherits_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s t : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x₀ : EuclideanSpace ℝ (Fin m)}
    (ht : t ⊆ s ∩ Metric.closedBall x₀ 1)
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    (t ⊆ Set.range IFin) ∧
      (∀ x ∈ t, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x) ∧
      (∀ x ∈ t, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) := by
  obtain ⟨hclosedRange, hclosedSmooth, hclosedCrit⟩ :=
    strictHypotheses_on_closedBallPiece
      (IFin := IFin) (s := s) (f := f) (x₀ := x₀) hst hsmooth hcrit
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    -- Push the subset membership into the ambient closed-ball source piece before reusing the
    -- packaged model-range hypothesis.
    exact hclosedRange (ht hx)
  · intro x hx
    -- The same closed-ball restriction also carries the required pointwise smoothness.
    exact hclosedSmooth x (ht hx)
  · intro x hx
    -- Finally, the rank-drop hypothesis descends verbatim to every subset of that closed-ball
    -- piece.
    exact hclosedCrit x (ht hx)

/-- Helper for Theorem 6.10: on a centered closed-ball source piece, the Step 1 witness branch is
exactly the original Step 1 witness branch intersected with that same closed ball. -/
private theorem firstOrderWitnessPiece_closedBallPiece_eq
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x₀ : EuclideanSpace ℝ (Fin m)} :
    firstOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x₀ 1) =
      firstOrderWitnessPiece (IFin := IFin) (f := f) s ∩ Metric.closedBall x₀ 1 := by
  ext x
  constructor
  · intro hx
    -- Unpack the restricted-source definition and keep the witness unchanged, since the Step 1
    -- witness does not depend on the marked subset parameter beyond source membership.
    exact ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
  · intro hx
    -- Repackage the same witness with the closed-ball-restricted source membership.
    exact ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩

/-- Helper for Theorem 6.10: to prove local null-image neighborhoods inside a witness branch, it
suffices to first obtain such neighborhoods in an ambient source set and then intersect with the
branch. -/
private theorem localNullNeighborhoods_within_subset_of_ambient
    {m n : ℕ} {s t : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hts : t ⊆ s)
    (hambient : ∀ x ∈ t, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    ∀ x ∈ t, ∃ u ∈ nhdsWithin x t, μ (f '' u) = 0 := by
  intro x hx
  rcases hambient x hx with ⟨u, hu, hzero⟩
  refine ⟨u ∩ t, ?_, ?_⟩
  · -- Intersect the ambient neighborhood with the branch to obtain a within-neighborhood in `t`.
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hu with ⟨v, hv, hvsub⟩
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    refine ⟨v, hv, ?_⟩
    intro y hy
    refine ⟨?_, hy.2⟩
    exact hvsub ⟨hy.1, hts hy.2⟩
  · -- The new neighborhood image is contained in the ambient null image already produced above.
    exact measure_mono_null (Set.image_mono fun _ hy ↦ hy.1) hzero

/-- Helper for Theorem 6.10: Lee Step 1 is owned by pointwise null-image neighborhoods on the
first-order witness piece, not by a closed-ball globalization. -/
private theorem firstOrderWitnessPiece_localNullNeighborhood_of_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (ih : StrictSardLowerDimensionalHypothesis (H := H) m)
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s,
      ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  intro x hx
  obtain ⟨hw, u, huOpen, hxu, hcoordOn, hsurj⟩ :=
    firstOrderCoordinateWitness_localScalarData
      (IFin := IFin) (s := s) (f := f) hst hsmooth hx
  have hxCrit : ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) := hcrit x hx.1
  -- Route correction: Step 1 is now reduced to the honest local witness data. The remaining
  -- geometric blocker is the straightening-and-slicing argument that turns this scalar coordinate
  -- into an `(m - 1, n - 1)` Sard input on nearby slices.
  -- TODO: normalize `hw.output`/`hw.input` to the first coordinates, apply Lemma 6.2 to a compact
  -- local patch, and invoke `ih` on each slice representative.
  sorry

/-- Helper for Theorem 6.10: Lee Step 2 is likewise owned by pointwise null-image neighborhoods on
the higher-order witness piece. -/
private theorem higherOrderWitnessPiece_localNullNeighborhood_of_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (ih : StrictSardLowerDimensionalHypothesis (H := H) m)
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s,
      ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  intro x hx
  obtain ⟨hw, v, hvOpen, hxv, hscalarOn, u, hu, hzero, hsurj⟩ :=
    higherOrderScalarWitness_localScalarData
      (IFin := IFin) (s := s) (f := f) hst hx
  have hxCrit : ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) := hcrit x hx.1
  -- Route correction: Step 2 now stops at the genuine codimension-one frontier. The remaining
  -- blocker is the zero-set reduction from the witness scalar to an `(m - 1, n)` Sard problem.
  -- TODO: use the regular scalar zero set given by `hw` to model the local source on a
  -- hypersurface and invoke `ih` on the induced restricted map.
  sorry

/-- Helper for Theorem 6.10: Lee Step 3 still needs one explicit bridge from the residual branch
to a local Hölder estimate of order `m + 1`. -/
private theorem deepVanishingRemainderPiece_localHolderOnWith_of_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s,
      ∃ C : NNReal, ∃ t ∈ nhdsWithin x s,
        HolderOnWith C (m + 1 : NNReal) f t := by
  intro x hx
  have hxData :=
    deepVanishingRemainderPiece_data (IFin := IFin) (s := s) (f := f) hx
  have hxSmooth := hsmooth x hx.1
  have hxCrit := hcrit x hx.1
  -- Route correction: Step 3 is now isolated to the single missing analytic bridge. The residual
  -- branch already records vanishing first derivative and absence of a higher-order witness; what
  -- remains is to convert that package into a local `(m + 1)`-Hölder estimate.
  -- TODO: extract the deep Taylor-remainder estimate from the residual branch data and package it
  -- as `HolderOnWith _ (m + 1)` on a neighborhood inside the residual piece.
  sorry

/-- Helper for Theorem 6.10: once the residual branch has a local Hölder estimate, the generic
Hausdorff-dimension argument closes its local null-image statement. -/
private theorem deepVanishingRemainderPiece_localNullNeighborhood_of_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s,
      ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  intro x hx
  obtain ⟨C, t, ht, hHolder⟩ :=
    deepVanishingRemainderPiece_localHolderOnWith_of_strictHypotheses
      (IFin := IFin) (s := s) (f := f) hst hsmooth hn hlt hcrit x hx
  have hmSucc : 0 < (m + 1 : NNReal) := by
    exact_mod_cast Nat.succ_pos m
  have hzero : μ (f '' t) = 0 := by
    -- Apply the generic Hölder-to-nullity theorem on the neighborhood returned by the residual
    -- branch bridge.
    exact
      measure_zero_image_of_locallyHolderOn_of_finrank_div_lt
        (f := f) (s := t) μ hmSucc
        (fun y hy ↦ ⟨C, t, self_mem_nhdsWithin, hHolder⟩)
        (finrankDivSucc_lt_targetFinrank_of_ne_zero hn)
  exact ⟨t, ht, hzero⟩

/-- Helper for Theorem 6.10: Lee's Step 1 branch should first be packaged in the same centered
closed-ball normal form already consumed by the strict globalization layer. -/
private theorem firstOrderWitnessPiece_imageZero_on_closedBallPiece_of_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (ih : StrictSardLowerDimensionalHypothesis (H := H) m)
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x₀ ∈ s,
      μ (f '' firstOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x₀ 1)) = 0 := by
  intro x₀ hx₀
  let sBall : Set (EuclideanSpace ℝ (Fin m)) := s ∩ Metric.closedBall x₀ 1
  have hstBall :
      sBall ⊆ Set.range IFin :=
    closedBallPiece_subset_modelRange (IFin := IFin) (x₀ := x₀) (r := 1) hst
  have hsmoothBall :
      ∀ x ∈ sBall, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x :=
    contDiffWithinAt_on_closedBallPiece
      (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hsmooth
  have hcritBall :
      ∀ x ∈ sBall, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) :=
    notSurjective_fderivWithin_on_closedBallPiece
      (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hcrit
  have hlocalAmbient :
      ∀ x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) sBall,
        ∃ u ∈ nhdsWithin x sBall, μ (f '' u) = 0 :=
    firstOrderWitnessPiece_localNullNeighborhood_of_strictHypotheses
      (IFin := IFin) (s := sBall) (f := f) μ ih hstBall hsmoothBall hn hlt hcritBall
  have hlocal :
      ∀ x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) sBall,
        ∃ u ∈ nhdsWithin x (firstOrderWitnessPiece (IFin := IFin) (f := f) sBall),
          μ (f '' u) = 0 :=
    localNullNeighborhoods_within_subset_of_ambient
      (f := f) μ
      (firstOrderWitnessPiece_subset (IFin := IFin) (s := sBall) (f := f))
      hlocalAmbient
  -- The old compact Step 1 owner is now only a wrapper around the pointwise local-null theorem.
  exact
    image_measure_zero_of_lindelof_nullNeighborhoods
      (f := f) μ hlocal

/-- Helper for Theorem 6.10: Lee's Step 2 branch should likewise be stated directly on centered
closed-ball pieces, matching the existing compact globalization API. -/
private theorem higherOrderWitnessPiece_imageZero_on_closedBallPiece_of_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (ih : StrictSardLowerDimensionalHypothesis (H := H) m)
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x₀ ∈ s,
      μ (f '' higherOrderWitnessPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x₀ 1)) = 0 := by
  intro x₀ hx₀
  let sBall : Set (EuclideanSpace ℝ (Fin m)) := s ∩ Metric.closedBall x₀ 1
  have hstBall :
      sBall ⊆ Set.range IFin :=
    closedBallPiece_subset_modelRange (IFin := IFin) (x₀ := x₀) (r := 1) hst
  have hsmoothBall :
      ∀ x ∈ sBall, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x :=
    contDiffWithinAt_on_closedBallPiece
      (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hsmooth
  have hcritBall :
      ∀ x ∈ sBall, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) :=
    notSurjective_fderivWithin_on_closedBallPiece
      (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hcrit
  have hlocalAmbient :
      ∀ x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) sBall,
        ∃ u ∈ nhdsWithin x sBall, μ (f '' u) = 0 :=
    higherOrderWitnessPiece_localNullNeighborhood_of_strictHypotheses
      (IFin := IFin) (s := sBall) (f := f) μ ih hstBall hsmoothBall hn hlt hcritBall
  have hlocal :
      ∀ x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) sBall,
        ∃ u ∈ nhdsWithin x (higherOrderWitnessPiece (IFin := IFin) (f := f) sBall),
          μ (f '' u) = 0 :=
    localNullNeighborhoods_within_subset_of_ambient
      (f := f) μ
      (higherOrderWitnessPiece_subset (IFin := IFin) (s := sBall) (f := f))
      hlocalAmbient
  -- The old compact Step 2 owner is now only a wrapper around the pointwise local-null theorem.
  exact
    image_measure_zero_of_lindelof_nullNeighborhoods
      (f := f) μ hlocal

/-- Helper for Theorem 6.10: Lee's Step 3 residual branch should also be closed on centered
closed-ball pieces before the final global assembly. -/
private theorem deepVanishingRemainderPiece_imageZero_on_closedBallPiece_of_strictHypotheses
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    ∀ x₀ ∈ s,
      μ (f '' deepVanishingRemainderPiece (IFin := IFin) (f := f) (s ∩ Metric.closedBall x₀ 1)) = 0 := by
  intro x₀ hx₀
  let sBall : Set (EuclideanSpace ℝ (Fin m)) := s ∩ Metric.closedBall x₀ 1
  have hstBall :
      sBall ⊆ Set.range IFin :=
    closedBallPiece_subset_modelRange (IFin := IFin) (x₀ := x₀) (r := 1) hst
  have hsmoothBall :
      ∀ x ∈ sBall, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x :=
    contDiffWithinAt_on_closedBallPiece
      (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hsmooth
  have hcritBall :
      ∀ x ∈ sBall, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) :=
    notSurjective_fderivWithin_on_closedBallPiece
      (IFin := IFin) (f := f) (x₀ := x₀) (r := 1) hcrit
  have hlocalAmbient :
      ∀ x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) sBall,
        ∃ u ∈ nhdsWithin x sBall, μ (f '' u) = 0 :=
    deepVanishingRemainderPiece_localNullNeighborhood_of_strictHypotheses
      (IFin := IFin) (s := sBall) (f := f) μ hstBall hsmoothBall hn hlt hcritBall
  have hlocal :
      ∀ x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) sBall,
        ∃ u ∈ nhdsWithin x (deepVanishingRemainderPiece (IFin := IFin) (f := f) sBall),
          μ (f '' u) = 0 :=
    localNullNeighborhoods_within_subset_of_ambient
      (f := f) μ
      (deepVanishingRemainderPiece_subset (IFin := IFin) (s := sBall) (f := f))
      hlocalAmbient
  -- The old compact Step 3 owner is now only a wrapper around the pointwise local-null theorem.
  exact
    image_measure_zero_of_lindelof_nullNeighborhoods
      (f := f) μ hlocal

/-- Helper for Theorem 6.10: once the three local Step 1/2/3 branch theorems are available, the
existing witness-piece Lindelof assembly finishes the strict Euclidean marked-subset theorem. -/
private theorem strictSardInductionStep_of_witnessPieceLocalNullity
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hfirst :
      ∀ x ∈ firstOrderWitnessPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hhigher :
      ∀ x ∈ higherOrderWitnessPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hdeep :
      ∀ x ∈ deepVanishingRemainderPiece (IFin := IFin) (f := f) s,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    μ (f '' s) = 0 := by
  -- The branchwise local-null statements already match the existing global assembly theorem.
  exact
    image_measure_zero_of_witnessPieceLocalNullity
      (IFin := IFin) (s := s) (f := f) μ hfirst hhigher hdeep

/-- Helper for Theorem 6.10: after excluding the zero-dimensional target, the remaining strict
finite-coordinate Sard statement should be packaged as one explicit strong-induction step on the
source dimension. -/
private theorem strictSardInductionStep
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (ih : StrictSardLowerDimensionalHypothesis (H := H) m)
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hn : n ≠ 0)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    μ (f '' s) = 0 := by
  -- Route correction: the strict owner now consumes the branchwise local-null theorems directly.
  exact
    strictSardInductionStep_of_witnessPieceLocalNullity
      (IFin := IFin) (s := s) (f := f) μ
      (firstOrderWitnessPiece_localNullNeighborhood_of_strictHypotheses
        (IFin := IFin) (s := s) (f := f) μ ih hst hsmooth hn hlt hcrit)
      (higherOrderWitnessPiece_localNullNeighborhood_of_strictHypotheses
        (IFin := IFin) (s := s) (f := f) μ ih hst hsmooth hn hlt hcrit)
      (deepVanishingRemainderPiece_localNullNeighborhood_of_strictHypotheses
        (IFin := IFin) (s := s) (f := f) μ hst hsmooth hn hlt hcrit)

/-- Helper for Theorem 6.10: the finite-coordinate Euclidean owner is the only remaining Sard
frontier after transporting away the abstract `Set.range I` spelling. -/
private theorem euclideanFinCriticalImage_measureZero_of_markedSubset
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    μ (f '' s) = 0 := by
  let P : ℕ → Prop := fun m =>
    ∀ (n0 : ℕ) (IFin0 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H)
      (s0 : Set (EuclideanSpace ℝ (Fin m)))
      (f0 : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n0))
      (μ0 : Measure (EuclideanSpace ℝ (Fin n0))),
      μ0.IsAddHaarMeasure →
        s0 ⊆ Set.range IFin0 →
          (∀ x ∈ s0, ContDiffWithinAt ℝ ∞ f0 (Set.range IFin0) x) →
            n0 < m →
              (∀ x ∈ s0, ¬ Function.Surjective (fderivWithin ℝ f0 (Set.range IFin0) x)) →
                μ0 (f0 '' s0) = 0
  have hm : P m := by
    refine Nat.strong_induction_on m ?_
    intro m ih
    intro n IFin s f μ hμ hst hsmooth hlt hcrit
    let _ : μ.IsAddHaarMeasure := hμ
    by_cases hn : n = 0
    · -- When the target dimension is zero, the rank-drop hypothesis forces the marked subset to be
      -- empty, so the image is empty as well.
      subst hn
      exact
        euclideanFinCriticalImage_measureZero_of_zeroTarget_rankDrop
          (IFin := IFin) (f := f) μ hcrit
    have ihMarked : StrictSardLowerDimensionalHypothesis (H := H) m := by
      intro k hk n' IFin' s' f' μ' hμ' hst' hsmooth' hlt' hcrit'
      -- Reuse the strong-induction hypothesis exactly in the marked-subset owner spelling.
      exact
        ih k hk n' IFin' s' f' μ' hμ' hst' hsmooth' hlt' hcrit'
  -- Route correction: after excluding the zero-dimensional target, the strict branch is now one
  -- explicit induction step driven by the lower-dimensional marked-subset owner `ihMarked`.
    exact
      strictSardInductionStep
        (IFin := IFin) (s := s) (f := f) μ ihMarked hst hsmooth hn hlt hcrit
  exact hm n IFin s f μ inferInstance hst hsmooth hlt hcrit

/-- Helper for Theorem 6.10: once the global marked-subset owner is available, the compact
closed-ball theorem is only its restriction corollary. -/
private theorem euclideanFinCriticalImage_measureZero_onClosedBallPiece
    {m n : ℕ} {IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    {x₀ : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hst : s ⊆ Set.range IFin)
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x)
    (hlt : n < m)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x)) :
    μ (f '' (s ∩ Metric.closedBall x₀ r)) = 0 := by
  have hpiece_subset :
      s ∩ Metric.closedBall x₀ r ⊆ Set.range IFin :=
    closedBallPiece_subset_modelRange (IFin := IFin) (x₀ := x₀) (r := r) hst
  have hpiece_smooth :
      ∀ x ∈ s ∩ Metric.closedBall x₀ r, ContDiffWithinAt ℝ ∞ f (Set.range IFin) x :=
    contDiffWithinAt_on_closedBallPiece (IFin := IFin) (f := f) (x₀ := x₀) (r := r) hsmooth
  have hpiece_rankDrop :
      ∀ x ∈ s ∩ Metric.closedBall x₀ r,
        ¬ Function.Surjective (fderivWithin ℝ f (Set.range IFin) x) :=
    notSurjective_fderivWithin_on_closedBallPiece
      (IFin := IFin) (f := f) (x₀ := x₀) (r := r) hcrit
  -- Apply the marked-subset owner to the closed-ball restriction of the original source set.
  exact
    euclideanFinCriticalImage_measureZero_of_markedSubset
      (IFin := IFin) (f := f) μ hpiece_subset hpiece_smooth hlt hpiece_rankDrop

/-- Helper for Theorem 6.10: after transporting the source model by a continuous linear
equivalence, the `within`-derivative of the conjugated representative is the expected linear
conjugate of the original one. -/
private theorem fderivWithin_conj_transContinuousLinearEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (domEquiv : E ≃L[ℝ] F) (codEquiv : E' ≃L[ℝ] G)
    {f : E → E'} {x : E} (hx : x ∈ Set.range I) :
    fderivWithin ℝ (codEquiv ∘ f ∘ domEquiv.symm)
        (Set.range (I.transContinuousLinearEquiv domEquiv)) (domEquiv x) =
      (codEquiv : E' →L[ℝ] G).comp
        ((fderivWithin ℝ f (Set.range I) x).comp (domEquiv.symm : F →L[ℝ] E)) := by
  have hpreimageRange :
      domEquiv.symm ⁻¹' Set.range I = Set.range (I.transContinuousLinearEquiv domEquiv) := by
    calc
      domEquiv.symm ⁻¹' Set.range I = domEquiv '' Set.range I := by
        ext z
        constructor
        · intro hz
          exact ⟨domEquiv.symm z, hz, by simp⟩
        · intro hz
          rcases hz with ⟨y, hy, rfl⟩
          simpa using hy
      _ = Set.range (I.transContinuousLinearEquiv domEquiv) := by
        simpa using (I.transContinuousLinearEquiv_range (e := domEquiv)).symm
  have hunique :
      UniqueDiffWithinAt ℝ (domEquiv.symm ⁻¹' Set.range I) (domEquiv x) := by
    -- The transported model range has the same unique-differential structure as the original one.
    simpa [hpreimageRange] using
      (I.transContinuousLinearEquiv domEquiv).uniqueDiffOn.uniqueDiffWithinAt <|
        by simpa [hpreimageRange] using hx
  have hright :
      fderivWithin ℝ (f ∘ domEquiv.symm) (domEquiv.symm ⁻¹' Set.range I) (domEquiv x) =
        (fderivWithin ℝ f (Set.range I) x).comp (domEquiv.symm : F →L[ℝ] E) := by
    -- First transport the domain chart spelling.
    simpa using
      (domEquiv.symm.comp_right_fderivWithin
        (f := f) (s := Set.range I) (x := domEquiv x) hunique)
  have hleft :
      fderivWithin ℝ (codEquiv ∘ (f ∘ domEquiv.symm))
          (domEquiv.symm ⁻¹' Set.range I) (domEquiv x) =
        (codEquiv : E' →L[ℝ] G).comp
          (fderivWithin ℝ (f ∘ domEquiv.symm) (domEquiv.symm ⁻¹' Set.range I) (domEquiv x)) := by
    -- Then transport the codomain chart spelling.
    exact codEquiv.comp_fderivWithin hunique
  -- Assemble the two linear-equivalence transport steps.
  calc
    fderivWithin ℝ (codEquiv ∘ f ∘ domEquiv.symm)
        (Set.range (I.transContinuousLinearEquiv domEquiv)) (domEquiv x) =
      (codEquiv : E' →L[ℝ] G).comp
        (fderivWithin ℝ (f ∘ domEquiv.symm) (domEquiv.symm ⁻¹' Set.range I) (domEquiv x)) := by
          simpa [hpreimageRange, Function.comp_assoc] using hleft
    _ =
      (codEquiv : E' →L[ℝ] G).comp
        ((fderivWithin ℝ f (Set.range I) x).comp (domEquiv.symm : F →L[ℝ] E)) := by
          rw [hright]

/-- Helper for Theorem 6.10: theorem-local strict Euclidean Sard core on a marked subset of
`Set.range I`. This is the isolated Lee Step 1/2/3 frontier consumed by the main file's wrapper.
-/
theorem euclideanCriticalImage_measureZero_of_modelRangeMarkedSubset_strictCore
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range I) (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range I) x)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    μ (f '' s) = 0 :=
  -- Route correction: the strict Euclidean induction is intentionally isolated in this theorem-
  -- local support file so the main chartwise Sard assembly no longer carries the Lee Step 1/2/3
  -- proof frontier. The abstract `Set.range I` statement is now reduced once and for all to the
  -- finite-coordinate Euclidean owner below.
  by
    let m : ℕ := Module.finrank ℝ E
    let n : ℕ := Module.finrank ℝ E'
    let domEquiv : E ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [m])
    let codEquiv : E' ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [n])
    let IFin : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H :=
      I.transContinuousLinearEquiv domEquiv
    let sFin : Set (EuclideanSpace ℝ (Fin m)) := domEquiv '' s
    let fFin : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
      codEquiv ∘ f ∘ domEquiv.symm
    let μFin : Measure (EuclideanSpace ℝ (Fin n)) := μ.map codEquiv
    have hpreimageRange :
        domEquiv.symm ⁻¹' Set.range I = Set.range IFin := by
      calc
        domEquiv.symm ⁻¹' Set.range I = domEquiv '' Set.range I := by
          ext z
          constructor
          · intro hz
            exact ⟨domEquiv.symm z, hz, by simp⟩
          · intro hz
            rcases hz with ⟨y, hy, rfl⟩
            simpa using hy
        _ = Set.range IFin := by
          simpa [IFin] using (I.transContinuousLinearEquiv_range (e := domEquiv)).symm
    have hstFin : sFin ⊆ Set.range IFin := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      -- The transported marked subset still lies in the transported model range.
      have hxRange : x ∈ Set.range I := hst hx
      have hxPreimage : domEquiv x ∈ domEquiv.symm ⁻¹' Set.range I := by
        simpa using hxRange
      simpa [hpreimageRange] using hxPreimage
    have hsmoothFin :
        ∀ z ∈ sFin, ContDiffWithinAt ℝ ∞ fFin (Set.range IFin) z := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hright :
          ContDiffWithinAt ℝ ∞ (f ∘ domEquiv.symm)
            (domEquiv.symm ⁻¹' Set.range I) (domEquiv x) := by
        -- Transport the domain model to the finite-coordinate spelling.
        exact
          (domEquiv.symm.contDiffWithinAt_comp_iff
            (f := f) (s := Set.range I) (x := x)).2 (hsmooth x hx)
      -- Transport the codomain spelling by a single linear equivalence.
      exact (codEquiv.comp_contDiffWithinAt_iff (f := f ∘ domEquiv.symm)).2 <| by
        simpa [fFin, hpreimageRange, Function.comp_assoc] using hright
    have hcritFin :
        ∀ z ∈ sFin, ¬ Function.Surjective (fderivWithin ℝ fFin (Set.range IFin) z) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxRange : x ∈ Set.range I := hst hx
      have hderiv :
          fderivWithin ℝ fFin (Set.range IFin) (domEquiv x) =
            (codEquiv : E' →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
              ((fderivWithin ℝ f (Set.range I) x).comp
                (domEquiv.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] E)) := by
        -- Rewrite the transported derivative once, instead of reopening chart transport later.
        simpa [fFin, IFin, Function.comp_assoc] using
          fderivWithin_conj_transContinuousLinearEquiv
            (I := I) domEquiv codEquiv (f := f) hxRange
      rw [hderiv]
      exact
        (notSurjective_conj_linearEquiv_iff
          (Ldom := domEquiv.symm) (Lcod := codEquiv)
          (A := fderivWithin ℝ f (Set.range I) x)).2 (hcrit x hx)
    have hltFin : n < m := by
      -- The strict branch dimension hypothesis is unchanged after choosing finite coordinates.
      simpa [m, n] using hlt
    have hzeroFin : μFin (fFin '' sFin) = 0 := by
      -- This is the only remaining proof frontier: the finite-coordinate Euclidean owner.
      exact
        euclideanFinCriticalImage_measureZero_of_markedSubset
          (IFin := IFin) (f := fFin) μFin hstFin hsmoothFin hltFin hcritFin
    have himage :
        fFin '' sFin = codEquiv '' (f '' s) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨z, hz, rfl⟩
        rcases hz with ⟨x, hx, rfl⟩
        refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
        simp [fFin]
      · intro hy
        rcases hy with ⟨y', hy', rfl⟩
        rcases hy' with ⟨x, hx, rfl⟩
        refine ⟨domEquiv x, ⟨x, hx, rfl⟩, ?_⟩
        simp [fFin]
    -- Pull the finite-coordinate nullity conclusion back across the codomain linear equivalence.
    calc
      μ (f '' s) = μFin (codEquiv '' (f '' s)) := by
        simpa [μFin] using
          (((codEquiv.toHomeomorph.measurableEmbedding).map_apply μ (codEquiv '' (f '' s))).trans
            (by simp [codEquiv.injective.preimage_image])).symm
      _ = μFin (fFin '' sFin) := by rw [himage]
      _ = 0 := hzeroFin

end
