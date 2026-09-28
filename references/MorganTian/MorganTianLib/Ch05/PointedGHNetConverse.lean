import MorganTianLib.Ch05.PointedGH

/-!
# Morgan--Tian Chapter 5: cardinal-controlled pointed net transport

The pointed realization/net bridge is useful in both directions.  This module
keeps the finite source net as an explicit input and records the cardinal cost
of inserting the target basepoint.  The symmetric theorem is obtained by
swapping the two realization legs, so no unpointed or ambient-universe claim is
introduced.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

/-! A finite net can be transported using only pointwise closeness of the
realization legs.  This is the reusable core of the compact realization
producer below. -/

/-- **Math.** Let `L` be a finite based `δ`-net in the left factor.  If every
left point has a chosen right point within `ε` in a pointed realization, then
the image together with the right basepoint is a finite based
`(δ + 2 ε)`-net.  The construction loses at most one point in cardinality. -/
theorem exists_finite_isDeltaNet_of_pointedGHRealization_of_finite
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : pointedHausdorffDist R < ε)
    {L : Set X.carrier} (hLfin : L.Finite)
    (hL : IsDeltaNet δ X.base L) :
    ∃ K : Set Y.carrier, K.Finite ∧ K.ncard ≤ L.ncard + 1 ∧
      IsDeltaNet (δ + 2 * ε) Y.base K := by
  have hεpos : 0 < ε :=
    lt_of_le_of_lt (pointedHausdorffDist_nonneg R) hε
  have hright : ∀ x : X.carrier,
      ∃ y : Y.carrier, dist (R.left x) (R.right y) < ε := by
    intro x
    exact exists_right_point_lt_of_pointedHausdorffDist_lt R hε x
  choose f hf using hright
  let K : Set Y.carrier := insert Y.base (f '' L)
  have hKfin : K.Finite := by
    dsimp [K]
    exact (hLfin.image f).insert Y.base
  have hKcard : K.ncard ≤ L.ncard + 1 := by
    dsimp [K]
    calc
      (insert Y.base (f '' L)).ncard ≤ (f '' L).ncard + 1 :=
        Set.ncard_insert_le Y.base (f '' L)
      _ ≤ L.ncard + 1 :=
        Nat.add_le_add_right
          (Set.ncard_image_le (f := f) (s := L) hLfin) 1
  have hKbase : Y.base ∈ K := by
    exact mem_insert Y.base (f '' L)
  have hKcover : ∀ y : Y.carrier, ∃ z ∈ K,
      dist y z < δ + 2 * ε := by
    intro y
    obtain ⟨x, hx⟩ := exists_left_point_lt_of_pointedHausdorffDist_lt R hε y
    obtain ⟨z, hz, hxz⟩ := hL.2.1 x
    refine ⟨f z, mem_insert_of_mem _ ⟨z, hz, rfl⟩, ?_⟩
    have hleft : dist (R.right y) (R.left x) < ε := by
      simpa [dist_comm] using hx
    have hmiddle : dist (R.left x) (R.left z) < δ := by
      rw [R.left_isometry.dist_eq]
      exact hxz
    have hright : dist (R.left z) (R.right (f z)) < ε := hf z
    calc
      dist y (f z) = dist (R.right y) (R.right (f z)) :=
        (R.right_isometry.dist_eq _ _).symm
      _ ≤ dist (R.right y) (R.left x) +
          dist (R.left x) (R.right (f z)) := by
        exact dist_triangle _ _ _
      _ ≤ dist (R.right y) (R.left x) +
          (dist (R.left x) (R.left z) + dist (R.left z) (R.right (f z))) := by
        exact add_le_add_right
          (dist_triangle (R.left x) (R.left z) (R.right (f z))) _
      _ < ε + (δ + ε) := by
        exact add_lt_add hleft (add_lt_add hmiddle hright)
      _ = δ + 2 * ε := by ring
  letI : Fintype K := hKfin.fintype
  have hKsep : ∃ η > 0, ∀ ⦃u v : Y.carrier⦄,
      u ∈ K → v ∈ K → u ≠ v → η ≤ dist u v := by
    by_cases hnontrivial : K.Nontrivial
    · obtain ⟨η, hη, hsep⟩ := Set.relatively_discrete_of_finite (s := K)
      obtain ⟨u, hu, v, hv, huv⟩ := hnontrivial
      have hηtop : η ≠ ⊤ := by
        intro htop
        have hle : (⊤ : ENNReal) ≤ edist u v := by
          simpa only [htop] using hsep u hu v hv huv
        exact edist_ne_top u v (top_unique hle)
      have hηreal : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
      refine ⟨η.toReal, hηreal, ?_⟩
      intro u v hu hv huv
      have hle := hsep u hu v hv huv
      have hreal := ENNReal.toReal_mono (edist_ne_top u v) hle
      simpa [edist_dist] using hreal
    · have hsubsingleton : K.Subsingleton :=
        Set.not_nontrivial_iff.mp hnontrivial
      refine ⟨1, zero_lt_one, ?_⟩
      intro u v hu hv huv
      exact (huv (hsubsingleton hu hv)).elim
  exact ⟨K, hKfin, hKcard, ⟨hKbase, hKcover, hKsep⟩⟩

/-! Compactness turns the separated source net into a finite set.  We expose
that step separately so callers can retain the cardinal estimate above. -/

private theorem finite_of_isDeltaNet_of_compactSpace
    {X : Type u} [MetricSpace X] [CompactSpace X]
    {δ : ℝ} {x : X} {L : Set X}
    (hL : IsDeltaNet δ x L) : L.Finite := by
  obtain ⟨σ, hσ, hσsep⟩ := hL.2.2
  obtain ⟨t, htSub, htFinite, htCover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).finite_cover_balls
      (e := σ / 3) (by linarith)
  letI : Fintype t := htFinite.fintype
  have hcover : ∀ x : X, ∃ z : t, dist x z < σ / 3 := by
    intro x
    have hx : x ∈ ⋃ z ∈ t, Metric.ball z (σ / 3) :=
      htCover (Set.mem_univ x)
    rcases Set.mem_iUnion₂.mp hx with ⟨z, hz, hxz⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    exact Metric.mem_ball.mp hxz
  choose c hc using hcover
  have hcLinj : Function.Injective (fun x : L => c x.1) := by
    intro a b hab
    by_contra hab'
    have hdist : dist (a : X) (b : X) < σ := by
      calc
        dist (a : X) (b : X) ≤ dist (a : X) (c a : X) +
            dist (c a : X) (b : X) := dist_triangle _ _ _
        _ = dist (a : X) (c a : X) +
            (dist (b : X) (c b : X) + 0) := by
          have hcab : (c a : X) = (c b : X) :=
            congrArg Subtype.val hab
          rw [hcab]
          simp [dist_comm]
        _ < σ / 3 + (σ / 3 + 0) := by
          gcongr
          · exact hc a
          · exact hc b
        _ < σ := by linarith
    have hab'' : (a : X) ≠ (b : X) := by
      intro hab''
      exact hab' (Subtype.ext hab'')
    exact (not_lt_of_ge (hσsep a.property b.property hab'')) hdist
  letI : Finite L := Finite.of_injective (fun x : L => c x.1) hcLinj
  exact Set.finite_coe_iff.mp (inferInstance : Finite L)

/-- **Math.** For compact carriers, a small pointed realization transports any
based `δ`-net and retains an explicit cardinal estimate on the target net. -/
theorem exists_finite_isDeltaNet_of_pointedGHRealization_with_card
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (R : PointedGHRealization X Y) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : pointedHausdorffDist R < ε)
    {L : Set X.carrier} (hL : IsDeltaNet δ X.base L) :
    ∃ K : Set Y.carrier, K.Finite ∧ K.ncard ≤ L.ncard + 1 ∧
      IsDeltaNet (δ + 2 * ε) Y.base K := by
  exact exists_finite_isDeltaNet_of_pointedGHRealization_of_finite R hδ hε
    (finite_of_isDeltaNet_of_compactSpace hL) hL

/-- **Math.** The cardinal-controlled finite-net transport is symmetric.  A
finite based net in the right factor yields one in the left factor with the
same error and the same `+1` basepoint cost. -/
theorem exists_finite_isDeltaNet_of_pointedGHRealization_right_with_card
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (R : PointedGHRealization X Y) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : pointedHausdorffDist R < ε)
    {L : Set Y.carrier} (hL : IsDeltaNet δ Y.base L) :
    ∃ K : Set X.carrier, K.Finite ∧ K.ncard ≤ L.ncard + 1 ∧
      IsDeltaNet (δ + 2 * ε) X.base K := by
  let R' : PointedGHRealization Y X :=
    { ambient := R.ambient
      left := R.right
      right := R.left
      left_isometry := R.right_isometry
      right_isometry := R.left_isometry
      left_base := R.right_base
      right_base := R.left_base }
  have hε' : pointedHausdorffDist R' < ε := by
    have hcomm : pointedHausdorffDist R' = pointedHausdorffDist R := by
      simp [pointedHausdorffDist, R', Metric.hausdorffDist_comm]
    rw [hcomm]
    exact hε
  exact exists_finite_isDeltaNet_of_pointedGHRealization_with_card
    R' hδ hε' hL

end MorganTianLib

end

#print axioms MorganTianLib.exists_finite_isDeltaNet_of_pointedGHRealization_of_finite
#print axioms MorganTianLib.exists_finite_isDeltaNet_of_pointedGHRealization_with_card
#print axioms
  MorganTianLib.exists_finite_isDeltaNet_of_pointedGHRealization_right_with_card
