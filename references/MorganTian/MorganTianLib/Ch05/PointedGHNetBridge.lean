import MorganTianLib.Ch05.PointedGH

/-!
# Morgan--Tian Chapter 5: transporting finite nets across a pointed realization

A small pointed realization transports a finite net in one compact factor to a
finite net in the other factor.  The two realization-error legs are retained
explicitly, giving the expected `δ + 2 ε` covering radius.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

/-- **Math.** A pointed realization with Hausdorff error below `ε` transports
a based `δ`-net in a compact source to a finite based `(δ + 2 ε)`-net in the
compact target.  The source compactness makes the separated source net finite;
the target basepoint is inserted explicitly in the transported set. -/
theorem exists_finite_isDeltaNet_of_pointedGHRealization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (R : PointedGHRealization X Y) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : pointedHausdorffDist R < ε)
    {L : Set X.carrier} (hL : IsDeltaNet δ X.base L) :
    ∃ K : Set Y.carrier, K.Finite ∧
      IsDeltaNet (δ + 2 * ε) Y.base K := by
  have hεpos : 0 < ε :=
    lt_of_le_of_lt (pointedHausdorffDist_nonneg R) hε
  obtain ⟨σ, hσ, hσsep⟩ := hL.2.2
  obtain ⟨t, htSub, htFinite, htCover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X.carrier)).finite_cover_balls
      (e := σ / 3) (by linarith)
  letI : Fintype t := htFinite.fintype
  have hcover : ∀ x : X.carrier, ∃ z : t, dist x z < σ / 3 := by
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
    have hdist : dist (a : X.carrier) (b : X.carrier) < σ := by
      calc
        dist (a : X.carrier) (b : X.carrier) ≤
            dist (a : X.carrier) (c a : X.carrier) +
              dist (c a : X.carrier) (b : X.carrier) :=
          dist_triangle _ _ _
        _ = dist (a : X.carrier) (c a : X.carrier) +
            (dist (b : X.carrier) (c b : X.carrier) + 0) := by
          have hcab : (c a : X.carrier) = (c b : X.carrier) :=
            congrArg Subtype.val hab
          rw [hcab]
          simp [dist_comm]
        _ < σ / 3 + (σ / 3 + 0) := by
          gcongr
          · exact hc a
          · exact hc b
        _ < σ := by linarith
    have hab'' : (a : X.carrier) ≠ (b : X.carrier) := by
      intro hab''
      exact hab' (Subtype.ext hab'')
    exact (not_lt_of_ge (hσsep a.property b.property hab'')) hdist
  letI : Finite L := Finite.of_injective (fun x : L => c x.1) hcLinj
  have hLfin : L.Finite := Set.finite_coe_iff.mp (inferInstance : Finite L)
  have hright : ∀ x : X.carrier,
      ∃ y : Y.carrier, dist (R.left x) (R.right y) < ε := by
    intro x
    exact exists_right_point_lt_of_pointedHausdorffDist_lt R hε x
  choose f hf using hright
  let K : Set Y.carrier := insert Y.base (f '' L)
  have hKfin : K.Finite := by
    dsimp [K]
    exact (hLfin.image f).insert Y.base
  have hKbase : Y.base ∈ K := by
    exact mem_insert Y.base (f '' L)
  have hKcover : ∀ y : Y.carrier, ∃ z ∈ K, dist y z < δ + 2 * ε := by
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
  refine ⟨K, hKfin, ⟨hKbase, hKcover, hKsep⟩⟩

end MorganTianLib

end

#print axioms MorganTianLib.exists_finite_isDeltaNet_of_pointedGHRealization
