import MorganTianLib.Ch05.PointedGHNetConverse
import MorganTianLib.Ch05.MarkedGHBridge

/-!
# Morgan--Tian Chapter 5: finite-net characterization of pointed convergence

Small pointed realizations transport separated nets with multiplicative metric
control. Conversely, exact-basepoint approximate gluing turns eventual
bilipschitz net models into pointed convergence when the target is compact.
-/

open Set Metric TopologicalSpace
open scoped ENNReal lp

noncomputable section

namespace MorganTianLib

universe u

/-! ## Exact pointed gluing from an approximate equivalence -/

/-- **Math.** A basepoint-preserving equivalence with additive distortion at
most `ε` bounds the pointed Gromov--Hausdorff distance by `ε`. The approximate
gluing initially places corresponding points a positive distance apart; the
two copies are then centered in a Kuratowski ambient, making their basepoints
agree exactly. The `ULift` keeps that ambient in the source universe. -/
theorem pointedGHDistance_le_of_separable_approximate_equiv
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [SeparableSpace X.carrier] [SeparableSpace Y.carrier]
    (e : X.carrier ≃ Y.carrier)
    (hbase : e X.base = Y.base)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdist : ∀ x y : X.carrier,
      |dist x y - dist (e x) (e y)| ≤ ε) :
    pointedGHDistance X Y ≤ ε := by
  apply le_of_forall_pos_le_add
  intro ρ hρ
  let θ : ℝ := ε / 2 + ρ / 2
  have hθ : 0 < θ := by
    dsimp [θ]
    linarith
  have hdist' : ∀ x y : X.carrier,
      |dist x y - dist (e x) (e y)| ≤ 2 * θ := by
    intro x y
    exact (hdist x y).trans (by dsimp [θ]; linarith)
  letI : MetricSpace (X.carrier ⊕ Y.carrier) :=
    Metric.glueMetricApprox id e θ hθ hdist'
  let Fl : X.carrier → X.carrier ⊕ Y.carrier := Sum.inl
  let Fr : Y.carrier → X.carrier ⊕ Y.carrier := Sum.inr
  have hFl : Isometry Fl := Isometry.of_dist_eq fun _ _ => rfl
  have hFr : Isometry Fr := Isometry.of_dist_eq fun _ _ => rfl
  let i : lp (fun _ : ℕ => ℝ) ∞ →
      ULift.{u} (lp (fun _ : ℕ => ℝ) ∞) := ULift.up
  have hi : Isometry i := Isometry.of_dist_eq fun _ _ => rfl
  let left : X.carrier → ULift.{u} (lp (fun _ : ℕ => ℝ) ∞) :=
    i ∘ centeredKuratowskiMap (Fl X.base) ∘ Fl
  let right : Y.carrier → ULift.{u} (lp (fun _ : ℕ => ℝ) ∞) :=
    i ∘ centeredKuratowskiMap (Fr Y.base) ∘ Fr
  have hleft : Isometry left :=
    hi.comp ((centeredKuratowskiMap_isometry (Fl X.base)).comp hFl)
  have hright : Isometry right :=
    hi.comp ((centeredKuratowskiMap_isometry (Fr Y.base)).comp hFr)
  let R : PointedGHRealization X Y :=
    { ambient :=
        { carrier := ULift.{u} (lp (fun _ : ℕ => ℝ) ∞)
          metric := inferInstance
          base := ULift.up 0 }
      left := left
      right := right
      left_isometry := hleft
      right_isometry := hright
      left_base := by simp [left, i, Function.comp_apply]
      right_base := by simp [right, i, Function.comp_apply] }
  have hpaired : ∀ x : X.carrier,
      dist (R.left x) (R.right (e x)) ≤ 2 * θ := by
    intro x
    change dist
      (centeredKuratowskiMap (Fl X.base) (Fl x))
      (centeredKuratowskiMap (Fr Y.base) (Fr (e x))) ≤ 2 * θ
    have hx : dist (Fl x) (Fr (e x)) = θ := by
      change Metric.glueDist id e θ (Sum.inl x) (Sum.inr (e x)) = θ
      simpa only [id_eq] using
        (Metric.glueDist_glued_points id e θ x)
    have hb : dist (Fl X.base) (Fr Y.base) = θ := by
      rw [← hbase]
      change Metric.glueDist id e θ
        (Sum.inl X.base) (Sum.inr (e X.base)) = θ
      simpa only [id_eq] using
        (Metric.glueDist_glued_points id e θ X.base)
    calc
      _ ≤ dist (Fl x) (Fr (e x)) + dist (Fl X.base) (Fr Y.base) := by
        dsimp [centeredKuratowskiMap]
        simpa only [(kuratowskiEmbedding.isometry
          (X.carrier ⊕ Y.carrier)).dist_eq] using
            (dist_sub_sub_le_additive
              (kuratowskiEmbedding (X.carrier ⊕ Y.carrier) (Fl x))
              (kuratowskiEmbedding (X.carrier ⊕ Y.carrier) (Fl X.base))
              (kuratowskiEmbedding (X.carrier ⊕ Y.carrier) (Fr (e x)))
              (kuratowskiEmbedding (X.carrier ⊕ Y.carrier) (Fr Y.base)))
      _ = θ + θ := by rw [hx, hb]
      _ = 2 * θ := by ring
  have hR : pointedHausdorffDist R ≤ 2 * θ := by
    unfold pointedHausdorffDist
    apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
    · rintro _ ⟨x, rfl⟩
      exact ⟨R.right (e x), ⟨e x, rfl⟩, hpaired x⟩
    · rintro _ ⟨y, rfl⟩
      let x := e.symm y
      refine ⟨R.left x, ⟨x, rfl⟩, ?_⟩
      rw [dist_comm]
      simpa [x] using hpaired x
  calc
    pointedGHDistance X Y ≤ pointedHausdorffDist R :=
      pointedGHDistance_le_realization R
    _ ≤ 2 * θ := hR
    _ = ε + ρ := by dsimp [θ]; ring

/-- **Math.** A small pointed realization turns a separated net into a based
target net. If `2 * ε ≤ η * σ`, where `σ` separates distinct net points, then
the chosen correspondence is `(1 + η)`-bilipschitz on the net in the explicit
two-sided inequality sense displayed below. -/
theorem bilipschitz_deltaNet_image_of_pointedGHRealization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {δ ε σ η : ℝ}
    (hεσ : 2 * ε < σ)
    (hη : 0 ≤ η)
    (hmargin : 2 * ε ≤ η * σ)
    {L : Set X.carrier} (hL : IsDeltaNet δ X.base L)
    (hsep : ∀ ⦃a b : X.carrier⦄, a ∈ L → b ∈ L → a ≠ b → σ ≤ dist a b)
    (f : L → Y.carrier)
    (hclose : ∀ z : L, dist (R.left z.1) (R.right (f z)) < ε)
    (hbase : f ⟨X.base, hL.1⟩ = Y.base)
    (hR : pointedHausdorffDist R < ε) :
    Function.Injective f ∧
      (∀ a b : L,
        (1 - η) * dist (a : X.carrier) (b : X.carrier) ≤
            dist (f a) (f b) ∧
          dist (f a) (f b) ≤ (1 + η) * dist (a : X.carrier) (b : X.carrier)) ∧
      IsDeltaNet (δ + 2 * ε) Y.base (Set.range f) := by
  have hdist_add : ∀ a b : L,
      dist (f a) (f b) ≤ dist (a : X.carrier) (b : X.carrier) + 2 * ε := by
    intro a b
    calc
      dist (f a) (f b) = dist (R.right (f a)) (R.right (f b)) :=
        (R.right_isometry.dist_eq _ _).symm
      _ ≤ dist (R.right (f a)) (R.left a.1) +
          dist (R.left a.1) (R.left b.1) +
          dist (R.left b.1) (R.right (f b)) := by
        exact dist_triangle4 _ _ _ _
      _ ≤ ε + dist (a : X.carrier) (b : X.carrier) + ε := by
        gcongr
        · exact le_of_lt (by simpa [dist_comm] using hclose a)
        · rw [R.left_isometry.dist_eq]
        · exact le_of_lt (by simpa [dist_comm] using hclose b)
      _ = dist (a : X.carrier) (b : X.carrier) + 2 * ε := by ring
  have hdist_rev : ∀ a b : L,
      dist (a : X.carrier) (b : X.carrier) ≤ dist (f a) (f b) + 2 * ε := by
    intro a b
    calc
      dist (a : X.carrier) (b : X.carrier) = dist (R.left a.1) (R.left b.1) :=
        (R.left_isometry.dist_eq _ _).symm
      _ ≤ dist (R.left a.1) (R.right (f a)) +
          dist (R.right (f a)) (R.right (f b)) +
          dist (R.right (f b)) (R.left b.1) := by
        exact dist_triangle4 _ _ _ _
      _ ≤ ε + dist (f a) (f b) + ε := by
        gcongr
        · exact le_of_lt (hclose a)
        · rw [R.right_isometry.dist_eq]
        · exact le_of_lt (by simpa [dist_comm] using hclose b)
      _ = dist (f a) (f b) + 2 * ε := by ring
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra habne
    have hσab : σ ≤ dist (a : X.carrier) (b : X.carrier) :=
      hsep a.property b.property (by
        intro heq
        exact habne (Subtype.ext heq))
    have hupper : dist (a : X.carrier) (b : X.carrier) ≤
        dist (f a) (f b) + 2 * ε := hdist_rev a b
    have hzero : dist (f a) (f b) = 0 := by rw [hab]; exact dist_self _
    nlinarith [hσab, hεσ]
  have hbilip : ∀ a b : L,
      (1 - η) * dist (a : X.carrier) (b : X.carrier) ≤ dist (f a) (f b) ∧
        dist (f a) (f b) ≤ (1 + η) * dist (a : X.carrier) (b : X.carrier) := by
    intro a b
    have hadd := hdist_add a b
    have hreverse := hdist_rev a b
    have hsepab : dist (a : X.carrier) (b : X.carrier) = 0 ∨
        σ ≤ dist (a : X.carrier) (b : X.carrier) := by
      by_cases hab : (a : X.carrier) = b
      · left; simp [hab]
      · right; exact hsep a.property b.property hab
    constructor
    · rcases hsepab with hzero | hσab
      · have hab : a = b := Subtype.ext (dist_eq_zero.mp hzero)
        simp [hab]
      · nlinarith [hreverse, hmargin]
    · rcases hsepab with hzero | hσab
      · have hab : a = b := Subtype.ext (dist_eq_zero.mp hzero)
        simp [hab]
      · nlinarith [hadd, hmargin]
  have hbase' : Y.base ∈ Set.range f := by
    exact ⟨⟨X.base, hL.1⟩, hbase⟩
  have hcover : ∀ y : Y.carrier, ∃ z ∈ Set.range f,
      dist y z < δ + 2 * ε := by
    intro y
    obtain ⟨x, hx⟩ := exists_left_point_lt_of_pointedHausdorffDist_lt R hR y
    obtain ⟨z, hz, hxz⟩ := hL.2.1 x
    refine ⟨f ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
    have hleft : dist (R.right y) (R.left x) < ε := by
      simpa [dist_comm] using hx
    calc
      dist y (f ⟨z, hz⟩) = dist (R.right y) (R.right (f ⟨z, hz⟩)) :=
        (R.right_isometry.dist_eq _ _).symm
      _ ≤ dist (R.right y) (R.left x) +
          (dist (R.left x) (R.left z) +
            dist (R.left z) (R.right (f ⟨z, hz⟩))) := by
        have hmid : dist (R.left x) (R.right (f ⟨z, hz⟩)) ≤
            dist (R.left x) (R.left z) +
              dist (R.left z) (R.right (f ⟨z, hz⟩)) :=
          dist_triangle _ _ _
        have hfirst : dist (R.right y) (R.right (f ⟨z, hz⟩)) ≤
            dist (R.right y) (R.left x) +
              dist (R.left x) (R.right (f ⟨z, hz⟩)) :=
          dist_triangle _ _ _
        have hadd : dist (R.right y) (R.left x) +
            dist (R.left x) (R.right (f ⟨z, hz⟩)) ≤
            dist (R.right y) (R.left x) +
              (dist (R.left x) (R.left z) +
                dist (R.left z) (R.right (f ⟨z, hz⟩))) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hmid (dist (R.right y) (R.left x))
        exact hfirst.trans hadd
      _ < ε + (δ + ε) := by
        exact add_lt_add hleft (add_lt_add
          (by simpa [R.left_isometry.dist_eq] using hxz) (hclose ⟨z, hz⟩))
      _ = δ + 2 * ε := by ring
  have hsepRange : ∃ τ > 0, ∀ ⦃u v : Y.carrier⦄,
      u ∈ Set.range f → v ∈ Set.range f → u ≠ v → τ ≤ dist u v := by
    refine ⟨σ - 2 * ε, sub_pos.mpr hεσ, ?_⟩
    rintro u v ⟨a, rfl⟩ ⟨b, rfl⟩ huv
    have hab : a ≠ b := by
      intro heq
      exact huv (congrArg f heq)
    have hσab := hsep a.property b.property (by
      intro heq
      exact hab (Subtype.ext heq))
    have hrev := hdist_rev a b
    nlinarith
  exact ⟨hinj, hbilip, hbase', hcover, hsepRange⟩

/-- **Math.** The finiteness and cardinality refinement of
`bilipschitz_deltaNet_image_of_pointedGHRealization`. -/
theorem finite_net_bilipschitz_image_of_pointedGHRealization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {δ ε σ η : ℝ}
    (hεσ : 2 * ε < σ)
    (hη : 0 ≤ η)
    (hmargin : 2 * ε ≤ η * σ)
    {L : Set X.carrier} (hL : IsDeltaNet δ X.base L)
    (hLfin : L.Finite)
    (hsep : ∀ ⦃a b : X.carrier⦄, a ∈ L → b ∈ L → a ≠ b → σ ≤ dist a b)
    (f : L → Y.carrier)
    (hclose : ∀ z : L, dist (R.left z.1) (R.right (f z)) < ε)
    (hbase : f ⟨X.base, hL.1⟩ = Y.base)
    (hR : pointedHausdorffDist R < ε) :
    Function.Injective f ∧
      (∀ a b : L,
        (1 - η) * dist (a : X.carrier) (b : X.carrier) ≤
            dist (f a) (f b) ∧
          dist (f a) (f b) ≤ (1 + η) * dist (a : X.carrier) (b : X.carrier)) ∧
      (Set.range f).Finite ∧
      (Set.range f).ncard = Nat.card L ∧
      IsDeltaNet (δ + 2 * ε) Y.base (Set.range f) := by
  obtain ⟨hinj, hbilip, hnet⟩ :=
    bilipschitz_deltaNet_image_of_pointedGHRealization
      R hεσ hη hmargin hL hsep f hclose hbase hR
  letI : Fintype L := hLfin.fintype
  have hrangefin : (Set.range f).Finite := Set.toFinite _
  have hcard : (Set.range f).ncard = Nat.card L :=
    Set.ncard_range_of_injective hinj
  exact ⟨hinj, hbilip, hrangefin, hcard, hnet⟩

/-- **Math.** A sufficiently small pointed realization itself supplies a
basepoint-preserving correspondence from a separated net. Its image is a
target net and the correspondence is injective and bilipschitz at the stated
scale; no choice of nearby-point map is required as an input. -/
theorem exists_bilipschitz_deltaNet_image_of_pointedGHRealization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {δ ε σ η : ℝ}
    (hε : 0 < ε)
    (hεσ : 2 * ε < σ)
    (hη : 0 ≤ η)
    (hmargin : 2 * ε ≤ η * σ)
    {L : Set X.carrier} (hL : IsDeltaNet δ X.base L)
    (hsep : ∀ ⦃a b : X.carrier⦄, a ∈ L → b ∈ L → a ≠ b → σ ≤ dist a b)
    (hR : pointedHausdorffDist R < ε) :
    ∃ f : L → Y.carrier,
      f ⟨X.base, hL.1⟩ = Y.base ∧
      Function.Injective f ∧
      (∀ a b : L,
        (1 - η) * dist (a : X.carrier) (b : X.carrier) ≤
            dist (f a) (f b) ∧
          dist (f a) (f b) ≤
            (1 + η) * dist (a : X.carrier) (b : X.carrier)) ∧
      IsDeltaNet (δ + 2 * ε) Y.base (Set.range f) := by
  have hnear : ∀ z : L, ∃ y : Y.carrier,
      dist (R.left z.1) (R.right y) < ε ∧
        (z.1 = X.base → y = Y.base) := by
    intro z
    by_cases hz : z.1 = X.base
    · refine ⟨Y.base, ?_, fun _ => rfl⟩
      calc
        dist (R.left z.1) (R.right Y.base) =
            dist R.ambient.base R.ambient.base := by
          rw [hz, R.left_base, R.right_base]
        _ = 0 := dist_self _
        _ < ε := hε
    · obtain ⟨y, hy⟩ :=
        exists_right_point_lt_of_pointedHausdorffDist_lt R hR z.1
      exact ⟨y, hy, fun h => (hz h).elim⟩
  choose f hclose hbase_if using hnear
  have hbase : f ⟨X.base, hL.1⟩ = Y.base :=
    hbase_if ⟨X.base, hL.1⟩ rfl
  obtain ⟨hinj, hbilip, hnet⟩ :=
    bilipschitz_deltaNet_image_of_pointedGHRealization
      R hεσ hη hmargin hL hsep f hclose hbase hR
  exact ⟨f, hbase, hinj, hbilip, hnet⟩

/-- **Math.** The forward implication in the finite-net characterization of
pointed Gromov--Hausdorff convergence. Every separated target `δ`-net is,
eventually, equivalent to a based `(δ + η)`-net in the source. The equivalence
has the explicit two-sided `(1 ± η)` metric bounds; its inverse is the
bijection oriented as in Morgan--Tian's statement. -/
theorem eventually_exists_bilipschitz_deltaNet_equiv_of_pointedGHConverges
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (hconv : PointedGHConverges X Y)
    {δ η : ℝ} (hη : 0 < η)
    {L : Set Y.carrier} (hL : IsDeltaNet δ Y.base L) :
    ∀ᶠ k in Filter.atTop,
      ∃ K : Set (X k).carrier, ∃ e : L ≃ K,
        (e ⟨Y.base, hL.1⟩ : (X k).carrier) = (X k).base ∧
        IsDeltaNet (δ + η) (X k).base K ∧
        ∀ a b : L,
          (1 - η) * dist (a : Y.carrier) (b : Y.carrier) ≤
              dist (e a) (e b) ∧
            dist (e a) (e b) ≤
              (1 + η) * dist (a : Y.carrier) (b : Y.carrier) := by
  obtain ⟨σ, hσ, hsep⟩ := hL.2.2
  let m : ℝ := min η (min σ (η * σ))
  let ε : ℝ := m / 4
  have hησ : 0 < η * σ := mul_pos hη hσ
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min hη (lt_min hσ hησ)
  have hmη : m ≤ η := min_le_left _ _
  have hmσ : m ≤ σ := (min_le_right _ _).trans (min_le_left _ _)
  have hmησ : m ≤ η * σ :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεσ : 2 * ε < σ := by
    dsimp [ε]
    nlinarith
  have hmargin : 2 * ε ≤ η * σ := by
    dsimp [ε]
    nlinarith
  have hmesh : δ + 2 * ε ≤ δ + η := by
    dsimp [ε]
    nlinarith
  have hsmall :
      ∀ᶠ k in Filter.atTop, pointedGHDistance (X k) Y < ε / 2 :=
    hconv.2.eventually_lt_const (half_pos hε)
  filter_upwards [hsmall] with k hk
  obtain ⟨R, hRapprox⟩ :=
    exists_pointedGHRealization_lt_add (X k) Y (half_pos hε)
  have hR : pointedHausdorffDist R < ε := by
    linarith
  let R' : PointedGHRealization Y (X k) :=
    { ambient := R.ambient
      left := R.right
      right := R.left
      left_isometry := R.right_isometry
      right_isometry := R.left_isometry
      left_base := R.right_base
      right_base := R.left_base }
  have hR' : pointedHausdorffDist R' < ε := by
    simpa [pointedHausdorffDist, R', Metric.hausdorffDist_comm] using hR
  obtain ⟨f, hbase, hinj, hbilip, hnet⟩ :=
    exists_bilipschitz_deltaNet_image_of_pointedGHRealization
      R' hε hεσ hη.le hmargin hL hsep hR'
  let K : Set (X k).carrier := Set.range f
  let e : L ≃ K := Equiv.ofInjective f hinj
  refine ⟨K, e, ?_, ?_, ?_⟩
  · simpa [e, K, Equiv.ofInjective_apply] using hbase
  · simpa [K] using hnet.mono hmesh
  · intro a b
    change
      (1 - η) * dist (a : Y.carrier) (b : Y.carrier) ≤
          dist (f a) (f b) ∧
        dist (f a) (f b) ≤
          (1 + η) * dist (a : Y.carrier) (b : Y.carrier)
    exact hbilip a b

/-- **Math.** The reverse finite-net implication for a compact target. If every
positive-scale target net eventually admits the based bilipschitz models from
the forward theorem, then the source spaces converge in pointed
Gromov--Hausdorff distance. Compactness is used only to choose a finite target
net; the approximating source spaces need not be compact. -/
theorem pointedGHConverges_of_eventually_exists_bilipschitz_deltaNet_equiv
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    [CompactSpace Y.carrier]
    (hbounded : UniformlyBoundedDiameter X)
    (hnets :
      ∀ {δ : ℝ}, 0 < δ →
      ∀ {L : Set Y.carrier}, (hL : IsDeltaNet δ Y.base L) →
      ∀ {η : ℝ}, 0 < η →
        ∀ᶠ k in Filter.atTop,
          ∃ K : Set (X k).carrier, ∃ e : L ≃ K,
            (e ⟨Y.base, hL.1⟩ : (X k).carrier) = (X k).base ∧
            IsDeltaNet (δ + η) (X k).base K ∧
            ∀ a b : L,
              (1 - η) * dist (a : Y.carrier) (b : Y.carrier) ≤
                  dist (e a) (e b) ∧
                dist (e a) (e b) ≤
                  (1 + η) * dist (a : Y.carrier) (b : Y.carrier)) :
    PointedGHConverges X Y := by
  refine ⟨hbounded, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  obtain ⟨C, hC⟩ := Y.finite_diameter
  have hC0 : 0 ≤ C := by
    simpa using hC Y.base Y.base
  let δ : ℝ := ε / 8
  let η : ℝ := ε / (8 * (C + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hC1 : 0 < C + 1 := by linarith
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨L, hLfin, hL⟩ :=
    exists_finite_isDeltaNet_of_compactSpace δ hδ Y.base
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hnets hδ hL hη)
  refine ⟨N, ?_⟩
  intro k hk
  obtain ⟨K, e, hbase, hK, hbilip⟩ := hN k hk
  letI : Fintype L := hLfin.fintype
  letI : Fintype K := Fintype.ofEquiv L e
  let α : ℝ := η * C
  have hα : 0 ≤ α := mul_nonneg hη.le hC0
  let YL := deltaNetModel Y L hL.1
  let XK := deltaNetModel (X k) K hK.1
  letI : Fintype YL.carrier := by
    change Fintype L
    infer_instance
  letI : Fintype XK.carrier := by
    change Fintype K
    infer_instance
  let e' : YL.carrier ≃ XK.carrier := e
  have hbase' : e' YL.base = XK.base := by
    apply Subtype.ext
    exact hbase
  have hdist' : ∀ a b : YL.carrier,
      |dist a b - dist (e' a) (e' b)| ≤ α := by
    intro a b
    change
      |dist (a.1 : Y.carrier) (b.1 : Y.carrier) -
          dist ((e' a).1 : (X k).carrier) ((e' b).1 : (X k).carrier)| ≤ α
    have hab := hbilip (show L from a) (show L from b)
    change
      (1 - η) * dist (a.1 : Y.carrier) (b.1 : Y.carrier) ≤
          dist ((e' a).1 : (X k).carrier) ((e' b).1 : (X k).carrier) ∧
        dist ((e' a).1 : (X k).carrier) ((e' b).1 : (X k).carrier) ≤
          (1 + η) * dist (a.1 : Y.carrier) (b.1 : Y.carrier) at hab
    have hdiam : dist (a.1 : Y.carrier) (b.1 : Y.carrier) ≤ C :=
      hC a.1 b.1
    have hetaDiam :
        η * dist (a.1 : Y.carrier) (b.1 : Y.carrier) ≤ η * C :=
      mul_le_mul_of_nonneg_left hdiam hη.le
    rw [abs_le]
    constructor
    · dsimp [α]
      nlinarith [hab.2, hetaDiam]
    · dsimp [α]
      nlinarith [hab.1, hetaDiam]
  have hmiddle : pointedGHDistance YL XK ≤ α :=
    pointedGHDistance_le_of_separable_approximate_equiv
      e' hbase' hα hdist'
  have hmiddle' : pointedGHDistance XK YL ≤ α := by
    rw [pointedGHDistance_symm]
    exact hmiddle
  have hleft : pointedGHDistance (X k) XK ≤ δ + η :=
    pointedGHDistance_le_deltaNet (X k) (δ + η)
      (add_nonneg hδ.le hη.le) K hK
  have hright : pointedGHDistance YL Y ≤ δ := by
    rw [pointedGHDistance_symm]
    exact pointedGHDistance_le_deltaNet Y δ hδ.le L hL
  have htotal :
      pointedGHDistance (X k) Y ≤ (δ + η) + α + δ := by
    calc
      pointedGHDistance (X k) Y ≤
          pointedGHDistance (X k) XK + pointedGHDistance XK Y :=
        pointedGHDistance_triangle _ _ _
      _ ≤ pointedGHDistance (X k) XK +
          (pointedGHDistance XK YL + pointedGHDistance YL Y) := by
        exact add_le_add (le_refl _)
          (pointedGHDistance_triangle XK YL Y)
      _ ≤ (δ + η) + (α + δ) :=
        add_le_add hleft (add_le_add hmiddle' hright)
      _ = (δ + η) + α + δ := by ring
  have heta_sum : η * (C + 1) = ε / 8 := by
    dsimp [η]
    field_simp
  have hbudget : (δ + η) + α + δ < ε := by
    calc
      (δ + η) + α + δ = 2 * δ + η * (C + 1) := by
        dsimp [α]
        ring
      _ = 2 * (ε / 8) + ε / 8 := by rw [heta_sum]
      _ < ε := by linarith
  have hgh : pointedGHDistance (X k) Y < ε :=
    htotal.trans_lt hbudget
  simpa [Real.dist_eq, abs_of_nonneg
    (pointedGHDistance_nonneg (X k) Y)] using hgh

/-- **Math.** For a compact target in the same universe, pointed
Gromov--Hausdorff convergence is equivalent to uniform diameter control together
with the eventual based bilipschitz finite-net criterion. -/
theorem pointedGHConverges_iff_eventually_exists_bilipschitz_deltaNet_equiv
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    [CompactSpace Y.carrier] :
    PointedGHConverges X Y ↔
      UniformlyBoundedDiameter X ∧
        ∀ {δ : ℝ}, 0 < δ →
        ∀ {L : Set Y.carrier}, (hL : IsDeltaNet δ Y.base L) →
        ∀ {η : ℝ}, 0 < η →
          ∀ᶠ k in Filter.atTop,
            ∃ K : Set (X k).carrier, ∃ e : L ≃ K,
              (e ⟨Y.base, hL.1⟩ : (X k).carrier) = (X k).base ∧
              IsDeltaNet (δ + η) (X k).base K ∧
              ∀ a b : L,
                (1 - η) * dist (a : Y.carrier) (b : Y.carrier) ≤
                    dist (e a) (e b) ∧
                  dist (e a) (e b) ≤
                    (1 + η) * dist (a : Y.carrier) (b : Y.carrier) := by
  constructor
  · intro hconv
    refine ⟨hconv.1, ?_⟩
    intro δ hδ L hL η hη
    exact
      eventually_exists_bilipschitz_deltaNet_equiv_of_pointedGHConverges
        hconv hη hL
  · rintro ⟨hbounded, hnets⟩
    exact
      pointedGHConverges_of_eventually_exists_bilipschitz_deltaNet_equiv
        X Y hbounded hnets

end MorganTianLib

end

#print axioms MorganTianLib.finite_net_bilipschitz_image_of_pointedGHRealization
#print axioms MorganTianLib.pointedGHDistance_le_of_separable_approximate_equiv
#print axioms MorganTianLib.bilipschitz_deltaNet_image_of_pointedGHRealization
#print axioms MorganTianLib.exists_bilipschitz_deltaNet_image_of_pointedGHRealization
#print axioms
  MorganTianLib.eventually_exists_bilipschitz_deltaNet_equiv_of_pointedGHConverges
#print axioms
  MorganTianLib.pointedGHConverges_of_eventually_exists_bilipschitz_deltaNet_equiv
#print axioms
  MorganTianLib.pointedGHConverges_iff_eventually_exists_bilipschitz_deltaNet_equiv
