import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

-- Semantic Lean search recalled Euclidean-ball volume lemmas in the Lebesgue measure modules; local
-- verification showed this item only needs Euclidean, measurable-space, and Lebesgue basic imports.

variable {n : ℕ}

/-- The open cube in `ℝ^n` centered at `c` with radius `r`, realized as the sup-metric ball in
`Fin n → ℝ` pulled back along the canonical equivalence with `EuclideanSpace ℝ (Fin n)`. -/
def openCube (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Metric.ball ((EuclideanSpace.equiv (Fin n) ℝ) c) r

/-- Open cubes are open subsets of `ℝ^n`. -/
theorem isOpen_openCube (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    IsOpen (openCube c r) := by
  simpa [openCube] using
    Metric.isOpen_ball.preimage (EuclideanSpace.equiv (Fin n) ℝ).continuous

/-- A sequence of open cubes covers `A` when every radius is nonnegative and their union contains
`A`; zero-radius terms serve only as padding for finite or empty countable covers. -/
def IsOpenCubeCover (A : Set (EuclideanSpace ℝ (Fin n)))
    (c : ℕ → EuclideanSpace ℝ (Fin n)) (r : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ r i) ∧ A ⊆ ⋃ i, openCube (c i) (r i)

namespace IsOpenCubeCover

/-- Every cube radius in an open-cube cover is nonnegative. -/
theorem radius_nonneg {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenCubeCover A c r) (i : ℕ) : 0 ≤ r i :=
  h.1 i

/-- The union of an open-cube cover contains the target set. -/
theorem subset_iUnion {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenCubeCover A c r) : A ⊆ ⋃ i, openCube (c i) (r i) :=
  h.2

end IsOpenCubeCover

section GenericBallCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- Helper for Exercise 6.1: doubling the radius of a ball multiplies its volume by
`2 ^ finrank ℝ E`, and closed and open balls have the same volume in finite dimensions. -/
private theorem volumeBall_two_mul_eq_mul_volumeClosedBall (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (x : E) {r : ℝ} (hr : 0 < r) :
    μ (Metric.ball x (2 * r)) =
      ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E) * μ (Metric.closedBall x r) := by
  -- Rewrite both measures using the Haar-scaling formulas for balls of radius `2 * r` and `r`.
  rw [Measure.addHaar_ball_of_pos μ x (show 0 < 2 * r by positivity)]
  rw [Measure.addHaar_closedBall μ x hr.le]
  -- The remaining identity is the real algebra `((2 * r) ^ d) = 2 ^ d * r ^ d`.
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring_nf

/-- Helper for Exercise 6.1: a null set for an additive Haar measure admits `ℕ`-indexed open-ball
covers with arbitrarily small total mass, and conversely such covers force the set to have
measure zero. -/
private theorem measure_eq_zero_iff_forall_pos_exists_smallBallCover (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] [SFinite μ] [Measure.OuterRegular μ]
    {A : Set E} :
    μ A = 0 ↔
      ∀ ε > 0, ∃ c : ℕ → E, ∃ r : ℕ → ℝ,
        (∀ i, 0 ≤ r i) ∧ A ⊆ ⋃ i, Metric.ball (c i) (r i) ∧
        (∑' i, μ (Metric.ball (c i) (r i))) < ENNReal.ofReal ε := by
  constructor
  · intro hA ε hε
    let scale : ℝ := (2 : ℝ) ^ Module.finrank ℝ E
    let η : ℝ := ε / (2 * scale)
    have hScalePos : 0 < scale := by
      dsimp [scale]
      positivity
    have hηpos : 0 < η := by
      dsimp [η]
      positivity
    obtain ⟨t, ρ, htCount, htsub, hρmem, hcover, hsum⟩ :=
      Besicovitch.exists_closedBall_covering_tsum_measure_le μ
        (ε := ENNReal.ofReal η)
        (by positivity)
        (fun _ ↦ Set.Ioi (0 : ℝ)) A
        (fun _ _ δ hδ ↦ ⟨δ / 2, by simp [half_pos hδ, hδ]⟩)
    haveI : Encodable t := htCount.toEncodable
    let c : ℕ → E := fun i =>
      match Encodable.decode₂ t i with
      | some x => (x : E)
      | none => 0
    let r : ℕ → ℝ := fun i =>
      match Encodable.decode₂ t i with
      | some x => 2 * ρ x
      | none => 0
    have hρpos : ∀ x : t, 0 < ρ x := by
      intro x
      simpa using hρmem x x.2
    have hcover' : ∀ x ∈ A, ∃ y ∈ t, x ∈ Metric.closedBall y (ρ y) := by
      simpa [Set.subset_def, Set.mem_iUnion] using hcover
    refine ⟨c, r, ?_, ?_, ?_⟩
    · intro i
      -- Decoded indices inherit positive radii; padded indices use radius `0`.
      dsimp [r]
      cases hdec : Encodable.decode₂ t i with
      | none =>
          simp
      | some x =>
          exact (mul_nonneg (by positivity) (hρpos x).le)
    · intro x hxA
      -- Encode the center supplied by Besicovitch to land in the required `ℕ`-indexed cover.
      rcases hcover' x hxA with ⟨y, hyt, hxy⟩
      let y' : t := ⟨y, hyt⟩
      have hypos : 0 < ρ y := hρpos y'
      have hyball : x ∈ Metric.ball y (2 * ρ y) := by
        exact Metric.closedBall_subset_ball (by linarith) hxy
      refine Set.mem_iUnion.2 ⟨Encodable.encode y', ?_⟩
      simpa [c, r, Encodable.encodek₂ y']
        using hyball
    · -- Compare the nat-indexed mass with the Besicovitch closed-ball mass via `decode₂`.
      have hdecodeMass :
          (∑' i, μ (Metric.ball (c i) (r i))) =
            ∑' i, μ (⋃ x ∈ Encodable.decode₂ t i, Metric.ball (x : E) (2 * ρ x)) := by
        apply tsum_congr
        intro i
        dsimp [c, r]
        cases hdec : Encodable.decode₂ t i with
        | none =>
            simp
        | some x =>
            simp
      have hballMass :
          (∑' x : t, μ (Metric.ball (x : E) (2 * ρ x))) =
            ENNReal.ofReal scale * ∑' x : t, μ (Metric.closedBall (x : E) (ρ x)) := by
        calc
          (∑' x : t, μ (Metric.ball (x : E) (2 * ρ x))) =
              ∑' x : t, ENNReal.ofReal scale * μ (Metric.closedBall (x : E) (ρ x)) := by
                apply tsum_congr
                intro x
                simpa [scale] using
                  volumeBall_two_mul_eq_mul_volumeClosedBall μ (x : E) (hρpos x)
          _ = ENNReal.ofReal scale * ∑' x : t, μ (Metric.closedBall (x : E) (ρ x)) := by
                rw [ENNReal.tsum_mul_left]
      have hscaleHalf :
          ENNReal.ofReal scale * ENNReal.ofReal η = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [η, scale]
        field_simp [hScalePos.ne']
      have hhalfLt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
        exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
      refine lt_of_le_of_lt ?_ hhalfLt
      calc
        (∑' i, μ (Metric.ball (c i) (r i))) =
            ∑' i, μ (⋃ x ∈ Encodable.decode₂ t i, Metric.ball (x : E) (2 * ρ x)) :=
          hdecodeMass
        _ = ∑' x : t, μ (Metric.ball (x : E) (2 * ρ x)) := by
          rw [tsum_iUnion_decode₂ (fun s : Set E => μ s) (by simp)
            (fun x : t => Metric.ball (x : E) (2 * ρ x))]
        _ = ENNReal.ofReal scale * ∑' x : t, μ (Metric.closedBall (x : E) (ρ x)) := hballMass
        _ ≤ ENNReal.ofReal scale * (μ A + ENNReal.ofReal η) := by
          gcongr
        _ = ENNReal.ofReal scale * ENNReal.ofReal η := by rw [hA, zero_add]
        _ = ENNReal.ofReal (ε / 2) := hscaleHalf
  · intro hsmall
    by_cases hA : μ A = 0
    · exact hA
    -- First obtain finiteness from the `ε = 1` cover, then contradict strict smallness at `μ A`.
    have hFinite : μ A < ⊤ := by
      obtain ⟨c, r, _, hcover, hmass⟩ := hsmall 1 zero_lt_one
      calc
        μ A ≤ μ (⋃ i, Metric.ball (c i) (r i)) := measure_mono hcover
        _ ≤ ∑' i, μ (Metric.ball (c i) (r i)) := measure_iUnion_le _
        _ < ENNReal.ofReal (1 : ℝ) := hmass
        _ < ⊤ := by simp
    have hAtoRealPos : 0 < (μ A).toReal := ENNReal.toReal_pos hA hFinite.ne
    obtain ⟨c, r, _, hcover, hmass⟩ := hsmall (μ A).toReal hAtoRealPos
    have hlt :
        μ A < μ A := by
      calc
        μ A ≤ μ (⋃ i, Metric.ball (c i) (r i)) := measure_mono hcover
        _ ≤ ∑' i, μ (Metric.ball (c i) (r i)) := measure_iUnion_le _
        _ < ENNReal.ofReal (μ A).toReal := hmass
        _ = μ A := ENNReal.ofReal_toReal hFinite.ne
    exact False.elim ((lt_irrefl _) hlt)

end GenericBallCover

/-- Helper for Exercise 6.1: `openCube c r` is the pullback of the corresponding function-space
ball, so the canonical Euclidean/function-space measurable equivalence preserves its volume. -/
private theorem volume_openCube_eq_volume_ball (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    volume (openCube c r) =
      volume (Metric.ball ((EuclideanSpace.equiv (Fin n) ℝ) c) r) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ᵐ (Fin n → ℝ) := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  have he : MeasurePreserving e volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  -- The cube is literally the preimage of the corresponding ball under the measure-preserving
  -- equivalence.
  simpa [openCube, e, EuclideanSpace.equiv] using
    (MeasureTheory.MeasurePreserving.measure_preimage_equiv he
      (Metric.ball (e c) r))

/-- Helper for Exercise 6.1: a ball cover of the coordinate image of `A` pulls back to a cube
cover of `A` with the same radii. -/
private theorem imageBallCover_pullbackCubeCover {A : Set (EuclideanSpace ℝ (Fin n))}
    {d : ℕ → Fin n → ℝ} {ρ : ℕ → ℝ}
    (hρnonneg : ∀ i, 0 ≤ ρ i)
    (hcover : ((EuclideanSpace.equiv (Fin n) ℝ) '' A) ⊆ ⋃ i, Metric.ball (d i) (ρ i)) :
    IsOpenCubeCover A (fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ).symm (d i)) ρ := by
  constructor
  · exact hρnonneg
  · intro x hx
    have hxImage : (EuclideanSpace.equiv (Fin n) ℝ) x ∈ (EuclideanSpace.equiv (Fin n) ℝ) '' A :=
      ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.1 (hcover hxImage) with ⟨i, hi⟩
    -- Membership in the pulled-back cube is just the corresponding ball-membership after applying
    -- the canonical equivalence.
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simpa [openCube] using hi

/-- Exercise 6.1. Open rectangles can be replaced by open cubes or open balls in the definition of
subsets of measure zero. This theorem records the open-cube formulation. -/
theorem volume_eq_zero_iff_forall_pos_exists_open_cube_cover
    {A : Set (EuclideanSpace ℝ (Fin n))} :
    volume A = 0 ↔
      ∀ ε > 0, ∃ c : ℕ → EuclideanSpace ℝ (Fin n), ∃ r : ℕ → ℝ,
        IsOpenCubeCover A c r ∧
        (∑' i, volume (openCube (c i) (r i))) < ENNReal.ofReal ε := by
  let e : EuclideanSpace ℝ (Fin n) ≃ᵐ (Fin n → ℝ) := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  have he : MeasurePreserving e volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  constructor
  · intro hA ε hε
    have hImageZero : volume (e '' A) = 0 := by
      simpa [hA] using
        (MeasureTheory.MeasurePreserving.measure_preimage_equiv he (e '' A)).symm
    -- Route correction: prove the cube statement by moving to `Fin n → ℝ`, applying the generic
    -- small-ball theorem there, and pulling the cover back through the canonical equivalence.
    obtain ⟨d, ρ, hρnonneg, hsubset, hmass⟩ :=
      (measure_eq_zero_iff_forall_pos_exists_smallBallCover
        (μ := (volume : Measure (Fin n → ℝ))) (A := e '' A)).1 hImageZero ε hε
    refine ⟨fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ).symm (d i), ρ,
      imageBallCover_pullbackCubeCover hρnonneg hsubset, ?_⟩
    -- Cube volumes agree termwise with the transported ball volumes.
    calc
      (∑' i, volume (openCube ((EuclideanSpace.equiv (Fin n) ℝ).symm (d i)) (ρ i))) =
          ∑' i, volume (Metric.ball (d i) (ρ i)) := by
            apply tsum_congr
            intro i
            simpa using
              volume_openCube_eq_volume_ball ((EuclideanSpace.equiv (Fin n) ℝ).symm (d i)) (ρ i)
      _ < ENNReal.ofReal ε := hmass
  · intro hcube
    have hImageCover :
        ∀ ε > 0, ∃ d : ℕ → Fin n → ℝ, ∃ ρ : ℕ → ℝ,
          (∀ i, 0 ≤ ρ i) ∧
            e '' A ⊆ ⋃ i, Metric.ball (d i) (ρ i) ∧
            (∑' i, volume (Metric.ball (d i) (ρ i))) < ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨c, ρ, hcover, hmass⟩ := hcube ε hε
      refine ⟨fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ) (c i), ρ, hcover.1, ?_, ?_⟩
      · intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases Set.mem_iUnion.1 (hcover.2 hx) with ⟨i, hi⟩
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        simpa [openCube] using
          (show (EuclideanSpace.equiv (Fin n) ℝ) x ∈
              Metric.ball ((EuclideanSpace.equiv (Fin n) ℝ) (c i)) (ρ i) from hi)
      · calc
          (∑' i, volume (Metric.ball ((EuclideanSpace.equiv (Fin n) ℝ) (c i)) (ρ i))) =
              ∑' i, volume (openCube (c i) (ρ i)) := by
                apply tsum_congr
                intro i
                symm
                simpa using volume_openCube_eq_volume_ball (c i) (ρ i)
          _ < ENNReal.ofReal ε := hmass
    have hImageZero : volume (e '' A) = 0 :=
      (measure_eq_zero_iff_forall_pos_exists_smallBallCover
        (μ := (volume : Measure (Fin n → ℝ))) (A := e '' A)).2 hImageCover
    -- Pull the zero-mass conclusion back through the same measure-preserving equivalence.
    simpa [hImageZero] using
      (MeasureTheory.MeasurePreserving.measure_preimage_equiv he (e '' A))

/-- A sequence of open balls covers `A` when every radius is nonnegative and their union contains
`A`; zero-radius terms serve only as padding for finite or empty countable covers. -/
def IsOpenBallCover (A : Set (EuclideanSpace ℝ (Fin n)))
    (c : ℕ → EuclideanSpace ℝ (Fin n)) (r : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ r i) ∧ A ⊆ ⋃ i, Metric.ball (c i) (r i)

namespace IsOpenBallCover

/-- Every ball radius in an open-ball cover is nonnegative. -/
theorem radius_nonneg {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenBallCover A c r) (i : ℕ) : 0 ≤ r i :=
  h.1 i

/-- The union of an open-ball cover contains the target set. -/
theorem subset_iUnion {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℕ → EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} (h : IsOpenBallCover A c r) : A ⊆ ⋃ i, Metric.ball (c i) (r i) :=
  h.2

end IsOpenBallCover

/-- Companion ball-cover formulation: a subset has measure zero if and only if it can be covered by
countably many open balls whose total volume is arbitrarily small. -/
theorem volume_eq_zero_iff_forall_pos_exists_open_ball_cover
    {A : Set (EuclideanSpace ℝ (Fin n))} :
    volume A = 0 ↔
      ∀ ε > 0, ∃ c : ℕ → EuclideanSpace ℝ (Fin n), ∃ r : ℕ → ℝ,
        IsOpenBallCover A c r ∧
        (∑' i, volume (Metric.ball (c i) (r i))) < ENNReal.ofReal ε := by
  -- The public ball theorem is exactly the Euclidean specialization of the generic Haar-measure
  -- cover characterization proved above.
  simpa [IsOpenBallCover, and_assoc, and_left_comm, and_comm] using
    (measure_eq_zero_iff_forall_pos_exists_smallBallCover
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (A := A))
