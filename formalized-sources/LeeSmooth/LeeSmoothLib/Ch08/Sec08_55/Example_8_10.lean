import Mathlib
import Mathlib.Geometry.Manifold.Instances.Sphere
import LeeSmoothLib.Ch01.Sec01.Example_1_8
import LeeSmoothLib.Ch04.Sec04_26.Example_4_35
import LeeSmoothLib.Ch08.Sec08_54.Example_8_2
import LeeSmoothLib.Ch08.Sec08_54.Example_8_4
import LeeSmoothLib.Ch08.Sec08_54.Example_8_5
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Torus

noncomputable section

-- Domain sampling pass:
-- * primary domain: smooth tangent-bundle frames on manifolds;
-- * inspected owner/API declarations: mathlib's `IsLocalFrameOn`,
--   `smooth_chart_coordinate_vector_field`, `circle_angle_vector_field`, and the chapter's torus
--   angle-coordinate vector fields from Example 8.5;
-- * core/canonical owner: `IsLocalFrameOn`;
-- * primitive data: a family of tangent-bundle sections, with smoothness and pointwise basis
--   properties derived through `IsLocalFrameOn` rather than stored in a parallel wrapper API.

section

variable {n : ℕ}

/-- Helper for Example 8.10: on any open subset of `ℝⁿ`, the standard coordinate vector fields
form a smooth local frame. -/
lemma modelCoordinateVectorField_isLocalFrameOn
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞
      (model_coordinate_vector_field U) Set.univ := by
  refine
    { linearIndependent := by
        intro y hy
        -- Transport the tangent vectors once to the ambient Euclidean basis.
        let φy : TangentSpace (𝓡 n) y ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
          NormedSpace.fromTangentSpace
            (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
        have hbasis :
            LinearIndependent ℝ (fun i : Fin n ↦ (EuclideanSpace.basisFun (Fin n) ℝ) i) :=
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
        simpa only [model_coordinate_vector_field] using
          LinearIndependent.map' hbasis φy.symm.toLinearMap
            (LinearMap.ker_eq_bot.mpr φy.symm.injective)
      generating := by
        intro y hy
        -- Once pointwise independence is known, cardinality equals finrank gives spanning.
        let φy : TangentSpace (𝓡 n) y ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
          NormedSpace.fromTangentSpace
            (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
        have hbasis :
            LinearIndependent ℝ (fun i : Fin n ↦ (EuclideanSpace.basisFun (Fin n) ℝ) i) :=
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
        have hlin :
            LinearIndependent ℝ (fun i : Fin n ↦ model_coordinate_vector_field U i y) := by
          simpa only [model_coordinate_vector_field] using
            LinearIndependent.map' hbasis φy.symm.toLinearMap
              (LinearMap.ker_eq_bot.mpr φy.symm.injective)
        letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) := by
          change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n))
          infer_instance
        have hcard :
            Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace (𝓡 n) y) := by
          change Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
          simp
        exact (hlin.span_eq_top_of_card_eq_finrank' hcard).ge
      contMDiffOn := by
        intro i
        -- Smoothness is exactly the constant-coordinate smoothness from Example 8.2.
        simpa using (model_coordinate_vector_field_smooth U i).contMDiffOn }

/-- Part (1) of Example 8.10: the standard coordinate vector fields form a smooth global frame for
`ℝⁿ`. -/
theorem example_8_10_euclidean_coordinate_frame (n : ℕ) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞
      (model_coordinate_vector_field
        (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))))
      Set.univ := by
  -- Specialize the open-subset frame to the global open set.
  simpa using
    (modelCoordinateVectorField_isLocalFrameOn
      (n := n) (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))))

end

section

variable {n : ℕ}
variable {M : Type*} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : ℕ∞ω) M]

/-- Helper for Example 8.10: the differential of a smooth chart sends the chart coordinate vector
fields back to the model coordinate vector fields. -/
lemma smoothChartCoordinateVectorField_mfderiv_eq_model
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M)
    (i : Fin n) (x : (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M)) :
    mfderiv (𝓡 n) (𝓡 n) (smoothChartDiffeomorph e he) x
      (smooth_chart_coordinate_vector_field e he i x) =
        model_coordinate_vector_field
          (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) i
          (smoothChartDiffeomorph e he x) := by
  -- Evaluate the vector-field pullback and cancel the inverse derivative once.
  rw [smooth_chart_coordinate_vector_field, VectorField.mpullback_apply]
  simpa using
    (smoothChartDiffeomorph_mfderiv_isInvertible e he x).self_apply_inverse
      (model_coordinate_vector_field
        (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) i
        (smoothChartDiffeomorph e he x))

/-- Part (2) of Example 8.10: for any smooth coordinate chart on an `n`-manifold, the associated
coordinate vector fields form a smooth local frame on the chart domain. -/
theorem example_8_10_chart_coordinate_frame
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞
      (smooth_chart_coordinate_vector_field e he) Set.univ := by
  let U := (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
  let Φ := smoothChartDiffeomorph e he
  have hModel := modelCoordinateVectorField_isLocalFrameOn (n := n) U
  refine
    { linearIndependent := by
        intro x hx
        -- Pull pointwise independence back through the chart derivative equivalence.
        let φx := Φ.mfderivToContinuousLinearEquiv (by simp) x
        have hlinModel :
            LinearIndependent ℝ (fun i : Fin n ↦ model_coordinate_vector_field U i (Φ x)) :=
          hModel.linearIndependent (by simp)
        have hpull :
            (fun i : Fin n ↦ smooth_chart_coordinate_vector_field e he i x) =
              fun i : Fin n ↦ φx.symm (model_coordinate_vector_field U i (Φ x)) := by
          funext i
          have hφx :
              (φx : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) (Φ x)) =
                mfderiv (𝓡 n) (𝓡 n) Φ x := by
            simpa [Φ, φx] using
              (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (hn := by simp) (x := x))
          have hvalue :
              φx (smooth_chart_coordinate_vector_field e he i x) =
                model_coordinate_vector_field U i (Φ x) := by
            simpa [U, Φ, hφx] using
              smoothChartCoordinateVectorField_mfderiv_eq_model (e := e) (he := he) i x
          apply φx.injective
          simpa using hvalue
        simpa [hpull] using
          LinearIndependent.map' hlinModel φx.symm.toLinearMap
            (LinearMap.ker_eq_bot.mpr φx.symm.injective)
      generating := by
        intro x hx
        -- The same cardinality argument upgrades pointwise independence to spanning.
        let φx := Φ.mfderivToContinuousLinearEquiv (by simp) x
        have hlinModel :
            LinearIndependent ℝ (fun i : Fin n ↦ model_coordinate_vector_field U i (Φ x)) :=
          hModel.linearIndependent (by simp)
        have hpull :
            (fun i : Fin n ↦ smooth_chart_coordinate_vector_field e he i x) =
              fun i : Fin n ↦ φx.symm (model_coordinate_vector_field U i (Φ x)) := by
          funext i
          have hφx :
              (φx : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) (Φ x)) =
                mfderiv (𝓡 n) (𝓡 n) Φ x := by
            simpa [Φ, φx] using
              (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (hn := by simp) (x := x))
          have hvalue :
              φx (smooth_chart_coordinate_vector_field e he i x) =
                model_coordinate_vector_field U i (Φ x) := by
            simpa [U, Φ, hφx] using
              smoothChartCoordinateVectorField_mfderiv_eq_model (e := e) (he := he) i x
          apply φx.injective
          simpa using hvalue
        have hlin :
            LinearIndependent ℝ
              (fun i : Fin n ↦ smooth_chart_coordinate_vector_field e he i x) := by
          simpa [hpull] using
            LinearIndependent.map' hlinModel φx.symm.toLinearMap
              (LinearMap.ker_eq_bot.mpr φx.symm.injective)
        letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
          change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n))
          infer_instance
        have hcard :
            Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace (𝓡 n) x) := by
          change Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
          simp
        exact (hlin.span_eq_top_of_card_eq_finrank' hcard).ge
      contMDiffOn := by
        intro i
        -- Smoothness was already established for each chart coordinate field in Example 8.2.
        simpa using (smooth_chart_coordinate_vector_field_smooth e he i).contMDiffOn }

/-- Part (3) of Example 8.10: every point of a smooth manifold lies in the domain of a coordinate
frame. -/
theorem example_8_10_point_mem_coordinate_frame_domain (x : M) :
    ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M),
      x ∈ e.source ∧
        IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞
          (smooth_chart_coordinate_vector_field e he) Set.univ := by
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  let he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := (⊤ : ℕ∞ω)) x
  refine ⟨e, he, ?_, ?_⟩
  · -- Every point lies in the source of its chosen chart.
    simp [e]
  · -- The chosen chart already carries the coordinate frame from the previous theorem.
    simpa [e, he] using example_8_10_chart_coordinate_frame (n := n) e he

end

/-- Helper for Example 8.10: the circle angle vector field never vanishes. -/
lemma circleAngleVectorField_ne_zero (z : Circle) :
    circle_angle_vector_field z ≠ 0 := by
  rcases Circle.exp_surjective z with ⟨t, rfl⟩
  let φt :=
    IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
      circle_exp_isSmoothCoveringMap.isLocalDiffeomorph (by simp) t
  have hunit :
      (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t).symm) (1 : ℝ) :
        TangentSpace (𝓘(ℝ)) t) ≠ 0 := by
    intro hzero
    have himage :=
      congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t) hzero
    simp at himage
  have hfield :
      circle_angle_vector_field (Circle.exp t) =
        φt (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t).symm) (1 : ℝ)) := by
    -- Rewrite the pulled-back angle field as the local-diffeomorphism derivative image of `1`.
    have hφt :
        (φt : TangentSpace (𝓘(ℝ)) t →L[ℝ] TangentSpace (𝓡 1) (Circle.exp t)) =
          mfderiv (𝓘(ℝ)) (𝓡 1) Circle.exp t := by
      simpa [φt] using
        (IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
          (hf := circle_exp_isSmoothCoveringMap.isLocalDiffeomorph) (hn := by simp) (x := t))
    calc
      circle_angle_vector_field (Circle.exp t) =
          mfderiv (𝓘(ℝ)) (𝓡 1) Circle.exp t
            (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t).symm) (1 : ℝ)) := by
          exact circle_angle_vector_field_apply_exp t
      _ = φt (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) t).symm) (1 : ℝ)) := by
          rw [← hφt]
          rfl
  intro hz
  apply hunit
  rw [hfield] at hz
  have hz0 := congrArg φt.symm hz
  rw [ContinuousLinearEquiv.symm_apply_apply] at hz0
  rw [map_zero] at hz0
  exact hz0

/-- Part (4) of Example 8.10: the circle angle vector field `d / dθ` from Example 8.4 is a
smooth global frame on `S¹`. -/
theorem example_8_10_circle_angle_frame :
    IsLocalFrameOn (𝓡 1) (EuclideanSpace ℝ (Fin 1)) ∞
      (fun _ : Fin 1 ↦ circle_angle_vector_field) Set.univ := by
  refine
    { linearIndependent := by
        intro z hz
        -- In one dimension, pointwise independence is exactly nonvanishing.
        rw [linearIndependent_unique_iff]
        exact circleAngleVectorField_ne_zero z
      generating := by
        intro z hz
        -- The `Fin 1` family has the correct cardinality for the circle tangent fiber.
        have hlin : LinearIndependent ℝ (fun _ : Fin 1 ↦ circle_angle_vector_field z) := by
          rw [linearIndependent_unique_iff]
          exact circleAngleVectorField_ne_zero z
        letI : FiniteDimensional ℝ (TangentSpace (𝓡 1) z) := by
          change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1))
          infer_instance
        have hcard :
            Fintype.card (Fin 1) = Module.finrank ℝ (TangentSpace (𝓡 1) z) := by
          change Fintype.card (Fin 1) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))
          exact (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 1)).symm
        exact (hlin.span_eq_top_of_card_eq_finrank' hcard).ge
      contMDiffOn := by
        intro i
        -- Each member of the singleton family is the same bundled smooth circle field.
        simpa using circle_angle_vector_field.contMDiff.contMDiffOn }

section

variable (n : ℕ)

local notation "TnModel" => ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)
local notation "TnFiber" => Fin n → EuclideanSpace ℝ (Fin 1)
local instance : IsManifold TnModel ∞ (𝕋^{n}) := by infer_instance

/-- Helper for Example 8.10: at each torus point, the angle coordinate vector fields are linearly
independent. -/
lemma torusAngleCoordinateVectorField_linearlyIndependentAt (p : 𝕋^{n}) :
    LinearIndependent ℝ (fun i : Fin n ↦ torus_angle_coordinate_vector_field n i p) := by
  rcases (standard_torus_covering_isSmoothCoveringMap n).surjective p with ⟨x, rfl⟩
  let φx : TangentSpace (𝓡 n) x ≃L[ℝ] TangentSpace TnModel (standardTorusCovering n x) :=
    IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
      ((standard_torus_covering_isSmoothCoveringMap n).isLocalDiffeomorph) (by simp) x
  have hbasis :
      LinearIndependent ℝ
        (fun i : Fin n ↦
          ((NormedSpace.fromTangentSpace
            (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x).symm)
              ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
    -- Transport the standard Euclidean basis into the tangent fiber of `ℝⁿ`.
    have hstd :
        LinearIndependent ℝ (fun i : Fin n ↦ (EuclideanSpace.basisFun (Fin n) ℝ) i) :=
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
    simpa only using
      LinearIndependent.map' hstd
        (NormedSpace.fromTangentSpace
          (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x).symm.toLinearMap
        (LinearMap.ker_eq_bot.mpr
          (NormedSpace.fromTangentSpace
            (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x).symm.injective)
  -- The torus covering derivative carries those basis vectors to the torus angle fields.
  have hcover :
      (fun i : Fin n ↦ torus_angle_coordinate_vector_field n i (standardTorusCovering n x)) =
        fun i : Fin n ↦ φx (((NormedSpace.fromTangentSpace
          (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x).symm)
          ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
    funext i
    have hφx :
        (φx : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace TnModel (standardTorusCovering n x)) =
          mfderiv (𝓡 n) TnModel (standardTorusCovering n) x := by
      simpa [φx] using
        (IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
          (hf := (standard_torus_covering_isSmoothCoveringMap n).isLocalDiffeomorph)
          (hn := by simp) (x := x))
    calc
      torus_angle_coordinate_vector_field n i (standardTorusCovering n x) =
          mfderiv (𝓡 n) TnModel (standardTorusCovering n) x
            (((NormedSpace.fromTangentSpace
              (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x).symm)
              ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
          exact torus_angle_coordinate_vector_field_apply_standardTorusCovering n i x
      _ = φx (((NormedSpace.fromTangentSpace
            (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x).symm)
            ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
          rw [← hφx]
          rfl
  simpa [hcover] using
    LinearIndependent.map' hbasis φx.toLinearMap
      (LinearMap.ker_eq_bot.mpr φx.injective)

/-- Example 8.10 (5): the angle coordinate vector fields
`(∂ / ∂θ¹, ..., ∂ / ∂θⁿ)` on the `n`-torus form a smooth global frame. -/
theorem example_8_10_torus_angle_frame :
    IsLocalFrameOn TnModel TnFiber ∞ (fun i ↦ torus_angle_coordinate_vector_field n i)
      Set.univ := by
  refine
    { linearIndependent := by
        intro p hp
        -- Pointwise independence is the lifted standard-basis argument on the covering space.
        exact torusAngleCoordinateVectorField_linearlyIndependentAt n p
      generating := by
        intro p hp
        -- The torus tangent fiber has dimension `n`, so independence yields spanning.
        have hlin :
            LinearIndependent ℝ (fun i : Fin n ↦ torus_angle_coordinate_vector_field n i p) :=
          torusAngleCoordinateVectorField_linearlyIndependentAt n p
        letI : FiniteDimensional ℝ (TangentSpace TnModel p) := by
          change FiniteDimensional ℝ TnFiber
          infer_instance
        have hcard :
            Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace TnModel p) := by
          change Fintype.card (Fin n) = Module.finrank ℝ TnFiber
          rw [Module.finrank_pi_fintype]
          simp [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 1)]
        exact (hlin.span_eq_top_of_card_eq_finrank' hcard).ge
      contMDiffOn := by
        intro i
        -- Each torus angle field is already bundled with its smoothness proof.
        simpa using (torus_angle_coordinate_vector_field n i).contMDiff.contMDiffOn }

/- The pullback formula for the torus angle-coordinate vector fields is already provided by the
owner theorem from Example 8.5. -/
#check torus_angle_coordinate_vector_field_apply_standardTorusCovering

end
