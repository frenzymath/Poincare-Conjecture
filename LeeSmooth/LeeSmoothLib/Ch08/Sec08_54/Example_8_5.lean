import Mathlib
import Mathlib.Geometry.Manifold.Instances.Sphere
import LeeSmoothLib.Ch01.Sec01.Example_1_8
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_14
import LeeSmoothLib.Ch04.Sec04_26.Example_4_35
import LeeSmoothLib.Ch08.Sec08_54.Example_8_4
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Torus

noncomputable section

-- Domain sampling pass:
-- * primary domain: smooth vector fields on the torus and their angle-coordinate description;
-- * inspected owner/API declarations: `Notation_8_54_extra_3` for the canonical bundled smooth
--   vector-field owner `Cₛ^∞⟮I; E, TangentSpace I⟯`, `Example_8_4` for the chapter's angle-field
--   theorem surface, and `Proposition_8_8` for nearby bundled smooth vector-field operations;
-- * source-facing item: the torus angle vector fields `∂ / ∂θⁱ`;
-- * core/canonical owner: bundled smooth tangent-bundle sections, written with
--   `Cₛ^∞⟮I; E, TangentSpace I⟯`;
-- * primitive data is only the vector field family itself, while smoothness is derived from that
--   owner, so no local raw `ContMDiffSection` alias should remain on the public theorem surface.

section

variable (n : ℕ)

local notation "TnModel" => ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)
local notation "TnChartModel" => 𝓘(ℝ, Fin n → EuclideanSpace ℝ (Fin 1))
local notation "CircleChartModel" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
local notation "SmoothTorusVectorField" =>
  Cₛ^∞⟮TnModel; Fin n → EuclideanSpace ℝ (Fin 1), fun z : 𝕋^{n} ↦ TangentSpace TnModel z⟯
local instance : IsManifold TnModel ∞ (𝕋^{n}) := by infer_instance

/-- Helper for Example 8.5: the raw `i`th torus angle field inserts the circle angle vector field
into the `i`th factor. -/
private def torusAngleCoordinateVectorFieldRaw (i : Fin n) (z : 𝕋^{n}) : TangentSpace TnModel z :=
  show TangentSpace TnModel z from
    ((Pi.single i
        (show EuclideanSpace ℝ (Fin 1) from circle_angle_vector_field (z i))) :
      Fin n → EuclideanSpace ℝ (Fin 1))

/-- Helper for Example 8.5: the raw torus angle field has support only in the chosen coordinate. -/
private theorem torusAngleCoordinateVectorFieldRaw_apply
    (i j : Fin n) (z : 𝕋^{n}) :
    (torusAngleCoordinateVectorFieldRaw n i z) j =
      if j = i then circle_angle_vector_field (z i) else 0 := by
  -- Read the single-supported vector field coordinatewise.
  by_cases hji : j = i
  · subst hji
    simp [torusAngleCoordinateVectorFieldRaw]
  · rw [if_neg hji]
    simp [torusAngleCoordinateVectorFieldRaw, hji]
    rfl

/-- Helper for Example 8.5: the torus extended chart reads each circle coordinate separately. -/
private theorem torusExtChartAt_component
    (p z : 𝕋^{n}) (j : Fin n) :
    (extChartAt TnModel p z) j = extChartAt (𝓡 1) (p j) (z j) := by
  -- The finite-product extended chart is coordinatewise by definition.
  rfl

/-- Helper for Example 8.5: membership in a torus chart source implies membership in each circle
factor chart source. -/
private theorem torusChartAt_source_component
    (p z : 𝕋^{n}) (j : Fin n)
    (hz : z ∈ (chartAt (ModelPi fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1)) p).source) :
    z j ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) (p j)).source := by
  -- The product chart source is the coordinatewise product of the factor chart sources.
  simpa [piChartedSpace_chartAt, ModelWithCorners.pi, PartialEquiv.pi_source] using hz j

/-- Helper for Example 8.5: the `j`th torus trivialization coordinate is the `j`th coordinate of
the torus extended-chart derivative. -/
private theorem torusTrivialization_component_eq_mfderiv
    (p z : 𝕋^{n}) (v : TangentSpace TnModel z) (j : Fin n)
    (hz :
      z ∈ (trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p).baseSet) :
    ((trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p
      ⟨z, v⟩).2) j =
      ((mfderiv TnModel TnChartModel (extChartAt TnModel p) z v) j) := by
  let ψ : 𝕋^{n} → Fin n → EuclideanSpace ℝ (Fin 1) := extChartAt TnModel p
  have hzChart :
      z ∈ (chartAt (ModelPi fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1)) p).source := by
    simpa [TangentBundle.trivializationAt_baseSet] using hz
  have hcoordinate :
      (trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p
        ⟨z, v⟩).2 =
        mfderiv TnModel TnChartModel ψ z v := by
    -- Rewrite the torus trivialization fiber coordinate through the tangent-bundle linear map.
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
      (R := ℝ)
      (e := trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p)
      hz v]
    -- Identify that linear map with the manifold derivative of the torus extended chart.
    change
      (Bundle.Trivialization.continuousLinearMapAt ℝ
          (trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p) z) v =
        mfderiv TnModel TnChartModel (extChartAt TnModel p) z v
    rw [TangentBundle.continuousLinearMapAt_trivializationAt
      (I := TnModel) (x₀ := p) (x := z) hzChart]
    rfl
  simpa [ψ] using congrArg (fun w : Fin n → EuclideanSpace ℝ (Fin 1) ↦ w j) hcoordinate

/-- Helper for Example 8.5: the `j`th coordinate of the torus extended-chart derivative is the
extended-chart derivative of the `j`th circle coordinate. -/
private theorem torusExtChartAt_mfderiv_component
    (p z : 𝕋^{n}) (v : TangentSpace TnModel z) (j : Fin n)
    (hz : z ∈ (chartAt (ModelPi fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1)) p).source) :
    (mfderiv TnModel TnChartModel (extChartAt TnModel p) z v) j =
      mfderiv (𝓡 1) CircleChartModel (extChartAt (𝓡 1) (p j)) (z j) (v j) := by
  let ψ : 𝕋^{n} → Fin n → EuclideanSpace ℝ (Fin 1) := extChartAt TnModel p
  let ψj : Circle → EuclideanSpace ℝ (Fin 1) := extChartAt (𝓡 1) (p j)
  have hzj :
      z j ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) (p j)).source :=
    torusChartAt_source_component (n := n) p z j hz
  have hTorusProjection :
      MDifferentiableAt TnModel (𝓡 1) (fun q : 𝕋^{n} ↦ q j) z := by
    simpa using
      (hasMFDerivAt_piProjection (I := fun _ : Fin n ↦ 𝓡 1)
        (p := z) (j := j)).mdifferentiableAt
  have hModelProjection :
      MDifferentiableAt TnChartModel CircleChartModel
        (ContinuousLinearMap.proj j :
          (Fin n → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1))
        (ψ z) := by
    simpa using
      (ContinuousLinearMap.mdifferentiableAt
        (ContinuousLinearMap.proj j :
          (Fin n → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1)))
  have hTorusComponent :
      (((ContinuousLinearMap.proj j :
          (Fin n → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ∘ ψ)) =
        fun q : 𝕋^{n} ↦ ψj (q j) := by
    -- The torus chart is coordinatewise, so the projected torus chart is the circle chart.
    funext q
    simpa [Function.comp, ψ, ψj] using
      (torusExtChartAt_component (n := n) (p := p) (z := q) (j := j))
  have hProjectionEval :
      (mfderiv TnModel TnChartModel ψ z v) j =
        (ContinuousLinearMap.proj j :
          (Fin n → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1))
          (mfderiv TnModel TnChartModel ψ z v) := by
    rfl
  have hChartChain :
      (ContinuousLinearMap.proj j :
        (Fin n → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1))
        (mfderiv TnModel TnChartModel ψ z v) =
        mfderiv TnModel CircleChartModel (((ContinuousLinearMap.proj j :
            (Fin n → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ∘ ψ)) z v := by
    -- Differentiate the model-space projection after the torus chart map.
    simpa using
      (mfderiv_comp_apply_of_eq
        (x := z)
        (y := ψ z)
        (I := TnModel)
        (I' := 𝓘(ℝ, Fin n → EuclideanSpace ℝ (Fin 1)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)))
        (g := ContinuousLinearMap.proj j)
        (f := ψ)
        hModelProjection
        ((hasMFDerivAt_extChartAt (I := TnModel) hz).mdifferentiableAt)
        rfl
        v).symm
  have hRewriteChart :
      mfderiv TnModel CircleChartModel (((ContinuousLinearMap.proj j :
          (Fin n → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ∘ ψ)) z v =
        (mfderiv TnModel (𝓡 1) (fun q : 𝕋^{n} ↦ ψj (q j)) z) v := by
    rw [hTorusComponent]
  have hCircleChain :
      (mfderiv TnModel (𝓡 1) (fun q : 𝕋^{n} ↦ ψj (q j)) z) v =
        mfderiv (𝓡 1) CircleChartModel ψj (z j)
          (mfderiv TnModel (𝓡 1) (fun q : 𝕋^{n} ↦ q j) z v) := by
    -- Differentiate the circle chart after the `j`th torus projection.
    simpa [Function.comp] using
      (mfderiv_comp_apply_of_eq
        (x := z)
        (y := z j)
        (I := TnModel)
        (I' := 𝓡 1)
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)))
        (g := ψj)
        (f := fun q : 𝕋^{n} ↦ q j)
        ((hasMFDerivAt_extChartAt (I := 𝓡 1) hzj).mdifferentiableAt)
        hTorusProjection
        rfl
        v)
  have hProjectionComponent :
      mfderiv (𝓡 1) CircleChartModel ψj (z j)
          (mfderiv TnModel (𝓡 1) (fun q : 𝕋^{n} ↦ q j) z v) =
        mfderiv (𝓡 1) CircleChartModel ψj (z j) (v j) := by
    -- The derivative of the torus coordinate projection is the ordinary coordinate map.
    rw [mfderiv_piProjection (I := fun _ : Fin n ↦ 𝓡 1) (p := z) (j := j)]
    rfl
  simpa [ψ, ψj] using hProjectionEval.trans <|
    hChartChain.trans <| hRewriteChart.trans <| hCircleChain.trans hProjectionComponent

/-- Helper for Example 8.5: the tangent-bundle trivialization of the torus reads one coordinate at
a time. -/
private theorem torusTangentTrivialization_component
    (p z : 𝕋^{n}) (v : TangentSpace TnModel z) (j : Fin n)
    (hz :
      z ∈ (trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p).baseSet) :
    ((trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p
      ⟨z, v⟩).2) j =
      (trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p j)
        ⟨z j, v j⟩).2 := by
  -- Route correction: cross the transport boundary once by rewriting both trivializations as the
  -- manifold derivatives of their extended charts, and only then project to the `j`th coordinate.
  have hzChart :
      z ∈ (chartAt (ModelPi fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1)) p).source := by
    simpa [TangentBundle.trivializationAt_baseSet] using hz
  have hzj :
      z j ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) (p j)).source :=
    torusChartAt_source_component (n := n) p z j hzChart
  have hzjBase :
      z j ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p j)).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hzj
  let ψj : Circle → EuclideanSpace ℝ (Fin 1) := extChartAt (𝓡 1) (p j)
  have hCircleCoordinate :
      (trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p j)
        ⟨z j, v j⟩).2 =
        mfderiv (𝓡 1) CircleChartModel ψj (z j) (v j) := by
    -- Rewrite the circle trivialization coordinate by the one-dimensional chart derivative.
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
      (R := ℝ)
      (e := trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p j))
      hzjBase (v j)]
    change
      (Bundle.Trivialization.continuousLinearMapAt ℝ
          (trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p j))
          (z j)) (v j) =
        mfderiv (𝓡 1) CircleChartModel (extChartAt (𝓡 1) (p j)) (z j) (v j)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt
      (I := 𝓡 1) (x₀ := p j) (x := z j) hzj]
    rfl
  -- Compare the two trivialization coordinates through their chart-derivative descriptions.
  exact
    (torusTrivialization_component_eq_mfderiv
      (n := n) (p := p) (z := z) (v := v) (j := j) hz).trans <|
      (torusExtChartAt_mfderiv_component
        (n := n) (p := p) (z := z) (v := v) (j := j) hzChart).trans hCircleCoordinate.symm

/-- Helper for Example 8.5: the raw `i`th torus angle field is a smooth tangent-bundle section. -/
private theorem torusAngleCoordinateVectorField_contMDiff (i : Fin n) :
    ContMDiff TnModel (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)).tangent ∞
      (T% (torusAngleCoordinateVectorFieldRaw n i)) := by
  intro p
  -- Route correction: work in the tangent-bundle trivialization at `p`, where the torus section
  -- becomes a tuple of circle coordinate functions, and then prove each tuple component smoothly.
  rw [Bundle.contMDiffAt_section p]
  refine contMDiffAt_pi_space.2 ?_
  intro j
  have hpBase :
      p ∈ (trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hnear :
      {z : 𝕋^{n} |
          z ∈
            (trivializationAt
              (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p).baseSet}
        ∈ nhds p := by
    let e := trivializationAt (Fin n → EuclideanSpace ℝ (Fin 1)) (TangentSpace TnModel) p
    exact e.open_baseSet.mem_nhds hpBase
  have hProjection :
      ContMDiffAt TnModel (𝓡 1) ∞ (fun z : 𝕋^{n} ↦ z j) p := by
    -- The torus coordinate projections are smooth because they are the components of `id`.
    have hId : ContMDiff TnModel TnModel ∞ (id : 𝕋^{n} → 𝕋^{n}) := contMDiff_id
    have hp := hId p
    rw [contMDiffAt_iff_target] at hp ⊢
    constructor
    · exact (continuous_apply j).continuousAt.comp hp.1
    · exact (contMDiffAt_pi_space.1 hp.2) j
  by_cases hji : j = i
  · subst j
    have hCircle :
        ContMDiffAt (𝓡 1) (𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
          (fun y : Circle ↦
            (trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p i)
              ⟨y, circle_angle_vector_field y⟩).2) (p i) := by
      have h := circleAngleVectorField_contMDiff (p i)
      rw [Bundle.contMDiffAt_section (p i)] at h
      simpa using h
    -- On the active coordinate, the torus field reduces to the circle field after projection.
    refine (hCircle.comp p hProjection).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with z hz
    rw [torusTangentTrivialization_component
      (n := n) (p := p) (z := z)
      (v := torusAngleCoordinateVectorFieldRaw n i z) (j := i) hz]
    rw [torusAngleCoordinateVectorFieldRaw_apply (n := n) (i := i) (j := i) (z := z)]
    simp
  · -- Off the active coordinate, the trivialized torus field is identically zero near `p`.
    refine (contMDiffAt_const :
      ContMDiffAt TnModel (𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
        (fun _ : 𝕋^{n} ↦ (0 : EuclideanSpace ℝ (Fin 1))) p).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with z hz
    have hz' :
        z ∈ (chartAt (ModelPi fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1)) p).source := by
      simpa [TangentBundle.trivializationAt_baseSet] using hz
    have hzj :
        z j ∈ (trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p j)).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet] using
        torusChartAt_source_component (n := n) p z j hz'
    rw [torusTangentTrivialization_component
      (n := n) (p := p) (z := z)
      (v := torusAngleCoordinateVectorFieldRaw n i z) (j := j) hz]
    rw [torusAngleCoordinateVectorFieldRaw_apply (n := n) (i := i) (j := j) (z := z)]
    rw [if_neg hji]
    simpa [Bundle.zeroSection] using
      congrArg Prod.snd <|
        (trivializationAt (EuclideanSpace ℝ (Fin 1)) (TangentSpace (𝓡 1)) (p j)).zeroSection
          ℝ hzj

/-- The `i`th angle-coordinate vector field `∂ / ∂θⁱ` on the `n`-torus. -/
def torus_angle_coordinate_vector_field (i : Fin n) : SmoothTorusVectorField :=
  ContMDiffSection.mk (torusAngleCoordinateVectorFieldRaw n i)
    (torusAngleCoordinateVectorField_contMDiff n i)

/-- Helper for Example 8.5: along the standard covering, the raw torus angle field is the
coordinatewise insertion of the circle angle field. -/
private theorem torusAngleCoordinateVectorFieldRaw_apply_standardTorusCovering
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    (torusAngleCoordinateVectorFieldRaw n i (standardTorusCovering n x)) j =
      if j = i then circle_angle_vector_field (Circle.exp (x i)) else 0 := by
  -- Reuse the raw-field support lemma and then unfold the covering coordinate.
  simpa [standardTorusCovering] using
    torusAngleCoordinateVectorFieldRaw_apply (n := n) (i := i) (j := j)
      (z := standardTorusCovering n x)

/-- Helper for Example 8.5: the derivative of the standard torus covering is coordinatewise the
derivative of `Circle.exp`. -/
private theorem standardTorusCovering_mfderiv_component
    (x : EuclideanSpace ℝ (Fin n)) (v : TangentSpace (𝓡 n) x) (j : Fin n) :
    (mfderiv (𝓡 n) TnModel (standardTorusCovering n) x v) j =
      mfderiv (𝓘(ℝ)) (𝓡 1) Circle.exp (x j)
        (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x) v) j) := by
  have hcover :
      MDifferentiableAt (𝓡 n) TnModel (standardTorusCovering n) x :=
    (standard_torus_covering_isSmoothCoveringMap n).isLocalDiffeomorph.contMDiff.mdifferentiableAt
      (by simp)
  have hprojHas :
      HasMFDerivAt TnModel (𝓡 1) (fun z : 𝕋^{n} ↦ z j) (standardTorusCovering n x)
        (ContinuousLinearMap.proj j) :=
    hasMFDerivAt_piProjection (I := fun _ : Fin n ↦ 𝓡 1)
      (p := standardTorusCovering n x) (j := j)
  have hproj :
      MDifferentiableAt TnModel (𝓡 1) (fun z : 𝕋^{n} ↦ z j) (standardTorusCovering n x) :=
    hprojHas.mdifferentiableAt
  have hevalContMDiff :
      ContMDiffAt (𝓡 n) (𝓘(ℝ)) ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) x := by
    simpa using
      (((PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contMDiffAt :
        ContMDiffAt (𝓡 n) (𝓘(ℝ)) ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) x)
  have heval :
      MDifferentiableAt (𝓡 n) (𝓘(ℝ)) (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) x := by
    exact hevalContMDiff.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hexp : MDifferentiableAt (𝓘(ℝ)) (𝓡 1) Circle.exp (x j) := by
    exact contMDiff_circleExp.contMDiffAt.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hcomponentComp :
      mfderiv TnModel (𝓡 1) (fun z : 𝕋^{n} ↦ z j) (standardTorusCovering n x)
          (mfderiv (𝓡 n) TnModel (standardTorusCovering n) x v) =
        mfderiv (𝓡 n) (𝓡 1) ((fun z : 𝕋^{n} ↦ z j) ∘ standardTorusCovering n) x v := by
    simpa using
      (mfderiv_comp_apply_of_eq (x := x) (y := standardTorusCovering n x)
        (I := 𝓡 n) (I' := TnModel) (I'' := 𝓡 1)
        (g := fun z : 𝕋^{n} ↦ z j) (f := standardTorusCovering n) hproj hcover rfl v).symm
  -- Read the `j`th torus component by postcomposing with the projection `z ↦ z j`.
  have hstart :
      (mfderiv (𝓡 n) TnModel (standardTorusCovering n) x v) j =
        mfderiv TnModel (𝓡 1) (fun z : 𝕋^{n} ↦ z j) (standardTorusCovering n x)
          (mfderiv (𝓡 n) TnModel (standardTorusCovering n) x v) := by
    rw [mfderiv_piProjection (I := fun _ : Fin n ↦ 𝓡 1) (p := standardTorusCovering n x) (j := j)]
    rfl
  have hcompExp :
      mfderiv (𝓡 n) (𝓡 1) ((fun z : 𝕋^{n} ↦ z j) ∘ standardTorusCovering n) x v =
        mfderiv (𝓡 n) (𝓡 1) (fun y : EuclideanSpace ℝ (Fin n) ↦ Circle.exp (y j)) x v := by
    rfl
  have hcircleComp :
      mfderiv (𝓡 n) (𝓡 1) (fun y : EuclideanSpace ℝ (Fin n) ↦ Circle.exp (y j)) x v =
        mfderiv (𝓘(ℝ)) (𝓡 1) Circle.exp (x j)
          (mfderiv (𝓡 n) (𝓘(ℝ)) (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) x v) := by
    exact mfderiv_comp_apply_of_eq (x := x) (y := x j)
      (I := 𝓡 n) (I' := 𝓘(ℝ)) (I'' := 𝓡 1)
      (g := Circle.exp) (f := fun y : EuclideanSpace ℝ (Fin n) ↦ y j) hexp heval rfl v
  have hevalDeriv :
      mfderiv (𝓘(ℝ)) (𝓡 1) Circle.exp (x j)
          (mfderiv (𝓡 n) (𝓘(ℝ)) (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) x v) =
        mfderiv (𝓘(ℝ)) (𝓡 1) Circle.exp (x j)
          (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x) v) j) := by
    have hfderivEval :
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) x =
          (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
      simpa using
        (((PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt.fderiv :
          fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y j) x =
            (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    rw [mfderiv_eq_fderiv]
    rw [hfderivEval]
    rfl
  exact hstart.trans <| hcomponentComp.trans <| hcompExp.trans <| hcircleComp.trans hevalDeriv

/-- Pulling back the torus angle-coordinate vector field `∂ / ∂θⁱ` along the standard covering
recovers the `i`th standard coordinate basis vector on `ℝⁿ`. -/
@[simp] theorem torus_angle_coordinate_vector_field_apply_standardTorusCovering
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    torus_angle_coordinate_vector_field n i (standardTorusCovering n x) =
      mfderiv (𝓡 n) TnModel (standardTorusCovering n) x
        ((NormedSpace.fromTangentSpace x).symm
          ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
  apply funext
  intro j
  -- Compare both tangent vectors on the `j`th torus coordinate.
  change (torusAngleCoordinateVectorFieldRaw n i (standardTorusCovering n x)) j =
    (mfderiv (𝓡 n) TnModel (standardTorusCovering n) x
      ((NormedSpace.fromTangentSpace x).symm ((EuclideanSpace.basisFun (Fin n) ℝ) i))) j
  rw [torusAngleCoordinateVectorFieldRaw_apply_standardTorusCovering]
  rw [standardTorusCovering_mfderiv_component (n := n)
    (x := x)
    (v := (NormedSpace.fromTangentSpace x).symm ((EuclideanSpace.basisFun (Fin n) ℝ) i))
    (j := j)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  by_cases hji : j = i
  · -- On the active coordinate, the torus field pulls back to the circle angle vector field.
    subst j
    rw [if_pos rfl]
    have hbasis :
        ((EuclideanSpace.basisFun (Fin n) ℝ) i) i = 1 := by
      rw [EuclideanSpace.basisFun_apply]
      simp
    rw [hbasis]
    have honeTangent :
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) (x i)).symm 1 :
          TangentSpace (𝓘(ℝ)) (x i)) = 1 := rfl
    simpa only [honeTangent] using circle_angle_vector_field_apply_exp (x i)
  · -- Off the active coordinate, both sides vanish.
    rw [if_neg hji]
    have hzero :
        ((EuclideanSpace.basisFun (Fin n) ℝ) i) j = 0 := by
      rw [EuclideanSpace.basisFun_apply]
      simp [hji]
    rw [hzero]
    exact ((mfderiv (𝓘(ℝ)) (𝓡 1) Circle.exp (x j)).map_zero).symm

/-- Example 8.5: for the `n`-torus `𝕋ⁿ`, the angle-coordinate vector fields
`∂ / ∂θ¹, ..., ∂ / ∂θⁿ` determined by local angle coordinates are globally defined and smooth.
Concretely, there is a global family of bundled smooth vector fields whose pullback along the
standard covering `standardTorusCovering n : ℝⁿ → 𝕋ⁿ` is the standard coordinate basis on `ℝⁿ`. -/
theorem exists_smooth_torus_angle_coordinate_vector_fields :
    ∃ X : Fin n → SmoothTorusVectorField,
      ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)),
        X i (standardTorusCovering n x) =
          mfderiv (𝓡 n) TnModel (standardTorusCovering n) x
            ((NormedSpace.fromTangentSpace x).symm
              ((EuclideanSpace.basisFun (Fin n) ℝ) i)) := by
  exact ⟨torus_angle_coordinate_vector_field n,
    torus_angle_coordinate_vector_field_apply_standardTorusCovering n⟩

end
