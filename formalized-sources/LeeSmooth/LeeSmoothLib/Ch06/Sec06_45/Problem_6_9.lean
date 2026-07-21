import Mathlib
import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch05.Sec05_29.Example_5_9
import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch05.Sec05_30.Corollary_5_14
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_7
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_1
import LeeSmoothLib.Ch06.Sec06_44.Theorem_6_30
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

open Manifold Set

noncomputable section

section

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "unitSphere2" => Metric.sphere (0 : R3) 1
local notation "sphereR" => Metric.sphere (0 : R3)

/-- Helper for Problem 6-9: nonzero radial scaling of `ℝ^3` is a diffeomorphism. -/
private noncomputable def radialScalingDiffeomorph (r : ℝ) (hr : r ≠ 0) :
    R3 ≃ₘ^((⊤ : WithTop ℕ∞))⟮𝓡 3, 𝓡 3⟯ R3 where
  toEquiv :=
    { toFun := fun x ↦ r • x
      invFun := fun x ↦ r⁻¹ • x
      left_inv := by
        intro x
        simp [smul_smul, hr]
      right_inv := by
        intro x
        simp [smul_smul, hr] }
  contMDiff_toFun := by
    simpa using ((r • ContinuousLinearMap.id ℝ R3) : R3 →L[ℝ] R3).contMDiff
  contMDiff_invFun := by
    simpa using ((r⁻¹ • ContinuousLinearMap.id ℝ R3) : R3 →L[ℝ] R3).contMDiff

/-- Helper for Problem 6-9: transport an `n`-manifold charted-space structure across a
homeomorphism. -/
noncomputable abbrev transportedHomeomorphChartedSpace
    {n : ℕ}
    {R : Type*} [TopologicalSpace R] [ChartedSpace (EuclideanSpace ℝ (Fin n)) R]
    {N : Type*} [TopologicalSpace N] (e : R ≃ₜ N) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) N := by
  let _ : ChartedSpace R N :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- The singleton-chart transport keeps the atlas definitionally visible.
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) R N

/-- Helper for Problem 6-9: a homeomorphic target inherits the transported smooth `n`-manifold
structure from the source. -/
lemma transportedHomeomorphIsManifoldTop
    {n : ℕ}
    {R : Type*} [TopologicalSpace R] [ChartedSpace (EuclideanSpace ℝ (Fin n)) R]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) R]
    {N : Type*} [TopologicalSpace N] (e : R ≃ₜ N) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
      transportedHomeomorphChartedSpace (n := n) e
    IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N := by
  let eN : OpenPartialHomeomorph N R := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace R N := eN.singletonChartedSpace (by
    ext x
    simp [eN])
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
    transportedHomeomorphChartedSpace (n := n) e
  have hGroupoid :
      HasGroupoid N (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eN := by
      simpa [eN] using eN.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eN]) f hf
    have hf'Eq : f' = eN := by
      simpa [eN] using eN.singletonChartedSpace_mem_atlas_eq (h := by
        ext x
        simp [eN]) f' hf'
    subst f
    subst f'
    have hmid : eN.symm.trans eN = OpenPartialHomeomorph.refl R := by
      simpa [eN] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- The transported transitions reduce to the original source transitions.
    have hcompat :
        ((c.symm ≫ₕ (eN.symm ≫ₕ eN)) ≫ₕ c') ∈
          contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible hc hc'
    simpa [eN, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  exact IsManifold.mk' (𝓡 n) (⊤ : WithTop ℕ∞) N

/-- Helper for Problem 6-9: a smooth embedding remains a smooth embedding after transporting the
source manifold structure across a homeomorphism. -/
lemma transportedHomeomorph_isSmoothEmbedding_explicit
    {n k : ℕ}
    {R : Type*} [TopologicalSpace R] [ChartedSpace (EuclideanSpace ℝ (Fin n)) R]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) R]
    {N : Type*} [TopologicalSpace N]
    {f : N → EuclideanSpace ℝ (Fin k)} {g : R → EuclideanSpace ℝ (Fin k)}
    (hg : IsSmoothEmbedding (𝓡 n) (𝓡 k) (⊤ : WithTop ℕ∞) g)
    (e : R ≃ₜ N) (he : ∀ x, f (e x) = g x) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
      transportedHomeomorphChartedSpace (n := n) e
    let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N :=
      transportedHomeomorphIsManifoldTop (n := n) e
    IsSmoothEmbedding (𝓡 n) (𝓡 k) (⊤ : WithTop ℕ∞) f := by
  let instCharted : ChartedSpace (EuclideanSpace ℝ (Fin n)) N :=
    transportedHomeomorphChartedSpace (n := n) e
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N := instCharted
  let instManifold : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N :=
    transportedHomeomorphIsManifoldTop (n := n) e
  let _ : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) N := instManifold
  have hImmersion :
      IsImmersion (𝓡 n) (𝓡 k) (⊤ : WithTop ℕ∞) f := by
    let hImm := hg.isImmersion
    let hComp := hImm.complement
    let hCompImm := hImm.isImmersionOfComplement_complement
    let eN : OpenPartialHomeomorph N R := e.symm.toOpenPartialHomeomorph
    let _ : ChartedSpace R N := eN.singletonChartedSpace (by
      ext z
      simp [eN])
    refine ⟨hComp, inferInstance, inferInstance, ?_⟩
    intro x
    let hx := hCompImm (e.symm x)
    -- Transport the source chart of `g` across the homeomorphism onto `N`.
    refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      hx.equiv (eN.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [eN, OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
    · have hxe : f x = g (e.symm x) := by
        simpa using he (e.symm x)
      simpa [hxe] using hx.mem_codChart_source
    · intro d hd
      rcases hd with ⟨f', hf', c', hc', rfl⟩
      have hfEq : f' = eN := by
        simpa [eN] using eN.singletonChartedSpace_mem_atlas_eq (h := by
          ext z
          simp [eN]) f' hf'
      subst f'
      have hmid : eN.symm.trans eN = OpenPartialHomeomorph.refl R := by
        simpa [eN] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
      constructor
      · have hleft :
            ((hx.domChart.symm ≫ₕ (eN.symm ≫ₕ eN)) ≫ₕ c') ∈
              contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').1
        simpa [eN, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hleft
      · have hright :
            ((c'.symm ≫ₕ (eN.symm ≫ₕ eN)) ≫ₕ hx.domChart) ∈
              contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) := by
          rw [hmid, OpenPartialHomeomorph.trans_refl]
          exact (hx.domChart_mem_maximalAtlas c' hc').2
        simpa [eN, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc] using hright
    · exact hx.codChart_mem_maximalAtlas
    · intro z hz
      have hz' : e.symm z ∈ hx.domChart.source := by
        simpa [eN, OpenPartialHomeomorph.trans_source] using hz
      have hze : f z = g (e.symm z) := by
        simpa using he (e.symm z)
      simpa [hze] using hx.source_subset_preimage_source hz'
    · intro u hu
      have hu' : u ∈ (hx.domChart.extend (𝓡 n)).target := by
        simpa [eN, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
      have hpoint : f (e (hx.domChart.symm u)) = g (hx.domChart.symm u) :=
        he (hx.domChart.symm u)
      simpa [eN, Function.comp, OpenPartialHomeomorph.extend_coe_symm,
        OpenPartialHomeomorph.extend_coe, hpoint] using hx.writtenInCharts hu'
  have hEmbedding : Topology.IsEmbedding f := by
    have hEq : f = g ∘ e.symm := by
      funext x
      simpa using he (e.symm x)
    rw [hEq]
    exact hg.isEmbedding.comp e.symm.isEmbedding
  exact ⟨hImmersion, hEmbedding⟩

/-- Helper for Problem 6-9: on a Euclidean model space, a top-regularity local diffeomorphism is
a pointwise immersion with trivial complement. -/
lemma modelLocalDiffeomorphAt_isImmersionAtOfComplementPUnit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x : E}
    (hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : WithTop ℕ∞) f x) :
    IsImmersionAtOfComplement PUnit.{1} 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : WithTop ℕ∞) f x := by
  have hCont : ContinuousAt f x := (IsLocalDiffeomorphAt.contMDiffAt hf).continuousAt
  rcases hf with ⟨Φ, hx, hEq⟩
  let domChart : OpenPartialHomeomorph E E := Φ.toOpenPartialHomeomorph
  have hdom_groupoid :
      domChart ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, E) := by
    simpa [domChart] using
      Manifold.IsImmersionAtOfComplement.ex416_model_partial_diffeomorph_mem_contDiffGroupoid
        (K := 𝓘(ℝ, E)) (Φ := Φ)
  have hdom_mem :
      domChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) (⊤ : WithTop ℕ∞) E := by
    exact StructureGroupoid.mem_maximalAtlas_of_mem_groupoid
      (G := contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, E)) hdom_groupoid
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    hCont
    (.prodUnique ℝ E PUnit.{1})
    domChart
    (OpenPartialHomeomorph.refl E)
    hx
    (by simp)
    hdom_mem
    (by
      simpa using
        (contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℝ, E)).id_mem_maximalAtlas)
    ?_
  intro u hu
  have hu_target : u ∈ domChart.target := by
    simpa [OpenPartialHomeomorph.extend_target] using hu
  have hu_source : domChart.symm u ∈ domChart.source := by
    simpa using domChart.map_target hu_target
  have hfu : f (domChart.symm u) = domChart (domChart.symm u) := hEq hu_source
  have hright : domChart (domChart.symm u) = u := domChart.right_inv hu_target
  -- In the chosen local-diffeomorphism chart, the map is literally the identity.
  simpa [domChart, Function.comp, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm] using hfu.trans hright

/- Radial scaling identifies the unit sphere in `ℝ^3` with the sphere of radius `r > 0`. -/
private noncomputable def positiveSphere_homeomorph (r : ℝ) (hr : 0 < r) :
    unitSphere2 ≃ₜ sphereR r where
  toFun x := ⟨r • (x : R3), by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp [mem_sphere_zero_iff_norm.1 x.2]⟩
  invFun x := ⟨r⁻¹ • (x : R3), by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    simp [hr.ne', mem_sphere_zero_iff_norm.1 x.2]⟩
  left_inv x := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  right_inv x := by
    apply Subtype.ext
    simp [smul_smul, hr.ne']
  continuous_toFun :=
    Continuous.subtype_mk (continuous_const.smul continuous_subtype_val) fun x ↦ by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      simp [mem_sphere_zero_iff_norm.1 x.2]
  continuous_invFun :=
    Continuous.subtype_mk (continuous_const.smul continuous_subtype_val) fun x ↦ by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      simp [hr.ne', mem_sphere_zero_iff_norm.1 x.2]

/- The canonical smooth structure on a positive-radius sphere is the transport of the standard
unit-sphere structure along radial scaling. -/
@[reducible]
private noncomputable def positiveSphere_chartedSpace (r : ℝ) (hr : 0 < r) :
    ChartedSpace R2 (sphereR r) :=
  transportedHomeomorphChartedSpace (n := 2) (positiveSphere_homeomorph r hr)

/-- The positive-radius sphere in `ℝ^3` carries the transported smooth `2`-manifold structure. -/
theorem positiveSphere_isManifold (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    IsManifold (𝓡 2) ∞ (sphereR r) := by
  -- Route correction: define the sphere owner directly in the transported spelling.
  let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
  have hTop : IsManifold (𝓡 2) (⊤ : WithTop ℕ∞) (sphereR r) := by
    simpa [positiveSphere_chartedSpace] using
      transportedHomeomorphIsManifoldTop (n := 2) (positiveSphere_homeomorph r hr)
  let _ : IsManifold (𝓡 2) (⊤ : WithTop ℕ∞) (sphereR r) := hTop
  exact IsManifold.of_le (I := 𝓡 2) (M := sphereR r) (m := ∞) (n := (⊤ : WithTop ℕ∞))
    (by simp)

/-- Helper for Problem 6-9: radial scaling by a positive scalar carries the standard unit-sphere
inclusion to a smooth embedding into `ℝ^3`. -/
lemma radialScaling_isSmoothEmbeddingTop (r : ℝ) (hr : 0 < r) :
    IsSmoothEmbedding (𝓡 3) (𝓡 3) (⊤ : WithTop ℕ∞) (fun x : R3 ↦ r • x) := by
  -- A global diffeomorphism is a local diffeomorphism, hence an immersion and a topological
  -- embedding.
  have hLocal :
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) (⊤ : WithTop ℕ∞) (fun x : R3 ↦ r • x) := by
    simpa [radialScalingDiffeomorph] using
      (radialScalingDiffeomorph r hr.ne').isLocalDiffeomorph
  have hImm :
      IsImmersion (𝓡 3) (𝓡 3) (⊤ : WithTop ℕ∞) (fun x : R3 ↦ r • x) := by
    refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
    intro x
    exact modelLocalDiffeomorphAt_isImmersionAtOfComplementPUnit (hLocal x)
  exact ⟨hImm, (radialScalingDiffeomorph r hr.ne').toHomeomorph.isEmbedding⟩

/-- Helper for Problem 6-9: radial scaling by a positive scalar carries the standard unit-sphere
inclusion to a smooth embedding into `ℝ^3`. -/
lemma positiveSphere_scaledInclusion_isSmoothEmbedding (r : ℝ) (hr : 0 < r) :
    IsSmoothEmbedding (𝓡 2) (𝓡 3) (⊤ : WithTop ℕ∞) (fun x : unitSphere2 ↦ r • (x : R3)) := by
  -- Compose the canonical unit-sphere inclusion with the ambient radial scaling embedding.
  simpa [Function.comp] using
    Manifold.IsSmoothEmbedding.comp
      (radialScaling_isSmoothEmbeddingTop r hr)
      (unitSphere_subtype_val_isSmoothEmbedding 2)

/-- The positive-radius sphere in `ℝ^3` is an embedded submanifold with its canonical transported
smooth structure. -/
theorem positiveSphere_isEmbeddedSubmanifold (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
    IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r) := by
  let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
  let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
  have hTop : IsManifold (𝓡 2) (⊤ : WithTop ℕ∞) (sphereR r) := by
    -- The transported charted-space spelling already carries the top-order sphere manifold owner.
    simpa [positiveSphere_chartedSpace] using
      transportedHomeomorphIsManifoldTop (n := 2) (positiveSphere_homeomorph r hr)
  let _ : IsManifold (𝓡 2) (⊤ : WithTop ℕ∞) (sphereR r) := hTop
  have hSubtype :
      IsSmoothEmbedding (𝓡 2) (𝓡 3) (⊤ : WithTop ℕ∞) ((↑) : sphereR r → R3) := by
    -- Transport the scaled unit-sphere inclusion across the radial homeomorphism.
    simpa using
      (transportedHomeomorph_isSmoothEmbedding_explicit
        (n := 2) (k := 3)
        (g := fun x : unitSphere2 ↦ r • (x : R3))
        (f := ((↑) : sphereR r → R3))
        (positiveSphere_scaledInclusion_isSmoothEmbedding r hr)
        (positiveSphere_homeomorph r hr)
        (by
          intro x
          rfl))
  exact
    { toBoundarylessManifold := inferInstance
      isSmoothEmbedding_subtype_val := hSubtype }

/-- Helper for Problem 6-9: the canonical linear identification `ℝ ≃ ℝ¹`. -/
def realToR1Equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Problem 6-9: for a surjective linear map `B`, surjectivity of `B ∘ A` is
equivalent to `A.range ⊔ B.ker = ⊤`. -/
theorem surjective_comp_iff_range_sup_ker_eq_top
    {V W Z : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : V →L[ℝ] W} {B : W →L[ℝ] Z} (hB : Function.Surjective B) :
    Function.Surjective (B.comp A) ↔ A.range ⊔ B.ker = ⊤ := by
  have hdom :
      Function.Surjective (B.toLinearMap.domRestrict A.range) ↔
        A.range ⊔ B.ker = ⊤ := by
    simpa using
      (LinearMap.surjective_domRestrict_iff
        (f := B.toLinearMap) (S := A.range) hB)
  constructor
  · intro hComp
    exact hdom.mp <| by
      intro z
      rcases hComp z with ⟨x, rfl⟩
      exact ⟨⟨A x, ⟨x, rfl⟩⟩, rfl⟩
  · intro hSup
    have hDomSurj : Function.Surjective (B.toLinearMap.domRestrict A.range) := hdom.mpr hSup
    intro z
    rcases hDomSurj z with ⟨y, hy⟩
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change B (A x) = z
    exact hx ▸ hy

/-- The map `F : ℝ^2 → ℝ^3` from Problem 6-9, written in Euclidean coordinates. -/
def problem_6_9_map (p : R2) : R3 :=
  WithLp.toLp 2
    ![Real.exp (p 1) * Real.cos (p 0), Real.exp (p 1) * Real.sin (p 0), Real.exp (-p 1)]

/-- Helper for Problem 6-9: the ambient squared-radius function on `ℝ^3`. -/
def ambientRadiusSq (x : R3) : ℝ :=
  ‖x‖ ^ (2 : ℕ)

/-- Helper for Problem 6-9: the map `problem_6_9_map` is smooth on all of `ℝ²`. -/
theorem problem_6_9_map_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞ problem_6_9_map := by
  rw [contMDiff_iff_contDiff]
  have hExplicit :
      ContDiff ℝ ∞
        (fun p : R2 ↦
          WithLp.toLp 2
            ![Real.exp (p 1) * Real.cos (p 0),
              Real.exp (p 1) * Real.sin (p 0),
              Real.exp (-p 1)]) := by
    refine (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 ↦ ℝ)).comp ?_
    rw [contDiff_pi]
    intro i
    fin_cases i
    · simpa using
        (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1)).exp.mul
          ((contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 0)).cos)
    · simpa using
        (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1)).exp.mul
          ((contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 0)).sin)
    · simpa using
        ((contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1)).neg).exp
  simpa [problem_6_9_map] using hExplicit

/-- The squared radius of the image point `F (x, y)`, simplified to the explicit formula that
depends only on the second coordinate. -/
def problem_6_9_radius_sq (p : R2) : ℝ :=
  Real.exp (2 * p 1) + Real.exp (-2 * p 1)

/-- Helper for Problem 6-9: the ambient squared-radius function is smooth on `ℝ³`. -/
theorem ambientRadiusSq_contMDiff :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ambientRadiusSq := by
  rw [contMDiff_iff_contDiff]
  simpa [ambientRadiusSq] using
    (contDiff_norm_sq ℝ : ContDiff ℝ ∞ fun x : R3 ↦ ‖x‖ ^ 2)

/-- Helper for Problem 6-9: away from the origin, the derivative of the ambient squared-radius
function is surjective. -/
theorem ambientRadiusSq_mfderiv_surjective_of_ne_zero {x : R3} (hx : x ≠ 0) :
    Function.Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ambientRadiusSq x) := by
  rw [mfderiv_eq_fderiv]
  change Function.Surjective (fderiv ℝ (fun x : R3 ↦ ‖x‖ ^ (2 : ℕ)) x)
  rw [fderiv_norm_sq_apply]
  have hnorm : ‖x‖ ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  intro y
  refine ⟨(y / (2 * ‖x‖ ^ (2 : ℕ))) • x, ?_⟩
  simp [innerSL, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm]

/-- Helper for Problem 6-9: on `ℝ^3 \\ {0}`, the function `x ↦ ‖x‖²` locally defines the
positive-radius sphere `sphereR r`. -/
theorem ambientRadiusSq_isLocalDefiningMapOnSphere (r : ℝ) (hr : 0 < r) :
    IsLocalDefiningMapOn (𝓡 3) 𝓘(ℝ, ℝ) (sphereR r) {x : R3 | x ≠ 0} ambientRadiusSq := by
  refine
    { isOpen_source := ?_
      smoothOn := ambientRadiusSq_contMDiff.contMDiffOn
      mem_iff_eq := ?_
      surjective_mfderiv := ?_ }
  · have hEq : {x : R3 | x ≠ 0} = ({0} : Set R3)ᶜ := by
      ext x
      simp
    rw [hEq]
    exact isOpen_compl_iff.mpr isClosed_singleton
  · intro p q hp _ _
    constructor
    · intro hq
      rw [mem_sphere_zero_iff_norm] at hp hq
      simpa [ambientRadiusSq, hp, hq]
    · intro hpq
      rw [mem_sphere_zero_iff_norm] at hp ⊢
      have hsq : ‖q‖ ^ (2 : ℕ) = r ^ (2 : ℕ) := by
        simpa [ambientRadiusSq, hp] using hpq
      exact (sq_eq_sq₀ (norm_nonneg q) hr.le).1 (by simpa [pow_two] using hsq)
  · intro x hx
    exact ambientRadiusSq_mfderiv_surjective_of_ne_zero hx

/-- Helper for Problem 6-9: the positive-radius sphere inclusion remains a `C^∞` smooth
embedding after lowering the stored top regularity. -/
theorem positiveSphere_subtypeVal_isSmoothEmbeddingInf (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
    IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ ((↑) : sphereR r → R3) := by
  let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
  let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
  exact
    isSmoothEmbedding_of_le (I := 𝓡 3) (I' := 𝓡 2) (M := R3) (N := sphereR r)
      (m := ∞) (n := ω) (by simp)
      (positiveSphere_isEmbeddedSubmanifold r hr).isSmoothEmbedding_subtype_val

/-- Helper for Problem 6-9: the radius-squared function differs from `2` by a square, so its
minimum value is attained exactly on the line `y = 0`. -/
theorem problem_6_9_radius_sq_sub_two_eq_square (p : R2) :
    problem_6_9_radius_sq p - 2 =
      (Real.exp (p 1) - Real.exp (-p 1)) ^ (2 : ℕ) := by
  -- Rewrite the two exponential terms as squares and expand the resulting identity.
  rw [problem_6_9_radius_sq]
  have hpos : Real.exp (2 * p 1) = (Real.exp (p 1)) ^ (2 : ℕ) := by
    rw [show 2 * p 1 = p 1 + p 1 by ring, Real.exp_add]
    ring
  have hneg : Real.exp (-2 * p 1) = (Real.exp (-p 1)) ^ (2 : ℕ) := by
    rw [show -2 * p 1 = (-p 1) + (-p 1) by ring, Real.exp_add]
    ring
  rw [hpos, hneg]
  have hmul : Real.exp (p 1) * Real.exp (-p 1) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith

/-- Helper for Problem 6-9: the exceptional level `2` is exactly the zero fiber of the second
coordinate. -/
theorem problem_6_9_radiusSq_eq_two_iff (p : R2) :
    problem_6_9_radius_sq p = 2 ↔ p 1 = 0 := by
  constructor
  · intro hp
    have hsquare :
        (Real.exp (p 1) - Real.exp (-p 1)) ^ (2 : ℕ) = 0 := by
      rw [← problem_6_9_radius_sq_sub_two_eq_square, hp]
      ring
    have hexp : Real.exp (p 1) = Real.exp (-p 1) := by
      nlinarith
    have hcoord : p 1 = -p 1 := Real.exp_injective hexp
    linarith
  · intro hp
    rw [problem_6_9_radius_sq, hp]
    norm_num

/-- Helper for Problem 6-9: the radius-squared profile is bounded below by `2`. -/
theorem problem_6_9_radius_sq_two_le (p : R2) : 2 ≤ problem_6_9_radius_sq p := by
  -- Rewrite the difference from `2` as a square and use nonnegativity.
  have hsquare : 0 ≤ (Real.exp (p 1) - Real.exp (-p 1)) ^ (2 : ℕ) := by
    positivity
  nlinarith [problem_6_9_radius_sq_sub_two_eq_square p]

/-- Helper for Problem 6-9: the scalar profile `y ↦ e^(2y) + e^(-2y)` has derivative
`2e^(2y) - 2e^(-2y)`. -/
theorem problem_6_9_radiusSqScalar_hasDerivAt (y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (2 * y) + Real.exp (-2 * y))
      (2 * Real.exp (2 * y) - 2 * Real.exp (-2 * y)) y := by
  -- Differentiate the positive and negative exponential terms separately.
  have hpos_raw : HasDerivAt (fun y : ℝ => Real.exp (y * 2))
      (Real.exp (y * 2) * 2) y := by
    simpa using
      (Real.hasDerivAt_exp (y * 2)).comp y (hasDerivAt_mul_const (2 : ℝ))
  have hpos : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * y)) y := by
    simpa [mul_comm, two_mul, mul_left_comm, mul_assoc] using hpos_raw
  have hneg_raw : HasDerivAt (fun y : ℝ => Real.exp (y * (-2)))
      (Real.exp (y * (-2)) * (-2)) y := by
    simpa using
      (Real.hasDerivAt_exp (y * (-2))).comp y (hasDerivAt_mul_const (-2 : ℝ))
  have hneg : HasDerivAt (fun y : ℝ => Real.exp (-2 * y))
      (-2 * Real.exp (-2 * y)) y := by
    simpa [mul_comm, two_mul, neg_mul, mul_left_comm, mul_assoc] using hneg_raw
  -- The derivative of the sum is the sum of the derivatives.
  simpa using hpos.add hneg

/-- Helper for Problem 6-9: differentiating `problem_6_9_radius_sq` produces the expected scalar
multiple of the second-coordinate projection. -/
theorem problem_6_9_radius_sq_fderiv_apply (p v : R2) :
    fderiv ℝ problem_6_9_radius_sq p v =
      (2 * Real.exp (2 * p 1) - 2 * Real.exp (-2 * p 1)) * v 1 := by
  -- Differentiate the second-coordinate projection once and compose with the scalar profile.
  have hcoord :
      HasFDerivAt (fun q : R2 ↦ q 1)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1
  have hcomp := (problem_6_9_radiusSqScalar_hasDerivAt (p 1)).hasFDerivAt.comp p hcoord
  -- Evaluating the resulting linear functional gives the advertised formula.
  change fderiv ℝ ((fun y : ℝ => Real.exp (2 * y) + Real.exp (-2 * y)) ∘ fun q : R2 ↦ q 1) p v =
    (2 * Real.exp (2 * p 1) - 2 * Real.exp (-2 * p 1)) * v 1
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.smul_apply, PiLp.proj_apply]
  ring

/-- Helper for Problem 6-9: the derivative of `problem_6_9_radius_sq` is onto exactly away from
the critical line `y = 0`. -/
theorem problem_6_9_radiusSq_mfderiv_surjective_iff (p : R2) :
    Function.Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq p) ↔ p 1 ≠ 0 := by
  rw [mfderiv_eq_fderiv]
  change Function.Surjective (fderiv ℝ problem_6_9_radius_sq p : R2 →L[ℝ] ℝ) ↔ p 1 ≠ 0
  constructor
  · intro hsurj
    -- On the critical line `y = 0`, the derivative formula collapses to the zero map.
    intro hp1
    have hzero : fderiv ℝ problem_6_9_radius_sq p = 0 := by
      ext v
      rw [problem_6_9_radius_sq_fderiv_apply]
      simp [hp1]
    rw [hzero] at hsurj
    rcases hsurj 1 with ⟨v, hv⟩
    simpa using hv
  · intro hp1
    have hdiff : Real.exp (2 * p 1) - Real.exp (-2 * p 1) ≠ 0 := by
      intro hzero
      have hexp : Real.exp (2 * p 1) = Real.exp (-2 * p 1) := by
        linarith
      have hcoord : 2 * p 1 = -2 * p 1 := Real.exp_injective hexp
      have hp10 : p 1 = 0 := by
        linarith
      exact hp1 hp10
    let c : ℝ := 2 * (Real.exp (2 * p 1) - Real.exp (-2 * p 1))
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero two_ne_zero hdiff
    -- Away from the critical line, solve explicitly for a tangent vector with prescribed image.
    intro y
    refine ⟨WithLp.toLp 2 ![(0 : ℝ), y / c], ?_⟩
    rw [problem_6_9_radius_sq_fderiv_apply]
    change (2 * Real.exp (2 * p 1) - 2 * Real.exp (-2 * p 1)) * (y / c) = y
    have hcEq : 2 * Real.exp (2 * p 1) - 2 * Real.exp (-2 * p 1) = c := by
      dsimp [c]
      ring
    rw [hcEq]
    field_simp [hc]

/-- Helper for Problem 6-9: the scalar radius-squared function is smooth on all of `ℝ²`. -/
theorem problem_6_9_radius_sq_contMDiff :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ problem_6_9_radius_sq := by
  rw [contMDiff_iff_contDiff]
  -- The explicit formula is a sum of smooth exponentials of the second coordinate.
  change ContDiff ℝ ∞ (fun p : R2 ↦ Real.exp (2 * p 1) + Real.exp (-2 * p 1))
  fun_prop

/-- Helper for Problem 6-9: the regular-level-set codimension here is `1`. -/
theorem problem_6_9_levelset_model_eq_one :
    Module.finrank ℝ R2 - Module.finrank ℝ ℝ = 1 := by
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - Module.finrank ℝ ℝ = 1
  norm_num

/-- Helper for Problem 6-9: the squared norm of `problem_6_9_map p` is the explicit scalar
radius-squared function `problem_6_9_radius_sq p`. -/
theorem problem_6_9_map_norm_sq_eq_radius_sq (p : R2) :
    ‖problem_6_9_map p‖ ^ (2 : ℕ) = problem_6_9_radius_sq p := by
  -- Expand the Euclidean norm into the sum of the three coordinate squares of `F p`.
  have hpos : Real.exp (p 1) ^ (2 : ℕ) = Real.exp (2 * p 1) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-p 1) ^ (2 : ℕ) = Real.exp (-2 * p 1) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  -- The trigonometric terms combine to `cos² x + sin² x = 1`.
  calc
    ‖problem_6_9_map p‖ ^ (2 : ℕ)
        = ∑ i : Fin 3, (problem_6_9_map p i) ^ (2 : ℕ) := by
          simpa using EuclideanSpace.real_norm_sq_eq (problem_6_9_map p)
    _ = (Real.exp (p 1) * Real.cos (p 0)) ^ (2 : ℕ) +
            (Real.exp (p 1) * Real.sin (p 0)) ^ (2 : ℕ) +
            (Real.exp (-p 1)) ^ (2 : ℕ) := by
          simp [Fin.sum_univ_three, problem_6_9_map, PiLp.toLp_apply]
    _ = (Real.exp (p 1) * Real.cos (p 0)) ^ (2 : ℕ) +
            (Real.exp (p 1) * Real.sin (p 0)) ^ (2 : ℕ) +
            (Real.exp (-p 1)) ^ (2 : ℕ) := rfl
    _ = Real.exp (p 1) ^ (2 : ℕ) * ((Real.cos (p 0)) ^ (2 : ℕ) + (Real.sin (p 0)) ^ (2 : ℕ)) +
          Real.exp (-p 1) ^ (2 : ℕ) := by
          ring
    _ = Real.exp (p 1) ^ (2 : ℕ) + Real.exp (-p 1) ^ (2 : ℕ) := by
          rw [show (Real.cos (p 0)) ^ (2 : ℕ) + (Real.sin (p 0)) ^ (2 : ℕ) = 1 by
            simpa [pow_two, add_comm] using Real.sin_sq_add_cos_sq (p 0)]
          ring
    _ = problem_6_9_radius_sq p := by
          rw [hpos, hneg, problem_6_9_radius_sq]

/-- For a nonnegative radius, the sphere equation `F (x, y) ∈ S_r(0)` is equivalent to the
explicit scalar equation `e^(2y) + e^(-2y) = r^2`. -/
theorem problem_6_9_preimage_eq_radius_sq_level_set (r : ℝ) (hr : 0 ≤ r) :
    problem_6_9_map ⁻¹' sphereR r =
      problem_6_9_radius_sq ⁻¹' {r ^ (2 : ℕ)} := by
  ext p
  constructor
  · intro hp
    -- Square the norm equation defining the sphere and then rewrite the squared norm explicitly.
    have hnorm : ‖problem_6_9_map p‖ = r := mem_sphere_zero_iff_norm.1 hp
    have hsq : ‖problem_6_9_map p‖ ^ (2 : ℕ) = r ^ (2 : ℕ) := by
      rw [hnorm]
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    simpa [problem_6_9_map_norm_sq_eq_radius_sq] using hsq
  · intro hp
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
    rw [Set.mem_preimage, mem_sphere_zero_iff_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hr).1 (by
      simpa [problem_6_9_map_norm_sq_eq_radius_sq] using hp)

/-- Helper for Problem 6-9 (1): transversality to `sphereR r` implies that `r²` is a regular
value of `problem_6_9_radius_sq`. -/
theorem problem_6_9_regularValue_of_transverse
    {r : ℝ} (hr : 0 < r)
    [ChartedSpace R2 (sphereR r)]
    [IsManifold (𝓡 2) ∞ (sphereR r)]
    [IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r)]
    (hTrans : IsTransverseToSubmanifold (𝓡 3) (𝓡 2) (𝓡 2) (sphereR r) problem_6_9_map) :
    IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq (r ^ (2 : ℕ)) := by
  have hRadiusEq : ambientRadiusSq ∘ problem_6_9_map = problem_6_9_radius_sq := by
    funext p
    simpa [ambientRadiusSq, Function.comp] using problem_6_9_map_norm_sq_eq_radius_sq p
  intro p hp
  have hpSphere : problem_6_9_map p ∈ sphereR r := by
    rw [mem_sphere_zero_iff_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hr.le).1 (by
      simpa [Set.mem_preimage, Set.mem_singleton_iff, problem_6_9_map_norm_sq_eq_radius_sq] using hp)
  let q : problem_6_9_map ⁻¹' sphereR r := ⟨p, hpSphere⟩
  let x : sphereR r := ⟨problem_6_9_map p, hpSphere⟩
  have hxNe : problem_6_9_map p ≠ 0 := by
    intro hx0
    have hnorm : ‖problem_6_9_map p‖ = r := mem_sphere_zero_iff_norm.1 hpSphere
    have hrZero : r = 0 := by
      simpa [hx0] using hnorm.symm
    exact hr.ne' hrZero
  have hSphereSubtype :
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ ((↑) : sphereR r → R3) := by
    exact
      isSmoothEmbedding_of_le (I := 𝓡 3) (I' := 𝓡 2) (M := R3) (N := sphereR r)
        (m := ∞) (n := (⊤ : WithTop ℕ∞)) (by simp)
        (show IsSmoothEmbedding (𝓡 2) (𝓡 3) (⊤ : WithTop ℕ∞) ((↑) : sphereR r → R3) from
          IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val
            (I := 𝓡 3) (J := 𝓡 2) (S := sphereR r))
  have hTangent :
      T[𝓡 2; x] =
        (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ambientRadiusSq (problem_6_9_map p)).ker := by
    simpa [x] using
      tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn
        hSphereSubtype
        (ambientRadiusSq_isLocalDefiningMapOnSphere r hr) x hxNe
  let A := mfderiv (𝓡 2) (𝓡 3) problem_6_9_map p
  let B := mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ambientRadiusSq (problem_6_9_map p)
  have hTop :
      A.range ⊔ B.ker = ⊤ := by
    simpa [A, B, q, x, hTangent] using hTrans.tangent_sup_eq_top q
  have hAmbientSurj : Function.Surjective B := by
    simpa [B] using ambientRadiusSq_mfderiv_surjective_of_ne_zero hxNe
  have hSurjComp :
      Function.Surjective (B.comp A) ↔ A.range ⊔ B.ker = ⊤ :=
    surjective_comp_iff_range_sup_ker_eq_top
      (V := R2) (W := R3) (Z := ℝ) (A := A) (B := B) hAmbientSurj
  have hCompSurj :
      Function.Surjective (B.comp A) :=
    hSurjComp.2 hTop
  have hMapMDiff :
      MDifferentiableAt (𝓡 2) (𝓡 3) problem_6_9_map p :=
    problem_6_9_map_contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hAmbientMDiff :
      MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) ambientRadiusSq (problem_6_9_map p) :=
    ambientRadiusSq_contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmfderivEq :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq p =
        B.comp A := by
    rw [← hRadiusEq]
    simpa [A, B, Function.comp] using mfderiv_comp p hAmbientMDiff hMapMDiff
  rw [hmfderivEq]
  exact hCompSurj

/-- Helper for Problem 6-9 (1): if `r²` is a regular value of `problem_6_9_radius_sq`, then
`problem_6_9_map` is transverse to `sphereR r`. -/
theorem problem_6_9_transverse_of_regularValue
    {r : ℝ} (hr : 0 < r)
    [ChartedSpace R2 (sphereR r)]
    [IsManifold (𝓡 2) ∞ (sphereR r)]
    [IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r)]
    (hReg : IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq (r ^ (2 : ℕ))) :
    IsTransverseToSubmanifold (𝓡 3) (𝓡 2) (𝓡 2) (sphereR r) problem_6_9_map := by
  have hRadiusEq : ambientRadiusSq ∘ problem_6_9_map = problem_6_9_radius_sq := by
    funext p
    simpa [ambientRadiusSq, Function.comp] using problem_6_9_map_norm_sq_eq_radius_sq p
  refine (isTransverseToSubmanifold_iff problem_6_9_map).2 ?_
  refine ⟨problem_6_9_map_contMDiff, ?_⟩
  intro q
  let x : sphereR r := ⟨problem_6_9_map q, q.2⟩
  have hqLevel : problem_6_9_radius_sq q = r ^ (2 : ℕ) := by
    have hnorm : ‖problem_6_9_map q‖ = r := mem_sphere_zero_iff_norm.1 q.2
    calc
      problem_6_9_radius_sq q = ‖problem_6_9_map q‖ ^ (2 : ℕ) := by
        symm
        exact problem_6_9_map_norm_sq_eq_radius_sq q
      _ = r ^ (2 : ℕ) := by rw [hnorm]
  have hxNe : problem_6_9_map q ≠ 0 := by
    intro hx0
    have hnorm : ‖problem_6_9_map q‖ = r := mem_sphere_zero_iff_norm.1 q.2
    have hrZero : r = 0 := by
      simpa [hx0] using hnorm.symm
    exact hr.ne' hrZero
  have hSphereSubtype :
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ ((↑) : sphereR r → R3) := by
    exact
      isSmoothEmbedding_of_le (I := 𝓡 3) (I' := 𝓡 2) (M := R3) (N := sphereR r)
        (m := ∞) (n := (⊤ : WithTop ℕ∞)) (by simp)
        (show IsSmoothEmbedding (𝓡 2) (𝓡 3) (⊤ : WithTop ℕ∞) ((↑) : sphereR r → R3) from
          IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val
            (I := 𝓡 3) (J := 𝓡 2) (S := sphereR r))
  have hTangent :
      T[𝓡 2; x] =
        (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ambientRadiusSq (problem_6_9_map q)).ker := by
    simpa [x] using
      tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn
        hSphereSubtype
        (ambientRadiusSq_isLocalDefiningMapOnSphere r hr) x hxNe
  have hRadiusSurj :
      Function.Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq q) :=
    hReg q hqLevel
  have hMapMDiff :
      MDifferentiableAt (𝓡 2) (𝓡 3) problem_6_9_map q :=
    problem_6_9_map_contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hAmbientMDiff :
      MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) ambientRadiusSq (problem_6_9_map q) :=
    ambientRadiusSq_contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  let A := mfderiv (𝓡 2) (𝓡 3) problem_6_9_map q
  let B := mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ambientRadiusSq (problem_6_9_map q)
  have hmfderivEq :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq q =
        B.comp A := by
    rw [← hRadiusEq]
    simpa [A, B, Function.comp] using mfderiv_comp (q : R2) hAmbientMDiff hMapMDiff
  have hAmbientSurj : Function.Surjective B := by
    simpa [B] using ambientRadiusSq_mfderiv_surjective_of_ne_zero hxNe
  have hSurjComp :
      Function.Surjective (B.comp A) ↔ A.range ⊔ B.ker = ⊤ :=
    surjective_comp_iff_range_sup_ker_eq_top
      (V := R2) (W := R3) (Z := ℝ) (A := A) (B := B) hAmbientSurj
  have hTop :
      A.range ⊔ B.ker = ⊤ := by
    refine hSurjComp.1 ?_
    rwa [← hmfderivEq]
  simpa [A, B, x, hTangent] using hTop

/-- Helper for Problem 6-9 (1): after rewriting the sphere equation in terms of the scalar
function `e^(2y) + e^(-2y)`, transversality to `S_r(0)` becomes the regular-value condition for
`problem_6_9_radius_sq`. -/
theorem problem_6_9_transverse_to_sphere_iff_regularValue (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
    let _ : IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r) :=
      positiveSphere_isEmbeddedSubmanifold r hr
    IsTransverseToSubmanifold (𝓡 3) (𝓡 2) (𝓡 2) (sphereR r)
      problem_6_9_map ↔
      IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq (r ^ (2 : ℕ)) := by
  let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
  let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
  let _ : IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r) :=
    positiveSphere_isEmbeddedSubmanifold r hr
  constructor
  · intro h
    exact problem_6_9_regularValue_of_transverse (r := r) hr h
  · intro h
    exact problem_6_9_transverse_of_regularValue (r := r) hr h

/-- Helper for Problem 6-9 (1): the explicit scalar function
`problem_6_9_radius_sq (x, y) = e^(2y) + e^(-2y)` has `r^2` as a regular value exactly when
`r ≠ √2`. -/
theorem problem_6_9_radius_sq_isRegularValue_iff (r : ℝ) (hr : 0 < r) :
    IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq (r ^ (2 : ℕ)) ↔
      r ≠ Real.sqrt 2 := by
  constructor
  · intro hreg
    -- The exceptional value `r = √2` fails at the critical point `p = 0`.
    intro hrEq
    have hsurj : Function.Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq 0) := by
      have hlevel : problem_6_9_radius_sq (0 : R2) = r ^ (2 : ℕ) := by
        calc
          problem_6_9_radius_sq (0 : R2) = 2 := by
            norm_num [problem_6_9_radius_sq]
          _ = r ^ (2 : ℕ) := by
            subst r
            norm_num [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      exact hreg 0 hlevel
    exact ((problem_6_9_radiusSq_mfderiv_surjective_iff 0).1 hsurj) (by norm_num)
  · intro hrNe
    by_cases hlt : r < Real.sqrt 2
    · have hsq_lt : r ^ (2 : ℕ) < 2 := by
        have : r * r < Real.sqrt 2 * Real.sqrt 2 := by
          nlinarith [hr, hlt, Real.sqrt_nonneg 2]
        simpa [pow_two, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)] using this
      have hempty : problem_6_9_radius_sq ⁻¹' ({r ^ (2 : ℕ)} : Set ℝ) = ∅ := by
        ext p
        constructor
        · intro hp
          rw [Set.mem_empty_iff_false]
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
          have htwo : 2 ≤ problem_6_9_radius_sq p := problem_6_9_radius_sq_two_le p
          linarith
        · intro hp
          simp at hp
      -- An empty fiber is automatically a regular value.
      exact Manifold.isRegularValue_of_preimage_eq_empty (I := 𝓡 2) (J := 𝓘(ℝ, ℝ)) hempty
    · have hsqrt_le : Real.sqrt 2 ≤ r := le_of_not_gt hlt
      have hsqrt_lt : Real.sqrt 2 < r := lt_of_le_of_ne hsqrt_le (by simpa [eq_comm] using hrNe)
      rw [Manifold.isRegularValue_iff_forall_isRegularPoint]
      intro p hp
      rw [Manifold.isRegularPoint_iff_surjective_mfderiv]
      refine (problem_6_9_radiusSq_mfderiv_surjective_iff p).2 ?_
      intro hp1
      have hrTwo : r ^ (2 : ℕ) = 2 := by
        rw [← hp]
        exact (problem_6_9_radiusSq_eq_two_iff p).2 hp1
      have hrSq :
          r ^ (2 : ℕ) = (Real.sqrt 2) ^ (2 : ℕ) := by
        simpa [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)] using hrTwo
      have hrEq : r = Real.sqrt 2 := by
        exact (sq_eq_sq₀ hr.le (Real.sqrt_nonneg 2)).1 (by simpa [pow_two] using hrSq)
      exact hrNe hrEq

/-- Problem 6-9 (1): for every positive radius `r`, the map
`F(x, y) = (e^y cos x, e^y sin x, e^{-y})` is transverse to the sphere `S_r(0) ⊆ ℝ^3` exactly
when `r ≠ √2`. -/
theorem problem_6_9_transverse_to_sphere_iff (r : ℝ) (hr : 0 < r) :
    let _ : ChartedSpace R2 (sphereR r) := positiveSphere_chartedSpace r hr
    let _ : IsManifold (𝓡 2) ∞ (sphereR r) := positiveSphere_isManifold r hr
    let _ : IsEmbeddedSubmanifold (𝓡 3) (𝓡 2) (sphereR r) :=
      positiveSphere_isEmbeddedSubmanifold r hr
    IsTransverseToSubmanifold (𝓡 3) (𝓡 2) (𝓡 2) (sphereR r)
      problem_6_9_map ↔
      r ≠ Real.sqrt 2 := by
  -- Once the sphere-side bridge is in place, the explicit scalar regular-value classification
  -- finishes the transversality criterion immediately.
  exact
    (problem_6_9_transverse_to_sphere_iff_regularValue r hr).trans
      (problem_6_9_radius_sq_isRegularValue_iff r hr)

/-- Helper for Problem 6-9: conjugating an `ℝ¹` chart transition by `realToR1Equiv` preserves the
same differentiability order on the resulting `ℝ` chart transition. -/
theorem r1TransitionMemContDiffGroupoidReal
    {m : WithTop ℕ∞}
    {e :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))}
    (he : e ∈ contDiffGroupoid m (𝓡 1)) :
    let eModel :
        OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) ℝ :=
      realToR1Equiv.toHomeomorph.symm.toOpenPartialHomeomorph
    (eModel.symm.trans e).trans eModel ∈ contDiffGroupoid m 𝓘(ℝ) := by
  let eModel :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) ℝ :=
    realToR1Equiv.toHomeomorph.symm.toOpenPartialHomeomorph
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  have he_left :
      ContDiffOn ℝ m
        (e : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) e.source := by
    simpa using he.1
  have he_right :
      ContDiffOn ℝ m
        (e.symm : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) e.target := by
    simpa using he.2
  have heModel_contDiff :
      ContDiff ℝ m (eModel : EuclideanSpace ℝ (Fin 1) → ℝ) := by
    simpa [eModel] using realToR1Equiv.symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ m (eModel.symm : ℝ → EuclideanSpace ℝ (Fin 1)) := by
    simpa [eModel] using realToR1Equiv.toContinuousLinearMap.contDiff
  constructor
  · -- Conjugate the old `ℝ¹` transition by the fixed linear model change.
    have hmid :
        ContDiffOn ℝ m
          (fun x : ℝ ↦ e (eModel.symm x))
          (eModel.symm ⁻¹' e.source) := by
      refine he_left.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ m
          (fun x : ℝ ↦ eModel (e (eModel.symm x)))
          (eModel.symm ⁻¹' e.source) := by
      refine (heModel_contDiff.contDiffOn :
        ContDiffOn ℝ m eModel Set.univ).comp
        hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source] using hfinal
  · -- The same conjugation argument applies to the inverse transition.
    have hmid :
        ContDiffOn ℝ m
          (fun x : ℝ ↦ e.symm (eModel.symm x))
          (eModel.symm ⁻¹' e.target) := by
      refine he_right.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ m
          (fun x : ℝ ↦ eModel (e.symm (eModel.symm x)))
          (eModel.symm ⁻¹' e.target) := by
      refine (heModel_contDiff.contDiffOn :
        ContDiffOn ℝ m eModel Set.univ).comp
        hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [eModel, Function.comp, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using
      hfinal

/-- Helper for Problem 6-9: the codimension computation in the regular-level-set theorem yields a
concrete charted-space witness modeled on `ℝ¹`. -/
theorem problem_6_9_codimOneChartedSpaceNonempty {S : Set R2}
    (cs :
      ChartedSpace
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ)))
        S) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 1)) S) := by
  let n : ℕ := Module.finrank ℝ R2 - Module.finrank ℝ ℝ
  have hn : n = 1 := by
    simpa [n] using problem_6_9_levelset_model_eq_one
  change ChartedSpace (EuclideanSpace ℝ (Fin n)) S at cs
  rw [hn] at cs
  exact ⟨cs⟩

/-- Helper for Problem 6-9: the normalized codimension-one charted-space witness packages the
level set as a topological `1`-manifold. -/
theorem problem_6_9_codimOneTopologicalManifoldNonempty {S : Set R2}
    (cs :
      ChartedSpace
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ)))
        S) :
    Nonempty (TopologicalManifold 1 S) := by
  rcases problem_6_9_codimOneChartedSpaceNonempty cs with ⟨cs1⟩
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S := cs1
  exact ⟨topologicalManifoldOfChartedSpace 1 S⟩

/-- Helper for Problem 6-9: an embedded one-dimensional regular level set modeled on `ℝ¹` can be
transported to the standard curve model `𝓘(ℝ)`. -/
theorem problem_6_9_transportInput_of_codimOne {S : Set R2}
    (hS :
      ∃ cs : ChartedSpace
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))) S,
        ∃ hs :
            IsManifold
              (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
              ∞
              S,
          let _ : ChartedSpace
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))) S := cs
          let _ :
              IsManifold
                (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
                ∞
                S := hs
          IsEmbeddedSubmanifold
            (𝓡 2)
            (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
            S) :
    ∃ cs1 : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S,
      ∃ hs1 : IsManifold (𝓡 1) ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S := cs1
        let _ : IsManifold (𝓡 1) ∞ S := hs1
        IsEmbeddedSubmanifold (𝓡 2) (𝓡 1) S := by
  have normalizeCodimOneInput
      {n : ℕ}
      (hn : n = 1)
      (hT :
        ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) S,
          ∃ hs : IsManifold (𝓡 n) ∞ S,
            let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) S := cs
            let _ : IsManifold (𝓡 n) ∞ S := hs
            IsEmbeddedSubmanifold (𝓡 2) (𝓡 n) S) :
      ∃ cs1 : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S,
        ∃ hs1 : IsManifold (𝓡 1) ∞ S,
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S := cs1
          let _ : IsManifold (𝓡 1) ∞ S := hs1
          IsEmbeddedSubmanifold (𝓡 2) (𝓡 1) S := by
    subst hn
    rcases hT with ⟨cs, hs, hEmb⟩
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S := cs
    let _ : IsManifold (𝓡 1) ∞ S := hs
    exact ⟨cs, hs, hEmb⟩
  let n : ℕ := Module.finrank ℝ R2 - Module.finrank ℝ ℝ
  have hn : n = 1 := by
    simpa [n] using problem_6_9_levelset_model_eq_one
  have hS' :
      ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) S,
        ∃ hs : IsManifold (𝓡 n) ∞ S,
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) S := cs
          let _ : IsManifold (𝓡 n) ∞ S := hs
          IsEmbeddedSubmanifold (𝓡 2) (𝓡 n) S := by
    simpa [n] using hS
  exact normalizeCodimOneInput hn hS'

/-- Helper for Problem 6-9: an embedded one-dimensional regular level set modeled on `ℝ¹` can be
transported to the standard curve model `𝓘(ℝ)`. -/
theorem transportEmbeddedSubmanifoldR1ToReal {S : Set R2}
    (hS :
      ∃ cs : ChartedSpace
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))) S,
        ∃ hs :
            IsManifold
              (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
              ∞
              S,
          let _ : ChartedSpace
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))) S := cs
          let _ :
              IsManifold
                (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
                ∞
                S := hs
          IsEmbeddedSubmanifold
            (𝓡 2)
            (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
            S) :
    ∃ (_ : ChartedSpace ℝ S) (_ : IsManifold 𝓘(ℝ) ∞ S),
      IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ) S := by
  -- First normalize the codimension-one witness to the chapter's `𝓡 1` owner.
  have hR1 :
      ∃ cs1 : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S,
        ∃ hs1 : IsManifold (𝓡 1) ∞ S,
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S := cs1
          let _ : IsManifold (𝓡 1) ∞ S := hs1
          IsEmbeddedSubmanifold (𝓡 2) (𝓡 1) S :=
    problem_6_9_transportInput_of_codimOne hS
  rcases hR1 with ⟨cs, hs, hEmb⟩
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S := cs
  let _ : IsManifold (𝓡 1) ∞ S := hs
  let eModel :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) ℝ :=
    realToR1Equiv.toHomeomorph.symm.toOpenPartialHomeomorph
  have heModel_source : eModel.source = Set.univ := by
    -- The model change comes from a global homeomorphism, so its source is all of `ℝ¹`.
    ext x
    simp [eModel]
  let _ : ChartedSpace ℝ (EuclideanSpace ℝ (Fin 1)) := eModel.singletonChartedSpace heModel_source
  let instCharted : ChartedSpace ℝ S := ChartedSpace.comp ℝ (EuclideanSpace ℝ (Fin 1)) S
  let _ : ChartedSpace ℝ S := instCharted
  have instManifold : IsManifold 𝓘(ℝ) ∞ S := by
    have hGroupoid : HasGroupoid S (contDiffGroupoid ∞ 𝓘(ℝ)) := by
      refine ⟨?_⟩
      rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
      have hcEq : c = eModel := by
        simpa [eModel] using
          eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c hc
      have hc'Eq : c' = eModel := by
        simpa [eModel] using
          eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c' hc'
      subst c
      subst c'
      have hcompat_old :
          f.symm.trans f' ∈ contDiffGroupoid ∞ (𝓡 1) :=
        HasGroupoid.compatible hf hf'
      simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc, eModel] using
        r1TransitionMemContDiffGroupoidReal hcompat_old
    let _ : HasGroupoid S (contDiffGroupoid ∞ 𝓘(ℝ)) := hGroupoid
    exact IsManifold.mk' 𝓘(ℝ) ∞ S
  let _ : IsManifold 𝓘(ℝ) ∞ S := instManifold
  have hSubtypeImmersion :
      Manifold.IsImmersion 𝓘(ℝ) (𝓡 2) (⊤ : WithTop ℕ∞) (Subtype.val : S → R2) := by
    have hSubtypeOld :
        Manifold.IsSmoothEmbedding
          (𝓡 1)
          (𝓡 2)
          (⊤ : WithTop ℕ∞)
          (Subtype.val : S → R2) := by
      simpa using hEmb.isSmoothEmbedding_subtype_val
    let hImm := hSubtypeOld.isImmersion
    let hComp := hImm.complement
    let hCompImm := hImm.isImmersionOfComplement_complement
    refine ⟨hComp, inferInstance, inferInstance, ?_⟩
    intro x
    let hx := hCompImm x
    let equivReal :
        (ℝ × hComp) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (realToR1Equiv.prodCongr (ContinuousLinearEquiv.refl ℝ hComp)).trans hx.equiv
    have hdomChart :
        hx.domChart.trans eModel ∈ IsManifold.maximalAtlas 𝓘(ℝ) (⊤ : WithTop ℕ∞) S := by
      rw [IsManifold.mem_maximalAtlas_iff]
      intro d hd
      rcases hd with ⟨f, hf, c, hc, rfl⟩
      have hcEq : c = eModel := by
        simpa [eModel] using
          eModel.singletonChartedSpace_mem_atlas_eq (h := heModel_source) c hc
      subst c
      have hleft_old :
          hx.domChart.symm.trans f ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1) := by
        exact (hx.domChart_mem_maximalAtlas f hf).1
      have hright_old :
          f.symm.trans hx.domChart ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 1) := by
        exact (hx.domChart_mem_maximalAtlas f hf).2
      constructor
      · simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc, eModel] using
          r1TransitionMemContDiffGroupoidReal hleft_old
      · simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_assoc, eModel] using
          r1TransitionMemContDiffGroupoidReal hright_old
    -- Reuse the old immersion witness pointwise and only change the source chart.
    refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      equivReal (hx.domChart.trans eModel) hx.codChart ?_ ?_ hdomChart hx.codChart_mem_maximalAtlas
      ?_ ?_
    · -- The transported source chart still contains the point `x`.
      simpa [OpenPartialHomeomorph.trans_source, eModel] using hx.mem_domChart_source
    · -- The codomain chart condition is unchanged.
      simpa using hx.mem_codChart_source
    · -- A point in the transported source chart is still in the old source chart.
      intro z hz
      have hz' : z ∈ hx.domChart.source := by
        simpa [OpenPartialHomeomorph.trans_source, eModel] using hz
      exact hx.source_subset_preimage_source hz'
    · -- In transported source coordinates, the inclusion has the same normal form as before.
      intro u hu
      have hu' :
          realToR1Equiv u ∈ (hx.domChart.extend (𝓡 1)).target := by
        simpa [eModel, OpenPartialHomeomorph.extend_target,
          OpenPartialHomeomorph.trans_target] using hu
      simpa [equivReal, eModel, Function.comp, OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm] using hx.writtenInCharts hu'
  have hSubtype :
      Manifold.IsSmoothEmbedding
        𝓘(ℝ)
        (𝓡 2)
        (⊤ : WithTop ℕ∞)
        (Subtype.val : S → R2) :=
    ⟨hSubtypeImmersion, Topology.IsEmbedding.subtypeVal⟩
  refine ⟨instCharted, instManifold, ?_⟩
  exact
    { toBoundarylessManifold := inferInstance
      isSmoothEmbedding_subtype_val := by
        simpa using hSubtype }

/-- Helper for Problem 6-9: a scalar regular level set in `ℝ²` is an embedded curve after the
canonical `ℝ¹`-to-`ℝ` transport. -/
theorem problem_6_9_scalarRegularLevel_isEmbeddedCurve
    {Φ : R2 → ℝ} {c : ℝ}
    (hΦ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ Φ)
    (hreg : IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) Φ c) :
    ∃ (_ : ChartedSpace ℝ (Φ ⁻¹' ({c} : Set ℝ)))
      (_ : IsManifold 𝓘(ℝ) ∞ (Φ ⁻¹' ({c} : Set ℝ))),
      IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ)
        (Φ ⁻¹' ({c} : Set ℝ)) := by
  -- First package the regular level set as an embedded codimension-one `ℝ¹`-submanifold.
  have hR1 :
      ∃ cs : ChartedSpace
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ)))
          (Φ ⁻¹' ({c} : Set ℝ)),
        ∃ hs :
            IsManifold
              (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
              ∞
              (Φ ⁻¹' ({c} : Set ℝ)),
          let _ : ChartedSpace
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ R2 - Module.finrank ℝ ℝ)))
              (Φ ⁻¹' ({c} : Set ℝ)) := cs
          let _ :
              IsManifold
                (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
                ∞
                (Φ ⁻¹' ({c} : Set ℝ)) := hs
          IsEmbeddedSubmanifold
            (𝓡 2)
            (𝓡 (Module.finrank ℝ R2 - Module.finrank ℝ ℝ))
            (Φ ⁻¹' ({c} : Set ℝ)) := by
    simpa using
      (regular_level_set_has_embedded_submanifold_structure
        (I := 𝓡 2) (J := 𝓘(ℝ, ℝ)) (Φ := Φ) (c := c) hΦ hreg)
  -- Then transport the codimension-one model to the standard real-line model used in the chapter.
  exact transportEmbeddedSubmanifoldR1ToReal hR1

/-- Helper for Problem 6-9: at the exceptional radius `√2`, the fiber `F ⁻¹(S_{√2}(0))` is the
zero fiber of the second coordinate projection. -/
theorem problem_6_9_preimage_eq_secondCoordinate_zeroFiber_of_sqrtTwo :
    problem_6_9_map ⁻¹' sphereR (Real.sqrt 2) =
      (fun p : R2 ↦ p 1) ⁻¹' ({0} : Set ℝ) := by
  rw [problem_6_9_preimage_eq_radius_sq_level_set (Real.sqrt 2) (by positivity)]
  ext p
  rw [Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff,
    Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  exact problem_6_9_radiusSq_eq_two_iff p

/-- Helper for Problem 6-9: the second-coordinate projection has surjective manifold derivative at
every point of `ℝ²`. -/
theorem problem_6_9_secondCoordinate_mfderiv_surjective (p : R2) :
    Function.Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q : R2 ↦ q 1) p) := by
  rw [mfderiv_eq_fderiv]
  change Function.Surjective (fderiv ℝ (fun q : R2 ↦ q 1) p : R2 →L[ℝ] ℝ)
  have h1 :
      HasFDerivAt (fun q : R2 ↦ q 1)
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1
  rw [h1.fderiv]
  intro y
  refine ⟨WithLp.toLp 2 ![(0 : ℝ), y], ?_⟩
  simp [PiLp.proj_apply, PiLp.toLp_apply]

/-- Helper for Problem 6-9 (2): for `r < 0` the sphere `S_r(0)` is empty, while for `r = 0` it
is `{0}`; since `problem_6_9_map` never hits the origin, the preimage is empty throughout
`r ≤ 0`. -/
theorem problem_6_9_preimage_eq_empty_of_nonpos (r : ℝ) (hr : r ≤ 0) :
    problem_6_9_map ⁻¹' sphereR r = ∅ := by
  -- A point on a nonpositive-radius sphere would force `F p = 0`, but the third coordinate of
  -- `F` is always positive.
  ext p
  constructor
  · intro hp
    have hnorm : ‖problem_6_9_map p‖ = r := mem_sphere_zero_iff_norm.1 hp
    have hr0 : r = 0 := by
      have hnonneg : 0 ≤ ‖problem_6_9_map p‖ := norm_nonneg _
      linarith
    have hzeroNorm : ‖problem_6_9_map p‖ = 0 := by
      simpa [hr0] using hnorm
    have hzero : problem_6_9_map p = 0 := norm_eq_zero.1 hzeroNorm
    have hcoord := congrArg (fun q : R3 ↦ q 2) hzero
    have hexpZero : Real.exp (-p 1) = 0 := by
      simpa [problem_6_9_map, PiLp.toLp_apply] using hcoord
    exact (Real.exp_ne_zero (-p 1)) hexpZero
  · intro hp
    simp at hp

/-- Problem 6-9 (2): for every radius `r`, the preimage `F ⁻¹(S_r(0))` carries a
1-dimensional embedded-submanifold structure in `ℝ^2`; for `r ≤ 0` this is the empty
submanifold. -/
theorem problem_6_9_preimage_is_embedded_submanifold (r : ℝ) :
    ∃ (_ : ChartedSpace ℝ (problem_6_9_map ⁻¹' sphereR r))
      (_ : IsManifold 𝓘(ℝ) ∞ (problem_6_9_map ⁻¹' sphereR r)),
      IsEmbeddedSubmanifold (𝓡 2) 𝓘(ℝ)
        (problem_6_9_map ⁻¹' sphereR r) := by
  by_cases hr : r ≤ 0
  · -- Nonpositive radii give the empty fiber.
    rw [problem_6_9_preimage_eq_empty_of_nonpos r hr]
    refine ⟨ChartedSpace.empty _ _, ?_, ?_⟩
    · infer_instance
    · infer_instance
  · have hrpos : 0 < r := lt_of_not_ge hr
    by_cases hsqrt : r = Real.sqrt 2
    · -- Rewrite the exceptional fiber to the zero set of the second coordinate.
      rw [hsqrt, problem_6_9_preimage_eq_secondCoordinate_zeroFiber_of_sqrtTwo]
      have hproj :
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : R2 ↦ p 1) := by
        rw [contMDiff_iff_contDiff]
        simpa using
          ((contDiff_piLp_apply (p := 2) (i := (1 : Fin 2))) :
            ContDiff ℝ ∞ (fun p : R2 ↦ p 1))
      have hreg :
          IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) (fun p : R2 ↦ p 1) 0 := by
        rw [Manifold.isRegularValue_iff_forall_isRegularPoint]
        intro p hp
        rw [Manifold.isRegularPoint_iff_surjective_mfderiv]
        exact problem_6_9_secondCoordinate_mfderiv_surjective p
      -- The exceptional radius is still a scalar regular level set, now packaged once and for all.
      exact problem_6_9_scalarRegularLevel_isEmbeddedCurve hproj hreg
    · -- Away from the exceptional radius, the scalar regular-level-set theorem applies.
      rw [problem_6_9_preimage_eq_radius_sq_level_set r hrpos.le]
      have hreg :
          IsRegularValue (𝓡 2) 𝓘(ℝ, ℝ) problem_6_9_radius_sq (r ^ (2 : ℕ)) := by
        exact (problem_6_9_radius_sq_isRegularValue_iff r hrpos).2 hsqrt
      -- Away from `√2`, the same scalar regular-level-set package closes the argument.
      exact problem_6_9_scalarRegularLevel_isEmbeddedCurve
        problem_6_9_radius_sq_contMDiff hreg

end
