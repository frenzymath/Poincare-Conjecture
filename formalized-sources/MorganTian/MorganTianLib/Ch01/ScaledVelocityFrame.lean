import MorganTianLib.Ch01.RicciFrameTrace

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- The coefficient space of the parallel frame (see `FrameRadialBridge`). -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The standard orthonormal basis of the coefficient space. -/
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-- **Math.** A parallel orthonormal frame with `L` times its first vector
equal to the geodesic velocity, for any positive initial speed `L`. -/
theorem exists_orthonormalParallelFrameAlong_scaled_velocity
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b L : ℝ} (hab : a < b) (hL : 0 < L)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsize : g.metricInner (γ a) (mfderivVelocity (I := I) (E := E) γ a)
      (mfderivVelocity (I := I) (E := E) γ a) = L ^ 2) :
    ∃ e : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
              = if i = j then 1 else 0)
        ∧ ∀ t ∈ Icc a b,
            L • (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have haIcc : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  set v₀ : TangentSpace I (γ a) := L⁻¹ • mfderivVelocity (I := I) (E := E) γ a with hv₀
  -- the velocity has unit length at `a`
  have hnorm : ‖v₀‖ = 1 := by
    have h1 : ‖v₀‖ * ‖v₀‖ = 1 := by
      rw [← real_inner_self_eq_norm_mul_norm]
      change g.metricInner (γ a) (L⁻¹ • mfderivVelocity (I := I) (E := E) γ a)
        (L⁻¹ • mfderivVelocity (I := I) (E := E) γ a) = 1
      rw [g.metricInner_smul_left, g.metricInner_smul_right, hsize]
      field_simp
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact h
    · exact absurd h (by linarith [norm_nonneg v₀])
  -- extend `{γ'(a)}` to an orthonormal basis of `T_{γ a}M`
  have hcard : Module.finrank ℝ (TangentSpace I (γ a))
      = Fintype.card (Fin (Module.finrank ℝ E)) := (Fintype.card_fin _).symm
  have hsingle : Orthonormal ℝ
      (Set.restrict ({0} : Set (Fin (Module.finrank ℝ E))) (fun _ => v₀)) := by
    constructor
    · intro i
      simpa using hnorm
    · intro i j hij
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
        (Set.mem_singleton_iff.mp j.2).symm)) hij
  obtain ⟨bas, hbas⟩ := hsingle.exists_orthonormalBasis_extension_of_card_eq hcard
  have hbas0 : bas 0 = v₀ := hbas 0 rfl
  have h0 : ∀ i j, g.metricInner (γ a) (bas i : TangentSpace I (γ a)) (bas j)
      = if i = j then 1 else 0 := fun i j => orthonormal_iff_ite.mp bas.orthonormal i j
  -- parallel-transport the basis
  obtain ⟨e, hinit, hpar, hgram⟩ :=
    exists_parallelFrameAlong (I := I) hab hgeo hγc
      (fun i => (bas i : TangentSpace I (γ a)))
  refine ⟨e, hpar, fun t ht i j => by rw [hgram i j t ht]; exact h0 i j, ?_⟩
  -- the `0`-th transported field and the velocity are parallel with the same initial value
  have hvel : IsParallelAlongOn (I := I) g γ (mfderivVelocity (I := I) (E := E) γ) a b :=
    isParallelAlongOn_mfderivVelocity (I := I) hab hgeo hγc
  have he0a : L • (e 0 a : TangentSpace I (γ a)) = mfderivVelocity (I := I) (E := E) γ a := by
    rw [hinit 0, hbas0]
    simp only [v₀, smul_smul, mul_inv_cancel₀ (ne_of_gt hL), one_smul]
  intro t ht
  have hVV := congrArg (fun z : ℝ => L * (L * z))
    ((hpar 0).metricInner_eq (hpar 0) hgeo hγc t ht)
  have hVW := congrArg (fun z : ℝ => L * z)
    ((hpar 0).metricInner_eq hvel hgeo hγc t ht)
  have hWV := congrArg (fun z : ℝ => L * z)
    (hvel.metricInner_eq (hpar 0) hgeo hγc t ht)
  have hWW := hvel.metricInner_eq hvel hgeo hγc t ht
  have h1 : g.metricInner (γ t) (L • e 0 t) (L • e 0 t) = L ^ 2 := by
    rw [g.metricInner_smul_left, g.metricInner_smul_right, hVV,
      ← g.metricInner_smul_right, ← g.metricInner_smul_left, he0a, hsize]
  have h2 : g.metricInner (γ t) (L • e 0 t) (mfderivVelocity (I := I) (E := E) γ t) = L ^ 2 := by
    rw [g.metricInner_smul_left, hVW, ← g.metricInner_smul_left, he0a, hsize]
  have h3 : g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t) (L • e 0 t) = L ^ 2 := by
    rw [g.metricInner_smul_right, hWV, ← g.metricInner_smul_right, he0a, hsize]
  exact eq_of_metricInner_eq_const (I := I) g h1 h2 h3 (hWW.trans hsize)

/-- **Math.** The first column of the frame Jacobi operator vanishes when
the velocity is a scalar multiple of the first frame vector. -/
theorem frameCurvOp_scaled_radial_eq_zero (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t L : ℝ)
    (hrad : L • (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t) :
    frameCurvOp (I := I) g γ e t (𝔟 0 : 𝔼) = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hB := isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC (γ t)
  have hcol (i : Fin (Module.finrank ℝ E)) : frameCurv (I := I) g γ e i 0 t = 0 := by
    change curvatureFormAt g g.leviCivitaConnection (γ t) (e 0 t)
      (mfderivVelocity (I := I) (E := E) γ t) (mfderivVelocity (I := I) (E := E) γ t) (e i t) = 0
    rw [← hrad, hB.smul_two]
    have h := hB.antisymm₁₂ (e 0 t) (e 0 t) (L • e 0 t) (e i t)
    have hz : curvatureFormAt g g.leviCivitaConnection (γ t)
        (e 0 t) (e 0 t) (L • e 0 t) (e i t) = 0 := by linarith
    rw [hz, mul_zero]
  rw [frameCurvOp_apply]
  simp only [basisFun_inner (E := E), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hcol, neg_zero, zero_smul, Finset.sum_const_zero]

end MorganTianLib
end
