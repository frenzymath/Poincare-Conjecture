import LeeSmoothLib.Ch06.Sec06_45.Problem_6_10
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

-- Semantic search note: `lean_leansearch` did not surface a ready-made composition/transversality
-- theorem for this chapter-local API, so this item follows the real finite-dimensional owner
-- level used by `Problem_6_10`.

section TransversePreimageComposition

universe uEM uEN uEP uEX uEGX uHM uHN uHP uHX uHGX uM uN uP

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {EP : Type uEP} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
variable {EX : Type uEX} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
variable {EGX : Type uEGX} [NormedAddCommGroup EGX] [NormedSpace ℝ EGX]
  [FiniteDimensional ℝ EGX]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HP : Type uHP} [TopologicalSpace HP]
variable {HX : Type uHX} [TopologicalSpace HX]
variable {HGX : Type uHGX} [TopologicalSpace HGX]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace HP P]
variable {I : ModelWithCorners ℝ EM HM} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N]
variable {K : ModelWithCorners ℝ EP HP} [IsManifold K ∞ P]
variable {JX : ModelWithCorners ℝ EX HX} {X : Set P}
variable [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold K JX X]

/-- Helper for Problem 6-11: transversality data for `A` against the pulled-back subspace
`S.comap B` is equivalent to transversality data for the composite `B.comp A` against `S` once
`B` is already transverse to `S`. -/
lemma compRangeSup_eq_top_iff_rangeSupComap_eq_top
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (A : U →ₗ[ℝ] V) (B : V →ₗ[ℝ] W) (S : Submodule ℝ W)
    (hB : B.range ⊔ S = ⊤) :
    A.range ⊔ S.comap B = ⊤ ↔ (B.comp A).range ⊔ S = ⊤ := by
  constructor
  · intro hA
    -- Decompose an ambient vector first using transversality of `B`, then refine the `B.range`
    -- part using transversality of `A` to the pulled-back subspace.
    rw [eq_top_iff]
    intro w hw
    have hw' : w ∈ B.range ⊔ S := by
      simp [hB]
    rcases Submodule.mem_sup.1 hw' with ⟨w₁, hw₁, w₂, hw₂, rfl⟩
    rcases LinearMap.mem_range.1 hw₁ with ⟨v, rfl⟩
    have hv : v ∈ A.range ⊔ S.comap B := by
      simp [hA]
    rcases Submodule.mem_sup.1 hv with ⟨v₁, hv₁, v₂, hv₂, rfl⟩
    rcases LinearMap.mem_range.1 hv₁ with ⟨u, rfl⟩
    refine Submodule.mem_sup.2 ?_
    refine ⟨B (A u), LinearMap.mem_range.2 ⟨u, rfl⟩, B v₂ + w₂, ?_, ?_⟩
    · exact S.add_mem (Submodule.mem_comap.1 hv₂) hw₂
    · simp [map_add, add_left_comm, add_comm]
  · intro hComp
    -- Read the composite transversality equation at `B v`, then move the `A.range` term back to
    -- the domain of `B`.
    rw [eq_top_iff]
    intro v hv
    have hBv : B v ∈ (B.comp A).range ⊔ S := by
      simp [hComp]
    rcases Submodule.mem_sup.1 hBv with ⟨w₁, hw₁, w₂, hw₂, hsum⟩
    rcases LinearMap.mem_range.1 hw₁ with ⟨u, hu⟩
    refine Submodule.mem_sup.2 ?_
    refine ⟨A u, LinearMap.mem_range.2 ⟨u, rfl⟩, v - A u, ?_, by simp⟩
    apply Submodule.mem_comap.2
    rw [map_sub]
    have hsub :
        B v - B (A u) = w₂ := by
      apply sub_eq_iff_eq_add.2
      calc
        B v = w₁ + w₂ := by simpa using hsum.symm
        _ = (B.comp A) u + w₂ := by rw [← hu]
        _ = B (A u) + w₂ := by rfl
        _ = w₂ + B (A u) := by simp [add_comm]
    simpa [hsub] using hw₂

omit [TopologicalSpace M] in
/-- Helper for Problem 6-11: at a composite-preimage point, the tangent space of `G ⁻¹' X`
is the comap of the tangent space of `X` under `dG`. -/
lemma preimageTangentSpaceEqComap_atCompositePoint
    {F : M → N} {G : N → P} {JGX : ModelWithCorners ℝ EGX HGX}
    [ChartedSpace HGX (G ⁻¹' X)] [IsManifold JGX ∞ (G ⁻¹' X)]
    [IsEmbeddedSubmanifold J JGX (G ⁻¹' X)]
    (hGtrans : IsTransverseToSubmanifold K J JX X G)
    (p : (G ∘ F) ⁻¹' X) :
    let q : G ⁻¹' X := ⟨F p, p.2⟩
    let x : X := ⟨G (F p), p.2⟩
    T[JGX; q] = (T[JX; x]).comap (mfderiv J K G (F p)).toLinearMap := by
  -- Repackage the composite-preimage point as a point of `G ⁻¹' X` and reuse Problem 6-10.
  let q : G ⁻¹' X := ⟨F p, p.2⟩
  let x : X := ⟨G (F p), p.2⟩
  simpa [q, x, Function.comp] using
    (tangentSpace_preimage_eq_comap_of_transverse
      (I := K) (K := J) (JX := JX) (X := X) (JW := JGX) (f := G) hGtrans q)

omit [FiniteDimensional ℝ EM] [IsManifold I ∞ M] in
/-- Helper for Problem 6-11: the pointwise transversality equation for `F` against `G ⁻¹' X`
matches the pointwise transversality equation for `G ∘ F` against `X`. -/
lemma compositeTransversePointwise_iff_preimageTransversePointwise
    {F : M → N} {G : N → P} {JGX : ModelWithCorners ℝ EGX HGX}
    [ChartedSpace HGX (G ⁻¹' X)] [IsManifold JGX ∞ (G ⁻¹' X)]
    [IsEmbeddedSubmanifold J JGX (G ⁻¹' X)]
    (hF : ContMDiff I J ∞ F)
    (hGtrans : IsTransverseToSubmanifold K J JX X G)
    (p : (G ∘ F) ⁻¹' X) :
    let q : G ⁻¹' X := ⟨F p, p.2⟩
    let x : X := ⟨G (F p), p.2⟩
    ((mfderiv I J F p).range ⊔ T[JGX; q] = ⊤) ↔
      ((mfderiv I K (G ∘ F) p).range ⊔ T[JX; x] = ⊤) := by
  -- Rewrite the pulled-back tangent space by Problem 6-10, rewrite the derivative of the
  -- composite by the chain rule, and apply the linear bridge.
  let q : G ⁻¹' X := ⟨F p, p.2⟩
  let x : X := ⟨G (F p), p.2⟩
  have hFmdiff : MDifferentiableAt I J F p :=
    hF.contMDiffAt.mdifferentiableAt (by simp)
  have hGmdiff : MDifferentiableAt J K G (F p) :=
    hGtrans.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hTangent :
      T[JGX; q] = (T[JX; x]).comap (mfderiv J K G (F p)).toLinearMap := by
    simpa [q, x, Function.comp] using
      preimageTangentSpaceEqComap_atCompositePoint
        (JX := JX) (JGX := JGX) (F := F) (G := G) hGtrans p
  have hAmbient :
      (mfderiv J K G (F p)).range ⊔ T[JX; x] = ⊤ := by
    simpa [q, x, Function.comp] using hGtrans.tangent_sup_eq_top q
  have hComp :
      mfderiv I K (G ∘ F) p = (mfderiv J K G (F p)).comp (mfderiv I J F p) := by
    simpa [Function.comp] using mfderiv_comp (x := (p : M)) (f := F) (g := G) hGmdiff hFmdiff
  simpa [q, x, hTangent, hComp] using
    (compRangeSup_eq_top_iff_rangeSupComap_eq_top
      (A := (mfderiv I J F p).toLinearMap)
      (B := (mfderiv J K G (F p)).toLinearMap)
      (S := T[JX; x])
      hAmbient)

/-- Problem 6-11: if `F : M → N` is smooth, `G : N → P` is transverse to the embedded
submanifold `X ⊆ P`, and `G ⁻¹' X` carries a chosen embedded submanifold structure, then `F` is
transverse to `G ⁻¹' X` if and only if `G ∘ F` is transverse to `X`. -/
theorem transverse_preimage_iff_comp_transverse
    {F : M → N} {G : N → P} {JGX : ModelWithCorners ℝ EGX HGX}
    [ChartedSpace HGX (G ⁻¹' X)] [IsManifold JGX ∞ (G ⁻¹' X)]
    (hF : ContMDiff I J ∞ F)
    [IsEmbeddedSubmanifold J JGX (G ⁻¹' X)]
    (hGtrans : IsTransverseToSubmanifold K J JX X G) :
    IsTransverseToSubmanifold J I JGX (G ⁻¹' X) F ↔
      IsTransverseToSubmanifold K I JX X (G ∘ F) := by
  constructor
  · intro hPreimage
    -- Unpack transversality of `F` to `G ⁻¹' X`, then transport each pointwise spanning equation
    -- to the composite map.
    refine (isTransverseToSubmanifold_iff (I := K) (K := I) (JX := JX) (X := X) (G ∘ F)).2 ?_
    refine ⟨hGtrans.contMDiff.comp hPreimage.contMDiff, ?_⟩
    intro p
    have hPoint :
        (mfderiv I J F p).range ⊔
            T[JGX; (⟨F p, p.2⟩ : G ⁻¹' X)] = ⊤ := by
      simpa [Function.comp] using hPreimage.tangent_sup_eq_top (⟨p, p.2⟩ : F ⁻¹' (G ⁻¹' X))
    exact
      (compositeTransversePointwise_iff_preimageTransversePointwise
        (JX := JX) (JGX := JGX) (F := F) (G := G) hPreimage.contMDiff hGtrans p).1 hPoint
  · intro hComp
    -- Read the composite transversality equation back through the same pointwise comparison and
    -- repackage it as transversality of `F` to the preimage submanifold.
    refine (isTransverseToSubmanifold_iff
      (I := J) (K := I) (JX := JGX) (X := G ⁻¹' X) F).2 ?_
    refine ⟨hF, ?_⟩
    intro p
    let q : (G ∘ F) ⁻¹' X := ⟨p, p.2⟩
    have hPoint :
        (mfderiv I K (G ∘ F) q).range ⊔ T[JX; (⟨G (F q), q.2⟩ : X)] = ⊤ := by
      simpa [q, Function.comp] using hComp.tangent_sup_eq_top q
    simpa [q, Function.comp] using
      (compositeTransversePointwise_iff_preimageTransversePointwise
        (JX := JX) (JGX := JGX) (F := F) (G := G) hF hGtrans q).2 hPoint

end TransversePreimageComposition
