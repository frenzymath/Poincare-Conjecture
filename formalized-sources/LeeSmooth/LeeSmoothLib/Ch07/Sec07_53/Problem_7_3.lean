import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch07.Sec07_46.Proposition_7_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uG

/-
The primary domain here is smooth group objects on manifolds. The owner abstractions are
`ContMDiffMul I ∞ G` for smooth multiplication, `LieGroup I ∞ G` for the full Lie-group structure,
and `IsLocalDiffeomorph` for the shear-map bridge used to recover inversion.
-/

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G]

/-- The shear map `(g, h) ↦ (g, gh)` on `G × G` is bijective. -/
theorem multiplication_shear_bijective :
    Function.Bijective (fun p : G × G ↦ (p.1, p.1 * p.2)) := by
  constructor
  · intro p q hpq
    -- Compare the two coordinates separately; the second then cancels on the left.
    rcases p with ⟨g, h⟩
    rcases q with ⟨g', h'⟩
    have hg : g = g' := by
      simpa using congrArg Prod.fst hpq
    have hmul : g * h = g' * h' := by
      simpa using congrArg Prod.snd hpq
    subst hg
    have hh : h = h' := mul_left_cancel hmul
    subst hh
    rfl
  · intro p
    -- The explicit inverse sends `(u, v)` to `(u, u⁻¹ * v)`.
    refine ⟨(p.1, p.1⁻¹ * p.2), ?_⟩
    ext <;> simp

section BoundarylessLocalDiffeomorph

variable {κ : Type*} [RCLike κ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace κ F] [CompleteSpace F]
variable {L : Type*} [TopologicalSpace L]
variable {K : ModelWithCorners κ F L}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace L M] [IsManifold K ∞ M]
  [BoundarylessManifold K M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace L N] [IsManifold K ∞ N]

/-- Helper for Problem 7-3: on a boundaryless source manifold, smoothness together with an
invertible manifold derivative already gives a local diffeomorphism. -/
lemma isLocalDiffeomorphAt_of_boundaryless_contMDiff_mfderivIsInvertible
    {f : M → N} {p : M}
    (hf : ContMDiff K K ∞ f)
    (hfp : (mfderiv K K f p).IsInvertible) :
    IsLocalDiffeomorphAt K K ∞ f p := by
  -- Route correction: prove the inverse-function-theorem bridge in a fresh scalar context, so
  -- later instantiations do not inherit the local `[NontriviallyNormedField]/[RCLike]` diamond.
  exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
    (I := K) (J := K) (n := ∞) (by simp)
    (BoundarylessManifold.isInteriorPoint (I := K) (x := p)) hf hfp

end BoundarylessLocalDiffeomorph

section SmoothMultiplication

variable [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]

/-- Helper for Problem 7-3: the shear map `(g, h) ↦ (g, gh)`. -/
def multiplicationShear : G × G → G × G := fun p ↦ (p.1, p.1 * p.2)

/-- Helper for Problem 7-3: evaluate the shear map pointwise. -/
@[simp] lemma multiplicationShear_apply (p : G × G) :
    multiplicationShear p = (p.1, p.1 * p.2) :=
  rfl

/-- Helper for Problem 7-3: the lower-triangular block map
`(U, Y) ↦ (U, B U + A Y)` on a product of tangent spaces. -/
def lowerTriangularProdMap
    {P Q R : Type*}
    [TopologicalSpace P] [AddCommGroup P] [Module 𝕜 P] [IsTopologicalAddGroup P]
    [ContinuousSMul 𝕜 P]
    [TopologicalSpace Q] [AddCommGroup Q] [Module 𝕜 Q] [IsTopologicalAddGroup Q]
    [ContinuousSMul 𝕜 Q]
    [TopologicalSpace R] [AddCommGroup R] [Module 𝕜 R] [IsTopologicalAddGroup R]
    [ContinuousSMul 𝕜 R]
    (B : P →L[𝕜] R) (A : Q →L[𝕜] R) :
    P × Q →L[𝕜] P × R :=
  (ContinuousLinearMap.fst 𝕜 P Q).prod
    (B.comp (ContinuousLinearMap.fst 𝕜 P Q) + A.comp (ContinuousLinearMap.snd 𝕜 P Q))

/-- Helper for Problem 7-3: evaluate the lower-triangular block map pointwise. -/
@[simp] lemma lowerTriangularProdMap_apply
    {P Q R : Type*}
    [TopologicalSpace P] [AddCommGroup P] [Module 𝕜 P] [IsTopologicalAddGroup P]
    [ContinuousSMul 𝕜 P]
    [TopologicalSpace Q] [AddCommGroup Q] [Module 𝕜 Q] [IsTopologicalAddGroup Q]
    [ContinuousSMul 𝕜 Q]
    [TopologicalSpace R] [AddCommGroup R] [Module 𝕜 R] [IsTopologicalAddGroup R]
    [ContinuousSMul 𝕜 R]
    (B : P →L[𝕜] R) (A : Q →L[𝕜] R) (u : P × Q) :
    lowerTriangularProdMap B A u = (u.1, B u.1 + A u.2) :=
  rfl

/-- Helper for Problem 7-3: the unit-diagonal shear `(U, V) ↦ (U, B U + V)` is invertible. -/
lemma unitLowerTriangularProdMapIsInvertible
    {P R : Type*}
    [TopologicalSpace P] [AddCommGroup P] [Module 𝕜 P] [IsTopologicalAddGroup P]
    [ContinuousSMul 𝕜 P]
    [TopologicalSpace R] [AddCommGroup R] [Module 𝕜 R] [IsTopologicalAddGroup R]
    [ContinuousSMul 𝕜 R]
    (B : P →L[𝕜] R) :
    (lowerTriangularProdMap B (ContinuousLinearMap.id 𝕜 R)).IsInvertible := by
  let F : P × R →L[𝕜] P × R :=
    lowerTriangularProdMap B (ContinuousLinearMap.id 𝕜 R)
  let G : P × R →L[𝕜] P × R :=
    (ContinuousLinearMap.fst 𝕜 P R).prod
      (ContinuousLinearMap.snd 𝕜 P R - B.comp (ContinuousLinearMap.fst 𝕜 P R))
  have hFG : F ∘L G = ContinuousLinearMap.id 𝕜 (P × R) := by
    -- Compose the explicit inverse on the right and simplify each coordinate separately.
    apply ContinuousLinearMap.ext
    intro u
    rcases u with ⟨U, V⟩
    apply Prod.ext
    · rfl
    · simp [F, G, lowerTriangularProdMap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hGF : G ∘L F = ContinuousLinearMap.id 𝕜 (P × R) := by
    -- The same coordinatewise computation gives the inverse in the other order.
    apply ContinuousLinearMap.ext
    intro u
    rcases u with ⟨U, V⟩
    apply Prod.ext
    · rfl
    · simp [F, G, lowerTriangularProdMap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  exact ContinuousLinearMap.IsInvertible.of_inverse hFG hGF

/-- Helper for Problem 7-3: a lower-triangular block map is invertible as soon as its diagonal
block is invertible. -/
lemma lowerTriangularProdMapIsInvertible
    {P Q R : Type*}
    [TopologicalSpace P] [AddCommGroup P] [Module 𝕜 P] [IsTopologicalAddGroup P]
    [ContinuousSMul 𝕜 P]
    [TopologicalSpace Q] [AddCommGroup Q] [Module 𝕜 Q] [IsTopologicalAddGroup Q]
    [ContinuousSMul 𝕜 Q]
    [TopologicalSpace R] [AddCommGroup R] [Module 𝕜 R] [IsTopologicalAddGroup R]
    [ContinuousSMul 𝕜 R]
    (B : P →L[𝕜] R) (A : Q →L[𝕜] R) (hA : A.IsInvertible) :
    (lowerTriangularProdMap B A).IsInvertible := by
  rcases hA with ⟨eA, rfl⟩
  -- Route correction: factor the block map through the diagonal equivalence and the unit shear.
  have hDiag :
      ((ContinuousLinearMap.id 𝕜 P).prodMap (eA : Q →L[𝕜] R)).IsInvertible := by
    refine ⟨(ContinuousLinearEquiv.refl 𝕜 P).prodCongr eA, ?_⟩
    simpa using
      (ContinuousLinearEquiv.coe_prodCongr (ContinuousLinearEquiv.refl 𝕜 P) eA)
  have hShear :
      (lowerTriangularProdMap B (ContinuousLinearMap.id 𝕜 R)).IsInvertible :=
    unitLowerTriangularProdMapIsInvertible B
  have hFactor :
      lowerTriangularProdMap B (eA : Q →L[𝕜] R) =
        lowerTriangularProdMap B (ContinuousLinearMap.id 𝕜 R) ∘L
          ((ContinuousLinearMap.id 𝕜 P).prodMap (eA : Q →L[𝕜] R)) := by
    -- Applying the diagonal block first reduces the target map to the unit shear.
    apply ContinuousLinearMap.ext
    intro u
    rcases u with ⟨U, Y⟩
    rfl
  rw [hFactor]
  exact hShear.comp hDiag

/-- Helper for Problem 7-3: the inverse left translation `h ↦ g⁻¹ * h` is smooth. -/
theorem contMDiff_mul_left_inv (g : G) : ContMDiff I I ∞ fun h : G ↦ g⁻¹ * h := by
  -- This is the ordinary left-multiplication smoothness theorem applied to `g⁻¹`.
  simpa using
    ((contMDiff_const : ContMDiff I I ∞ fun _ : G ↦ g⁻¹).mul contMDiff_id)

/-- Helper for Problem 7-3: left translation by a fixed group element is a smooth
diffeomorphism. -/
def leftMulDiffeomorph (g : G) : G ≃ₘ⟮I, I⟯ G :=
  { toEquiv := Equiv.mulLeft g
    contMDiff_toFun := by
      simpa using ((contMDiff_const : ContMDiff I I ∞ fun _ : G ↦ g).mul contMDiff_id)
    contMDiff_invFun := contMDiff_mul_left_inv g }

/-- Helper for Problem 7-3: one interior chart point and smooth left translations show that `G`
has no boundary. -/
lemma boundarylessManifold_of_contMDiffMul : BoundarylessManifold I G := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := interior_extChartAt_target_nonempty I (1 : G)
  have hz_target : z ∈ (extChartAt I (1 : G)).target := interior_subset hz
  have hz_target_data : z ∈ Set.range I ∧ I.symm z ∈ (chartAt H (1 : G)).target := by
    simpa [extChartAt_target, Set.mem_preimage, Set.mem_inter_iff] using hz_target
  have hz_range : z ∈ Set.range I := hz_target_data.1
  have hz_chart_target : I.symm z ∈ (chartAt H (1 : G)).target := hz_target_data.2
  let x₀ : G := (chartAt H (1 : G)).symm (I.symm z)
  have hx₀_source : x₀ ∈ (chartAt H (1 : G)).source := by
    simpa [x₀] using (chartAt H (1 : G)).map_target hz_chart_target
  have hx₀_interior : I.IsInteriorPoint x₀ := by
    -- Convert the chosen interior chart point into an actual manifold interior point.
    refine
      (show I.IsInteriorPoint x₀ ↔
          extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target from
        @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜 _ E _ _ H _ I G _ _ ∞
          inferInstance (chartAt H (1 : G)) x₀ (by simp) (chart_mem_atlas H (1 : G))
          hx₀_source).2 ?_
    have hx₀_extChart : extChartAt I (1 : G) x₀ = z := by
      change I ((chartAt H (1 : G)) ((chartAt H (1 : G)).symm (I.symm z))) = z
      rw [(chartAt H (1 : G)).right_inv hz_chart_target]
      exact I.right_inv hz_range
    change extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target
    rw [hx₀_extChart]
    exact hz
  let Φ : G ≃ₘ⟮I, I⟯ G := leftMulDiffeomorph (x * x₀⁻¹)
  have hΦx : I.IsInteriorPoint (Φ x₀) := by
    -- Left translation preserves interior points because diffeomorphisms are local diffeomorphisms.
    exact
      ((Φ.isLocalDiffeomorph x₀).isInteriorPoint_iff (by simp)).1
        hx₀_interior
  have hΦ_apply : Φ x₀ = x := by
    change (x * x₀⁻¹) * x₀ = x
    simp [mul_assoc]
  -- The chosen translation sends the seed point `x₀` to the requested point `x`.
  simpa [hΦ_apply] using hΦx

/-- Helper for Problem 7-3: the derivative of the shear map is lower triangular, with first
coordinate the identity and second coordinate the sum of the two partial derivatives of
multiplication. -/
lemma mfderivMultiplicationShear_apply (g h : G)
    (X : TangentSpace I g) (Y : TangentSpace I h) :
    mfderiv% (multiplicationShear : G × G → G × G) (g, h) (X, Y) =
      (X, mfderiv% (fun z : G ↦ z * h) g X + mfderiv% (fun z : G ↦ g * z) h Y) := by
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) (g, h) := by
    -- Smooth multiplication gives the differentiability input for the product derivative formula.
    simpa using
      (show ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * p.2) from
        contMDiff_fst.mul contMDiff_snd).mdifferentiableAt
  have hPair :
      mfderiv% (multiplicationShear : G × G → G × G) (g, h) (X, Y) =
        (mfderiv% (fun p : G × G ↦ p.1) (g, h) (X, Y),
          mfderiv% (fun p : G × G ↦ p.1 * p.2) (g, h) (X, Y)) := by
    -- Differentiate the two coordinates of the shear separately and then evaluate.
    have hderiv :
        mfderiv% (multiplicationShear : G × G → G × G) (g, h) =
          (mfderiv% (fun p : G × G ↦ p.1) (g, h)).prod
            (mfderiv% (fun p : G × G ↦ p.1 * p.2) (g, h)) := by
      simpa [multiplicationShear] using mfderiv_prodMk mdifferentiableAt_fst hMul
    have happly := congrArg (fun F ↦ F (X, Y)) hderiv
    simpa using happly
  have hMulApply :
      mfderiv% (fun p : G × G ↦ p.1 * p.2) (g, h) (X, Y) =
        mfderiv% (fun z : G ↦ z * h) g X + mfderiv% (fun z : G ↦ g * z) h Y :=
    mfderiv_prod_eq_add_apply hMul
  -- Repackage the two coordinate computations into the claimed lower-triangular formula.
  rw [hPair, mfderiv_fst, hMulApply]
  apply Prod.ext <;> rfl

/-- Helper for Problem 7-3: rewrite the derivative of the shear map as a single lower-triangular
continuous linear map. -/
lemma mfderivMultiplicationShear_eq_blockMap (g h : G) :
    mfderiv (I.prod I) (I.prod I) (multiplicationShear : G × G → G × G) (g, h) =
      lowerTriangularProdMap
        (mfderiv I I (fun z : G ↦ z * h) g)
        (mfderiv I I (fun z : G ↦ g * z) h) := by
  -- Compare the two continuous linear maps on an arbitrary tangent pair.
  apply ContinuousLinearMap.ext
  intro u
  rcases u with ⟨X, Y⟩
  have hApply :
      mfderiv% (multiplicationShear : G × G → G × G) (g, h) (X, Y) =
        (X, mfderiv% (fun z : G ↦ z * h) g X + mfderiv% (fun z : G ↦ g * z) h Y) :=
    mfderivMultiplicationShear_apply g h X Y
  simpa using hApply

/-- Helper for Problem 7-3: the derivative of left translation by `g` is invertible at every
point. -/
lemma leftMulMfderivIsInvertible (g h : G) :
    (mfderiv I I (fun z : G ↦ g * z) h).IsInvertible := by
  have hInf : (∞ : ℕ∞ω) ≠ 0 := by simp
  let Φ : G ≃ₘ⟮I, I⟯ G := leftMulDiffeomorph g
  let e := Φ.mfderivToContinuousLinearEquiv hInf h
  -- Differentiate the left-translation diffeomorphism and read off the associated equivalence.
  refine ⟨e, ?_⟩
  simpa [Φ, e] using (Φ.mfderivToContinuousLinearEquiv_coe hInf).symm

/-- Helper for Problem 7-3: the shear derivative is invertible at every point because it is a
lower-triangular block map with invertible left-translation block. -/
lemma mfderivMultiplicationShearIsInvertible (g h : G) :
    (mfderiv (I.prod I) (I.prod I) (multiplicationShear : G × G → G × G) (g, h)).IsInvertible := by
  -- Route correction: rewrite once into the block-map normal form and then apply the generic
  -- lower-triangular invertibility lemma.
  have hBlock :
      mfderiv (I.prod I) (I.prod I) (multiplicationShear : G × G → G × G) (g, h) =
        lowerTriangularProdMap
          (mfderiv I I (fun z : G ↦ z * h) g)
          (mfderiv I I (fun z : G ↦ g * z) h) :=
    mfderivMultiplicationShear_eq_blockMap g h
  rw [hBlock]
  exact lowerTriangularProdMapIsInvertible
    (mfderiv I I (fun z : G ↦ z * h) g)
    (mfderiv I I (fun z : G ↦ g * z) h)
    (leftMulMfderivIsInvertible g h)

/-- Helper for Problem 7-3: the shear map is smooth on `G × G`. -/
lemma multiplicationShear_contMDiff :
    ContMDiff (I.prod I) (I.prod I) ∞ (multiplicationShear : G × G → G × G) := by
  -- Smoothness comes from the first projection together with smooth multiplication.
  simpa [multiplicationShear] using (contMDiff_fst.prodMk (contMDiff_fst.mul contMDiff_snd))

/-- Helper for Problem 7-3: smooth multiplication makes the product manifold `G × G`
boundaryless. -/
lemma boundarylessManifoldProd_of_contMDiffMul :
    BoundarylessManifold (I.prod I) (G × G) := by
  letI : BoundarylessManifold I G := boundarylessManifold_of_contMDiffMul
  infer_instance

/-- Helper for Problem 7-3: the derivative of the shear map is invertible at any chosen point. -/
lemma multiplicationShear_mfderivIsInvertible (p : G × G) :
    (mfderiv (I.prod I) (I.prod I) (multiplicationShear : G × G → G × G) p).IsInvertible := by
  simpa using mfderivMultiplicationShearIsInvertible p.1 p.2

variable [CompleteSpace E]

/-- Helper for Problem 7-3: the shear map is a local diffeomorphism at each point. -/
lemma multiplicationShear_isLocalDiffeomorphAt (p : G × G) :
    IsLocalDiffeomorphAt (I.prod I) (I.prod I) ∞ (multiplicationShear : G × G → G × G) p := by
  letI : BoundarylessManifold (I.prod I) (G × G) := boundarylessManifoldProd_of_contMDiffMul
  -- Route correction: use the boundaryless inverse-function wrapper directly instead of
  -- rebuilding the chart-level local diffeomorphism argument on `G × G`.
  refine isLocalDiffeomorphAt_of_boundaryless_contMDiff_mfderivIsInvertible
    (κ := 𝕜) (K := I.prod I) (M := G × G) (N := G × G)
    (f := multiplicationShear) (p := p)
    ?_ ?_
  · exact multiplicationShear_contMDiff
  · simpa using multiplicationShear_mfderivIsInvertible p

/-- The shear map `(g, h) ↦ (g, gh)` is a smooth local diffeomorphism when multiplication on `G`
is smooth. -/
theorem multiplication_shear_isLocalDiffeomorph :
    IsLocalDiffeomorph (I.prod I) (I.prod I) ∞ (fun p : G × G ↦ (p.1, p.1 * p.2)) := by
  intro p
  simpa [multiplicationShear] using multiplicationShear_isLocalDiffeomorphAt p

/-- Smoothness of multiplication on a smooth manifold group forces smoothness of inversion. -/
theorem contMDiff_inv_of_contMDiff_mul
    [IsManifold I ∞ G] :
    ContMDiff I I ∞ fun g : G ↦ g⁻¹ := by
  classical
  let Φ : (G × G) ≃ₘ⟮I.prod I, I.prod I⟯ (G × G) :=
    multiplication_shear_isLocalDiffeomorph.diffeomorphOfBijective multiplication_shear_bijective
  have hSecondCoord : ∀ g : G, (Φ.symm (g, (1 : G))).2 = g⁻¹ := by
    intro g
    have hApply : Φ (Φ.symm (g, (1 : G))) = (g, (1 : G)) :=
      Φ.apply_symm_apply (g, (1 : G))
    -- Compare the two coordinates of the shear inverse at `(g, 1)`.
    have hfst : (Φ.symm (g, (1 : G))).1 = g := congrArg Prod.fst hApply
    have hsnd : (Φ.symm (g, (1 : G))).1 * (Φ.symm (g, (1 : G))).2 = (1 : G) :=
      congrArg Prod.snd hApply
    rw [hfst] at hsnd
    exact (inv_eq_of_mul_eq_one_right hsnd).symm
  have hSmoothSecond :
      ContMDiff I I ∞ fun g : G ↦ (Φ.symm (g, (1 : G))).2 := by
    have hInput : ContMDiff I (I.prod I) ∞ fun g : G ↦ (g, (1 : G)) := by
      -- The input map to `Φ.symm` is the graph of the constant unit section.
      exact contMDiff_id.prodMk contMDiff_const
    -- Compose the inverse diffeomorphism with the smooth section and project to the second factor.
    exact contMDiff_snd.comp ((Φ.symm.contMDiff_toFun).comp hInput)
  have hInv :
      (fun g : G ↦ (Φ.symm (g, (1 : G))).2) = fun g : G ↦ g⁻¹ := by
    funext g
    exact hSecondCoord g
  simpa [hInv] using hSmoothSecond

/-- Problem 7-3: if `G` is a smooth manifold with a group structure such that multiplication
`G × G → G` is smooth, then `G` is a Lie group. -/
theorem lieGroup_of_contMDiff_mul
    [IsManifold I ∞ G] :
    LieGroup I ∞ G := by
  -- Assemble the Lie-group structure from the given smooth multiplication and the recovered
  -- smooth inversion.
  exact
    { contMDiff_mul := contMDiff_mul I ∞
      contMDiff_inv := contMDiff_inv_of_contMDiff_mul }

end SmoothMultiplication
