import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Pointwise

/-!
# do Carmo Chapter 6 §3 — immersions into ambients of constant curvature

Specializations of the fundamental equations (`DoCarmoCh6Fundamental`) to an
ambient manifold `(M̄, g)` of **constant sectional curvature** `K₀`
(do Carmo, *Riemannian Geometry*, Ch. 6 §3, Remarks 3.3 and 3.5):

* `AffineConnection.IsConstantCurvature` — the constant-curvature hypothesis in
  do Carmo's Lemma 3.4 form,
  `⟨R̄(X,Y)Z, W⟩ = K₀(⟨X,Z⟩⟨Y,W⟩ − ⟨Y,Z⟩⟨X,W⟩)`;
* the two vanishing pairings it forces on an immersed patch: for tangent
  `X, Y` the form `⟨R̄(X,Y)Z, ζ⟩` dies when the test field `ζ` is normal
  (`curvature_inner_isNormalField_eq_zero`), and `⟨R̄(X,Y)η, W⟩` dies when the
  differentiated field `η` is normal (`curvature_isNormalField_inner_eq_zero`);
* **Remark 3.3**: the Ricci equation reduces to
  `⟨R^⊥(X,Y)η, ζ⟩ = −⟨[S_η, S_ζ]X, Y⟩`
  (`ricci_equation_of_isConstantCurvature`), and the normal bundle is **flat**
  (`R^⊥ ≡ 0`, `HasFlatNormalBundle`) iff at every point the shape operators
  all commute (`hasFlatNormalBundle_iff_shapeOperatorsCommute`);
* **Remark 3.5**: the Codazzi equation reduces to the symmetry
  `(∇̄_X B)(Y, Z, η) = (∇̄_Y B)(X, Z, η)`
  (`codazzi_symm_of_isConstantCurvature`); and for a **hypersurface** — a unit
  normal field `η` spanning every normal space — the normal connection kills
  `η` (`normalCov_eq_zero_of_unit_spanning`) and Codazzi becomes
  `∇_X(S_η Y) − ∇_Y(S_η X) = S_η([X, Y])` (`codazzi_hypersurface`).

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §3, Remarks 3.3 and 3.5.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Ambient manifolds of constant sectional curvature -/

/-- **Math.** do Carmo Ch. 4, Lemma 3.4: an affine connection `∇̄` on `(M̄, g)`
has **constant (sectional) curvature `K₀`** when its curvature 4-form is the
`K₀`-multiple of the model form `R'`,

`⟨R̄(X,Y)Z, W⟩ = K₀ (⟨X,Z⟩⟨Y,W⟩ − ⟨Y,Z⟩⟨X,W⟩)`

at every point — the field-level reading of `K ≡ K₀` (cf. the algebraic model
`stdCurvForm` and `IsAlgCurvatureForm.eq_smul_stdCurvForm_of_const`). -/
def AffineConnection.IsConstantCurvature (nabla : AffineConnection I M)
    (g : RiemannianMetric I M) (K₀ : ℝ) : Prop :=
  ∀ (X Y Z W : SmoothVectorField I M) (p : M),
    g.metricInner p (nabla.curvature X Y Z p) (W p)
      = K₀ * (g.metricInner p (X p) (Z p) * g.metricInner p (Y p) (W p)
          - g.metricInner p (Y p) (Z p) * g.metricInner p (X p) (W p))

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)
variable (nabla : AffineConnection I M)

/-! ### Vanishing pairings of the ambient curvature

In the model form `K₀(⟨X,Z⟩⟨Y,W⟩ − ⟨Y,Z⟩⟨X,W⟩)`, every product dies as soon as
each summand contains a tangent–normal pairing: with `X, Y` tangent this
happens when the test field `W` is normal (kill `⟨Y,W⟩` and `⟨X,W⟩`) and when
the differentiated field `Z` is normal (kill `⟨X,Z⟩` and `⟨Y,Z⟩`). -/

/-- **Math.** In a constant-curvature ambient, `⟨R̄(X,Y)Z, ζ⟩ = 0` for `X, Y`
tangent and the *test field* `ζ` normal (the field `Z` is arbitrary): both
model products contain a tangent–normal pairing against `ζ`. -/
theorem curvature_inner_isNormalField_eq_zero {K₀ : ℝ}
    (hK : nabla.IsConstantCurvature g K₀) (Z : SmoothVectorField I M)
    {X Y ζ : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hζ : D.IsNormalField ζ) (p : M) :
    g.metricInner p (nabla.curvature X Y Z p) (ζ p) = 0 := by
  rw [hK X Y Z ζ p,
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace (hY p) (hζ p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace (hX p) (hζ p)]
  ring

/-- **Math.** In a constant-curvature ambient, `⟨R̄(X,Y)η, W⟩ = 0` for `X, Y`
tangent and the *differentiated field* `η` normal (the test field `W` is
arbitrary): both model products contain a tangent–normal pairing against
`η`. -/
theorem curvature_isNormalField_inner_eq_zero {K₀ : ℝ}
    (hK : nabla.IsConstantCurvature g K₀) (W : SmoothVectorField I M)
    {X Y η : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hη : D.IsNormalField η) (p : M) :
    g.metricInner p (nabla.curvature X Y η p) (W p) = 0 := by
  rw [hK X Y η W p,
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace (hX p) (hη p),
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace (hY p) (hη p)]
  ring

/-! ### Remark 3.3: the Ricci equation in constant curvature -/

/-- **Math.** do Carmo Ch. 6 §3, **Remark 3.3**: in a constant-curvature
ambient the term `⟨R̄(X,Y)η, ζ⟩` of the Ricci equation vanishes, and the Ricci
equation reduces to

`⟨R^⊥(X,Y)η, ζ⟩ = −⟨[S_η, S_ζ]X, Y⟩`,

where `[S_η, S_ζ] = S_η ∘ S_ζ − S_ζ ∘ S_η` is the commutator of the shape
operators. -/
theorem ricci_equation_of_isConstantCurvature (hLC : nabla.IsLeviCivita g)
    {K₀ : ℝ} (hK : nabla.IsConstantCurvature g K₀)
    {X Y η ζ : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hη : D.IsNormalField η)
    (hζ : D.IsNormalField ζ) (p : M) :
    g.metricInner p (D.normalCurvature nabla X Y η p) (ζ p)
      = -g.metricInner p
          ((D.shapeOperator nabla η (D.shapeOperator nabla ζ X)
            - D.shapeOperator nabla ζ (D.shapeOperator nabla η X)) p) (Y p) := by
  have hr := D.ricci_equation nabla hLC X hY hη hζ p
  have h0 := D.curvature_inner_isNormalField_eq_zero nabla hK η hX hY hζ p
  linarith

omit [CompleteSpace E] in
/-- **Math.** Vectors of `(T_pM)^⊥` are separated by their inner products
against `(T_pM)^⊥` (companion of `eq_of_inner_eq_of_mem_tang`): if `u, v` are
normal at `p` and pair equally against every normal vector, then testing
against `u − v` itself gives `⟨u − v, u − v⟩ = 0`, so `u = v` by positive
definiteness. -/
theorem eq_of_inner_eq_of_mem_normalSpace {p : M} {u v : TangentSpace I p}
    (hu : u ∈ D.normalSpace p) (hv : v ∈ D.normalSpace p)
    (h : ∀ w ∈ D.normalSpace p, g.metricInner p u w = g.metricInner p v w) :
    u = v := by
  by_contra hne
  have h0 : g.metricInner p (u - v) (u - v) = 0 := by
    rw [g.metricInner_sub_left, h (u - v) (sub_mem hu hv), sub_self]
  exact absurd h0
    (ne_of_gt (g.metricInner_self_pos p (u - v) (sub_ne_zero.mpr hne)))

/-- **Math.** do Carmo Ch. 6 §3, Remark 3.3: the immersion has **flat normal
bundle** when the normal curvature vanishes identically, `R^⊥(X,Y)η = 0` for
all tangent `X, Y` and normal `η`. -/
def HasFlatNormalBundle : Prop :=
  ∀ X Y η : SmoothVectorField I M, D.IsTangentField X → D.IsTangentField Y →
    D.IsNormalField η → ∀ p : M, D.normalCurvature nabla X Y η p = 0

/-! ### Remark 3.5: the Codazzi equation in constant curvature -/

/-- **Math.** do Carmo Ch. 6 §3, **Remark 3.5** (first part): in a
constant-curvature ambient `⟨R̄(X,Y)Z, η⟩ = 0`, so the Codazzi equation
becomes the symmetry

`(∇̄_X B)(Y, Z, η) = (∇̄_Y B)(X, Z, η)`

of the covariant derivative of the second fundamental tensor in its first two
slots. -/
theorem codazzi_symm_of_isConstantCurvature (hLC : nabla.IsLeviCivita g)
    {K₀ : ℝ} (hK : nabla.IsConstantCurvature g K₀)
    {X Y : SmoothVectorField I M} (Z : SmoothVectorField I M)
    {η : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hη : D.IsNormalField η) (p : M) :
    D.secondFundTensorCovDeriv nabla X Y Z η p
      = D.secondFundTensorCovDeriv nabla Y X Z η p := by
  have hc := D.codazzi_equation nabla hLC Z hX hY hη p
  have h0 := D.curvature_inner_isNormalField_eq_zero nabla hK Z hX hY hη p
  linarith

/-! ### Hypersurfaces: the normal connection of a unit normal field -/

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6 §3, Remark 3.5: for a codimension-one immersion
with a **unit** normal field `η` spanning every normal space,
`∇^⊥_X η = 0` for every `X`: differentiating `⟨η, η⟩ ≡ 1` gives
`⟨∇̄_X η, η⟩ = 0` by compatibility; the shape-operator part of `∇̄_X η` is
orthogonal to `η` anyway, so `∇^⊥_X η ⊥ η` — but `∇^⊥_X η` is a multiple of
`η`, hence zero. -/
theorem normalCov_eq_zero_of_unit_spanning (hcompat : nabla.IsMetricCompatible g)
    {η : SmoothVectorField I M} (hη : D.IsNormalField η)
    (hunit : ∀ q : M, g.metricInner q (η q) (η q) = 1)
    (hspan : ∀ q : M, ∀ w ∈ D.normalSpace q, ∃ c : ℝ, w = c • η q)
    (X : SmoothVectorField I M) (p : M) :
    D.normalCov nabla X η p = 0 := by
  -- `X⟨η, η⟩ = 0` since `⟨η, η⟩` is the constant function `1`
  have hone : (fun q => g.metricInner q (η q) (η q)) = fun _ => (1 : ℝ) :=
    funext hunit
  have hdir : X.dir (fun q => g.metricInner q (η q) (η q)) p = 0 := by
    rw [hone]
    simp only [SmoothVectorField.dir, mfderiv_const]
    rfl
  -- compatibility: `⟨∇̄_X η, η⟩ = 0`
  have hc := hcompat X η η p
  rw [hdir, g.metricInner_comm p (η p) (nabla.cov X η p)] at hc
  have hcov : g.metricInner p (nabla.cov X η p) (η p) = 0 := by linarith
  -- split off the (tangent) shape-operator part: `⟨∇^⊥_X η, η⟩ = 0`
  have hsplit := congrArg (fun F : SmoothVectorField I M => F p)
    (D.cov_eq_neg_shapeOperator_add_normalCov nabla X η)
  simp only [SmoothVectorField.add_apply, SmoothVectorField.neg_apply] at hsplit
  rw [hsplit, g.metricInner_add_left, g.metricInner_neg_left,
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace
      (D.shapeOperator_mem nabla η X p) (hη p), neg_zero, zero_add] at hcov
  -- `∇^⊥_X η (p)` is a multiple of `η(p)`; its coefficient dies
  obtain ⟨c, hcw⟩ := hspan p _ (D.normalCov_mem nabla X η p)
  rw [hcw, g.metricInner_smul_left, hunit p, mul_one] at hcov
  rw [hcw, hcov, zero_smul]

omit [CompleteSpace E] in
/-- **Math.** `S_0 = 0`: the shape operator along the zero normal field
vanishes. -/
theorem shapeOperator_zero_left (X : SmoothVectorField I M) (p : M) :
    D.shapeOperator nabla 0 X p = 0 := by
  have h0 : nabla.cov X (0 : SmoothVectorField I M) p
      = (0 : SmoothVectorField I M) p := by
    rw [SmoothVectorField.zero_apply]
    exact nabla.cov_zero_right X p
  rw [shapeOperator, SmoothVectorField.neg_apply, D.tangentProj_congr_apply h0,
    D.tangentProj_zero, SmoothVectorField.zero_apply, neg_zero]

/-- **Math.** do Carmo Ch. 6 §3, **Remark 3.5** (hypersurfaces), scalar form:
for a unit spanning normal field `η` in a constant-curvature ambient,

`⟨∇_X(S_η Y) − ∇_Y(S_η X), Z⟩ = ⟨S_η([X, Y]), Z⟩`

for tangent `X, Y, Z`. Pairing the normal decomposition of `R̄(X,Y)η` with the
tangent field `Z` kills the normal terms; the `S_{∇^⊥η}` terms die because
`∇^⊥ η = 0` (`normalCov_eq_zero_of_unit_spanning`), and `⟨R̄(X,Y)η, Z⟩ = 0` by
constant curvature. -/
theorem codazzi_hypersurface_inner (hcompat : nabla.IsMetricCompatible g)
    {K₀ : ℝ} (hK : nabla.IsConstantCurvature g K₀)
    {η : SmoothVectorField I M} (hη : D.IsNormalField η)
    (hunit : ∀ q : M, g.metricInner q (η q) (η q) = 1)
    (hspan : ∀ q : M, ∀ w ∈ D.normalSpace q, ∃ c : ℝ, w = c • η q)
    {X Y Z : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hZ : D.IsTangentField Z) (p : M) :
    g.metricInner p
        (D.inducedCov nabla X (D.shapeOperator nabla η Y) p
          - D.inducedCov nabla Y (D.shapeOperator nabla η X) p) (Z p)
      = g.metricInner p (D.shapeOperator nabla η (bracketField X Y) p) (Z p) := by
  -- `∇^⊥ η` vanishes as a field in both directions
  have hzX : D.normalCov nabla X η = 0 := SmoothVectorField.ext fun q => by
    rw [SmoothVectorField.zero_apply]
    exact D.normalCov_eq_zero_of_unit_spanning nabla hcompat hη hunit hspan X q
  have hzY : D.normalCov nabla Y η = 0 := SmoothVectorField.ext fun q => by
    rw [SmoothVectorField.zero_apply]
    exact D.normalCov_eq_zero_of_unit_spanning nabla hcompat hη hunit hspan Y q
  -- pair the normal decomposition of `R̄(X,Y)η` with `Z`
  have hpair := congrArg (fun v => g.metricInner p v (Z p))
    (D.curvature_normal_decomposition nabla X Y η p)
  simp only [g.metricInner_add_left, g.metricInner_sub_left] at hpair
  have h₁ : g.metricInner p (nabla.curvature X Y η p) (Z p) = 0 :=
    D.curvature_isNormalField_inner_eq_zero nabla hK Z hX hY hη p
  have h₂ : g.metricInner p (D.normalCurvature nabla X Y η p) (Z p) = 0 :=
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.normalCurvature_mem nabla X Y η p) (hZ p)
  have h₃ : g.metricInner p
      (D.shapeOperator nabla (D.normalCov nabla X η) Y p) (Z p) = 0 := by
    rw [hzX, D.shapeOperator_zero_left nabla Y p, g.metricInner_zero_left]
  have h₄ : g.metricInner p
      (D.shapeOperator nabla (D.normalCov nabla Y η) X p) (Z p) = 0 := by
    rw [hzY, D.shapeOperator_zero_left nabla X p, g.metricInner_zero_left]
  have h₅ : g.metricInner p
      (D.secondFundForm nabla Y (D.shapeOperator nabla η X) p) (Z p) = 0 :=
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.secondFundForm_mem nabla Y (D.shapeOperator nabla η X) p) (hZ p)
  have h₆ : g.metricInner p
      (D.secondFundForm nabla X (D.shapeOperator nabla η Y) p) (Z p) = 0 :=
    D.inner_eq_zero_of_mem_normalSpace_of_mem_tang
      (D.secondFundForm_mem nabla X (D.shapeOperator nabla η Y) p) (hZ p)
  rw [g.metricInner_sub_left]
  linarith [hpair, h₁, h₂, h₃, h₄, h₅, h₆]

/-! ### The pointwise statements: flat normal bundle ⟺ commuting shape
operators, and the hypersurface Codazzi identity -/

section Pointwise

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** do Carmo Ch. 6 §3, Remark 3.3: the shape operators of the
immersion **commute at `p`** when `S_η ∘ S_ζ = S_ζ ∘ S_η` on `T_pM` for all
normal vectors `η, ζ ∈ (T_pM)^⊥`. -/
def ShapeOperatorsCommuteAt (p : M) : Prop :=
  ∀ η ∈ D.normalSpace p, ∀ ζ ∈ D.normalSpace p, ∀ x ∈ D.tang p,
    D.shapeOperatorAt nabla p η (D.shapeOperatorAt nabla p ζ x)
      = D.shapeOperatorAt nabla p ζ (D.shapeOperatorAt nabla p η x)

omit [CompleteSpace E] in
/-- **Math.** Bridging the field-level and the pointwise composed shape
operators: if the normal fields `N, Z` extend the normal vectors `η, ζ` at
`p`, then `S_N(S_Z X)(p) = S_η(S_ζ(X(p)))` — both compositions are computed by
(any) extensions, by do Carmo's Prop. 2.3 applied twice. -/
theorem shapeOperator_shapeOperator_apply (hcompat : nabla.IsMetricCompatible g)
    {p : M} {η ζ : TangentSpace I p} (hη : η ∈ D.normalSpace p)
    (hζ : ζ ∈ D.normalSpace p) {N Z : SmoothVectorField I M}
    (hN : D.IsNormalField N) (hNp : N p = η) (hZ : D.IsNormalField Z)
    (hZp : Z p = ζ) (X : SmoothVectorField I M) :
    D.shapeOperator nabla N (D.shapeOperator nabla Z X) p
      = D.shapeOperatorAt nabla p η (D.shapeOperatorAt nabla p ζ (X p)) := by
  rw [D.shapeOperatorAt_eq_shapeOperator nabla hcompat hζ hZ hZp X,
    D.shapeOperatorAt_eq_shapeOperator nabla hcompat hη hN hNp
      (D.shapeOperator nabla Z X)]

/-- **Math.** do Carmo Ch. 6 §3, **Remark 3.3**: in a constant-curvature
ambient the normal bundle of the immersion is **flat** (`R^⊥ ≡ 0`) **iff** at
every point all shape operators commute — by the reduced Ricci equation
`⟨R^⊥(X,Y)η, ζ⟩ = −⟨[S_η, S_ζ]X, Y⟩`, separating over tangent test vectors in
one direction and over normal test vectors in the other. -/
theorem hasFlatNormalBundle_iff_shapeOperatorsCommute (hLC : nabla.IsLeviCivita g)
    {K₀ : ℝ} (hK : nabla.IsConstantCurvature g K₀) :
    D.HasFlatNormalBundle nabla ↔ ∀ p : M, D.ShapeOperatorsCommuteAt nabla p := by
  constructor
  · intro hflat p η hη ζ hζ x hx
    obtain ⟨N, hN, hNp⟩ := D.exists_isNormalField_eq p hη
    obtain ⟨Z, hZ, hZp⟩ := D.exists_isNormalField_eq p hζ
    obtain ⟨X, hX, hXp⟩ := D.exists_isTangentField_eq p hx
    have hb₁ : D.shapeOperatorAt nabla p η (D.shapeOperatorAt nabla p ζ x)
        = D.shapeOperator nabla N (D.shapeOperator nabla Z X) p := by
      rw [← hXp]
      exact (D.shapeOperator_shapeOperator_apply nabla hLC.2 hη hζ hN hNp hZ
        hZp X).symm
    have hb₂ : D.shapeOperatorAt nabla p ζ (D.shapeOperatorAt nabla p η x)
        = D.shapeOperator nabla Z (D.shapeOperator nabla N X) p := by
      rw [← hXp]
      exact (D.shapeOperator_shapeOperator_apply nabla hLC.2 hζ hη hZ hZp hN
        hNp X).symm
    rw [hb₁, hb₂]
    refine D.eq_of_inner_eq_of_mem_tang (D.shapeOperator_mem nabla N _ p)
      (D.shapeOperator_mem nabla Z _ p) fun w hw => ?_
    obtain ⟨W, hWt, hWp⟩ := D.exists_isTangentField_eq p hw
    have hric := D.ricci_equation_of_isConstantCurvature nabla hLC hK hX hWt
      hN hZ p
    rw [hflat X W N hX hWt hN p, g.metricInner_zero_left,
      SmoothVectorField.sub_apply, g.metricInner_sub_left] at hric
    rw [← hWp]
    linarith
  · intro hcomm X Y η hX hY hη p
    refine D.eq_of_inner_eq_of_mem_normalSpace
      (D.normalCurvature_mem nabla X Y η p) (zero_mem _) fun w hw => ?_
    obtain ⟨Z, hZ, hZp⟩ := D.exists_isNormalField_eq p hw
    have hric := D.ricci_equation_of_isConstantCurvature nabla hLC hK hX hY
      hη hZ p
    have hb : D.shapeOperator nabla η (D.shapeOperator nabla Z X) p
        = D.shapeOperator nabla Z (D.shapeOperator nabla η X) p := by
      rw [D.shapeOperator_shapeOperator_apply nabla hLC.2 (hη p) hw hη rfl
          hZ hZp X,
        D.shapeOperator_shapeOperator_apply nabla hLC.2 hw (hη p) hZ hZp
          hη rfl X]
      exact hcomm p (η p) (hη p) w hw (X p) (hX p)
    rw [SmoothVectorField.sub_apply, g.metricInner_sub_left, hb, sub_self,
      neg_zero] at hric
    rw [← hZp, g.metricInner_zero_left]
    exact hric

/-- **Math.** do Carmo Ch. 6 §3, **Remark 3.5** (hypersurfaces): for a
codimension-one immersion with unit normal field `η` in a constant-curvature
ambient, the Codazzi equation takes the classical form

`∇_X(S_η Y) − ∇_Y(S_η X) = S_η([X, Y])`

for tangent `X, Y` — separate the scalar identity
(`codazzi_hypersurface_inner`) over tangent test vectors. -/
theorem codazzi_hypersurface (hcompat : nabla.IsMetricCompatible g)
    {K₀ : ℝ} (hK : nabla.IsConstantCurvature g K₀)
    {η : SmoothVectorField I M} (hη : D.IsNormalField η)
    (hunit : ∀ q : M, g.metricInner q (η q) (η q) = 1)
    (hspan : ∀ q : M, ∀ w ∈ D.normalSpace q, ∃ c : ℝ, w = c • η q)
    {X Y : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (p : M) :
    D.inducedCov nabla X (D.shapeOperator nabla η Y) p
      - D.inducedCov nabla Y (D.shapeOperator nabla η X) p
      = D.shapeOperator nabla η (bracketField X Y) p := by
  refine D.eq_of_inner_eq_of_mem_tang
    (sub_mem (D.isTangentField_inducedCov nabla X _ p)
      (D.isTangentField_inducedCov nabla Y _ p))
    (D.shapeOperator_mem nabla η (bracketField X Y) p) fun w hw => ?_
  obtain ⟨Z, hZ, hZp⟩ := D.exists_isTangentField_eq p hw
  rw [← hZp]
  exact D.codazzi_hypersurface_inner nabla hcompat hK hη hunit hspan hX hY hZ p

end Pointwise

end DCImmersedPatch

end Riemannian
