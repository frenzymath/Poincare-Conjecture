import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.Sphere
import PetersenLib.Ch04.ComputationalSimplifications

/-!
# Petersen Ch. 4, §4.2.2 — Product spheres

Petersen's product-sphere example `Sⁿ_a × Sᵐ_b := Sⁿ(1/√a) × Sᵐ(1/√b)` with
the metric `g = (1/a) ds²_n + (1/b) ds²_m` for `a, b > 0`.

* `productSphereMetric` — the metric itself: the product of the two round
  unit-sphere metrics of Ch. 1 scaled by `1/a` and `1/b` (positive scaling
  supplied by the helper `smulMetric`); the sphere of radius `1/√a` with its
  induced metric is exactly `(Sⁿ, (1/a) ds²_n)`.
* `productSphereDiagonalization` — pointwise algebra on a single tangent
  space: in an adapted orthonormal basis (index type `ι₁ ⊕ ι₂` split into the
  `Sⁿ`- and `Sᵐ`-factor directions), the hypotheses "each factor block has
  constant curvature (`a`, resp. `b`) and all mixed components vanish" force
  the full Kronecker diagonal form
  `B(e_p,e_q,e_r,e_s) = λ_{pq}(δ_{pr}δ_{qs} − δ_{ps}δ_{qr})`, with
  `λ = productSphereEigenvalue a b`: `a` on pure-`Sⁿ` wedges, `b` on
  pure-`Sᵐ` wedges, `0` on mixed wedges — Petersen's three displayed
  formulas for the curvature operator `𝔊` in component form.
* `productSphereCurvature` — the diagonalization together with the sectional
  curvature bounds `sec ∈ [0, max a b]` for `a, b ≥ 0` (via Prop 4.1.1,
  `secBoundsFromDiagonalCurvatureOperator`).
* `productSphereRicciEinstein` — `Ric = (n−1)a` on the `Sⁿ` block,
  `(m−1)b` on the `Sᵐ` block, `0` off the diagonal;
  `scal = n(n−1)a + m(m−1)b`; and the Einstein criterion
  `Ric = λ·g ↔ (n−1)a = (m−1)b`.

The manifold-level derivation of the block hypotheses — that the curvature
tensor of a Riemannian product whose factors have constant curvature is
block-diagonal in an adapted basis — is upstream of this file; it enters the
algebraic anchors as the hypotheses `hfac1`, `hfac2`, `hmix`. Out of scope
here (noted by Petersen but not formalized): that the curvature tensor is
parallel (`∇R = 0`), and that the product has constant curvature only when
`n = m = 1`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.2.2, p. 136.
-/

open Metric Module
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace PetersenLib

/-! ## The curvature eigenvalues of a product of spheres -/

section Algebraic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι₁ ι₂ : Type*}

/-- **Math.** Petersen §4.2.2: the eigenvalue function of the curvature
operator of `Sⁿ_a × Sᵐ_b` on the basis wedges `e_p ∧ e_q` of an adapted
orthonormal basis: `a` when both indices lie in the `Sⁿ`-factor, `b` when
both lie in the `Sᵐ`-factor, and `0` on mixed wedges. -/
def productSphereEigenvalue (a b : ℝ) : ι₁ ⊕ ι₂ → ι₁ ⊕ ι₂ → ℝ :=
  Sum.elim (fun _ => Sum.elim (fun _ => a) fun _ => 0)
    (fun _ => Sum.elim (fun _ => 0) fun _ => b)

@[simp]
theorem productSphereEigenvalue_inl_inl (a b : ℝ) (i : ι₁) (j : ι₁) :
    productSphereEigenvalue a b (Sum.inl i : ι₁ ⊕ ι₂) (Sum.inl j) = a := rfl

@[simp]
theorem productSphereEigenvalue_inr_inr (a b : ℝ) (i : ι₂) (j : ι₂) :
    productSphereEigenvalue a b (Sum.inr i : ι₁ ⊕ ι₂) (Sum.inr j) = b := rfl

@[simp]
theorem productSphereEigenvalue_inl_inr (a b : ℝ) (i : ι₁) (j : ι₂) :
    productSphereEigenvalue a b (Sum.inl i) (Sum.inr j) = 0 := rfl

@[simp]
theorem productSphereEigenvalue_inr_inl (a b : ℝ) (i : ι₂) (j : ι₁) :
    productSphereEigenvalue a b (Sum.inr i) (Sum.inl j) = 0 := rfl

variable [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Math.** Petersen §4.2.2: on `Sⁿ_a × Sᵐ_b`, the wedges of an adapted
orthonormal basis diagonalize the curvature operator. Hypotheses: each factor
block of the curvature form has the constant-curvature Kronecker shape with
eigenvalue `a` (resp. `b`) — `hfac1`, `hfac2` — and every component with
indices from both factors vanishes (`hmix`); the manifold-level derivation of
these from the product structure is upstream of this file. Conclusion: the
*full* component matrix has the Kronecker diagonal form
`B(e_p,e_q,e_r,e_s) = λ_{pq}(δ_{pr}δ_{qs} − δ_{ps}δ_{qr})` with
`λ = productSphereEigenvalue a b`. The proof is pure case analysis; no
curvature symmetry of `B` is needed. -/
theorem productSphereDiagonalization (e : OrthonormalBasis (ι₁ ⊕ ι₂) ℝ V)
    {B : V → V → V → V → ℝ} (a b : ℝ)
    (hfac1 : ∀ i j k l : ι₁, B (e (.inl i)) (e (.inl j)) (e (.inl k)) (e (.inl l)) =
      a * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hfac2 : ∀ i j k l : ι₂, B (e (.inr i)) (e (.inr j)) (e (.inr k)) (e (.inr l)) =
      b * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ p q r s : ι₁ ⊕ ι₂,
      ¬(p.isLeft = q.isLeft ∧ q.isLeft = r.isLeft ∧ r.isLeft = s.isLeft) →
      B (e p) (e q) (e r) (e s) = 0)
    (p q r s : ι₁ ⊕ ι₂) :
    B (e p) (e q) (e r) (e s) =
      productSphereEigenvalue a b p q *
        ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
          - (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0)) := by
  rcases p with i | i <;> rcases q with j | j <;> rcases r with k | k <;> rcases s with l | l <;>
    first
      | (rw [hfac1 i j k l]; simp)
      | (rw [hfac2 i j k l]; simp)
      | (rw [hmix _ _ _ _ (by simp)]; simp)

/-! ## The anchor theorems -/

/-- **Math.** Petersen §4.2.2 (curvature of `Sⁿ_a × Sᵐ_b`): in an adapted
orthonormal basis the curvature operator `𝔊` is diagonalized by the basis
wedges,

* `𝔊(e_i ∧ e_j) = a · e_i ∧ e_j` for `e_i, e_j` tangent to `Sⁿ_a`,
* `𝔊(v_i ∧ v_j) = b · v_i ∧ v_j` for `v_i, v_j` tangent to `Sᵐ_b`,
* `𝔊(e_i ∧ v_j) = 0` on mixed wedges

(first conjunct: the component form of these three formulas, with the
eigenvalue function `productSphereEigenvalue a b`), and consequently for
`a, b ≥ 0` all sectional curvatures lie in `[0, max a b]` (second conjunct,
by Prop 4.1.1 `secBoundsFromDiagonalCurvatureOperator`). The block
hypotheses `hfac1`, `hfac2`, `hmix` encode the product structure; their
manifold-level derivation is upstream of this file. -/
theorem productSphereCurvature (e : OrthonormalBasis (ι₁ ⊕ ι₂) ℝ V)
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfac1 : ∀ i j k l : ι₁, B (e (.inl i)) (e (.inl j)) (e (.inl k)) (e (.inl l)) =
      a * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hfac2 : ∀ i j k l : ι₂, B (e (.inr i)) (e (.inr j)) (e (.inr k)) (e (.inr l)) =
      b * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ p q r s : ι₁ ⊕ ι₂,
      ¬(p.isLeft = q.isLeft ∧ q.isLeft = r.isLeft ∧ r.isLeft = s.isLeft) →
      B (e p) (e q) (e r) (e s) = 0) :
    (∀ p q r s : ι₁ ⊕ ι₂, B (e p) (e q) (e r) (e s) =
      productSphereEigenvalue a b p q *
        ((if p = r then (1 : ℝ) else 0) * (if q = s then (1 : ℝ) else 0)
          - (if p = s then (1 : ℝ) else 0) * (if q = r then (1 : ℝ) else 0))) ∧
    (∀ v w : V, ⟪v, v⟫ = 1 → ⟪w, w⟫ = 1 → ⟪v, w⟫ = 0 →
      algSectionalCurvature B v w ∈ Set.Icc 0 (max a b)) := by
  have hdiag := productSphereDiagonalization e a b hfac1 hfac2 hmix
  refine ⟨hdiag, fun v w hv hw hvw => ?_⟩
  refine secBoundsFromDiagonalCurvatureOperator hB e hdiag ?_ ?_ hv hw hvw
  · rintro (i | i) (j | j) _
    exacts [ha, le_refl 0, le_refl 0, hb]
  · rintro (i | i) (j | j) _
    exacts [le_max_left a b, le_max_of_le_left ha, le_max_of_le_left ha, le_max_right a b]

/-- **Math.** Petersen §4.2.2 (Ricci and scalar curvature of `Sⁿ_a × Sᵐ_b`,
with `n = card ι₁`, `m = card ι₂`): in an adapted orthonormal basis, tracing
the block-diagonal curvature form gives

* `Ric(X) = (n − 1)a · X` for `X` tangent to `Sⁿ_a` (first conjunct, the
  diagonal Ricci values on the `Sⁿ` block),
* `Ric(V) = (m − 1)b · V` for `V` tangent to `Sᵐ_b` (second conjunct),
* the adapted basis diagonalizes `Ric` (third conjunct, off-diagonal zero,
  via Prop 4.1.3 `ricciDiagonalFromTripleVanishing`),
* `scal = n(n−1)a + m(m−1)b` (fourth conjunct),
* the metric is Einstein — all Ricci eigenvalues equal — iff
  `(n−1)a = (m−1)b` (fifth conjunct; `ι₁, ι₂` nonempty so that both
  eigenvalues actually occur).

The block hypotheses `hfac1`, `hfac2`, `hmix` encode the product structure;
their manifold-level derivation is upstream of this file. -/
theorem productSphereRicciEinstein [FiniteDimensional ℝ V] [Nonempty ι₁] [Nonempty ι₂]
    (e : OrthonormalBasis (ι₁ ⊕ ι₂) ℝ V)
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (a b : ℝ)
    (hfac1 : ∀ i j k l : ι₁, B (e (.inl i)) (e (.inl j)) (e (.inl k)) (e (.inl l)) =
      a * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hfac2 : ∀ i j k l : ι₂, B (e (.inr i)) (e (.inr j)) (e (.inr k)) (e (.inr l)) =
      b * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ p q r s : ι₁ ⊕ ι₂,
      ¬(p.isLeft = q.isLeft ∧ q.isLeft = r.isLeft ∧ r.isLeft = s.isLeft) →
      B (e p) (e q) (e r) (e s) = 0) :
    (∀ i : ι₁, ricciForm hB (e (.inl i)) (e (.inl i)) = ((Fintype.card ι₁ : ℝ) - 1) * a) ∧
    (∀ j : ι₂, ricciForm hB (e (.inr j)) (e (.inr j)) = ((Fintype.card ι₂ : ℝ) - 1) * b) ∧
    (∀ p q : ι₁ ⊕ ι₂, p ≠ q → ricciForm hB (e p) (e q) = 0) ∧
    (algScalarCurvature hB =
      (Fintype.card ι₁ : ℝ) * ((Fintype.card ι₁ : ℝ) - 1) * a
        + (Fintype.card ι₂ : ℝ) * ((Fintype.card ι₂ : ℝ) - 1) * b) ∧
    ((∃ lam0 : ℝ, ∀ p : ι₁ ⊕ ι₂, ricciForm hB (e p) (e p) = lam0) ↔
      ((Fintype.card ι₁ : ℝ) - 1) * a = ((Fintype.card ι₂ : ℝ) - 1) * b) := by
  have hdiag := productSphereDiagonalization e a b hfac1 hfac2 hmix
  -- Ricci diagonal on the `Sⁿ` block: `n − 1` terms of size `a`.
  have hL : ∀ i : ι₁,
      ricciForm hB (e (.inl i)) (e (.inl i)) = ((Fintype.card ι₁ : ℝ) - 1) * a := by
    intro i
    rw [ricciForm_eq_sum hB _ _ e, Fintype.sum_sum_type]
    have h1 : ∀ k : ι₁, B (e (Sum.inl i)) (e (Sum.inl k)) (e (Sum.inl i)) (e (Sum.inl k)) =
        a - (if i = k then a else 0) := by
      intro k
      rw [hdiag]
      rcases eq_or_ne i k with rfl | h
      · simp
      · simp [h, Ne.symm h]
    have h2 : ∀ k : ι₂,
        B (e (Sum.inl i)) (e (Sum.inr k)) (e (Sum.inl i)) (e (Sum.inr k)) = 0 := by
      intro k
      rw [hdiag]
      simp
    simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  -- Ricci diagonal on the `Sᵐ` block: `m − 1` terms of size `b`.
  have hR : ∀ j : ι₂,
      ricciForm hB (e (.inr j)) (e (.inr j)) = ((Fintype.card ι₂ : ℝ) - 1) * b := by
    intro j
    rw [ricciForm_eq_sum hB _ _ e, Fintype.sum_sum_type]
    have h1 : ∀ k : ι₁,
        B (e (Sum.inr j)) (e (Sum.inl k)) (e (Sum.inr j)) (e (Sum.inl k)) = 0 := by
      intro k
      rw [hdiag]
      simp
    have h2 : ∀ k : ι₂, B (e (Sum.inr j)) (e (Sum.inr k)) (e (Sum.inr j)) (e (Sum.inr k)) =
        b - (if j = k then b else 0) := by
      intro k
      rw [hdiag]
      rcases eq_or_ne j k with rfl | h
      · simp
      · simp [h, Ne.symm h]
    simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  -- The adapted basis diagonalizes the Ricci tensor (Prop 4.1.3).
  have hoff : ∀ p q : ι₁ ⊕ ι₂, p ≠ q → ricciForm hB (e p) (e q) = 0 := by
    intro p q hpq
    refine ricciDiagonalFromTripleVanishing hB e ?_ hpq
    intro p' q' r' hpq' hqr' hpr'
    rw [hdiag]
    simp [hpr', hqr', Ne.symm hpq']
  -- Scalar curvature: sum of the Ricci diagonal.
  have hscal : algScalarCurvature hB =
      (Fintype.card ι₁ : ℝ) * ((Fintype.card ι₁ : ℝ) - 1) * a
        + (Fintype.card ι₂ : ℝ) * ((Fintype.card ι₂ : ℝ) - 1) * b := by
    rw [algScalarCurvature_eq_sum_ricci hB e, Fintype.sum_sum_type]
    simp only [hL, hR, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  refine ⟨hL, hR, hoff, hscal, ?_⟩
  constructor
  · -- Einstein forces the two block eigenvalues to agree.
    rintro ⟨lam0, hlam0⟩
    have h1 := hlam0 (Sum.inl (Classical.arbitrary ι₁))
    have h2 := hlam0 (Sum.inr (Classical.arbitrary ι₂))
    rw [hL] at h1
    rw [hR] at h2
    exact h1.trans h2.symm
  · -- Conversely, equal block eigenvalues give a constant Ricci diagonal.
    intro h
    refine ⟨((Fintype.card ι₁ : ℝ) - 1) * a, ?_⟩
    rintro (i | j)
    · exact hL i
    · exact (hR j).trans h.symm

end Algebraic

/-! ## The product-sphere metric -/

section ScaledMetric

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]

/-- **Math.** Scaling a Riemannian metric by a positive constant:
`(c·g)(u, v) = c ⟨u, v⟩_g`. Symmetry and positive-definiteness are inherited
(`c > 0`), boundedness comes from positive-definiteness, and smoothness holds
because a constant scalar multiple of a smooth section of the bilinear-form
bundle is smooth. Petersen §4.2.2 uses the scalings `(1/a) ds²_n`: the round
sphere `Sⁿ(1/√a)` is isometric to `(Sⁿ, (1/a) ds²_n)`. -/
def smulMetric [FiniteDimensional ℝ EM] (c : ℝ) (hc : 0 < c)
    (g : RiemannianMetric IM M) : RiemannianMetric IM M where
  inner x := c • g.inner x
  symm x u v := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.symm x u v]
  pos x u hu := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_pos hc (g.pos x u hu)
  isVonNBounded x := by
    refine isVonNBounded_of_posDef (E := EM) (c • g.inner x) fun u hu => ?_
    exact mul_pos hc (g.pos x u hu)
  contMDiff := ContMDiff.const_smul_section (a := c) g.contMDiff

@[simp]
theorem smulMetric_apply [FiniteDimensional ℝ EM] (c : ℝ) (hc : 0 < c)
    (g : RiemannianMetric IM M) (x : M) (u v : TangentSpace IM x) :
    (smulMetric c hc g).metricInner x u v = c * g.metricInner x u v := rfl

end ScaledMetric

section ProductSphereMetric

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  {n m : ℕ} [Fact (finrank ℝ E₁ = n + 1)] [Fact (finrank ℝ E₂ = m + 1)]

variable (E₁ E₂) in
/-- **Math.** Petersen §4.2.2: the metric of the **product of spheres**
`Sⁿ_a × Sᵐ_b := Sⁿ(1/√a) × Sᵐ(1/√b)`, `a, b > 0`, realized as the product
metric `g = (1/a) ds²_n + (1/b) ds²_m` on `Sⁿ × Sᵐ` — the product of the two
round unit-sphere metrics of Ch. 1 (`sphereMetricUnit`, Example 1.1.3)
scaled by `1/a` and `1/b`. (The sphere of radius `1/√a` with its induced
metric is isometric to the unit sphere with metric `(1/a) ds²_n`, which is
Petersen's own identification.) -/
def productSphereMetric (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    RiemannianMetric ((𝓡 n).prod (𝓡 m)) (sphere (0 : E₁) 1 × sphere (0 : E₂) 1) :=
  productMetric (smulMetric a⁻¹ (inv_pos.mpr ha) (sphereMetricUnit E₁))
    (smulMetric b⁻¹ (inv_pos.mpr hb) (sphereMetricUnit E₂))

/-- **Math.** The product-sphere metric computes as
`⟨u, v⟩ = (1/a) ⟨u₁, v₁⟩_{Sⁿ} + (1/b) ⟨u₂, v₂⟩_{Sᵐ}` on product tangent
vectors. -/
theorem productSphereMetric_apply (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p : sphere (0 : E₁) 1 × sphere (0 : E₂) 1)
    (u v : TangentSpace ((𝓡 n).prod (𝓡 m)) p) :
    (productSphereMetric E₁ E₂ a b ha hb).metricInner p u v =
      a⁻¹ * (sphereMetricUnit E₁).metricInner p.1 u.1 v.1
        + b⁻¹ * (sphereMetricUnit E₂).metricInner p.2 u.2 v.2 := by
  unfold productSphereMetric
  rw [productMetric_apply, smulMetric_apply, smulMetric_apply]

end ProductSphereMetric

end PetersenLib
