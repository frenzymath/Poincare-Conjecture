import PoincareLib.Ch01.JacobiMatrix
import PoincareLib.Ch01.OperatorRiccati
import PoincareLib.Ch01.TraceRiccati
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Morgan–Tian Ch. 1 — the radial shape operator and its Riccati equation

This file supplies the **geometric ↔ analytic keystone** of the comparison
chain of Chapter 1: it identifies the radial shape operator of the geodesic
spheres with `A(r) = 𝒥'(r) 𝒥(r)⁻¹`, where `𝒥` is the matrix Jacobi field of
`lem:geodesic-polar-form`(3), and proves that `A` satisfies the **matrix
Riccati equation**

  `A' + A² + ℛ = 0`

together with the two structural facts that the comparison engines require:
`A(r)` is symmetric (a Wronskian/Lagrange identity), and
`A(r) − (1/r)·Id → 0` as `r → 0⁺`.

Everything is stated in a *parallel orthonormal frame* along a fixed radial
geodesic, exactly as the blueprint proof of `lem:geodesic-polar-form`(2)–(3)
does: the frame identifies the normal bundle along the geodesic with a fixed
real inner product space `E`, turns covariant derivatives along the geodesic
into ordinary derivatives, and turns the Jacobi operator
`X ↦ ℛ(X, γ')γ'` into a curve `ℛ : ℝ → E →L[ℝ] E` of symmetric endomorphisms.

## Why this is the keystone

Both comparison engines already available in this library take *exactly* the
data produced here, and under this identification their curvature hypotheses
become the geometric ones:

* `operator_riccati_le` (blueprint `lem:operator-riccati-upper`) needs
  `⟪A' X, X⟫ ≤ k‖X‖² − ⟪A(A X), X⟫`. Substituting `A' = −ℛ − A²` this is
  *equivalent* to `⟪ℛ(r) X, X⟫ ≥ −k‖X‖²`, i.e. to the **sectional curvature
  lower bound `K ≥ −k`**. This yields the shape-operator half of
  `thm:sectional-curvature-comparison`.
* `trace_riccati_comparison` (blueprint `lem:trace-riccati-comparison`) needs
  `Tr A' + Tr(A²) ≤ m·k`. Substituting `A' = −ℛ − A²` this is *equivalent* to
  `Tr ℛ(r) ≥ −m·k`, i.e. to the **Ricci curvature lower bound
  `Ric(γ',γ') ≥ −(n−1)k`**. This yields `thm:ricci-curvature-comparison` and
  the volume-element bound feeding `thm:bishop-gromov`.

Blueprint: `lem:geodesic-polar-form`(2)(3), `lem:jacobi-matrix-inverse`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The Jacobi ODE on the endomorphism algebra -/

/-- **Math.** The curvature (Jacobi) operator family `ℛ` acting on the Banach
algebra `E →L[ℝ] E` by **left multiplication**, i.e. by composition
`X ↦ ℛ(t) ∘ X`. With this coefficient the pair system of
`PoincareLib.IsJacobiSolOn` is precisely the matrix Jacobi equation
`𝒥'' + ℛ(t) 𝒥 = 0` of `lem:geodesic-polar-form`(3): each *column* of `𝒥` is a
Jacobi field along the radial geodesic. -/
def jacobiOpCoeff (ℛ : ℝ → E →L[ℝ] E) (t : ℝ) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (ℛ t)

@[simp] theorem jacobiOpCoeff_apply (ℛ : ℝ → E →L[ℝ] E) (t : ℝ) (X : E →L[ℝ] E) :
    jacobiOpCoeff ℛ t X = ℛ t * X := rfl

/-- The `jacobiOpCoeff` family is continuous wherever `ℛ` is: it is `ℛ`
followed by the continuous linear map `mul`. -/
theorem continuousOn_jacobiOpCoeff {ℛ : ℝ → E →L[ℝ] E} {s : Set ℝ}
    (hℛ : ContinuousOn ℛ s) : ContinuousOn (jacobiOpCoeff ℛ) s :=
  (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).continuous.comp_continuousOn hℛ

variable [Nontrivial E]

/-- The operator norm of left multiplication by `ℛ t` is exactly `‖ℛ t‖`
(`mul` is a linear isometry on a unital normed algebra). -/
@[simp] theorem norm_jacobiOpCoeff (ℛ : ℝ → E →L[ℝ] E) (t : ℝ) :
    ‖jacobiOpCoeff ℛ t‖ = ‖ℛ t‖ :=
  (ContinuousLinearMap.mulₗᵢ ℝ (E →L[ℝ] E)).norm_map (ℛ t)

/-! ### The radial Jacobi data -/

/-- **Math.** The data of a **radial matrix Jacobi field** in a parallel
orthonormal frame along a unit-speed geodesic `γ`, as set up in the proof of
`lem:geodesic-polar-form`(3):

* `ℛ(r)` is the Jacobi (directional curvature) operator `X ↦ ℛ(X, γ')γ'`
  restricted to `γ'(r)^⊥` and read in the parallel frame — a **symmetric**,
  continuous, bounded family of endomorphisms of `E`;
* `𝒥` is the matrix solution of `𝒥'' + ℛ 𝒥 = 0` with `𝒥(0) = 0`,
  `𝒥'(0) = Id`, so that its columns are the Jacobi fields vanishing at the
  centre `p`, and `𝒥(r)` is the differential `d(exp_p)_{r v}` up to the frame
  identification (`lem:exponential-differential-jacobi`).

`C` is a bound for `‖ℛ‖` on `[0, b]`, used for the small-time asymptotics. -/
structure IsRadialJacobi (ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E) (b C : ℝ) : Prop where
  /-- `𝒥'' + ℛ 𝒥 = 0`, in the first-order pair formulation. -/
  sol : IsJacobiSolOn (jacobiOpCoeff ℛ) 0 b 𝒥 𝒥'
  /-- The Jacobi fields vanish at the centre. -/
  fst_zero : 𝒥 0 = 0
  /-- Unit initial covariant derivative: `𝒥'(0) = Id`. -/
  snd_one : 𝒥' 0 = 1
  /-- The Jacobi operator is symmetric (curvature symmetry `R_{ijkl} = R_{klij}`). -/
  curv_symm : ∀ t ∈ Icc (0 : ℝ) b, ∀ X Y : E, ⟪ℛ t X, Y⟫ = ⟪X, ℛ t Y⟫
  /-- `ℛ` is continuous on `[0, b]`. -/
  curv_cont : ContinuousOn ℛ (Icc (0 : ℝ) b)
  /-- `‖ℛ‖ ≤ C` on `[0, b]`. -/
  curv_bound : ∀ t ∈ Icc (0 : ℝ) b, ‖ℛ t‖ ≤ C

namespace IsRadialJacobi

variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

theorem coeff_cont (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) :
    ContinuousOn (jacobiOpCoeff ℛ) (Icc (0 : ℝ) b) :=
  continuousOn_jacobiOpCoeff h.curv_cont

theorem coeff_bound (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) :
    ∀ t ∈ Icc (0 : ℝ) b, ‖jacobiOpCoeff ℛ t‖ ≤ C := by
  intro t ht
  rw [norm_jacobiOpCoeff]
  exact h.curv_bound t ht

/-- The Morgan–Tian smallness threshold `M = e^{Kb}` with `K = max 1 C`, from
`lem:jacobi-small-time`. -/
def bigM (_h : IsRadialJacobi ℛ 𝒥 𝒥' b C) : ℝ := Real.exp (max 1 C * b)

/-- **Math.** The matrix Jacobi field is invertible for small positive time:
this is `IsJacobiSolOn.isUnit_fst` transported through the frame. Geometrically
it says the radial geodesic has no conjugate point yet, so `exp_p` is
non-singular. Blueprint: `lem:jacobi-matrix-inverse`. -/
theorem isUnit_fst (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) {t : ℝ} (ht : t ∈ Ioc 0 b)
    (hsmall : C * h.bigM * t ^ 2 < 6) : IsUnit (𝒥 t) :=
  h.sol.isUnit_fst h.coeff_cont h.coeff_bound h.fst_zero h.snd_one ht hsmall

end IsRadialJacobi

/-! ### The radial shape operator -/

/-- **Math.** The **radial shape operator** `A(r) = 𝒥'(r) 𝒥(r)⁻¹` of the
geodesic spheres, read in the parallel frame. By `lem:geodesic-polar-form`(2)
it is the `g`-symmetric operator `X ↦ ∇_X ∂_r` associated to the Hessian
`S = Hess(r)` of the radial distance function; the identity `A = 𝒥' 𝒥⁻¹`
holds because `A` maps the polar Jacobi field `J` to `∇_{∂_r} J`, and the
columns of `𝒥` are exactly those Jacobi fields. -/
def shapeOp (𝒥 𝒥' : ℝ → E →L[ℝ] E) (r : ℝ) : E →L[ℝ] E :=
  𝒥' r * Ring.inverse (𝒥 r)

theorem shapeOp_apply (𝒥 𝒥' : ℝ → E →L[ℝ] E) (r : ℝ) (X : E) :
    shapeOp 𝒥 𝒥' r X = 𝒥' r (Ring.inverse (𝒥 r) X) := rfl

variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

/-! #### The Riccati equation -/

/-- **Math.** **The matrix Riccati equation** `A' + A² + ℛ = 0` for the radial
shape operator `A = 𝒥' 𝒥⁻¹` — the analytic form of
`lem:geodesic-polar-form`(2), `∇_{∂_r} A + A² + R_{∂_r} = 0`.

Proof: differentiate `A = 𝒥' · 𝒥⁻¹` by the product rule, using the Jacobi
equation `𝒥'' = −ℛ 𝒥` and the derivative of inversion in a Banach algebra
(`(𝒥⁻¹)' = −𝒥⁻¹ 𝒥' 𝒥⁻¹`):
`A' = 𝒥'' 𝒥⁻¹ + 𝒥' · (−𝒥⁻¹ 𝒥' 𝒥⁻¹) = −ℛ (𝒥 𝒥⁻¹) − (𝒥' 𝒥⁻¹)² = −ℛ − A²`.

Blueprint: `lem:geodesic-polar-form`(2). -/
theorem hasDerivAt_shapeOp (h : IsRadialJacobi ℛ 𝒥 𝒥' b C)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) b) (hu : IsUnit (𝒥 t)) :
    HasDerivAt (shapeOp 𝒥 𝒥')
      (-(ℛ t) - shapeOp 𝒥 𝒥' t * shapeOp 𝒥 𝒥' t) t := by
  have htIcc : Icc (0 : ℝ) b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have htmem : t ∈ Icc (0 : ℝ) b := ⟨ht.1.le, ht.2.le⟩
  -- the two components of the Jacobi system, as honest derivatives at an
  -- interior point
  have hy : HasDerivAt 𝒥 (𝒥' t) t :=
    (h.sol.hasDerivWithinAt_fst t htmem).hasDerivAt htIcc
  have hv : HasDerivAt 𝒥' (-(ℛ t * 𝒥 t)) t := by
    have := (h.sol.hasDerivWithinAt_snd t htmem).hasDerivAt htIcc
    simpa using this
  -- derivative of inversion in the Banach algebra `E →L[ℝ] E`
  have hspec : (hu.unit : E →L[ℝ] E) = 𝒥 t := hu.unit_spec
  have hinvu : Ring.inverse (𝒥 t) = ((hu.unit⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) := by
    have h' := Ring.inverse_unit hu.unit
    rwa [hspec] at h'
  have hinv : HasDerivAt (fun r => Ring.inverse (𝒥 r))
      (-(Ring.inverse (𝒥 t) * 𝒥' t * Ring.inverse (𝒥 t))) t := by
    have hF : HasFDerivAt (Ring.inverse (M₀ := E →L[ℝ] E))
        (-(ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
            ((hu.unit⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E)
            ((hu.unit⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E))) (𝒥 t) := by
      have := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
      rwa [hspec] at this
    have := hF.comp_hasDerivAt t hy
    simpa [Function.comp_def, hinvu, ContinuousLinearMap.mulLeftRight_apply,
      mul_assoc] using this
  -- product rule
  have hA : HasDerivAt (fun r => 𝒥' r * Ring.inverse (𝒥 r))
      (-(ℛ t * 𝒥 t) * Ring.inverse (𝒥 t)
        + 𝒥' t * -(Ring.inverse (𝒥 t) * 𝒥' t * Ring.inverse (𝒥 t))) t := by
    simpa [Pi.mul_def] using hv.mul hinv
  -- algebra: `-(ℛ 𝒥) 𝒥⁻¹ - 𝒥' (𝒥⁻¹ 𝒥' 𝒥⁻¹) = -ℛ - A²`
  have hcancel : 𝒥 t * Ring.inverse (𝒥 t) = 1 := Ring.mul_inverse_cancel _ hu
  -- `-(ℛ 𝒥) 𝒥⁻¹ = -ℛ` (the Jacobi equation, after cancelling `𝒥 𝒥⁻¹ = 1`)
  have e1 : -(ℛ t * 𝒥 t) * Ring.inverse (𝒥 t) = -(ℛ t) := by
    rw [neg_mul, mul_assoc, hcancel, mul_one]
  -- `𝒥' (𝒥⁻¹ 𝒥' 𝒥⁻¹) = A²` (pure associativity)
  have e2 : 𝒥' t * -(Ring.inverse (𝒥 t) * 𝒥' t * Ring.inverse (𝒥 t))
      = -((𝒥' t * Ring.inverse (𝒥 t)) * (𝒥' t * Ring.inverse (𝒥 t))) := by
    noncomm_ring
  have hkey : -(ℛ t * 𝒥 t) * Ring.inverse (𝒥 t)
      + 𝒥' t * -(Ring.inverse (𝒥 t) * 𝒥' t * Ring.inverse (𝒥 t))
      = -(ℛ t) - shapeOp 𝒥 𝒥' t * shapeOp 𝒥 𝒥' t := by
    rw [e1, e2, shapeOp, sub_eq_add_neg]
  rw [shapeOp]
  simpa only [hkey] using hA

/-! #### Symmetry of the shape operator (Wronskian identity) -/

/-- **Math.** **The Wronskian (Lagrange) identity** for the matrix Jacobi
field: `⟪𝒥'(t) a, 𝒥(t) c⟫ = ⟪𝒥(t) a, 𝒥'(t) c⟫` for all `a, c`.

Proof: the scalar `w(t) = ⟪𝒥' a, 𝒥 c⟫ − ⟪𝒥 a, 𝒥' c⟫` has derivative
`⟪−ℛ(𝒥 a), 𝒥 c⟫ + ⟪𝒥' a, 𝒥' c⟫ − ⟪𝒥' a, 𝒥' c⟫ − ⟪𝒥 a, −ℛ(𝒥 c)⟫ = 0`
because `ℛ` is symmetric, and `w(0) = 0` because `𝒥(0) = 0`. So `w ≡ 0`.

This is the reason the shape operator of the geodesic spheres is symmetric,
i.e. that `S = Hess(r)` really is a symmetric two-tensor
(`lem:geodesic-polar-form`(2)); at the level of the curvature tensor it is the
symmetry `R_{ijkl} = R_{klij}` of `claim:curvature-symmetries-bianchi`. -/
theorem wronskian_eq (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) (a c : E) :
    ⟪𝒥' t a, 𝒥 t c⟫ = ⟪𝒥 t a, 𝒥' t c⟫ := by
  set w : ℝ → ℝ := fun r => ⟪𝒥' r a, 𝒥 r c⟫ - ⟪𝒥 r a, 𝒥' r c⟫ with hw
  -- `w` has vanishing derivative on `[0, b]`
  have hderiv : ∀ r ∈ Icc (0 : ℝ) b, HasDerivWithinAt w 0 (Icc (0 : ℝ) b) r := by
    intro r hr
    have hy : HasDerivWithinAt 𝒥 (𝒥' r) (Icc (0 : ℝ) b) r :=
      h.sol.hasDerivWithinAt_fst r hr
    have hv : HasDerivWithinAt 𝒥' (-(ℛ r * 𝒥 r)) (Icc (0 : ℝ) b) r := by
      have := h.sol.hasDerivWithinAt_snd r hr
      simpa using this
    -- the four vector-valued curves
    have hya : HasDerivWithinAt (fun s => 𝒥 s a) (𝒥' r a) (Icc (0 : ℝ) b) r := by
      simpa using hy.clm_apply (hasDerivWithinAt_const r _ a)
    have hyc : HasDerivWithinAt (fun s => 𝒥 s c) (𝒥' r c) (Icc (0 : ℝ) b) r := by
      simpa using hy.clm_apply (hasDerivWithinAt_const r _ c)
    have hva : HasDerivWithinAt (fun s => 𝒥' s a) (-(ℛ r (𝒥 r a))) (Icc (0 : ℝ) b) r := by
      simpa using hv.clm_apply (hasDerivWithinAt_const r _ a)
    have hvc : HasDerivWithinAt (fun s => 𝒥' s c) (-(ℛ r (𝒥 r c))) (Icc (0 : ℝ) b) r := by
      simpa using hv.clm_apply (hasDerivWithinAt_const r _ c)
    -- `w' = ⟪-ℛ(𝒥 a), 𝒥 c⟫ - ⟪𝒥 a, -ℛ(𝒥 c)⟫ = 0` by symmetry of `ℛ`
    -- (the `⟪𝒥' a, 𝒥' c⟫` terms cancel)
    have hsub := (hva.inner ℝ hyc).sub (hya.inner ℝ hvc)
    convert hsub using 1
    have hs := h.curv_symm r hr (𝒥 r a) (𝒥 r c)
    simp only [inner_neg_left, inner_neg_right]
    linarith
  -- hence `w` is constant on `[0, b]`, equal to `w 0 = 0`
  have hdiff : DifferentiableOn ℝ w (Icc (0 : ℝ) b) := fun r hr =>
    (hderiv r hr).differentiableWithinAt
  have huniq : UniqueDiffOn ℝ (Icc (0 : ℝ) b) := uniqueDiffOn_Icc hb
  have hdw : ∀ r ∈ Ico (0 : ℝ) b, derivWithin w (Icc (0 : ℝ) b) r = 0 := by
    intro r hr
    exact (hderiv r ⟨hr.1, hr.2.le⟩).derivWithin (huniq r ⟨hr.1, hr.2.le⟩)
  have hconst := constant_of_derivWithin_zero hdiff hdw t ht
  have hw0 : w 0 = 0 := by simp [hw, h.fst_zero]
  rw [hw0] at hconst
  have hz : ⟪𝒥' t a, 𝒥 t c⟫ - ⟪𝒥 t a, 𝒥' t c⟫ = 0 := hconst
  linarith

/-- **Math.** **The radial shape operator is symmetric.** Substituting
`X = 𝒥(t) a`, `Y = 𝒥(t) c` (legitimate since `𝒥(t)` is invertible) turns the
Wronskian identity into `⟪A X, Y⟫ = ⟪X, A Y⟫`.

This is the hypothesis `hsymm` of `operator_riccati_le` and `hsym` of
`trace_riccati_comparison`. Blueprint: `lem:geodesic-polar-form`(2). -/
theorem shapeOp_symm (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) (hu : IsUnit (𝒥 t)) (X Y : E) :
    ⟪shapeOp 𝒥 𝒥' t X, Y⟫ = ⟪X, shapeOp 𝒥 𝒥' t Y⟫ := by
  have hcancel : 𝒥 t * Ring.inverse (𝒥 t) = 1 := Ring.mul_inverse_cancel _ hu
  have hX : 𝒥 t (Ring.inverse (𝒥 t) X) = X := by
    have := congrArg (fun T : E →L[ℝ] E => T X) hcancel
    simpa using this
  have hY : 𝒥 t (Ring.inverse (𝒥 t) Y) = Y := by
    have := congrArg (fun T : E →L[ℝ] E => T Y) hcancel
    simpa using this
  have hwr := wronskian_eq h hb ht (Ring.inverse (𝒥 t) X) (Ring.inverse (𝒥 t) Y)
  rw [hX, hY] at hwr
  simpa [shapeOp_apply] using hwr

/-! #### Small-time asymptotics `A(r) = (1/r)·Id + O(r)` -/

/-- **Math.** **The asymptotics `A(r) − (1/r)·Id → 0` as `r → 0⁺`** — the
initial condition of the Riccati comparison. It comes from the small-time
expansion `𝒥(r) = r·Id + O(r³)`, `𝒥'(r) = Id + O(r²)` of
`lem:jacobi-small-time`, packaged in `norm_snd_mul_inverse_fst_sub_le` as
`‖A(r) − (1/r)·Id‖ ≤ 2 C M r`.

Geometrically: the geodesic spheres of radius `r` about `p` are, to first
order, round spheres of radius `r`, whose shape operator is `(1/r)·Id`.

This is the hypothesis `h0` of `operator_riccati_le`. Blueprint:
`lem:geodesic-polar-form`(3). -/
theorem tendsto_shapeOp_sub_inv_smul_id (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b) :
    Tendsto (fun r => shapeOp 𝒥 𝒥' r - r⁻¹ • ContinuousLinearMap.id ℝ E)
      (𝓝[>] 0) (𝓝 0) := by
  have hC0 : (0 : ℝ) ≤ C :=
    (norm_nonneg (ℛ 0)).trans (h.curv_bound 0 ⟨le_rfl, hb.le⟩)
  set M : ℝ := h.bigM with hM
  have hM0 : (0 : ℝ) < M := Real.exp_pos _
  -- the quantitative bound holds eventually to the right of `0`
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖shapeOp 𝒥 𝒥' r - r⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ 2 * (C * M) * r := by
    -- the constraints `r ≤ b` and `C M r² ≤ 3` are eventually satisfied
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < b ∧ C * M * r ^ 2 ≤ 3 := by
      have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < b :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hb)
      have hsq : Tendsto (fun r : ℝ => C * M * r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc : Continuous fun r : ℝ => C * M * r ^ 2 :=
          continuous_const.mul (continuous_pow 2)
        have h0 : Tendsto (fun r : ℝ => C * M * r ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
          simpa using hc.tendsto (0 : ℝ)
        exact h0.mono_left nhdsWithin_le_nhds
      have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), C * M * r ^ 2 ≤ 3 := by
        have := hsq.eventually_le_const (by norm_num : (0 : ℝ) < 3)
        exact this
      exact h1.and h2
    filter_upwards [hev, self_mem_nhdsWithin] with r ⟨hrb, hr3⟩ (hr0 : (0 : ℝ) < r)
    have hrIoc : r ∈ Ioc 0 b := ⟨hr0, hrb.le⟩
    have := h.sol.norm_snd_mul_inverse_fst_sub_le h.coeff_cont h.coeff_bound
      h.fst_zero h.snd_one hrIoc (by simpa [hM, IsRadialJacobi.bigM] using hr3)
    have hone : (1 : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := rfl
    simpa [shapeOp, hM, IsRadialJacobi.bigM, hone] using this
  -- squeeze
  refine squeeze_zero_norm' hbound ?_
  have hc : Continuous fun r : ℝ => 2 * (C * M) * r := continuous_const.mul continuous_id
  have h0 : Tendsto (fun r : ℝ => 2 * (C * M) * r) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using hc.tendsto (0 : ℝ)
  exact h0.mono_left nhdsWithin_le_nhds

end PoincareLib

end
