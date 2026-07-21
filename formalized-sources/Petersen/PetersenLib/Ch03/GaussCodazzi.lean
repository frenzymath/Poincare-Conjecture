import PetersenLib.Ch03.SecondFundamentalForm

/-!
# Petersen Ch. 3, §3.2.1 — The Gauss and Peterson–Codazzi–Mainardi equations

The **tangential connection** of a hypersurface with unit normal `N` —
`∇^H_v Z = (∇_v Z)^⊤ = ∇_v Z − g(∇_v Z, N)N` (`tangentialCov`,
`tangentialCovField`) — and its curvature `R^H`
(`tangentialCurvatureTensor`); the covariant derivative of the second
fundamental form along the hypersurface
(`secondFundamentalFormCovariantDerivative`); **Theorem 3.2.4** — the
tangential (Gauss) curvature equation
`g(R(X,Y)Z,W) = g(R^H(X,Y)Z,W) − Π(X,W)Π(Y,Z) + Π(X,Z)Π(Y,W)`
(`tangentialCurvatureEquation`); **Theorem 3.2.5** — the normal
(Peterson–Codazzi–Mainardi) curvature equation
`g(R(X,Y)Z,N) = −(∇_XΠ)(Y,Z) + (∇_YΠ)(X,Z)` (`normalCurvatureEquation`); and
**Gauss's Theorema Egregium** (`gaussTheoremaEgregium`).

## Design notes

* As in `SecondFundamentalForm.lean`, the hypersurface enters through a unit
  normal field `N` on an open set `U`; fields tangent to the hypersurface are
  ambient fields `Z` with `g(Z,N) ≡ 0` on `U`. The induced objects `∇^H`,
  `R^H`, `∇Π` are built from the ambient connection by tangential projection,
  so no submanifold layer is required; on a genuine hypersurface they agree
  with the intrinsic ones by uniqueness of the Riemannian connection.
* The Gauss equation needs `Z` tangent on `U` and `W` tangent at `p` only;
  the Codazzi equation needs `Z` tangent on `U` and the bracket `[X,Y]`
  tangent at `p` (automatic for level sets, `bracket_tangent_levelSet`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2.1.
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The tangential connection -/

/-- **Math.** The **tangential connection** of a hypersurface with unit normal
`N` (Petersen §3.2.1): `∇^H_v Z = (∇_v Z)^⊤ = ∇_v Z − g(∇_v Z, N)N`. On fields
tangent to the hypersurface this is the Riemannian connection of the induced
metric (by uniqueness, via the Koszul formula). -/
def tangentialCov (D : AffineConnection I M) (g : RiemannianMetric I M)
    (N : Π x : M, TangentSpace I x) (p : M) (v : TangentSpace I p)
    (Z : Π x : M, TangentSpace I x) : TangentSpace I p :=
  D.cov p v Z - g.metricInner p (D.cov p v Z) (N p) • N p

theorem tangentialCov_apply (D : AffineConnection I M) (g : RiemannianMetric I M)
    (N : Π x : M, TangentSpace I x) (p : M) (v : TangentSpace I p)
    (Z : Π x : M, TangentSpace I x) :
    tangentialCov D g N p v Z
      = D.cov p v Z - g.metricInner p (D.cov p v Z) (N p) • N p := rfl

/-- The tangential covariant derivative along a field, as a field. -/
def tangentialCovField (D : AffineConnection I M) (g : RiemannianMetric I M)
    (N Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun q => tangentialCov D g N q (Y q) Z

@[simp]
theorem tangentialCovField_apply (D : AffineConnection I M)
    (g : RiemannianMetric I M) (N Y Z : Π x : M, TangentSpace I x) (q : M) :
    tangentialCovField D g N Y Z q = tangentialCov D g N q (Y q) Z := rfl

/-- Pairing against a vector orthogonal to `N` does not see the tangential
projection: `g(∇^H_v Z, w) = g(∇_v Z, w)` when `w ⊥ N_p`. -/
theorem tangentialCov_metricInner_of_orthogonal (D : AffineConnection I M)
    (g : RiemannianMetric I M) (N : Π x : M, TangentSpace I x) (p : M)
    (v : TangentSpace I p) (Z : Π x : M, TangentSpace I x)
    {w : TangentSpace I p} (hw : g.metricInner p w (N p) = 0) :
    g.metricInner p (tangentialCov D g N p v Z) w
      = g.metricInner p (D.cov p v Z) w := by
  rw [tangentialCov_apply, g.metricInner_sub_left, g.metricInner_smul_left]
  have hcomm : g.metricInner p (N p) w = g.metricInner p w (N p) :=
    g.metricInner_comm ..
  rw [hcomm, hw]
  ring

/-- The normal coefficient of `∇_Y Z`, as a function on `M`. -/
def normalCoefficient (D : AffineConnection I M) (g : RiemannianMetric I M)
    (N Y Z : Π x : M, TangentSpace I x) : M → ℝ :=
  fun q => g.metricInner q (D.cov q (Y q) Z) (N q)

/-- `∇_Y Z` splits into its tangential part and its normal coefficient. -/
theorem covField_eq_tangential_add_normal (D : AffineConnection I M)
    (g : RiemannianMetric I M) (N Y Z : Π x : M, TangentSpace I x) :
    D.covField Y Z = fun q => tangentialCovField D g N Y Z q
      + normalCoefficient D g N Y Z q • N q := by
  funext q
  simp [tangentialCovField, tangentialCov, normalCoefficient]

section Smoothness

/-- Smoothness of the normal coefficient. -/
theorem contMDiff_normalCoefficient {g : RiemannianMetric I M}
    (D : AffineConnection I M) {N Y Z : Π x : M, TangentSpace I x}
    (hN : IsSmoothVectorField N) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) :
    ContMDiff I 𝓘(ℝ) ∞ (normalCoefficient D g N Y Z) := by
  have hcov : IsSmoothVectorField (D.covField Y Z) := D.smooth_cov hY hZ
  have h := (metricOperator_isTensorOperator g).smooth_eval ![D.covField Y Z, N]
    (by
      intro i
      fin_cases i
      · simpa using hcov
      · simpa using hN)
  have e : (metricOperator g ![D.covField Y Z, N] : M → ℝ)
      = normalCoefficient D g N Y Z := by
    funext q; simp [metricOperator, normalCoefficient]
  rwa [e] at h

/-- Smoothness of the tangential covariant derivative field. -/
theorem isSmoothVectorField_tangentialCovField {g : RiemannianMetric I M}
    (D : AffineConnection I M) {N Y Z : Π x : M, TangentSpace I x}
    (hN : IsSmoothVectorField N) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) :
    IsSmoothVectorField (tangentialCovField D g N Y Z) := by
  have hcov : IsSmoothVectorField (D.covField Y Z) := D.smooth_cov hY hZ
  have hcoeff := contMDiff_normalCoefficient (g := g) D hN hY hZ
  have hsmul : IsSmoothVectorField
      (fun q => normalCoefficient D g N Y Z q • N q) := by
    simpa using
      (SmoothVectorField.smul (normalCoefficient D g N Y Z) hcoeff ⟨N, hN⟩).smooth
  have hsub := ((⟨_, hcov⟩ : SmoothVectorField I M) - ⟨_, hsmul⟩).smooth
  have e : (fun q => D.covField Y Z q
        - normalCoefficient D g N Y Z q • N q)
      = tangentialCovField D g N Y Z := by
    funext q; simp [tangentialCovField, tangentialCov, normalCoefficient]
  rw [← e]
  simpa using hsub

end Smoothness

/-! ## The induced (tangential) curvature -/

/-- **Math.** The **curvature of the tangential connection** (Petersen §3.2.1):
`R^H(X,Y)Z = ∇^H_X∇^H_YZ − ∇^H_Y∇^H_XZ − ∇^H_{[X,Y]}Z`, the curvature tensor
of the hypersurface built from the tangential projection of the ambient
connection. -/
def tangentialCurvatureTensor (D : AffineConnection I M)
    (g : RiemannianMetric I M) (N X Y Z : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun p => tangentialCov D g N p (X p) (tangentialCovField D g N Y Z)
    - tangentialCov D g N p (Y p) (tangentialCovField D g N X Z)
    - tangentialCov D g N p (lieDerivativeVectorField I X Y p) Z

theorem tangentialCurvatureTensor_apply (D : AffineConnection I M)
    (g : RiemannianMetric I M) (N X Y Z : Π x : M, TangentSpace I x) (p : M) :
    tangentialCurvatureTensor D g N X Y Z p
      = tangentialCov D g N p (X p) (tangentialCovField D g N Y Z)
        - tangentialCov D g N p (Y p) (tangentialCovField D g N X Z)
        - tangentialCov D g N p (lieDerivativeVectorField I X Y p) Z := rfl

/-! ## The normal coefficient against the second fundamental form -/

section NormalCoefficient

/-- **Math.** For `Z` tangent to the hypersurface, the normal coefficient of
`∇_V Z` is `−Π(V,Z)`: differentiating `g(Z,N) ≡ 0` gives
`g(∇_V Z, N) = −g(Z, ∇_V N) = −Π(V,Z)` on `U`. -/
theorem normalCoefficient_eq_neg_secondFundamentalForm
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) {U : Set M}
    (hU : IsOpen U) {N Z : Π x : M, TangentSpace I x}
    (hN : IsSmoothVectorField N) (hZ : IsSmoothVectorField Z)
    (hZtan : ∀ q ∈ U, g.metricInner q (Z q) (N q) = 0)
    (V : Π x : M, TangentSpace I x) {q : M} (hq : q ∈ U) :
    normalCoefficient D.toAffineConnection g N V Z q
      = -secondFundamentalForm D.toAffineConnection g N V Z q := by
  have hcompat := D.metric_compat hZ hN q (V q)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  have hloc : (fun x => g.metricInner x (Z x) (N x)) =ᶠ[𝓝 q]
      fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hq] with x hx
    exact hZtan x hx
  have hdd : directionalDerivative V
      (fun x => g.metricInner x (Z x) (N x)) q = 0 := by
    rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]
    rfl
  rw [hdd] at hcompat
  have hcomm : g.metricInner q (Z q) (D.cov q (V q) N)
      = g.metricInner q (D.cov q (V q) N) (Z q) := g.metricInner_comm ..
  rw [hcomm] at hcompat
  rw [normalCoefficient, secondFundamentalForm_apply]
  linarith [hcompat]

end NormalCoefficient

/-! ## Theorem 3.2.4 — the tangential (Gauss) curvature equation -/

section GaussEquation

/-- **Eng.** The key expansion for both curvature equations: pairing
`∇_X(∇_Y Z)` against a vector `w ⊥ N_p` splits it into the tangential
second derivative and one `Π·Π` correction,
`g(∇_X(∇_Y Z), w) = g(∇^H_X(∇^H_Y Z), w) + normalCoefficient(Y,Z)(p)·g(∇_X N, w)`. -/
private theorem cov_cov_metricInner_split {g : RiemannianMetric I M}
    (D : RiemannianConnection I g)
    {N X Y Z : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (p : M) {w : TangentSpace I p} (hw : g.metricInner p w (N p) = 0) :
    g.metricInner p (D.cov p (X p) (D.toAffineConnection.covField Y Z)) w
      = g.metricInner p
          (tangentialCov D.toAffineConnection g N p (X p)
            (tangentialCovField D.toAffineConnection g N Y Z)) w
        + normalCoefficient D.toAffineConnection g N Y Z p
          * g.metricInner p (D.cov p (X p) N) w := by
  have htcf : IsSmoothVectorField
      (tangentialCovField D.toAffineConnection g N Y Z) :=
    isSmoothVectorField_tangentialCovField D.toAffineConnection hN hY hZ
  have hcoeff := contMDiff_normalCoefficient (g := g) D.toAffineConnection hN hY hZ
  have hsmul : IsSmoothVectorField
      (fun q => normalCoefficient D.toAffineConnection g N Y Z q • N q) := by
    simpa using (SmoothVectorField.smul
      (normalCoefficient D.toAffineConnection g N Y Z) hcoeff ⟨N, hN⟩).smooth
  -- split `∇_Y Z` into tangential + normal parts and differentiate
  have hsplit : D.cov p (X p) (D.toAffineConnection.covField Y Z)
      = D.cov p (X p) (tangentialCovField D.toAffineConnection g N Y Z)
        + D.cov p (X p)
            (fun q => normalCoefficient D.toAffineConnection g N Y Z q • N q) := by
    rw [covField_eq_tangential_add_normal D.toAffineConnection g N Y Z]
    exact D.toAffineConnection.add_field p (X p) htcf hsmul
  -- Leibniz on the normal part
  have hleib := D.toAffineConnection.leibniz p (X p) hcoeff hN
  rw [hsplit, hleib, g.metricInner_add_left, g.metricInner_add_left,
    g.metricInner_smul_left, g.metricInner_smul_left]
  have hcomm : g.metricInner p (N p) w = g.metricInner p w (N p) :=
    g.metricInner_comm ..
  rw [hcomm, hw,
    tangentialCov_metricInner_of_orthogonal D.toAffineConnection g N p (X p)
      (tangentialCovField D.toAffineConnection g N Y Z) hw]
  ring

/-- **Math.** **Theorem 3.2.4 — the tangential (Gauss) curvature equation**
(Petersen, `thm:pet-ch3-tangential-curvature-equation`): for `Z` tangent to
the hypersurface on `U` and `W` tangent at `p ∈ U`,
`g(R(X,Y)Z, W) = g(R^H(X,Y)Z, W) − Π(X,W)Π(Y,Z) + Π(X,Z)Π(Y,W)`. -/
theorem tangentialCurvatureEquation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U)
    {N X Y Z W : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z)
    (hZtan : ∀ q ∈ U, g.metricInner q (Z q) (N q) = 0)
    {p : M} (hp : p ∈ U) (hW : g.metricInner p (W p) (N p) = 0) :
    curvatureTensorFour D X Y Z W p
      = g.metricInner p
          (tangentialCurvatureTensor D.toAffineConnection g N X Y Z p) (W p)
        - secondFundamentalForm D.toAffineConnection g N X W p
          * secondFundamentalForm D.toAffineConnection g N Y Z p
        + secondFundamentalForm D.toAffineConnection g N X Z p
          * secondFundamentalForm D.toAffineConnection g N Y W p := by
  -- expand `g(R(X,Y)Z, W)` term by term
  have h₁ := cov_cov_metricInner_split D (X := X) hN hY hZ p hW
  have h₂ := cov_cov_metricInner_split D (X := Y) hN hX hZ p hW
  have h₃ := tangentialCov_metricInner_of_orthogonal D.toAffineConnection g N p
    (lieDerivativeVectorField I X Y p) Z hW
  -- identify the normal coefficients with `−Π`
  have hcY := normalCoefficient_eq_neg_secondFundamentalForm D hU hN hZ hZtan Y hp
  have hcX := normalCoefficient_eq_neg_secondFundamentalForm D hU hN hZ hZtan X hp
  rw [curvatureTensorFour_apply, curvatureTensor_apply,
    tangentialCurvatureTensor_apply, g.metricInner_sub_left,
    g.metricInner_sub_left, g.metricInner_sub_left, g.metricInner_sub_left,
    h₁, h₂, h₃, hcY, hcX]
  simp only [secondFundamentalForm_apply]
  ring

end GaussEquation

/-! ## Theorem 3.2.5 — the normal (Codazzi–Mainardi) curvature equation -/

section CodazziEquation

/-- **Math.** The **covariant derivative of the second fundamental form along
the hypersurface** (Petersen §3.2.1):
`(∇_XΠ)(Y,Z) = D_X(Π(Y,Z)) − Π(∇^H_XY, Z) − Π(Y, ∇^H_XZ)`. -/
def secondFundamentalFormCovariantDerivative (D : AffineConnection I M)
    (g : RiemannianMetric I M) (N X Y Z : Π x : M, TangentSpace I x)
    (p : M) : ℝ :=
  directionalDerivative X (fun q => secondFundamentalForm D g N Y Z q) p
    - secondFundamentalForm D g N (tangentialCovField D g N X Y) Z p
    - secondFundamentalForm D g N Y (tangentialCovField D g N X Z) p

/-- **Eng.** The normal pairing of `∇_X(∇_Y Z)`:
`g(∇_X(∇_Y Z), N) = −D_X(Π(Y,Z)) − Π(X, ∇^H_YZ)` at points of `U`, by metric
compatibility, the identification `g(∇_Y Z, N) = −Π(Y,Z)` on `U`, and
tangency of `∇_X N`. -/
private theorem cov_cov_metricInner_normal {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U)
    {N X Y Z : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (hunit : ∀ q ∈ U, g.metricInner q (N q) (N q) = 1)
    (hZtan : ∀ q ∈ U, g.metricInner q (Z q) (N q) = 0)
    {p : M} (hp : p ∈ U) :
    g.metricInner p (D.cov p (X p) (D.toAffineConnection.covField Y Z)) (N p)
      = -directionalDerivative X
          (fun q => secondFundamentalForm D.toAffineConnection g N Y Z q) p
        - secondFundamentalForm D.toAffineConnection g N X
            (tangentialCovField D.toAffineConnection g N Y Z) p := by
  have hcov : IsSmoothVectorField (D.toAffineConnection.covField Y Z) :=
    D.smooth_cov hY hZ
  -- metric compatibility on the pair `(∇_Y Z, N)` along `X`
  have hcompat := D.metric_compat hcov hN p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- the function `g(∇_Y Z, N)` agrees with `−Π(Y,Z)` near `p`
  have hloc : (fun q => g.metricInner q (D.toAffineConnection.covField Y Z q) (N q))
      =ᶠ[𝓝 p] fun q => -secondFundamentalForm D.toAffineConnection g N Y Z q := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact normalCoefficient_eq_neg_secondFundamentalForm D hU hN hZ hZtan Y hq
  have hdd : directionalDerivative X
        (fun q => g.metricInner q (D.toAffineConnection.covField Y Z q) (N q)) p
      = -directionalDerivative X
          (fun q => secondFundamentalForm D.toAffineConnection g N Y Z q) p := by
    rw [directionalDerivative_apply, directionalDerivative_apply, hloc.mfderiv_eq]
    have hneg : (fun q => -secondFundamentalForm D.toAffineConnection g N Y Z q)
        = -(fun q => secondFundamentalForm D.toAffineConnection g N Y Z q) := rfl
    rw [hneg, mfderiv_neg]
    rfl
  rw [hdd] at hcompat
  -- `g(∇_Y Z, ∇_X N) = Π(X, ∇^H_YZ)`: the normal part of `∇_Y Z` dies against
  -- the tangent vector `∇_X N`
  have hXN_tan : g.metricInner p (D.cov p (X p) N) (N p) = 0 :=
    secondFundamentalForm_normal_orthogonal D hU hN hunit X hp
  have hsecond : g.metricInner p (D.toAffineConnection.covField Y Z p)
        (D.cov p (X p) N)
      = secondFundamentalForm D.toAffineConnection g N X
          (tangentialCovField D.toAffineConnection g N Y Z) p := by
    rw [secondFundamentalForm_apply]
    have hdecomp : D.toAffineConnection.covField Y Z p
        = tangentialCovField D.toAffineConnection g N Y Z p
          + normalCoefficient D.toAffineConnection g N Y Z p • N p := by
      rw [covField_eq_tangential_add_normal D.toAffineConnection g N Y Z]
    rw [hdecomp, g.metricInner_add_left, g.metricInner_smul_left]
    have hcommN : g.metricInner p (N p) (D.cov p (X p) N)
        = g.metricInner p (D.cov p (X p) N) (N p) := g.metricInner_comm ..
    have hcommT : g.metricInner p
          (tangentialCovField D.toAffineConnection g N Y Z p) (D.cov p (X p) N)
        = g.metricInner p (D.cov p (X p) N)
            (tangentialCovField D.toAffineConnection g N Y Z p) :=
      g.metricInner_comm ..
    rw [hcommN, hXN_tan, hcommT]
    ring
  rw [hsecond] at hcompat
  linarith [hcompat]

/-- **Math.** **Theorem 3.2.5 — the normal (Peterson–Codazzi–Mainardi)
curvature equation** (Petersen, `thm:pet-ch3-normal-curvature-equation`): for
`Z` tangent to the hypersurface on `U` and the bracket `[X,Y]` tangent at
`p ∈ U`, `g(R(X,Y)Z, N) = −(∇_XΠ)(Y,Z) + (∇_YΠ)(X,Z)`. -/
theorem normalCurvatureEquation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U)
    {N X Y Z : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z)
    (hunit : ∀ q ∈ U, g.metricInner q (N q) (N q) = 1)
    (hZtan : ∀ q ∈ U, g.metricInner q (Z q) (N q) = 0)
    {p : M} (hp : p ∈ U)
    (hbr : g.metricInner p (N p) (lieDerivativeVectorField I X Y p) = 0) :
    curvatureTensorFour D X Y Z N p
      = -secondFundamentalFormCovariantDerivative D.toAffineConnection g
          N X Y Z p
        + secondFundamentalFormCovariantDerivative D.toAffineConnection g
            N Y X Z p := by
  have h₁ := cov_cov_metricInner_normal (X := X) D hU hN hY hZ hunit hZtan hp
  have h₂ := cov_cov_metricInner_normal (X := Y) D hU hN hX hZ hunit hZtan hp
  -- the bracket term is `−Π([X,Y], Z)`
  have h₃ : g.metricInner p
        (D.cov p (lieDerivativeVectorField I X Y p) Z) (N p)
      = -secondFundamentalForm D.toAffineConnection g N
          (lieDerivativeVectorField I X Y) Z p :=
    normalCoefficient_eq_neg_secondFundamentalForm D hU hN hZ hZtan
      (lieDerivativeVectorField I X Y) hp
  -- `Π(∇^H_XY − ∇^H_YX, Z) = Π([X,Y], Z)` using tangency of the bracket
  have htf := D.torsion_free hX hY p
  have hbracket : secondFundamentalForm D.toAffineConnection g N
        (tangentialCovField D.toAffineConnection g N X Y) Z p
      - secondFundamentalForm D.toAffineConnection g N
          (tangentialCovField D.toAffineConnection g N Y X) Z p
      = secondFundamentalForm D.toAffineConnection g N
          (lieDerivativeVectorField I X Y) Z p := by
    simp only [secondFundamentalForm_apply, tangentialCovField_apply,
      tangentialCov_apply]
    rw [← g.metricInner_sub_left, ← D.toAffineConnection.cov_sub_direction]
    congr 2
    have hcoeff : g.metricInner p (D.cov p (X p) Y) (N p)
        - g.metricInner p (D.cov p (Y p) X) (N p)
        = g.metricInner p (lieDerivativeVectorField I X Y p) (N p) := by
      rw [← g.metricInner_sub_left, htf]
    have hbr' : g.metricInner p (lieDerivativeVectorField I X Y p) (N p) = 0 := by
      rw [g.metricInner_comm]
      exact hbr
    rw [hbr'] at hcoeff
    -- assemble the two projected directions
    have : D.cov p (X p) Y - g.metricInner p (D.cov p (X p) Y) (N p) • N p
        - (D.cov p (Y p) X - g.metricInner p (D.cov p (Y p) X) (N p) • N p)
        = (D.cov p (X p) Y - D.cov p (Y p) X)
          - (g.metricInner p (D.cov p (X p) Y) (N p)
            - g.metricInner p (D.cov p (Y p) X) (N p)) • N p := by
      module
    rw [this, hcoeff, htf, zero_smul, sub_zero]
  rw [curvatureTensorFour_apply, curvatureTensor_apply, g.metricInner_sub_left,
    g.metricInner_sub_left, h₁, h₂, h₃, secondFundamentalFormCovariantDerivative,
    secondFundamentalFormCovariantDerivative]
  linarith [hbracket]

end CodazziEquation

/-! ## Gauss's Theorema Egregium -/

section Egregium

/-- **Math.** **Gauss's Theorema Egregium** (Petersen §3.2.1,
`cor:pet-ch3-gauss-egregium`): for a surface in flat ambient space
(`R ≡ 0`, e.g. `H ⊂ ℝ³`), with `E₁, E₂` tangent to `H` at `p`,
`g(R^H(E₁,E₂)E₂, E₁) = Π(E₁,E₁)Π(E₂,E₂) − Π(E₁,E₂)² = det[Π]` —
the extrinsic quantity `det[Π]` equals the intrinsic sectional curvature
`sec(T_pH) = g_H(R^H(E₁,E₂)E₂, E₁)` of the (orthonormal) tangent plane. -/
theorem gaussTheoremaEgregium {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U)
    {N E₁ E₂ : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    (hE₁ : IsSmoothVectorField E₁) (hE₂ : IsSmoothVectorField E₂)
    (hE₂tan : ∀ q ∈ U, g.metricInner q (E₂ q) (N q) = 0)
    {p : M} (hp : p ∈ U) (hE₁tan : g.metricInner p (E₁ p) (N p) = 0)
    (hflat : curvatureTensorFour D E₁ E₂ E₂ E₁ p = 0)
    (hsymm : secondFundamentalForm D.toAffineConnection g N E₂ E₁ p
      = secondFundamentalForm D.toAffineConnection g N E₁ E₂ p) :
    g.metricInner p
        (tangentialCurvatureTensor D.toAffineConnection g N E₁ E₂ E₂ p) (E₁ p)
      = secondFundamentalForm D.toAffineConnection g N E₁ E₁ p
          * secondFundamentalForm D.toAffineConnection g N E₂ E₂ p
        - secondFundamentalForm D.toAffineConnection g N E₁ E₂ p ^ 2 := by
  have hgauss := tangentialCurvatureEquation D hU hN hE₁ hE₂ hE₂ hE₂tan hp hE₁tan
  rw [hflat, hsymm] at hgauss
  nlinarith [hgauss]

end Egregium

end PetersenLib
