import DoCarmoLib.Riemannian.Jacobi.CartanMFDerivBridge
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6
import MorganTianLib.Ch01.ConstantGeodesicJacobi

/-!
# Morgan--Tian Ch. 1: constant rescaling and constant-curvature Jacobi fields

This file supplies reusable parts of two late Chapter 1 preliminaries.

* `rescaledMetric` is the constant multiple `c g` of an arbitrary Riemannian
  metric.  Its metric pairing is `c` times the old pairing, its Levi-Civita
  connection is unchanged, its `(1,3)` curvature is unchanged, and its
  `(0,4)` curvature form is multiplied by `c`.  Constant sectional curvature
  `K` therefore becomes `K / c`.
* `exists_constantCurvatureJacobiProfile` and
  `constantCurvatureJacobi_normal_profile` package the scalar ODE and the
  resulting normal Jacobi field along a unit-speed geodesic.  Together with
  `constantCurvature_expMapGlobal_localDiffeomorph`, they formalize the normal
  Jacobi-field and nonzero nonsingularity parts of Morgan--Tian's
  constant-curvature exponential-map lemma.

The distance, volume, injectivity-radius, and global model-space clauses need
metric-space and measure instances built from a rescaled metric.  DoCarmoLib
currently keeps the ambient `MetricSpace M` fixed while taking the Riemannian
metric as explicit data, so those clauses are deliberately not asserted here.

References: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
`lem:metric-rescaling` and `lem:constant-curvature-jacobi`.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Constant rescaling of a Riemannian metric -/

/-- **Math.** The constant rescaling `c g` of a Riemannian metric, for `c > 0`.

The boundedness proof sends its unit ball into the unit ball of `g` by
`v ↦ √c v`; this avoids choosing any norm compatible with `g`.
Blueprint: `lem:metric-rescaling`. -/
def rescaledMetric (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) :
    RiemannianMetric I M where
  inner x := c • g.inner x
  symm x v w := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.symm x v w]
  pos x v hv := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_pos hc (g.pos x v hv)
  isVonNBounded x := by
    let L : TangentSpace I x →L[ℝ] TangentSpace I x :=
      (Real.sqrt c)⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace I x)
    refine ((g.isVonNBounded x).image L).subset ?_
    intro v hv
    refine ⟨Real.sqrt c • v, ?_, ?_⟩
    · change g.inner x (Real.sqrt c • v) (Real.sqrt c • v) < 1
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, Real.mul_self_sqrt hc.le]
      exact hv
    · change (Real.sqrt c)⁻¹ • (Real.sqrt c • v) = v
      rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hc), one_smul]
  contMDiff := g.contMDiff.const_smul_section

@[simp]
theorem rescaledMetric_metricInner (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (x : M) (v w : TangentSpace I x) :
    (rescaledMetric g c hc).metricInner x v w = c * g.metricInner x v w := by
  rfl

section LeviCivitaScaling

variable [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A connection compatible with `g` is compatible with every positive
constant multiple `c g`.  The factor `c` passes through the directional
derivative because it is constant. -/
theorem AffineConnection.IsMetricCompatible.rescaledMetric
    {g : RiemannianMetric I M} {nabla : AffineConnection I M}
    (hcompat : nabla.IsMetricCompatible g) (c : ℝ) (hc : 0 < c) :
    nabla.IsMetricCompatible (rescaledMetric g c hc) := by
  intro X Y Z p
  change X.dir (fun q => c * g.metricInner q (Y q) (Z q)) p =
    c * g.metricInner p ((nabla.cov X Y) p) (Z p) +
      c * g.metricInner p (Y p) ((nabla.cov X Z) p)
  rw [X.dir_const_mul c p (g.metricInner_field_mdifferentiableAt Y Z p),
    hcompat X Y Z p]
  ring

/-- **Math.** Constant rescaling does not change the Levi-Civita connection.
Consequently it does not change parameterized geodesics, exponential maps, or
the `(1,3)` curvature tensor, all of which depend only on this connection.
Blueprint: `lem:metric-rescaling` (connection part of item 1). -/
theorem rescaledMetric_leviCivitaConnection
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) :
    (rescaledMetric g c hc).leviCivitaConnection = g.leviCivitaConnection := by
  apply AffineConnection.leviCivita_unique' (rescaledMetric g c hc)
  · exact Riemannian.AffineConnection.isLeviCivita_of_koszulDual
      (g := rescaledMetric g c hc)
      (nabla := (rescaledMetric g c hc).leviCivitaConnection)
      (fun X Y Z p => (rescaledMetric g c hc).koszulDualSection_dual X Y Z p)
  · have hLC := Riemannian.AffineConnection.isLeviCivita_of_koszulDual
      (g := g) (nabla := g.leviCivitaConnection)
      (fun X Y Z p => g.koszulDualSection_dual X Y Z p)
    exact ⟨hLC.1,
      MorganTianLib.AffineConnection.IsMetricCompatible.rescaledMetric hLC.2 c hc⟩

/-- **Math.** The `(1,3)` curvature tensor is unchanged by constant metric
rescaling, because it is built only from the unchanged connection.
Blueprint: `lem:metric-rescaling` (item 1). -/
theorem rescaledMetric_curvature
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (X Y Z : SmoothVectorField I M) :
    (rescaledMetric g c hc).leviCivitaConnection.curvature X Y Z =
      g.leviCivitaConnection.curvature X Y Z := by
  rw [rescaledMetric_leviCivitaConnection]

/-- **Math.** Lowering the output of the unchanged `(1,3)` curvature tensor
with `c g` multiplies the `(0,4)` curvature form by `c`.
Blueprint: `lem:metric-rescaling` (item 1). -/
theorem rescaledMetric_curvatureForm
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (X Y Z W : SmoothVectorField I M) (p : M) :
    (rescaledMetric g c hc).leviCivitaConnection.curvatureForm
        (rescaledMetric g c hc) X Y Z W p =
      c * g.leviCivitaConnection.curvatureForm g X Y Z W p := by
  rw [AffineConnection.curvatureForm, rescaledMetric_metricInner,
    rescaledMetric_curvature]
  rfl

/-- **Math.** Constant sectional curvature `K` becomes `K / c` under the
rescaling `g ↦ c g`.
Blueprint: `lem:metric-rescaling` (sectional-curvature part of item 2). -/
theorem rescaledMetric_isConstantCurvature
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (K : ℝ)
    (hK : g.leviCivitaConnection.IsConstantCurvature g K) :
    (rescaledMetric g c hc).leviCivitaConnection.IsConstantCurvature
      (rescaledMetric g c hc) (K / c) := by
  intro X Y Z W p
  rw [rescaledMetric_leviCivitaConnection]
  rw [rescaledMetric_metricInner, rescaledMetric_metricInner,
    rescaledMetric_metricInner, rescaledMetric_metricInner,
    rescaledMetric_metricInner, hK X Y Z W p]
  field_simp

end LeviCivitaScaling

/-! ## Jacobi fields in constant curvature -/

section ConstantCurvatureJacobi

variable {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]

/-- **Math.** The sign-uniform scalar profile `s_K`: there are functions
`s, s'` solving `s'' + K s = 0`, with `s(0)=0` and `s'(0)=1`.
They are respectively sine, linear, or hyperbolic sine profiles according to
the sign of `K`.
Blueprint: `lem:constant-curvature-jacobi`. -/
theorem exists_constantCurvatureJacobiProfile (K : ℝ) :
    ∃ s ds : ℝ → ℝ,
      (∀ t, HasDerivAt s (ds t) t) ∧
      (∀ t, HasDerivAt ds (-K * s t) t) ∧
      s 0 = 0 ∧ ds 0 = 1 :=
  Riemannian.Jacobi.exists_constCurvatureSol K


/-- **Math.** The normal scalar profile produces a Jacobi field along every
unit-speed geodesic in constant curvature.  This is the chart-independent
normal component of Morgan--Tian's constant-curvature Jacobi decomposition.
Blueprint: `lem:constant-curvature-jacobi` (normal component). -/
theorem constantCurvatureJacobi_normal_profile
    (g : RiemannianMetric I N) {K : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K)
    {γ : ℝ → N} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ t = 1)
    (Epar : ℝ → E)
    (hEpar : Riemannian.Jacobi.IsParallelFieldAlongOn g γ Epar 0 ℓ)
    (hperp : ∀ t ∈ Icc (0 : ℝ) ℓ,
      g.metricInner (γ t) (Epar t : TangentSpace I (γ t))
        (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1) = 0)
    (s ds : ℝ → ℝ) (hs' : ∀ t, HasDerivAt s (ds t) t)
    (hds' : ∀ t, HasDerivAt ds (-K * s t) t) :
    Riemannian.Jacobi.IsJacobiFieldAlongOn g γ
      (fun t => s t • Epar t) (fun t => ds t • Epar t) 0 ℓ :=
  Riemannian.Jacobi.isJacobiFieldAlongOn_of_constantCurvature
    (I := I) g hK hℓ hgeo hγc hspeed Epar hEpar hperp s ds hs' hds'

/-- **Math.** Every Jacobi field `J` vanishing at the initial point of a
unit-speed geodesic in constant curvature has the classical orthogonal
decomposition

`J(t) = a · t · γ'(t) + s_K(t) · E(t)`,

where `a = ⟨∇J(0), γ'(0)⟩` and `E` is the parallel transport of the
component of `∇J(0)` perpendicular to `γ'(0)`.  The second equality records
the corresponding covariant derivative.  This is the full field-valued form
behind the norm identity in
`Riemannian.Jacobi.metricInner_jacobiField_eq_of_constantCurvature`.
Blueprint: `lem:constant-curvature-jacobi` (item 1). -/
theorem constantCurvatureJacobi_decomposition
    (g : RiemannianMetric I N) {K : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K)
    {γ : ℝ → N} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ t = 1)
    (J DJ : ℝ → E)
    (hJF : Riemannian.Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 ℓ)
    (hJ0 : J 0 = 0)
    (s ds : ℝ → ℝ) (hs' : ∀ t, HasDerivAt s (ds t) t)
    (hds' : ∀ t, HasDerivAt ds (-K * s t) t) (hs0 : s 0 = 0) (hds0 : ds 0 = 1) :
    let X : ℝ → E := fun t => mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1
    ∃ Epar : ℝ → E,
      Riemannian.Jacobi.IsParallelFieldAlongOn g γ Epar 0 ℓ ∧
      Epar 0 =
        DJ 0 - g.metricInner (γ 0) (DJ 0) (X 0) • X 0 ∧
      (∀ t ∈ Icc (0 : ℝ) ℓ,
        g.metricInner (γ t) (Epar t : TangentSpace I (γ t))
          (X t : TangentSpace I (γ t)) = 0) ∧
      ∀ t ∈ Icc (0 : ℝ) ℓ,
        J t =
            g.metricInner (γ 0) (DJ 0) (X 0) • (t • X t) + s t • Epar t ∧
          DJ t =
            g.metricInner (γ 0) (DJ 0) (X 0) • X t + ds t • Epar t := by
  classical
  dsimp only
  set X : ℝ → E := fun t => mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1
  set a : ℝ := g.metricInner (γ 0) (DJ 0) (X 0)
  have hXpar : Riemannian.Jacobi.IsParallelFieldAlongOn g γ X 0 ℓ :=
    Riemannian.Jacobi.isParallelFieldAlongOn_velocity g hℓ hgeo hγc
  have hXX0 : g.metricInner (γ 0) (X 0) (X 0) = 1 := by
    have h := hspeed 0 ⟨le_rfl, hℓ.le⟩
    rwa [Geodesic.speedSq_def] at h
  let DJ0T : TangentSpace I (γ 0) := DJ 0
  let X0T : TangentSpace I (γ 0) := X 0
  have hXX0T : g.metricInner (γ 0) X0T X0T = 1 := by
    simpa [X0T] using hXX0
  have hperp0T : g.metricInner (γ 0) (DJ0T - a • X0T) X0T = 0 := by
    rw [g.metricInner_sub_left, g.metricInner_smul_left, hXX0T, mul_one]
    exact sub_self a
  obtain ⟨Epar, hEpar, hEpar0⟩ :=
    Riemannian.Jacobi.exists_parallelFieldAlongOn
      (I := I) hℓ hgeo hγc (DJ 0 - a • X 0)
  have hEpar0T : (Epar 0 : TangentSpace I (γ 0)) = DJ0T - a • X0T := by
    simpa [DJ0T, X0T] using hEpar0
  have hperp : ∀ t ∈ Icc (0 : ℝ) ℓ,
      g.metricInner (γ t) (Epar t : TangentSpace I (γ t))
        (X t : TangentSpace I (γ t)) = 0 := by
    intro t ht
    rw [Riemannian.Jacobi.IsParallelFieldAlongOn.metricInner_const
      (I := I) hℓ.le hEpar hXpar hgeo hγc ht, hEpar0T]
    simpa [X0T] using hperp0T
  have hnormal : Riemannian.Jacobi.IsJacobiFieldAlongOn g γ
      (fun t => s t • Epar t) (fun t => ds t • Epar t) 0 ℓ :=
    constantCurvatureJacobi_normal_profile g hK hℓ hgeo hγc hspeed
      Epar hEpar hperp s ds hs' hds'
  have htangent :=
    (Riemannian.Jacobi.isJacobiFieldAlongOn_smul_velocity
      (I := I) g hℓ hgeo hγc).smul a
  have hsum := htangent.add hℓ hgeo hγc hnormal
  refine ⟨Epar, hEpar, ?_, hperp, ?_⟩
  · simpa [a, X] using hEpar0
  · intro t ht
    obtain ⟨hJt, hDJt⟩ :=
      Riemannian.Jacobi.IsJacobiFieldAlongOn.eqOn_of_initial
        (I := I) hℓ hgeo hγc hJF hsum
        (by
          rw [hJ0]
          simp only [hs0, zero_smul, add_zero]
          exact (smul_zero a).symm)
        (by simp only [hds0, one_smul, hEpar0]; abel) t ht
    simpa [a, X] using And.intro hJt hDJt

/-- **Math.** On a complete constant-curvature manifold, the exponential map
is nonsingular at every nonzero `v` satisfying `K |v|^2 < pi^2`.  This is the
metric-free inequality equivalent to `|v| < D_K` in Morgan--Tian.
Blueprint: `lem:constant-curvature-jacobi` (item 2). -/
theorem constantCurvature_expMapGlobal_localDiffeomorph
    (g : RiemannianMetric I N) (hg : g.IsRiemannianDist) [CompleteSpace N]
    {K : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K)
    (p : N) (v : E) (hv : v ≠ 0)
    (hlt : K * g.metricInner p (v : TangentSpace I p) v < Real.pi ^ 2) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E) I ∞
      (fun w : E => expMapGlobal (I := I) g hg p w) v := by
  have hnc :=
    Riemannian.Jacobi.not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi
      (I := I) g hg hK p hv hlt
  exact Riemannian.Jacobi.isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate
    (I := I) g hg p hnc

/-- **Math.** On a complete constant-curvature manifold, the exponential map
is a local diffeomorphism at every vector satisfying
`K · |v|_g² < π²`, including the origin.  For `v ≠ 0` this is the
constant-curvature Jacobi calculation; at `v = 0` the Jacobi equation is
`J'' = 0` and no curvature hypothesis is needed.
Blueprint: `lem:constant-curvature-jacobi` (item 2). -/
theorem constantCurvature_expMapGlobal_isLocalDiffeomorph_of_lt
    (g : RiemannianMetric I N) (hg : g.IsRiemannianDist) [CompleteSpace N]
    {K : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K)
    (p : N) (v : E)
    (hlt : K * g.metricInner p (v : TangentSpace I p) v < Real.pi ^ 2) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E) I ∞
      (fun w : E => expMapGlobal (I := I) g hg p w) v := by
  by_cases hv : v = 0
  · subst v
    exact Riemannian.Jacobi.isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate
      (I := I) g hg p
        (Riemannian.Jacobi.not_isConjugatePointAt_globalGeodesic_zero
          (I := I) g hg p)
  · exact constantCurvature_expMapGlobal_localDiffeomorph g hg hK p v hv hlt

end ConstantCurvatureJacobi

/-! ## Euclidean submanifold connection: the existing identified-patch API -/

/-- **Math.** For an immersed patch, the induced covariant derivative is the
orthogonal tangential projection of the ambient covariant derivative.  This is
the precise identified-patch form of the Gauss formula
`nabla_X Y = P(D_X Y)`; for a Euclidean ambient one takes
`nabla = opensEuclideanConnection`.
Blueprint: `lem:submanifold-connection` (connection formula). -/
theorem submanifoldConnection_eq_tangentProjection
    {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)
    (nabla : AffineConnection I M) (X Y : SmoothVectorField I M) :
    D.inducedCov nabla X Y = D.tangentProj (nabla.cov X Y) :=
  rfl

end MorganTianLib

end
