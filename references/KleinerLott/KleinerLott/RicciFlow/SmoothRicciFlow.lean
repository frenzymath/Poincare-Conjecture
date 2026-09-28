import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Order.Interval.Set.OrdConnected
import KleinerLott.RicciFlow.MetricFamily
import KleinerLott.RicciFlow.HopfRinow

/-!
# Smooth complete Ricci flows

This file supplies the geometric interface between a smooth Ricci flow and the
scalar data used by point selection. The time-slice distance is required to be
the Riemannian length distance, Ricci is the contraction of the supplied
Riemann tensor, and the scalar score is definitionally its full tensor norm.

The pinned mathlib revision supplies the local ingredients, but no packaged
Hopf--Rinow theorem.  `KleinerLott.RicciFlow.HopfRinow` proves the needed metric
compactness implication from approximate radial projections.  The latter
follow here by cutting an almost-minimizing Riemannian path at a prescribed
distance from its initial point.
-/

open Bundle Manifold Set
open scoped BigOperators Bundle ContDiff ENNReal Manifold Topology

noncomputable section

namespace KleinerLott

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- A smooth Riemannian metric on the tangent bundle of `M`. -/
abbrev SmoothRiemannianMetric :=
  Bundle.ContMDiffRiemannianMetric I ∞ E
    (TangentSpace I : M → Type _)

/-- The horizontal tangent space over product spacetime. -/
abbrev HorizontalTangentSpace (z : M × ℝ) : Type _ :=
  TangentSpace I z.1

noncomputable instance instHorizontalTotalSpaceTopology :
    TopologicalSpace (TotalSpace E (HorizontalTangentSpace (I := I) (M := M))) := by
  change TopologicalSpace
    (TotalSpace E
      ((Prod.fst : M × ℝ → M) *ᵖ (TangentSpace I : M → Type _)))
  infer_instance

noncomputable instance instHorizontalFiberBundle :
    FiberBundle E (HorizontalTangentSpace (I := I) (M := M)) := by
  let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
  change FiberBundle E (f *ᵖ (TangentSpace I : M → Type _))
  infer_instance

noncomputable instance instHorizontalVectorBundle :
    VectorBundle ℝ E (HorizontalTangentSpace (I := I) (M := M)) := by
  let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
  change VectorBundle ℝ E (f *ᵖ (TangentSpace I : M → Type _))
  infer_instance

noncomputable instance instHorizontalContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ E
      (HorizontalTangentSpace (I := I) (M := M))
      (I.prod 𝓘(ℝ, ℝ)) := by
  let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
  change ContMDiffVectorBundle ∞ E
    (f *ᵖ (TangentSpace I : M → Type _)) (I.prod 𝓘(ℝ, ℝ))
  infer_instance

/-- The evolving metric as a horizontal bilinear-form section over spacetime. -/
def horizontalMetricSection (g : ℝ → SmoothRiemannianMetric (I := I) (M := M))
    (z : M × ℝ) :
    TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun q : M × ℝ =>
        HorizontalTangentSpace (I := I) (M := M) q →L[ℝ]
          HorizontalTangentSpace (I := I) (M := M) q →L[ℝ] ℝ) :=
  TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) z ((g z.2).inner z.1)

/-- A metric family is jointly smooth in space and time on `J`. -/
def IsSmoothMetricFamilyOn
    (g : ℝ → SmoothRiemannianMetric (I := I) (M := M))
    (J : Set ℝ) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
    ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (horizontalMetricSection g) ((Set.univ : Set M) ×ˢ J)

/-- A pointwise covariant four-tensor on a tangent space. -/
abbrev RiemannCurvatureTensorAt (p : M) :=
  TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ]
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ

/-- The Riemann tensor of an evolving metric, exposed as geometric interface
data with the standard algebraic curvature symmetries. -/
structure RiemannCurvatureFamily where
  tensor : ℝ → ∀ (p : M), RiemannCurvatureTensorAt (I := I) p
  skew_first : ∀ (t : ℝ) (p : M) x y z w,
    tensor t p x y z w = -tensor t p y x z w
  pair_symm : ∀ (t : ℝ) (p : M) x y z w,
    tensor t p x y z w = tensor t p z w x y
  first_bianchi : ∀ (t : ℝ) (p : M) x y z w,
    tensor t p x y z w + tensor t p y z x w + tensor t p z x y w = 0

namespace RiemannCurvatureFamily

/-- The Ricci contraction of the Riemann tensor in an orthonormal frame. -/
noncomputable def ricciAt
    (Rm : RiemannCurvatureFamily (I := I) (M := M))
    (g : SmoothRiemannianMetric (I := I) (M := M))
    (t : ℝ) (p : M) (v w : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  ∑ i, Rm.tensor t p (e i) v w (e i)

/-- The full pointwise norm `|Rm|`, computed in an orthonormal frame. -/
noncomputable def normAt
    (Rm : RiemannCurvatureFamily (I := I) (M := M))
    (g : SmoothRiemannianMetric (I := I) (M := M))
    (t : ℝ) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  Real.sqrt
    (∑ i, ∑ j, ∑ k, ∑ l,
      (Rm.tensor t p (e i) (e j) (e k) (e l)) ^ 2)

omit [SigmaCompactSpace M] [T2Space M] in
theorem normAt_nonneg
    (Rm : RiemannCurvatureFamily (I := I) (M := M))
    (g : SmoothRiemannianMetric (I := I) (M := M))
    (t : ℝ) (p : M) : 0 ≤ Rm.normAt g t p :=
  Real.sqrt_nonneg _

end RiemannCurvatureFamily

/-- A bundled covariant derivative on the tangent bundle. -/
abbrev TangentCovariantDerivative :=
  CovariantDerivative I E (TangentSpace I : M → Type _)

/-- Metric compatibility for a bundled connection and a specified smooth
metric, expressed using mathlib's real-valued manifold differential. -/
def IsMetricCompatibleWith
    (g : SmoothRiemannianMetric (I := I) (M := M))
    (nabla : TangentCovariantDerivative (I := I) (M := M)) : Prop :=
  ∀ (p : M) (x y z : TangentSpace I p),
    let Y := FiberBundle.extend E y
    let Z := FiberBundle.extend E z
    d% (fun q ↦ g.inner q (Y q) (Z q)) p x =
      g.inner p (nabla Y p x) z + g.inner p y (nabla Z p x)

/-- A smooth bundled connection certified to be the Levi-Civita connection of
a smooth Riemannian metric.

The affine connection laws are supplied by mathlib's
`CovariantDerivative`; the remaining fields impose smoothness, torsion freedom,
and compatibility with the specified metric. -/
structure LeviCivitaConnectionData
    (g : SmoothRiemannianMetric (I := I) (M := M)) where
  cov : TangentCovariantDerivative (I := I) (M := M)
  smooth : CovariantDerivative.ContMDiffCovariantDerivative cov ∞
  torsion_free : cov.torsion = 0
  metric_compatible : IsMetricCompatibleWith (I := I) (M := M) g cov

namespace LeviCivitaConnectionData

/-- The `(0,4)` curvature form of the certified Levi-Civita connection.

Mathlib's canonical local extensions turn the four tangent vectors into
sections differentiable near `p`; the covariant-derivative commutator is then
evaluated at `p`. -/
noncomputable def curvatureFormAt
    (g : SmoothRiemannianMetric (I := I) (M := M))
    (nabla : LeviCivitaConnectionData (I := I) (M := M) g)
    (p : M) (x y z w : TangentSpace I p) : ℝ :=
  let X := FiberBundle.extend E x
  let Y := FiberBundle.extend E y
  let Z := FiberBundle.extend E z
  g.inner p
    (nabla.cov (fun q ↦ nabla.cov Z q (Y q)) p x -
      nabla.cov (fun q ↦ nabla.cov Z q (X q)) p y -
        nabla.cov Z p (VectorField.mlieBracket I X Y p))
    w

end LeviCivitaConnectionData

/-- The Ricci-flow equation `partial_t g = -2 Ric(g)` evaluated on tangent
vectors, with Ricci obtained by contracting the same Riemann tensor used below
to define `|Rm|`. -/
def IsRicciFlowEquationOn
    (g : ℝ → SmoothRiemannianMetric (I := I) (M := M))
    (Rm : RiemannCurvatureFamily (I := I) (M := M))
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p),
    HasDerivWithinAt (fun s => (g s).inner p x y)
      (-2 * Rm.ricciAt (g t) t p x y) J t

/-- The Riemannian extended distance induced by a smooth metric. -/
noncomputable def inducedRiemannianEDist
    (g : SmoothRiemannianMetric (I := I) (M := M)) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

/-- A smooth complete Ricci flow on `J`, together with the real-valued
time-slice distances and volume data used by Kleiner--Lott.

The distance-identification field also records finiteness of every induced
Riemannian distance, since its right-hand side is `ENNReal.ofReal` of a real
metric distance. -/
structure SmoothCompleteRicciFlowOn (J : Set ℝ) where
  metric : ℝ → SmoothRiemannianMetric (I := I) (M := M)
  curvature : RiemannCurvatureFamily (I := I) (M := M)
  leviCivita : ∀ t, LeviCivitaConnectionData (I := I) (M := M) (metric t)
  curvature_is_leviCivita : ∀ t ∈ J, ∀ (p : M)
    (x y z w : TangentSpace I p),
      curvature.tensor t p x y z w =
        LeviCivitaConnectionData.curvatureFormAt
          (metric t) (leviCivita t) p x y z w
  distance : MetricFamily M
  volume : ℝ → Set M → ℝ
  ordConnected : J.OrdConnected
  nontrivial : J.Nontrivial
  smooth : IsSmoothMetricFamilyOn metric J
  equation : IsRicciFlowEquationOn metric curvature J
  induced_distance : ∀ t ∈ J, ∀ x y,
    inducedRiemannianEDist (metric t) x y =
      ENNReal.ofReal (distance.dist t x y)
  complete : ∀ t ∈ J,
    @CompleteSpace M (distance.metricSpaceAt t).toUniformSpace
  distance_continuous : distance.IsContinuousOn J
  curvature_continuous :
    ContinuousOn
      (Function.uncurry fun x t => curvature.normAt (metric t) t x)
      (Set.univ ×ˢ J)

namespace SmoothCompleteRicciFlowOn

/-- The pointwise Riemann curvature norm, with argument order matching
`RicciFlowData.curvatureNorm`. -/
noncomputable def curvatureNorm
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J) :
    M → ℝ → ℝ :=
  fun x t => flow.curvature.normAt (flow.metric t) t x

/-- Scalar flow data obtained from the induced distance and the actual
Riemann-tensor norm of a smooth Ricci flow. -/
noncomputable def toFlowData
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J) :
    RicciFlowData M :=
  flow.distance.toFlowData flow.curvatureNorm flow.volume

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem toFlowData_dist
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J)
    (t : ℝ) (x y : M) :
    flow.toFlowData.dist t x y = flow.distance.dist t x y :=
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem toFlowData_curvatureNorm
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J)
    (x : M) (t : ℝ) :
    flow.toFlowData.curvatureNorm x t =
      flow.curvature.normAt (flow.metric t) t x :=
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
/-- Induced Riemannian length distance supplies paths staying in an arbitrarily
small enlargement of the endpoint distance sublevel. No geodesic-minimizer or
Hopf--Rinow hypothesis is needed for this almost-minimizing form. -/
theorem hasAlmostRadialDistancePathsOn
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J)
    (x₀ : M) :
    flow.toFlowData.HasAlmostRadialDistancePathsOn x₀ J := by
  intro s hs x delta hdelta
  letI : MetricSpace M := flow.distance.metricSpaceAt s
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(flow.metric s).toRiemannianMetric⟩
  have hedist (y z : M) :
      Manifold.riemannianEDist I y z =
        ENNReal.ofReal (flow.distance.dist s y z) := by
    simpa [inducedRiemannianEDist] using
      flow.induced_distance s hs y z
  have hdist_nonneg : ∀ y, 0 ≤ flow.distance.dist s x₀ y := by
    intro y
    change 0 ≤ Dist.dist x₀ y
    exact dist_nonneg
  have hsum_pos : 0 < flow.distance.dist s x₀ x + delta :=
    add_pos_of_nonneg_of_pos (hdist_nonneg x) hdelta
  have hr :
      Manifold.riemannianEDist I x₀ x <
        ENNReal.ofReal (flow.distance.dist s x₀ x + delta) := by
    rw [hedist x₀ x]
    exact (ENNReal.ofReal_lt_ofReal_iff hsum_pos).2
      (lt_add_of_pos_right _ hdelta)
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I) hr
  refine ⟨Path.ofLine hγsmooth.continuousOn hγ0 hγ1, ?_⟩
  intro u
  change flow.distance.dist s x₀ (γ (u : ℝ)) ≤
    flow.distance.dist s x₀ x + delta
  have hγprefix : CMDiff[Set.Icc 0 (u : ℝ)] 1 γ :=
    hγsmooth.mono fun z hz => ⟨hz.1, hz.2.trans u.property.2⟩
  have hprefix :
      Manifold.riemannianEDist I x₀ (γ (u : ℝ)) ≤
        Manifold.pathELength I γ 0 (u : ℝ) :=
    Manifold.riemannianEDist_le_pathELength
      hγprefix hγ0 rfl u.property.1
  have hmono :
      Manifold.pathELength I γ 0 (u : ℝ) ≤
        Manifold.pathELength I γ 0 1 :=
    Manifold.pathELength_mono
      (I := I) (γ := γ) le_rfl u.property.2
  have hu :
      Manifold.riemannianEDist I x₀ (γ (u : ℝ)) <
        ENNReal.ofReal (flow.distance.dist s x₀ x + delta) :=
    (hprefix.trans hmono).trans_lt hγlen
  rw [hedist x₀ (γ (u : ℝ))] at hu
  exact ((ENNReal.ofReal_lt_ofReal_iff hsum_pos).1 hu).le

omit [SigmaCompactSpace M] [T2Space M] in
/-- An almost-minimizing Riemannian path can be cut at any smaller radius, and
the remaining endpoint distance is arbitrarily close to the difference of
the two radii. -/
theorem hasApproximateRadialProjectionsAt
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J)
    (s : ℝ) (hs : s ∈ J) :
    @HasApproximateRadialProjections M (flow.distance.metricSpaceAt s) := by
  letI : MetricSpace M := flow.distance.metricSpaceAt s
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(flow.metric s).toRiemannianMetric⟩
  intro x z r delta hr hrxz hdelta
  change r < flow.distance.dist s x z at hrxz
  change ∃ q, flow.distance.dist s x q = r ∧
    flow.distance.dist s q z < flow.distance.dist s x z - r + delta
  have hedist (y w : M) :
      Manifold.riemannianEDist I y w =
        ENNReal.ofReal (flow.distance.dist s y w) := by
    simpa [inducedRiemannianEDist] using
      flow.induced_distance s hs y w
  have hdist_xz_nonneg : 0 ≤ flow.distance.dist s x z := by
    change 0 ≤ dist x z
    exact dist_nonneg
  have htotal_pos : 0 < flow.distance.dist s x z + delta :=
    add_pos_of_nonneg_of_pos hdist_xz_nonneg hdelta
  have hriem :
      Manifold.riemannianEDist I x z <
        ENNReal.ofReal (flow.distance.dist s x z + delta) := by
    rw [hedist x z]
    exact (ENNReal.ofReal_lt_ofReal_iff htotal_pos).2
      (lt_add_of_pos_right _ hdelta)
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (I := I) hriem
  have hdist_cont :
      ContinuousOn (fun u : ℝ ↦ flow.distance.dist s x (γ u))
        (Set.Icc 0 1) := by
    change ContinuousOn (fun u : ℝ ↦ dist x (γ u)) (Set.Icc 0 1)
    simpa only [Function.comp_def] using
      continuous_dist.continuousOn.comp
        (continuousOn_const.prodMk hγsmooth.continuousOn)
        (fun _ _ ↦ Set.mem_univ _)
  have hr_between :
      r ∈ Set.Icc (flow.distance.dist s x (γ 0))
        (flow.distance.dist s x (γ 1)) := by
    simp only [hγ0, hγ1]
    exact ⟨by simpa [flow.distance.dist_self] using hr,
      hrxz.le⟩
  obtain ⟨u, hu, hu_radius⟩ :=
    (intermediate_value_Icc zero_le_one hdist_cont) hr_between
  refine ⟨γ u, hu_radius, ?_⟩
  have hprefix_smooth : CMDiff[Set.Icc 0 u] 1 γ :=
    hγsmooth.mono fun y hy ↦ ⟨hy.1, hy.2.trans hu.2⟩
  have htail_smooth : CMDiff[Set.Icc u 1] 1 γ :=
    hγsmooth.mono fun y hy ↦ ⟨hu.1.trans hy.1, hy.2⟩
  have hprefix :
      ENNReal.ofReal r ≤ Manifold.pathELength I γ 0 u := by
    have h := Manifold.riemannianEDist_le_pathELength
      hprefix_smooth hγ0 rfl hu.1
    rw [hedist x (γ u)] at h
    simpa [hu_radius] using h
  have htail :
      ENNReal.ofReal (flow.distance.dist s (γ u) z) ≤
        Manifold.pathELength I γ u 1 := by
    have h := Manifold.riemannianEDist_le_pathELength
      htail_smooth rfl hγ1 hu.2
    simpa [hedist] using h
  have hdist_qz_nonneg : 0 ≤ flow.distance.dist s (γ u) z := by
    change 0 ≤ dist (γ u) z
    exact dist_nonneg
  have hsum :
      ENNReal.ofReal (r + flow.distance.dist s (γ u) z) <
        ENNReal.ofReal (flow.distance.dist s x z + delta) := by
    calc
      ENNReal.ofReal (r + flow.distance.dist s (γ u) z) =
          ENNReal.ofReal r +
            ENNReal.ofReal (flow.distance.dist s (γ u) z) :=
        ENNReal.ofReal_add hr hdist_qz_nonneg
      _ ≤ Manifold.pathELength I γ 0 u +
          Manifold.pathELength I γ u 1 := add_le_add hprefix htail
      _ = Manifold.pathELength I γ 0 1 :=
        Manifold.pathELength_add hu.1 hu.2
      _ < ENNReal.ofReal (flow.distance.dist s x z + delta) := hγlen
  have hreal := (ENNReal.ofReal_lt_ofReal_iff htotal_pos).1 hsum
  linarith

/-- Properness of every relevant time slice, the compactness conclusion of
Hopf--Rinow. -/
def HasHopfRinowProperSlicesOn
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J) : Prop :=
  flow.distance.IsProperOn J

omit [SigmaCompactSpace M] [T2Space M] in
/-- Completeness of every induced Riemannian length-distance slice implies
properness. -/
theorem hasHopfRinowProperSlicesOn
    {J : Set ℝ} (flow : SmoothCompleteRicciFlowOn (I := I) (M := M) J) :
    flow.HasHopfRinowProperSlicesOn := by
  intro s hs
  letI : MetricSpace M := flow.distance.metricSpaceAt s
  letI : CompleteSpace M := flow.complete s hs
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional I
  exact properSpace_of_complete_locallyCompact_of_approximateRadialProjections
    (flow.hasApproximateRadialProjectionsAt s hs)

omit [SigmaCompactSpace M] [T2Space M] in
/-- Kleiner--Lott point selection for a genuine smooth complete Ricci flow,
with proper time slices supplied explicitly.

The dimension in the smallness hypothesis is definitionally the dimension of
the model space; there is no independent natural-number parameter. -/
theorem exists_point_selection_of_smooth_complete_ricci_flow_of_hopfRinow
    [ConnectedSpace M]
    {alpha A epsilon t : ℝ} {x₀ x : M}
    (flow : SmoothCompleteRicciFlowOn (I := I) (M := M)
      (Set.Icc 0 (epsilon ^ 2)))
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon :
      A * epsilon < (100 * (Module.finrank ℝ E : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.toFlowData.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤
        flow.toFlowData.curvatureNorm x t)
    (hHopfRinow : flow.HasHopfRinowProperSlicesOn) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.toFlowData.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.toFlowData.dist tbar x₀ xbar <
          (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.toFlowData.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.toFlowData.dist t' x₀ x' ≤
                  flow.toFlowData.dist tbar x₀ xbar +
                    A * (Real.sqrt
                      (flow.toFlowData.curvatureNorm xbar tbar))⁻¹ →
                flow.toFlowData.curvatureNorm x' t' ≤
                  4 * flow.toFlowData.curvatureNorm xbar tbar := by
  have hproper :
      ∀ s ∈ Set.Icc 0 (epsilon ^ 2),
        flow.toFlowData.IsProperAt x₀ s := by
    intro s hs
    exact hHopfRinow.isProperAt flow.curvatureNorm flow.volume x₀ hs
  have hdist_self :
      ∀ s ∈ Set.Icc 0 (epsilon ^ 2),
        flow.toFlowData.dist s x₀ x₀ = 0 := by
    intro s _
    exact flow.distance.dist_self s x₀
  have hdist_cont :
      ContinuousOn
        (Function.uncurry fun s y => flow.toFlowData.dist s x₀ y)
        (Set.Icc 0 (epsilon ^ 2) ×ˢ Set.univ) :=
    flow.distance_continuous.continuousOn_toFlowData_dist
      flow.curvatureNorm flow.volume x₀
  exact exists_point_selection_of_almost_radial_distance_family
    flow.toFlowData (Module.finrank ℝ E) halpha hA hepsilon hAepsilon ht
    hdist hcurvature flow.curvature_continuous hproper hdist_self hdist_cont
    (flow.hasAlmostRadialDistancePathsOn x₀)

omit [SigmaCompactSpace M] [T2Space M] in
/-- Kleiner--Lott point selection for the induced distance and curvature norm
of a smooth complete Ricci-flow metric family.  Proper time slices are derived
from completeness by the metric Hopf--Rinow compactness theorem. -/
theorem exists_point_selection_of_smooth_complete_ricci_flow
    [ConnectedSpace M]
    {alpha A epsilon t : ℝ} {x₀ x : M}
    (flow : SmoothCompleteRicciFlowOn (I := I) (M := M)
      (Set.Icc 0 (epsilon ^ 2)))
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon :
      A * epsilon < (100 * (Module.finrank ℝ E : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.toFlowData.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤
        flow.toFlowData.curvatureNorm x t) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.toFlowData.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.toFlowData.dist tbar x₀ xbar <
          (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.toFlowData.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.toFlowData.dist t' x₀ x' ≤
                  flow.toFlowData.dist tbar x₀ xbar +
                    A * (Real.sqrt
                      (flow.toFlowData.curvatureNorm xbar tbar))⁻¹ →
                flow.toFlowData.curvatureNorm x' t' ≤
                  4 * flow.toFlowData.curvatureNorm xbar tbar := by
  exact flow.exists_point_selection_of_smooth_complete_ricci_flow_of_hopfRinow
    halpha hA hepsilon hAepsilon ht hdist hcurvature
    flow.hasHopfRinowProperSlicesOn

end SmoothCompleteRicciFlowOn

end KleinerLott
