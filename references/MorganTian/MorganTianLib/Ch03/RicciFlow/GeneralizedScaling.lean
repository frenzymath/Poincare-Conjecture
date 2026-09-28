import MorganTianLib.Ch03.RicciFlow.GeneralizedRicciFlow
import MorganTianLib.Ch03.RicciFlow.GeneralizedEmbedding
import MorganTianLib.Ch01.Chapter1BasicRemaining
import Mathlib.Order.Interval.Set.OrderIso

/-!
# Morgan--Tian Ch. 3 - scaling and translation data

For a positive factor `Q`, parabolic rescaling changes the time coordinate by
`t |-> Q t`, the time vector by `chi |-> Q⁻¹ chi`, and the horizontal metric
by `G |-> Q G`.  A subsequent time translation adds a constant to time and
leaves the other two components unchanged.
-/

open scoped ContDiff Manifold Topology
open Riemannian Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

noncomputable local instance (n : ℕ) [NeZero n] :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
  ⟨by simpa using (NeZero.out : n ≠ 0)⟩

/-- **Math.** The positive affine change of time `t |-> Q t + a`. -/
def parabolicTimeOrderIso (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : ℝ ≃o ℝ where
  toFun t := Q * t + a
  invFun s := (s - a) / Q
  left_inv t := by
    field_simp [hQ.ne']
    ring
  right_inv s := by
    field_simp [hQ.ne']
    ring
  map_rel_iff' := by
    intro s t
    change (Q * s + a ≤ Q * t + a) ↔ s ≤ t
    constructor <;> intro h <;> nlinarith [hQ]

@[simp]
theorem parabolicTimeOrderIso_apply (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) :
    parabolicTimeOrderIso Q hQ a t = Q * t + a :=
  rfl

@[simp]
theorem parabolicTimeOrderIso_symm_apply (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) :
    (parabolicTimeOrderIso Q hQ a).symm t = (t - a) / Q :=
  rfl

/-- **Math.** Positive affine time changes carry closed intervals to the
corresponding closed intervals. -/
theorem parabolicTimeOrderIso_image_Icc (Q : ℝ) (hQ : 0 < Q)
    (a s t : ℝ) :
    parabolicTimeOrderIso Q hQ a '' Icc s t =
      Icc (Q * s + a) (Q * t + a) := by
  simpa only [parabolicTimeOrderIso_apply] using
    (parabolicTimeOrderIso Q hQ a).image_Icc s t

/-- **Math.** Positive affine time changes carry open intervals to the
corresponding open intervals. -/
theorem parabolicTimeOrderIso_image_Ioo (Q : ℝ) (hQ : 0 < Q)
    (a s t : ℝ) :
    parabolicTimeOrderIso Q hQ a '' Ioo s t =
      Ioo (Q * s + a) (Q * t + a) := by
  simpa only [parabolicTimeOrderIso_apply] using
    (parabolicTimeOrderIso Q hQ a).image_Ioo s t

/-! The half-open interval cases are needed when a maximal time range has one
closed endpoint and one open endpoint. -/

/-- **Math.** A positive affine time change carries a left-closed, right-open
interval to the corresponding interval. -/
theorem parabolicTimeOrderIso_image_Ico (Q : ℝ) (hQ : 0 < Q)
    (a s t : ℝ) :
    parabolicTimeOrderIso Q hQ a '' Ico s t =
      Ico (Q * s + a) (Q * t + a) := by
  simpa only [parabolicTimeOrderIso_apply] using
    (parabolicTimeOrderIso Q hQ a).image_Ico s t

/-- **Math.** A positive affine time change carries a left-open, right-closed
interval to the corresponding interval. -/
theorem parabolicTimeOrderIso_image_Ioc (Q : ℝ) (hQ : 0 < Q)
    (a s t : ℝ) :
    parabolicTimeOrderIso Q hQ a '' Ioc s t =
      Ioc (Q * s + a) (Q * t + a) := by
  simpa only [parabolicTimeOrderIso_apply] using
    (parabolicTimeOrderIso Q hQ a).image_Ioc s t

/-! The half-infinite interval laws are useful when a generalized flow has a
one-sided maximal time range.  They are the endpoint cases of the same
order-isomorphism calculation, rather than extra assumptions on the range. -/

/-- **Math.** A positive affine time change carries a closed upper ray to the
corresponding closed upper ray. -/
theorem parabolicTimeOrderIso_image_Ici (Q : ℝ) (hQ : 0 < Q)
    (a s : ℝ) :
    parabolicTimeOrderIso Q hQ a '' Ici s = Ici (Q * s + a) := by
  simpa only [parabolicTimeOrderIso_apply] using
    (parabolicTimeOrderIso Q hQ a).image_Ici s

/-- **Math.** A positive affine time change carries a closed lower ray to the
corresponding closed lower ray. -/
theorem parabolicTimeOrderIso_image_Iic (Q : ℝ) (hQ : 0 < Q)
    (a s : ℝ) :
    parabolicTimeOrderIso Q hQ a '' Iic s = Iic (Q * s + a) := by
  simpa only [parabolicTimeOrderIso_apply] using
    (parabolicTimeOrderIso Q hQ a).image_Iic s

/-- **Math.** Reparameterize a compatible space-time map by the positive
affine change of time `s = Q t + a`. -/
def GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    N × ℝ → N :=
  fun z => e.toFun (z.1, (parabolicTimeOrderIso Q hQ a).symm z.2)

/-- **Math.** Affine time reparameterization does not change the image of a
compatible space-time map; it only changes the time coordinate on its domain. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam_image
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    e.affineTimeReparam n Q hQ a ''
        (C ×ˢ (parabolicTimeOrderIso Q hQ a '' J)) = e.image n := by
  ext y
  constructor
  · rintro ⟨⟨x, s⟩, ⟨hx, ⟨t, ht, rfl⟩⟩, rfl⟩
    refine ⟨(x, t), ⟨hx, ht⟩, ?_⟩
    have hqt : Q * t / Q = t := by
      field_simp [hQ.ne']
    simp [GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam, hqt]
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    refine ⟨(x, parabolicTimeOrderIso Q hQ a t),
      ⟨hx, ⟨t, ht, rfl⟩⟩, ?_⟩
    have hqt : Q * t / Q = t := by
      field_simp [hQ.ne']
    simp [GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam, hqt]

/-- **Math.** The scaled time function `t' = Q t`. -/
def GeneralizedSpaceTime.scaledTime
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) : N → ℝ :=
  Q • S.time

/-- **Math.** The translated time function `t' = t + a`. -/
def GeneralizedSpaceTime.translatedTime
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) : N → ℝ :=
  fun x => S.time x + a

/-- **Math.** The time vector after parabolic rescaling, `chi' = Q⁻¹ chi`. -/
def GeneralizedSpaceTime.scaledTimeVector
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) :
    SmoothVectorField (modelWithCornersEuclideanHalfSpace n.succ) N :=
  Q⁻¹ • S.timeVector

/-- **Math.** Along the affine reparameterization of a compatible embedding,
the scaled-and-translated time coordinate is exactly the new parameter. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam_time
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    {x : N} {s : ℝ} (hx : x ∈ C)
    (hs : s ∈ parabolicTimeOrderIso Q hQ a '' J) :
    Q * S.time (e.affineTimeReparam n Q hQ a (x, s)) + a = s := by
  obtain ⟨t, ht, rfl⟩ := hs
  simp only [GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam,
    parabolicTimeOrderIso_apply, parabolicTimeOrderIso_symm_apply]
  have harg : (Q * t + a - a) / Q = t := by
    field_simp [hQ.ne']
    ring
  rw [harg]
  rw [e.time_toFun n hx ht]

/-! The transformed time image is exact whenever the spatial source is
nonempty. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam_time_image
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (hC : C.Nonempty)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (fun y => Q * S.time y + a) ''
        (e.affineTimeReparam n Q hQ a ''
          (C ×ˢ (parabolicTimeOrderIso Q hQ a '' J))) =
      parabolicTimeOrderIso Q hQ a '' J := by
  rw [e.affineTimeReparam_image n Q hQ a]
  ext s
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp [e.time_toFun n hx ht, parabolicTimeOrderIso_apply]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := hC
    refine ⟨e.toFun (x, t), ?_, ?_⟩
    · exact ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    · simp [e.time_toFun n hx ht, parabolicTimeOrderIso_apply]

/-- **Math.** Compatible flow lines remain integral curves after the positive
affine time change `s = Q t + a`, with the scaled time vector `Q⁻¹ chi`. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.isIntegralCurveOn_affineTimeReparam
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    {x : N} (hx : x ∈ C) :
    IsMIntegralCurveOn
      (fun s => e.affineTimeReparam n Q hQ a (x, s))
      (fun y => S.scaledTimeVector n Q y)
      (parabolicTimeOrderIso Q hQ a '' J) := by
  have hscale := (e.isIntegralCurveOn x hx).comp_mul Q⁻¹
  have htranslate := hscale.comp_add (-a)
  have hset :
      {t : ℝ | t + (-a) ∈ {u : ℝ | u * Q⁻¹ ∈ J}} =
        parabolicTimeOrderIso Q hQ a '' J := by
    ext t
    constructor
    · intro ht
      change (t - a) * Q⁻¹ ∈ J at ht
      refine ⟨(t - a) / Q, ht, ?_⟩
      simp only [parabolicTimeOrderIso_apply]
      field_simp [hQ.ne']
      ring
    · rintro ⟨u, hu, rfl⟩
      simp only [parabolicTimeOrderIso_apply]
      change (Q * u + a + -a) * Q⁻¹ ∈ J
      have heq : (Q * u + a + -a) * Q⁻¹ = u := by
        field_simp [hQ.ne']
        ring
      rw [heq]
      exact hu
  rw [hset] at htranslate
  have hfunc :
      (fun s => e.affineTimeReparam n Q hQ a (x, s)) =
        ((fun s => e.toFun (x, s)) ∘ (fun z => z * Q⁻¹)) ∘
          (fun z => z + (-a)) := by
    funext s
    simp only [GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam,
      Function.comp_apply, parabolicTimeOrderIso_symm_apply]
    congr 1
  have hvector :
      (fun y => S.scaledTimeVector n Q y) =
        Q⁻¹ • (fun y => S.timeVector y) := by
    funext y
    rfl
  rw [hfunc, hvector]
  exact htranslate

@[simp]
theorem GeneralizedSpaceTime.scaledTime_apply
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (x : N) :
    S.scaledTime n Q x = Q * S.time x :=
  rfl

@[simp]
theorem GeneralizedSpaceTime.translatedTime_apply
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) (x : N) :
    S.translatedTime n a x = S.time x + a :=
  rfl

@[simp]
theorem GeneralizedSpaceTime.scaledTimeVector_apply
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (x : N) :
    S.scaledTimeVector n Q x = Q⁻¹ • S.timeVector x :=
  rfl

theorem GeneralizedSpaceTime.scaledTime_contMDiff
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) :
    ContMDiff (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) ∞ (S.scaledTime n Q) :=
  contMDiff_const.mul S.time_contMDiff

theorem GeneralizedSpaceTime.translatedTime_contMDiff
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) :
    ContMDiff (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) ∞ (S.translatedTime n a) :=
  S.time_contMDiff.add contMDiff_const

/-- **Math.** The differential of the scaled time function, regarded as a
real-valued linear functional. -/
def GeneralizedSpaceTime.scaledTimeDifferential
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (x : N) :
    TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ] ℝ :=
  mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
    (modelWithCornersSelf ℝ ℝ) (S.scaledTime n Q) x

/-- **Math.** The differential of the translated time function, regarded as
a real-valued linear functional. -/
def GeneralizedSpaceTime.translatedTimeDifferential
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) (x : N) :
    TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ] ℝ :=
  mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
    (modelWithCornersSelf ℝ ℝ) (S.translatedTime n a) x

/-- **Math.** The differential of scaled time is `Q dtime`. -/
theorem GeneralizedSpaceTime.scaledTimeDifferential_eq
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (x : N) :
    S.scaledTimeDifferential n Q x =
      Q • S.timeDifferential (n := n) x := by
  exact const_smul_mfderiv
    (S.time_contMDiff.mdifferentiableAt (by simp)) Q

/-- **Math.** Time translation does not change the time differential. -/
theorem GeneralizedSpaceTime.translatedTimeDifferential_eq
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) (x : N) :
    S.translatedTimeDifferential n a x =
      S.timeDifferential (n := n) x := by
  change mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) (S.time + fun _ => a) x =
    S.timeDifferential (n := n) x
  rw [mfderiv_add (S.time_contMDiff.mdifferentiableAt (by simp))
    (mdifferentiableAt_const (c := a)), mfderiv_const]
  exact add_zero _

/-- **Math.** The inverse scaling of the time vector exactly compensates for
the scaling of time: `d(Q t)(Q⁻¹ chi) = 1`. -/
theorem GeneralizedSpaceTime.scaledTimeDifferential_scaledTimeVector
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (x : N) :
    S.scaledTimeDifferential n Q x (S.scaledTimeVector n Q x) = 1 := by
  rw [S.scaledTimeDifferential_eq (n := n) Q x]
  simp only [S.scaledTimeVector_apply (n := n) Q x,
    smul_apply, map_smul,
    S.timeDifferential_timeVector (n := n) x, smul_eq_mul]
  field_simp [hQ.ne']

/-- **Math.** Time translation leaves the normalization `dtime(chi) = 1`
unchanged. -/
theorem GeneralizedSpaceTime.translatedTimeDifferential_timeVector
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) (x : N) :
    S.translatedTimeDifferential n a x (S.timeVector x) = 1 := by
  rw [S.translatedTimeDifferential_eq (n := n) a x,
    S.timeDifferential_timeVector (n := n) x]

/-- **Math.** The zero-extended horizontal metric is nonnegative on every
ambient tangent vector. -/
theorem GeneralizedSpaceTime.HorizontalMetric.inner_self_nonneg
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    0 ≤ G.inner x v v := by
  rw [← G.horizontalProjection_both n x v v]
  let w := S.horizontalProjectionAt n x v
  by_cases hw : w = 0
  · simp [w, hw]
  · exact (G.pos x w
      (S.timeDifferential_horizontalProjectionAt (n := n) x v) hw).le

/-- **Math.** Positive constant rescaling `G |-> Q G` of a horizontal metric. -/
def GeneralizedSpaceTime.HorizontalMetric.constScale
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) : S.HorizontalMetric n where
  inner x := Q • G.inner x
  symm x v w := by
    simp only [smul_apply, smul_eq_mul]
    rw [G.symm x v w]
  timeVector_null x v := by
    simp only [smul_apply, smul_eq_mul, G.timeVector_null,
      mul_zero]
  pos x v hv hv0 := by
    simp only [smul_apply, smul_eq_mul]
    exact mul_pos hQ (G.pos x v hv hv0)
  smooth := G.smooth.const_smul_section

@[simp]
theorem GeneralizedSpaceTime.HorizontalMetric.constScale_inner
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (x : N)
    (v w : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    (G.constScale n Q hQ).inner x v w = Q * G.inner x v w :=
  rfl

/-- **Math.** A local chart realization of a horizontal metric transports
positive constant scaling to the chart metric family. -/
theorem GeneralizedSpaceTimeLocalChart.realizesHorizontalMetric_constScale
    [NeZero n] {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (G : S.HorizontalMetric n)
    (g : ℝ → RiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (c.spatialOpens n))
    (hG : c.RealizesHorizontalMetric n G g) (Q : ℝ) (hQ : 0 < Q) :
    c.RealizesHorizontalMetric n (G.constScale n Q hQ)
      (fun t => rescaledMetric (g t) Q hQ) := by
  intro t ht p v w
  rw [rescaledMetric_metricInner, hG t ht p v w]
  exact (G.constScale_inner n Q hQ _ _ _).symm

end MorganTianLib

end
