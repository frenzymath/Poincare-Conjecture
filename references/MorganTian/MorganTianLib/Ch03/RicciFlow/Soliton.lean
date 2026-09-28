import MorganTianLib.Ch03.RicciFlow.Basic
import MorganTianLib.Ch02.Gradient
import MorganTianLib.Ch02.Laplacian

/-!
# Morgan--Tian Ch. 3 - Ricci solitons

This file formalizes the definitions and differential-geometric identities in
the soliton subsection of Chapter 3.  A `RicciSoliton` is an actual Ricci flow
whose time slices are pullbacks of the initial metric up to a positive constant
factor.  The infinitesimal construction is recorded separately by
`IsSolitonGenerator`.

The main proved bridge is the source identity
`L_(grad f) g = 2 Hess_g f`.  Consequently the gradient shrinker equation
`-Ric = Hess f - lambda g` is exactly the general soliton generator equation
with `X = grad f`.  Constructing the time-dependent diffeomorphisms and proving
that their scaled pullbacks solve Ricci flow is the subsequent
`claim:soliton-generation`; it is not assumed here.

Reference: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 3,
"Solitons".
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian Set

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ## Self-similar Ricci flows -/

/-- **Math.** A Ricci soliton on a time interval `J` beginning at `0`.

Besides the Ricci-flow contract, this records a positive scale `sigma(t)` and
diffeomorphisms `phi_t` satisfying
`g(t) = sigma(t) phi_t^* g(0)`.  The last field states this equality on every
tangent fiber, which is the defining formula for pullback metrics and keeps
all positivity and interval hypotheses explicit.

Blueprint: the unlabelled definition immediately before
`claim:soliton-generation`. -/
structure RicciSoliton (g : ℝ → RiemannianMetric I M) (J : Set ℝ) where
  flow : IsRicciFlowOn g J
  initial : IsInitialTime J 0
  scale : ℝ → ℝ
  scale_pos : ∀ t ∈ J, 0 < scale t
  diffeomorphism : ℝ → Diffeomorph I I M M ∞
  selfSimilar : ∀ t ∈ J, ∀ (p : M) (v w : TangentSpace I p),
    (g t).metricInner p v w =
      scale t * (g 0).metricInner (diffeomorphism t p)
        (mfderiv I I (diffeomorphism t) p v)
        (mfderiv I I (diffeomorphism t) p w)

/-- **Math.** A presentation of a Ricci soliton is shrinking when its scale
has negative derivative at every time.  Within-derivatives give the intended
one-sided derivative at the initial endpoint.

Blueprint: the unlabelled shrinking-soliton definition immediately before
`claim:soliton-generation`. -/
def RicciSoliton.IsShrinking {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (S : RicciSoliton g J) : Prop :=
  ∀ t ∈ J, ∃ d : ℝ, d < 0 ∧ HasDerivWithinAt S.scale d J t

/-! ## The infinitesimal soliton equation -/

/-- **Math.** The value of the Lie derivative of a metric along a smooth
vector field, evaluated on tangent vectors:
`(L_X g)(v,w) = g(nabla_v X,w) + g(v,nabla_w X)`.

The covariant derivatives are evaluated using arbitrary global extensions of
`v` and `w`; tensoriality of a connection in its first slot makes the value
independent of those extensions.

Blueprint: Equation `(soliton)` and `prop:gradient-shrinking-soliton-generation`.
-/
def metricLieDerivativeAt (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (p : M) (v w : TangentSpace I p) : ℝ :=
  g.metricInner p
      ((g.leviCivitaConnection.cov (extendVector p v) X) p) w +
    g.metricInner p v
      ((g.leviCivitaConnection.cov (extendVector p w) X) p)

omit [I.Boundaryless] in
/-- **Math.** The metric Lie derivative is symmetric in its two tangent
arguments. -/
theorem metricLieDerivativeAt_symm (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (p : M) (v w : TangentSpace I p) :
    metricLieDerivativeAt g X p v w = metricLieDerivativeAt g X p w v := by
  unfold metricLieDerivativeAt
  rw [g.metricInner_comm p
      ((g.leviCivitaConnection.cov (extendVector p v) X) p) w,
    g.metricInner_comm p v
      ((g.leviCivitaConnection.cov (extendVector p w) X) p)]
  exact add_comm _ _

/-- **Math.** The soliton generator equation
`-Ric(g) = (1/2) L_X g - lambda g`, with all tensor arguments explicit.

Blueprint: Equation `(soliton)` preceding `claim:soliton-generation`. -/
def IsSolitonGenerator (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (lambda : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p),
    -(ricciTensorAt g p v w) =
      (1 / 2 : ℝ) * metricLieDerivativeAt g X p v w -
        lambda * g.metricInner p v w

/-- **Math.** The fundamental gradient identity
`L_(grad f) g = 2 Hess_g f`, pointwise on arbitrary tangent vectors.

This is the precise bridge used in Morgan--Tian's proof that the gradient
shrinker equation is a soliton equation.

Blueprint: `prop:gradient-shrinking-soliton-generation`, using
`lem:hessian-symmetric`. -/
theorem metricLieDerivativeAt_gradientField
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M)
    (v w : TangentSpace I p) :
    metricLieDerivativeAt g (gradientField g f hf) p v w =
      2 * hessianAt g.leviCivitaConnection f p v w := by
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hvw :
      g.metricInner p
          ((g.leviCivitaConnection.cov (extendVector p v)
            (gradientField g f hf)) p) w =
        hessianAt g.leviCivitaConnection f p v w := by
    calc
      g.metricInner p
          ((g.leviCivitaConnection.cov (extendVector p v)
            (gradientField g f hf)) p) w =
          g.metricInner p
            ((g.leviCivitaConnection.cov (extendVector p v)
              (gradientField g f hf)) p) ((extendVector p w) p) := by
                rw [extendVector_apply]
      _ = hessian g.leviCivitaConnection f
            (extendVector p v) (extendVector p w) p :=
          (hessian_eq_metricInner_cov_gradientField g
            g.leviCivitaConnection hLC.2 hf
            (extendVector p v) (extendVector p w) p).symm
      _ = hessianAt g.leviCivitaConnection f p v w := rfl
  have hwv :
      g.metricInner p v
          ((g.leviCivitaConnection.cov (extendVector p w)
            (gradientField g f hf)) p) =
        hessianAt g.leviCivitaConnection f p w v := by
    rw [g.metricInner_comm p v]
    calc
      g.metricInner p
          ((g.leviCivitaConnection.cov (extendVector p w)
            (gradientField g f hf)) p) v =
          g.metricInner p
            ((g.leviCivitaConnection.cov (extendVector p w)
              (gradientField g f hf)) p) ((extendVector p v) p) := by
                rw [extendVector_apply]
      _ = hessian g.leviCivitaConnection f
            (extendVector p w) (extendVector p v) p :=
          (hessian_eq_metricInner_cov_gradientField g
            g.leviCivitaConnection hLC.2 hf
            (extendVector p w) (extendVector p v) p).symm
      _ = hessianAt g.leviCivitaConnection f p w v := rfl
  unfold metricLieDerivativeAt
  rw [hvw, hwv,
    hessianAt_symm g.leviCivitaConnection hLC.1 hf p w v]
  ring

/-- **Math.** The source gradient-shrinker equation
`-Ric(g) = Hess_g f - lambda g`, including smoothness of `f` and the sign
`lambda > 0` required for a shrinking soliton.

Blueprint: Equation `(GSS)` in
`prop:gradient-shrinking-soliton-generation`. -/
def IsGradientShrinkerPotential (g : RiemannianMetric I M)
    (f : M → ℝ) (lambda : ℝ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ 0 < lambda ∧
    ∀ (p : M) (v w : TangentSpace I p),
      -(ricciTensorAt g p v w) =
        hessianAt g.leviCivitaConnection f p v w -
          lambda * g.metricInner p v w

/-- **Math.** Any solution of the gradient shrinker equation supplies the
general soliton generator equation with vector field `grad f`.

This proves the infinitesimal step of
`prop:gradient-shrinking-soliton-generation`; the remaining step is the
global construction in `claim:soliton-generation`.

Blueprint: `prop:gradient-shrinking-soliton-generation`. -/
theorem IsGradientShrinkerPotential.isSolitonGenerator
    {g : RiemannianMetric I M} {f : M → ℝ} {lambda : ℝ}
    (h : IsGradientShrinkerPotential g f lambda) :
    IsSolitonGenerator g (gradientField g f h.1) lambda := by
  intro p v w
  rw [metricLieDerivativeAt_gradientField g h.1 p v w]
  have heq := h.2.2 p v w
  rw [heq]
  ring

/-- **Math.** A metric and potential generate a gradient shrinking soliton
when they satisfy the source Hessian equation for some positive `lambda`.
The existence of the resulting flow is the content, rather than a premise,
of `prop:gradient-shrinking-soliton-generation`.

Blueprint: `def:gradient-shrinking-soliton-generator`. -/
def GeneratesGradientShrinkingSoliton (g : RiemannianMetric I M)
    (f : M → ℝ) : Prop :=
  ∃ lambda : ℝ, IsGradientShrinkerPotential g f lambda

/-- **Math.** A gradient shrinking Ricci soliton consists of a shrinking
self-similar Ricci flow and a smooth potential whose gradient satisfies the
soliton generator equation with a positive constant.

Blueprint: `def:gradient-shrinking-soliton`. -/
structure GradientShrinkingRicciSoliton
    (g : ℝ → RiemannianMetric I M) (J : Set ℝ)
    extends RicciSoliton g J where
  shrinking : toRicciSoliton.IsShrinking
  potential : M → ℝ
  potential_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ potential
  lambda : ℝ
  lambda_pos : 0 < lambda
  generator : IsSolitonGenerator (g 0)
    (gradientField (g 0) potential potential_smooth) lambda

/-! ## The canonical scale and time interval -/

/-- **Math.** The scale in the soliton construction:
`sigma(t) = 1 - 2 lambda t`. -/
def solitonScale (lambda t : ℝ) : ℝ :=
  1 - 2 * lambda * t

/-! The time change below is the scalar part of the source construction.  If
`lambda ≠ 0`, the autonomous flow of `X` is reparametrized by
`-log (sigma(t)) / (2 lambda)`; the zero-`lambda` branch is the identity. -/

/-- **Math.** Time reparametrization for the vector field
`Y_t = X / solitonScale lambda t` in the soliton construction. -/
def solitonFlowTime (lambda t : ℝ) : ℝ :=
  if lambda = 0 then t
  else -(Real.log (solitonScale lambda t)) / (2 * lambda)

@[simp] theorem solitonFlowTime_zero (lambda : ℝ) :
    solitonFlowTime lambda 0 = 0 := by
  by_cases hl : lambda = 0
  · simp [solitonFlowTime, hl]
  · simp [solitonFlowTime, hl, solitonScale]

/-- **Math.** The source time interval: `[0, infinity)` for `lambda <= 0`,
and `[0, (2 lambda)^(-1))` for `lambda > 0`. -/
def solitonTimeSet (lambda : ℝ) : Set ℝ :=
  if 0 < lambda then Ico 0 (2 * lambda)⁻¹ else Ici 0

@[simp] theorem solitonScale_zero (lambda : ℝ) :
    solitonScale lambda 0 = 1 := by
  simp [solitonScale]

/-- **Math.** The canonical scale has constant derivative `-2 lambda`. -/
theorem hasDerivAt_solitonScale (lambda t : ℝ) :
    HasDerivAt (solitonScale lambda) (-2 * lambda) t := by
  have h₂ := hasDerivAt_const_mul (x := t) (2 * lambda)
  have h := h₂.const_sub (1 : ℝ)
  change HasDerivAt (fun s : ℝ => 1 - 2 * lambda * s) (-2 * lambda) t
  simpa only [sub_eq_add_neg, solitonScale, Pi.add_apply, Pi.neg_apply,
    neg_mul, mul_one, zero_sub] using h

/-- **Math.** On the positive-scale region, the soliton time change has
derivative `1 / sigma(t)`.  Thus an autonomous `X`-flow reparametrized by
`solitonFlowTime lambda` has the source velocity `X / sigma(t)`. -/
theorem hasDerivAt_solitonFlowTime {lambda t : ℝ}
    (hscale : 0 < solitonScale lambda t) :
    HasDerivAt (fun s => solitonFlowTime lambda s)
      (1 / solitonScale lambda t) t := by
  by_cases hl : lambda = 0
  · subst lambda
    have hfun : (fun s : ℝ => solitonFlowTime 0 s) = id := by
      funext s
      simp [solitonFlowTime]
    rw [hfun]
    simpa [solitonScale] using (hasDerivAt_id t)
  · have hfun : (fun s : ℝ => solitonFlowTime lambda s) =
        (fun s : ℝ => -(Real.log (solitonScale lambda s)) / (2 * lambda)) := by
      funext s
      simp [solitonFlowTime, hl]
    rw [hfun]
    have hlog := (hasDerivAt_solitonScale lambda t).log (ne_of_gt hscale)
    have hneg : HasDerivAt (fun s : ℝ => -Real.log (solitonScale lambda s))
        (-( (-2 * lambda) / solitonScale lambda t)) t := hlog.neg
    have hdiv := hneg.div_const (2 * lambda)
    have hcoef :
        -((-2 * lambda) / solitonScale lambda t) / (2 * lambda) =
          1 / solitonScale lambda t := by
      field_simp [hl]
    rw [hcoef] at hdiv
    exact hdiv

/-- **Math.** The canonical scale is positive throughout its source time
interval. -/
theorem solitonScale_pos_of_mem {lambda t : ℝ}
    (ht : t ∈ solitonTimeSet lambda) :
    0 < solitonScale lambda t := by
  by_cases hlambda : 0 < lambda
  · rw [solitonTimeSet, if_pos hlambda] at ht
    have htwo : 0 < 2 * lambda := mul_pos (by norm_num) hlambda
    have hprod : (2 * lambda) * t < 1 := by
      have h := mul_lt_mul_of_pos_left ht.2 htwo
      exact h.trans_eq (mul_inv_cancel₀ htwo.ne')
    unfold solitonScale
    linarith
  · rw [solitonTimeSet, if_neg hlambda] at ht
    have hlambda' : lambda ≤ 0 := le_of_not_gt hlambda
    have hmul : lambda * t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlambda' ht
    unfold solitonScale
    nlinarith

/-- **Math.** The time-change derivative holds throughout the source soliton
interval. -/
theorem hasDerivAt_solitonFlowTime_of_mem {lambda t : ℝ}
    (ht : t ∈ solitonTimeSet lambda) :
    HasDerivAt (fun s => solitonFlowTime lambda s)
      (1 / solitonScale lambda t) t :=
  hasDerivAt_solitonFlowTime (solitonScale_pos_of_mem ht)

/-- **Math.** For `lambda > 0`, the canonical scale has negative derivative
at every time and hence is shrinking on the source interval. -/
theorem solitonScale_isShrinking {lambda : ℝ} (hlambda : 0 < lambda) :
    ∀ t ∈ solitonTimeSet lambda,
      ∃ d : ℝ, d < 0 ∧ HasDerivWithinAt (solitonScale lambda) d
        (solitonTimeSet lambda) t := by
  intro t ht
  refine ⟨-2 * lambda, by nlinarith, ?_⟩
  exact (hasDerivAt_solitonScale lambda t).hasDerivWithinAt

end MorganTianLib

end
