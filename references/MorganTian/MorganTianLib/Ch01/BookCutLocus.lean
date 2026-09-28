import MorganTianLib.Ch01.CutLocus
import MorganTianLib.Ch01.ExpBallDiffeo

/-!
# The differential-geometric cut locus and injectivity radius

The metric cut-time API in `CutLocus.lean` is the form used by the later
volume arguments.  Morgan--Tian first introduce the equivalent differential
geometric formulation, however: the segment domain consists of vectors giving
the unique minimizing radial geodesic and a local diffeomorphism of `exp_p`,
and the cut locus is the complement of its image.  These definitions keep the
two formulations distinct until the comparison theorem relating them is
proved.
-/

open Set Metric Riemannian
open scoped ContDiff Manifold Topology Bundle ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M]

/-- **Math.** The differential-geometric predicate for a radial vector to lie in the
book's segment domain: the radial geodesic is minimizing, its endpoint has no
second minimizing initial velocity, and the exponential map is a local
diffeomorphism at the vector. -/
def bookSegmentDomain (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) : Set (TangentSpace I p) :=
  {v | IsMinimizingUpTo (E := E) (I := I) g hg p v 1 ∧
    (∀ w : TangentSpace I p,
      IsMinimizingUpTo (E := E) (I := I) g hg p w 1 →
        expMapGlobal (I := I) g hg p w = expMapGlobal (I := I) g hg p v → w = v) ∧
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun w : E => expMapGlobal (I := I) g hg p (w : TangentSpace I p)) (v : E)}

/-- **Math.** The differential-geometric cut locus, namely the complement of the image
of the book's segment domain under the exponential map. -/
def bookCutLocus (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) : Set M :=
  (Set.univ : Set M) \
    expMapGlobal (I := I) g hg p '' bookSegmentDomain (I := I) g hg p

/-- **Math.** The predicate that the exponential map is a diffeomorphism onto its image
on the open tangent-space ball of radius `r`.  The inverse is stated on the
image, which avoids choosing a global inverse outside that image. -/
def expBallDiffeomorph (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) (r : ℝ) : Prop :=
  0 < r ∧
    Set.InjOn
      (fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p))
      (Metric.ball (0 : E) r) ∧
    ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p))
      (Metric.ball (0 : E) r) ∧
    IsOpen
      ((fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p)) ''
        Metric.ball (0 : E) r) ∧
    ∃ inv : M → E,
      ContMDiffOn I 𝓘(ℝ, E) ∞ inv
        ((fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p)) ''
          Metric.ball (0 : E) r) ∧
      ∀ v ∈ Metric.ball (0 : E) r,
        inv (expMapGlobal (I := I) g hg p (v : TangentSpace I p)) = v

/-- **Math.** The book's injectivity radius: the supremum of the positive radii on
which `exp_p` is a diffeomorphism into the manifold. -/
def bookInjectivityRadius (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // expBallDiffeomorph (I := I) g hg p r},
    ENNReal.ofReal (r : ℝ)

end MorganTianLib

end
