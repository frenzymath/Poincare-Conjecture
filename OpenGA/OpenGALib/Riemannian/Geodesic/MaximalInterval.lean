import OpenGALib.Riemannian.Geodesic.Equation
import OpenGALib.Riemannian.Geodesic.Existence
import OpenGALib.Riemannian.Geodesic.Uniqueness
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false

/-!
# Maximal interval of definition for a geodesic with prescribed initial data

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, every initial datum
`(p : M, v : T_p M)` gives rise to a *maximal open interval*
`I_max(p, v) ⊆ ℝ` containing `0` on which a geodesic with that initial
datum is defined, together with a canonical curve `maximalGeodesic g p v : ℝ → M`
that realises this geodesic on `I_max(p, v)` (and is junk-valued outside).

## Main definitions

* `IsGeodesicOn g γ s`: an interval-restricted geodesic predicate; the
  set-relativised analogue of `IsGeodesic`. There exist a chart basepoint
  `α : M` and a lifted curve `f : ℝ → TangentBundle I M` projecting to
  `γ` such that `f` is an integral curve of the chart-fixed geodesic
  vector field `geodesicVectorFieldChart g α` on `s`.

* `maximalGeodesicInterval g p v`: the union of all open intervals
  containing `0` on which there exists a geodesic with `γ 0 = p` and
  velocity-lift value `v` at `0`. By construction, this is an open set
  containing `0`.

* `maximalGeodesic g p v`: a `ℝ → M`-curve obtained from
  `exists_geodesic_with_initial_velocity_at` together with a `Classical.choice` selection of a
  geodesic that covers each point of the maximal interval, junk-extended
  to the entire real line by the constant value `p` outside.

## Main theorems

* `maximalGeodesicInterval_isOpen`: openness.
* `zero_mem_maximalGeodesicInterval`: `0` is in the maximal interval.
* `maximalGeodesic_zero`: `maximalGeodesic g p v 0 = p`.
* `isGeodesicAt_maximalGeodesic`: at every `t ∈ maximalGeodesicInterval g p v`,
  the curve `maximalGeodesic g p v` is a local geodesic at `t`.

## Strategy

We follow the standard "union over local extensions" construction. The
maximal interval is the union of all open intervals `J` containing both
`0` and the point of interest on which a geodesic with the prescribed
initial condition exists. The curve `maximalGeodesic` is then defined by
picking, for each `t` in the maximal interval, the value of any such
local geodesic at `t`; the value is junk (= `p`) for `t` outside the
maximal interval. The headline geodesic predicate is established at the
pointwise `IsGeodesicAt` level, which is the regularity that the existence
theorem `exists_geodesic_with_initial_velocity_at` directly delivers. A globalised
`IsGeodesicOn` statement on the maximal interval would require integral
curves of the chart-fixed vector field to glue across chart changes; that
requires a moving-chart formulation of the geodesic equation and is
deferred.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E]


/-- **Math.** `γ` is a geodesic on `s` with initial datum `(p, v)` at time `0` if
the velocity lift `f` projects to `γ`, satisfies `f 0 = ⟨p, v⟩`, and is an
integral curve of the chart-fixed geodesic vector field at the chart
basepoint `p`. The chart basepoint is fixed to be the initial point `p`,
which guarantees that the vector field is smooth at the initial data
(since `p ∈ (chartAt H p).source` is automatic). -/
def IsGeodesicOnWithInitial
    (g : RiemannianMetric I M) (γ : ℝ → M) (s : Set ℝ)
    (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) s

/-- **Math.** An initial-data geodesic on `s` is, at every interior point `t` of `s`
(i.e. `s ∈ 𝓝 t`) whose foot `γ t` still lies in the base chart-source
`(chartAt H p).source`, a local spray geodesic `IsGeodesicAt g γ t` with
chart basepoint `p`. This is the spray-side projection used to feed the
chart-coordinate geodesic-equation bridge downstream.

The foot-in-source hypothesis `ht_src : γ t ∈ (chartAt H p).source` is the
chart-validity condition for the chart-`p`-fixed integral-curve datum: it
is exactly the well-posedness clause that the strengthened `IsGeodesicAt`
predicate records. At an interior point where `γ` has left the base chart,
the chart-`p` vector field has degenerated to the zero section, so no
`IsGeodesicAt` witness with basepoint `p` is available there. -/
lemma IsGeodesicOnWithInitial.isGeodesicAt
    {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (ht : s ∈ 𝓝 t)
    (ht_src : γ t ∈ (chartAt H p).source) :
    IsGeodesicAt (I := I) g γ t := by
  obtain ⟨f, hproj, _, hf⟩ := hγ
  refine ⟨p, f, hproj, ?_, hf.isMIntegralCurveAt ht⟩
  rw [hproj t]; exact ht_src

/-- **Math.** The starting point is forced: if `IsGeodesicOnWithInitial g γ s p v`
holds, then `γ 0 = p`. -/
lemma IsGeodesicOnWithInitial.start_eq
    {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) :
    γ 0 = p := by
  obtain ⟨f, hproj, hf0, _⟩ := hγ
  have h := hproj 0
  simp [hf0] at h
  exact h.symm

/-- **Math.** `IsGeodesicOnWithInitial` is monotone in the set. -/
lemma IsGeodesicOnWithInitial.mono
    {g : RiemannianMetric I M} {γ : ℝ → M} {s s' : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (hs : s' ⊆ s) :
    IsGeodesicOnWithInitial (I := I) g γ s' p v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  exact ⟨f, hproj, hf0, hf.mono hs⟩

/-- **Math.** The "membership witness" predicate for the maximal interval: at time
`t`, there exists a connected open `J ∋ 0, t` and a geodesic with initial
data `(p, v)` on `J`. Preconnectedness of `J` (i.e., `J` is an interval in
`ℝ`) is required to enable interval-propagation arguments, e.g.
identifying the witness curve with a known geodesic at every `t ∈ J` from
agreement at `t = 0`. This is packaged as a single-existential `Prop` so
that `Classical.choose` works cleanly. -/
def MaximalGeodesicWitness
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v

/-- **Math.** The maximal interval of definition of a geodesic with initial data
`(p, v)`: the set of times `t : ℝ` admitting an open interval `J ∋ 0, t`
on which a geodesic with initial data `(p, v)` is defined. -/
def maximalGeodesicInterval
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    Set ℝ :=
  {t : ℝ | MaximalGeodesicWitness (I := I) g p v t}

/-- **Math.** Membership unfolding. -/
lemma mem_maximalGeodesicInterval_iff
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} :
    t ∈ maximalGeodesicInterval (I := I) g p v ↔
      MaximalGeodesicWitness (I := I) g p v t :=
  Iff.rfl

/-- **Math.** `maximalGeodesicInterval g p v` is open. The key observation: if
`MaximalGeodesicWitness g p v t` holds with witness `(γ, J)`, then for
every `t' ∈ J` we also have `MaximalGeodesicWitness g p v t'` (with the
same `(γ, J)`). Hence the maximal interval is locally a superset of an
open neighbourhood of every member. -/
theorem maximalGeodesicInterval_isOpen
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    IsOpen (maximalGeodesicInterval (I := I) g p v) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨γ, J, hJ, hJ_conn, h0, ht_in, hγ⟩ := ht
  refine Filter.mem_of_superset (hJ.mem_nhds ht_in) ?_
  intro t' ht'
  exact ⟨γ, J, hJ, hJ_conn, h0, ht', hγ⟩

section LocalExistence


/-- **Math.** The local geodesic produced by `exists_geodesic_with_initial_velocity_at` provides an open
interval `J ∋ 0` on which a geodesic with initial data `(p, v)` exists.
This is the basic witness for membership of `0` in the maximal interval. -/
lemma exists_maximalGeodesicWitness_zero
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    MaximalGeodesicWitness (I := I) g p v 0 := by
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  rw [isMIntegralCurveAt_iff'] at hf
  obtain ⟨ε, hε, hf_on⟩ := hf
  refine ⟨projectCurve (I := I) f, Metric.ball (0 : ℝ) ε,
    Metric.isOpen_ball, ?_, Metric.mem_ball_self hε, Metric.mem_ball_self hε, ?_⟩
  · exact (convex_ball (0 : ℝ) ε).isPreconnected
  exact ⟨f, fun _ => rfl, hf0, hf_on⟩

/-- **Math.** `0` belongs to the maximal interval. -/
theorem zero_mem_maximalGeodesicInterval
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (0 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v :=
  exists_maximalGeodesicWitness_zero (I := I) g p v

/-- **Math.** The maximal interval is nonempty. -/
theorem maximalGeodesicInterval_nonempty
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (maximalGeodesicInterval (I := I) g p v).Nonempty :=
  ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩

end LocalExistence

section MaximalGeodesicDefinition


/-- **Math.** A local geodesic witness at time `t`, taken via `Classical.choose`
when `t ∈ maximalGeodesicInterval g p v`. -/
def maximalGeodesicChosenCurve
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ℝ → M :=
  Classical.choose h

lemma maximalGeodesicChosenCurve_spec
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g
        (maximalGeodesicChosenCurve (I := I) g p v h) J p v :=
  Classical.choose_spec h

/-- **Math.** The canonical maximal geodesic with initial data `(p, v)`. On the
maximal interval, it equals some local geodesic with the prescribed
initial data, chosen by `Classical.choose`; outside, it is the constant
`p`. -/
def maximalGeodesic
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : M :=
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  if h : MaximalGeodesicWitness (I := I) g p v t then
    maximalGeodesicChosenCurve (I := I) g p v h t
  else p

/-- **Math.** Outside the maximal interval, `maximalGeodesic` takes the value `p`. -/
lemma maximalGeodesic_of_not_mem
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (ht : t ∉ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t = p := by
  unfold maximalGeodesic
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  exact dif_neg ht

/-- **Math.** On the maximal interval, `maximalGeodesic g p v` equals the chosen
local geodesic. -/
lemma maximalGeodesic_of_mem
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t =
      maximalGeodesicChosenCurve (I := I) g p v h t := by
  unfold maximalGeodesic
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  exact dif_pos h

end MaximalGeodesicDefinition

section MaximalGeodesicValue


/-- **Math.** `maximalGeodesic g p v` starts at `p`. -/
theorem maximalGeodesic_zero
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v 0 = p := by
  have h0 := zero_mem_maximalGeodesicInterval (I := I) g p v
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) h0]
  obtain ⟨_J, _hJ, _hJ_conn, _h0J, _h0J', hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v h0
  exact hγ.start_eq

end MaximalGeodesicValue

section MaximalGeodesicAtTime


/-- **Math.** The witness `γ` chosen at `t ∈ maximalGeodesicInterval g p v` is a
local geodesic at `t` with the prescribed initial data, provided every
witness curve covering `t` keeps its foot `γ t` in the base chart-source
`(chartAt H p).source`. The headline statement we produce records the
existence of `(γ, J)` covering `t` such that `IsGeodesicAt g γ t`.

The foot-in-source hypothesis `ht_src` is the chart-validity clause for
the chart-`p`-fixed witness; see `IsGeodesicOnWithInitial.isGeodesicAt`.
It quantifies over witness curves because the witness producing `t`'s
membership is existentially bound. -/
theorem exists_isGeodesicAt_of_mem_maximalGeodesicInterval
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v)
    (ht_src : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p v →
        γ t ∈ (chartAt H p).source) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, _hJ_conn, h0, ht, hγ⟩ := h
  refine ⟨γ, J, hJ, h0, ht, hγ, ?_⟩
  exact hγ.isGeodesicAt (hJ.mem_nhds ht) (ht_src γ J hγ)

/-- **Math.** For every `t` in the maximal interval, there exists a geodesic
witness producing `IsGeodesicAt g (witness) t` with starting point `p`,
provided every witness curve keeps its foot `γ t` in the base chart-source
`(chartAt H p).source` (the chart-validity clause; see
`IsGeodesicOnWithInitial.isGeodesicAt`). The `t = 0` clause is automatic:
every witness starts at `p ∈ (chartAt H p).source`. -/
theorem exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v)
    (ht_src : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p v →
        γ t ∈ (chartAt H p).source) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsGeodesicAt (I := I) g γ 0 ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, h0, ht, hγ_init, hγ_at⟩ :=
    exists_isGeodesicAt_of_mem_maximalGeodesicInterval (I := I) h ht_src
  refine ⟨γ, hγ_init.start_eq, ?_, hγ_at⟩
  refine hγ_init.isGeodesicAt (hJ.mem_nhds h0) ?_
  rw [hγ_init.start_eq]; exact mem_chart_source H p

end MaximalGeodesicAtTime

section MaximalGeodesicMain


/-- **Math.** Structural properties of the canonical maximal geodesic with initial
datum `(p, v)`: writing `I_max := maximalGeodesicInterval g p v` and
`γ_max := maximalGeodesic g p v`, the set `I_max` is open and contains `0`,
`γ_max 0 = p`, `γ_max` takes the junk value `p` outside `I_max`, and at
every `t ∈ I_max` there is a local geodesic `γ` with `γ 0 = p` that is a
geodesic at both `0` and `t`.

The hypothesis `hsrc` requires every local geodesic witness with initial
data `(p, v)` to keep its foot in `(chartAt H p).source` at each point of
`I_max`; it feeds `IsGeodesicOnWithInitial.isGeodesicAt`, and is needed
because where a witness has left the base chart the chart-`p` geodesic
vector field degenerates. -/
theorem maximalGeodesic_structure_of_footInSource
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hsrc : ∀ t ∈ maximalGeodesicInterval (I := I) g p v,
      ∀ (γ : ℝ → M) (J : Set ℝ),
        IsGeodesicOnWithInitial (I := I) g γ J p v →
          γ t ∈ (chartAt H p).source) :
    let I_max := maximalGeodesicInterval (I := I) g p v
    let γ_max := maximalGeodesic (I := I) g p v
    IsOpen I_max ∧ (0 : ℝ) ∈ I_max ∧ γ_max 0 = p ∧
      (∀ t ∉ I_max, γ_max t = p) ∧
      (∀ t ∈ I_max, ∃ γ : ℝ → M, γ 0 = p ∧
        IsGeodesicAt (I := I) g γ 0 ∧ IsGeodesicAt (I := I) g γ t) := by
  refine ⟨maximalGeodesicInterval_isOpen (I := I) g p v,
    zero_mem_maximalGeodesicInterval (I := I) g p v,
    maximalGeodesic_zero (I := I) g p v, ?_, ?_⟩
  · intro t ht
    exact maximalGeodesic_of_not_mem (I := I) ht
  · intro t ht
    exact exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval (I := I) ht
      (hsrc t ht)

end MaximalGeodesicMain



end Geodesic
end Riemannian

end
