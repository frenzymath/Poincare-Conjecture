import DoCarmoLib.Riemannian.Variation.EnergyFirstDeriv
import DoCarmoLib.Riemannian.Variation.SegmentAssembly

/-!
# do Carmo's formula (1): the first variation of energy, assembled

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4 (`prop:dc-ch9-2-4`).

This file **composes** the two halves of do Carmo's proof, which until now had never met:

1. *the surface half* — `hasDerivAt_dcEnergy_of_dominated`
   (`Variation/EnergyFirstDeriv.lean`): differentiating `E(s) = ∫⟨∂f/∂t, ∂f/∂t⟩ dt` under
   the integral sign gives `E'(s₀) = 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩ dt`;
2. *the intrinsic half* — `IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left`
   (`Variation/FirstVariation.lean`): integrating `∫⟨DV/dt, dc/dt⟩ dt` by parts gives do
   Carmo's right-hand side.

The hinge between them is the **symmetry of the Riemannian connection**,
`D/∂s ∂f/∂t = D/∂t ∂f/∂s` (do Carmo Ch. 3, Lemma 3.4), which turns half 1's `D/∂s ∂f/∂t`
into half 2's `DV/dt`.  Here it is carried as the **hypothesis** `hsymm`; see `## Scope`.

## Scope — what is and is not claimed

The first theorem below proves do Carmo's formula (1) **on a single segment carrying no
breakpoint**:
$$\frac{1}{2}E'(0)
  = -\int_a^b \Big\langle V, \frac{D}{dt}\frac{dc}{dt}\Big\rangle dt
    - \Big\langle V(a), \frac{dc}{dt}(a)\Big\rangle
    + \Big\langle V(b), \frac{dc}{dt}(b)\Big\rangle .$$
The two finite-subdivision theorems then sum this formula over the segments
`[t_i, t_{i+1}]`.  Their boundary terms telescope into do Carmo's jump sum
`∑_i ⟨V(t_i), dc/dt(t_i^+) − dc/dt(t_i^-)⟩`.  The geometric wrapper exposes the actual
variational field, one-sided segment velocities, covariant accelerations, and integrals;
extracting its per-segment hypotheses from an arbitrary `IsVariation` is a separate
regularity step.

`hsymm` is a hypothesis, not a theorem, in this file.  It is exactly do Carmo's "using the
symmetry of the Riemannian connection" step, and — this matters for discharging it — it is
required only at **interior** times `t ∈ (a, b)`: the boundary instances are a null set, and
the proof exchanges `d/ds` past `∫` through `intervalIntegral.integral_congr_ae`.  That is
precisely the range on which `SurfaceSymmetryManifold.covariantDerivS_velT_eq_covariantDerivT_velS`
produces the identity (its conclusion holds at times strictly interior to the covariant
pair's window).  The chart-level form is
`surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst`
(`Variation/SurfaceSymmetry.lean`); discharging `hsymm` from it requires transferring that
identity from a chart reading of the surface to the intrinsic covariant pairs used here.

Four distinct fields appear, and conflating any two of them silently changes the statement:
`T = ∂f/∂t`, `S = ∂f/∂s`, `DsT = D/∂s ∂f/∂t` and `DtT = D/∂t ∂f/∂t = D/dt(dc/dt)`, plus
`DtS = D/∂t ∂f/∂s = DV/dt`.  Only `T` is pinned to the surface by the type system, via
`hvel`; `S` is *not* forced to be `∂f/∂s`, and `DtS`, `DtT` are tied to their fields only by
the covariant-pair hypotheses `hV`, `hW` — the same convention `FirstVariation.lean` uses,
and the reason `hsymm` must be stated rather than derived from the types.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4; the symmetry of the
connection is Ch. 3, Lemma 3.4, and metric compatibility is Ch. 2, Prop. 3.2.
-/

open Set Riemannian Filter MeasureTheory
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** do Carmo Ch. 9, §2, **formula (1) on a segment with no breakpoint**
(`prop:dc-ch9-2-4` for `k = 0`):
$$\frac{1}{2}E'(s_0)
  = -\int_a^b \Big\langle V, \frac{D}{dt}\frac{dc}{dt}\Big\rangle dt
    - \Big\langle V(a), \frac{dc}{dt}(a)\Big\rangle
    + \Big\langle V(b), \frac{dc}{dt}(b)\Big\rangle ,$$
where `c = f(s₀, ·)` is the curve in the variation at `s₀`, `V = ∂f/∂s(s₀, ·)` is the
variational field, `W = ∂f/∂t(s₀, ·) = dc/dt` its velocity and `DW = D/dt(dc/dt)`.

The three inputs are do Carmo's three steps, in his order:
* `hasDerivAt_dcEnergy_of_dominated` — differentiation under the integral sign;
* `hsymm` — the symmetry of the Riemannian connection, `D/∂s ∂f/∂t = D/∂t ∂f/∂s`
  (Ch. 3, Lemma 3.4), supplied as a hypothesis;
* `IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left` — integration by
  parts, which is metric compatibility (Ch. 2, Prop. 3.2) plus the fundamental theorem of
  calculus. -/
theorem hasDerivAt_dcEnergy_eq_first_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {T S DsT DtS DtT : ℝ × ℝ → E}
    {s₀ a b ε : ℝ} {bound : ℝ → ℝ}
    (hab : a ≤ b) (hε : 0 < ε)
    (hvel : ∀ σ t, T (σ, t) = DCVelocity (I := I) (fun τ => f (σ, τ)) t)
    -- the surface half, along the transversals
    (hslice : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hsdiff : ∀ t ∈ uIoc a b, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (s₀ - ε) (s₀ + ε))
    (hscont : ∀ t ∈ uIoc a b, ∀ σ ∈ Icc (s₀ - ε) (s₀ + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds s₀, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t)) (T (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (T (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hF'_meas : AEStronglyMeasurable
      (fun t => 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      (volume.restrict (uIoc a b)))
    (h_bound : ∀ t ∈ uIoc a b, ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖2 * g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖
        ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume a b)
    -- the symmetry of the connection: `D/∂s ∂f/∂t = D/∂t ∂f/∂s`, at interior times
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    -- the intrinsic half, along the curve in the variation at `s₀`
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => S (s₀, τ)) (fun τ => DtS (s₀, τ)) a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => T (s₀, τ)) (fun τ => DtT (s₀, τ)) a b)
    (htdiff : IsChartDifferentiableOn (I := I) (fun τ => f (s₀, τ)) a b)
    (htcont : ∀ t ∈ Icc a b, ContinuousAt (fun τ => f (s₀, τ)) t)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtT (s₀, t)))
      volume a b) :
    HasDerivAt (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)
      (2 * ((g.metricInner (f (s₀, b)) (S (s₀, b) : TangentSpace I (f (s₀, b))) (T (s₀, b))
              - g.metricInner (f (s₀, a)) (S (s₀, a) : TangentSpace I (f (s₀, a))) (T (s₀, a)))
            - ∫ t in a..b, g.metricInner (f (s₀, t))
                (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtT (s₀, t)))) s₀ := by
  -- half 1: differentiation under the integral sign
  have hE := hasDerivAt_dcEnergy_of_dominated (I := I) (g := g) (f := f) (T := T) (DsT := DsT)
    (bound := bound) hε hvel hslice hsdiff hscont hF_meas hF_int hF'_meas h_bound hbound_int
  -- half 2: integration by parts, along the curve in the variation at `s₀`
  have hparts := hV.integral_metricInner_covariantDeriv_left hW htdiff htcont hab hint₁ hint₂
  -- the hinge: the symmetry of the connection turns `D/∂s ∂f/∂t` into `DV/dt`
  have hrw : (∫ t in a..b, 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      = 2 * ∫ t in a..b, g.metricInner (f (s₀, t))
        (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
    rw [hsymm t (ht.mpr htm)]
  rw [hrw, hparts] at hE
  exact hE

/-- **Math.** do Carmo Ch. 9, Prop. 2.4, the finite-subdivision assembly step.

Suppose the first-variation formula has been proved separately on every segment
`[tau i, tau (i+1)]`.  The total energy is their sum near `s0`; differentiating that finite
sum and telescoping the endpoint pairings gives the outer endpoint terms and the negative
jump sum in do Carmo's formula (1).

`bulk i` is the integral `integral <V, D/dt (dc/dt)>` on segment `i`; `minus i` and
`plus i` are the pairings with the left and right velocity limits at subdivision point
`tau i`.  The remaining hypotheses of the full proposition are precisely what must
produce the segment formulas and these one-sided values from an arbitrary variation. -/
theorem hasDerivAt_dcEnergy_eq_piecewise_first_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0) :
    HasDerivAt
      (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau 0) (tau (k + 1)))
      (2 * (minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
        - ∑ i ∈ Finset.range (k + 1), bulk i)) s0 := by
  have hsum := hasDerivAt_sum_segments_of_first_variation k
    (fun i s => DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
    bulk minus plus s0 hsegment
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hint] with s hs
  exact dcEnergy_eq_sum_subdivision (I := I) g (fun t => f (s, t)) tau (k + 1) hs

set_option linter.overlappingInstances false in
/-- **Math.** do Carmo Ch. 9, Prop. 2.4 (`prop:dc-ch9-2-4`), formula (1) over the finite
subdivision in `def:dc-ch9-2-1`, with its geometric terms exposed.

The field `V` is the common variational field.  On segment `i`, `W i` is the one-sided
velocity field and `DW i` is its covariant derivative.  Consequently the interior term at
`tau (i + 1)` is exactly
`<V, W (i + 1) - W i>`, written as the difference of the two metric pairings so that no
vector-space identification between different tangent fibers is hidden.

Each hypothesis in `hsegment` is the smooth-segment formula supplied by
`hasDerivAt_dcEnergy_eq_first_variation`.  Its `hsymm` hypothesis is precisely the symmetry
of the Riemannian connection used by do Carmo, implemented by
`covariant_sndFDeriv_symm` in `Geodesic/SymmetryLemma.lean`.  This theorem performs the
remaining analytic assembly: finite additivity of energy, differentiation of the finite
sum, and telescoping of the one-sided endpoint terms. -/
theorem hasDerivAt_dcEnergy_eq_piecewise_first_variation_of_segment_formulas
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {V : ℝ → E} {W DW : ℕ → ℝ → E}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
        (2 * ((g.metricInner (f (s0, tau (i + 1)))
                  (V (tau (i + 1)) : TangentSpace I (f (s0, tau (i + 1))))
                  (W i (tau (i + 1)))
                - g.metricInner (f (s0, tau i))
                  (V (tau i) : TangentSpace I (f (s0, tau i))) (W i (tau i)))
              - ∫ t in tau i..tau (i + 1), g.metricInner (f (s0, t))
                  (V t : TangentSpace I (f (s0, t))) (DW i t))) s0) :
    HasDerivAt
      (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau 0) (tau (k + 1)))
      (2 * (g.metricInner (f (s0, tau (k + 1)))
                (V (tau (k + 1)) : TangentSpace I (f (s0, tau (k + 1))))
                (W k (tau (k + 1)))
              - g.metricInner (f (s0, tau 0))
                (V (tau 0) : TangentSpace I (f (s0, tau 0))) (W 0 (tau 0))
            - ∑ i ∈ Finset.range k,
                (g.metricInner (f (s0, tau (i + 1)))
                    (V (tau (i + 1)) : TangentSpace I (f (s0, tau (i + 1))))
                    (W (i + 1) (tau (i + 1)))
                  - g.metricInner (f (s0, tau (i + 1)))
                    (V (tau (i + 1)) : TangentSpace I (f (s0, tau (i + 1))))
                    (W i (tau (i + 1))))
            - ∑ i ∈ Finset.range (k + 1),
                ∫ t in tau i..tau (i + 1), g.metricInner (f (s0, t))
                  (V t : TangentSpace I (f (s0, t))) (DW i t))) s0 := by
  let bulk : ℕ → ℝ := fun i =>
    ∫ t in tau i..tau (i + 1), g.metricInner (f (s0, t))
      (V t : TangentSpace I (f (s0, t))) (DW i t)
  let minus : ℕ → ℝ := fun j =>
    g.metricInner (f (s0, tau j))
      (V (tau j) : TangentSpace I (f (s0, tau j))) (W (j - 1) (tau j))
  let plus : ℕ → ℝ := fun j =>
    g.metricInner (f (s0, tau j))
      (V (tau j) : TangentSpace I (f (s0, tau j))) (W j (tau j))
  have h := hasDerivAt_dcEnergy_eq_piecewise_first_variation
    (I := I) (g := g) (f := f) (tau := tau) (k := k) (s0 := s0)
    (bulk := bulk) (minus := minus) (plus := plus) hint (by
      intro i hi
      simpa [bulk, minus, plus] using hsegment i hi)
  simpa [bulk, minus, plus] using h

set_option linter.overlappingInstances false in
/-- **Math.** do Carmo Ch. 9, Proposition 2.5, the finite-subdivision assembly of the
forward implication: a geodesic is critical for energy under proper variations.

On each smooth segment, `hsegment` is formula (1) from `prop:dc-ch9-2-4` after the
covariant acceleration of the geodesic has been set to zero. Properness from
`def:dc-ch9-2-1` supplies `hV0` and `hVend`. The remaining interior terms are the jumps
of the one-sided velocity fields; `hmatch` says that these velocities agree at every
breakpoint, as they do for a geodesic. The finite-subdivision formula
`lem:dc-ch9-2-4-piecewise-assembly` then makes every contribution vanish. -/
theorem hasDerivAt_dcEnergy_zero_of_piecewise_geodesic_segment_formulas
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {V : ℝ → E} {W : ℕ → ℝ → E}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
        (2 * (g.metricInner (f (s0, tau (i + 1)))
                  (V (tau (i + 1)) : TangentSpace I (f (s0, tau (i + 1))))
                  (W i (tau (i + 1)))
              - g.metricInner (f (s0, tau i))
                  (V (tau i) : TangentSpace I (f (s0, tau i))) (W i (tau i)))) s0)
    (hV0 : V (tau 0) = 0)
    (hVend : V (tau (k + 1)) = 0)
    (hmatch : ∀ i < k,
      W (i + 1) (tau (i + 1)) = W i (tau (i + 1))) :
    HasDerivAt
      (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau 0) (tau (k + 1)))
      0 s0 := by
  have hzero : ∀ t, g.metricInner (f (s0, t))
      (V t : TangentSpace I (f (s0, t))) (0 : E) = 0 :=
    fun t => g.metricInner_zero_right _ _
  have hassembled :=
    hasDerivAt_dcEnergy_eq_piecewise_first_variation_of_segment_formulas
      (I := I) (g := g) (f := f) (tau := tau) (k := k) (s0 := s0)
      (V := V) (W := W) (DW := fun _ _ => 0) hint (by
        intro i hi
        simpa only [hzero, intervalIntegral.integral_zero, sub_zero] using hsegment i hi)
  have hjump : ∑ i ∈ Finset.range k,
      (g.metricInner (f (s0, tau (i + 1)))
          (V (tau (i + 1)) : TangentSpace I (f (s0, tau (i + 1))))
          (W (i + 1) (tau (i + 1)))
        - g.metricInner (f (s0, tau (i + 1)))
          (V (tau (i + 1)) : TangentSpace I (f (s0, tau (i + 1))))
          (W i (tau (i + 1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hmatch i (Finset.mem_range.mp hi)]
    ring
  have hbulk : ∑ i ∈ Finset.range (k + 1),
      ∫ t in tau i..tau (i + 1), g.metricInner (f (s0, t))
        (V t : TangentSpace I (f (s0, t))) (0 : E) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [hzero, intervalIntegral.integral_zero]
  have hleft : g.metricInner (f (s0, tau 0))
      (V (tau 0) : TangentSpace I (f (s0, tau 0))) (W 0 (tau 0)) = 0 := by
    rw [hV0]
    exact g.metricInner_zero_left _ _
  have hright : g.metricInner (f (s0, tau (k + 1)))
      (V (tau (k + 1)) : TangentSpace I (f (s0, tau (k + 1))))
      (W k (tau (k + 1))) = 0 := by
    rw [hVend]
    exact g.metricInner_zero_left _ _
  rw [hjump, hbulk, hleft, hright] at hassembled
  simpa using hassembled

/-- **Math.** do Carmo Ch. 9, Prop. 2.5, the direction
*geodesic implies critical point of energy*, on a segment with no breakpoint.

This specializes `hasDerivAt_dcEnergy_eq_first_variation`: the covariant
acceleration of the base curve is zero, and properness makes the variational
field vanish at both endpoints, so every term in the first-variation formula
vanishes. -/
theorem hasDerivAt_dcEnergy_zero_of_geodesic
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {T S DsT DtS : ℝ × ℝ → E}
    {s₀ a b ε : ℝ} {bound : ℝ → ℝ}
    (hab : a ≤ b) (hε : 0 < ε)
    (hvel : ∀ σ t, T (σ, t) = DCVelocity (I := I) (fun τ => f (σ, τ)) t)
    (hslice : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hsdiff : ∀ t ∈ uIoc a b, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (s₀ - ε) (s₀ + ε))
    (hscont : ∀ t ∈ uIoc a b, ∀ σ ∈ Icc (s₀ - ε) (s₀ + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds s₀, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t)) (T (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (T (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hF'_meas : AEStronglyMeasurable
      (fun t => 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      (volume.restrict (uIoc a b)))
    (h_bound : ∀ t ∈ uIoc a b, ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖2 * g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖
        ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume a b)
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => S (s₀, τ)) (fun τ => DtS (s₀, τ)) a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => T (s₀, τ)) (fun _ => 0) a b)
    (htdiff : IsChartDifferentiableOn (I := I) (fun τ => f (s₀, τ)) a b)
    (htcont : ∀ t ∈ Icc a b, ContinuousAt (fun τ => f (s₀, τ)) t)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (0 : E))
      volume a b)
    (hSa : S (s₀, a) = 0) (hSb : S (s₀, b) = 0) :
    HasDerivAt (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b) 0 s₀ := by
  have hE := hasDerivAt_dcEnergy_eq_first_variation (I := I) (g := g)
    (f := f) (T := T) (S := S) (DsT := DsT) (DtS := DtS) (DtT := fun _ => 0)
    hab hε hvel hslice hsdiff hscont hF_meas hF_int hF'_meas h_bound hbound_int
    hsymm hV hW htdiff htcont hint₁ hint₂
  have hleft : g.metricInner (f (s₀, a))
      (S (s₀, a) : TangentSpace I (f (s₀, a))) (T (s₀, a)) = 0 := by
    rw [hSa]
    exact g.metricInner_zero_left _ _
  have hright : g.metricInner (f (s₀, b))
      (S (s₀, b) : TangentSpace I (f (s₀, b))) (T (s₀, b)) = 0 := by
    rw [hSb]
    exact g.metricInner_zero_left _ _
  have hzero : (∫ t in a..b, g.metricInner (f (s₀, t))
      (S (s₀, t) : TangentSpace I (f (s₀, t))) (0 : E)) = 0 := by
    have hz : ∀ t, g.metricInner (f (s₀, t))
        (S (s₀, t) : TangentSpace I (f (s₀, t))) (0 : E) = 0 :=
      fun t => g.metricInner_zero_right _ _
    simp only [hz, intervalIntegral.integral_zero]
  rw [hleft, hright, hzero] at hE
  simpa using hE

end Riemannian.Variation
