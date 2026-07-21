import DoCarmoLib.Riemannian.Jacobi.ParallelFrame

/-!
# The Jacobi reduction in a parallel orthonormal frame (do Carmo Ch. 5, `def:dc-ch5-2-1`)

This file formalizes the **intrinsic reduction** at the heart of do Carmo's Jacobi
field definition `def:dc-ch5-2-1`.  Having produced a parallel orthonormal frame
`e₁(t),…,eₙ(t)` along the geodesic `γ` (`DoCarmoLib/Riemannian/Jacobi/ParallelFrame.lean`),
do Carmo writes a candidate field as `J(t) = Σᵢ fᵢ(t) eᵢ(t)` and reads the Jacobi
equation `D²J/dt² + R(γ',J)γ' = 0` in that frame.  The two displayed computations of
his proof are:

* `D²J/dt² = Σᵢ fᵢ''(t) eᵢ(t)` — because the frame is **parallel** (`Deᵢ/dt = 0`), the
  covariant derivative `D/dt` differentiates only the scalar components (Leibniz rule
  `covariantDerivCoord_smul` + additivity over the frame), so `D/dt(Σ fᵢ eᵢ) = Σ fᵢ' eᵢ`
  and iterating gives `Σ fᵢ'' eᵢ`;
* `R(γ',J)γ' = Σᵢⱼ fᵢ aᵢⱼ eⱼ`, `aᵢⱼ = ⟨R(γ',eᵢ)γ',eⱼ⟩` — by linearity of the curvature
  operator in `J`.

Pairing the Jacobi equation with `eⱼ` and using **orthonormality**
`⟨eᵢ(t),eⱼ(t)⟩ = δᵢⱼ` then extracts do Carmo's second-order linear system

  `fⱼ''(t) + Σᵢ aᵢⱼ(t) fᵢ(t) = 0`,   `j = 1,…,n`,

whose existence/uniqueness theory is the abstract ODE core of
`DoCarmoLib/Riemannian/Jacobi/JacobiEquationODE.lean` (`lem:dc-ch5-2-1-ode`).

Everything here is read in the fixed chart at `α = γ(0)`, in terms of the coordinate
covariant derivative `covariantDerivCoord` and the chart inner product
`chartMetricInner` (do Carmo Ch. 2, §2).  The curvature term `R(γ',·)γ'` is carried
as an abstract continuous-linear coordinate field `R : E →L[ℝ] E` (its identification
with the intrinsic `curvatureOperatorAt` at `γ(t)` is the chart-curvature bridge, a
separate step); everything else is discharged here.

## Main results

* `Riemannian.Jacobi.covariantDerivCoord_sum` — `D/dt` is additive over a finite sum
  of coordinate fields.
* `Riemannian.Jacobi.covariantDerivCoord_frameCombination` — **`D/dt(Σ fᵢ eᵢ) = Σ fᵢ' eᵢ`**
  in a parallel frame (do Carmo's first identity, first order).
* `Riemannian.Jacobi.covariantDerivCoord2_frameCombination` — **`D²/dt²(Σ fᵢ eᵢ) = Σ fᵢ'' eᵢ`**
  (do Carmo's `D²J/dt² = Σ fᵢ'' eᵢ`).
* `Riemannian.Jacobi.chartMetricInner_frameCombination_left` — the orthonormal
  extraction `⟨Σ cᵢ eᵢ, eⱼ⟩ = cⱼ`.
* `Riemannian.Jacobi.chartMetricInner_covariantDerivCoord2_frame` — **`⟨D²J/dt², eⱼ⟩ = fⱼ''`**.
* `Riemannian.Jacobi.chartMetricInner_map_frameCombination_left` — **`⟨R(J), eⱼ⟩ = Σᵢ fᵢ aᵢⱼ`**
  with `aᵢⱼ = ⟨R(eᵢ), eⱼ⟩`, do Carmo's second identity.
* `Riemannian.Jacobi.frameJacobiComponent` — the two identities combined: pairing the
  Jacobi equation `D²J + R(J) = 0` with `eⱼ` yields do Carmo's scalar system
  `fⱼ'' + Σᵢ aᵢⱼ fᵢ = 0`.
-/

open Set
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The Christoffel contraction vanishes when its vector slot is `0`
(linearity in that slot): `Γ(u, 0)(y) = 0`. -/
theorem chartChristoffelContraction_zero_right (g : RiemannianMetric I M) (α : M) (u y : E) :
    Geodesic.chartChristoffelContraction (I := I) g α u 0 y = 0 := by
  have h := Geodesic.chartChristoffelContraction_smul_right (I := I) g α u (0 : ℝ) (0 : E) y
  simpa only [zero_smul] using h

/-! ## `D/dt` is additive over finite sums, and equals the component derivative in a
parallel frame -/

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 (a), extended to a **finite sum**: the
covariant derivative along a curve is additive over `Σᵢ Wᵢ`,
`D/dt(Σᵢ Wᵢ) = Σᵢ DWᵢ/dt`. -/
theorem covariantDerivCoord_sum {ι : Type*} (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (s : Finset ι) (W : ι → ℝ → E) {t : ℝ} :
    (∀ i ∈ s, DifferentiableAt ℝ (W i) t) →
    covariantDerivCoord (I := I) g α u (fun r => ∑ i ∈ s, W i r) t
      = ∑ i ∈ s, covariantDerivCoord (I := I) g α u (W i) t := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro _
    have h0 : (fun r => ∑ i ∈ (∅ : Finset ι), W i r) = fun _ => (0 : E) := by
      funext r; simp
    rw [h0, Finset.sum_empty, covariantDerivCoord_def]
    simp [chartChristoffelContraction_zero_right]
  | insert x s hx ih =>
    intro hW
    have hxd : DifferentiableAt ℝ (W x) t := hW x (Finset.mem_insert_self x s)
    have hsd : ∀ i ∈ s, DifferentiableAt ℝ (W i) t := fun i hi =>
      hW i (Finset.mem_insert_of_mem hi)
    have htail : DifferentiableAt ℝ (fun r => ∑ i ∈ s, W i r) t := by
      refine (DifferentiableAt.sum (fun i hi => hsd i hi)).congr_of_eventuallyEq ?_
      filter_upwards with r using (Finset.sum_apply r s W).symm
    have hfun : (fun r => ∑ i ∈ insert x s, W i r) = W x + (fun r => ∑ i ∈ s, W i r) := by
      funext r; simp only [Pi.add_apply]; rw [Finset.sum_insert hx]
    rw [hfun, covariantDerivCoord_add g α u (W x) (fun r => ∑ i ∈ s, W i r) hxd htail,
      ih hsd, Finset.sum_insert hx]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`, first identity (first order): in a
**parallel** frame `eᵢ` (`Deᵢ/dt = 0`), the covariant derivative of a combination
`J = Σᵢ fᵢ eᵢ` differentiates only the scalar components:

  `D/dt(Σᵢ fᵢ eᵢ) = Σᵢ fᵢ' eᵢ`.

This is do Carmo's use of "the fields `eᵢ` are parallel" to reduce `D/dt` to ordinary
differentiation of the components. -/
theorem covariantDerivCoord_frameCombination {ι : Type*} [Fintype ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (f : ι → ℝ → ℝ) (e : ι → ℝ → E) {t : ℝ}
    (hf : ∀ i, DifferentiableAt ℝ (f i) t)
    (he : ∀ i, DifferentiableAt ℝ (e i) t)
    (hpar : ∀ i, covariantDerivCoord (I := I) g α u (e i) t = 0) :
    covariantDerivCoord (I := I) g α u (fun r => ∑ i, f i r • e i r) t
      = ∑ i, deriv (f i) t • e i t := by
  classical
  have hconv : (fun r => ∑ i, f i r • e i r) = fun r => ∑ i, (f i • e i) r := by
    funext r; exact Finset.sum_congr rfl fun i _ => rfl
  rw [hconv, covariantDerivCoord_sum g α u Finset.univ (fun i => f i • e i)
      (fun i _ => (hf i).smul (he i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [covariantDerivCoord_smul g α u (f i) (e i) (hf i) (he i), hpar i, smul_zero, add_zero]

/-- **Math.** The covariant derivative `D/dt V` at `t` depends on `V` only through its
germ at `t`: two coordinate fields agreeing on a neighborhood of `t` have equal
covariant derivative there.  (`covariantDerivCoord` reads `V` through `deriv V t` and
`V t`, both germ-local.)  This lets the second covariant derivative be computed from
the neighborhood formula for the first. -/
theorem covariantDerivCoord_congr_of_eventuallyEq (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) {V W : ℝ → E} {t : ℝ} (h : V =ᶠ[𝓝 t] W) :
    covariantDerivCoord (I := I) g α u V t = covariantDerivCoord (I := I) g α u W t := by
  rw [covariantDerivCoord_def, covariantDerivCoord_def, h.deriv_eq, h.eq_of_nhds]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`, first identity (second order): in a
parallel frame, the **second** covariant derivative of `J = Σᵢ fᵢ eᵢ` is

  `D²/dt²(Σᵢ fᵢ eᵢ) = Σᵢ fᵢ'' eᵢ`.

do Carmo's `D²J/dt² = Σᵢ fᵢ'' eᵢ`.  The frame is parallel and the components `fᵢ`
twice differentiable on a neighborhood of `t`; the first covariant derivative equals
`Σᵢ fᵢ' eᵢ` on that neighborhood (`covariantDerivCoord_frameCombination`), so its own
covariant derivative differentiates the `fᵢ'` again. -/
theorem covariantDerivCoord2_frameCombination {ι : Type*} [Fintype ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (f : ι → ℝ → ℝ) (e : ι → ℝ → E) {t : ℝ}
    (hf : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (f i) r)
    (hf2 : ∀ i, DifferentiableAt ℝ (deriv (f i)) t)
    (he : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (e i) r)
    (hpar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I) g α u (e i) r = 0) :
    covariantDerivCoord (I := I) g α u
        (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, f i s • e i s) r) t
      = ∑ i, deriv (deriv (f i)) t • e i t := by
  classical
  have hev : (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, f i s • e i s) r)
      =ᶠ[𝓝 t] (fun r => ∑ i, deriv (f i) r • e i r) := by
    have H1 : ∀ᶠ r in 𝓝 t, ∀ i, DifferentiableAt ℝ (f i) r := Filter.eventually_all.mpr hf
    have H2 : ∀ᶠ r in 𝓝 t, ∀ i, DifferentiableAt ℝ (e i) r := Filter.eventually_all.mpr he
    have H3 : ∀ᶠ r in 𝓝 t, ∀ i, covariantDerivCoord (I := I) g α u (e i) r = 0 :=
      Filter.eventually_all.mpr hpar
    filter_upwards [H1, H2, H3] with r hr1 hr2 hr3
    exact covariantDerivCoord_frameCombination g α u f e hr1 hr2 hr3
  rw [covariantDerivCoord_congr_of_eventuallyEq g α u hev]
  exact covariantDerivCoord_frameCombination g α u (fun i => deriv (f i)) e hf2
    (fun i => (he i).self_of_nhds) (fun i => (hpar i).self_of_nhds)

/-! ## Pairing with the frame: extracting the scalar components -/

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: the **orthonormal extraction**.
Pairing a frame combination `Σᵢ cᵢ eᵢ` with `eⱼ` and using orthonormality
`⟨eᵢ,eⱼ⟩ = δᵢⱼ` returns the `j`-th coefficient: `⟨Σᵢ cᵢ eᵢ, eⱼ⟩ = cⱼ`. -/
theorem chartMetricInner_frameCombination_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (α : M) (y : E) (c : ι → ℝ) (e : ι → E) (j : ι)
    (horth : ∀ i, chartMetricInner (I := I) g α y (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    chartMetricInner (I := I) g α y (∑ i, c i • e i) (e j) = c j := by
  classical
  rw [chartMetricInner_sum_left]
  simp only [chartMetricInner_smul_left, horth, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`, the component equation of the
acceleration: in a parallel orthonormal frame, pairing `D²J/dt²` with `eⱼ` extracts
the second derivative of the `j`-th component,

  `⟨D²J/dt²(t), eⱼ(t)⟩ = fⱼ''(t)`. -/
theorem chartMetricInner_covariantDerivCoord2_frame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (f : ι → ℝ → ℝ) (e : ι → ℝ → E) {t : ℝ}
    (hf : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (f i) r)
    (hf2 : ∀ i, DifferentiableAt ℝ (deriv (f i)) t)
    (he : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (e i) r)
    (hpar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I) g α u (e i) r = 0)
    (horth : ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0) (j : ι) :
    chartMetricInner (I := I) g α (u t)
        (covariantDerivCoord (I := I) g α u
          (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, f i s • e i s) r) t)
        (e j t)
      = deriv (deriv (f j)) t := by
  rw [covariantDerivCoord2_frameCombination g α u f e hf hf2 he hpar,
    chartMetricInner_frameCombination_left g α (u t) (fun i => deriv (deriv (f i)) t)
      (fun i => e i t) j (fun i => horth i j)]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`, second identity: for a linear
coordinate field `R` (the chart reading of `w ↦ R(γ',w)γ'`), pairing `R(J)` with `eⱼ`
expands over the frame `J = Σᵢ fᵢ eᵢ` by linearity,

  `⟨R(J), eⱼ⟩ = Σᵢ fᵢ ⟨R(eᵢ), eⱼ⟩ = Σᵢ fᵢ aᵢⱼ`,   `aᵢⱼ = ⟨R(eᵢ), eⱼ⟩`.

do Carmo's `R(γ',J)γ' = Σᵢⱼ fᵢ aᵢⱼ eⱼ`, read against `eⱼ`. -/
theorem chartMetricInner_map_frameCombination_left {ι : Type*} [Fintype ι]
    (g : RiemannianMetric I M) (α : M) (y : E) (R : E →L[ℝ] E) (c : ι → ℝ) (e : ι → E) (w : E) :
    chartMetricInner (I := I) g α y (R (∑ i, c i • e i)) w
      = ∑ i, c i * chartMetricInner (I := I) g α y (R (e i)) w := by
  rw [map_sum, chartMetricInner_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, chartMetricInner_smul_left]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: the **scalar Jacobi system**.
Assume `J = Σᵢ fᵢ eᵢ` in a parallel orthonormal frame, with `R : E →L[ℝ] E` the chart
curvature contraction `w ↦ R(γ',w)γ'`.  If `J` satisfies the Jacobi equation
`D²J/dt² + R(J) = 0`, then its components solve do Carmo's second-order linear system

  `fⱼ''(t) + Σᵢ aᵢⱼ(t) fᵢ(t) = 0`,   `aᵢⱼ(t) = ⟨R(eᵢ(t)), eⱼ(t)⟩`.

This is the pairing of the intrinsic Jacobi equation with `eⱼ`, combining the
acceleration identity (`chartMetricInner_covariantDerivCoord2_frame`) with the
curvature identity (`chartMetricInner_map_frameCombination_left`). -/
theorem frameJacobiComponent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (f : ι → ℝ → ℝ) (e : ι → ℝ → E)
    (R : E →L[ℝ] E) {t : ℝ}
    (hf : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (f i) r)
    (hf2 : ∀ i, DifferentiableAt ℝ (deriv (f i)) t)
    (he : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (e i) r)
    (hpar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I) g α u (e i) r = 0)
    (horth : ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0)
    (hjac : covariantDerivCoord (I := I) g α u
          (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, f i s • e i s) r) t
        + R (∑ i, f i t • e i t) = 0) (j : ι) :
    deriv (deriv (f j)) t
        + ∑ i, f i t * chartMetricInner (I := I) g α (u t) (R (e i t)) (e j t) = 0 := by
  have hpair := congrArg (fun V => chartMetricInner (I := I) g α (u t) V (e j t)) hjac
  simp only at hpair
  rw [chartMetricInner_add_left, chartMetricInner_zero_left,
    chartMetricInner_covariantDerivCoord2_frame g α u f e hf hf2 he hpar horth j,
    chartMetricInner_map_frameCombination_left g α (u t) R (fun i => f i t)
      (fun i => e i t) (e j t)] at hpair
  exact hpair

/-! ## The frame is a basis: orthonormal expansion and the reconstruction (converse) -/

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1` / `cor:dc-ch5-3-10`: an orthonormal
frame `e₁,…,eₙ` (`n = dim M`) is a **basis**, and every vector expands as

  `w = Σⱼ ⟨w, eⱼ⟩ eⱼ`.

Orthonormality forces linear independence (`linearIndependent_of_chartMetricInner_orthonormal`);
with `card ι = dim M` the family is a basis, so `w = Σⱼ cⱼ eⱼ`, and pairing with `eⱼ`
identifies `cⱼ = ⟨w, eⱼ⟩`. -/
theorem frameExpansion {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (g : RiemannianMetric I M) (α : M) (y : E) (e : ι → E)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (horth : ∀ i j, chartMetricInner (I := I) g α y (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : E) :
    w = ∑ j, chartMetricInner (I := I) g α y w (e j) • e j := by
  classical
  have hli : LinearIndependent ℝ e :=
    linearIndependent_of_chartMetricInner_orthonormal g α y e horth
  have hb := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbdef
  have h1 : w = ∑ j, b.repr w j • e j := by
    conv_lhs => rw [← b.sum_repr w]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb]
  have hcoord : ∀ j, chartMetricInner (I := I) g α y w (e j) = b.repr w j := fun j => by
    conv_lhs => rw [h1]
    exact chartMetricInner_frameCombination_left g α y (fun k => b.repr w k) e j
      (fun i => horth i j)
  conv_lhs => rw [h1]
  exact Finset.sum_congr rfl fun j _ => by rw [hcoord j]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`, the **reconstruction (converse)** of the
frame reduction.  In a parallel orthonormal frame that is a basis (`card ι = dim M`), the
left-hand side of the Jacobi equation `D²J/dt² + R(J)` for `J = Σᵢ fᵢ eᵢ` expands in the
frame with do Carmo's scalar-system expressions as coefficients:

  `D²J/dt² + R(J) = Σⱼ (fⱼ'' + Σᵢ aᵢⱼ fᵢ) eⱼ`,   `aᵢⱼ = ⟨R(eᵢ), eⱼ⟩`.

Hence `J` is a Jacobi field (`D²J/dt² + R(J) = 0`) **iff** every scalar equation
`fⱼ'' + Σᵢ aᵢⱼ fᵢ = 0` holds (the coefficients of a basis expansion vanish iff the
vector does).  Combined with `frameJacobiComponent` (the forward reading), this is do
Carmo's "equation (1) is equivalent to the system." -/
theorem covariantDerivCoord2_add_map_frameCombination_expand {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (f : ι → ℝ → ℝ) (e : ι → ℝ → E)
    (R : E →L[ℝ] E) {t : ℝ}
    (hf : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (f i) r)
    (hf2 : ∀ i, DifferentiableAt ℝ (deriv (f i)) t)
    (he : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (e i) r)
    (hpar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I) g α u (e i) r = 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (horth : ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0) :
    covariantDerivCoord (I := I) g α u
        (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, f i s • e i s) r) t
      + R (∑ i, f i t • e i t)
      = ∑ j, (deriv (deriv (f j)) t
          + ∑ i, f i t * chartMetricInner (I := I) g α (u t) (R (e i t)) (e j t)) • e j t := by
  classical
  have hRJ : R (∑ i, f i t • e i t)
      = ∑ j, (∑ i, f i t * chartMetricInner (I := I) g α (u t) (R (e i t)) (e j t)) • e j t := by
    rw [map_sum]
    have step1 : ∀ i, R (f i t • e i t)
        = ∑ j, (f i t * chartMetricInner (I := I) g α (u t) (R (e i t)) (e j t)) • e j t := by
      intro i
      rw [map_smul]
      conv_lhs => rw [frameExpansion g α (u t) (fun k => e k t) hcard horth (R (e i t))]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    rw [Finset.sum_congr rfl (fun i _ => step1 i), Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_smul.symm
  rw [covariantDerivCoord2_frameCombination g α u f e hf hf2 he hpar, hRJ,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (add_smul _ _ _).symm

end Riemannian.Jacobi
