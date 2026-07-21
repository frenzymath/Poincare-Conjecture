import PetersenLib.Ch05.Geodesics
import PetersenLib.Riemannian.Exponential.StrictDerivative
import PetersenLib.Riemannian.Exponential.Ray

/-!
# Petersen Ch. 5, §5.5.1 — the exponential map and Riemannian coordinates

Blueprint-facing (`PetersenLib.*`) layer over the vendored openga exponential-map
engineering (`PetersenLib.Exponential.*`).  For a smooth Riemannian metric `g` on
a boundaryless manifold modelled on a complete inner-product space, the maximal
geodesic through `(p, v)` gives a canonical curve; the **exponential map**
`exp_p(v)` is its value at time `1`.

## Blueprint nodes

* `def:pet-ch5-exponential-map` — `expMap` (with the already-proven
  `geodesicHomogeneity`, Petersen's homogeneity property `c_{av}(t) = c_v(at)`).
* `prop:pet-ch5-exp-diffeomorphism-properties` (part 1) — `expMap_localDiffeomorphism`:
  `D exp_p` at the origin is the identity (nonsingular), `exp_p` is injective on a
  small ball around `0` and maps the neighbourhood filter of `0` onto that of `p`;
  the inverse function theorem then makes `exp_p` a local diffeomorphism near `0`.
  Part 2 (the map `E : O → M × M`, `E(v) = (π v, exp v)`, is a local diffeomorphism
  near the diagonal) is formalized in `Ch05/ExpDiagonal.lean` as
  `expDiagonalMap_localDiffeomorphism`, at `C^∞` — the `C¹` ceiling this file used to
  record as "what is genuinely missing" was lifted in run 0181 r1 by
  `Exponential.exists_totallyNormal_cinfty_diffeo`
  (`Exponential/TotallyNormalCInfty.lean`), which ports the `C¹` package off
  `Geodesic.exists_uniform_geodesic_flow_contDiffAt`.  It was never blocked on
  smoothness of the geodesic flow in `t`: `E` is an evaluation at a **fixed** time, so
  it needs joint smoothness in the initial condition `(q, v)` only.
  What `expDiagonalMap_localDiffeomorphism` does *not* yet do — and why
  `prop:pet-ch5-exp-diffeomorphism-properties` is still not `\leanok` — is global: it
  is a per-`p`, chart-at-`p` statement about `(y, w) ↦ (y, (Z (y, T⁻¹ • w) T).1)` on a
  product ball, whereas Petersen asks for a single diffeomorphism from a neighbourhood
  of the zero section of `TM` onto a neighbourhood of the diagonal in `M × M`, and it
  pins the second component via the geodesic characterization rather than by
  identifying it with `expMap` (an easy but unwritten consequence of geodesic
  uniqueness).
* `def:pet-ch5-injectivity-radius` — `injectivityRadius`.

The crux is that the strict Fréchet derivative of the chart reading
`w ↦ φ_p(exp_p w)` at `0` is the identity
(`Exponential.exists_hasStrictFDerivAt_extChartAt_expMap`, proved sorry-free via the
spray-linearization / Picard–Lindelöf route in the vendored openga tree), so the
`C^∞`-ODE smooth-dependence gap of §5.2 does **not** obstruct the differential
computation of Prop. 5.5.1(1).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-exponential-map`): the **exponential map**
at `p ∈ M` applied to `v ∈ T_pM`, the value at time `t = 1` of the maximal geodesic
`c_v` with `c_v(0) = p`, `ċ_v(0) = v`.  Equivalently `exp_p(tv) = c_v(t)`
(`expMap_smul` / `geodesicHomogeneity`), so `exp_p(v)` is reached from `p` by going
"distance" `|v|` in the direction `v/|v|`. -/
def expMap (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) : M :=
  Exponential.expMap (I := I) g p v

@[simp] lemma expMap_eq (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    expMap (I := I) g p v = Exponential.expMap (I := I) g p v := rfl

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-exponential-map`): the natural domain
`O_p ⊂ T_pM` of `exp_p`, the vectors `v` whose maximal geodesic is defined at
time `1`. -/
def expDomain (g : RiemannianMetric I M) (p : M) : Set (TangentSpace I p) :=
  Exponential.expDomain (I := I) g p

@[simp] lemma expDomain_eq (g : RiemannianMetric I M) (p : M) :
    expDomain (I := I) g p = Exponential.expDomain (I := I) g p := rfl

@[simp] lemma mem_expDomain_iff {g : RiemannianMetric I M} {p : M}
    {v : TangentSpace I p} :
    v ∈ expDomain (I := I) g p ↔
      (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v := Iff.rfl

/-- **Math.** `exp_p(0) = p`: the zero vector maps to the base point. -/
@[simp] theorem expMap_zero (g : RiemannianMetric I M) (p : M) :
    expMap (I := I) g p (0 : TangentSpace I p) = p :=
  Exponential.expMap_zero (I := I) g p

/-- **Math.** The zero vector always lies in the natural domain. -/
theorem zero_mem_expDomain (g : RiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ expDomain (I := I) g p :=
  Exponential.zero_mem_expDomain (I := I) g p

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-exponential-map`, ray form): the
exponential map traces the geodesic along each ray, `exp_p(tv) = c_v(t)`, whenever
`t` lies in the maximal interval of the geodesic with initial data `(p, v)`.  The
chart-validity clause `hsrc` requires geodesic witnesses with initial data
`(p, tv)` to keep their foot in the chart at `p`. -/
theorem expMap_smul (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (hmem : t ∈ maximalGeodesicInterval (I := I) g p v)
    (hsrc : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p (t • v) →
        ∀ s ∈ J, γ s ∈ (chartAt H p).source) :
    expMap (I := I) g p (t • v) = maximalGeodesic (I := I) g p v t :=
  Exponential.expMap_smul (I := I) g p v hmem hsrc

/-- **Math.** Petersen Ch. 5 (`prop:pet-ch5-exp-diffeomorphism-properties`, Prop.
5.5.1 (1)).  Read in the chart at `p`, `exp_p` has strict Fréchet derivative the
identity at the origin, so `D\exp_p` is nonsingular at `0`; moreover `exp_p` is
injective on a small ball `B(0, ρ)` (contained in the natural domain) and maps the
neighbourhood filter of `0 ∈ T_pM` onto that of `p`.  With the inverse function
theorem this is exactly the statement that `exp_p` is a local diffeomorphism near
`0`.

Part (2) of Prop. 5.5.1 — that `E(v) = (π v, \exp v)` is a local diffeomorphism of
a neighbourhood of the zero section of `TM` onto a neighbourhood of the diagonal in
`M × M` — is `expDiagonalMap_localDiffeomorphism` in `Ch05/ExpDiagonal.lean`, proved
at `C^∞` but only in the chart at a fixed `p`; see this file's header. -/
theorem expMap_localDiffeomorphism (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (Metric.ball (0 : E) ρ) ∧
      HasStrictFDerivAt
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ContinuousLinearMap.id ℝ E) 0 ∧
      Filter.map (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) (𝓝 0)
        = 𝓝 p := by
  obtain ⟨ρ₁, hρ₁, hdom₁, _hsrc, hstrict⟩ :=
    Exponential.exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g p
  obtain ⟨ρ₂, hρ₂, hinj, _hdom₂⟩ := Exponential.exists_injOn_expMap (I := I) g p
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact hdom₁ w (lt_of_lt_of_le hw (min_le_left _ _))
  · exact hinj.mono (Metric.ball_subset_ball (min_le_right _ _))
  · exact hstrict
  · exact Exponential.map_expMap_nhds (I := I) g p

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-injectivity-radius`): the **injectivity
radius** at `p`, the largest `ε > 0` (possibly `+∞`) such that `exp_p` is defined
on the **`g_p`-metric** ball `B_g(0, ε) = {v ∈ T_pM ∣ |v|_g < ε}` and injective
there — the radius up to which `exp_p` restricts to a diffeomorphism onto its
image.  (Its differential is nonsingular near `0` by `expMap_localDiffeomorphism`.)

The ball is measured in the Riemannian inner product `g_p`
(`g.metricInner p v v = |v|_g^2`), *not* the ambient model-space norm on `E`: this
makes `injectivityRadius` a genuine metric invariant (e.g. it scales by `√λ` under
`g ↦ λg`), as opposed to the model-norm surrogate which is left unchanged by such a
rescaling. -/
def injectivityRadius (g : RiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ ε : ℝ, 0 < ε ∧ r = ENNReal.ofReal ε ∧
    (∀ v : TangentSpace I p, g.metricInner p v v < ε ^ 2 →
        v ∈ expDomain (I := I) g p) ∧
    Set.InjOn (expMap (I := I) g p)
      {v : TangentSpace I p | g.metricInner p v v < ε ^ 2}}

end PetersenLib

end
