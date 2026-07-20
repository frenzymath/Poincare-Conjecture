import DoCarmoLib.Riemannian.Geodesic.Equation
import Mathlib.Geometry.Manifold.MFDeriv.Atlas


/-!
# The fibre-scaling bundle map and the geodesic spray

For a smooth manifold `M` modelled on a normed space `E`, the *fibre-scaling*
map `fiberScaling a : TM → TM`, `⟨x, w⟩ ↦ ⟨x, a·w⟩`, scales each tangent
vector by the scalar `a` while fixing its foot point. It is the bundle-level
map underlying do Carmo's homogeneity lemma (Ch. 3, Lemma 2.6)
`γ(t, q, a v) = γ(a t, q, v)`: the geodesic spray `geodesicVectorFieldChart`
is *degree-2 homogeneous* under `fiberScaling a`, so an integral curve of the
spray, reparametrised in time by `a` and fibre-scaled by `a`, is again an
integral curve of the spray.

This file records the reusable bundle-level infrastructure:

* `fiberScaling a` — the map, with its projection/fibre unfolding lemmas.
* `chartFiberCoord_fiberScaling` — fibre linearity: the chart-`α` fibre
  coordinate of `fiberScaling a p` is `a` times that of `p` (on the chart
  domain, where the trivialisation is genuinely linear).
* `fiberScaling_contMDiff` — smoothness of the bundle map.
* `geodesicVectorFieldChartFiber_fiberScaling` — the coordinate pushforward:
  the chart-fibre spray value at `fiberScaling a p` is the spray coordinate
  map at the scaled velocity `a·v`, which by `geodesicSprayCoord_smul_velocity`
  scales the horizontal component by `a` and the vertical by `a²`.

On top of this, the file carries out the tangent-map (`mfderiv`) development on
`T(TM)`:

* `fiberScalingLinearMap a` (`Λ_a : (x, w) ↦ (x, a • w)`) — the common coordinate
  shadow of `fiberScaling a` in every tangent-bundle chart
  (`extChartAt_tangent_fiberScaling`), since `TM`-charts depend only on the foot
  point, which fibre scaling fixes.
* `hasMFDerivAt_fiberScaling` / `mfderiv_fiberScaling` — `d(fiberScaling a) = Λ_a`
  in the definitional `E × E` presentation of the double tangent spaces.
* `symmL_trivializationAt_tangent_fiberScaling` — the graded naturality `(★)` of
  the inverse trivialization of `T(TM)` under fibre scaling, proved by a
  conjugation trick (differentiate `Φ ∘ Λ_a = S_a ∘ Φ` for the inverse chart `Φ`).
* `geodesicVectorFieldChart_fiberScaling` / `mfderiv_fiberScaling_smul_spray` —
  the keystone: the chart-fixed geodesic spray is degree-2 homogeneous under fibre
  scaling in definitional coordinates, equivalently
  `d(fiberScaling a)(a • G) = G ∘ fiberScaling a`. This feeds the integral-curve
  homogeneity transform in `Geodesic/Homogeneity.lean` (do Carmo Ch. 3, Lemma 2.6).
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The fibre-scaling bundle map `⟨x, w⟩ ↦ ⟨x, a·w⟩` on `TM`: it scales
each tangent vector by `a` while fixing its foot point. -/
def fiberScaling (a : ℝ) (p : TangentBundle I M) : TangentBundle I M :=
  ⟨p.proj, a • p.2⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma fiberScaling_proj (a : ℝ) (p : TangentBundle I M) :
    (fiberScaling (I := I) a p).proj = p.proj := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma fiberScaling_snd (a : ℝ) (p : TangentBundle I M) :
    (fiberScaling (I := I) a p).2 = a • p.2 := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
/-- **Math.** `fiberScaling` fixes the foot point, so it preserves the chart domain
`geodesicChartDomain α`. -/
lemma fiberScaling_mem_geodesicChartDomain {α : M} {a : ℝ}
    {p : TangentBundle I M} (hp : p ∈ geodesicChartDomain (I := I) α) :
    fiberScaling (I := I) a p ∈ geodesicChartDomain (I := I) α := hp

section FibreLinearity

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Fibre linearity of the chart-`α` fibre coordinate.** On the chart
domain (where the trivialisation at `α` is genuinely linear on the fibre),
the chart-`α` fibre coordinate of `fiberScaling a p` is `a` times that of `p`. -/
lemma chartFiberCoord_fiberScaling (α : M) (a : ℝ)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartFiberCoord (I := I) α (fiberScaling (I := I) a p) =
      a • chartFiberCoord (I := I) α p := by
  classical
  set e := trivializationAt E (TangentSpace I) α with he
  -- fibre coordinate of `⟨x, a•w⟩` = value of the fibrewise linear map at `a•w`
  have hlin : ∀ y : TangentSpace I p.proj,
      (e (⟨p.proj, y⟩ : TangentBundle I M)).2 = e.linearMapAt ℝ p.proj y := by
    intro y
    rw [Bundle.Trivialization.coe_linearMapAt_of_mem e hp]
  change (e (fiberScaling (I := I) a p)).2 = a • (e p).2
  have hp2 : fiberScaling (I := I) a p = (⟨p.proj, a • p.2⟩ : TangentBundle I M) := rfl
  rw [hp2, hlin (a • p.2), map_smul]
  congr 1
  exact (hlin p.2).symm

end FibreLinearity

section Smoothness

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The chart-`α`-fixed fibre coordinate `p ↦ (e_α p).2` is smooth at every
point whose foot lies in the trivialisation base set (obtained from the
identity map via `Bundle.contMDiffAt_totalSpace`). -/
lemma contMDiffAt_trivializationAt_snd (α : M) {p₀ : TangentBundle I M}
    (hp₀ : p₀.proj = α) :
    ContMDiffAt I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M =>
        (trivializationAt E (TangentSpace I) α p).2) p₀ := by
  have hid : ContMDiffAt I.tangent I.tangent ∞
      (id : TangentBundle I M → TangentBundle I M) p₀ := contMDiffAt_id
  have h := (Bundle.contMDiffAt_totalSpace (F := E) (E := TangentSpace I)
    (IB := I) (n := (∞ : WithTop ℕ∞))
    (f := id) (x₀ := p₀)).mp hid |>.2
  simp only [id_eq] at h
  rw [hp₀] at h
  exact h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** **Smoothness of the fibre-scaling bundle map.** `fiberScaling a` is
`C^∞` as a self-map of the tangent bundle. -/
theorem fiberScaling_contMDiff (a : ℝ) :
    ContMDiff I.tangent I.tangent ∞ (fiberScaling (I := I) (M := M) a) := by
  classical
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace (F := E) (E := TangentSpace I) (IB := I)
    (n := (∞ : WithTop ℕ∞))]
  refine ⟨?_, ?_⟩
  · -- base part: `(fiberScaling a p).proj = p.proj`, smooth
    have : (fun p : TangentBundle I M => (fiberScaling (I := I) a p).proj) =
        (fun p : TangentBundle I M => p.proj) := rfl
    rw [this]
    exact (Bundle.contMDiff_proj (TangentSpace I)
      (n := (∞ : WithTop ℕ∞))).contMDiffAt
  · -- fibre part: `(e_{p₀.proj} (fiberScaling a p)).2`, smooth via fibre linearity
    set x₀ := (fiberScaling (I := I) a p₀).proj with hx₀
    have hx₀_eq : x₀ = p₀.proj := rfl
    set e := trivializationAt E (TangentSpace I) x₀ with he
    -- the fibre coordinate `p ↦ (e p).2` is smooth at p₀
    have hsnd : ContMDiffAt I.tangent 𝓘(ℝ, E) ∞
        (fun p : TangentBundle I M => (e p).2) p₀ := by
      have := contMDiffAt_trivializationAt_snd (I := I) x₀ (p₀ := p₀) hx₀_eq.symm
      exact this
    -- on the base-set neighbourhood, `(e (fiberScaling a p)).2 = a • (e p).2`
    have hbase_open : IsOpen
        ((Bundle.TotalSpace.proj : TangentBundle I M → M) ⁻¹' e.baseSet) :=
      e.open_baseSet.preimage (FiberBundle.continuous_proj E (TangentSpace I))
    have hmem₀ : p₀ ∈ (Bundle.TotalSpace.proj : TangentBundle I M → M) ⁻¹' e.baseSet := by
      show p₀.proj ∈ e.baseSet
      exact FiberBundle.mem_baseSet_trivializationAt' p₀.proj
    have heq : (fun p : TangentBundle I M => (e (fiberScaling (I := I) a p)).2)
        =ᶠ[𝓝 p₀] (fun p : TangentBundle I M => a • (e p).2) := by
      refine Filter.eventuallyEq_of_mem (hbase_open.mem_nhds hmem₀) ?_
      intro p hp
      have hp' : p.proj ∈ e.baseSet := hp
      exact chartFiberCoord_fiberScaling (I := I) x₀ a (p := p) hp'
    have hclm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun w : E => a • w) := by
      have hfun : (fun w : E => a • w) = ⇑(a • ContinuousLinearMap.id ℝ E) := by
        funext w; simp
      rw [hfun]
      exact (a • ContinuousLinearMap.id ℝ E).contMDiff
    refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
    exact hclm.contMDiffAt.comp p₀ hsnd

end Smoothness

section CoordinatePushforward

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Coordinate pushforward.** The chart-fibre spray value at
`fiberScaling a p` is the spray coordinate map evaluated at the scaled
velocity `a·v`; by `geodesicSprayCoord_smul_velocity` this equals
`(a·v, a²·(spray velocity component))`. This is the coordinate form of the
degree-2 homogeneity of the geodesic spray under fibre scaling. -/
lemma geodesicVectorFieldChartFiber_fiberScaling
    (g : RiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    geodesicVectorFieldChartFiber (I := I) g α (fiberScaling (I := I) a p) =
      (a • chartFiberCoord (I := I) α p,
        (a * a) • (geodesicSprayCoord (I := I) g α
          (extChartAt I α p.proj) (chartFiberCoord (I := I) α p)).2) := by
  classical
  rw [geodesicVectorFieldChartFiber_eq_sprayCoord]
  have hcoord : chartFiberCoord (I := I) α (fiberScaling (I := I) a p) =
      a • chartFiberCoord (I := I) α p :=
    chartFiberCoord_fiberScaling (I := I) α a hp
  have hproj : (fiberScaling (I := I) a p).proj = p.proj := rfl
  rw [hcoord, hproj]
  exact geodesicSprayCoord_smul_velocity (I := I) g α a
    (extChartAt I α p.proj) (chartFiberCoord (I := I) α p)

end CoordinatePushforward

/-! ### The tangent map of the fibre-scaling bundle map, and graded naturality

In EVERY tangent-bundle chart (the chart of `TM` at a basepoint `b` depends only on
the foot point `b.proj`, which `fiberScaling a` fixes), the fibre-scaling map reads
as one and the same *linear* model map
`Λ_a := fiberScalingLinearMap a : (x, w) ↦ (x, a • w)` on `E × E`.

Two consequences, obtained purely by the chain rule (no block-matrix computation on
the double tangent bundle is needed):

* `hasMFDerivAt_fiberScaling` — `fiberScaling a` has manifold derivative `Λ_a` at
  every point of `TM`, in the definitional `E × E` presentation of the double
  tangent spaces.
* `symmL_trivializationAt_tangent_fiberScaling` — the **graded naturality** of the
  inverse trivialization of `T(TM)`: writing `e₀` for the trivialization of
  `T(TM)` at `⟨α, 0⟩` and `S_a` for `fiberScaling a`,
  `e₀.symmL (S_a q) ∘ Λ_a = Λ_a ∘ e₀.symmL q` over the chart domain. The proof is a
  conjugation trick: `S_a` reads as `Λ_a` in the chart at `⟨α, 0⟩`, so
  `Φ ∘ Λ_a = S_a ∘ Φ` near the chart image of `q`, where `Φ` is the inverse chart;
  differentiating both sides (with `Λ_a` linear) yields the naturality because
  `e₀.symmL` is the manifold derivative of `Φ`
  (`TangentBundle.symmL_trivializationAt`).

Combining with the coordinate pushforward `geodesicVectorFieldChartFiber_fiberScaling`
gives the keystone `geodesicVectorFieldChart_fiberScaling`: the chart-fixed geodesic
spray is degree-2 homogeneous under fibre scaling, **in definitional coordinates**,
which is the form consumed by the integral-curve homogeneity transform.
-/

section ChartReading

/-- **Math.** The graded fibre-scaling model map `Λ_a : E × E → E × E`,
`(x, w) ↦ (x, a • w)`, as a continuous linear map. This is the coordinate shadow of
`fiberScaling a` in every tangent-bundle chart. -/
def fiberScalingLinearMap (a : ℝ) : (E × E) →L[ℝ] E × E :=
  (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ E)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma fiberScalingLinearMap_apply (a : ℝ) (z : E × E) :
    fiberScalingLinearMap (E := E) a z = (z.1, a • z.2) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The extended chart of the tangent bundle at a basepoint `b : TM` is the
product of the base chart at `b.proj` and the fibre trivialization at `b.proj`:
`φ_b(r) = (φ_{b.proj}(r.proj), (e_{b.proj} r).2)` for every `r` whose foot lies in
the trivialization base set. -/
lemma extChartAt_tangent_apply (b : TangentBundle I M) {r : TangentBundle I M}
    (hr : r.proj ∈ (trivializationAt E (TangentSpace I) b.proj).baseSet) :
    extChartAt I.tangent b r =
      (extChartAt I b.proj r.proj,
        (trivializationAt E (TangentSpace I) b.proj r).2) := by
  classical
  rw [FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I) b]
  have hr_src : r ∈ (trivializationAt E (TangentSpace I) b.proj).source :=
    (trivializationAt E (TangentSpace I) b.proj).mem_source.mpr hr
  have hfst : ((trivializationAt E (TangentSpace I) b.proj) r).1 = r.proj :=
    (trivializationAt E (TangentSpace I) b.proj).coe_fst hr_src
  simp only [PartialEquiv.coe_trans, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    Function.comp_apply]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** In the tangent-bundle chart at ANY basepoint `b : TM`, the fibre-scaling
bundle map reads as the graded linear model map `Λ_a = fiberScalingLinearMap a`, at every
point whose foot lies in the trivialization base set at `b.proj`. -/
lemma extChartAt_tangent_fiberScaling (b : TangentBundle I M) (a : ℝ)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (trivializationAt E (TangentSpace I) b.proj).baseSet) :
    extChartAt I.tangent b (fiberScaling (I := I) a p) =
      fiberScalingLinearMap (E := E) a (extChartAt I.tangent b p) := by
  classical
  have hp' : (fiberScaling (I := I) a p).proj ∈
      (trivializationAt E (TangentSpace I) b.proj).baseSet := hp
  rw [extChartAt_tangent_apply (I := I) b hp', extChartAt_tangent_apply (I := I) b hp]
  have hsnd : (trivializationAt E (TangentSpace I) b.proj
      (fiberScaling (I := I) a p)).2 =
        a • (trivializationAt E (TangentSpace I) b.proj p).2 :=
    chartFiberCoord_fiberScaling (I := I) b.proj a hp
  rw [fiberScalingLinearMap_apply]
  exact Prod.ext rfl hsnd

end ChartReading

section MFDerivFiberScaling

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The extended chart of `TM` at `fiberScaling a p` is the extended chart at
`p` itself: tangent-bundle charts depend only on the foot point, which fibre scaling
fixes. -/
lemma extChartAt_tangent_fiberScaling_basepoint (a : ℝ) (p : TangentBundle I M) :
    extChartAt I.tangent (fiberScaling (I := I) a p) = extChartAt I.tangent p := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** **The manifold derivative of the fibre-scaling bundle map.**
`fiberScaling a : TM → TM` has manifold derivative the graded linear map
`Λ_a = fiberScalingLinearMap a` at every point, in the definitional `E × E` presentation
of the double tangent spaces. -/
theorem hasMFDerivAt_fiberScaling (a : ℝ) (p : TangentBundle I M) :
    HasMFDerivAt I.tangent I.tangent (fiberScaling (I := I) (M := M) a) p
      (fiberScalingLinearMap (E := E) a) := by
  classical
  refine ⟨(fiberScaling_contMDiff (I := I) (M := M) a).continuous.continuousAt, ?_⟩
  have hfoot : ∀ r : TangentBundle I M, r ∈ (extChartAt I.tangent p).source →
      r.proj ∈ (trivializationAt E (TangentSpace I) p.proj).baseSet := by
    intro r hr
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff] at hr
    rw [TangentBundle.trivializationAt_baseSet]
    exact hr
  have hev : writtenInExtChartAt I.tangent I.tangent p
        (fiberScaling (I := I) (M := M) a) =ᶠ[𝓝[Set.range (I.tangent)]
          (extChartAt I.tangent p p)] ⇑(fiberScalingLinearMap (E := E) a) := by
    have htgt : (extChartAt I.tangent p).target ∈
        𝓝[Set.range (I.tangent)] (extChartAt I.tangent p p) :=
      extChartAt_target_mem_nhdsWithin p
    filter_upwards [htgt] with z hz
    have hzsrc : (extChartAt I.tangent p).symm z ∈ (extChartAt I.tangent p).source :=
      (extChartAt I.tangent p).map_target hz
    have hzfoot := hfoot _ hzsrc
    show extChartAt I.tangent (fiberScaling (I := I) a p)
        (fiberScaling (I := I) a ((extChartAt I.tangent p).symm z)) =
      fiberScalingLinearMap (E := E) a z
    rw [extChartAt_tangent_fiberScaling_basepoint,
      extChartAt_tangent_fiberScaling p a hzfoot,
      (extChartAt I.tangent p).right_inv hz]
  have hp_self : p ∈ (extChartAt I.tangent p).source := mem_extChartAt_source p
  have heq_at : writtenInExtChartAt I.tangent I.tangent p
        (fiberScaling (I := I) (M := M) a) (extChartAt I.tangent p p) =
      fiberScalingLinearMap (E := E) a (extChartAt I.tangent p p) := by
    show extChartAt I.tangent (fiberScaling (I := I) a p)
        (fiberScaling (I := I) a ((extChartAt I.tangent p).symm
          (extChartAt I.tangent p p))) = _
    rw [extChartAt_tangent_fiberScaling_basepoint,
      (extChartAt I.tangent p).left_inv hp_self,
      extChartAt_tangent_fiberScaling p a (hfoot p hp_self)]
  exact ((fiberScalingLinearMap (E := E) a).hasFDerivAt.hasFDerivWithinAt).congr_of_eventuallyEq
    hev heq_at

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The `mfderiv` of the fibre-scaling map is the graded linear map `Λ_a`. -/
theorem mfderiv_fiberScaling (a : ℝ) (p : TangentBundle I M) :
    mfderiv I.tangent I.tangent (fiberScaling (I := I) (M := M) a) p =
      fiberScalingLinearMap (E := E) a :=
  (hasMFDerivAt_fiberScaling (I := I) (M := M) a p).mfderiv

end MFDerivFiberScaling

section SymmLNaturality

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Graded naturality of the double-tangent trivialization under fibre
scaling** (the keystone identity `(★)`). Writing `e₀` for the trivialization of
`T(TM)` at `⟨α, 0⟩`, `S_a := fiberScaling a` and `Λ_a := fiberScalingLinearMap a`,

`e₀.symmL (S_a q) (Λ_a w) = Λ_a (e₀.symmL q w)`

for every `q : TM` with foot in the chart at `α` and every `w : E × E`. Both sides
live in the definitional `E × E` presentation of the double tangent spaces. -/
theorem symmL_trivializationAt_tangent_fiberScaling (α : M) (a : ℝ)
    {q : TangentBundle I M} (hq : q.proj ∈ (chartAt H α).source) (w : E × E) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).symmL ℝ (fiberScaling (I := I) a q)
      (fiberScalingLinearMap (E := E) a w) =
    fiberScalingLinearMap (E := E) a
      ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).symmL ℝ q w) := by
  classical
  set x₀ : TangentBundle I M := ⟨α, (0 : E)⟩ with hx₀
  have hq_src : q ∈ (chartAt (ModelProd H E) x₀).source := by
    rw [TangentBundle.mem_chart_source_iff]
    exact hq
  have hq'_src : fiberScaling (I := I) a q ∈ (chartAt (ModelProd H E) x₀).source := by
    rw [TangentBundle.mem_chart_source_iff]
    exact hq
  have hq_esrc : q ∈ (extChartAt I.tangent x₀).source := by
    rw [extChartAt_source]; exact hq_src
  have hfoot : q.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hq
  -- symmL as the manifold derivative of the inverse chart
  have h1 := TangentBundle.symmL_trivializationAt (I := I.tangent)
    (M := TangentBundle I M) (x₀ := x₀) (x := q) hq_src
  have h2 := TangentBundle.symmL_trivializationAt (I := I.tangent)
    (M := TangentBundle I M) (x₀ := x₀) (x := fiberScaling (I := I) a q) hq'_src
  rw [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] at h1 h2
  -- the evaluation point of `h2` is `Λ_a` of that of `h1`
  have hpt : extChartAt I.tangent x₀ (fiberScaling (I := I) a q) =
      fiberScalingLinearMap (E := E) a (extChartAt I.tangent x₀ q) :=
    extChartAt_tangent_fiberScaling (I := I) x₀ a hfoot
  rw [hpt] at h2
  -- conjugation: `Φ ∘ Λ_a = S_a ∘ Φ` near the chart image of `q`
  set Φ : E × E → TangentBundle I M := ⇑(extChartAt I.tangent x₀).symm with hΦ
  set z : E × E := extChartAt I.tangent x₀ q with hz
  have hz_tgt : z ∈ (extChartAt I.tangent x₀).target :=
    (extChartAt I.tangent x₀).map_source hq_esrc
  have hev : (fun y => Φ (fiberScalingLinearMap (E := E) a y)) =ᶠ[𝓝 z]
      (fun y => fiberScaling (I := I) a (Φ y)) := by
    have htgt : (extChartAt I.tangent x₀).target ∈ 𝓝 z :=
      extChartAt_target_mem_nhds' hz_tgt
    filter_upwards [htgt] with y hy
    have hysrc : Φ y ∈ (extChartAt I.tangent x₀).source :=
      (extChartAt I.tangent x₀).map_target hy
    have hyfoot : (Φ y).proj ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [extChartAt_source, TangentBundle.mem_chart_source_iff] at hysrc
      rw [TangentBundle.trivializationAt_baseSet]
      exact hysrc
    have hSy_src : fiberScaling (I := I) a (Φ y) ∈
        (extChartAt I.tangent x₀).source := by
      rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
      rw [extChartAt_source, TangentBundle.mem_chart_source_iff] at hysrc
      exact hysrc
    have hkey : extChartAt I.tangent x₀ (fiberScaling (I := I) a (Φ y)) =
        fiberScalingLinearMap (E := E) a y := by
      rw [extChartAt_tangent_fiberScaling (I := I) x₀ a hyfoot,
        (extChartAt I.tangent x₀).right_inv hy]
    calc Φ (fiberScalingLinearMap (E := E) a y)
        = Φ (extChartAt I.tangent x₀ (fiberScaling (I := I) a (Φ y))) := by rw [hkey]
      _ = fiberScaling (I := I) a (Φ y) :=
          (extChartAt I.tangent x₀).left_inv hSy_src
  -- differentiate both sides of the conjugation identity at `z`
  have hΦ_mdiff : MDifferentiableAt 𝓘(ℝ, E × E) I.tangent Φ z := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I.tangent)
      (x := x₀) hz_tgt
    rw [ModelWithCorners.Boundaryless.range_eq_univ] at h
    exact h.mdifferentiableAt Filter.univ_mem
  have hΦ_mdiff' : MDifferentiableAt 𝓘(ℝ, E × E) I.tangent Φ
      (fiberScalingLinearMap (E := E) a z) := by
    have hz'_tgt : fiberScalingLinearMap (E := E) a z ∈ (extChartAt I.tangent x₀).target := by
      rw [← hpt]
      exact (extChartAt I.tangent x₀).map_source (by
        rw [extChartAt_source]; exact hq'_src)
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I.tangent)
      (x := x₀) hz'_tgt
    rw [ModelWithCorners.Boundaryless.range_eq_univ] at h
    exact h.mdifferentiableAt Filter.univ_mem
  have hΛ_mdiff : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E)
      (⇑(fiberScalingLinearMap (E := E) a)) z :=
    (fiberScalingLinearMap (E := E) a).hasMFDerivAt.mdifferentiableAt
  have hΦz : Φ z = q := (extChartAt I.tangent x₀).left_inv hq_esrc
  have hSa_mdiff : MDifferentiableAt I.tangent I.tangent
      (fiberScaling (I := I) (M := M) a) (Φ z) :=
    (hasMFDerivAt_fiberScaling (I := I) (M := M) a (Φ z)).mdifferentiableAt
  have hcomp1 : mfderiv 𝓘(ℝ, E × E) I.tangent
      (fun y => Φ (fiberScalingLinearMap (E := E) a y)) z =
      (mfderiv 𝓘(ℝ, E × E) I.tangent Φ (fiberScalingLinearMap (E := E) a z)).comp
        (fiberScalingLinearMap (E := E) a) := by
    have := mfderiv_comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ, E × E)) (I'' := I.tangent)
      z hΦ_mdiff' hΛ_mdiff
    rw [(fiberScalingLinearMap (E := E) a).hasMFDerivAt.mfderiv] at this
    exact this
  have hcomp2 : mfderiv 𝓘(ℝ, E × E) I.tangent
      (fun y => fiberScaling (I := I) a (Φ y)) z =
      (mfderiv I.tangent I.tangent (fiberScaling (I := I) (M := M) a) (Φ z)).comp
        (mfderiv 𝓘(ℝ, E × E) I.tangent Φ z) :=
    mfderiv_comp z hSa_mdiff hΦ_mdiff
  have hev_deriv : mfderiv 𝓘(ℝ, E × E) I.tangent
      (fun y => Φ (fiberScalingLinearMap (E := E) a y)) z =
      mfderiv 𝓘(ℝ, E × E) I.tangent
        (fun y => fiberScaling (I := I) a (Φ y)) z :=
    Filter.EventuallyEq.mfderiv_eq hev
  rw [hcomp1, hcomp2, mfderiv_fiberScaling (I := I) (M := M) a (Φ z)] at hev_deriv
  -- read off the identity applied to `w`
  have hfinal := DFunLike.congr_fun hev_deriv w
  rw [h1, h2]
  rw [hΦz] at hfinal
  exact hfinal

end SymmLNaturality

section SprayKeystone

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Degree-2 graded homogeneity of the chart-fixed geodesic spray in
definitional coordinates** (do Carmo Ch. 3, the heart of Lemma 2.6). For every
`q : TM` (no chart hypothesis — off the chart domain both sides are junk `0`):

`G(S_a q) = Λ_a (a • G q)`, i.e. `G(S_a q) = (a • (G q).1, a² • (G q).2)`

where `G = geodesicVectorFieldChart g α` is the chart-fixed geodesic spray,
`S_a = fiberScaling a`, and both sides are read in the definitional `E × E`
presentation of the double tangent spaces. -/
theorem geodesicVectorFieldChart_fiberScaling (g : RiemannianMetric I M) (α : M)
    (a : ℝ) (q : TangentBundle I M) :
    geodesicVectorFieldChart (I := I) g α (fiberScaling (I := I) a q) =
      fiberScalingLinearMap (E := E) a
        (a • geodesicVectorFieldChart (I := I) g α q) := by
  classical
  set e₀ := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he₀
  by_cases hq : q.proj ∈ (chartAt H α).source
  · -- on the chart domain: symmL naturality + coordinate pushforward
    have hfoot : q.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hq
    have hfiber : geodesicVectorFieldChartFiber (I := I) g α
        (fiberScaling (I := I) a q) =
        fiberScalingLinearMap (E := E) a
          (a • geodesicVectorFieldChartFiber (I := I) g α q) := by
      rw [geodesicVectorFieldChartFiber_fiberScaling (I := I) g α a hfoot,
        geodesicVectorFieldChartFiber_eq_sprayCoord]
      have : (a • geodesicSprayCoord (I := I) g α (extChartAt I α q.proj)
          (chartFiberCoord (I := I) α q)) =
          (a • chartFiberCoord (I := I) α q,
            a • (geodesicSprayCoord (I := I) g α (extChartAt I α q.proj)
              (chartFiberCoord (I := I) α q)).2) := by
        rw [Prod.smul_def]
        rfl
      rw [this, fiberScalingLinearMap_apply]
      exact Prod.ext rfl (by rw [smul_smul])
    show e₀.symmL ℝ (fiberScaling (I := I) a q)
        (geodesicVectorFieldChartFiber (I := I) g α (fiberScaling (I := I) a q)) = _
    rw [hfiber]
    rw [symmL_trivializationAt_tangent_fiberScaling (I := I) α a hq
      (a • geodesicVectorFieldChartFiber (I := I) g α q)]
    rw [map_smul]
    rfl
  · -- off the chart domain: both sides are the junk value 0
    have hnot : q ∉ e₀.baseSet := by
      rw [he₀, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]
      exact hq
    have hnot' : fiberScaling (I := I) a q ∉ e₀.baseSet := by
      rw [he₀, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]
      exact hq
    show e₀.symm (fiberScaling (I := I) a q) _ = fiberScalingLinearMap (E := E) a
      (a • e₀.symm q _)
    rw [e₀.symm_apply_of_notMem hnot, e₀.symm_apply_of_notMem hnot']
    rw [smul_zero]
    exact (map_zero _).symm

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Spray equivariance of the fibre-scaling tangent map**: the manifold
derivative of `S_a = fiberScaling a` sends the time-rescaled spray `a • G` at `q` to
the spray at `S_a q`. This is the exact identity consumed by the integral-curve
homogeneity transform (do Carmo Ch. 3, Lemma 2.6). -/
theorem mfderiv_fiberScaling_smul_spray (g : RiemannianMetric I M) (α : M)
    (a : ℝ) (q : TangentBundle I M) :
    (mfderiv I.tangent I.tangent (fiberScaling (I := I) (M := M) a) q)
        (a • geodesicVectorFieldChart (I := I) g α q) =
      geodesicVectorFieldChart (I := I) g α (fiberScaling (I := I) a q) := by
  rw [mfderiv_fiberScaling (I := I) (M := M) a q,
    geodesicVectorFieldChart_fiberScaling (I := I) g α a q]
  rfl

end SprayKeystone

end Geodesic
end Riemannian

end
