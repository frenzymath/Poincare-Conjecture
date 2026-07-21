/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/Homogeneity.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.FiberScaling
import PetersenLib.Riemannian.Geodesic.MaximalInterval

set_option linter.unusedSectionVars false

/-!
# Homogeneity of geodesics (do Carmo Ch. 3, Lemma 2.6)

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M` modelled
on a complete inner-product space `E`, the geodesic with initial data `(p, a • v)`
is the affine time-reparametrisation of the geodesic with initial data `(p, v)`:

`γ(t, p, a • v) = γ(a t, p, v)`.

The bundle-level mechanism is the degree-2 homogeneity of the geodesic spray under
the fibre scaling `S_a := fiberScaling a` (`Geodesic/FiberScaling.lean`): if
`f : ℝ → TM` is an integral curve of the chart-fixed spray, then so is
`t ↦ S_a (f (a t))`, with initial datum scaled by `a` in the fibre.

## Main results

* `IsMIntegralCurveOn.fiberScaling_comp_mul` — the integral-curve transform: the
  fibre-scaled time-rescaled lift of a spray integral curve is again a spray
  integral curve.
* `IsGeodesicOnWithInitial.fiberScale` — the witness-level homogeneity, do Carmo's
  Lemma 2.6: if `γ` is a geodesic on `s` with initial data `(p, v)`, then
  `t ↦ γ (a t)` is a geodesic on `{t | a t ∈ s}` with initial data `(p, a • v)`.
* `MaximalGeodesicWitness.fiberScale`, `maximalGeodesicInterval_fiberScale` — the
  maximal interval scales inversely with the velocity:
  `I_max(p, a • v) = {t | a t ∈ I_max(p, v)}` for `a ≠ 0`.
* `isMIntegralCurveOn_geodesicVectorFieldChart_eqOn` — connected-propagation
  uniqueness for spray integral curves whose common foot stays in the base chart
  (the clopen argument).
* `maximalGeodesic_fiberScale` — the value-level homogeneity for the canonical
  maximal geodesic, `maximalGeodesic g p (a • v) t = maximalGeodesic g p v (a t)`,
  under the chart-validity clause that every witness with initial data
  `(p, a • v)` keeps its foot in the chart at `p` (the same proviso as
  `maximalGeodesic_structure_of_footInSource`; off the chart the chart-`p`-fixed
  spray degenerates and the canonical curve is junk-extended).
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace PetersenLib
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section IntegralCurveTransform

variable [I.Boundaryless]

/-- **Math.** **Integral-curve homogeneity transform** (do Carmo Ch. 3, Lemma 2.6,
bundle level). If `f` is an integral curve of the chart-fixed geodesic spray on
`s`, then the fibre-scaled, time-rescaled lift `t ↦ S_a (f (a t))` is an integral
curve of the same spray on `{t | a t ∈ s}`. The two scalings compensate through
the degree-2 fibre homogeneity of the spray. -/
theorem IsMIntegralCurveOn.fiberScaling_comp_mul
    {g : RiemannianMetric I M} {α : M} {f : ℝ → TangentBundle I M} {s : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) s) (a : ℝ) :
    IsMIntegralCurveOn (fun t => fiberScaling (I := I) a (f (a * t)))
      (geodesicVectorFieldChart (I := I) g α) {t | a * t ∈ s} := by
  have h1 : IsMIntegralCurveOn (f ∘ (· * a))
      (a • geodesicVectorFieldChart (I := I) g α) {t | t * a ∈ s} :=
    hf.comp_mul a
  have hfun : (f ∘ (· * a)) = (fun t => f (a * t)) := by
    funext t; simp [mul_comm]
  have hset : {t : ℝ | t * a ∈ s} = {t : ℝ | a * t ∈ s} := by
    ext t; simp [mul_comm]
  rw [hfun, hset] at h1
  intro t ht
  have hbase := h1 t ht
  have hS := hasMFDerivAt_fiberScaling (I := I) (M := M) a (f (a * t))
  have hcomp := hS.comp_hasMFDerivWithinAt t hbase
  have hderiv : (fiberScalingLinearMap (E := E) a).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((a • geodesicVectorFieldChart (I := I) g α) (f (a * t)))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g α
          (fiberScaling (I := I) a (f (a * t)))) := by
    refine ContinuousLinearMap.ext fun r => ?_
    show fiberScalingLinearMap (E := E) a
        (r • (a • geodesicVectorFieldChart (I := I) g α) (f (a * t))) =
      r • geodesicVectorFieldChart (I := I) g α (fiberScaling (I := I) a (f (a * t)))
    rw [geodesicVectorFieldChart_fiberScaling (I := I) g α a (f (a * t))]
    exact (fiberScalingLinearMap (E := E) a).map_smul r
      ((a • geodesicVectorFieldChart (I := I) g α) (f (a * t)))
  convert hcomp using 1
  exact hderiv.symm

end IntegralCurveTransform

section WitnessTransform

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Homogeneity of geodesics, witness level** (do Carmo Ch. 3,
Lemma 2.6). If `γ` is a geodesic on `s` with initial data `(p, v)`, then the
affine reparametrisation `t ↦ γ (a t)` is a geodesic on `{t | a t ∈ s}` with
initial data `(p, a • v)`: "the geodesic with `a`-scaled initial velocity is the
`a`-fold time-rescaling of the original geodesic, on the inversely rescaled
interval". -/
theorem IsGeodesicOnWithInitial.fiberScale
    {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ} {p : M}
    {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (a : ℝ) :
    IsGeodesicOnWithInitial (I := I) g (fun t => γ (a * t)) {t | a * t ∈ s}
      p (a • v) := by
  obtain ⟨f, hproj, hf0, hint⟩ := hγ
  refine ⟨fun t => fiberScaling (I := I) a (f (a * t)), ?_, ?_,
    IsMIntegralCurveOn.fiberScaling_comp_mul hint a⟩
  · intro t
    exact hproj (a * t)
  · show fiberScaling (I := I) a (f (a * 0)) = _
    rw [mul_zero, hf0]
    rfl

/-- **Math.** **Homogeneity of the maximal-interval witness**: if a geodesic with
initial data `(p, v)` covers time `t`, then a geodesic with initial data
`(p, a • v)` covers time `t / a` (for `a ≠ 0`). -/
theorem MaximalGeodesicWitness.fiberScale
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p} {t : ℝ}
    (h : MaximalGeodesicWitness (I := I) g p v t) {a : ℝ} (ha : a ≠ 0) :
    MaximalGeodesicWitness (I := I) g p (a • v) (t / a) := by
  obtain ⟨γ, J, hJo, hJc, h0, ht, hγ⟩ := h
  refine ⟨fun u => γ (a * u), {u | a * u ∈ J}, ?_, ?_, ?_, ?_, hγ.fiberScale a⟩
  · exact hJo.preimage (continuous_const.mul continuous_id)
  · have himg : {u : ℝ | a * u ∈ J} = (fun x => a⁻¹ * x) '' J := by
      ext u
      constructor
      · intro hu
        exact ⟨a * u, hu, by
          show a⁻¹ * (a * u) = u
          rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]⟩
      · rintro ⟨x, hx, rfl⟩
        show a * (a⁻¹ * x) ∈ J
        rwa [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [himg]
    exact hJc.image _ (continuous_const.mul continuous_id).continuousOn
  · show a * 0 ∈ J
    rwa [mul_zero]
  · show a * (t / a) ∈ J
    rwa [mul_div_cancel₀ _ ha]

/-- **Math.** **Scaling of the maximal interval of definition** (do Carmo Ch. 3,
Lemma 2.6, interval half): for `a ≠ 0`,
`I_max(p, a • v) = {t | a t ∈ I_max(p, v)}`. In particular, if the geodesic with
initial velocity `v` is defined on `(-δ, δ)`, the geodesic with initial velocity
`a • v` is defined on `(-δ/a, δ/a)`. -/
theorem maximalGeodesicInterval_fiberScale
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) {a : ℝ} (ha : a ≠ 0) :
    maximalGeodesicInterval (I := I) g p (a • v) =
      {t | a * t ∈ maximalGeodesicInterval (I := I) g p v} := by
  ext t
  constructor
  · intro htv
    have h := MaximalGeodesicWitness.fiberScale (I := I) htv (inv_ne_zero ha)
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
    have harg : t / a⁻¹ = a * t := by
      rw [div_eq_mul_inv, inv_inv, mul_comm]
    rw [harg] at h
    exact h
  · intro hatv
    have h := MaximalGeodesicWitness.fiberScale (I := I) hatv ha
    have harg : a * t / a = t := by
      rw [mul_div_cancel_left₀ _ ha]
    rw [harg] at h
    exact h

/-- **Math.** **Pointwise uniform interval of definition** (do Carmo Ch. 3,
Prop. 2.7, pointwise-in-`(p, v)` form). For every initial datum `(p, v)` and
every time bound `T`, a positive rescaling `c • v` of the initial velocity makes
the geodesic defined on all of `(-T, T)`: shrinking the velocity extends the
interval of definition, by the homogeneity of geodesics
(\cref{lem:dc-ch3-2-6}). The uniform-in-`q` smooth-family version is the open
composite of Prop. 2.5/2.7. -/
theorem exists_pos_smul_maximalGeodesicInterval
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) (T : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      Set.Ioo (-T) T ⊆ maximalGeodesicInterval (I := I) g p (c • v) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    (maximalGeodesicInterval_isOpen (I := I) g p v) 0
    (zero_mem_maximalGeodesicInterval (I := I) g p v)
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨1, one_pos, ?_⟩
    rw [Set.Ioo_eq_empty (by intro h; linarith)]
    exact Set.empty_subset _
  · refine ⟨δ / (2 * T), by positivity, ?_⟩
    intro t ht
    rw [maximalGeodesicInterval_fiberScale (I := I) g p v
      (ne_of_gt (by positivity))]
    show δ / (2 * T) * t ∈ maximalGeodesicInterval (I := I) g p v
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul,
      abs_of_pos (show (0 : ℝ) < δ / (2 * T) by positivity)]
    have habs : |t| < T := abs_lt.mpr ⟨ht.1, ht.2⟩
    calc δ / (2 * T) * |t| < δ / (2 * T) * T := by
          exact mul_lt_mul_of_pos_left habs (by positivity)
      _ = δ / 2 := by field_simp
      _ < δ := by linarith

end WitnessTransform

section ConnectedPropagation

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **Connected-propagation uniqueness for spray integral curves.** Two
integral curves of the chart-fixed geodesic vector field on an open preconnected
set `J` that agree at some `t₀ ∈ J` agree on all of `J`, provided the foot of the
first curve stays in the base chart-source throughout `J` (where the chart-fixed
spray is the genuine geodesic spray). Clopen argument: the agreement set is closed
by Hausdorffness and open by local (Picard–Lindelöf/Grönwall) uniqueness. -/
theorem isMIntegralCurveOn_geodesicVectorFieldChart_eqOn
    {g : RiemannianMetric I M} {α : M} {f₁ f₂ : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJo : IsOpen J) (hJc : IsPreconnected J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h₁ : IsMIntegralCurveOn f₁ (geodesicVectorFieldChart (I := I) g α) J)
    (h₂ : IsMIntegralCurveOn f₂ (geodesicVectorFieldChart (I := I) g α) J)
    (heq : f₁ t₀ = f₂ t₀)
    (hsrc : ∀ t ∈ J, (f₁ t).proj ∈ (chartAt H α).source) :
    Set.EqOn f₁ f₂ J := by
  classical
  haveI : PreconnectedSpace (↥J) := isPreconnected_iff_preconnectedSpace.mp hJc
  set Tsub : Set (↥J) := {t : ↥J | f₁ (t : ℝ) = f₂ (t : ℝ)} with hTsub_def
  suffices hTsub_univ : Tsub = Set.univ by
    intro t ht
    have ht_sub : (⟨t, ht⟩ : ↥J) ∈ Tsub := by
      have hu : (⟨t, ht⟩ : ↥J) ∈ (Set.univ : Set ↥J) := Set.mem_univ _
      rw [← hTsub_univ] at hu
      exact hu
    exact ht_sub
  have h0_mem : (⟨t₀, ht₀⟩ : ↥J) ∈ Tsub := heq
  have hf₁_cont : Continuous (fun t : ↥J => f₁ (t : ℝ)) :=
    continuousOn_iff_continuous_restrict.mp h₁.continuousOn
  have hf₂_cont : Continuous (fun t : ↥J => f₂ (t : ℝ)) :=
    continuousOn_iff_continuous_restrict.mp h₂.continuousOn
  have hTsub_closed : IsClosed Tsub := by
    have hdiag : IsClosed {p : TangentBundle I M × TangentBundle I M | p.1 = p.2} :=
      isClosed_diagonal
    have hpair_cont : Continuous (fun t : ↥J => (f₁ (t : ℝ), f₂ (t : ℝ))) :=
      hf₁_cont.prodMk hf₂_cont
    have hpre : Tsub = (fun t : ↥J => (f₁ (t : ℝ), f₂ (t : ℝ))) ⁻¹'
        {p : TangentBundle I M × TangentBundle I M | p.1 = p.2} := by
      ext t; rfl
    rw [hpre]
    exact hdiag.preimage hpair_cont
  have hTsub_open : IsOpen Tsub := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hfs : f₁ (s : ℝ) = f₂ (s : ℝ) := hs
    have hsrc_s : (f₁ (s : ℝ)).proj ∈ (chartAt H α).source := hsrc _ s.2
    have h₁_at : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α)
        (s : ℝ) := h₁.isMIntegralCurveAt (hJo.mem_nhds s.2)
    have h₂_at : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α)
        (s : ℝ) := h₂.isMIntegralCurveAt (hJo.mem_nhds s.2)
    have hev : f₁ =ᶠ[𝓝 (s : ℝ)] f₂ :=
      isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
        (I := I) (g := g) (α := α) (t₀ := (s : ℝ))
        (f₁ := f₁) (f₂ := f₂) hsrc_s h₁_at h₂_at hfs
    rcases Filter.eventually_iff_exists_mem.mp hev with ⟨U, hU_nhds, hU_eq⟩
    rcases mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem⟩
    refine Filter.mem_of_superset
      (hV_open.preimage continuous_subtype_val |>.mem_nhds hV_mem) ?_
    intro u hu
    exact hU_eq _ (hVU hu)
  exact (IsClopen.eq_univ ⟨hTsub_closed, hTsub_open⟩ ⟨_, h0_mem⟩ :)

/-- **Math.** **Agreement of initial-data geodesic witnesses.** Two geodesics with
the same initial data `(p, v)` on open witness sets agree on any preconnected open
subset of the overlap containing `0`, provided the first witness keeps its foot in
the chart at `p` there. -/
theorem IsGeodesicOnWithInitial.eqOn
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {J₁ J₂ J : Set ℝ} {p : M}
    {v : TangentSpace I p}
    (h₁ : IsGeodesicOnWithInitial (I := I) g γ₁ J₁ p v)
    (h₂ : IsGeodesicOnWithInitial (I := I) g γ₂ J₂ p v)
    (hJo : IsOpen J) (hJc : IsPreconnected J) (h0 : (0 : ℝ) ∈ J)
    (hJ₁ : J ⊆ J₁) (hJ₂ : J ⊆ J₂)
    (hsrc : ∀ t ∈ J, γ₁ t ∈ (chartAt H p).source) :
    Set.EqOn γ₁ γ₂ J := by
  obtain ⟨f₁, hproj₁, hf₁0, hint₁⟩ := h₁
  obtain ⟨f₂, hproj₂, hf₂0, hint₂⟩ := h₂
  have heq0 : f₁ 0 = f₂ 0 := by rw [hf₁0, hf₂0]
  have hsrc' : ∀ t ∈ J, (f₁ t).proj ∈ (chartAt H p).source := by
    intro t ht
    rw [hproj₁ t]
    exact hsrc t ht
  have heqf : Set.EqOn f₁ f₂ J :=
    isMIntegralCurveOn_geodesicVectorFieldChart_eqOn (I := I)
      hJo hJc h0 (hint₁.mono hJ₁) (hint₂.mono hJ₂) heq0 hsrc'
  intro t ht
  rw [← hproj₁ t, ← hproj₂ t, heqf ht]

end ConnectedPropagation

section ValueHomogeneity

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **Homogeneity of the canonical maximal geodesic** (do Carmo Ch. 3,
Lemma 2.6): `γ(t, p, a • v) = γ(a t, p, v)` for `a ≠ 0` and `a t` in the maximal
interval of `(p, v)`.

The chart-validity clause `hsrc` requires every geodesic witness with the scaled
initial data `(p, a • v)` to keep its foot in the chart at `p` (the same proviso
as `maximalGeodesic_structure_of_footInSource`): the canonical curve is built from
the chart-`p`-fixed spray, which degenerates off the chart. -/
theorem maximalGeodesic_fiberScale
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p} {a t : ℝ}
    (ha : a ≠ 0)
    (hmem : a * t ∈ maximalGeodesicInterval (I := I) g p v)
    (hsrc : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p (a • v) →
        ∀ s ∈ J, γ s ∈ (chartAt H p).source) :
    maximalGeodesic (I := I) g p (a • v) t = maximalGeodesic (I := I) g p v (a * t) := by
  classical
  -- `t` lies in the maximal interval of `(p, a • v)`
  have hmem' : t ∈ maximalGeodesicInterval (I := I) g p (a • v) := by
    rw [maximalGeodesicInterval_fiberScale (I := I) g p v ha]
    exact hmem
  -- the two chosen witnesses
  rw [maximalGeodesic_of_mem (I := I) hmem', maximalGeodesic_of_mem (I := I) hmem]
  obtain ⟨J₁, hJ₁o, hJ₁c, hJ₁0, hJ₁t, hγ₁⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (a • v) hmem'
  obtain ⟨J₂, hJ₂o, hJ₂c, hJ₂0, hJ₂t, hγ₂⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v hmem
  -- transform the `(p, v)`-witness into a `(p, a • v)`-witness
  have hγ₂' : IsGeodesicOnWithInitial (I := I) g
      (fun u => maximalGeodesicChosenCurve (I := I) g p v hmem (a * u))
      {u | a * u ∈ J₂} p (a • v) := hγ₂.fiberScale a
  -- the overlap
  set J : Set ℝ := J₁ ∩ {u | a * u ∈ J₂} with hJ
  have hJo : IsOpen J :=
    hJ₁o.inter (hJ₂o.preimage (continuous_const.mul continuous_id))
  have hpre₂ : IsPreconnected {u : ℝ | a * u ∈ J₂} := by
    have himg : {u : ℝ | a * u ∈ J₂} = (fun x => a⁻¹ * x) '' J₂ := by
      ext u
      constructor
      · intro hu
        exact ⟨a * u, hu, by
          show a⁻¹ * (a * u) = u
          rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]⟩
      · rintro ⟨x, hx, rfl⟩
        show a * (a⁻¹ * x) ∈ J₂
        rwa [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [himg]
    exact hJ₂c.image _ (continuous_const.mul continuous_id).continuousOn
  have hJc : IsPreconnected J :=
    (hJ₁c.ordConnected.inter hpre₂.ordConnected).isPreconnected
  have h0J : (0 : ℝ) ∈ J := ⟨hJ₁0, by show a * 0 ∈ J₂; rwa [mul_zero]⟩
  have htJ : t ∈ J := ⟨hJ₁t, hJ₂t⟩
  -- agreement of the two `(p, a • v)`-witnesses on the overlap
  have heq := IsGeodesicOnWithInitial.eqOn (I := I) hγ₁ hγ₂'
    hJo hJc h0J inter_subset_left inter_subset_right
    (fun s hs => hsrc _ _ hγ₁ s (inter_subset_left hs))
  exact heq htJ

end ValueHomogeneity

end Geodesic
end PetersenLib

end
