import MorganTianLib.Ch02.GradientFlowLine

/-!
# Morgan–Tian Ch. 2 — covariant differentiation along two-parameter maps

Blueprint `lem:covariant-derivative-along-maps`, two-parameter case: for a map
`α : ℝ × ℝ → M` into a Riemannian manifold, the **partial covariant
derivatives** `D/∂s`, `D/∂t` of a field along `α` are the covariant
derivatives (`HasCovDerivAlongAt`, `CovDerivAlongCurve.lean`) of the field
restricted along the frozen curves `s ↦ α (s, t)`, `t ↦ α (s, t)` — so the
algebraic clauses (1)–(2) and the curve clauses (4)–(5) of the blueprint node
are precisely the curve-case lemmas applied to the frozen curves. The
genuinely two-parameter content is clause (3), the **symmetry of mixed
covariant partials**, proved here:

* `hasCovDerivAlongAt_fst_curveVelocity_snd` — the mixed covariant partial
  `D/∂s (∂α/∂t)` exists at `(s₀, t₀)` as soon as `α` is continuous at
  `(s₀, t₀)` with chart representation `u = φ_{α(s₀,t₀)} ∘ α` twice
  continuously differentiable there, with the chart value
  `∂²u/∂s∂t + Γ(∂u/∂s, ∂u/∂t)(u₀)`;
* `hasCovDerivAlongAt_snd_curveVelocity_fst` — the mirrored statement for
  `D/∂t (∂α/∂s)`, with value `∂²u/∂t∂s + Γ(∂u/∂t, ∂u/∂s)(u₀)`;
* `curveVelocity_comp_fst_eq` / `curveVelocity_comp_snd_eq` — the partial
  velocity fields read in the chart at the base point are the partial
  derivatives of `u`;
* `hasCovDerivAlongAt_fst_snd_symm` — blueprint clause (3):
  `D/∂s (∂α/∂t) = D/∂t (∂α/∂s)`, by the symmetry of the second derivative of
  `u` (Schwarz, `ContDiffAt.isSymmSndFDerivAt`) and the symmetry of the
  Christoffel contraction in its two vector slots
  (`chartChristoffelContraction_symm`, the torsion-free property of the
  Levi-Civita connection).

The general `m`-parameter clause reduces to this one: a mixed covariant
partial `D/∂u^a ∂α/∂u^b` only involves the two parameters `u^a, u^b`, so
freezing the remaining `m − 2` parameters reduces it to the two-parameter
statement, exactly as the one-parameter clauses reduce to curves.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:covariant-derivative-along-maps`); do Carmo, *Riemannian
Geometry*, Ch. 3 Lemma 3.4 (symmetry lemma).
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

section TwoParameter

variable {α : ℝ × ℝ → M} {s₀ t₀ : ℝ}

/-- **Math.** The chart representation of a two-parameter map `α` at the base
point `α (s₀, t₀)`: the map `u = φ_{α(s₀,t₀)} ∘ α : ℝ × ℝ → E`. All chart
quantities of the mixed covariant partials at `(s₀, t₀)` are expressed
through `u`. -/
def chartLocalMap (α : ℝ × ℝ → M) (s₀ t₀ : ℝ) : ℝ × ℝ → E :=
  fun p => extChartAt I (α (s₀, t₀)) (α p)

@[simp] theorem chartLocalMap_def (α : ℝ × ℝ → M) (s₀ t₀ : ℝ) (p : ℝ × ℝ) :
    chartLocalMap (I := I) α s₀ t₀ p = extChartAt I (α (s₀, t₀)) (α p) := rfl

/-- **Math.** The horizontal line `s ↦ (s, t₀)` has derivative `(1, 0)`. -/
theorem hasDerivAt_prodMk_fst (s₀ t₀ : ℝ) :
    HasDerivAt (fun s : ℝ => (s, t₀)) ((1 : ℝ), (0 : ℝ)) s₀ :=
  (hasDerivAt_id s₀).prodMk (hasDerivAt_const s₀ t₀)

/-- **Math.** The vertical line `t ↦ (s₀, t)` has derivative `(0, 1)`. -/
theorem hasDerivAt_prodMk_snd (s₀ t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => (s₀, t)) ((0 : ℝ), (1 : ℝ)) t₀ :=
  (hasDerivAt_const t₀ s₀).prodMk (hasDerivAt_id t₀)

variable (hcont : ContinuousAt α (s₀, t₀))
  (hu : ContDiffAt ℝ 2 (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀))

include hcont in
/-- **Math.** A two-parameter map continuous at `(s₀, t₀)` eventually lies in
the chart source at its base point, jointly in both parameters. -/
theorem eventually_mem_chartAt_source_prod :
    ∀ᶠ p in 𝓝 (s₀, t₀), α p ∈ (chartAt H (α (s₀, t₀))).source :=
  hcont.preimage_mem_nhds
    ((chartAt H (α (s₀, t₀))).open_source.mem_nhds (mem_chart_source H _))

include hu in
/-- **Math.** The chart representation of a two-parameter map is twice
continuously differentiable near the base parameters (C² at a point spreads
to a neighbourhood at finite regularity). -/
theorem eventually_contDiffAt_chartLocalMap :
    ∀ᶠ p in 𝓝 (s₀, t₀), ContDiffAt ℝ 2 (chartLocalMap (I := I) α s₀ t₀) p :=
  hu.eventually (by simp)

include hcont hu in
/-- **Math.** The `t`-partial velocity field of `α` along the horizontal curve
`s ↦ α (s, t₀)`, read in the chart at the base point, is the `t`-partial
derivative of the chart representation: for `s` near `s₀`,
`(∂α/∂t)(s, t₀)^{chart} = ∂u/∂t (s, t₀)`. -/
theorem chartFieldCoord_curveVelocity_snd_eventually :
    ∀ᶠ s in 𝓝 s₀,
      chartFieldCoord (I := I) (α (s₀, t₀)) (fun s' => α (s', t₀))
        (fun s' => curveVelocity (I := I) (fun τ => α (s', τ)) t₀) s
      = fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s, t₀) ((0 : ℝ), (1 : ℝ)) := by
  have hchart := eventually_mem_chartAt_source_prod (H := H) hcont
  have hchart2 : ∀ᶠ s in 𝓝 s₀, ∀ᶠ τ in 𝓝 t₀,
      α (s, τ) ∈ (chartAt H (α (s₀, t₀))).source := by
    rw [nhds_prod_eq] at hchart
    exact hchart.curry
  have hline : Filter.Tendsto (fun s : ℝ => (s, t₀)) (𝓝 s₀) (𝓝 (s₀, t₀)) := by
    simpa using ((continuous_id.prodMk continuous_const).tendsto s₀)
  have hu2 := hline.eventually (eventually_contDiffAt_chartLocalMap (I := I) hu)
  filter_upwards [hchart2, hu2] with s hmem_t hu_s
  have hdiff : DifferentiableAt ℝ (chartLocalMap (I := I) α s₀ t₀) (s, t₀) :=
    hu_s.differentiableAt (by simp)
  have hd_t' := hdiff.hasFDerivAt.comp_hasDerivAt t₀ (hasDerivAt_prodMk_snd s t₀)
  have hd_t : HasDerivAt (fun τ => extChartAt I (α (s₀, t₀)) (α (s, τ)))
      (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s, t₀) ((0 : ℝ), (1 : ℝ))) t₀ :=
    hd_t'
  have hkey := chartFieldCoord_curveVelocity_eq (I := I) (x := α (s₀, t₀))
    (γ := fun τ => α (s, τ)) (s := t₀) hmem_t hd_t
  exact hkey

include hcont hu in
/-- **Math.** The `s`-partial velocity field of `α` along the vertical curve
`t ↦ α (s₀, t)`, read in the chart at the base point, is the `s`-partial
derivative of the chart representation: for `t` near `t₀`,
`(∂α/∂s)(s₀, t)^{chart} = ∂u/∂s (s₀, t)`. -/
theorem chartFieldCoord_curveVelocity_fst_eventually :
    ∀ᶠ t in 𝓝 t₀,
      chartFieldCoord (I := I) (α (s₀, t₀)) (fun τ => α (s₀, τ))
        (fun τ => curveVelocity (I := I) (fun s' => α (s', τ)) s₀) t
      = fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t) ((1 : ℝ), (0 : ℝ)) := by
  have hchart := eventually_mem_chartAt_source_prod (H := H) hcont
  have hswap : Filter.Tendsto (fun q : ℝ × ℝ => (q.2, q.1)) (𝓝 (t₀, s₀))
      (𝓝 (s₀, t₀)) := by
    simpa using ((continuous_snd.prodMk continuous_fst).tendsto ((t₀ : ℝ), (s₀ : ℝ)))
  have hchart2 : ∀ᶠ t in 𝓝 t₀, ∀ᶠ s in 𝓝 s₀,
      α (s, t) ∈ (chartAt H (α (s₀, t₀))).source := by
    have := hswap.eventually hchart
    rw [nhds_prod_eq] at this
    exact this.curry
  have hline : Filter.Tendsto (fun t : ℝ => (s₀, t)) (𝓝 t₀) (𝓝 (s₀, t₀)) := by
    simpa using ((continuous_const.prodMk continuous_id).tendsto t₀)
  have hu2 := hline.eventually (eventually_contDiffAt_chartLocalMap (I := I) hu)
  filter_upwards [hchart2, hu2] with t hmem_s hu_t
  have hdiff : DifferentiableAt ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t) :=
    hu_t.differentiableAt (by simp)
  have hd_s' := hdiff.hasFDerivAt.comp_hasDerivAt s₀ (hasDerivAt_prodMk_fst s₀ t)
  have hd_s : HasDerivAt (fun s' => extChartAt I (α (s₀, t₀)) (α (s', t)))
      (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t) ((1 : ℝ), (0 : ℝ))) s₀ :=
    hd_s'
  have hkey := chartFieldCoord_curveVelocity_eq (I := I) (x := α (s₀, t₀))
    (γ := fun s' => α (s', t)) (s := s₀) hmem_s hd_s
  exact hkey

include hcont hu in
/-- **Math.** The `t`-partial velocity of `α` at the base parameters is the
`t`-partial derivative of the chart representation. -/
theorem curveVelocity_comp_snd_eq :
    curveVelocity (I := I) (fun τ => α (s₀, τ)) t₀
      = (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((0 : ℝ), (1 : ℝ)) :
          TangentSpace I (α (s₀, t₀))) := by
  refine curveVelocity_eq_of_hasDerivAt (I := I) ?_
  exact (hu.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t₀
    (hasDerivAt_prodMk_snd s₀ t₀)

include hcont hu in
/-- **Math.** The `s`-partial velocity of `α` at the base parameters is the
`s`-partial derivative of the chart representation. -/
theorem curveVelocity_comp_fst_eq :
    curveVelocity (I := I) (fun s' => α (s', t₀)) s₀
      = (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((1 : ℝ), (0 : ℝ)) :
          TangentSpace I (α (s₀, t₀))) := by
  refine curveVelocity_eq_of_hasDerivAt (I := I) ?_
  exact (hu.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s₀
    (hasDerivAt_prodMk_fst s₀ t₀)

include hcont hu in
/-- **Math.** Blueprint `lem:covariant-derivative-along-maps`(3), first mixed
partial: the covariant derivative `D/∂s (∂α/∂t)` at `(s₀, t₀)` exists, with
chart value `∂²u/∂s∂t + Γ(∂u/∂s, ∂u/∂t)(u₀)` — the coordinate formula for the
mixed covariant partial, read in the chart at the base point. -/
theorem hasCovDerivAlongAt_fst_curveVelocity_snd (g : RiemannianMetric I M) :
    HasCovDerivAlongAt (I := I) g (fun s => α (s, t₀))
      (fun s => curveVelocity (I := I) (fun τ => α (s, τ)) t₀) s₀
      (fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
          ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
        + chartChristoffelContraction (I := I) g (α (s₀, t₀))
            (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((1 : ℝ), (0 : ℝ)))
            (curveVelocity (I := I) (fun τ => α (s₀, τ)) t₀)
            (extChartAt I (α (s₀, t₀)) (α (s₀, t₀)))) := by
  have hline : Filter.Tendsto (fun s : ℝ => (s, t₀)) (𝓝 s₀) (𝓝 (s₀, t₀)) := by
    simpa using ((continuous_id.prodMk continuous_const).tendsto s₀)
  have hmemS : ∀ᶠ s in 𝓝 s₀,
      (fun s' => α (s', t₀)) s ∈ (chartAt H (α (s₀, t₀))).source :=
    hline.eventually (eventually_mem_chartAt_source_prod (H := H) hcont)
  refine ⟨hmemS, fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((1 : ℝ), (0 : ℝ)),
    fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
      ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)), ?_, ?_, rfl⟩
  · exact (hu.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s₀
      (hasDerivAt_prodMk_fst s₀ t₀)
  · have hd2 : DifferentiableAt ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀))
        (s₀, t₀) :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have hcomp : HasDerivAt (fun s => fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s, t₀))
        (fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
          ((1 : ℝ), (0 : ℝ))) s₀ :=
      hd2.hasFDerivAt.comp_hasDerivAt s₀ (hasDerivAt_prodMk_fst s₀ t₀)
    have happ : HasDerivAt
        (fun s => fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s, t₀) ((0 : ℝ), (1 : ℝ)))
        (fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
          ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) s₀ := by
      simpa using hcomp.clm_apply (hasDerivAt_const s₀ ((0 : ℝ), (1 : ℝ)))
    exact happ.congr_of_eventuallyEq
      (chartFieldCoord_curveVelocity_snd_eventually (I := I) hcont hu)

include hcont hu in
/-- **Math.** Blueprint `lem:covariant-derivative-along-maps`(3), second mixed
partial: the covariant derivative `D/∂t (∂α/∂s)` at `(s₀, t₀)` exists, with
chart value `∂²u/∂t∂s + Γ(∂u/∂t, ∂u/∂s)(u₀)`. -/
theorem hasCovDerivAlongAt_snd_curveVelocity_fst (g : RiemannianMetric I M) :
    HasCovDerivAlongAt (I := I) g (fun τ => α (s₀, τ))
      (fun τ => curveVelocity (I := I) (fun s' => α (s', τ)) s₀) t₀
      (fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
          ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))
        + chartChristoffelContraction (I := I) g (α (s₀, t₀))
            (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((0 : ℝ), (1 : ℝ)))
            (curveVelocity (I := I) (fun s' => α (s', t₀)) s₀)
            (extChartAt I (α (s₀, t₀)) (α (s₀, t₀)))) := by
  have hline : Filter.Tendsto (fun t : ℝ => (s₀, t)) (𝓝 t₀) (𝓝 (s₀, t₀)) := by
    simpa using ((continuous_const.prodMk continuous_id).tendsto t₀)
  have hmemT : ∀ᶠ t in 𝓝 t₀,
      (fun τ => α (s₀, τ)) t ∈ (chartAt H (α (s₀, t₀))).source :=
    hline.eventually (eventually_mem_chartAt_source_prod (H := H) hcont)
  refine ⟨hmemT, fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((0 : ℝ), (1 : ℝ)),
    fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
      ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)), ?_, ?_, rfl⟩
  · exact (hu.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t₀
      (hasDerivAt_prodMk_snd s₀ t₀)
  · have hd2 : DifferentiableAt ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀))
        (s₀, t₀) :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have hcomp : HasDerivAt (fun t => fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t))
        (fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
          ((0 : ℝ), (1 : ℝ))) t₀ :=
      hd2.hasFDerivAt.comp_hasDerivAt t₀ (hasDerivAt_prodMk_snd s₀ t₀)
    have happ : HasDerivAt
        (fun t => fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t) ((1 : ℝ), (0 : ℝ)))
        (fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
          ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))) t₀ := by
      simpa using hcomp.clm_apply (hasDerivAt_const t₀ ((1 : ℝ), (0 : ℝ)))
    exact happ.congr_of_eventuallyEq
      (chartFieldCoord_curveVelocity_fst_eventually (I := I) hcont hu)

include hcont hu in
/-- **Math.** Blueprint `lem:covariant-derivative-along-maps`(3), **symmetry of
mixed covariant partials**: for a two-parameter map `α` that is continuous at
`(s₀, t₀)` with C² chart representation there, the mixed covariant partials
`D/∂s (∂α/∂t)` and `D/∂t (∂α/∂s)` both exist at `(s₀, t₀)` and are **equal**.
The chart values differ by the order of the second derivative of `u` —
symmetric by Schwarz's theorem (`ContDiffAt.isSymmSndFDerivAt`) — and by the
order of the Christoffel contraction slots — symmetric by the torsion-free
property of the Levi-Civita connection (`chartChristoffelContraction_symm`). -/
theorem hasCovDerivAlongAt_fst_snd_symm (g : RiemannianMetric I M) :
    ∃ D : E,
      HasCovDerivAlongAt (I := I) g (fun s => α (s, t₀))
        (fun s => curveVelocity (I := I) (fun τ => α (s, τ)) t₀) s₀ D ∧
      HasCovDerivAlongAt (I := I) g (fun τ => α (s₀, τ))
        (fun τ => curveVelocity (I := I) (fun s' => α (s', τ)) s₀) t₀ D := by
  refine ⟨_, hasCovDerivAlongAt_fst_curveVelocity_snd (I := I) hcont hu g, ?_⟩
  have hsnd := hasCovDerivAlongAt_snd_curveVelocity_fst (I := I) hcont hu g
  have hsymm2 : fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
        ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))
      = fderiv ℝ (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀)) (s₀, t₀)
        ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) :=
    (hu.isSymmSndFDerivAt (by simp)) _ _
  have hΓ : chartChristoffelContraction (I := I) g (α (s₀, t₀))
        (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((0 : ℝ), (1 : ℝ)))
        (curveVelocity (I := I) (fun s' => α (s', t₀)) s₀)
        (extChartAt I (α (s₀, t₀)) (α (s₀, t₀)))
      = chartChristoffelContraction (I := I) g (α (s₀, t₀))
        (fderiv ℝ (chartLocalMap (I := I) α s₀ t₀) (s₀, t₀) ((1 : ℝ), (0 : ℝ)))
        (curveVelocity (I := I) (fun τ => α (s₀, τ)) t₀)
        (extChartAt I (α (s₀, t₀)) (α (s₀, t₀))) := by
    rw [curveVelocity_comp_fst_eq (I := I) hcont hu,
      curveVelocity_comp_snd_eq (I := I) hcont hu]
    exact chartChristoffelContraction_symm (I := I) g (α (s₀, t₀)) _ _ _
  rw [hsymm2, hΓ] at hsnd
  exact hsnd

end TwoParameter

end MorganTianLib

end
