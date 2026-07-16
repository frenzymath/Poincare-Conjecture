/- Vendored from DoCarmo `OpenGALib/Riemannian/Connection/ChartFrameBridge.lean` (truncated before the geodesic-dependent tail). Namespace `Riemannian` mapped to
   `PetersenLib`; engineering infrastructure only, not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Connection.ChristoffelBridge
import PetersenLib.Vendored.OpenGA.Connection.ChartChristoffelSmooth

/-!
# The coordinate frame fields closing the chart-Christoffel bridge

do Carmo's Proposition 2.2 property (c) — the manifold-level identity
`DY/dt = ∇_{dc/dt} Y` for the Levi-Civita connection `∇` — was reduced in
`ChristoffelBridge.lean` to the *algebraic* formula (10) tested against a
coordinate frame: for smooth vector fields `X₁, …, X_n` realising the chart
basis at `p`, with vanishing pairwise brackets `[X_a, X_b](p) = 0` and
directional derivatives `X_r⟨X_a, X_b⟩(p) = ∂_r G_{ab}`, the Levi-Civita
covariant derivative is `∇_{X_i} X_j = ∑_m Γ^m_{ij} X_m`
(`christoffel_bridge_vector`).

This file supplies the two genuinely analytic frame identities for the concrete
chart frame `chartBasisVec` and packages the whole bridge
(`lem:dc-ch2-2-2-c-bridge`). The construction:

* **`mfderiv_extChartAt_chartBasisVecFiber`** — the differential of the chart
  sends the frame vector `chartBasisVecFiber α i q` to the constant model basis
  vector `finBasis i`. This is the trivialization ↔ `mfderiv` identity
  (`TangentBundle.continuousLinearMapAt_trivializationAt`) applied to the frame.
* **`chartBasisVecFiber_eventuallyEq_mpullback`** — near `p`, the frame field is
  the chart-pullback of the constant model field `finBasis i` (the linchpin, via
  invertibility of `mfderiv (extChartAt I α)`).
* **`mlieBracket_chartBasisVecFiber_eq_zero`** (discharges `hbr`) — the pairwise
  brackets vanish: by naturality of the Lie bracket
  (`VectorField.mpullback_mlieBracket`) the frame bracket is the chart-pullback
  of the bracket of the constant model fields, which is `0`.
* **`mfderiv_chartGramMatrix_eq_partialDeriv`** (discharges `hdir`) — the
  directional derivative of the frame Gram function equals the partial derivative
  of the chart Gram matrix, by the chart chain rule using
  `mfderiv_extChartAt_chartBasisVecFiber`.

Feeding these to `christoffel_bridge_vector` with `∇ = g.leviCivitaConnection`
gives the frame-field bridge `exists_chartFrame_leviCivita_christoffel`, do
Carmo's formula (10) for the metric's own Levi-Civita connection, closing
`lem:dc-ch2-2-2-c-bridge` and with it `prop:dc-ch2-2-2` property (c).

Reference: do Carmo, *Riemannian Geometry*, Ch. 2 §2, Prop. 2.2 and eq. (10).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The Lie bracket of two constant vector fields on the model space `E`
vanishes identically: both directional-derivative terms are derivatives of
constants. -/
theorem mlieBracket_const_const (c d : E) :
    VectorField.mlieBracket 𝓘(ℝ, E) (fun _ : E => c) (fun _ : E => d) = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  funext x
  show fderiv ℝ (fun _ : E => d) x ((fun _ : E => c) x)
      - fderiv ℝ (fun _ : E => c) x ((fun _ : E => d) x) = 0
  rw [fderiv_fun_const, fderiv_fun_const]
  simp

/-- **Math.** The constant tangent section `x ↦ (x, c)` on the model space `E` is
smooth. -/
theorem contMDiffAt_const_tangentSection (c : E) (x₀ : E) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (TotalSpace.mk' E x c : TangentBundle 𝓘(ℝ, E) E)) x₀ := by
  rw [contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const⟩

/-- **Math.** do Carmo Ch. 2, the chart differential on the coordinate frame. The
manifold differential of the chart `extChartAt I α` sends the chart-basis frame
vector `chartBasisVecFiber α i q` to the constant model basis vector
`finBasis i`. This is the identification of the tangent trivialization with
`mfderiv (extChartAt I α)` (`TangentBundle.continuousLinearMapAt_trivializationAt`)
applied to the frame `(trivializationAt …).symm q (finBasis i)`. -/
theorem mfderiv_extChartAt_chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E)) {q : M}
    (hq : q ∈ (chartAt H α).source) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I α) q (chartBasisVecFiber (I := I) α i q)
      = (Module.finBasis ℝ E) i := by
  have hb : q ∈ (trivializationAt E (TangentSpace I) α).baseSet := hq
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := α) hq]
  exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) α) hb (chartBasisVecFiber (I := I) α i q)).trans
    (trivializationAt_chartBasisVec_snd (I := I) α i hb)

/-- **Math.** The linchpin identity for the frame bracket. Near a chart-source
point `p`, the chart-basis frame field `chartBasisVecFiber α i` coincides with the
chart-pullback of the constant model field `finBasis i` under `extChartAt I α`,
`mpullback I 𝓘(ℝ,E) (extChartAt I α) (fun _ => finBasis i)`. This holds because
`mfderiv (extChartAt I α) q` is invertible and sends the frame vector to
`finBasis i` (`mfderiv_extChartAt_chartBasisVecFiber`). -/
theorem chartBasisVecFiber_eventuallyEq_mpullback (α : M) (i : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H α).source) :
    (fun q => chartBasisVecFiber (I := I) α i q)
      =ᶠ[nhds p]
        VectorField.mpullback I 𝓘(ℝ, E) (extChartAt I α)
          (fun _ => (Module.finBasis ℝ E) i) := by
  have hopen : IsOpen (chartAt H α).source := (chartAt H α).open_source
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hqsrc : q ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  rw [VectorField.mpullback_apply]
  exact (((isInvertible_mfderiv_extChartAt hqsrc).inverse_apply_eq).mpr
    (mfderiv_extChartAt_chartBasisVecFiber (I := I) α i hq).symm).symm

/-- **Math.** do Carmo Ch. 2, §2 — the coordinate frame has **vanishing pairwise
Lie brackets** (discharges `hbr` of `christoffel_bridge_vector`). At any
chart-source point `p`, `[X_a, X_b](p) = 0` for the chart-basis frame
`X_a = chartBasisVecFiber α a`.

By the linchpin identity the frame fields agree near `p` with the chart-pullbacks
of the constant model fields, so — the bracket being local
(`EventuallyEq.mlieBracket_vectorField_eq`) — it equals the bracket of those
pullbacks. Naturality of the bracket (`VectorField.mpullback_mlieBracket`) turns
this into the chart-pullback of the model bracket of the two constant fields,
which is `0` (`mlieBracket_const_const`). -/
theorem mlieBracket_chartBasisVecFiber_eq_zero (α : M) (a b : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H α).source) :
    VectorField.mlieBracket I (fun q => chartBasisVecFiber (I := I) α a q)
      (fun q => chartBasisVecFiber (I := I) α b q) p = 0 := by
  haveI hmsm : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  rw [Filter.EventuallyEq.mlieBracket_vectorField_eq
      (chartBasisVecFiber_eventuallyEq_mpullback (I := I) α a hp)
      (chartBasisVecFiber_eventuallyEq_mpullback (I := I) α b hp)]
  have hsrc_nhds : (chartAt H α).source ∈ nhds p := (chartAt H α).open_source.mem_nhds hp
  have hf : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) p :=
    (contMDiffOn_extChartAt (I := I) (x := α) (n := ∞)).contMDiffAt hsrc_nhds
  have hV : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun x => (TotalSpace.mk' E x ((Module.finBasis ℝ E) a) : TangentBundle 𝓘(ℝ, E) E))
      (extChartAt I α p) :=
    (contMDiffAt_const_tangentSection _ _).mdifferentiableAt (by decide)
  have hW : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun x => (TotalSpace.mk' E x ((Module.finBasis ℝ E) b) : TangentBundle 𝓘(ℝ, E) E))
      (extChartAt I α p) :=
    (contMDiffAt_const_tangentSection _ _).mdifferentiableAt (by decide)
  have hn : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top
  rw [← VectorField.mpullback_mlieBracket hV hW hf hn]
  rw [mlieBracket_const_const, VectorField.mpullback_zero, Pi.zero_apply]

/-- **Math.** do Carmo Ch. 2, §2 — the **directional-derivative–partial-derivative
identity** for the coordinate frame (discharges `hdir` of
`christoffel_bridge_vector`). The manifold directional derivative of the chart Gram
entry `q ↦ G_{ab}(q)` along the frame vector `chartBasisVecFiber α r p` equals the
partial derivative `∂_r G_{ab}` of the chart Gram matrix read in the chart.

The chart Gram entry agrees near `p` with `chartGramOnE g α a b ∘ extChartAt I α`
(by `left_inv` of the chart), so its manifold differential factors through the
chart chain rule (`mfderiv_comp`); the inner factor
`mfderiv (extChartAt I α) p (chartBasisVecFiber α r p) = finBasis r`
(`mfderiv_extChartAt_chartBasisVecFiber`) turns the outer manifold derivative into
`fderiv (chartGramOnE g α a b) (extChartAt I α p) (finBasis r) = ∂_r G_{ab}`. -/
theorem mfderiv_chartGramMatrix_eq_partialDeriv (g : RiemannianMetric I M) (α : M)
    (a b r : Fin (Module.finrank ℝ E)) {p : M} (hp : p ∈ (chartAt H α).source) :
    mfderiv I 𝓘(ℝ, ℝ) (fun q => chartGramMatrix (I := I) g α q a b) p
        (chartBasisVecFiber (I := I) α r p)
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) (extChartAt I α p) := by
  have hpsrc : p ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hy : extChartAt I α p ∈ (extChartAt I α).target := (extChartAt I α).map_source hpsrc
  have hEq : (fun q => chartGramMatrix (I := I) g α q a b)
      =ᶠ[nhds p] ((chartGramOnE (I := I) g α a b) ∘ (extChartAt I α)) := by
    have hopen : IsOpen (chartAt H α).source := (chartAt H α).open_source
    filter_upwards [hopen.mem_nhds hp] with q hq
    show chartGramMatrix (I := I) g α q a b = chartGramOnE (I := I) g α a b (extChartAt I α q)
    rw [chartGramOnE_def, (extChartAt I α).left_inv (by rwa [extChartAt_source])]
  have hGdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (chartGramOnE (I := I) g α a b)
      (extChartAt I α p) := by
    have hcd : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α a b) (extChartAt I α p) :=
      (chartGramOnE_contDiffOn (I := I) g α a b).contDiffAt
        (extChartAt_target_mem_nhds' (I := I) hy)
    exact hcd.contMDiffAt.mdifferentiableAt (by decide)
  have hφdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) p := mdifferentiableAt_extChartAt hp
  rw [hEq.mfderiv_eq, mfderiv_comp p hGdiff hφdiff]
  show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (chartGramOnE (I := I) g α a b) (extChartAt I α p))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) p (chartBasisVecFiber (I := I) α r p))
    = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) (extChartAt I α p)
  rw [mfderiv_extChartAt_chartBasisVecFiber (I := I) α r hp, mfderiv_eq_fderiv]
  rfl


end PetersenLib
