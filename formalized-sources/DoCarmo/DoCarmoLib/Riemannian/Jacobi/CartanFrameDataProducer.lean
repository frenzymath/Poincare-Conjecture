import DoCarmoLib.Riemannian.Jacobi.CartanParallelFrame
import DoCarmoLib.Riemannian.Jacobi.MetricOrthoBasis
import DoCarmoLib.Riemannian.Jacobi.JacobiConstantCurvatureConjugate
import DoCarmoLib.Riemannian.Jacobi.CartanExpNormTransfer
import DoCarmoLib.Riemannian.Jacobi.CartanExpNormTransferGeneral

/-!
# do Carmo Ch. 8, §2 — E. Cartan's frames and `φ_t`, as an explicit construction

`metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt` (the variable-curvature exp-side
chain) takes its two parallel orthonormal frames `Efr`, `Ebar` and do Carmo's parallel-transport
conjugate `φ_t` as **abstract data**, constrained by `hEpar`/`hEbarpar`/`hEorth`/`hEbarorth`,
`hvel` (`φ_t` carries `γ'` to `γ̃'`), `hfr` (`φ_t` carries `eⱼ` to `ẽⱼ`), `hφ0` (`φ_0 = i`) and
`hφ` (the curvature match). This file produces all of them except `hφ`, which is E. Cartan's own
hypothesis and must remain one.

## The seed-point problem, and why conjugating the seed solves it

`parallelTransportConjugate` builds `φ_t = P̃_t ∘ i ∘ P_t⁻¹` out of the two parallel transports
`P_t`, `P̃_t` *from the left endpoint `a'`*: the seed time is not a parameter, it is baked into
`parallelFieldSeed`. So the `φ` it returns satisfies `φ_{a'} = i` (`parallelTransportConjugate_left`),
whereas the transfer wants `φ_0 = i` — and `0` is **interior** to the window `[a', b']`, since the
window must satisfy `a' < 0 < 1 < b'`.

The fix does **not** need a re-based transport (there is no `P_{a→c} = P_{b→c} ∘ P_{a→b}` in the
library, and none is added here). Conjugate the *seed map* instead: feed
`parallelTransportConjugate` not `i` but

  `j = P̃_0⁻¹ ∘ i ∘ P_0` (`cartanSeed`),

the map `i` viewed from time `a'` rather than from time `0`. Then at any `t`

  `φ_t = P̃_t ∘ (P̃_0⁻¹ ∘ i ∘ P_0) ∘ P_t⁻¹`,

and at `t = 0` the two outer transports cancel their own inverses, leaving `φ_0 = i` exactly. This
costs one line (`LinearEquiv.apply_symm_apply` twice) and no new mathematics, because
`parallelTransportAlongEquiv` — the inverted propagator that the analogous Jacobi-side interior
seeding (`JacobiInteriorData.lean`) had to build from time reversal and backward uniqueness — is
already available here: parallel transport is invertible for the cheap reason that it is a metric
isometry.

## Why `φ` is a definition and not an existential

`cartanPhi` is a **`def`**, not something produced existentially, and this is load-bearing rather
than stylistic. Its seed `cartanSeed` depends only on `g, g', p, p', v, i` and the window — *not*
on the frames — so nothing forces `φ` to be hidden behind an `∃`.

That matters because E. Cartan's curvature hypothesis is a statement about **this** `φ`. An earlier
version of this file produced `φ` existentially and therefore had to state the curvature match for
*every* `φ` that is a metric isometry carrying `γ'` to `γ̃'` and restricting to `i` at `0`. That
quantified hypothesis is much stronger than do Carmo's, and demonstrably so: at any interior
`t ≠ 0` one may replace `φ_t` by `φ_t ∘ ρ` for any `g`-isometry `ρ` of `T_{γ(t)}M` fixing `γ'(t)`,
and the three antecedents survive; so the hypothesis secretly forces the curvature at `γ(t)` to be
invariant under all of `O(n-1)` about the velocity — isotropy that holds in constant curvature but
fails for a general `M`. Naming `φ` removes that hole entirely.

## Contents

* `cartanTransportZero` — `P_0`, parallel transport along `γ_v` from `a'` to the interior time `0`.
* `cartanSeed` — `j = P̃_0⁻¹ ∘ i ∘ P_0`, and `metricInner_cartanSeed`: it is an isometry at `a'`.
* `cartanPhi` — do Carmo's `φ_t`, with `cartanPhi_zero` (`φ_0 = i`), `cartanPhi_velocity`
  (`hvel`) and `metricInner_cartanPhi` (`φ_t` a metric isometry).
* `exists_cartanFrameData` — parallel orthonormal frames on both sides matched by `cartanPhi`.
* `metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt_of_isLocalDiffeomorphAt` — the
  transfer with its frames, `φ`, and both no-conjugacy clauses discharged.

The frames are seeded by `exists_metricOrthonormalBasis` at `γ(a')` — no orthonormal basis needs to
be transported from `p`, since orthonormality is required at every time and parallel transport
supplies it from any single time.

What this file does **not** discharge: the single-chart hypotheses `hsrc`/`hsrcbar`
(`lem:dc-ch8-2-1-single-chart`, still open) and the curvature match `hφ` (E. Cartan's hypothesis).

Blueprint: `lem:dc-ch8-2-1-phi`, `lem:dc-ch8-2-1-transported-frame`.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-! ### The standing geodesic data of a window -/

/-- **Math.** `γ_v` is a geodesic on any time window. -/
theorem isGeodesicOn_globalGeodesic_Icc (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) (a b : ℝ) :
    IsGeodesicOn (I := I) g (globalGeodesic (I := I) g hg p v) (Icc a b) :=
  fun t _ => isGeodesic_globalGeodesic g hg p v t

/-- **Math.** `γ_v` is continuous at every time of any window. -/
theorem continuousAt_globalGeodesic_Icc (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) (a b : ℝ) :
    ∀ t ∈ Icc a b, ContinuousAt (globalGeodesic (I := I) g hg p v) t :=
  fun _t _ => (continuous_globalGeodesic g hg p v).continuousAt

/-! ### `P_0`, the seed `j`, and `φ_t` -/

/-- **Math.** `P_0`: parallel transport along `γ_v` from the window's left endpoint `a'` to the
interior time `0`. An isomorphism, since parallel transport is a metric isometry. -/
def cartanTransportZero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : E) {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') : E ≃ₗ[ℝ] E :=
  parallelTransportAlongEquiv (I := I) (show a' < b' by linarith)
    (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
    (continuousAt_globalGeodesic_Icc g hg p v a' b')
    (show (0 : ℝ) ∈ Icc a' b' from ⟨ha'.le, by linarith⟩)

/-- **Math.** `j = P̃_0⁻¹ ∘ i ∘ P_0`, the linear isometry `i` read from the window's left endpoint
`a'` rather than from time `0`. Feeding this to `parallelTransportConjugate` in place of `i` is what
makes `cartanPhi_zero` hold; see the module docstring. -/
def cartanSeed (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (p : M) (p' : M') (v : E) (i : E ≃L[ℝ] E)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') : E ≃ₗ[ℝ] E :=
  (cartanTransportZero (I := I) g hg p v ha' hb').trans
    ((i : E ≃ₗ[ℝ] E).trans (cartanTransportZero (I := I') g' hg' p' (i v) ha' hb').symm)

/-- **Math.** **do Carmo's `φ_t`**, along the geodesic pair `γ_v`, `γ_{i(v)}` on a window `[a',b']`
with `a' < 0 < 1 < b'`: the parallel-transport conjugate of `i`, re-seeded at `a'` through
`cartanSeed` so that `φ_0 = i` (`cartanPhi_zero`) rather than `φ_{a'} = i`.

Off the window `φ` is set to `i`; that branch is never used — every statement about `cartanPhi` in
this file is either restricted to `t ∈ [a',b']` or taken at `t = 0`, which lies in the window. -/
def cartanPhi (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (p : M) (p' : M') (v : E) (i : E ≃L[ℝ] E)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') : ℝ → E → E :=
  fun t =>
    if ht : t ∈ Icc a' b' then
      (parallelTransportConjugate (I := I) (I' := I') (show a' < b' by linarith)
        (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
        (continuousAt_globalGeodesic_Icc g hg p v a' b')
        (isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
        (continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')
        (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb').toLinearMap ht : E → E)
    else (i : E → E)

section Data

variable (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
  (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
  (p : M) (p' : M') (v : E) (i : E ≃L[ℝ] E)

/-- **Math.** On the window, `cartanPhi` is the parallel-transport conjugate of `cartanSeed`. -/
theorem cartanPhi_apply_of_mem {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b')
    {t : ℝ} (ht : t ∈ Icc a' b') (x : E) :
    cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t x
      = parallelTransportConjugate (I := I) (I' := I') (show a' < b' by linarith)
          (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
          (continuousAt_globalGeodesic_Icc g hg p v a' b')
          (isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
          (continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')
          (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb').toLinearMap ht x := by
  rw [cartanPhi, dif_pos ht]

/-- **Math.** `φ_t` is linear on the window, being a composite of linear maps. -/
theorem cartanPhi_isLinear {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b')
    {t : ℝ} (ht : t ∈ Icc a' b') :
    IsLinearMap ℝ (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t) := by
  constructor
  · intro x y
    simp only [cartanPhi_apply_of_mem g hg g' hg' p p' v i ha' hb' ht]
    exact map_add _ x y
  · intro c x
    simp only [cartanPhi_apply_of_mem g hg g' hg' p p' v i ha' hb' ht]
    exact map_smul _ c x

/-- **Math.** **`j` is a linear isometry `T_{γ(a')}M → T_{γ̃(a')}M̃`.** Both parallel transports
preserve their Riemannian pairings and `i` is an isometry at `γ(0) = p`, `γ̃(0) = p̃`, so the
composite `j = P̃_0⁻¹ ∘ i ∘ P_0` is an isometry at the window's left endpoint — which is where the
frame producer needs it. -/
theorem metricInner_cartanSeed
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') (u w : E) :
    g'.metricInner (globalGeodesic (I := I') g' hg' p' (i v) a')
        (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' u
          : TangentSpace I' (globalGeodesic (I := I') g' hg' p' (i v) a'))
        (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' w)
      = g.metricInner (globalGeodesic (I := I) g hg p v a')
          (u : TangentSpace I (globalGeodesic (I := I) g hg p v a')) w := by
  set γ := globalGeodesic (I := I) g hg p v with hγdef
  set γbar := globalGeodesic (I := I') g' hg' p' (i v) with hγbardef
  have hab : a' < b' := by linarith
  have h0 : (0 : ℝ) ∈ Icc a' b' := ⟨ha'.le, by linarith⟩
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγbar0 : γbar 0 = p' := globalGeodesic_zero g' hg' p' (i v)
  set P0 := cartanTransportZero (I := I) g hg p v ha' hb' with hP0
  set P0bar := cartanTransportZero (I := I') g' hg' p' (i v) ha' hb' with hP0bar
  have happ : ∀ x : E, cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' x
      = P0bar.symm (i (P0 x)) := fun x => rfl
  have hPiso : ∀ x y : E, g.metricInner (γ 0) (P0 x : TangentSpace I (γ 0)) (P0 y)
      = g.metricInner (γ a') (x : TangentSpace I (γ a')) y := fun x y =>
    metricInner_parallelTransportAlong (I := I) hab
      (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
      (continuousAt_globalGeodesic_Icc g hg p v a' b') h0 x y
  have hPbariso : ∀ x y : E,
      g'.metricInner (γbar 0) (P0bar x : TangentSpace I' (γbar 0)) (P0bar y)
        = g'.metricInner (γbar a') (x : TangentSpace I' (γbar a')) y := fun x y =>
    metricInner_parallelTransportAlong (I := I') hab
      (isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
      (continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b') h0 x y
  rw [happ u, happ w, ← hPbariso (P0bar.symm (i (P0 u))) (P0bar.symm (i (P0 w))),
    P0bar.apply_symm_apply, P0bar.apply_symm_apply, hγbar0, hi (P0 u) (P0 w), ← hγ0]
  exact hPiso u w

/-- **Math.** **`φ_0 = i`** — the point of the re-seeding. At `t = 0` the outer transports cancel
their own inverses: `φ_0 = P̃_0 ∘ (P̃_0⁻¹ ∘ i ∘ P_0) ∘ P_0⁻¹ = i`. -/
theorem cartanPhi_zero {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') (x : E) :
    cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' 0 x = i x := by
  have h0 : (0 : ℝ) ∈ Icc a' b' := ⟨ha'.le, by linarith⟩
  rw [cartanPhi_apply_of_mem g hg g' hg' p p' v i ha' hb' h0]
  set P0 := cartanTransportZero (I := I) g hg p v ha' hb' with hP0
  set P0bar := cartanTransportZero (I := I') g' hg' p' (i v) ha' hb' with hP0bar
  show P0bar (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' (P0.symm x)) = i x
  show P0bar (P0bar.symm (i (P0 (P0.symm x)))) = i x
  rw [P0.apply_symm_apply]
  exact P0bar.apply_symm_apply (i x)

/-- **Math.** **`hvel`: `φ_t` carries `γ'(t)` to `γ̃'(t)`.** Both velocity fields are parallel, and
their seed identity at `a'` reduces through `P_0`, `P̃_0` to `i(γ'(0)) = i(v) = γ̃'(0)`. -/
theorem cartanPhi_velocity {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') :
    ∀ t ∈ Icc a' b',
      cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t
          (mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) t 1)
        = mfderiv 𝓘(ℝ, ℝ) I' (globalGeodesic (I := I') g' hg' p' (i v)) t 1 := by
  intro t ht
  rw [cartanPhi_apply_of_mem g hg g' hg' p p' v i ha' hb' ht]
  set γ := globalGeodesic (I := I) g hg p v with hγdef
  set γbar := globalGeodesic (I := I') g' hg' p' (i v) with hγbardef
  have hab : a' < b' := by linarith
  have h0 : (0 : ℝ) ∈ Icc a' b' := ⟨ha'.le, by linarith⟩
  set P0 := cartanTransportZero (I := I) g hg p v ha' hb' with hP0
  set P0bar := cartanTransportZero (I := I') g' hg' p' (i v) ha' hb' with hP0bar
  refine (eq_parallelTransportConjugate_of_isParallelFieldAlongOn
    (hab := show a' < b' by linarith)
    (hgeo := isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
    (hγc := continuousAt_globalGeodesic_Icc g hg p v a' b')
    (hgeobar := isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
    (hγcbar := continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')
    (i := (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb').toLinearMap)
    (isParallelFieldAlongOn_velocity (I := I) g hab
      (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
      (continuousAt_globalGeodesic_Icc g hg p v a' b'))
    (isParallelFieldAlongOn_velocity (I := I') g' hab
      (isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
      (continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')) ?_ ht).symm
  -- the seed identity at `a'`: `γ̃'(a') = j(γ'(a'))`
  have hv0 : P0.symm (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) = mfderiv 𝓘(ℝ, ℝ) I γ a' 1 :=
    parallelTransportAlongEquiv_symm_apply_of_isParallelFieldAlongOn (I := I)
      (isParallelFieldAlongOn_velocity (I := I) g hab
        (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
        (continuousAt_globalGeodesic_Icc g hg p v a' b')) h0
  have hvbar0 : P0bar.symm (mfderiv 𝓘(ℝ, ℝ) I' γbar 0 1) = mfderiv 𝓘(ℝ, ℝ) I' γbar a' 1 :=
    parallelTransportAlongEquiv_symm_apply_of_isParallelFieldAlongOn (I := I')
      (isParallelFieldAlongOn_velocity (I := I') g' hab
        (isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
        (continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')) h0
  have hP0vel : P0 (mfderiv 𝓘(ℝ, ℝ) I γ a' 1) = v := by
    rw [← hv0, P0.apply_symm_apply, hγdef]
    exact mfderiv_globalGeodesic_zero g hg p v
  show mfderiv 𝓘(ℝ, ℝ) I' γbar a' 1
    = (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb').toLinearMap
        (mfderiv 𝓘(ℝ, ℝ) I γ a' 1)
  show mfderiv 𝓘(ℝ, ℝ) I' γbar a' 1 = P0bar.symm (i (P0 (mfderiv 𝓘(ℝ, ℝ) I γ a' 1)))
  rw [hP0vel, ← hvbar0]
  refine congrArg P0bar.symm ?_
  rw [hγbardef]
  exact mfderiv_globalGeodesic_zero g' hg' p' (i v)

/-- **Math.** **`φ_t` is a metric isometry** `T_{γ(t)}M → T_{γ̃(t)}M̃` on the window: both parallel
transports and `j` are isometries. -/
theorem metricInner_cartanPhi
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') {t : ℝ} (ht : t ∈ Icc a' b') (u w : E) :
    g'.metricInner (globalGeodesic (I := I') g' hg' p' (i v) t)
        (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t u
          : TangentSpace I' (globalGeodesic (I := I') g' hg' p' (i v) t))
        (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t w)
      = g.metricInner (globalGeodesic (I := I) g hg p v t)
          (u : TangentSpace I (globalGeodesic (I := I) g hg p v t)) w := by
  rw [cartanPhi_apply_of_mem g hg g' hg' p p' v i ha' hb' ht,
    cartanPhi_apply_of_mem g hg g' hg' p p' v i ha' hb' ht]
  exact metricInner_parallelTransportConjugate (I := I) (I' := I')
    (show a' < b' by linarith)
    (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
    (continuousAt_globalGeodesic_Icc g hg p v a' b')
    (isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
    (continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')
    (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb').toLinearMap
    (metricInner_cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i hi ha' hb') ht u w

end Data

/-- **Math.** **E. Cartan's frames, matched by `cartanPhi`.** Let `M`, `M̃` be complete, `p ∈ M`,
`p̃ ∈ M̃`, let `i : T_pM → T_{p̃}M̃` be a linear isometry, let `v ∈ T_pM`, and let `[a', b']` be a
window with `a' < 0 < 1 < b'`. Along `γ = γ_v` and `γ̃ = γ_{i(v)}` there exist parallel
**orthonormal** frames `e`, `ẽ` on `[a', b']` with

  `φ_t(eⱼ(t)) = ẽⱼ(t)` for `t ∈ [a', b']`,

where `φ = cartanPhi …`. Only the frames are existential: `φ` is a definition, and its own
properties — `φ_0 = i` (`cartanPhi_zero`), `φ_t(γ'(t)) = γ̃'(t)` (`cartanPhi_velocity`), linearity
(`cartanPhi_isLinear`) and metric preservation (`metricInner_cartanPhi`) — are separate lemmas that
do not depend on the frames.

Together these supply every abstract-data hypothesis of
`metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt` **except** the curvature match, which
is E. Cartan's own hypothesis.

Proof: seed the frames by an orthonormal basis at `γ(a')` (`exists_metricOrthonormalBasis`) and
apply `exists_transportedParallelOrthoFrame_pair` through `cartanSeed`, whose isometry at `a'` is
`metricInner_cartanSeed`. The matching clause is then
`eq_parallelTransportConjugate_of_isParallelFieldAlongOn` applied to the frames, whose seed identity
at `a'` the frame producer returns.

Blueprint: `lem:dc-ch8-2-1-transported-frame`. -/
theorem exists_cartanFrameData
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (p : M) (p' : M') (v : E) (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b') :
    ∃ Efr Ebar : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ k, IsParallelFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) (Efr k) a' b') ∧
      (∀ k, IsParallelFieldAlongOn (I := I') g'
        (globalGeodesic (I := I') g' hg' p' (i v)) (Ebar k) a' b') ∧
      (∀ t ∈ Icc a' b', ∀ k l,
        g.metricInner (globalGeodesic (I := I) g hg p v t)
            (Efr k t : TangentSpace I (globalGeodesic (I := I) g hg p v t)) (Efr l t)
          = if k = l then (1 : ℝ) else 0) ∧
      (∀ t ∈ Icc a' b', ∀ k l,
        g'.metricInner (globalGeodesic (I := I') g' hg' p' (i v) t)
            (Ebar k t : TangentSpace I' (globalGeodesic (I := I') g' hg' p' (i v) t)) (Ebar l t)
          = if k = l then (1 : ℝ) else 0) ∧
      (∀ t ∈ Icc a' b', ∀ k,
        cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t (Efr k t) = Ebar k t) := by
  classical
  obtain ⟨e₀, he₀⟩ := exists_metricOrthonormalBasis (I := I) g (globalGeodesic (I := I) g hg p v a')
  obtain ⟨e, ebar, he0, hePar, heorth, hebar0, hebarPar, hebarorth⟩ :=
    exists_transportedParallelOrthoFrame_pair (I := I) (I' := I') (g := g) (g' := g')
      (γ := globalGeodesic (I := I) g hg p v)
      (γbar := globalGeodesic (I := I') g' hg' p' (i v))
      (show a' < b' by linarith)
      (isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
      (continuousAt_globalGeodesic_Icc g hg p v a' b')
      (isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
      (continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')
      e₀
      ((cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb').toContinuousLinearEquiv)
      (metricInner_cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i hi ha' hb') he₀
  refine ⟨e, ebar, hePar, hebarPar, heorth, hebarorth, fun t ht k => ?_⟩
  rw [cartanPhi_apply_of_mem g hg g' hg' p p' v i ha' hb' ht]
  exact (eq_parallelTransportConjugate_of_isParallelFieldAlongOn
    (hab := show a' < b' by linarith)
    (hgeo := isGeodesicOn_globalGeodesic_Icc g hg p v a' b')
    (hγc := continuousAt_globalGeodesic_Icc g hg p v a' b')
    (hgeobar := isGeodesicOn_globalGeodesic_Icc g' hg' p' (i v) a' b')
    (hγcbar := continuousAt_globalGeodesic_Icc g' hg' p' (i v) a' b')
    (i := (cartanSeed (I := I) (I' := I') g hg g' hg' p p' v i ha' hb').toLinearMap)
    (hePar k) (hebarPar k) (hebar0 k) ht).symm

/-! ### The transfer with its frames, `φ`, and no-conjugacy discharged -/

/-- **Math.** **The variable-curvature exp-side chain, with the frames, `φ`, and the
no-conjugacy clauses all discharged.** Same conclusion as
`metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt` — `f` preserves the metric at
`q = exp_p(v)` — but the abstract data it took as hypotheses is now produced:

* the frames come from `exists_cartanFrameData` and `φ` is the definition `cartanPhi`; the two
  hypotheses the transfer asks of `φ` beyond the curvature match are discharged by
  `cartanPhi_velocity` (`hvel`) and `cartanPhi_zero` (`hφ0`). The transfer asks for no isometry
  property of `φ` — it uses orthonormality of the frames instead — so `metricInner_cartanPhi` and
  `cartanPhi_isLinear` are *not* consumed here; they are what justify calling `cartanPhi` do
  Carmo's `φ_t` at all, and are stated for that reason;
* `hnc`, `hnc'` come from `not_isConjugatePointAt_globalGeodesic_of_isLocalDiffeomorphAt`, i.e.
  from `hnormal`/`hnormal'`, the hypothesis that `exp_p` and `exp_{p̃}` are local diffeomorphisms
  at `v` and `i(v)`. That is exactly what `thm:dc-ch8-2-1` is handed — its `V` is a **normal**
  neighbourhood — and unlike the constant-curvature ball criterion it costs no curvature bound.

Two hypotheses survive, both honest:

* `hsrc`/`hsrcbar`, the single-chart clauses (`lem:dc-ch8-2-1-single-chart`, still open);
* `hcurv`, E. Cartan's curvature hypothesis — stated about **`cartanPhi` itself**, which is do
  Carmo's own hypothesis and nothing more. (An earlier version quantified `hcurv` over every
  metric isometry carrying `γ'` to `γ̃'` and fixing `i` at `0`; that is strictly stronger, since it
  secretly forces `O(n-1)`-isotropy of the curvature about the velocity at each interior time. See
  the module docstring.) -/
theorem metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt_of_isLocalDiffeomorphAt
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (α : M) (α' : M') (p : M) (p' : M') (v : E)
    (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b')
    (hsrc : ∀ t ∈ Icc a' b', globalGeodesic (I := I) g hg p v t ∈ (chartAt H α).source)
    (hsrcbar : ∀ t ∈ Icc a' b',
      globalGeodesic (I := I') g' hg' p' (i v) t ∈ (chartAt H' α').source)
    (hcurv : ∀ t ∈ Icc a' b',
      ∀ x y z w : TangentSpace I (globalGeodesic (I := I) g hg p v t),
      g.leviCivitaConnection.curvatureFormAt g (globalGeodesic (I := I) g hg p v t) x y z w
        = g'.leviCivitaConnection.curvatureFormAt g'
            (globalGeodesic (I := I') g' hg' p' (i v) t)
            (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t x)
            (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t y)
            (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t z)
            (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb' t w))
    (hnormal : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun w : E => expMapGlobal (I := I) g hg p w) v)
    (hnormal' : IsLocalDiffeomorphAt 𝓘(ℝ, E) I' ∞
      (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v))
    (f : M → M')
    (hfd : MDifferentiableAt I I' f (expMapGlobal (I := I) g hg p v))
    (hsemi : ∀ᶠ w : E in nhds v, f (expMapGlobal (I := I) g hg p w)
      = expMapGlobal (I := I') g' hg' p' (i w))
    (u u' : TangentSpace I (expMapGlobal (I := I) g hg p v)) :
    g.metricInner (expMapGlobal (I := I) g hg p v) u u'
      = g'.metricInner (f (expMapGlobal (I := I) g hg p v))
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) u)
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) u') := by
  classical
  obtain ⟨Efr, Ebar, hEpar, hEbarpar, hEorth, hEbarorth, hfr⟩ :=
    exists_cartanFrameData (I := I) (I' := I') g hg g' hg' p p' v i hi ha' hb'
  exact metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt g hg g' hg' α α' p p' v i hi
    ha' hb' hsrc hsrcbar Efr Ebar hEpar hEbarpar hEorth hEbarorth (by simp)
    (cartanPhi (E := E) (I := I) (I' := I') g hg g' hg' p p' v i ha' hb')
    (cartanPhi_velocity (I := I) (I' := I') g hg g' hg' p p' v i ha' hb') hfr hcurv
    (cartanPhi_zero (I := I) (I' := I') g hg g' hg' p p' v i ha' hb')
    (not_isConjugatePointAt_globalGeodesic_of_isLocalDiffeomorphAt g hg p hnormal)
    (not_isConjugatePointAt_globalGeodesic_of_isLocalDiffeomorphAt g' hg' p' hnormal')
    f hfd hsemi u u'

end Riemannian.Jacobi
