import MorganTianLib.Ch01.OrthoFrame
import MorganTianLib.Ch01.PointwiseCurvature
import MorganTianLib.Ch01.CurvatureFrameBridge
import MorganTianLib.Ch01.ManifoldCurvature

/-!
# Morgan–Tian Ch. 1, §1.2 — Ricci and scalar curvature in a local orthonormal frame

Local-frame calculus for the divergence lemma `lem:div-ricci-scalar-curvature`
(`dR = 2 div Ric`). With `E i := orthoFrameField g α i` the smooth local
orthonormal frame of `MorganTianLib.Ch01.OrthoFrame`, we prove, at every point
`q` of the open orthonormality neighbourhood `orthoFrameSet α`:

* `ricciField_eq_frame_sum` — `Ric(X,Y)(q) = ∑ⱼ ℛ(X, Eⱼ, Y, Eⱼ)(q)`, the
  orthonormal-frame expansion of the (pointwise-defined) Ricci tensor as a sum
  of smooth functions;
* `scalarCurvatureAt_eq_frame_sum` — `R(q) = ∑ᵢ∑ⱼ ℛ(Eᵢ, Eⱼ, Eᵢ, Eⱼ)(q)`;
* `ricciField_mdifferentiableAt` / `scalarCurvatureAt_mdifferentiableAt` —
  consequently both are differentiable (this is where the *smoothness* of the
  Gram–Schmidt frame is genuinely needed);
* `orthoFrame_connection_antisymm` — the connection coefficients
  `ω_{jk}(U) = ⟨∇_U Eⱼ, E_k⟩` are antisymmetric in `(j,k)` (differentiate
  `⟨Eⱼ, E_k⟩ = δⱼₖ`, valid on the *open* set, with metric compatibility);
* the **trace–∇ commutation corrections**: the frame-derivative correction
  terms produced when a covariant derivative is pushed through an
  orthonormal-frame trace cancel in pairs
  (`sum_curvature_cov_corrections_snd_fth`,
  `sum_curvature_cov_corrections_fst_trd`,
  `sum_curvature_cov_corrections_snd_fth_diag`), by the antisymmetry of `ω`
  against the symmetry of the paired curvature sums.

Together these say: *metric contraction commutes with covariant
differentiation*, which the blueprint proof of
`lem:div-ricci-scalar-curvature` uses freely ("Since `∇g = 0`, contraction
with `g` commutes with covariant differentiation").

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
Blueprint: `lem:div-ricci-scalar-curvature`.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Bundle

noncomputable section

set_option linter.unusedSectionVars false

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Directional-derivative calculus helpers -/

/-- **Math.** The directional derivative only sees the germ: functions agreeing
near `p` have equal derivatives along any field.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem dir_congr_nhds (X : SmoothVectorField I M) {f f' : M → ℝ} {p : M}
    (h : f =ᶠ[𝓝 p] f') : X.dir f p = X.dir f' p := by
  simp only [SmoothVectorField.dir]
  rw [h.mfderiv_eq]
  rfl

/-- **Math.** The directional derivative of a locally constant function
vanishes. Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem dir_eventuallyEq_const (X : SmoothVectorField I M) {f : M → ℝ} {c : ℝ}
    {p : M} (h : f =ᶠ[𝓝 p] fun _ => c) : X.dir f p = 0 := by
  rw [dir_congr_nhds X h]
  simp only [SmoothVectorField.dir, mfderiv_const]
  rfl

/-- **Math.** Finite sums of functions differentiable at `p` are
differentiable at `p`.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem mdifferentiableAt_finset_sum {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    {p : M} (hf : ∀ j ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) p) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => ∑ j ∈ s, f j q) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mdifferentiableAt_const
  | @insert a s ha ih =>
    have h : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun q => f a q + ∑ j ∈ s, f j q) p :=
      (hf a (Finset.mem_insert_self a s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    exact Finset.sum_insert ha

/-- **Math.** The directional derivative distributes over finite sums of
differentiable functions.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem dir_finset_sum (X : SmoothVectorField I M) {ι : Type*} (s : Finset ι)
    {f : ι → M → ℝ} (p : M)
    (hf : ∀ j ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) p) :
    X.dir (fun q => ∑ j ∈ s, f j q) p = ∑ j ∈ s, X.dir (f j) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact dir_eventuallyEq_const (c := 0) X
      (Filter.Eventually.of_forall fun q => Finset.sum_empty)
  | @insert a s ha ih =>
    have hstep : X.dir (fun q => ∑ j ∈ insert a s, f j q) p
        = X.dir (fun q => f a q + ∑ j ∈ s, f j q) p :=
      dir_congr_nhds X (Filter.Eventually.of_forall fun q => Finset.sum_insert ha)
    rw [hstep, X.dir_add p (hf a (Finset.mem_insert_self a s))
      (mdifferentiableAt_finset_sum s fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj), Finset.sum_insert ha]

/-- **Math.** The curvature `(0,4)`-tensor of smooth vector fields is a
differentiable scalar function: it is the metric pairing of the smooth fields
`R(X,Y)Z` and `W`. Blueprint: `lem:div-ricci-scalar-curvature`
(infrastructure). -/
theorem curvatureForm_mdifferentiableAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (X Y Z W : SmoothVectorField I M) (p : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (nabla.curvatureForm g X Y Z W) p :=
  g.metricInner_field_mdifferentiableAt (nabla.curvature X Y Z) W p

/-! ### Single-slot sum expansions of the pointwise curvature tensor -/

/-- **Math.** The pointwise curvature tensor expands linearly over a finite
combination in the **first** slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem curvatureFormAt_sum_fst (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → TangentSpace I p) (w z t : TangentSpace I p) :
    curvatureFormAt g nabla p (∑ a ∈ s, c a • e a) w z t
      = ∑ a ∈ s, c a * curvatureFormAt g nabla p (e a) w z t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := curvatureFormAt_smul_left g nabla p 0 0 w z t
    simpa using h
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, curvatureFormAt_add_left, curvatureFormAt_smul_left,
      ih, Finset.sum_insert ha]

/-- **Math.** Sum expansion in the **second** slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem curvatureFormAt_sum_snd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → TangentSpace I p) (v z t : TangentSpace I p) :
    curvatureFormAt g nabla p v (∑ a ∈ s, c a • e a) z t
      = ∑ a ∈ s, c a * curvatureFormAt g nabla p v (e a) z t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := curvatureFormAt_smul_snd g nabla p 0 v 0 z t
    simpa using h
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, curvatureFormAt_add_snd, curvatureFormAt_smul_snd,
      ih, Finset.sum_insert ha]

/-- **Math.** Sum expansion in the **third** slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem curvatureFormAt_sum_trd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → TangentSpace I p) (v w t : TangentSpace I p) :
    curvatureFormAt g nabla p v w (∑ a ∈ s, c a • e a) t
      = ∑ a ∈ s, c a * curvatureFormAt g nabla p v w (e a) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := curvatureFormAt_smul_trd g nabla p 0 v w 0 t
    simpa using h
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, curvatureFormAt_add_trd, curvatureFormAt_smul_trd,
      ih, Finset.sum_insert ha]

/-- **Math.** Sum expansion in the **fourth** slot.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem curvatureFormAt_sum_fth (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → TangentSpace I p) (v w z : TangentSpace I p) :
    curvatureFormAt g nabla p v w z (∑ a ∈ s, c a • e a)
      = ∑ a ∈ s, c a * curvatureFormAt g nabla p v w z (e a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := curvatureFormAt_smul_fth g nabla p 0 v w z 0
    simpa using h
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, curvatureFormAt_add_fth, curvatureFormAt_smul_fth,
      ih, Finset.sum_insert ha]

/-! ### The Ricci tensor as a field, and its frame expansion -/

/-- **Math.** The **Ricci tensor evaluated on smooth vector fields**, as a
scalar function on `M`: `Ric(X,Y)(q) = Ric_q(X(q), Y(q))`.
Blueprint: `lem:div-ricci-scalar-curvature`, `def:ricci-curvature`. -/
def ricciField (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (X Y : SmoothVectorField I M) : M → ℝ :=
  fun q => ricciAt g nabla hLC q (X q) (Y q)

/-- **Math.** **Frame expansion of the Ricci tensor**: on the orthonormality
neighbourhood of the frame at `α`,
`Ric(X,Y)(q) = ∑ⱼ ℛ(X, Eⱼ, Y, Eⱼ)(q)` with `Eⱼ` the smooth orthonormal frame
fields — the trace over the orthonormal basis `{Eⱼ(q)}` of `T_qM` computed by
`Riemannian.ricciForm_eq_sum`. This exhibits the (pointwise-defined) Ricci
tensor locally as a finite sum of smooth functions of `q`.
Blueprint: `lem:div-ricci-scalar-curvature`, `def:ricci-curvature`. -/
theorem ricciField_eq_frame_sum (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (X Y : SmoothVectorField I M) :
    ricciField g nabla hLC X Y q
      = ∑ j, nabla.curvatureForm g X (orthoFrameField g α j) Y
          (orthoFrameField g α j) q := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := ricciForm_eq_sum (isAlgCurvatureForm_curvatureFormAt g nabla hLC q)
    (X q) (Y q) (orthoFrameBasis g α hq)
  rw [ricciField, ricciAt, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [orthoFrameBasis_apply g α hq j]
  exact curvatureFormAt_eq g nabla X (orthoFrameField g α j) Y
    (orthoFrameField g α j) q

/-- **Math.** **Frame expansion of the scalar curvature**: on the
orthonormality neighbourhood of the frame at `α`,
`R(q) = ∑ᵢ∑ⱼ ℛ(Eᵢ, Eⱼ, Eᵢ, Eⱼ)(q)` (`Riemannian.scalarCurvature_eq_sum`
against the frame basis).
Blueprint: `lem:div-ricci-scalar-curvature`, `def:ricci-curvature`. -/
theorem scalarCurvatureAt_eq_frame_sum (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) :
    scalarCurvatureAt g nabla hLC q
      = ∑ i, ∑ j, nabla.curvatureForm g (orthoFrameField g α i)
          (orthoFrameField g α j) (orthoFrameField g α i)
          (orthoFrameField g α j) q := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := scalarCurvature_eq_sum (isAlgCurvatureForm_curvatureFormAt g nabla hLC q)
    (orthoFrameBasis g α hq)
  refine h.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [orthoFrameBasis_apply g α hq i, orthoFrameBasis_apply g α hq j]
  exact curvatureFormAt_eq g nabla (orthoFrameField g α i) (orthoFrameField g α j)
    (orthoFrameField g α i) (orthoFrameField g α j) q

/-- **Math.** The Ricci tensor of two smooth vector fields is a
**differentiable** function on `M`: near any point it agrees with its
orthonormal-frame expansion (a finite sum of curvature pairings of smooth
fields). This is where the smoothness of the Gram–Schmidt frame enters.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem ricciField_mdifferentiableAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y : SmoothVectorField I M) (p : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (ricciField g nabla hLC X Y) p := by
  have hrep : ricciField g nabla hLC X Y =ᶠ[𝓝 p]
      fun q => ∑ j, nabla.curvatureForm g X (orthoFrameField g p j) Y
        (orthoFrameField g p j) q := by
    filter_upwards [(isOpen_orthoFrameSet (I := I) (M := M) p).mem_nhds
      (mem_orthoFrameSet_self (I := I) p)] with q hq
    exact ricciField_eq_frame_sum g nabla hLC p hq X Y
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ hrep
  exact mdifferentiableAt_finset_sum _ fun j _ =>
    curvatureForm_mdifferentiableAt g nabla X (orthoFrameField g p j) Y
      (orthoFrameField g p j) p

/-- **Math.** The scalar curvature is a **differentiable** function on `M`.
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem scalarCurvatureAt_mdifferentiableAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarCurvatureAt g nabla hLC) p := by
  have hrep : scalarCurvatureAt g nabla hLC =ᶠ[𝓝 p]
      fun q => ∑ i, ∑ j, nabla.curvatureForm g (orthoFrameField g p i)
        (orthoFrameField g p j) (orthoFrameField g p i) (orthoFrameField g p j) q := by
    filter_upwards [(isOpen_orthoFrameSet (I := I) (M := M) p).mem_nhds
      (mem_orthoFrameSet_self (I := I) p)] with q hq
    exact scalarCurvatureAt_eq_frame_sum g nabla hLC p hq
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ hrep
  exact mdifferentiableAt_finset_sum _ fun i _ =>
    mdifferentiableAt_finset_sum _ fun j _ =>
      curvatureForm_mdifferentiableAt g nabla _ _ _ _ p

/-! ### Antisymmetry of the connection coefficients -/

/-- **Math.** **Antisymmetry of the connection coefficients** of an
orthonormal frame: `⟨∇_U Eⱼ, E_k⟩ + ⟨∇_U E_k, Eⱼ⟩ = 0` at points of the open
orthonormality neighbourhood. Differentiate the locally constant function
`⟨Eⱼ, E_k⟩ = δⱼₖ` along `U` and use metric compatibility. This is the
mechanism by which "∇g = 0" lets covariant derivatives pass through
orthonormal-frame traces. Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem orthoFrame_connection_antisymm (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (U : SmoothVectorField I M)
    (j k : Fin (Module.finrank ℝ E)) :
    g.metricInner q ((nabla.cov U (orthoFrameField g α j)) q) (orthoFrameField g α k q)
      + g.metricInner q ((nabla.cov U (orthoFrameField g α k)) q)
          (orthoFrameField g α j q) = 0 := by
  have hcomp := hLC.2 U (orthoFrameField g α j) (orthoFrameField g α k) q
  have hconst : (fun q' => g.metricInner q' (orthoFrameField g α j q')
      (orthoFrameField g α k q')) =ᶠ[𝓝 q] fun _ => if j = k then 1 else 0 := by
    filter_upwards [(isOpen_orthoFrameSet (I := I) (M := M) α).mem_nhds hq] with q' hq'
    exact orthoFrameField_orthonormal g α hq' j k
  have hdir : U.dir (fun q' => g.metricInner q' (orthoFrameField g α j q')
      (orthoFrameField g α k q')) q = 0 :=
    dir_eventuallyEq_const U hconst
  rw [hdir] at hcomp
  have hsymm : g.metricInner q (orthoFrameField g α j q)
      ((nabla.cov U (orthoFrameField g α k)) q)
      = g.metricInner q ((nabla.cov U (orthoFrameField g α k)) q)
        (orthoFrameField g α j q) := g.metricInner_comm q _ _
  linarith [hcomp, hsymm]

/-! ### The pairing-cancellation engine -/

/-- **Math.** An antisymmetric matrix pairs to zero against a symmetric one:
`∑ⱼₖ ωⱼₖ Sⱼₖ = 0` when `ωⱼₖ = −ω_{kj}` and `Sⱼₖ = S_{kj}`. This is the
algebraic heart of "trace commutes with ∇".
Blueprint: `lem:div-ricci-scalar-curvature` (infrastructure). -/
theorem sum_antisymm_mul_symm_eq_zero {n : ℕ} (om S : Fin n → Fin n → ℝ)
    (hom : ∀ j k, om j k + om k j = 0) (hS : ∀ j k, S j k = S k j) :
    ∑ j, ∑ k, om j k * S j k = 0 := by
  have hswap : ∑ j, ∑ k, om j k * S j k = ∑ j, ∑ k, om k j * S k j :=
    Finset.sum_comm
  have hneg : ∀ j k : Fin n, om k j * S k j = -(om j k * S j k) := by
    intro j k
    have h1 : om k j = -om j k := by linarith [hom j k]
    rw [h1, hS j k]
    ring
  have hkey : ∑ j, ∑ k, om j k * S j k = -∑ j, ∑ k, om j k * S j k := by
    nth_rewrite 1 [hswap]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hneg j k
  linarith

/-! ### The trace–∇ commutation corrections

Pushing a directional derivative through an orthonormal-frame trace produces
frame-derivative correction terms `ℛ(…, ∇_U Eⱼ, …)`; expanding `∇_U Eⱼ` in the
frame with coefficients `ωⱼₖ = ⟨∇_U Eⱼ, E_k⟩` and pairing the antisymmetry of
`ω` (`orthoFrame_connection_antisymm`) against the symmetry of the paired
curvature sums makes all corrections cancel. The three lemmas below are the
three instances needed for the Ricci trace and the double scalar trace. -/

/-- **Math.** Frame-derivative corrections in the **second and fourth** slots
of the Ricci trace cancel: for any fields `X, Y, U`,
`∑ⱼ [ℛ(X, ∇_U Eⱼ, Y, Eⱼ) + ℛ(X, Eⱼ, Y, ∇_U Eⱼ)](q) = 0` at
`q ∈ orthoFrameSet α`. Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem sum_curvature_cov_corrections_snd_fth (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (X Y U : SmoothVectorField I M) :
    ∑ j, (nabla.curvatureForm g X (nabla.cov U (orthoFrameField g α j)) Y
        (orthoFrameField g α j) q
      + nabla.curvatureForm g X (orthoFrameField g α j) Y
          (nabla.cov U (orthoFrameField g α j)) q) = 0 := by
  classical
  have hexp : ∀ j : Fin (Module.finrank ℝ E),
      (nabla.cov U (orthoFrameField g α j)) q
        = ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α j)) q)
            (orthoFrameField g α k q) • orthoFrameField g α k q :=
    fun j => orthoFrameField_expansion g α hq _
  have hterm1 : ∀ j, nabla.curvatureForm g X (nabla.cov U (orthoFrameField g α j)) Y
      (orthoFrameField g α j) q
        = ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α j)) q)
            (orthoFrameField g α k q)
          * curvatureFormAt g nabla q (X q) (orthoFrameField g α k q) (Y q)
              (orthoFrameField g α j q) := by
    intro j
    conv_lhs =>
      rw [← curvatureFormAt_eq g nabla X (nabla.cov U (orthoFrameField g α j)) Y
        (orthoFrameField g α j) q, hexp j,
        curvatureFormAt_sum_snd g nabla q Finset.univ _ _ _ _ _]
  have hterm2 : ∀ j, nabla.curvatureForm g X (orthoFrameField g α j) Y
      (nabla.cov U (orthoFrameField g α j)) q
        = ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α j)) q)
            (orthoFrameField g α k q)
          * curvatureFormAt g nabla q (X q) (orthoFrameField g α j q) (Y q)
              (orthoFrameField g α k q) := by
    intro j
    conv_lhs =>
      rw [← curvatureFormAt_eq g nabla X (orthoFrameField g α j) Y
        (nabla.cov U (orthoFrameField g α j)) q, hexp j,
        curvatureFormAt_sum_fth g nabla q Finset.univ _ _ _ _ _]
  have hkey : ∑ j, (nabla.curvatureForm g X (nabla.cov U (orthoFrameField g α j)) Y
        (orthoFrameField g α j) q
      + nabla.curvatureForm g X (orthoFrameField g α j) Y
          (nabla.cov U (orthoFrameField g α j)) q)
      = ∑ j, ∑ k,
          g.metricInner q ((nabla.cov U (orthoFrameField g α j)) q)
            (orthoFrameField g α k q)
          * (curvatureFormAt g nabla q (X q) (orthoFrameField g α k q) (Y q)
              (orthoFrameField g α j q)
            + curvatureFormAt g nabla q (X q) (orthoFrameField g α j q) (Y q)
                (orthoFrameField g α k q)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hterm1 j, hterm2 j, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hkey]
  exact sum_antisymm_mul_symm_eq_zero _ _
    (fun j k => orthoFrame_connection_antisymm g nabla hLC α hq U j k)
    (fun j k => add_comm _ _)

/-- **Math.** Frame-derivative corrections in the **first and third** slots of
the double scalar trace cancel:
`∑ᵢ∑ⱼ [ℛ(∇_U Eᵢ, Eⱼ, Eᵢ, Eⱼ) + ℛ(Eᵢ, Eⱼ, ∇_U Eᵢ, Eⱼ)](q) = 0` at
`q ∈ orthoFrameSet α`. Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem sum_curvature_cov_corrections_fst_trd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (U : SmoothVectorField I M) :
    ∑ i, ∑ j, (nabla.curvatureForm g (nabla.cov U (orthoFrameField g α i))
        (orthoFrameField g α j) (orthoFrameField g α i) (orthoFrameField g α j) q
      + nabla.curvatureForm g (orthoFrameField g α i) (orthoFrameField g α j)
          (nabla.cov U (orthoFrameField g α i)) (orthoFrameField g α j) q) = 0 := by
  classical
  have hexp : ∀ i : Fin (Module.finrank ℝ E),
      (nabla.cov U (orthoFrameField g α i)) q
        = ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
            (orthoFrameField g α k q) • orthoFrameField g α k q :=
    fun i => orthoFrameField_expansion g α hq _
  have hterm1 : ∀ i j, nabla.curvatureForm g (nabla.cov U (orthoFrameField g α i))
      (orthoFrameField g α j) (orthoFrameField g α i) (orthoFrameField g α j) q
        = ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
            (orthoFrameField g α k q)
          * curvatureFormAt g nabla q (orthoFrameField g α k q)
              (orthoFrameField g α j q) (orthoFrameField g α i q)
              (orthoFrameField g α j q) := by
    intro i j
    conv_lhs =>
      rw [← curvatureFormAt_eq g nabla (nabla.cov U (orthoFrameField g α i))
        (orthoFrameField g α j) (orthoFrameField g α i) (orthoFrameField g α j) q,
        hexp i, curvatureFormAt_sum_fst g nabla q Finset.univ _ _ _ _ _]
  have hterm2 : ∀ i j, nabla.curvatureForm g (orthoFrameField g α i)
      (orthoFrameField g α j) (nabla.cov U (orthoFrameField g α i))
      (orthoFrameField g α j) q
        = ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
            (orthoFrameField g α k q)
          * curvatureFormAt g nabla q (orthoFrameField g α i q)
              (orthoFrameField g α j q) (orthoFrameField g α k q)
              (orthoFrameField g α j q) := by
    intro i j
    conv_lhs =>
      rw [← curvatureFormAt_eq g nabla (orthoFrameField g α i)
        (orthoFrameField g α j) (nabla.cov U (orthoFrameField g α i))
        (orthoFrameField g α j) q,
        hexp i, curvatureFormAt_sum_trd g nabla q Finset.univ _ _ _ _ _]
  have hinner : ∀ i, ∑ j, (nabla.curvatureForm g (nabla.cov U (orthoFrameField g α i))
        (orthoFrameField g α j) (orthoFrameField g α i) (orthoFrameField g α j) q
      + nabla.curvatureForm g (orthoFrameField g α i) (orthoFrameField g α j)
          (nabla.cov U (orthoFrameField g α i)) (orthoFrameField g α j) q)
      = ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
          (orthoFrameField g α k q)
        * ((∑ j, curvatureFormAt g nabla q (orthoFrameField g α k q)
              (orthoFrameField g α j q) (orthoFrameField g α i q)
              (orthoFrameField g α j q))
          + ∑ j, curvatureFormAt g nabla q (orthoFrameField g α i q)
              (orthoFrameField g α j q) (orthoFrameField g α k q)
              (orthoFrameField g α j q)) := by
    intro i
    calc ∑ j, (nabla.curvatureForm g (nabla.cov U (orthoFrameField g α i))
          (orthoFrameField g α j) (orthoFrameField g α i) (orthoFrameField g α j) q
        + nabla.curvatureForm g (orthoFrameField g α i) (orthoFrameField g α j)
            (nabla.cov U (orthoFrameField g α i)) (orthoFrameField g α j) q)
        = ∑ j, ∑ k,
            (g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
                (orthoFrameField g α k q)
              * curvatureFormAt g nabla q (orthoFrameField g α k q)
                  (orthoFrameField g α j q) (orthoFrameField g α i q)
                  (orthoFrameField g α j q)
            + g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
                (orthoFrameField g α k q)
              * curvatureFormAt g nabla q (orthoFrameField g α i q)
                  (orthoFrameField g α j q) (orthoFrameField g α k q)
                  (orthoFrameField g α j q)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hterm1 i j, hterm2 i j, ← Finset.sum_add_distrib]
      _ = ∑ k, ∑ j,
            (g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
                (orthoFrameField g α k q)
              * curvatureFormAt g nabla q (orthoFrameField g α k q)
                  (orthoFrameField g α j q) (orthoFrameField g α i q)
                  (orthoFrameField g α j q)
            + g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
                (orthoFrameField g α k q)
              * curvatureFormAt g nabla q (orthoFrameField g α i q)
                  (orthoFrameField g α j q) (orthoFrameField g α k q)
                  (orthoFrameField g α j q)) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  have hgoal : ∑ i, ∑ j, (nabla.curvatureForm g (nabla.cov U (orthoFrameField g α i))
        (orthoFrameField g α j) (orthoFrameField g α i) (orthoFrameField g α j) q
      + nabla.curvatureForm g (orthoFrameField g α i) (orthoFrameField g α j)
          (nabla.cov U (orthoFrameField g α i)) (orthoFrameField g α j) q)
      = ∑ i, ∑ k, g.metricInner q ((nabla.cov U (orthoFrameField g α i)) q)
          (orthoFrameField g α k q)
        * ((∑ j, curvatureFormAt g nabla q (orthoFrameField g α k q)
              (orthoFrameField g α j q) (orthoFrameField g α i q)
              (orthoFrameField g α j q))
          + ∑ j, curvatureFormAt g nabla q (orthoFrameField g α i q)
              (orthoFrameField g α j q) (orthoFrameField g α k q)
              (orthoFrameField g α j q)) :=
    Finset.sum_congr rfl fun i _ => hinner i
  rw [hgoal]
  refine sum_antisymm_mul_symm_eq_zero _
    (fun i k => (∑ j, curvatureFormAt g nabla q (orthoFrameField g α k q)
        (orthoFrameField g α j q) (orthoFrameField g α i q) (orthoFrameField g α j q))
      + ∑ j, curvatureFormAt g nabla q (orthoFrameField g α i q)
          (orthoFrameField g α j q) (orthoFrameField g α k q) (orthoFrameField g α j q))
    (fun i k => orthoFrame_connection_antisymm g nabla hLC α hq U i k)
    (fun i k => add_comm _ _)

/-- **Math.** Frame-derivative corrections in the **second and fourth** slots
of the double scalar trace cancel:
`∑ᵢ∑ⱼ [ℛ(Eᵢ, ∇_U Eⱼ, Eᵢ, Eⱼ) + ℛ(Eᵢ, Eⱼ, Eᵢ, ∇_U Eⱼ)](q) = 0` at
`q ∈ orthoFrameSet α`. Blueprint: `lem:div-ricci-scalar-curvature`. -/
theorem sum_curvature_cov_corrections_snd_fth_diag (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (α : M) {q : M}
    (hq : q ∈ orthoFrameSet (I := I) (M := M) α) (U : SmoothVectorField I M) :
    ∑ i, ∑ j, (nabla.curvatureForm g (orthoFrameField g α i)
        (nabla.cov U (orthoFrameField g α j)) (orthoFrameField g α i)
        (orthoFrameField g α j) q
      + nabla.curvatureForm g (orthoFrameField g α i) (orthoFrameField g α j)
          (orthoFrameField g α i) (nabla.cov U (orthoFrameField g α j)) q) = 0 :=
  Finset.sum_eq_zero fun i _ =>
    sum_curvature_cov_corrections_snd_fth g nabla hLC α hq
      (orthoFrameField g α i) (orthoFrameField g α i) U

end MorganTianLib
