import PetersenLib.Ch01.VolumeForm
import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 2, §2.1.3 — Divergence, Laplacian, and the parallel volume form

The volume form of Ch. 1 as a `(0,n)`-tensor operator (`volumeOperator`),
the divergence defined through the Lie derivative of the volume form
(`divergenceLieDerivative`, `L_X vol = (div X)·vol`), the Laplacian
(`laplacian`, `Δf = div ∇f`), Petersen's trace formula
`div X = Σᵢ ½ (L_X g)(Eᵢ, Eᵢ)` for a positively oriented orthonormal frame
(`divergence_trace_formula`) with the corollary
`Δf = Σᵢ Hess f(Eᵢ, Eᵢ)` (`laplacian_eq_hessian_trace`), and the volume half
of Prop. 2.2.5, `∇ vol = 0` (`volume_parallel`, `metric_and_volume_parallel`).

## Design notes

* **The orientation datum.** Ch. 1's `volumeForm` is parametrized by a
  *pointwise* orientation datum `o : ∀ x, Orientation ℝ (TangentSpace I x) (Fin n)`
  with no smoothness or local-constancy imposed (Mathlib has no oriented
  manifolds yet).  Consequently the evaluation `x ↦ vol_x(Y₁ x, …, Y_n x)` of
  the volume form on smooth fields need **not** be smooth — `o` may jump
  arbitrarily from point to point — so `volumeOperator` provably satisfies the
  two *algebraic* clauses of `IsTensorOperator` (`volumeOperator_add_slot`,
  `volumeOperator_smul_slot`) but its `smooth_eval` clause is **false in this
  generality**; the bundled predicate is therefore not stated.  All analytic
  statements below instead carry Petersen's standing hypothesis: an
  orthonormal frame `E₁, …, E_n` near the point on which the volume form is
  *normalized* (`vol(E₁, …, E_n) = 1` on a neighborhood), which is exactly the
  content of "positively oriented orthonormal frame" and restores every
  differentiability the proofs need.

* **The divergence.** Petersen defines `div X` implicitly by
  `L_X vol = (div X)·vol`.  The concrete realization divides the Lie
  derivative of the volume form, evaluated on the chart-basis frame at the
  point, by the (nonzero, `volumeOperator_chartFrame_ne_zero`) value of the
  volume form on the same frame.  The defining identity holds against the
  chart frame definitionally (`lieDerivativeTensor_volumeOperator_chartFrame`)
  and against *every* tuple of smooth fields under the normalized-frame
  hypothesis (`lieDerivativeTensor_volumeOperator_eq_smul`) — the proof is the
  honest "Leibniz rule for the determinant along the flow"
  (`lieDerivativeTensor_volumeOperator_combination`), via Jacobi's formula
  (`directionalDerivative_det_coeff`) and the Cramer identity
  (`sum_mul_det_updateRow`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.3 and §2.2.2
(Prop. 2.2.5).
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace Matrix

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Evaluating an updated tuple of fields -/

omit [IsManifold I ∞ M] in
/-- Evaluating a slot-updated tuple of vector fields at a point is the
slot-update of the evaluated tuple. -/
private theorem eval_update {k : ℕ} (Y : Fin k → Π x : M, TangentSpace I x)
    (i : Fin k) (V : Π x : M, TangentSpace I x) (x : M) :
    (fun j => Function.update Y i V j x)
      = Function.update (fun j => Y j x) i (V x) := by
  funext j
  exact Function.apply_update (fun _ f => f x) Y i V j

/-! ## The volume form as a `(0,n)`-tensor operator -/

section VolumeOperator

variable [hm : HasMetric I M]

/-- The metric inner product of the `HasMetric` instance metric *is* the inner
product carried by the tangent fibres through the Riemannian-bundle bridge. -/
theorem hasMetric_metricInner_eq_inner (x : M) (v w : TangentSpace I x) :
    hm.metric.metricInner x v w = ⟪v, w⟫ := rfl

/-- **Math.** Petersen §2.1.3: the **volume form as a `(0,n)`-tensor
operator** on the oriented Riemannian manifold `(M, g, o)`, `n = dim M`:
`vol(Y₁, …, Y_n)(x) = vol_x(Y₁|_x, …, Y_n|_x)`, the Ch. 1 volume form of
`(T_xM, g_x, o x)` evaluated on the values of the fields. -/
def volumeOperator (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E))) :
    TensorOperator I M (finrank ℝ E) :=
  fun Y x => volumeForm rfl o x fun i => Y i x

theorem volumeOperator_apply
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (Y : Fin (finrank ℝ E) → Π x : M, TangentSpace I x) (x : M) :
    volumeOperator o Y x = volumeForm rfl o x fun i => Y i x := rfl

/-- The volume operator at `x` only involves the values of the fields at `x`
(it is pointwise, hence tensorial). -/
theorem volumeOperator_congr_at
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {Y Z : Fin (finrank ℝ E) → Π x : M, TangentSpace I x} {x : M}
    (h : ∀ i, Y i x = Z i x) :
    volumeOperator o Y x = volumeOperator o Z x := by
  simp only [volumeOperator_apply]
  exact congrArg _ (funext h)

/-- **Math.** Additivity of the volume form in each slot — the `add_slot`
clause of `IsTensorOperator` for `volumeOperator` (the `smooth_eval` clause is
false for a general pointwise orientation datum; see the module docstring). -/
theorem volumeOperator_add_slot
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (Y : Fin (finrank ℝ E) → Π x : M, TangentSpace I x) (i : Fin (finrank ℝ E))
    (V W : Π x : M, TangentSpace I x) (x : M) :
    volumeOperator o (Function.update Y i (fun p => V p + W p)) x
      = volumeOperator o (Function.update Y i V) x
        + volumeOperator o (Function.update Y i W) x := by
  simp only [volumeOperator_apply, eval_update]
  exact (volumeForm rfl o x).map_update_add (fun j => Y j x) i (V x) (W x)

/-- **Math.** `C^∞(M)`-homogeneity of the volume form in each slot — the
`smul_slot` clause of `IsTensorOperator` for `volumeOperator`. -/
theorem volumeOperator_smul_slot
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (Y : Fin (finrank ℝ E) → Π x : M, TangentSpace I x) (i : Fin (finrank ℝ E))
    (f : M → ℝ) (V : Π x : M, TangentSpace I x) (x : M) :
    volumeOperator o (Function.update Y i (fun p => f p • V p)) x
      = f x * volumeOperator o (Function.update Y i V) x := by
  simp only [volumeOperator_apply, eval_update]
  exact (volumeForm rfl o x).map_update_smul (fun j => Y j x) i (f x) (V x)

/-- **Math.** Alternation: the volume form vanishes on tuples whose values at
`x` coincide in two distinct slots. -/
theorem volumeOperator_eq_zero_of_slot_eq
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (Y : Fin (finrank ℝ E) → Π x : M, TangentSpace I x) (x : M)
    {i j : Fin (finrank ℝ E)} (h : Y i x = Y j x) (hij : i ≠ j) :
    volumeOperator o Y x = 0 :=
  (volumeForm rfl o x).map_eq_zero_of_eq (fun k => Y k x) h hij

end VolumeOperator

/-! ## Orthonormal frames: bases, expansion, and the determinant formula -/

section FrameAlgebra

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [hm : HasMetric I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- A `g`-orthonormal `n`-tuple in an `n`-dimensional tangent space is
orthonormal for the fibre inner product. -/
theorem orthonormal_of_metricInner_ite {y : M}
    {v : Fin (finrank ℝ E) → TangentSpace I y}
    (h : ∀ i j, hm.metric.metricInner y (v i) (v j) = if i = j then 1 else 0) :
    Orthonormal ℝ v := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [← hasMetric_metricInner_eq_inner]
  exact h i j

/-- A `g`-orthonormal `n`-tuple in the `n`-dimensional tangent space is a
basis. -/
def basisOfMetricOrthonormal {y : M}
    {v : Fin (finrank ℝ E) → TangentSpace I y}
    (h : ∀ i j, hm.metric.metricInner y (v i) (v j) = if i = j then 1 else 0) :
    Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I y) :=
  haveI : Nonempty (Fin (finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne _))
  basisOfLinearIndependentOfCardEqFinrank
    (orthonormal_of_metricInner_ite h).linearIndependent
    ((Fintype.card_fin _).trans rfl)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem basisOfMetricOrthonormal_apply {y : M}
    {v : Fin (finrank ℝ E) → TangentSpace I y}
    (h : ∀ i j, hm.metric.metricInner y (v i) (v j) = if i = j then 1 else 0)
    (j : Fin (finrank ℝ E)) :
    basisOfMetricOrthonormal h j = v j := by
  haveI : Nonempty (Fin (finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne _))
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) j

omit [FiniteDimensional ℝ E] in
/-- **Math.** Orthonormal expansion: against a `g`-orthonormal `n`-tuple
`v₁, …, v_n` of `T_yM`, every `w` expands as `w = Σⱼ g(w, vⱼ) vⱼ`. -/
theorem metricInner_orthonormal_expansion {y : M}
    {v : Fin (finrank ℝ E) → TangentSpace I y}
    (h : ∀ i j, hm.metric.metricInner y (v i) (v j) = if i = j then 1 else 0)
    (w : TangentSpace I y) :
    w = ∑ j, hm.metric.metricInner y w (v j) • v j := by
  set b := basisOfMetricOrthonormal h with hb
  have hcoe : ∀ j, b j = v j := basisOfMetricOrthonormal_apply h
  have hrepr : ∀ j, b.repr w j = hm.metric.metricInner y w (v j) := by
    intro j
    have hw : w = ∑ k, b.repr w k • v k := by
      conv_lhs => rw [← b.sum_repr w]
      exact Finset.sum_congr rfl fun k _ => by rw [hcoe k]
    calc b.repr w j
        = ∑ k, b.repr w k * (if k = j then 1 else 0) := by
          simp [mul_ite, Finset.sum_ite_eq']
      _ = ∑ k, b.repr w k * hm.metric.metricInner y (v k) (v j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [h k j]
      _ = hm.metric.metricInner y w (v j) := by
          conv_rhs => rw [hw]
          simp only [hasMetric_metricInner_eq_inner]
          rw [sum_inner]
          exact (Finset.sum_congr rfl fun k _ => real_inner_smul_left ..).symm
  conv_lhs => rw [← b.sum_repr w]
  exact Finset.sum_congr rfl fun j _ => by rw [hrepr j, hcoe j]

/-- **Math.** The determinant formula for a top-degree alternating form: on a
combination `wᵢ = Σⱼ dᵢⱼ bⱼ` of a basis, `f(w₁, …, w_n) = det d · f(b)` — the
`1`-dimensionality of top alternating forms, through `Basis.det`. -/
private theorem alternatingMap_apply_sum_smul {V : Type*} [AddCommGroup V]
    [Module ℝ V] {N : ℕ} (f : V [⋀^Fin N]→ₗ[ℝ] ℝ) (b : Basis (Fin N) ℝ V)
    (d : Fin N → Fin N → ℝ) :
    f (fun i => ∑ j, d i j • b j) = (Matrix.of d).det * f b := by
  have hf := f.eq_smul_basis_det b
  have happly : ∀ w : Fin N → V, f w = f b * b.det w := by
    intro w
    conv_lhs => rw [hf]
    simp
  rw [happly, happly b, b.det_self, mul_one, Basis.det_apply]
  have htm : b.toMatrix (fun i => ∑ j, d i j • b j) = (Matrix.of d)ᵀ := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Basis.toMatrix_apply, map_sum,
      map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq']
  rw [htm, Matrix.det_transpose]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Math.** The volume form on frame combinations: if the values `Yᵢ|_x`
expand as `Σⱼ dᵢⱼ vⱼ` in a `g`-orthonormal tuple `v` at `x`, then
`vol(Y₁, …, Y_n)(x) = det d · vol_x(v)`. -/
theorem volumeOperator_apply_of_expansion
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {x : M} {v : Fin (finrank ℝ E) → TangentSpace I x}
    (h : ∀ i j, hm.metric.metricInner x (v i) (v j) = if i = j then 1 else 0)
    (Y : Fin (finrank ℝ E) → Π q : M, TangentSpace I q)
    (d : Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ)
    (hY : ∀ i, Y i x = ∑ j, d i j • v j) :
    volumeOperator o Y x = (Matrix.of d).det * volumeForm rfl o x v := by
  have hb : ∀ j, basisOfMetricOrthonormal h j = v j := basisOfMetricOrthonormal_apply h
  have hval : (fun i => Y i x) = fun i => ∑ j, d i j • basisOfMetricOrthonormal h j := by
    funext i
    rw [hY i]
    exact Finset.sum_congr rfl fun j _ => by rw [hb j]
  rw [volumeOperator_apply, hval,
    alternatingMap_apply_sum_smul (volumeForm rfl o x) (basisOfMetricOrthonormal h) d]
  congr 1
  exact congrArg _ (funext hb)

omit [FiniteDimensional ℝ E] in
/-- **Math.** Petersen §2.1.3, the "one slot changed" computation: replacing
the `i`-th field of a `g`-orthonormal frame normalized to `vol(E₁, …, E_n) = 1`
at `x` by any field `W` gives `vol(E₁, …, W, …, E_n)(x) = g(W|_x, Eᵢ|_x)` —
orthonormal expansion of `W|_x` plus alternation. -/
theorem volumeOperator_update_frame
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q} {x : M}
    (horth : ∀ i j, hm.metric.metricInner x (Efr i x) (Efr j x) = if i = j then 1 else 0)
    (hvol : volumeOperator o Efr x = 1)
    (i : Fin (finrank ℝ E)) (W : Π q : M, TangentSpace I q) :
    volumeOperator o (Function.update Efr i W) x
      = hm.metric.metricInner x (W x) (Efr i x) := by
  have hexp := metricInner_orthonormal_expansion horth (W x)
  set c : Fin (finrank ℝ E) → ℝ := fun j => hm.metric.metricInner x (W x) (Efr j x)
    with hc
  have hval : (fun k => Function.update Efr i W k x)
      = Function.update (fun k => Efr k x) i (∑ j, c j • Efr j x) := by
    rw [eval_update, hexp]
  have hsum := (volumeForm rfl o x).toMultilinearMap.map_update_sum Finset.univ i
    (fun j => c j • Efr j x) (fun k => Efr k x)
  rw [AlternatingMap.coe_multilinearMap] at hsum
  rw [volumeOperator_apply, hval, hsum]
  have hterm : ∀ j, (volumeForm rfl o x)
      (Function.update (fun k => Efr k x) i (c j • Efr j x))
      = if j = i then c j else 0 := by
    intro j
    rw [show (volumeForm rfl o x)
        (Function.update (fun k => Efr k x) i (c j • Efr j x))
        = c j * (volumeForm rfl o x)
            (Function.update (fun k => Efr k x) i (Efr j x)) by
      have := (volumeForm rfl o x).map_update_smul (fun k => Efr k x) i (c j) (Efr j x)
      simp only [smul_eq_mul] at this
      exact this]
    rcases eq_or_ne j i with rfl | hji
    · rw [Function.update_eq_self]
      have : (volumeForm rfl o x) (fun k => Efr k x) = 1 := hvol
      rw [this, mul_one, if_pos rfl]
    · rw [if_neg hji]
      have hzero : (volumeForm rfl o x)
          (Function.update (fun k => Efr k x) i (Efr j x)) = 0 := by
        refine (volumeForm rfl o x).map_eq_zero_of_eq _ (i := i) (j := j) ?_ ?_
        · rw [Function.update_self, Function.update_of_ne hji]
        · exact fun h => hji (h.symm)
      rw [hzero, mul_zero]
  calc ∑ j, (volumeForm rfl o x)
        (Function.update (fun k => Efr k x) i (c j • Efr j x))
      = ∑ j, if j = i then c j else 0 := Finset.sum_congr rfl fun j _ => hterm j
    _ = c i := by simp
    _ = hm.metric.metricInner x (W x) (Efr i x) := rfl

end FrameAlgebra

/-! ## Directional-derivative calculus: sums, products, Jacobi's formula -/

section DerivativeCalculus

omit [IsManifold I ∞ M] in
/-- A finite sum of functions differentiable at `x` is differentiable at `x`. -/
theorem mdifferentiableAt_finset_sum {ι : Type*} {s : Finset ι} {f : ι → M → ℝ}
    {x : M} (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun q => ∑ i ∈ s, f i q) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mdifferentiableAt_const (c := (0 : ℝ))
  | @insert a s ha ih =>
      have heq : (fun q => ∑ i ∈ insert a s, f i q)
          = fun q => f a q + ∑ i ∈ s, f i q := by
        funext q; rw [Finset.sum_insert ha]
      rw [heq]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

omit [IsManifold I ∞ M] in
/-- A finite product of functions differentiable at `x` is differentiable at
`x`. -/
theorem mdifferentiableAt_finset_prod {ι : Type*} {s : Finset ι} {f : ι → M → ℝ}
    {x : M} (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun q => ∏ i ∈ s, f i q) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mdifferentiableAt_const (c := (1 : ℝ))
  | @insert a s ha ih =>
      have heq : (fun q => ∏ i ∈ insert a s, f i q)
          = fun q => f a q * ∏ i ∈ s, f i q := by
        funext q; rw [Finset.prod_insert ha]
      rw [heq]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The directional derivative of a finite sum is the sum of the directional
derivatives. -/
theorem directionalDerivative_finset_sum {ι : Type*} {s : Finset ι}
    {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x)
    (X : Π q : M, TangentSpace I q) :
    directionalDerivative X (fun q => ∑ i ∈ s, f i q) x
      = ∑ i ∈ s, directionalDerivative X (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact directionalDerivative_const X 0 x
  | @insert a s ha ih =>
      have heq : (fun q => ∑ i ∈ insert a s, f i q)
          = fun q => f a q + ∑ i ∈ s, f i q := by
        funext q; rw [Finset.sum_insert ha]
      have hsum := mdifferentiableAt_finset_sum
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hadd : directionalDerivative X (fun q => f a q + ∑ i ∈ s, f i q) x
          = directionalDerivative X (f a) x
            + directionalDerivative X (fun q => ∑ i ∈ s, f i q) x :=
        directionalDerivative_add (hf a (Finset.mem_insert_self a s)) hsum X
      rw [heq, hadd, Finset.sum_insert ha,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **Math.** Leibniz rule for finite products:
`D_X (Π f_i) = Σ_i (Π_{j ≠ i} f_j)·(D_X f_i)`. -/
theorem directionalDerivative_finset_prod {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (f i) x)
    (X : Π q : M, TangentSpace I q) :
    directionalDerivative X (fun q => ∏ i ∈ s, f i q) x
      = ∑ i ∈ s, (∏ j ∈ s.erase i, f j x) * directionalDerivative X (f i) x := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Finset.prod_empty]
      exact directionalDerivative_const X 1 x
  | @insert a s ha ih =>
      have heq : (fun q => ∏ i ∈ insert a s, f i q)
          = fun q => f a q * ∏ i ∈ s, f i q := by
        funext q; rw [Finset.prod_insert ha]
      have hprod := mdifferentiableAt_finset_prod
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hmul : directionalDerivative X (fun q => f a q * ∏ i ∈ s, f i q) x
          = f a x * directionalDerivative X (fun q => ∏ i ∈ s, f i q) x
            + (∏ i ∈ s, f i x) * directionalDerivative X (f a) x :=
        directionalDerivative_mul (hf a (Finset.mem_insert_self a s)) hprod X
      rw [heq, hmul, ih fun i hi => hf i (Finset.mem_insert_of_mem hi),
        Finset.sum_insert ha, Finset.erase_insert ha]
      have hterm : ∀ i ∈ s,
          (∏ j ∈ (insert a s).erase i, f j x) * directionalDerivative X (f i) x
            = f a x * ((∏ j ∈ s.erase i, f j x)
                * directionalDerivative X (f i) x) := by
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [Finset.erase_insert_of_ne (Ne.symm hia),
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      ring

end DerivativeCalculus

/-! ## The Cramer identity and Jacobi's formula for the determinant -/

/-- **Math.** The Cramer identity: replacing the `i`-th row of `A` by a fixed
row `r` and pairing against the `l`-th column of `A`,
`Σᵢ Aᵢₗ · det(A with row i ← r) = det A · rₗ` — Cramer's rule transposed. -/
private theorem sum_mul_det_updateRow {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (r : Fin N → ℝ) (l : Fin N) :
    ∑ i, A i l * (A.updateRow i r).det = A.det * r l := by
  have hdet : ∀ i, (A.updateRow i r).det = Matrix.cramer Aᵀ r i := by
    intro i
    rw [Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]
  have hmv := congrFun (Matrix.mulVec_cramer Aᵀ r) l
  calc ∑ i, A i l * (A.updateRow i r).det
      = ∑ i, Aᵀ l i * Matrix.cramer Aᵀ r i :=
        Finset.sum_congr rfl fun i _ => by rw [hdet i, Matrix.transpose_apply]
    _ = (Aᵀ *ᵥ Matrix.cramer Aᵀ r) l := rfl
    _ = (Aᵀ.det • r) l := by rw [hmv]
    _ = A.det * r l := by rw [Matrix.det_transpose]; simp

/-- **Math.** **Jacobi's formula** for a matrix of functions: the directional
derivative of `q ↦ det (c q)` is the sum over rows `k` of the determinant of
`c x` with the `k`-th row replaced by its derivative,
`D_X det(c) = Σₖ det(c x with row k ← D_X (row k))`. -/
private theorem directionalDerivative_det_coeff {N : ℕ}
    (c : Fin N → Fin N → M → ℝ) {x : M}
    (hc : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (c i j) x)
    (X : Π q : M, TangentSpace I q) :
    directionalDerivative X (fun q => (Matrix.of fun i j => c i j q).det) x
      = ∑ k, ((Matrix.of fun i j => c i j x).updateRow k
          (fun j => directionalDerivative X (c k j) x)).det := by
  classical
  set s : Equiv.Perm (Fin N) → ℝ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) with hs
  have hdet : (fun q => (Matrix.of fun i j => c i j q).det)
      = fun q => ∑ σ : Equiv.Perm (Fin N), s σ * ∏ i, c (σ i) i q := by
    funext q
    rw [Matrix.det_apply']
    rfl
  have hterm_diff : ∀ σ : Equiv.Perm (Fin N),
      MDifferentiableAt I 𝓘(ℝ) (fun q => ∏ i, c (σ i) i q) x :=
    fun σ => mdifferentiableAt_finset_prod fun i _ => hc (σ i) i
  have hsmul_diff : ∀ σ : Equiv.Perm (Fin N),
      MDifferentiableAt I 𝓘(ℝ) (fun q => s σ * ∏ i, c (σ i) i q) x :=
    fun σ => mdifferentiableAt_const.mul (hterm_diff σ)
  -- the right-hand side, one row-replaced determinant at a time
  have hRHS : ∀ k, ((Matrix.of fun i j => c i j x).updateRow k
      (fun j => directionalDerivative X (c k j) x)).det
      = ∑ σ : Equiv.Perm (Fin N), s σ *
          (directionalDerivative X (c k (σ.symm k)) x
            * ∏ i ∈ Finset.univ.erase (σ.symm k), c (σ i) i x) := by
    intro k
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ((Matrix.of fun i j => c i j x).updateRow k
        (fun j => directionalDerivative X (c k j) x)) (σ i) i)
      (Finset.mem_univ (σ.symm k))]
    congr 1
    · rw [Matrix.updateRow_apply, if_pos (σ.apply_symm_apply k)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hik : σ i ≠ k := by
        intro h
        exact Finset.ne_of_mem_erase hi (by rw [← h, Equiv.symm_apply_apply])
      rw [Matrix.updateRow_apply, if_neg hik]
      rfl
  have hRHS_total : ∑ k, ((Matrix.of fun i j => c i j x).updateRow k
      (fun j => directionalDerivative X (c k j) x)).det
      = ∑ σ : Equiv.Perm (Fin N), s σ * ∑ i₀,
          directionalDerivative X (c (σ i₀) i₀) x
            * ∏ i ∈ Finset.univ.erase i₀, c (σ i) i x := by
    simp_rw [hRHS]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [← Equiv.sum_comp σ (fun k => directionalDerivative X (c k (σ.symm k)) x
      * ∏ i ∈ Finset.univ.erase (σ.symm k), c (σ i) i x)]
    refine Finset.sum_congr rfl fun i₀ _ => ?_
    rw [Equiv.symm_apply_apply]
  rw [hdet, hRHS_total,
    directionalDerivative_finset_sum (fun σ _ => hsmul_diff σ) X]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hcs : directionalDerivative X (fun q => s σ * ∏ i, c (σ i) i q) x
      = s σ * directionalDerivative X (fun q => ∏ i, c (σ i) i q) x :=
    directionalDerivative_const_smul (hterm_diff σ) (s σ) X
  have hpr : directionalDerivative X (fun q => ∏ i, c (σ i) i q) x
      = ∑ i₀, (∏ j ∈ Finset.univ.erase i₀, c (σ j) j x)
          * directionalDerivative X (c (σ i₀) i₀) x :=
    directionalDerivative_finset_prod (fun i _ => hc (σ i) i) X
  rw [hcs, hpr]
  congr 1
  exact Finset.sum_congr rfl fun i₀ _ => mul_comm _ _

/-! ## The Lie bracket against frame combinations -/

section BracketExpansion

variable [CompleteSpace E]

/-- **Math.** Leibniz expansion of the Lie bracket against a combination of
fields: `[X, Σⱼ cⱼ Vⱼ]|_x = Σⱼ ((D_X cⱼ)|_x Vⱼ|_x + cⱼ(x) [X, Vⱼ]|_x)`. -/
theorem lieDerivativeVectorField_finset_sum_smul {N : ℕ}
    (X : Π q : M, TangentSpace I q)
    {c : Fin N → M → ℝ} (hc : ∀ j, ContMDiff I 𝓘(ℝ) ∞ (c j))
    {V : Fin N → Π q : M, TangentSpace I q} (hV : ∀ j, IsSmoothVectorField (V j))
    (x : M) :
    lieDerivativeVectorField I X (fun q => ∑ j, c j q • V j q) x
      = ∑ j, (directionalDerivative X (c j) x • V j x
          + c j x • lieDerivativeVectorField I X (V j) x) := by
  classical
  have hsmul_smooth : ∀ j, IsSmoothVectorField (fun q => c j q • V j q) := by
    intro j
    have := (SmoothVectorField.smul (c j) (hc j) ⟨V j, hV j⟩).smooth
    simpa using this
  have hpartial : ∀ s : Finset (Fin N),
      IsSmoothVectorField (fun q => ∑ j ∈ s, c j q • V j q) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have := ((0 : SmoothVectorField I M)).smooth
        have heq : (fun q : M => ∑ j ∈ (∅ : Finset (Fin N)), c j q • V j q)
            = fun q : M => ((0 : SmoothVectorField I M) q) := by
          funext q; simp
        rw [heq]
        exact this
    | @insert a s ha ih =>
        have := ((⟨_, hsmul_smooth a⟩ + ⟨_, ih⟩ : SmoothVectorField I M)).smooth
        have heq : (fun q => ∑ j ∈ insert a s, c j q • V j q)
            = fun q => c a q • V a q + ∑ j ∈ s, c j q • V j q := by
          funext q; rw [Finset.sum_insert ha]
        rw [heq]
        exact this
  have key : ∀ s : Finset (Fin N),
      lieDerivativeVectorField I X (fun q => ∑ j ∈ s, c j q • V j q) x
        = ∑ j ∈ s, (directionalDerivative X (c j) x • V j x
            + c j x • lieDerivativeVectorField I X (V j) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        show VectorField.mlieBracket I X (0 : Π q : M, TangentSpace I q) x = 0
        rw [VectorField.mlieBracket_zero_right]
        rfl
    | @insert a s ha ih =>
        have heq : (fun q => ∑ j ∈ insert a s, c j q • V j q)
            = fun q => c a q • V a q + ∑ j ∈ s, c j q • V j q := by
          funext q; rw [Finset.sum_insert ha]
        have h1 : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
            (fun q => (⟨q, c a q • V a q⟩ : TangentBundle I M)) x :=
          ((hsmul_smooth a) x).mdifferentiableAt (by decide)
        have h2 : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
            (fun q => (⟨q, ∑ j ∈ s, c j q • V j q⟩ : TangentBundle I M)) x :=
          ((hpartial s) x).mdifferentiableAt (by decide)
        have hadd : lieDerivativeVectorField I X
            (fun q => c a q • V a q + ∑ j ∈ s, c j q • V j q) x
            = lieDerivativeVectorField I X (fun q => c a q • V a q) x
              + lieDerivativeVectorField I X (fun q => ∑ j ∈ s, c j q • V j q) x := by
          show VectorField.mlieBracket I X
            ((fun q => c a q • V a q) + fun q => ∑ j ∈ s, c j q • V j q) x = _
          rw [VectorField.mlieBracket_add_right h1 h2]
          rfl
        have hfd : MDifferentiableAt I 𝓘(ℝ) (c a) x :=
          ((hc a) x).mdifferentiableAt (by decide)
        have hVd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
            (fun q => (⟨q, V a q⟩ : TangentBundle I M)) x :=
          ((hV a) x).mdifferentiableAt (by decide)
        have hsm : lieDerivativeVectorField I X (fun q => c a q • V a q) x
            = directionalDerivative X (c a) x • V a x
              + c a x • lieDerivativeVectorField I X (V a) x := by
          show VectorField.mlieBracket I X ((c a) • (V a)) x = _
          rw [VectorField.mlieBracket_smul_right hfd hVd]
          rfl
        rw [heq, hadd, hsm, Finset.sum_insert ha, ih]
  exact key Finset.univ

end BracketExpansion

/-! ## Locality of `L_X vol` at a point -/

section Locality

variable [FiniteDimensional ℝ E] [hm : HasMetric I M]

omit [FiniteDimensional ℝ E] in
/-- The value `(L_X vol)(Y₁, …, Y_n)(x)` only depends on the fields `Yᵢ` near
`x`: the volume operator is pointwise and both the directional derivative and
the Lie brackets are local. -/
theorem lieDerivativeTensor_volumeOperator_congr_nhds
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q)
    {Y Z : Fin (finrank ℝ E) → Π q : M, TangentSpace I q} {x : M}
    (h : ∀ i, Y i =ᶠ[𝓝 x] Z i) :
    lieDerivativeTensor I X (volumeOperator o) Y x
      = lieDerivativeTensor I X (volumeOperator o) Z x := by
  have hall : ∀ᶠ q in 𝓝 x, ∀ i, Y i q = Z i q := Filter.eventually_all.mpr h
  have hev : volumeOperator o Y =ᶠ[𝓝 x] volumeOperator o Z := by
    filter_upwards [hall] with q hq
    exact volumeOperator_congr_at o hq
  rw [lieDerivativeTensor_formula, lieDerivativeTensor_formula]
  congr 1
  · show mfderiv I 𝓘(ℝ) (volumeOperator o Y) x (X x)
      = mfderiv I 𝓘(ℝ) (volumeOperator o Z) x (X x)
    rw [hev.mfderiv_eq]
    rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine volumeOperator_congr_at o fun k => ?_
    rcases eq_or_ne k i with rfl | hk
    · simp only [Function.update_self]
      show lieDerivativeVectorField I X (Y k) x = lieDerivativeVectorField I X (Z k) x
      exact Filter.EventuallyEq.mlieBracket_vectorField_eq
        (Filter.EventuallyEq.refl _ _) (h k)
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      exact (h k).self_of_nhds

end Locality

/-! ## The frame computation: `L_X vol` against a normalized orthonormal frame -/

section FrameComputation

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [hm : HasMetric I M]

omit [FiniteDimensional ℝ E] in
/-- **Math.** Petersen §2.1.3, the frame computation behind the trace formula:
against an orthonormal frame `E₁, …, E_n` with `vol(E₁, …, E_n) = 1` on a
neighborhood of `x`,
`(L_X vol)(E₁, …, E_n)(x) = −Σᵢ g([X, Eᵢ], Eᵢ)(x)` —
the `D_X` term dies because `vol(E₁, …, E_n)` is constant near `x`, and each
correction term is computed by orthonormal expansion and alternation. -/
theorem lieDerivativeTensor_volumeOperator_frame
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q} {U : Set M} {x : M}
    (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    lieDerivativeTensor I X (volumeOperator o) Efr x
      = -∑ i, hm.metric.metricInner x
          (lieDerivativeVectorField I X (Efr i) x) (Efr i x) := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  rw [lieDerivativeTensor_formula]
  have hconst : volumeOperator o Efr =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hU] with y hy
    exact hvol y hy
  have hD : directionalDerivative X (volumeOperator o Efr) x = 0 := by
    rw [directionalDerivative_apply, hconst.mfderiv_eq, mfderiv_const]
    rfl
  have hcor : ∀ i, volumeOperator o
      (Function.update Efr i (lieDerivativeVectorField I X (Efr i))) x
      = hm.metric.metricInner x (lieDerivativeVectorField I X (Efr i) x) (Efr i x) :=
    fun i => volumeOperator_update_frame o (horth x hxU) (hvol x hxU) i _
  rw [hD, Finset.sum_congr rfl fun i _ => hcor i]
  ring

/-- **Math.** The Leibniz rule for the determinant along the flow: against a
normalized orthonormal frame near `x` and smooth coefficient functions `c`,
`(L_X vol)(Σⱼ c₁ⱼ Eⱼ, …, Σⱼ c_nⱼ Eⱼ)(x) = det(c(x)) · (L_X vol)(E₁, …, E_n)(x)`.
The `D_X` term is Jacobi's formula (`directionalDerivative_det_coeff`), the
bracket corrections expand by the Leibniz rule for `[X, Σⱼ cⱼ Eⱼ]`, and the
row-replaced determinants recombine through the Cramer identity
(`sum_mul_det_updateRow`). This is the tensoriality of `L_X vol`, made
quantitative. -/
theorem lieDerivativeTensor_volumeOperator_combination
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {c : Fin (finrank ℝ E) → Fin (finrank ℝ E) → M → ℝ}
    (hc : ∀ i j, ContMDiff I 𝓘(ℝ) ∞ (c i j)) :
    lieDerivativeTensor I X (volumeOperator o) (fun i q => ∑ j, c i j q • Efr j q) x
      = (Matrix.of fun i j => c i j x).det
          * lieDerivativeTensor I X (volumeOperator o) Efr x := by
  classical
  have hxU : x ∈ U := mem_of_mem_nhds hU
  set A : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
    Matrix.of fun i j => c i j x with hA
  set B : Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ :=
    fun k j => directionalDerivative X (c k j) x with hB
  set Γ : Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ := fun l j =>
    hm.metric.metricInner x (lieDerivativeVectorField I X (Efr l) x) (Efr j x)
    with hΓ
  -- evaluating the volume form on any pointwise frame combination
  have happ : ∀ d : Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ,
      (volumeForm rfl o x) (fun k => ∑ j, d k j • Efr j x) = (Matrix.of d).det := by
    intro d
    have h1 : (fun k => ∑ j, d k j • Efr j x)
        = fun k => ∑ j, d k j • (basisOfMetricOrthonormal (horth x hxU)) j := by
      funext k
      exact Finset.sum_congr rfl fun j _ => by
        rw [basisOfMetricOrthonormal_apply (horth x hxU) j]
    have h2 : (volumeForm rfl o x) ⇑(basisOfMetricOrthonormal (horth x hxU)) = 1 := by
      have hcoe : ⇑(basisOfMetricOrthonormal (horth x hxU)) = fun k => Efr k x :=
        funext (basisOfMetricOrthonormal_apply (horth x hxU))
      rw [hcoe]
      exact hvol x hxU
    rw [h1, alternatingMap_apply_sum_smul (volumeForm rfl o x)
      (basisOfMetricOrthonormal (horth x hxU)) d, h2, mul_one]
  -- the evaluation of `vol` on the combination agrees with `det ∘ c` near `x`
  have hvolY : volumeOperator o (fun i q => ∑ j, c i j q • Efr j q)
      =ᶠ[𝓝 x] fun q => (Matrix.of fun i j => c i j q).det := by
    filter_upwards [hU] with y hy
    have h1 := volumeOperator_apply_of_expansion o (horth y hy)
      (fun i q => ∑ j, c i j q • Efr j q) (fun i j => c i j y) (fun i => rfl)
    rw [h1, show volumeForm rfl o y (fun j => Efr j y) = volumeOperator o Efr y
      from rfl, hvol y hy, mul_one]
  -- the `D_X` term: Jacobi's formula
  have hDX : directionalDerivative X
      (volumeOperator o (fun i q => ∑ j, c i j q • Efr j q)) x
      = ∑ k, (A.updateRow k (B k)).det := by
    rw [directionalDerivative_apply, hvolY.mfderiv_eq]
    exact directionalDerivative_det_coeff c
      (fun i j => ((hc i j) x).mdifferentiableAt (by decide)) X
  -- the bracket of `X` with each combination field
  have hbr : ∀ i, lieDerivativeVectorField I X (fun q => ∑ j, c i j q • Efr j q) x
      = ∑ j, (B i j • Efr j x
          + c i j x • lieDerivativeVectorField I X (Efr j) x) :=
    fun i => lieDerivativeVectorField_finset_sum_smul X (fun j => hc i j) hEs x
  -- each correction term
  have hcor : ∀ i, volumeOperator o
      (Function.update (fun i q => ∑ j, c i j q • Efr j q) i
        (lieDerivativeVectorField I X (fun q => ∑ j, c i j q • Efr j q))) x
      = (A.updateRow i (B i)).det + ∑ l, c i l x * (A.updateRow i (Γ l)).det := by
    intro i
    have htuple : ∀ (r : Fin (finrank ℝ E) → ℝ) (u : TangentSpace I x),
        u = ∑ j, r j • Efr j x →
        Function.update (fun k => ∑ j, c k j x • Efr j x) i u
          = fun k => ∑ j, (A.updateRow i r) k j • Efr j x := by
      intro r u hu
      funext k
      rcases eq_or_ne k i with rfl | hk
      · rw [Function.update_self, hu]
        exact Finset.sum_congr rfl fun j _ => by simp [Matrix.updateRow_self]
      · rw [Function.update_of_ne hk]
        exact Finset.sum_congr rfl fun j _ => by simp [Matrix.updateRow_ne hk, hA]
    have hupd : (fun k => Function.update (fun i q => ∑ j, c i j q • Efr j q) i
        (lieDerivativeVectorField I X (fun q => ∑ j, c i j q • Efr j q)) k x)
        = Function.update (fun k => ∑ j, c k j x • Efr j x) i
            ((∑ j, B i j • Efr j x)
              + ∑ j, c i j x • lieDerivativeVectorField I X (Efr j) x) := by
      rw [eval_update]
      congr 1
      rw [hbr i, Finset.sum_add_distrib]
    rw [volumeOperator_apply, hupd,
      (volumeForm rfl o x).map_update_add (fun k => ∑ j, c k j x • Efr j x) i
        (∑ j, B i j • Efr j x)
        (∑ j, c i j x • lieDerivativeVectorField I X (Efr j) x)]
    congr 1
    · -- the `B`-row term
      rw [htuple (B i) _ rfl]
      exact happ _
    · -- the bracket terms, expanded in the frame
      have hsum := (volumeForm rfl o x).toMultilinearMap.map_update_sum Finset.univ i
        (fun j => c i j x • lieDerivativeVectorField I X (Efr j) x)
        (fun k => ∑ j, c k j x • Efr j x)
      rw [AlternatingMap.coe_multilinearMap] at hsum
      rw [hsum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hsm := (volumeForm rfl o x).map_update_smul
        (fun k => ∑ j, c k j x • Efr j x) i (c i l x)
        (lieDerivativeVectorField I X (Efr l) x)
      rw [hsm, smul_eq_mul]
      congr 1
      have hexp : lieDerivativeVectorField I X (Efr l) x = ∑ j, Γ l j • Efr j x :=
        metricInner_orthonormal_expansion (horth x hxU) _
      rw [htuple (Γ l) _ hexp]
      exact happ _
  -- assemble, and recombine through the Cramer identity
  have hframe : lieDerivativeTensor I X (volumeOperator o) Efr x = -∑ l, Γ l l :=
    lieDerivativeTensor_volumeOperator_frame o X hU horth hvol
  have hcram : ∑ i, ∑ l, c i l x * (A.updateRow i (Γ l)).det
      = A.det * ∑ l, Γ l l := by
    rw [Finset.sum_comm]
    have hlrow : ∀ l, ∑ i, c i l x * (A.updateRow i (Γ l)).det = A.det * Γ l l :=
      fun l => sum_mul_det_updateRow A (Γ l) l
    rw [Finset.sum_congr rfl fun l _ => hlrow l, ← Finset.mul_sum]
  rw [lieDerivativeTensor_formula, hDX,
    Finset.sum_congr rfl fun i _ => hcor i, Finset.sum_add_distrib, hcram, hframe]
  ring

/-- **Math.** The **defining property of the divergence against a normalized
orthonormal frame**: for any tuple of smooth fields `Y₁, …, Y_n`,
`(L_X vol)(Y₁, …, Y_n)(x) = (L_X vol)(E₁, …, E_n)(x) · vol(Y₁, …, Y_n)(x)` —
`L_X vol` is a top-degree form, hence a multiple of `vol`. Proved by expanding
each `Yᵢ` in the frame near `x` (locality + orthonormal expansion) and applying
the determinant Leibniz rule `lieDerivativeTensor_volumeOperator_combination`. -/
theorem lieDerivativeTensor_volumeOperator_eq_frame_smul
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {Y : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hY : ∀ i, IsSmoothVectorField (Y i)) :
    lieDerivativeTensor I X (volumeOperator o) Y x
      = lieDerivativeTensor I X (volumeOperator o) Efr x * volumeOperator o Y x := by
  classical
  have hxU : x ∈ U := mem_of_mem_nhds hU
  -- the smooth coefficients of `Y` in the frame
  set c : Fin (finrank ℝ E) → Fin (finrank ℝ E) → M → ℝ :=
    fun i j q => hm.metric.metricInner q (Y i q) (Efr j q) with hcdef
  have hc : ∀ i j, ContMDiff I 𝓘(ℝ) ∞ (c i j) := by
    intro i j
    have h := (metricOperator_isTensorOperator hm.metric).smooth_eval ![Y i, Efr j]
      (fun k => by fin_cases k <;> [exact hY i; exact hEs j])
    have heq : metricOperator hm.metric ![Y i, Efr j] = c i j := by
      funext q
      simp [metricOperator_apply, hcdef]
    rwa [heq] at h
  -- `Y` agrees with its frame expansion near `x`
  have hev : ∀ i, Y i =ᶠ[𝓝 x] (fun i q => ∑ j, c i j q • Efr j q) i := by
    intro i
    filter_upwards [hU] with y hy
    exact metricInner_orthonormal_expansion (horth y hy) (Y i y)
  have hvolY : volumeOperator o Y x = (Matrix.of fun i j => c i j x).det := by
    have h1 := volumeOperator_apply_of_expansion o (horth x hxU) Y
      (fun i j => c i j x)
      (fun i => metricInner_orthonormal_expansion (horth x hxU) (Y i x))
    rw [h1, show volumeForm rfl o x (fun j => Efr j x) = volumeOperator o Efr x
      from rfl, hvol x hxU, mul_one]
  rw [lieDerivativeTensor_volumeOperator_congr_nhds o X hev,
    lieDerivativeTensor_volumeOperator_combination o X hEs hU horth hvol hc, hvolY]
  ring

end FrameComputation

/-! ## The divergence via the Lie derivative of the volume form -/

section Divergence

variable [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [hm : HasMetric I M]

/-- **Math.** Petersen §2.1.3: the **divergence** of a vector field `X`,
defined implicitly by `L_X vol = (div X) · vol` — the function measuring how
the volume form changes along the flow of `X`.

**Eng.** Concrete realization: at each `x` the chart-basis fields
`Tensor.chartBasisVecFiber x i` form a basis of `T_xM`, on which the volume
form is nonzero (`volumeOperator_chartFrame_ne_zero`); `div X (x)` is the
ratio `(L_X vol)(∂₁, …, ∂_n)(x) / vol(∂₁, …, ∂_n)(x)`. The defining property
holds definitionally against this frame
(`lieDerivativeTensor_volumeOperator_chartFrame`) and against every tuple of
smooth fields whenever a normalized orthonormal frame exists near `x`
(`lieDerivativeTensor_volumeOperator_eq_smul`). -/
def divergenceLieDerivative
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q) (x : M) : ℝ :=
  lieDerivativeTensor I X (volumeOperator o)
      (fun i => Tensor.chartBasisVecFiber (I := I) x i) x
    / volumeOperator o (fun i => Tensor.chartBasisVecFiber (I := I) x i) x

/-- **Math.** Well-posedness of the divergence: the volume form is nonzero on
the chart-basis frame at `x` (a basis of `T_xM`), by the `1`-dimensionality of
top-degree alternating forms. -/
theorem volumeOperator_chartFrame_ne_zero
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E))) (x : M) :
    volumeOperator o (fun i => Tensor.chartBasisVecFiber (I := I) x i) x ≠ 0 := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hpos : 0 < finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hne : (volumeForm rfl o x : (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→ₗ[ℝ] ℝ)
      ≠ 0 := by
    show (o x).volumeForm ≠ 0
    rw [(o x).volumeForm_robust ((o x).finOrthonormalBasis hpos rfl)
      ((o x).finOrthonormalBasis_orientation hpos rfl)]
    exact ((o x).finOrthonormalBasis hpos rfl).toBasis.det_ne_zero
  have hval := ((volumeForm rfl o x).map_basis_ne_zero_iff
    (Tensor.chartBasisFamily (I := I) x hb)).mpr hne
  have hcoe : (fun i => Tensor.chartBasisVecFiber (I := I) x i x)
      = ⇑(Tensor.chartBasisFamily (I := I) x hb) := by
    funext i
    exact (Tensor.chartBasisFamily_apply (I := I) x hb i).symm
  rw [volumeOperator_apply, hcoe]
  exact hval

/-- **Math.** The defining property `L_X vol = (div X) · vol` of
`def:pet-ch2-divergence-lie-derivative`, against the chart-basis frame at `x`
(definitional, given the nonvanishing of the denominator). -/
theorem lieDerivativeTensor_volumeOperator_chartFrame
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q) (x : M) :
    lieDerivativeTensor I X (volumeOperator o)
        (fun i => Tensor.chartBasisVecFiber (I := I) x i) x
      = divergenceLieDerivative o X x
          * volumeOperator o (fun i => Tensor.chartBasisVecFiber (I := I) x i) x :=
  (div_mul_cancel₀ _ (volumeOperator_chartFrame_ne_zero o x)).symm

/-- **Math.** Petersen §2.1.3: the **Laplacian** `Δf = div ∇f`
(`def:pet-ch2-laplacian`). -/
def laplacian (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (f : M → ℝ) : M → ℝ :=
  divergenceLieDerivative o (gradient hm.metric f)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem laplacian_apply
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (f : M → ℝ) (x : M) :
    laplacian o f x = divergenceLieDerivative o (gradient hm.metric f) x := rfl

end Divergence

/-! ## The trace formula for the divergence -/

section TraceFormula

variable [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [hm : HasMetric I M]

/-- **Math.** Against a normalized orthonormal frame near `x`, the divergence
is the Lie derivative of the volume form evaluated on the frame:
`div X (x) = (L_X vol)(E₁, …, E_n)(x)`. The chart-basis frame defining
`div X (x)` is replaced by global smooth fields agreeing with it near `x`, on
which the defining property `lieDerivativeTensor_volumeOperator_eq_frame_smul`
applies. -/
theorem divergenceLieDerivative_eq_frame
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    divergenceLieDerivative o X x
      = lieDerivativeTensor I X (volumeOperator o) Efr x := by
  classical
  -- global smooth fields agreeing with the chart-basis frame near `x`
  have hZ : ∀ i : Fin (finrank ℝ E), ∃ Z : SmoothVectorField I M,
      ∀ᶠ y in 𝓝 x, Z y = Tensor.chartBasisVecFiber (I := I) x i y :=
    fun i => exists_smoothVectorField_eventuallyEq (I := I)
      (trivializationAt E (TangentSpace I) x).open_baseSet
      (Tensor.chartBasisVec_contMDiffOn (I := I) x i)
      (FiberBundle.mem_baseSet_trivializationAt' x)
  choose Z hZev using hZ
  have hloc : lieDerivativeTensor I X (volumeOperator o)
      (fun i => Tensor.chartBasisVecFiber (I := I) x i) x
      = lieDerivativeTensor I X (volumeOperator o) (fun i => ⇑(Z i)) x :=
    lieDerivativeTensor_volumeOperator_congr_nhds o X
      fun i => Filter.EventuallyEq.symm (hZev i)
  have hvalx : volumeOperator o (fun i => Tensor.chartBasisVecFiber (I := I) x i) x
      = volumeOperator o (fun i => ⇑(Z i)) x :=
    volumeOperator_congr_at o fun i => ((hZev i).self_of_nhds).symm
  have hkey := lieDerivativeTensor_volumeOperator_eq_frame_smul o X hEs hU horth
    hvol (Y := fun i => ⇑(Z i)) (fun i => (Z i).smooth)
  have hne : volumeOperator o (fun i => ⇑(Z i)) x ≠ 0 := by
    rw [← hvalx]
    exact volumeOperator_chartFrame_ne_zero o x
  show lieDerivativeTensor I X (volumeOperator o)
      (fun i => Tensor.chartBasisVecFiber (I := I) x i) x
    / volumeOperator o (fun i => Tensor.chartBasisVecFiber (I := I) x i) x = _
  rw [hloc, hvalx, hkey]
  exact mul_div_cancel_right₀ _ hne

/-- **Math.** The **defining property of the divergence**
(`def:pet-ch2-divergence-lie-derivative`): whenever a normalized orthonormal
frame exists near `x`, then for every tuple of smooth fields `Y₁, …, Y_n`,
`(L_X vol)(Y₁, …, Y_n)(x) = div X (x) · vol(Y₁, …, Y_n)(x)`. -/
theorem lieDerivativeTensor_volumeOperator_eq_smul
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {Y : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hY : ∀ i, IsSmoothVectorField (Y i)) :
    lieDerivativeTensor I X (volumeOperator o) Y x
      = divergenceLieDerivative o X x * volumeOperator o Y x := by
  rw [lieDerivativeTensor_volumeOperator_eq_frame_smul o X hEs hU horth hvol hY,
    divergenceLieDerivative_eq_frame o X hEs hU horth hvol]

/-- **Math.** **`prop:pet-ch2-divergence-trace-formula`** (Petersen §2.1.3):
for a positively oriented orthonormal frame `E₁, …, E_n` near `x` — orthonormal
w.r.t. `g` and normalized to `vol(E₁, …, E_n) = 1` on a neighborhood `U` of `x`
— the divergence is the metric trace of the Lie derivative of the metric:
`div X = Σᵢ ½ (L_X g)(Eᵢ, Eᵢ)`.

Petersen's proof: differentiate `vol(E₁, …, E_n) ≡ 1` along `X`, so
`0 = (L_X vol)(E₁, …, E_n) + Σᵢ vol(E₁, …, [X, Eᵢ], …, E_n)`; each summand is
`g([X, Eᵢ], Eᵢ)` by orthonormal expansion and alternation, and
`g([X, Eᵢ], Eᵢ) = −½ (L_X g)(Eᵢ, Eᵢ)` since `g(Eᵢ, Eᵢ) ≡ 1` near `x`. -/
theorem divergence_trace_formula
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    divergenceLieDerivative o X x
      = ∑ i, (1 / 2 : ℝ)
          * lieDerivativeTensor I X (metricOperator hm.metric) ![Efr i, Efr i] x := by
  have hdiag : ∀ i, lieDerivativeTensor I X (metricOperator hm.metric)
      ![Efr i, Efr i] x
      = -2 * hm.metric.metricInner x
          (lieDerivativeVectorField I X (Efr i) x) (Efr i x) := by
    intro i
    rw [lieDerivativeTensor_formula, Fin.sum_univ_two]
    have h0 : (Function.update (![Efr i, Efr i]) (0 : Fin 2)
        (lieDerivativeVectorField I X (Efr i)))
        = ![lieDerivativeVectorField I X (Efr i), Efr i] := by
      funext j; fin_cases j <;> simp
    have h1 : (Function.update (![Efr i, Efr i]) (1 : Fin 2)
        (lieDerivativeVectorField I X (Efr i)))
        = ![Efr i, lieDerivativeVectorField I X (Efr i)] := by
      funext j; fin_cases j <;> simp
    have hconst : (metricOperator hm.metric ![Efr i, Efr i]) =ᶠ[𝓝 x]
        fun _ => (1 : ℝ) := by
      filter_upwards [hU] with y hy
      simpa [metricOperator_apply] using horth y hy i i
    have hD : directionalDerivative X (metricOperator hm.metric ![Efr i, Efr i]) x
        = 0 := by
      rw [directionalDerivative_apply, hconst.mfderiv_eq, mfderiv_const]
      rfl
    rw [hD]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1,
      metricOperator_apply]
    rw [hm.metric.metricInner_comm x (Efr i x)
      (lieDerivativeVectorField I X (Efr i) x)]
    ring
  rw [divergenceLieDerivative_eq_frame o X hEs hU horth hvol,
    lieDerivativeTensor_volumeOperator_frame o X hU horth hvol]
  have hsum : ∑ i, (1 / 2 : ℝ)
        * lieDerivativeTensor I X (metricOperator hm.metric) ![Efr i, Efr i] x
      = ∑ i, (1 / 2 : ℝ) * (-2 * hm.metric.metricInner x
          (lieDerivativeVectorField I X (Efr i) x) (Efr i x)) :=
    Finset.sum_congr rfl fun i _ => by rw [hdiag i]
  rw [hsum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Math.** Corollary of the trace formula (Petersen §2.1.3):
`Δf = div ∇f = Σᵢ Hess f(Eᵢ, Eᵢ)` against a positively oriented orthonormal
frame near `x` — the Laplacian is the metric trace of the Hessian. -/
theorem laplacian_eq_hessian_trace
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (f : M → ℝ)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    laplacian o f x = ∑ i, hessianLieDerivative hm.metric f ![Efr i, Efr i] x := by
  rw [laplacian_apply,
    divergence_trace_formula o (gradient hm.metric f) hEs hU horth hvol]
  exact Finset.sum_congr rfl fun i _ =>
    (hessianLieDerivative_apply hm.metric f ![Efr i, Efr i] x).symm

end TraceFormula

/-! ## The volume form is parallel (volume half of Prop. 2.2.5) -/

section VolumeParallel

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [hm : HasMetric I M]

omit [FiniteDimensional ℝ E] in
/-- **Math.** Volume half of **Prop. 2.2.5** (Petersen §2.2.2): `∇ vol = 0`
for any Riemannian connection, formulated against a normalized orthonormal
frame near `x`: `(∇_X vol)(E₁, …, E_n)(x) = 0`. The `D_X` term dies because
`vol(E₁, …, E_n) ≡ 1` near `x`, and each correction term
`vol(E₁, …, ∇_X Eᵢ, …, E_n)(x) = g(∇_X Eᵢ, Eᵢ)(x)` vanishes by metric
compatibility applied to the constant function `g(Eᵢ, Eᵢ) ≡ 1`. -/
theorem volume_parallel
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    covariantDerivativeTensor D.toAffineConnection X (volumeOperator o) Efr x
      = 0 := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  rw [covariantDerivativeTensor_formula]
  have hconst : volumeOperator o Efr =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hU] with y hy
    exact hvol y hy
  have hD : directionalDerivative X (volumeOperator o Efr) x = 0 := by
    rw [directionalDerivative_apply, hconst.mfderiv_eq, mfderiv_const]
    rfl
  have hcor : ∀ i, volumeOperator o
      (Function.update Efr i (D.covField X (Efr i))) x = 0 := by
    intro i
    rw [volumeOperator_update_frame o (horth x hxU) (hvol x hxU) i _]
    -- `g(∇_X Eᵢ, Eᵢ)(x) = 0` by metric compatibility on the constant `g(Eᵢ, Eᵢ)`
    have hcompat := D.metric_compat (hEs i) (hEs i) x (X x)
    rw [dirTangent_eq_directionalDerivative] at hcompat
    have hgconst : (fun q => hm.metric.metricInner q (Efr i q) (Efr i q))
        =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hU] with y hy
      simpa using horth y hy i i
    have hzero : directionalDerivative X
        (fun q => hm.metric.metricInner q (Efr i q) (Efr i q)) x = 0 := by
      rw [directionalDerivative_apply, hgconst.mfderiv_eq, mfderiv_const]
      rfl
    rw [hzero] at hcompat
    have hsym := hm.metric.metricInner_comm x (Efr i x) (D.cov x (X x) (Efr i))
    rw [AffineConnection.covField_apply]
    linarith [hcompat, hsym]
  rw [hD, Finset.sum_congr rfl fun i _ => hcor i]
  simp

omit [FiniteDimensional ℝ E] in
/-- **Math.** **Prop. 2.2.5** (Petersen §2.2.2): both the metric and the
volume form are parallel with respect to any Riemannian connection — `∇g = 0`
(globally, `metric_parallel`) and `∇ vol = 0` (against a normalized
orthonormal frame near `x`, `volume_parallel`). -/
theorem metric_and_volume_parallel
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    IsParallel D.toAffineConnection (metricOperator hm.metric)
      ∧ covariantDerivativeTensor D.toAffineConnection X (volumeOperator o) Efr x
          = 0 :=
  ⟨metric_parallel D, volume_parallel o D X hEs hU horth hvol⟩

end VolumeParallel

/-! ## The interior product

The remark `rem:pet-ch2-lie-derivative-volume-exact` (`L_X vol = d(i_X vol)`)
requires, beyond the interior product below, the identification of
`exteriorDerivative_lieFormula` on an `(n−1)`-tuple of frame fields with the
Lie derivative of the volume form; this combinatorial identity is **not**
formalized here (see the module docstring). -/

variable (I) in
/-- **Math.** The **interior product** `i_X T` of a `(0,k+1)`-tensor with a
vector field: `(i_X T)(Y₁, …, Y_k) = T(X, Y₁, …, Y_k)` — evaluation of `T` on
`X` in its first variable (Petersen §2.1.3). -/
def interiorProduct {k : ℕ} (T : TensorOperator I M (k + 1))
    (X : Π q : M, TangentSpace I q) : TensorOperator I M k :=
  fun Y => T (Fin.cons X Y)

omit [IsManifold I ∞ M] in
theorem interiorProduct_apply {k : ℕ} (T : TensorOperator I M (k + 1))
    (X : Π q : M, TangentSpace I q) (Y : Fin k → Π q : M, TangentSpace I q) :
    interiorProduct I T X Y = T (Fin.cons X Y) := rfl

end PetersenLib
