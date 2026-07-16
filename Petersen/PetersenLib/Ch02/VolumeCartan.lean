import PetersenLib.Ch02.VolumeDivergence
import PetersenLib.Ch02.ExteriorDerivative

/-!
# Petersen Ch. 2, §2.1.3 — `L_X vol = d(i_X vol)` (Cartan's magic formula for the
volume form)

`rem:pet-ch2-lie-derivative-volume-exact`.  Contrary to an earlier assessment,
this remark is **not** a statement about Stokes' theorem or manifold
integration.  It is the *pointwise algebraic* Cartan magic formula for a
top-degree form: with `d` Petersen's Lie-derivative exterior derivative
(`exteriorDerivative_lieFormula`, already in the project) and `i_X` the interior
product (`interiorProduct`), the identity `L_X vol = d(i_X vol)` holds because
`d(vol) = 0` (a top+1 form vanishes), so Cartan's `L_X = d i_X + i_X d`
collapses.  The Stokes/divergence-theorem input only enters the **downstream**
`adjoint_L2_identity` (Prop. 2.2.8), not this remark.

The one wrinkle is arity bookkeeping: `volumeOperator o` is a `(0, finrank ℝ E)`
tensor, while `interiorProduct` lowers a `(0, k+1)` tensor to a `(0, k)` tensor.
We therefore carry an explicit `hn : finrank ℝ E = m + 1` and reindex tuples
through `finCongr hn`.

## Status and route to `lieDerivative_volume_exact`

**Frame-value toolkit — LANDED and kernel-checked** (this file):
`interiorVolume` + the arity-`(m+1)` bridge `interiorVolume_eq_domDomCongr`;
`alternating_cons_succAbove_real` (the Laplace sign); and the four frame-value
lemmas that carry *all* the sign content of the Cartan formula:
* `interiorVolume_frame_succAbove` — `(i_X vol)(E'∘ŝᵢ) = (-1)^i g(X, E'ᵢ)`
  (deleted-index value);
* `interiorVolume_frame_perm` — general permuted co-frame:
  `(i_X vol)(fun j ↦ E'_{σ(j+1)}) = sign(σ) · g(X, E'_{σ 0})`;
* `interiorVolume_frame_update_self` — the overwrite value
  `(i_X vol)(update (E'∘ŝᵢ) j E'ᵢ) = -(-1)^i g(X, E'_{ŝᵢ(j)})`
  (permutation `(cycleRange i)⁻¹ ∘ swap 0 (j+1)`, sign `-(-1)^i`);
* `interiorVolume_frame_bracket_minor` — the **signed 2×2 minor**
  `(i_X vol)(update (E'∘ŝᵢ) j W)
     = (-1)^i (g(W,E'_{ŝᵢ j}) g(X,E'ᵢ) − g(W,E'ᵢ) g(X,E'_{ŝᵢ j}))`.

The remark's target theorem `PetersenLib.lieDerivative_volume_exact` is **LANDED**
(this file, `section CartanAssembly`) in its frame instance: under the standing
normalized-orthonormal-frame hypotheses of `VolumeDivergence.lean` (I-0089),
`(L_X vol)(E)(x) = d(i_X vol)(E')(x)` with `E' = E ∘ finCongr hn.symm`, both
sides equal to `div X`.  It requires **no** Stokes/integration (those enter only
the downstream `adjoint_L2_identity`, Prop. 2.2.8).  The proof is Cartan step 1
(`exteriorDerivative_interiorVolume_frame`) plus `divergenceLieDerivative_eq_frame`:

1. **Frame matching — `exteriorDerivative_interiorVolume_frame`** (LANDED):
   `d(i_X vol)(E')(x) = div X(x)`.  Expanding `exteriorDerivative_lieFormula` +
   `lieDerivativeTensor_formula`, using `interiorVolume_frame_succAbove` for the
   `D`-terms and `interiorVolume_frame_bracket_minor` for the corrections
   (`exteriorDerivative_interiorVolume_frame_expand`), gives
   `(‡)  d(i_X vol)(E')(x) = Σᵢ D_{E'ᵢ}(g(X,E'ᵢ)) − ½ S₁ + ½ S₂`.  Independently,
   expand `div X` by Leibniz (`divergenceLieDerivative_frame_leibniz`) to
   `(◇)  div X = Σᵢ D_{E'ᵢ}(g(X,E'ᵢ)) + S₂`.  The `D`-terms match and the double
   bracket sums satisfy `S₂ = −S₁` by the swap `i ↔ u`, `[E'ᵢ,E'ᵤ] = −[E'ᵤ,E'ᵢ]`.

2. **Full tensorial generality (OPEN — the natural strengthening).** The
   unrestricted `d(i_X vol)(Y)(x) = div X(x) · vol(Y')(x)` for arbitrary smooth
   `Y : Fin (m+1) → fields` follows from step 1 by the `1`-dimensionality of
   top-degree forms, i.e. the tensoriality (combination lemma)
   `d(i_X vol)(Σⱼ cᵢⱼ Eⱼ)(x) = det(c(x)) · d(i_X vol)(E')(x)` — the
   exterior-derivative analogue of `lieDerivativeTensor_volumeOperator_combination`
   (both direction and removed tuple vary), via the Cramer/Jacobi helpers
   `sum_mul_det_updateRow`, `directionalDerivative_det_coeff`.  Not yet formalized;
   the frame instance above is the faithful rendering forced by I-0089 (the
   volume operator is not globally a tensor), consistent with the frame-restricted
   statement of `divergence_trace_formula`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.3, page 67.
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace Matrix

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [hm : HasMetric I M]

variable (I) in
/-- **Math.** The **interior product of the volume form** with a vector field
`X`: the `(0, m)`-tensor `(i_X vol)(Z₁, …, Z_m) = vol(X, Z₁, …, Z_m)`, where
`m + 1 = finrank ℝ E`.  This is `interiorProduct I (volumeOperator o) X` up to
the arity reindexing `finCongr hn`. -/
def interiorVolume
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q) {m : ℕ} (hn : finrank ℝ E = m + 1) :
    TensorOperator I M m :=
  fun Z => volumeOperator o
    (fun i => (Fin.cons X Z : Fin (m + 1) → Π q : M, TangentSpace I q) (finCongr hn i))

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [NeZero (finrank ℝ E)] in
theorem interiorVolume_apply
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (X : Π q : M, TangentSpace I q) {m : ℕ} (hn : finrank ℝ E = m + 1)
    (Z : Fin m → Π q : M, TangentSpace I q) (x : M) :
    interiorVolume I o X hn Z x
      = volumeOperator o
        (fun i => (Fin.cons X Z : Fin (m + 1) → Π q : M, TangentSpace I q)
          (finCongr hn i)) x := rfl

/-- **Math.** Laplace-type sign identity for an alternating `n+1`-form: moving
the `i`-th argument to the front costs the sign `(-1)^i`,
`f(vᵢ, v₀, …, v̂ᵢ, …, v_n) = (-1)^i · f(v₀, …, v_n)`.  (The reindexing of the
front-insertion permutation `Fin.cons (v i) (v ∘ i.succAbove) = v ∘ (cycleRange
i)⁻¹` has sign `(-1)^i` by `Fin.sign_cycleRange`.)  This is the alternation
input to the frame computation of `L_X vol = d(i_X vol)`. -/
theorem alternating_cons_succAbove_real {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (f : V [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (v : Fin (n + 1) → V) (i : Fin (n + 1)) :
    f (Fin.cons (v i) (fun j => v (i.succAbove j))) = (-1 : ℝ) ^ (i : ℕ) * f v := by
  have hcons : (Fin.cons (v i) (fun j => v (i.succAbove j)) : Fin (n + 1) → V)
      = v ∘ (i.cycleRange).symm := by
    funext k
    refine Fin.cases ?_ ?_ k
    · simp only [Fin.cons_zero, Function.comp_apply]
      rw [show (i.cycleRange).symm 0 = i from
        (Equiv.symm_apply_eq _).2 (Fin.cycleRange_self i).symm]
    · intro j
      simp only [Fin.cons_succ, Function.comp_apply]
      rw [show (i.cycleRange).symm j.succ = i.succAbove j from
        (Equiv.symm_apply_eq _).2 (Fin.cycleRange_succAbove i j).symm]
  rw [hcons, f.map_perm, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Units.smul_def,
    zsmul_eq_mul]
  push_cast
  ring

/-! ## Evaluating `interiorVolume` through the arity-`(m+1)` volume form

`interiorVolume` is defined at arity `finrank ℝ E`; the exterior derivative acts
at arity `m + 1`.  The bridge is the reindexed alternating form
`(volumeForm rfl o x).domDomCongr (finCongr hn)`, a genuine
`(0, m+1)`-alternating form on `T_xM`, on which `Fin.cons`/`Fin.succAbove`
calculus (the Laplace sign `alternating_cons_succAbove_real`) applies natively. -/

section CartanBridge

variable {X : Π q : M, TangentSpace I q}
  {o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E))}
  {m : ℕ} (hn : finrank ℝ E = m + 1)

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [NeZero (finrank ℝ E)] in
/-- **Eng.** `interiorVolume` evaluated at `x` is the reindexed alternating form
`(volumeForm rfl o x).domDomCongr (finCongr hn)` applied to the `(m+1)`-tuple
`Fin.cons (X x) (Z · x)`.  Pure unfolding plus the pointwise commutation of
`Fin.cons` with evaluation at `x`. -/
theorem interiorVolume_eq_domDomCongr
    (Z : Fin m → Π q : M, TangentSpace I q) (x : M) :
    interiorVolume I o X hn Z x
      = (volumeForm rfl o x).domDomCongr (finCongr hn)
          (Fin.cons (X x) (fun j => Z j x)) := by
  rw [interiorVolume_apply, volumeOperator_apply,
    AlternatingMap.domDomCongr_apply]
  congr 1
  funext i
  simp only [Function.comp_apply]
  generalize finCongr hn i = l
  refine Fin.cases ?_ ?_ l
  · simp
  · intro j; simp

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
/-- **Math.** The **interior product on the frame with slot `i` removed** (Petersen
§2.1.3, the closed form entering `L_X vol = d i_X vol`): for a positively
oriented orthonormal frame `E₁, …, E_n` normalized to `vol = 1` near `x`,
`(i_X vol)(E_{≠i}) = (-1)^i · g(X, E_i)` on a neighborhood of `x`, where `E_{≠i}`
is the `(m)`-tuple obtained by deleting the `i`-th frame field.  Proved by
expanding `X` in the frame, killing all but the `i`-th term by alternation, and
applying the Laplace sign `alternating_cons_succAbove_real`. -/
theorem interiorVolume_frame_succAbove
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) (i : Fin (m + 1)) :
    interiorVolume I o X hn (fun j => Efr (finCongr hn.symm (i.succAbove j)))
      =ᶠ[𝓝 x] fun q => (-1) ^ (i : ℕ)
          * hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q) := by
  classical
  filter_upwards [hU] with q hq
  set v : Fin (m + 1) → TangentSpace I q := fun l => Efr (finCongr hn.symm l) q with hv
  -- reindexing identity `v (finCongr hn k) = Efr k q`
  have hvk : ∀ k : Fin (finrank ℝ E), v (finCongr hn k) = Efr k q := by
    intro k
    simp only [hv, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  -- rewrite the tuple `Efr ∘ finCongr hn.symm ∘ succAbove i` as `v ∘ succAbove i`
  have hVeq : (fun j => Efr (finCongr hn.symm (i.succAbove j)) q)
      = fun j => v (i.succAbove j) := by funext j; rw [hv]
  rw [interiorVolume_eq_domDomCongr, hVeq]
  set A : (TangentSpace I q) [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ :=
    (volumeForm rfl o q).domDomCongr (finCongr hn) with hA
  -- `A` on the full reindexed frame is the normalization `vol(Efr) = 1`
  have hAfull : A (fun l => v l) = 1 := by
    rw [hA, AlternatingMap.domDomCongr_apply]
    have hcomp : (fun l => v l) ∘ (finCongr hn) = fun k => Efr k q := by
      funext k; exact hvk k
    rw [hcomp]; exact hvol q hq
  -- expand `X q` in the reindexed frame `v`
  have hXexp : X q = ∑ l, hm.metric.metricInner q (X q) (v l) • v l := by
    rw [← Equiv.sum_comp (finCongr hn)
      (fun l => hm.metric.metricInner q (X q) (v l) • v l)]
    simp only [hvk]
    exact metricInner_orthonormal_expansion (horth q hq) (X q)
  -- each `A (cons (v l) (v ∘ succAbove i))` is `(-1)^i` if `l = i`, else `0`
  have hterm : ∀ l : Fin (m + 1),
      A (Fin.cons (v l) (fun j => v (i.succAbove j)))
      = if l = i then (-1) ^ (i : ℕ) else 0 := by
    intro l
    rcases eq_or_ne l i with rfl | hli
    · rw [if_pos rfl, alternating_cons_succAbove_real A v l, hAfull, mul_one]
    · rw [if_neg hli]
      obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hli
      refine A.map_eq_zero_of_eq _ (i := 0) (j := j₀.succ) ?_ (Fin.succ_ne_zero j₀).symm
      simp only [Fin.cons_zero, Fin.cons_succ, hj₀]
  -- assemble by multilinearity of `A` in slot `0`
  have hlin : ∀ w : TangentSpace I q, A (Fin.cons w (fun j => v (i.succAbove j)))
      = A.toMultilinearMap.toLinearMap (Fin.cons 0 (fun j => v (i.succAbove j))) 0 w := by
    intro w
    rw [MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]
    rfl
  calc A (Fin.cons (X q) (fun j => v (i.succAbove j)))
      = A.toMultilinearMap.toLinearMap (Fin.cons 0 (fun j => v (i.succAbove j))) 0 (X q) :=
        hlin (X q)
    _ = ∑ l, hm.metric.metricInner q (X q) (v l)
          * A (Fin.cons (v l) (fun j => v (i.succAbove j))) := by
        conv_lhs => rw [hXexp, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_smul, ← hlin (v l), smul_eq_mul]
    _ = ∑ l, hm.metric.metricInner q (X q) (v l)
          * (if l = i then (-1) ^ (i : ℕ) else 0) := by
        refine Finset.sum_congr rfl fun l _ => ?_; rw [hterm l]
    _ = (-1) ^ (i : ℕ) * hm.metric.metricInner q (X q) (v i) := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ i, Finset.mem_univ,
          if_true]
        ring
    _ = (-1) ^ (i : ℕ) * hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q) := by
        rw [hv]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
/-- **Math.** `interiorVolume` on a **permuted co-frame** (the general form of
`interiorVolume_frame_succAbove`): for a positively oriented orthonormal frame
`E₁, …, E_n` normalized to `vol = 1` near `x` and any permutation `σ` of
`Fin (m+1)`, deleting the index `σ 0` and listing the remaining frame vectors in
the order `σ ∘ succ` gives
`(i_X vol)(E'_{σ(1)}, …, E'_{σ(m)}) = sign(σ) · g(X, E'_{σ 0})` on a
neighborhood of `x`.  Specializing `σ` to the front-insertion cycle at `i`
recovers `interiorVolume_frame_succAbove` with sign `(-1)^i`; the two-index
bracket corrections of `L_X vol = d i_X vol` come from other choices of `σ`. -/
theorem interiorVolume_frame_perm
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) (σ : Equiv.Perm (Fin (m + 1))) :
    interiorVolume I o X hn (fun j => Efr (finCongr hn.symm (σ j.succ)))
      =ᶠ[𝓝 x] fun q => ((Equiv.Perm.sign σ : ℤ) : ℝ)
          * hm.metric.metricInner q (X q) (Efr (finCongr hn.symm (σ 0)) q) := by
  classical
  filter_upwards [hU] with q hq
  set v : Fin (m + 1) → TangentSpace I q := fun l => Efr (finCongr hn.symm l) q with hv
  have hvk : ∀ k : Fin (finrank ℝ E), v (finCongr hn k) = Efr k q := by
    intro k
    simp only [hv, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  have hVeq : (fun j : Fin m => Efr (finCongr hn.symm (σ j.succ)) q)
      = fun j : Fin m => v (σ j.succ) := by funext j; rw [hv]
  rw [interiorVolume_eq_domDomCongr, hVeq]
  set A : (TangentSpace I q) [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ :=
    (volumeForm rfl o q).domDomCongr (finCongr hn) with hA
  have hAfull : A (fun l => v l) = 1 := by
    rw [hA, AlternatingMap.domDomCongr_apply]
    have hcomp : (fun l => v l) ∘ (finCongr hn) = fun k => Efr k q := by
      funext k; exact hvk k
    rw [hcomp]; exact hvol q hq
  have hXexp : X q = ∑ l, hm.metric.metricInner q (X q) (v l) • v l := by
    rw [← Equiv.sum_comp (finCongr hn)
      (fun l => hm.metric.metricInner q (X q) (v l) • v l)]
    simp only [hvk]
    exact metricInner_orthonormal_expansion (horth q hq) (X q)
  have hterm : ∀ l : Fin (m + 1),
      A (Fin.cons (v l) (fun j => v (σ j.succ)))
      = if l = σ 0 then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0 := by
    intro l
    rcases eq_or_ne l (σ 0) with rfl | hl
    · rw [if_pos rfl]
      have hcons : (Fin.cons (v (σ 0)) (fun j => v (σ j.succ)) :
          Fin (m + 1) → TangentSpace I q) = v ∘ σ := by
        funext k
        refine Fin.cases ?_ ?_ k <;> simp
      rw [hcons, A.map_perm, hAfull, Units.smul_def, zsmul_eq_mul, mul_one]
    · rw [if_neg hl]
      have hsymm : σ.symm l ≠ 0 := by
        intro h
        exact hl (by rw [← σ.apply_symm_apply l, h])
      obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr hsymm
      refine A.map_eq_zero_of_eq _ (i := 0) (j := k.succ) ?_ (Fin.succ_ne_zero k).symm
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hk, σ.apply_symm_apply]
  have hlin : ∀ w : TangentSpace I q, A (Fin.cons w (fun j => v (σ j.succ)))
      = A.toMultilinearMap.toLinearMap (Fin.cons 0 (fun j => v (σ j.succ))) 0 w := by
    intro w
    rw [MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]
    rfl
  calc A (Fin.cons (X q) (fun j => v (σ j.succ)))
      = A.toMultilinearMap.toLinearMap (Fin.cons 0 (fun j => v (σ j.succ))) 0 (X q) :=
        hlin (X q)
    _ = ∑ l, hm.metric.metricInner q (X q) (v l)
          * A (Fin.cons (v l) (fun j => v (σ j.succ))) := by
        conv_lhs => rw [hXexp, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_smul, ← hlin (v l), smul_eq_mul]
    _ = ∑ l, hm.metric.metricInner q (X q) (v l)
          * (if l = σ 0 then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun l _ => ?_; rw [hterm l]
    _ = ((Equiv.Perm.sign σ : ℤ) : ℝ) * hm.metric.metricInner q (X q) (v (σ 0)) := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ (σ 0), Finset.mem_univ,
          if_true]
        ring
    _ = ((Equiv.Perm.sign σ : ℤ) : ℝ)
          * hm.metric.metricInner q (X q) (Efr (finCongr hn.symm (σ 0)) q) := by
        rw [hv]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
/-- **Math.** The interior product on the co-frame `E'∘ŝ_i` with slot `j`
overwritten by the *deleted* vector `E'_i`.  The two tuples
`(E'_{ŝ_i(0)}, …, E'_i \text{ at slot } j, …)` and the front-inserted
`(E'_i, E'∘ŝ_i)` differ by the transposition `swap 0 (j+1)`, so the underlying
permutation is `(cycleRange i)⁻¹ ∘ swap 0 (j+1)` with sign `(-1)^i·(-1)`, giving
`(i_X vol)(update (E'∘ŝ_i) j E'_i) = -(-1)^i · g(X, E'_{ŝ_i(j)})` on a
neighborhood of `x`.  This is the second (non-trivial) surviving frame value
entering the bracket corrections of `L_X vol = d i_X vol`. -/
theorem interiorVolume_frame_update_self
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) (i : Fin (m + 1)) (j : Fin m) :
    interiorVolume I o X hn
        (Function.update (fun j' => Efr (finCongr hn.symm (i.succAbove j'))) j
          (Efr (finCongr hn.symm i)))
      =ᶠ[𝓝 x] fun q => -(-1) ^ (i : ℕ)
          * hm.metric.metricInner q (X q) (Efr (finCongr hn.symm (i.succAbove j)) q) := by
  classical
  set σ : Equiv.Perm (Fin (m + 1)) := (i.cycleRange).symm * Equiv.swap 0 j.succ with hσ
  have hs0 : (i.cycleRange).symm 0 = i :=
    (Equiv.symm_apply_eq _).2 (Fin.cycleRange_self i).symm
  have hsucc : ∀ k : Fin m, (i.cycleRange).symm k.succ = i.succAbove k :=
    fun k => (Equiv.symm_apply_eq _).2 (Fin.cycleRange_succAbove i k).symm
  -- `σ 0 = i.succAbove j`
  have hσ0 : σ 0 = i.succAbove j := by
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hsucc j]
  -- the reindexed co-frame is the updated tuple
  have htuple : (fun j' : Fin m => Efr (finCongr hn.symm (σ j'.succ)))
      = Function.update (fun j' => Efr (finCongr hn.symm (i.succAbove j'))) j
          (Efr (finCongr hn.symm i)) := by
    funext j'
    rcases eq_or_ne j' j with rfl | hj'
    · rw [Function.update_self]
      have hσj : σ j'.succ = i := by
        rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, hs0]
      rw [hσj]
    · rw [Function.update_of_ne hj']
      have hσj : σ j'.succ = i.succAbove j' := by
        rw [hσ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j')
            ((Fin.succ_injective _).ne hj'), hsucc j']
      rw [hσj]
  -- the sign is `-(-1)^i`
  have hsign : ((Equiv.Perm.sign σ : ℤ) : ℝ) = -(-1) ^ (i : ℕ) := by
    rw [hσ, map_mul, Equiv.Perm.sign_swap (Ne.symm (Fin.succ_ne_zero j)),
      Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    push_cast
    ring
  have hperm := interiorVolume_frame_perm (X := X) (o := o) hn hU horth hvol σ
  rw [htuple] at hperm
  rw [hσ0] at hperm
  refine hperm.trans ?_
  filter_upwards with q
  rw [hsign]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
/-- **Math.** The **signed 2×2 minor** giving a single bracket correction of
`L_X vol = d i_X vol`.  Overwriting slot `j` of the co-frame `E'∘ŝ_i` with an
arbitrary field `W`, only the deleted direction `E'_i` and the overwritten
direction `E'_{ŝ_i(j)}` survive (all other frame directions repeat, killing the
top form), giving at `x`
`(i_X vol)(update (E'∘ŝ_i) j W)
   = (-1)^i (g(W, E'_{ŝ_i(j)}) g(X, E'_i) − g(W, E'_i) g(X, E'_{ŝ_i(j)}))`.
The two surviving coefficients are `interiorVolume_frame_succAbove` and
`interiorVolume_frame_update_self`. -/
theorem interiorVolume_frame_bracket_minor
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) (i : Fin (m + 1)) (j : Fin m)
    (W : Π q : M, TangentSpace I q) :
    interiorVolume I o X hn
        (Function.update (fun j' => Efr (finCongr hn.symm (i.succAbove j'))) j W) x
      = (-1) ^ (i : ℕ)
          * (hm.metric.metricInner x (W x) (Efr (finCongr hn.symm (i.succAbove j)) x)
                * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm i) x)
            - hm.metric.metricInner x (W x) (Efr (finCongr hn.symm i) x)
                * hm.metric.metricInner x (X x)
                    (Efr (finCongr hn.symm (i.succAbove j)) x)) := by
  classical
  have hxU : x ∈ U := mem_of_mem_nhds hU
  set v : Fin (m + 1) → TangentSpace I x := fun l => Efr (finCongr hn.symm l) x with hv
  have hvk : ∀ k : Fin (finrank ℝ E), v (finCongr hn k) = Efr k x := by
    intro k
    simp only [hv, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  set A : (TangentSpace I x) [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ :=
    (volumeForm rfl o x).domDomCongr (finCongr hn) with hA
  set base : Fin (m + 1) → TangentSpace I x :=
    Fin.cons (X x) (fun j' => v (i.succAbove j')) with hbaseDef
  -- `interiorVolume(update coframe j V) x = A(update base (j+1) (V x))`
  have hconv : ∀ V : Π q : M, TangentSpace I q,
      interiorVolume I o X hn
          (Function.update (fun j' => Efr (finCongr hn.symm (i.succAbove j'))) j V) x
        = A (Function.update base j.succ (V x)) := by
    intro V
    rw [interiorVolume_eq_domDomCongr, ← hA, hbaseDef, ← Fin.cons_update]
    congr 2
    rw [eval_update]
  -- the deleted-index frame value `A base = (-1)^i g(X, E'_i)`
  have hbase : A base = (-1) ^ (i : ℕ) * hm.metric.metricInner x (X x) (v i) := by
    have h := (interiorVolume_frame_succAbove (X := X) (o := o) hn hU horth hvol i).self_of_nhds
    rw [interiorVolume_eq_domDomCongr, ← hA] at h
    rw [hbaseDef]
    exact h
  -- expand `W x` in the frame
  have hWexp : W x = ∑ l, hm.metric.metricInner x (W x) (v l) • v l := by
    rw [← Equiv.sum_comp (finCongr hn)
      (fun l => hm.metric.metricInner x (W x) (v l) • v l)]
    simp only [hvk]
    exact metricInner_orthonormal_expansion (horth x hxU) (W x)
  -- the single-frame values at every index
  have hterm : ∀ a : Fin (m + 1), A (Function.update base j.succ (v a))
      = (if a = i.succAbove j then (-1) ^ (i : ℕ) * hm.metric.metricInner x (X x) (v i)
         else if a = i then -(-1) ^ (i : ℕ)
             * hm.metric.metricInner x (X x) (v (i.succAbove j)) else 0) := by
    intro a
    by_cases h1 : a = i.succAbove j
    · subst h1
      rw [if_pos rfl]
      have hbe : base j.succ = v (i.succAbove j) := by rw [hbaseDef, Fin.cons_succ]
      rw [← hbe, Function.update_eq_self, hbase]
    · rw [if_neg h1]
      by_cases h2 : a = i
      · rw [if_pos h2, h2]
        have hself :=
          (interiorVolume_frame_update_self (X := X) (o := o) hn hU horth hvol i j).self_of_nhds
        rw [hconv (Efr (finCongr hn.symm i))] at hself
        exact hself
      · rw [if_neg h2]
        obtain ⟨j'', hj''⟩ := Fin.exists_succAbove_eq h2
        have hjj : j'' ≠ j := fun h => h1 (by rw [← hj'', h])
        refine A.map_eq_zero_of_eq _ (i := j.succ) (j := j''.succ) ?_
          ((Fin.succ_injective m).ne (Ne.symm hjj))
        rw [Function.update_self,
          Function.update_of_ne ((Fin.succ_injective m).ne hjj), hbaseDef,
          Fin.cons_succ, hj'']
  -- assemble by multilinearity of `A` in slot `j+1`
  rw [hconv W]
  conv_lhs => rw [hWexp]
  have hexpand : A (Function.update base j.succ
        (∑ l, hm.metric.metricInner x (W x) (v l) • v l))
      = ∑ l, hm.metric.metricInner x (W x) (v l) * A (Function.update base j.succ (v l)) := by
    have hsum := A.toMultilinearMap.map_update_sum Finset.univ j.succ
      (fun l => hm.metric.metricInner x (W x) (v l) • v l) base
    rw [AlternatingMap.coe_multilinearMap] at hsum
    rw [hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [A.map_update_smul base j.succ, smul_eq_mul]
  rw [hexpand]
  rw [← Finset.sum_subset (Finset.subset_univ ({i.succAbove j, i} : Finset (Fin (m + 1))))
    (fun l _ hl => by
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      rw [hterm l, if_neg hl.1, if_neg hl.2, mul_zero])]
  rw [Finset.sum_pair (Fin.succAbove_ne i j)]
  rw [hterm (i.succAbove j), hterm i, if_pos rfl,
    if_neg (Ne.symm (Fin.succAbove_ne i j)), if_pos rfl]
  simp only [hv]
  ring

end CartanBridge

/-! ## Step 1 — matching `d(i_X vol)` and `div X` on the frame

The two inputs to the Cartan identity `L_X vol = d(i_X vol)` on a normalized
orthonormal frame.  Writing `E'_k = E_{finCongr hn.symm k}` for the frame
reindexed to arity `m + 1` and `c_p = g(X, E'_p)`:

* the **divergence** side (`divergenceLieDerivative_frame_leibniz`): expand
  `X = Σ_p c_p E'_p` near `x` and the bracket `[E'_k, X]` by Leibniz to
  `div X = Σ_k D_{E'_k}(c_k) + Σ_k Σ_p c_p · g([E'_k, E'_p], E'_k)`  `(◇)`;
* the **exterior-derivative** side (`exteriorDerivative_interiorVolume_frame`):
  expand `d(i_X vol)(E')` through the frame-value toolkit
  (`interiorVolume_frame_succAbove`, `interiorVolume_frame_bracket_minor`) to
  `Σ_i D_{E'_i}(c_i) − Σ_i Σ_u g([E'_i, E'_u], E'_u) · c_i`  `(‡)`.

The two double sums are negatives of each other under the swap `i ↔ u` and the
bracket antisymmetry `[E'_i, E'_u] = −[E'_u, E'_i]`, giving
`d(i_X vol)(E') = div X` on the frame. -/

section CartanAssembly

variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `interiorVolume` on a tuple of frame combinations is a
determinant.  For a positively oriented orthonormal frame `E₁, …, E_n`
normalized to `vol = 1` near `x` (`E'_p = E_{finCongr hn.symm p}`), if the tuple
`Z` expands at a point `q` near `x` as `Z_j(q) = Σ_p d_{jp} E'_p(q)`, then
`(i_X vol)(Z)(q) = det B`, where `B` is the `(m+1) × (m+1)` matrix whose `0`-th
row is `p ↦ g(X, E'_p)(q)` and whose `(j+1)`-st row is `d_j`.  (Expand `X` and
each `Z_j` in the reindexed orthonormal basis and apply the determinant formula
`alternatingMap_apply_sum_smul` for a top alternating form.)  This is the
exterior-derivative analogue of `volumeOperator_apply_of_expansion`, the input to
the determinant Leibniz rule for `d(i_X vol)`. -/
theorem interiorVolume_comb
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {X : Π q : M, TangentSpace I q}
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    {U : Set M}
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {m : ℕ} (hn : finrank ℝ E = m + 1)
    (d : Fin m → Fin (m + 1) → ℝ) {q : M} (hq : q ∈ U)
    (Z : Fin m → Π q : M, TangentSpace I q)
    (hZ : ∀ j, Z j q = ∑ p, d j p • Efr (finCongr hn.symm p) q) :
    interiorVolume I o X hn Z q
      = (Matrix.of (Fin.cons
          (fun p => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm p) q))
          d)).det := by
  classical
  set v : Fin (m + 1) → TangentSpace I q := fun l => Efr (finCongr hn.symm l) q with hv
  have hvk : ∀ k : Fin (finrank ℝ E), v (finCongr hn k) = Efr k q := by
    intro k
    simp only [hv, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  -- the reindexed orthonormal basis, indexed by `Fin (m + 1)`
  set b' : Basis (Fin (m + 1)) ℝ (TangentSpace I q) :=
    (basisOfMetricOrthonormal (horth q hq)).reindex (finCongr hn) with hb'
  have hb'p : ∀ p, b' p = v p := by
    intro p
    rw [hb', Basis.reindex_apply, basisOfMetricOrthonormal_apply, hv]
    simp only [finCongr_symm, finCongr_apply]
  -- expand `X q` in the reindexed orthonormal basis
  have hXexp : X q = ∑ p, hm.metric.metricInner q (X q) (v p) • v p := by
    rw [← Equiv.sum_comp (finCongr hn)
      (fun p => hm.metric.metricInner q (X q) (v p) • v p)]
    simp only [hvk]
    exact metricInner_orthonormal_expansion (horth q hq) (X q)
  rw [interiorVolume_eq_domDomCongr]
  set A : (TangentSpace I q) [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ :=
    (volumeForm rfl o q).domDomCongr (finCongr hn) with hA
  -- the `(m+1)`-tuple `cons (X q) (Z · q)` is `Σ_p B · b'` with `B = cons (g(X,·)) d`
  set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
    Fin.cons (fun p => hm.metric.metricInner q (X q) (v p)) d with hB
  have htuple : (Fin.cons (X q) (fun j => Z j q) : Fin (m + 1) → TangentSpace I q)
      = fun k => ∑ p, B k p • b' p := by
    funext k
    refine Fin.cases ?_ ?_ k
    · simp only [Fin.cons_zero, hB]
      conv_lhs => rw [hXexp]
      exact Finset.sum_congr rfl fun p _ => by rw [hb'p]
    · intro j
      simp only [Fin.cons_succ, hB]
      rw [hZ j]
      exact Finset.sum_congr rfl fun p _ => by rw [hb'p]
  rw [htuple, alternatingMap_apply_sum_smul A b' B]
  have hAb' : A ⇑b' = 1 := by
    rw [hA, AlternatingMap.domDomCongr_apply]
    have hcomp : (⇑b') ∘ (finCongr hn) = fun k => Efr k q := by
      funext k
      rw [Function.comp_apply, hb'p, hvk]
    rw [hcomp]
    exact hvol q hq
  rw [hAb', mul_one, hB]

/-- **Math.** Leibniz expansion of the divergence against a normalized
orthonormal frame `E₁, …, E_n` reindexed to arity `m + 1`.  With
`E'_k = E_{finCongr hn.symm k}`, expand `X = Σ_p g(X, E'_p) E'_p` near `x` and
the bracket `[E'_k, X]` by Leibniz to obtain the `(◇)` identity
`div X = Σ_k D_{E'_k}(g(X, E'_k)) + Σ_k Σ_p g(X, E'_p) · g([E'_k, E'_p], E'_k)`. -/
theorem divergenceLieDerivative_frame_leibniz
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {X : Π q : M, TangentSpace I q} (hX : IsSmoothVectorField X)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {m : ℕ} (hn : finrank ℝ E = m + 1) :
    divergenceLieDerivative o X x
      = (∑ k : Fin (m + 1), directionalDerivative (Efr (finCongr hn.symm k))
            (fun q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm k) q)) x)
        + ∑ k : Fin (m + 1), ∑ p : Fin (m + 1),
            hm.metric.metricInner x (X x) (Efr (finCongr hn.symm p) x)
              * hm.metric.metricInner x
                  (lieDerivativeVectorField I (Efr (finCongr hn.symm k))
                    (Efr (finCongr hn.symm p)) x)
                  (Efr (finCongr hn.symm k) x) := by
  classical
  have hxU : x ∈ U := mem_of_mem_nhds hU
  -- the smooth coefficients of `X` in the reindexed frame
  set c : Fin (m + 1) → M → ℝ :=
    fun p q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm p) q) with hcdef
  have hE'V : ∀ p, IsSmoothVectorField (Efr (finCongr hn.symm p)) :=
    fun p => hEs (finCongr hn.symm p)
  have hc : ∀ p, ContMDiff I 𝓘(ℝ) ∞ (c p) := by
    intro p
    have h := (metricOperator_isTensorOperator hm.metric).smooth_eval
      ![X, Efr (finCongr hn.symm p)] (fun k => by fin_cases k <;> [exact hX; exact hE'V p])
    have heq : metricOperator hm.metric ![X, Efr (finCongr hn.symm p)] = c p := by
      funext q; simp [metricOperator_apply, hcdef]
    rwa [heq] at h
  -- `X` agrees with its frame expansion near `x`
  have hXexp : X =ᶠ[𝓝 x] fun q => ∑ p, c p q • Efr (finCongr hn.symm p) q := by
    filter_upwards [hU] with q hq
    have hexp := metricInner_orthonormal_expansion (horth q hq) (X q)
    rw [hexp, ← Equiv.sum_comp (finCongr hn.symm)
      (fun a => hm.metric.metricInner q (X q) (Efr a q) • Efr a q)]
  -- the per-frame Leibniz identity
  have hkey : ∀ k : Fin (m + 1),
      hm.metric.metricInner x (lieDerivativeVectorField I (Efr (finCongr hn.symm k)) X x)
          (Efr (finCongr hn.symm k) x)
        = directionalDerivative (Efr (finCongr hn.symm k)) (c k) x
          + ∑ p, c p x * hm.metric.metricInner x
              (lieDerivativeVectorField I (Efr (finCongr hn.symm k))
                (Efr (finCongr hn.symm p)) x)
              (Efr (finCongr hn.symm k) x) := by
    intro k
    -- expand the bracket `[E'_k, X]` via Leibniz
    have hbr : lieDerivativeVectorField I (Efr (finCongr hn.symm k)) X x
        = ∑ p, (directionalDerivative (Efr (finCongr hn.symm k)) (c p) x
              • Efr (finCongr hn.symm p) x
            + c p x • lieDerivativeVectorField I (Efr (finCongr hn.symm k))
                (Efr (finCongr hn.symm p)) x) := by
      rw [show lieDerivativeVectorField I (Efr (finCongr hn.symm k)) X x
          = lieDerivativeVectorField I (Efr (finCongr hn.symm k))
              (fun q => ∑ p, c p q • Efr (finCongr hn.symm p) q) x from
        Filter.EventuallyEq.mlieBracket_vectorField_eq (Filter.EventuallyEq.refl _ _) hXexp,
        lieDerivativeVectorField_finset_sum_smul (Efr (finCongr hn.symm k)) hc hE'V x]
    -- pair with the metric and reduce by orthonormality
    have horthx : ∀ p k : Fin (m + 1),
        hm.metric.metricInner x (Efr (finCongr hn.symm p) x) (Efr (finCongr hn.symm k) x)
          = if p = k then 1 else 0 := by
      intro p k
      rw [horth x hxU]
      simp [Fin.ext_iff]
    rw [hbr, hasMetric_metricInner_eq_inner, sum_inner]
    rw [show (∑ p, @inner ℝ _ _
          (directionalDerivative (Efr (finCongr hn.symm k)) (c p) x
              • Efr (finCongr hn.symm p) x
            + c p x • lieDerivativeVectorField I (Efr (finCongr hn.symm k))
                (Efr (finCongr hn.symm p)) x)
          (Efr (finCongr hn.symm k) x))
        = ∑ p, (directionalDerivative (Efr (finCongr hn.symm k)) (c p) x
              * hm.metric.metricInner x (Efr (finCongr hn.symm p) x)
                  (Efr (finCongr hn.symm k) x)
            + c p x * hm.metric.metricInner x
                (lieDerivativeVectorField I (Efr (finCongr hn.symm k))
                  (Efr (finCongr hn.symm p)) x)
                (Efr (finCongr hn.symm k) x)) from by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        ← hasMetric_metricInner_eq_inner, ← hasMetric_metricInner_eq_inner]]
    simp_rw [horthx, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k]
    simp
  -- assemble: div = L_X vol on the frame, reindex, use hkey
  rw [divergenceLieDerivative_eq_frame o X hEs hU horth hvol,
    lieDerivativeTensor_volumeOperator_frame o X hU horth hvol,
    ← Equiv.sum_comp (finCongr hn.symm)
      (fun a => hm.metric.metricInner x (lieDerivativeVectorField I X (Efr a) x) (Efr a x))]
  rw [show (-∑ k : Fin (m + 1), hm.metric.metricInner x
        (lieDerivativeVectorField I X (Efr (finCongr hn.symm k)) x)
        (Efr (finCongr hn.symm k) x))
      = ∑ k : Fin (m + 1), hm.metric.metricInner x
          (lieDerivativeVectorField I (Efr (finCongr hn.symm k)) X x)
          (Efr (finCongr hn.symm k) x) from by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show lieDerivativeVectorField I X (Efr (finCongr hn.symm k)) x
        = -lieDerivativeVectorField I (Efr (finCongr hn.symm k)) X x from
      VectorField.mlieBracket_swap_apply, hm.metric.metricInner_neg_left, neg_neg]]
  rw [Finset.sum_congr rfl fun k _ => hkey k, Finset.sum_add_distrib]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Frame expansion of the exterior derivative `d(i_X vol)` on the
reindexed orthonormal frame `E'`.  Through the frame-value toolkit
(`interiorVolume_frame_succAbove` for the directional-derivative terms,
`interiorVolume_frame_bracket_minor` for the Lie-bracket corrections) and the
`(-1)^i·(-1)^i = 1` sign collapse, `d(i_X vol)(E')` is the `(‡)` identity
`Σ_i D_{E'_i}(g(X, E'_i)) − ½ Σ_i Σ_u g([E'_i, E'_u], E'_u)·g(X, E'_i)
   + ½ Σ_i Σ_u g([E'_i, E'_u], E'_i)·g(X, E'_u)`. -/
theorem exteriorDerivative_interiorVolume_frame_expand
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {X : Π q : M, TangentSpace I q} (hX : IsSmoothVectorField X)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {m : ℕ} (hn : finrank ℝ E = m + 1) :
    exteriorDerivative_lieFormula I (interiorVolume I o X hn)
        (fun k => Efr (finCongr hn.symm k)) x
      = (∑ i : Fin (m + 1), directionalDerivative (Efr (finCongr hn.symm i))
            (fun q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q)) x)
        - (1 / 2 : ℝ) * ∑ i : Fin (m + 1), ∑ u : Fin (m + 1),
            hm.metric.metricInner x
                (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
                  (Efr (finCongr hn.symm u)) x)
                (Efr (finCongr hn.symm u) x)
              * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm i) x)
        + (1 / 2 : ℝ) * ∑ i : Fin (m + 1), ∑ u : Fin (m + 1),
            hm.metric.metricInner x
                (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
                  (Efr (finCongr hn.symm u)) x)
                (Efr (finCongr hn.symm i) x)
              * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm u) x) := by
  classical
  -- the coefficient function `q ↦ g(X, E'_i)` is smooth (differentiable at `x`)
  have hgdiff : ∀ i : Fin (m + 1),
      MDifferentiableAt I 𝓘(ℝ) (fun q => hm.metric.metricInner q (X q)
        (Efr (finCongr hn.symm i) q)) x := by
    intro i
    have h := (metricOperator_isTensorOperator hm.metric).smooth_eval
      ![X, Efr (finCongr hn.symm i)]
      (fun k => by fin_cases k <;> [exact hX; exact hEs (finCongr hn.symm i)])
    have heq : metricOperator hm.metric ![X, Efr (finCongr hn.symm i)]
        = fun q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q) := by
      funext q; simp [metricOperator_apply]
    rw [heq] at h
    exact h.mdifferentiableAt (by norm_num)
  -- `(-1)^i · (-1)^i = 1`
  have hsq : ∀ i : Fin (m + 1), ((-1 : ℝ) ^ (i : ℕ)) * ((-1 : ℝ) ^ (i : ℕ)) = 1 := by
    intro i; rw [← pow_add]; exact Even.neg_one_pow ⟨(i : ℕ), rfl⟩
  -- the full-index minor value function; diagonal vanishes since `E'_u = E'_i`
  set mv : Fin (m + 1) → Fin (m + 1) → ℝ := fun i u =>
    hm.metric.metricInner x (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
        (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm u) x)
      * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm i) x)
    - hm.metric.metricInner x (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
        (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm i) x)
      * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm u) x) with hmv
  have hmv_diag : ∀ i, mv i i = 0 := fun i => by rw [hmv]; ring
  -- the per-summand identity for `∑ i, (-1)^i · (Lie term + directional term)`
  have hsummand : ∀ i : Fin (m + 1),
      (-1 : ℝ) ^ (i : ℕ) *
        (lieDerivativeTensor I (Efr (finCongr hn.symm i)) (interiorVolume I o X hn)
            (fun j => Efr (finCongr hn.symm (i.succAbove j))) x
          + directionalDerivative (Efr (finCongr hn.symm i))
              (interiorVolume I o X hn (fun j => Efr (finCongr hn.symm (i.succAbove j)))) x)
      = 2 * directionalDerivative (Efr (finCongr hn.symm i))
            (fun q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q)) x
        - ∑ j : Fin m, mv i (i.succAbove j) := by
    intro i
    -- the directional-derivative term collapses via `interiorVolume_frame_succAbove`
    have hsucc := interiorVolume_frame_succAbove (X := X) (o := o) hn hU horth hvol i
    have hDeq : directionalDerivative (Efr (finCongr hn.symm i))
          (interiorVolume I o X hn (fun j => Efr (finCongr hn.symm (i.succAbove j)))) x
        = (-1 : ℝ) ^ (i : ℕ) * directionalDerivative (Efr (finCongr hn.symm i))
            (fun q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q)) x := by
      rw [← directionalDerivative_const_smul (hgdiff i) ((-1 : ℝ) ^ (i : ℕ))
          (Efr (finCongr hn.symm i))]
      simp only [directionalDerivative_apply]
      rw [hsucc.mfderiv_eq]
      rfl
    -- expand the Lie term by `lieDerivativeTensor_formula`
    rw [lieDerivativeTensor_formula]
    -- each bracket correction is a signed 2×2 minor
    have hminor : ∀ j : Fin m,
        interiorVolume I o X hn (Function.update
            (fun j' => Efr (finCongr hn.symm (i.succAbove j'))) j
            (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
              (Efr (finCongr hn.symm (i.succAbove j))))) x
          = (-1 : ℝ) ^ (i : ℕ) * mv i (i.succAbove j) := by
      intro j
      rw [interiorVolume_frame_bracket_minor (X := X) (o := o) hn hU horth hvol i j
        (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
          (Efr (finCongr hn.symm (i.succAbove j)))), hmv]
    rw [hDeq, Finset.sum_congr rfl fun j _ => hminor j, ← Finset.mul_sum]
    have key : ∀ (s D N : ℝ), s * s = 1 → s * (s * D - s * N + s * D) = 2 * D - N := by
      intro s D N h
      have hsD : s * (s * D - s * N + s * D) = (s * s) * (2 * D - N) := by ring
      rw [hsD, h, one_mul]
    exact key ((-1 : ℝ) ^ (i : ℕ)) _ _ (hsq i)
  -- convert `∑ j, mv i (succAbove j)` to `∑ u, mv i u` (diagonal vanishes)
  have hconv : ∀ i : Fin (m + 1), ∑ j : Fin m, mv i (i.succAbove j) = ∑ u, mv i u := by
    intro i
    rw [Fin.sum_univ_succAbove (mv i) i, hmv_diag i, zero_add]
  -- split `∑ u, mv i u` into its two halves
  have hsplit : ∀ i : Fin (m + 1), (∑ u, mv i u)
      = (∑ u : Fin (m + 1), hm.metric.metricInner x
            (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
              (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm u) x)
          * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm i) x))
        - ∑ u : Fin (m + 1), hm.metric.metricInner x
            (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
              (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm i) x)
          * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm u) x) := by
    intro i; rw [hmv, Finset.sum_sub_distrib]
  -- assemble
  rw [exteriorDerivative_lieFormula_apply, Finset.sum_congr rfl fun i _ => hsummand i,
    Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ => hconv i,
    Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib,
    show (∑ i : Fin (m + 1), 2 * directionalDerivative (Efr (finCongr hn.symm i))
          (fun q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q)) x)
        = 2 * ∑ i : Fin (m + 1), directionalDerivative (Efr (finCongr hn.symm i))
          (fun q => hm.metric.metricInner q (X q) (Efr (finCongr hn.symm i) q)) x
      from (Finset.mul_sum _ _ _).symm]
  ring

/-- **Math.** **Step 1 — `d(i_X vol) = div X` on the frame.**  Combining the two
frame expansions `(◇)` and `(‡)` with the antisymmetrisation of the double
bracket sums (swap `i ↔ u`, `[E'_i, E'_u] = −[E'_u, E'_i]`) collapses the
Lie-bracket corrections and matches the directional-derivative terms:
`d(i_X vol)(E')(x) = div X(x)`.  This is the frame instance of Cartan's magic
formula `L_X vol = d(i_X vol)` for the top-degree volume form. -/
theorem exteriorDerivative_interiorVolume_frame
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {X : Π q : M, TangentSpace I q} (hX : IsSmoothVectorField X)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {m : ℕ} (hn : finrank ℝ E = m + 1) :
    exteriorDerivative_lieFormula I (interiorVolume I o X hn)
        (fun k => Efr (finCongr hn.symm k)) x
      = divergenceLieDerivative o X x := by
  rw [exteriorDerivative_interiorVolume_frame_expand o hX hEs hU horth hvol hn,
    divergenceLieDerivative_frame_leibniz o hX hEs hU horth hvol hn]
  -- antisymmetry: the two double bracket sums are negatives of each other
  have hswap : (∑ i : Fin (m + 1), ∑ u : Fin (m + 1), hm.metric.metricInner x
          (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
            (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm u) x)
        * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm i) x))
      = -(∑ i : Fin (m + 1), ∑ u : Fin (m + 1), hm.metric.metricInner x
          (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
            (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm i) x)
        * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm u) x)) := by
    have h1 : (∑ i : Fin (m + 1), ∑ u : Fin (m + 1), hm.metric.metricInner x
            (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
              (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm u) x)
          * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm i) x))
        = ∑ i : Fin (m + 1), ∑ u : Fin (m + 1), -(hm.metric.metricInner x
            (lieDerivativeVectorField I (Efr (finCongr hn.symm u))
              (Efr (finCongr hn.symm i)) x) (Efr (finCongr hn.symm u) x)
          * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm i) x)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
      rw [show lieDerivativeVectorField I (Efr (finCongr hn.symm i))
            (Efr (finCongr hn.symm u)) x
          = -lieDerivativeVectorField I (Efr (finCongr hn.symm u))
            (Efr (finCongr hn.symm i)) x from VectorField.mlieBracket_swap_apply,
        hm.metric.metricInner_neg_left]
      ring
    rw [h1]
    simp only [Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  -- commutativity: the divergence double sum equals the second bracket sum
  have hTS2 : (∑ k : Fin (m + 1), ∑ p : Fin (m + 1),
          hm.metric.metricInner x (X x) (Efr (finCongr hn.symm p) x)
        * hm.metric.metricInner x
            (lieDerivativeVectorField I (Efr (finCongr hn.symm k))
              (Efr (finCongr hn.symm p)) x) (Efr (finCongr hn.symm k) x))
      = ∑ i : Fin (m + 1), ∑ u : Fin (m + 1), hm.metric.metricInner x
            (lieDerivativeVectorField I (Efr (finCongr hn.symm i))
              (Efr (finCongr hn.symm u)) x) (Efr (finCongr hn.symm i) x)
        * hm.metric.metricInner x (X x) (Efr (finCongr hn.symm u) x) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  rw [hTS2]
  linarith [hswap]

/-- **Math.** **`rem:pet-ch2-lie-derivative-volume-exact`** (Petersen §2.1.3):
`L_X vol = d(i_X vol)`, Cartan's magic formula for the top-degree volume form.
Both sides are top-degree forms, hence multiples of `vol`; testing against a
positively oriented orthonormal frame `E₁, …, E_n` normalized to `vol = 1` near
`x` (the standing frame hypothesis forced by I-0089 — the pointwise orientation
datum obstructs a global tensor structure on `volumeOperator o`), both sides
equal `div X`:
`(L_X vol)(E₁, …, E_n)(x) = d(i_X vol)(E')(x)` where `E'` reindexes the frame to
arity `m + 1 = finrank ℝ E`.  The `L_X vol` side is `div X` by
`divergenceLieDerivative_eq_frame`; the `d(i_X vol)` side is `div X` by
`exteriorDerivative_interiorVolume_frame` (Cartan step 1).  The unrestricted
operator identity on arbitrary smooth tuples follows from this frame instance by
the `1`-dimensionality of top-degree alternating forms (the tensoriality of
`d(i_X vol)`, i.e. the exterior-derivative analogue of
`lieDerivativeTensor_volumeOperator_combination`). -/
theorem lieDerivative_volume_exact
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    {X : Π q : M, TangentSpace I q} (hX : IsSmoothVectorField X)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ a b, hm.metric.metricInner y (Efr a y) (Efr b y)
      = if a = b then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    {m : ℕ} (hn : finrank ℝ E = m + 1) :
    lieDerivativeTensor I X (volumeOperator o) Efr x
      = exteriorDerivative_lieFormula I (interiorVolume I o X hn)
          (fun k => Efr (finCongr hn.symm k)) x := by
  rw [exteriorDerivative_interiorVolume_frame o hX hEs hU horth hvol hn]
  exact (divergenceLieDerivative_eq_frame o X hEs hU horth hvol).symm

end CartanAssembly

end PetersenLib
