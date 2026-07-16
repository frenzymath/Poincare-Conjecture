import PetersenLib.Ch02.NormalCoordinates
import PetersenLib.Ch02.VolumeDivergence

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.19: existence of a normal frame

Petersen (§2.5, Exercise 2.5.19) asks: for `p ∈ (M, g)` and orthonormal
`e_1, …, e_n ∈ T_pM`, construct an orthonormal frame `E_1, …, E_n` near `p` with
`E_i(p) = e_i` and `(∇ E_i)|_p = 0` — a **normal frame** at `p`
(def:pet-ch2-normal-coordinates-frame, `isNormalFrameAt`).

**Construction (parallel gauge fix).**  Extend each `e_i` to a *smooth* vector
field `F_i` with `F_i(p) = e_i` (`exists_smoothVectorField_eq`).  Its covariant
derivative at `p`, `∇_v F_i`, need not vanish; we cancel it to first order by a
smooth linear-combination correction.  Set

    E_i := Σ_m c_{im} · F_m,   with c_{im} smooth, c_{im}(p) = δ_{im},
                               d c_{im}|_p (v) = − g(∇_v F_i, e_m).

By the finite Leibniz rule for the connection,

    ∇_v E_i|_p = Σ_m ( d c_{im}(v) · F_m(p) + c_{im}(p) · ∇_v F_m )
               = Σ_m (− g(∇_v F_i, e_m)) · e_m  +  ∇_v F_i
               = −∇_v F_i + ∇_v F_i = 0,

the middle equality using the orthonormal expansion
`w = Σ_m g(w, e_m) · e_m` (`metricInner_orthonormal_expansion`) applied to
`w = ∇_v F_i`, and `Σ_m δ_{im} ∇_v F_m = ∇_v F_i`.  Since `E_i(p) = e_i`, the
frame is orthonormal at `p`; the two clauses are exactly `isNormalFrameAt`.

The correction functions `c_{im}` are produced by a reusable **prescribed
1-jet** lemma `exists_contMDiff_prescribed_value_jet`: for any covector
`ξ ∈ T_p^*M` and value `val`, there is a global smooth `u : M → ℝ` with
`u(p) = val` and `du|_p = ξ`, built as `val` plus `ξ` composed with the chart
`extChartAt I p` (whose differential at `p` is the identity,
`mfderiv_extChartAt_self`), truncated to a global function by a smooth cutoff.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.19.
-/

open Bundle Set Function Finset Module Filter
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M] [hm : HasMetric I M]

/-! ## General connection utilities (local copies)

`∇_v 0 = 0`, finite additivity of smooth fields, and the finite Leibniz rule for
a linear combination — mirrors of the `private` helpers in
`ConnectionAlongCurve.lean`, reproved here so this file stays self-contained. -/

/-- `∇_v 0 = 0`. -/
private theorem cov_zeroField (D : AffineConnection I M) (p : M) (v : TangentSpace I p) :
    D.cov p v (fun q : M => (0 : TangentSpace I q)) = 0 := by
  have h0 : IsSmoothVectorField (fun q : M => (0 : TangentSpace I q)) := by
    simpa using (0 : SmoothVectorField I M).smooth
  have h := D.add_field p v h0 h0
  have e : (fun q : M => (0 : TangentSpace I q) + 0)
      = fun q : M => (0 : TangentSpace I q) := by funext q; simp
  rw [e] at h
  have h2 : D.cov p v (fun q : M => (0 : TangentSpace I q)) + 0
      = D.cov p v (fun q : M => (0 : TangentSpace I q))
        + D.cov p v (fun q : M => (0 : TangentSpace I q)) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- Finite sums of smooth vector fields are smooth. -/
private theorem isSmoothVF_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → Π x : M, TangentSpace I x) (hF : ∀ i, IsSmoothVectorField (F i)) :
    IsSmoothVectorField (fun q => ∑ i ∈ s, F i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (0 : SmoothVectorField I M).smooth
  | insert a s ha ih =>
      have h : IsSmoothVectorField (fun q => F a q + ∑ i ∈ s, F i q) := by
        simpa using ((⟨F a, hF a⟩ : SmoothVectorField I M)
          + ⟨fun q => ∑ i ∈ s, F i q, ih⟩).smooth
      have e : (fun q => ∑ i ∈ insert a s, F i q)
          = fun q => F a q + ∑ i ∈ s, F i q := by
        funext q; exact Finset.sum_insert ha
      rw [e]; exact h

/-- `∇_v (Σ_m f_m • V_m) = Σ_m (df_m(v) • V_m|_p + f_m(p) • ∇_v V_m)`. -/
private theorem cov_finsetSumSmul (D : AffineConnection I M)
    (p : M) (v : TangentSpace I p) {ι : Type*} (s : Finset ι)
    (f : ι → M → ℝ) (V : ι → Π x : M, TangentSpace I x)
    (hf : ∀ m, ContMDiff I 𝓘(ℝ) ∞ (f m)) (hV : ∀ m, IsSmoothVectorField (V m)) :
    D.cov p v (fun q => ∑ m ∈ s, f m q • V m q)
      = ∑ m ∈ s, (dirTangent (f m) v • V m p + f m p • D.cov p v (V m)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have e : (fun q => ∑ m ∈ (∅ : Finset ι), f m q • V m q)
          = fun q : M => (0 : TangentSpace I q) := by funext q; simp
      rw [e, cov_zeroField]; simp
  | insert a s ha ih =>
      have hterm : ∀ m, IsSmoothVectorField (fun q => f m q • V m q) := fun m => by
        simpa using (SmoothVectorField.smul (f m) (hf m) ⟨V m, hV m⟩).smooth
      have hsum : IsSmoothVectorField (fun q => ∑ m ∈ s, f m q • V m q) :=
        isSmoothVF_finsetSum s _ hterm
      have e : (fun q => ∑ m ∈ insert a s, f m q • V m q)
          = fun q => f a q • V a q + ∑ m ∈ s, f m q • V m q := by
        funext q; exact Finset.sum_insert ha
      rw [e, D.add_field p v (hterm a) hsum, D.leibniz p v (hf a) (hV a), ih,
        Finset.sum_insert ha]

/-- A function smooth on an open set agrees near any point of it with a globally
smooth function. -/
private theorem exists_contMDiff_eventuallyEq {f : M → ℝ} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f s) {x : M} (hx : x ∈ s) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ F ∧ F =ᶠ[nhds x] f := by
  classical
  obtain ⟨K, hK_nhds, hK_closed, hK_sub⟩ :=
    exists_mem_nhds_isClosed_subset (hs.mem_nhds hx)
  obtain ⟨K', hK'_nhds, hK'_closed, hK'_sub⟩ :=
    exists_mem_nhds_isClosed_subset
      (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hK_nhds))
  obtain ⟨lam, hlam0, hlam1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed I
      (isClosed_compl_iff.mpr isOpen_interior) hK'_closed
      (by rw [Set.disjoint_compl_left_iff_subset]; exact hK'_sub)
  refine ⟨fun q => if q ∈ s then (lam : M → ℝ) q * f q else 0, ?_, ?_⟩
  · intro q
    by_cases hq : q ∈ s
    · have hsmul : ContMDiffOn I 𝓘(ℝ) ∞ (fun q' => (lam : M → ℝ) q' * f q') s :=
        (lam.contMDiff.contMDiffOn).mul hf
      have hcongr : ContMDiffOn I 𝓘(ℝ) ∞
          (fun q' => if q' ∈ s then (lam : M → ℝ) q' * f q' else 0) s :=
        hsmul.congr fun q' hq' => if_pos hq'
      exact (hcongr q hq).contMDiffAt (hs.mem_nhds hq)
    · have hqK : q ∉ K := fun h => hq (hK_sub h)
      have hzero : ∀ q' ∈ (Kᶜ : Set M),
          (if q' ∈ s then (lam : M → ℝ) q' * f q' else 0) = 0 := by
        intro q' hq'
        by_cases hq's : q' ∈ s
        · rw [if_pos hq's]
          have hlamq' : (lam : M → ℝ) q' = 0 := by
            have hq'int : q' ∉ interior K := fun h => hq' (interior_subset h)
            simpa using hlam0 (Set.mem_compl hq'int)
          rw [hlamq', zero_mul]
        · rw [if_neg hq's]
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hK_closed.isOpen_compl.mem_nhds hqK) hzero)
  · filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hK'_nhds)]
      with q hq
    have hqK' : q ∈ K' := interior_subset hq
    have hqs : q ∈ s := hK_sub (interior_subset (hK'_sub hqK'))
    rw [if_pos hqs, show (lam : M → ℝ) q = 1 from by simpa using hlam1 hqK', one_mul]

/-! ## The prescribed 1-jet lemma -/

/-- **Math.** **Prescribed 1-jet.**  For any covector `ξ ∈ T_p^*M` (a continuous
linear functional on `T_pM = E`) and value `val ∈ ℝ`, there is a *globally
smooth* `u : M → ℝ` with `u(p) = val` and `du|_p = ξ`, i.e.
`dirTangent u v = ξ v` for every `v ∈ T_pM`.  Constructed from
`ξ ∘ (extChartAt I p)` (whose differential at `p` is `ξ`, since
`mfderiv (extChartAt I p) p = id`) plus the constant fixing the value, made
global by `exists_contMDiff_eventuallyEq`. -/
theorem exists_contMDiff_prescribed_value_jet (p : M) (ξ : E →L[ℝ] ℝ) (val : ℝ) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧ u p = val ∧
      ∀ v : TangentSpace I p, dirTangent u v = ξ v := by
  set b : ℝ := val - ξ (extChartAt I p p) with hb
  set u₀ : M → ℝ := fun y => ξ (extChartAt I p y) + b with hu₀
  -- `u₀` is smooth on the chart source
  have hsrc : (extChartAt I p).source ∈ nhds p := extChartAt_source_mem_nhds (I := I) p
  have hu₀on : ContMDiffOn I 𝓘(ℝ) ∞ u₀ (extChartAt I p).source := by
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p) (extChartAt I p).source := by
      rw [extChartAt_source]; exact contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)
    have hlin : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun w : E => ξ w + b) :=
      (ξ.contMDiff).add contMDiff_const
    exact hlin.comp_contMDiffOn hchart
  -- globalize
  obtain ⟨u, hu_smooth, hu_ev⟩ :=
    exists_contMDiff_eventuallyEq (I := I) (isOpen_extChartAt_source (I := I) p) hu₀on
      (mem_extChartAt_source (I := I) p)
  refine ⟨u, hu_smooth, ?_, ?_⟩
  · rw [hu_ev.self_of_nhds]
    show ξ (extChartAt I p p) + b = val
    rw [hb]; ring
  · intro v
    have hmfd : mfderiv I 𝓘(ℝ) u p = mfderiv I 𝓘(ℝ) u₀ p := hu_ev.mfderiv_eq
    show mfderiv I 𝓘(ℝ) u p v = ξ v
    rw [hmfd]
    -- differential of `u₀ = ξ ∘ extChartAt + const` at `p` is `ξ`
    have hφ : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) :=
      ((contMDiffAt_extChartAt (I := I) (x := p) (n := ∞)).mdifferentiableAt (by simp)).hasMFDerivAt
    have hk : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ) (fun w : E => ξ w + b) (extChartAt I p p) ξ :=
      (hasMFDerivAt_iff_hasFDerivAt).mpr (ξ.hasFDerivAt.add_const b)
    have hcomp : HasMFDerivAt I 𝓘(ℝ) u₀ p
        (ξ.comp (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p)) := hk.comp p hφ
    have hid : (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) v = v := by
      rw [mfderiv_extChartAt_self]; rfl
    rw [hcomp.mfderiv]
    show ξ ((mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) v) = ξ v
    rw [hid]

/-! ## The covariant-derivative covector -/

/-- **Math.** The linear functional `v ↦ g(∇_v X, w)` on `T_pM = E`, packaged as a
`LinearMap`; linear in `v` by tensoriality of the connection in the direction. -/
def covMetricLinear (p : M) (X : Π x : M, TangentSpace I x) (w : TangentSpace I p) :
    TangentSpace I p →ₗ[ℝ] ℝ where
  toFun v := hm.metric.metricInner p ((hm.metric.leviCivita).cov p v X) w
  map_add' v₁ v₂ := by
    show hm.metric.metricInner p ((hm.metric.leviCivita).cov p (v₁ + v₂) X) w
      = hm.metric.metricInner p ((hm.metric.leviCivita).cov p v₁ X) w
        + hm.metric.metricInner p ((hm.metric.leviCivita).cov p v₂ X) w
    rw [(hm.metric.leviCivita).add_direction, hm.metric.metricInner_add_left]
  map_smul' a v := by
    show hm.metric.metricInner p ((hm.metric.leviCivita).cov p (a • v) X) w
      = (RingHom.id ℝ) a * hm.metric.metricInner p ((hm.metric.leviCivita).cov p v X) w
    rw [(hm.metric.leviCivita).smul_direction, hm.metric.metricInner_smul_left,
      RingHom.id_apply]

@[simp] theorem covMetricLinear_apply (p : M) (X : Π x : M, TangentSpace I x)
    (w : TangentSpace I p) (v : TangentSpace I p) :
    covMetricLinear (I := I) p X w v
      = hm.metric.metricInner p ((hm.metric.leviCivita).cov p v X) w := rfl

/-! ## Exercise 2.5.19 -/

/-- **Math.** **Exercise 2.5.19 (existence of a normal frame).**  For `p ∈ (M, g)`
and a `g`-orthonormal tuple `e_1, …, e_n ∈ T_pM`, there is a smooth frame
`E_1, …, E_n` with `E_i(p) = e_i` that is **normal at `p`**
(`isNormalFrameAt hm.metric p E`): orthonormal at `p` and covariantly constant at
`p`, `(∇_v E_i)|_p = 0` for all `v`.

The frame is `E_i = Σ_m c_{im} F_m`, where `F_m` is a smooth extension of `e_m`
and the smooth coefficients `c_{im}` are chosen with prescribed 1-jet
`c_{im}(p) = δ_{im}`, `d c_{im}|_p(v) = − g(∇_v F_i, e_m)` to cancel the covariant
derivative of `F_i` to first order at `p`. -/
theorem exercise2_5_19 (p : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I p)
    (he : ∀ i j, hm.metric.metricInner p (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    ∃ E : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x,
      (∀ i, IsSmoothVectorField (E i)) ∧
      (∀ i, E i p = e i) ∧
      isNormalFrameAt hm.metric p E := by
  classical
  -- smooth extensions of the `e_i`
  choose Z hZ using fun i => exists_smoothVectorField_eq (I := I) p (e i)
  set F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x := fun i => ⇑(Z i) with hF
  have hFsmooth : ∀ i, IsSmoothVectorField (F i) := fun i => (Z i).smooth
  have hFval : ∀ i, F i p = e i := hZ
  -- correction covectors and their prescribed-jet functions
  set ξ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (TangentSpace I p →L[ℝ] ℝ) :=
    fun i m => -(covMetricLinear (I := I) p (F i) (e m)).toContinuousLinearMap with hξ
  have hjet : ∀ i m, ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      u p = (if i = m then (1 : ℝ) else 0) ∧
      ∀ v : TangentSpace I p, dirTangent u v = ξ i m v :=
    fun i m => exists_contMDiff_prescribed_value_jet (I := I) p (ξ i m) _
  choose c hc_smooth hc_val hc_dir using hjet
  refine ⟨fun i => fun x => ∑ m, c i m x • F m x, ?_, ?_, ?_⟩
  · -- smoothness
    intro i
    exact isSmoothVF_finsetSum Finset.univ _
      (fun m => by
        simpa using (SmoothVectorField.smul (c i m) (hc_smooth i m) ⟨F m, hFsmooth m⟩).smooth)
  · -- E i p = e i
    intro i
    dsimp only
    have hEval : ∀ i, (∑ m, c i m p • F m p) = e i := by
      intro i
      rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by
        rw [hc_val i m, hFval m, ite_smul, one_smul, zero_smul] :
        ∀ m ∈ Finset.univ, c i m p • F m p = if i = m then e m else 0)]
      simp
    exact hEval i
  · -- normal frame
    have hEval : ∀ i, (∑ m, c i m p • F m p) = e i := by
      intro i
      rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by
        rw [hc_val i m, hFval m, ite_smul, one_smul, zero_smul] :
        ∀ m ∈ Finset.univ, c i m p • F m p = if i = m then e m else 0)]
      simp
    constructor
    · -- orthonormal at p
      intro i j
      show hm.metric.metricInner p (∑ m, c i m p • F m p) (∑ m, c j m p • F m p)
        = if i = j then (1 : ℝ) else 0
      rw [hEval i, hEval j, he i j]
    · -- covariant derivative vanishes at p
      intro i v
      show (hm.metric.leviCivita).cov p v (fun x => ∑ m, c i m x • F m x) = 0
      rw [cov_finsetSumSmul (hm.metric.leviCivita).toAffineConnection p v Finset.univ
        (c i) F (hc_smooth i) hFsmooth]
      -- substitute the prescribed values
      have hterm : ∀ m,
          dirTangent (c i m) v • F m p + c i m p • (hm.metric.leviCivita).cov p v (F m)
            = (-(hm.metric.metricInner p ((hm.metric.leviCivita).cov p v (F i)) (e m))) • e m
              + (if i = m then (1 : ℝ) else 0) • (hm.metric.leviCivita).cov p v (F m) := by
        intro m
        rw [hc_dir i m v, hc_val i m, hFval m]
        congr 2
      rw [Finset.sum_congr rfl (fun m _ => hterm m)]
      rw [Finset.sum_add_distrib]
      -- second sum collapses to ∇_v F_i
      have hsnd : (∑ m, (if i = m then (1 : ℝ) else 0)
          • (hm.metric.leviCivita).cov p v (F m)) = (hm.metric.leviCivita).cov p v (F i) := by
        simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      -- first sum is −∇_v F_i by the orthonormal expansion
      have hfst : (∑ m, (-(hm.metric.metricInner p
          ((hm.metric.leviCivita).cov p v (F i)) (e m))) • e m)
            = -(hm.metric.leviCivita).cov p v (F i) := by
        have hexp := metricInner_orthonormal_expansion (I := I) he
          ((hm.metric.leviCivita).cov p v (F i))
        simp only [neg_smul]
        rw [Finset.sum_neg_distrib, ← hexp]
      rw [hfst, hsnd, neg_add_cancel]

end PetersenLib

end
