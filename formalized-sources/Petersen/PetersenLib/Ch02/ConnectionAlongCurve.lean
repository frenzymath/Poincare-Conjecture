import PetersenLib.Ch02.FrameDecomposition

/-!
# Petersen Ch. 2, §2.2 — Locality of the connection along a curve (Lem. 2.2.4)

If two smooth vector fields `X` and `Y` agree along a curve `c` near `t₀`
(`X ∘ c = Y ∘ c`), then their covariant derivatives in the direction of the
velocity `ċ(t₀)` agree: `∇_{ċ(t₀)} X = ∇_{ċ(t₀)} Y`
(`connection_local_alongCurve`).

Petersen's proof: choose a local frame `E_1, …, E_n` near `p = c(t₀)` and write
`X = Xⁱ E_i`, `Y = Yⁱ E_i` with smooth coefficient functions.  By the Leibniz
rule, `∇_v X = Σᵢ (dXⁱ(v) · E_i|_p + Xⁱ(p) · ∇_v E_i)`.  Since `X ∘ c = Y ∘ c`,
the coefficients satisfy `Xⁱ ∘ c = Yⁱ ∘ c`, so `Xⁱ(p) = Yⁱ(p)` and
`dXⁱ(v) = dYⁱ(v)` (equal derivatives along the curve, `v = ċ(t₀)`), whence the
two expansions coincide.

The frame `E_i` is the chart coordinate frame, and the smooth coefficient
functions are `chartVectorFieldCoeff` (`FrameDecomposition.lean`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2, `lem:pet-ch2-locality-along-curve`.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]

namespace AlongCurve

/-! ## Ch02-local copies of general connection/extension utilities

These are general utilities (`∇_v 0 = 0`, finite additivity, finite Leibniz,
germ extension of smooth functions, and a global smooth frame field) that also
appear in Ch03; they are reproved here `private` so that the along-a-curve
locality lemma stays in Ch02 without importing Ch03. -/

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

/-- A global smooth vector field agreeing with the coordinate frame field
`∂_j = chartBasisVecFiber p j` near `p`. -/
private def frameField (p : M) (j : Fin (Module.finrank ℝ E)) : SmoothVectorField I M :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) p j q)
    (trivializationAt E (TangentSpace I) p).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) p j)
    (FiberBundle.mem_baseSet_trivializationAt' p)).choose

private theorem frameField_eventuallyEq (p : M) (j : Fin (Module.finrank ℝ E)) :
    ⇑(frameField (I := I) p j) =ᶠ[nhds p] fun q => chartBasisVecFiber (I := I) p j q :=
  (exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => chartBasisVecFiber (I := I) p j q)
    (trivializationAt E (TangentSpace I) p).open_baseSet
    (chartBasisVec_contMDiffOn (I := I) p j)
    (FiberBundle.mem_baseSet_trivializationAt' p)).choose_spec

/-! ## The frame expansion of `∇_v` -/

/-- **Math.** The frame expansion of the covariant derivative at `p`: for a smooth
vector field `W`, `∇_v W = Σᵢ (dWⁱ(v) · E_i|_p + Wⁱ(p) · ∇_v E_i)`, where
`Wⁱ = chartVectorFieldCoeff p W i` are the (smooth) chart-frame coordinates and
`E_i = frameField p i` a global smooth field agreeing with the coordinate frame
near `p`.  Obtained by replacing `W` near `p` by `Σᵢ Wⁱ E_i` (frame
decomposition + locality of the connection) and applying the finite Leibniz
rule. -/
private theorem cov_eq_frameExpansion (D : AffineConnection I M) (p : M)
    (v : TangentSpace I p) {W : Π x : M, TangentSpace I x} (hW : IsSmoothVectorField W) :
    D.cov p v W
      = ∑ i, (dirTangent (chartVectorFieldCoeff p W i) v • frameField (I := I) p i p
          + chartVectorFieldCoeff p W i p • D.cov p v (⇑(frameField (I := I) p i))) := by
  classical
  have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  -- global smooth extensions of the (smooth-on-base-set) coordinate functions
  choose γ hγsmooth hγev using fun i =>
    exists_contMDiff_eventuallyEq (I := I) hbaseopen
      (chartVectorFieldCoeff_contMDiffOn p hW i) hbase
  have hterm : ∀ i, IsSmoothVectorField (fun q => γ i q • ⇑(frameField (I := I) p i) q) :=
    fun i => by simpa using
      (SmoothVectorField.smul (γ i) (hγsmooth i) (frameField (I := I) p i)).smooth
  have hWsum : IsSmoothVectorField (fun q => ∑ i, γ i q • ⇑(frameField (I := I) p i) q) :=
    isSmoothVF_finsetSum Finset.univ _ hterm
  -- open neighborhood of `p` where `W = Σᵢ γᵢ • Eᵢ`
  obtain ⟨U, hU, hUopen, hpU⟩ := eventually_nhds_iff.mp
    (((eventually_all.mpr fun i => frameField_eventuallyEq (I := I) p i).and
        (eventually_all.mpr fun i => hγev i)).and
      (hbaseopen.eventually_mem hbase))
  have hEqOn : Set.EqOn W (fun q => ∑ i, γ i q • ⇑(frameField (I := I) p i) q) U := by
    intro q hq
    rw [vectorField_eq_sum_chartCoeff p W (hU q hq).2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hU q hq).1.2 i, (hU q hq).1.1 i]
  rw [connection_local_openSet D v hW hWsum hUopen hpU hEqOn,
    cov_finsetSumSmul D p v Finset.univ γ _ hγsmooth
      (fun i => (frameField (I := I) p i).smooth)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hval : γ i p = chartVectorFieldCoeff p W i p := (hγev i).self_of_nhds
  have hd : dirTangent (γ i) v = dirTangent (chartVectorFieldCoeff p W i) v :=
    DFunLike.congr_fun (hγev i).mfderiv_eq v
  rw [hd, hval]

end AlongCurve

open AlongCurve in
/-- **Math.** **Lem. 2.2.4 (locality along a curve)**: if the smooth vector
fields `X` and `Y` agree along the curve `c` near `t₀` (`X ∘ c = Y ∘ c`), then
`∇_{ċ(t₀)} X = ∇_{ċ(t₀)} Y` — the covariant derivative in a direction only sees
the field along a curve tangent to that direction.  Petersen's proof: in a local
frame, `∇_v` expands through the coefficients `Xⁱ`, whose values and directional
derivatives along the curve agree with those of `Yⁱ` because `X ∘ c = Y ∘ c`. -/
theorem connection_local_alongCurve (D : AffineConnection I M)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ) I ∞ c) {t₀ : ℝ}
    (hXY : ∀ᶠ t in nhds t₀, X (c t) = Y (c t)) :
    D.cov (c t₀) (mfderiv 𝓘(ℝ) I c t₀ (1 : ℝ)) X
      = D.cov (c t₀) (mfderiv 𝓘(ℝ) I c t₀ (1 : ℝ)) Y := by
  classical
  set p := c t₀ with hp
  set v := mfderiv 𝓘(ℝ) I c t₀ (1 : ℝ) with hv
  rw [cov_eq_frameExpansion D p v hX, cov_eq_frameExpansion D p v hY]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hXYp : X p = Y p := hXY.self_of_nhds
  -- coefficient values at `p` agree
  have hcoeff_p : chartVectorFieldCoeff p X i p = chartVectorFieldCoeff p Y i p := by
    show (Module.finBasis ℝ E).coord i
        ((trivializationAt E (TangentSpace I) p ⟨p, X p⟩).2)
      = (Module.finBasis ℝ E).coord i
        ((trivializationAt E (TangentSpace I) p ⟨p, Y p⟩).2)
    rw [hXYp]
  -- directional derivatives along the curve agree
  have hcX_diff : MDifferentiableAt I 𝓘(ℝ) (chartVectorFieldCoeff p X i) p :=
    ((chartVectorFieldCoeff_contMDiffOn p hX i).contMDiffAt
      ((trivializationAt E (TangentSpace I) p).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' p))).mdifferentiableAt (by simp)
  have hcY_diff : MDifferentiableAt I 𝓘(ℝ) (chartVectorFieldCoeff p Y i) p :=
    ((chartVectorFieldCoeff_contMDiffOn p hY i).contMDiffAt
      ((trivializationAt E (TangentSpace I) p).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' p))).mdifferentiableAt (by simp)
  have hc_diff : MDifferentiableAt 𝓘(ℝ) I c t₀ := hc.mdifferentiable (by simp) t₀
  have hchainX : mfderiv 𝓘(ℝ) 𝓘(ℝ) (chartVectorFieldCoeff p X i ∘ c) t₀ (1 : ℝ)
      = mfderiv I 𝓘(ℝ) (chartVectorFieldCoeff p X i) p v := by
    rw [mfderiv_comp t₀ hcX_diff hc_diff]; rfl
  have hchainY : mfderiv 𝓘(ℝ) 𝓘(ℝ) (chartVectorFieldCoeff p Y i ∘ c) t₀ (1 : ℝ)
      = mfderiv I 𝓘(ℝ) (chartVectorFieldCoeff p Y i) p v := by
    rw [mfderiv_comp t₀ hcY_diff hc_diff]; rfl
  have hev : (chartVectorFieldCoeff p X i ∘ c) =ᶠ[nhds t₀]
      (chartVectorFieldCoeff p Y i ∘ c) := by
    filter_upwards [hXY] with t ht
    show (Module.finBasis ℝ E).coord i
        ((trivializationAt E (TangentSpace I) p ⟨c t, X (c t)⟩).2)
      = (Module.finBasis ℝ E).coord i
        ((trivializationAt E (TangentSpace I) p ⟨c t, Y (c t)⟩).2)
    rw [ht]
  have hcoeff_dir : dirTangent (chartVectorFieldCoeff p X i) v
      = dirTangent (chartVectorFieldCoeff p Y i) v := by
    show mfderiv I 𝓘(ℝ) (chartVectorFieldCoeff p X i) p v
      = mfderiv I 𝓘(ℝ) (chartVectorFieldCoeff p Y i) p v
    rw [← hchainX, ← hchainY]
    exact DFunLike.congr_fun hev.mfderiv_eq (1 : ℝ)
  rw [hcoeff_p, hcoeff_dir]

end PetersenLib

end
