import MorganTianLib.Ch02.LaplacianExtremum
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Morgan--Tian Ch. 3 - compact parabolic comparison

This file isolates the real-variable maximum-principle step used by the Shi
localization argument.  The geometric evolution and cutoff estimates are kept
as explicit hypotheses in the downstream producers; no curvature estimate is
assumed here.
-/

open Set Filter

noncomputable section

namespace MorganTianLib

private theorem isLocalMaxOn_of_isMaxOn {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {s : Set X} {x : X} (h : IsMaxOn f s x) :
    IsLocalMaxOn f s x := by
  rw [IsLocalMaxOn, IsMaxFilter]
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact h hy

/-- **Math.** At a positive-time maximum on a closed interval, the within derivative is
nonnegative.  The proof also covers a maximum at the terminal endpoint. -/
theorem shi_time_deriv_nonneg_of_isMaxOn_Icc {f : ℝ → ℝ} {f' t T : ℝ}
    (ht : t ∈ Icc 0 T) (htpos : 0 < t)
    (hmax : IsMaxOn f (Icc 0 T) t)
    (hderiv : HasDerivWithinAt f f' (Icc 0 T) t) :
    0 ≤ f' := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hcone : 0 - t ∈ posTangentConeAt (Icc 0 T) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 T).segment_subset ht hzero)
  have hnonpos := (isLocalMaxOn_of_isMaxOn hmax).hasFDerivWithinAt_nonpos
    hderiv.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hnonpos
  nlinarith

/-- **Math.** Compact-space weak maximum principle in the form needed for an affine
barrier.  The only spatial input is the derivative inequality at a positive
spacetime maximum; the initial endpoint is used only as data. -/
theorem shi_nonpos_of_forall_isMax_time_deriv_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {w wt : X → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : X × ℝ => w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (w x) (wt x t) (Icc 0 T) t)
    (hmax : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, 0 < w x t →
      (∀ y, w y t ≤ w x t) → wt x t ≤ K * w x t)
    (hzero : ∀ x, w x 0 ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → w x t ≤ 0 := by
  classical
  intro x t ht
  by_contra hle
  have hwt : 0 < w x t := lt_of_not_ge hle
  have htne : t ≠ 0 := by
    intro heq
    subst t
    exact (not_lt_of_ge (hzero x)) hwt
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
  set ε : ℝ := Real.exp (-K * t) * w x t / (2 * t) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact div_pos (mul_pos (Real.exp_pos _) hwt) (mul_pos (by norm_num) htpos)
  set V : X × ℝ → ℝ :=
    fun z => Real.exp (-K * z.2) * w z.1 z.2 - ε * z.2 with hV
  have hVcont : ContinuousOn V ((Set.univ : Set X) ×ˢ Icc 0 T) := by
    rw [hV]
    have hexp : Continuous (fun z : X × ℝ => Real.exp (-K * z.2)) := by
      fun_prop
    have hlin : Continuous (fun z : X × ℝ => ε * z.2) := by
      fun_prop
    exact (hexp.continuousOn.mul hcont).sub hlin.continuousOn
  have hcompact : IsCompact ((Set.univ : Set X) ×ˢ Icc 0 T) :=
    isCompact_univ.prod isCompact_Icc
  have hne : ((Set.univ : Set X) ×ˢ Icc 0 T).Nonempty := by
    let x₀ := Classical.choice (inferInstance : Nonempty X)
    exact ⟨(x₀, 0), ⟨mem_univ _, le_rfl, hT⟩⟩
  obtain ⟨z, hz, hzmax⟩ := hcompact.exists_isMaxOn hne hVcont
  have hVxt : 0 < V (x, t) := by
    have heq : V (x, t) = Real.exp (-K * t) * w x t / 2 := by
      rw [hV, hε]
      field_simp [htne]
      ring
    rw [heq]
    positivity
  have hVzpos : 0 < V z := lt_of_lt_of_le hVxt (hzmax ⟨mem_univ _, ht⟩)
  have hzt : z.2 ∈ Icc 0 T := hz.2
  have hztne : z.2 ≠ 0 := by
    intro heq
    have hzle : V z ≤ 0 := by
      simpa [hV, heq] using hzero z.1
    exact (not_lt_of_ge hzle) hVzpos
  have hztpos : 0 < z.2 := lt_of_le_of_ne hzt.1 (Ne.symm hztne)
  have hwzpos : 0 < w z.1 z.2 := by
    rw [hV] at hVzpos
    have hεtpos : 0 < ε * z.2 := mul_pos hεpos hztpos
    nlinarith [Real.exp_pos (-K * z.2)]
  have hwmax : ∀ y, w y z.2 ≤ w z.1 z.2 := by
    intro y
    have hleV := hzmax (show (y, z.2) ∈
        (Set.univ : Set X) ×ˢ Icc 0 T from ⟨mem_univ _, hzt⟩)
    change V (y, z.2) ≤ V z at hleV
    rw [hV] at hleV
    nlinarith [Real.exp_pos (-K * z.2)]
  have hrate : wt z.1 z.2 ≤ K * w z.1 z.2 :=
    hmax z.2 hzt hztpos z.1 hwzpos hwmax
  set vtime : ℝ → ℝ :=
    (fun s => Real.exp (-K * s)) * w z.1 - fun s => ε * id s with hvtime
  have hvtime_eq (s : ℝ) : vtime s = V (z.1, s) := by
    rw [hvtime, hV]
    rfl
  have htimeMax : IsMaxOn vtime (Icc 0 T) z.2 := by
    intro s hs
    change vtime s ≤ vtime z.2
    rw [hvtime_eq s, hvtime_eq z.2]
    exact hzmax ⟨mem_univ _, hs⟩
  have hlin : HasDerivAt (fun s : ℝ => -K * s) (-K) z.2 := by
    simpa using (hasDerivAt_id z.2).const_mul (-K)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-K * s))
      (Real.exp (-K * z.2) * (-K)) z.2 := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-K * z.2)).comp z.2 hlin
  have hVderiv : HasDerivWithinAt vtime
      (Real.exp (-K * z.2) * (-K) * w z.1 z.2
        + Real.exp (-K * z.2) * wt z.1 z.2 - ε)
      (Icc 0 T) z.2 := by
    rw [hvtime]
    simpa only [mul_one] using
      (hexp.hasDerivWithinAt.mul (hderiv z.1 z.2 hzt)).sub
        ((hasDerivAt_id z.2).const_mul ε).hasDerivWithinAt
  have hdnonneg := shi_time_deriv_nonneg_of_isMaxOn_Icc hzt hztpos
    htimeMax hVderiv
  have hmul : Real.exp (-K * z.2) * wt z.1 z.2 ≤
      Real.exp (-K * z.2) * (K * w z.1 z.2) :=
    mul_le_mul_of_nonneg_left hrate (Real.exp_pos _).le
  nlinarith

/-- **Math.** Affine comparison obtained from the compact maximum principle. -/
theorem shi_le_affineBarrier_of_parabolic_inequality
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {u ut : X → ℝ → ℝ} {T a c : ℝ}
    (hT : 0 < T)
    (hu : ContinuousOn (fun z : X × ℝ => u z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ x, 0 < t →
      (∀ y, u y t ≤ u x t) → ut x t ≤ c)
    (hzero : ∀ x, u x 0 ≤ a) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ a + c * t := by
  let w : X → ℝ → ℝ := fun x t => u x t - (a + c * t)
  have hwcont : ContinuousOn (fun z : X × ℝ => w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T) := by
    dsimp [w]
    exact hu.sub (by fun_prop)
  have hwderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (w x) (ut x t - c)
        (Icc 0 T) t := by
    intro x t ht
    have hbar : HasDerivWithinAt (fun s : ℝ => a + c * s) c
        (Icc 0 T) t := by
      convert ((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul c)).hasDerivWithinAt using 1 <;>
        first | rfl | ring
    change HasDerivWithinAt (fun s : ℝ => u x s - (a + c * s))
      (ut x t - c) (Icc 0 T) t
    have hsub := (huderiv x t ht).sub hbar
    convert hsub using 1 <;> rfl
  have hwhmax : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, 0 < w x t →
      (∀ y, w y t ≤ w x t) → ut x t - c ≤ 0 := by
    intro t ht htpos x hx hmaxx
    have hu_max : ∀ y, u y t ≤ u x t := by
      intro y
      have hy := hmaxx y
      dsimp [w] at hy
      linarith
    have hdu := hmax t ht x htpos hu_max
    linarith
  have hwzero : ∀ x, w x 0 ≤ 0 := by
    intro x
    dsimp [w]
    simpa using hzero x
  have hnonpos := shi_nonpos_of_forall_isMax_time_deriv_le
    (w := w) (wt := fun x t => ut x t - c)
    (T := T) (K := 0) hT.le hwcont hwderiv
    (by
      intro t ht htpos x hx hmx
      simpa using hwhmax t ht htpos x hx hmx)
    hwzero
  intro x t ht
  have h := hnonpos x t ht
  dsimp [w] at h
  linarith

/-- **Math.** Compact-support localization bridge.  The affine comparison only
needs compactness of the set on which the cutoff is supported; the ambient
space itself need not be compact.  All differential and maximum hypotheses are
therefore restricted explicitly to `K`. -/
theorem shi_le_affineBarrier_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {u ut : X → ℝ → ℝ} {T a c : ℝ}
    (hT : 0 < T)
    (hu : ContinuousOn (fun z : X × ℝ => u z.1 z.2)
      (K ×ˢ Icc 0 T))
    (huderiv : ∀ x ∈ K, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ x ∈ K, 0 < t →
      (∀ y ∈ K, u y t ≤ u x t) → ut x t ≤ c)
    (hzero : ∀ x ∈ K, u x 0 ≤ a) :
    ∀ x ∈ K, ∀ t ∈ Icc 0 T, u x t ≤ a + c * t := by
  let Y := K
  let uY : Y → ℝ → ℝ := fun x t => u (x : X) t
  let utY : Y → ℝ → ℝ := fun x t => ut (x : X) t
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hK
  letI : Nonempty Y := Set.nonempty_coe_sort.mpr hKne
  have huY : ContinuousOn (fun z : Y × ℝ => uY z.1 z.2)
    ((Set.univ : Set Y) ×ˢ Icc 0 T) := by
    have hmap : ContinuousOn (fun z : Y × ℝ => ((z.1 : X), z.2))
        ((Set.univ : Set Y) ×ˢ Icc 0 T) := by
      have hval : Continuous (fun z : Y × ℝ => (z.1 : X)) :=
        continuous_subtype_val.comp continuous_fst
      exact hval.continuousOn.prodMk continuous_snd.continuousOn
    apply hu.comp' hmap
    intro z hz
    exact ⟨z.1.property, hz.2⟩
  have hderivY : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (uY x) (utY x t) (Icc 0 T) t := by
    intro x t ht
    exact huderiv (x : X) x.property t ht
  have hmaxY : ∀ t ∈ Icc 0 T, ∀ x, 0 < t →
      (∀ y, uY y t ≤ uY x t) → utY x t ≤ c := by
    intro t ht x htpos hmx
    apply hmax t ht (x : X) x.property htpos
    intro y hy
    exact hmx ⟨y, hy⟩
  have hzeroY : ∀ x, uY x 0 ≤ a := by
    intro x
    exact hzero (x : X) x.property
  have hbar := shi_le_affineBarrier_of_parabolic_inequality
    (X := Y) (u := uY) (ut := utY) (T := T) (a := a) (c := c)
    hT huY hderivY hmaxY hzeroY
  intro x hx t ht
  exact hbar ⟨x, hx⟩ t ht

end MorganTianLib
