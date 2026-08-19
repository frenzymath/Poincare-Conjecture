import PetersenLib.Ch05.LocalIsometryCovering
import PetersenLib.Ch05.GeodesicFlowBox

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff ENNReal
namespace PetersenLib
open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

theorem scratch_controlled_extension (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) {J : Set ℝ} (hJ : IsOpen J)
    (hJab : Icc a b ⊆ J) (hcont : ContinuousOn γ J)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ J) :
    UniformExtensionProp (I := I) g γ a b := by
  classical
  obtain ⟨δJ, hδJ, hth⟩ := isCompact_Icc.exists_thickening_subset_open hJ hJab
  have hJ'sub : Ioo (a - δJ) (b + δJ) ⊆ J := by
    intro t ht
    refine hth ?_
    rw [Metric.mem_thickening_iff]
    rcases le_total t a with h | h
    · exact ⟨a, Set.left_mem_Icc.mpr hab,
        by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith [ht.1]⟩
    · rcases le_total t b with h' | h'
      · exact ⟨t, ⟨h, h'⟩, by rw [Real.dist_eq, sub_self, abs_zero]; exact hδJ⟩
      · exact ⟨b, Set.right_mem_Icc.mpr hab,
          by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [ht.2]⟩
  set J' : Set ℝ := Ioo (a - δJ) (b + δJ) with hJ'def
  have hJ'o : IsOpen J' := isOpen_Ioo
  have habJ' : Icc a b ⊆ J' := fun t ht =>
    ⟨by linarith [ht.1, hδJ], by linarith [ht.2, hδJ]⟩
  have hcont' : ContinuousOn γ J' := hcont.mono hJ'sub
  have hγ' : Geodesic.IsGeodesicOn (I := I) g γ J' := hγ.mono hJ'sub
  have hK : IsCompact (geodesicVelocityCurve (I := I) γ '' Icc a b) :=
    isCompact_geodesicVelocityCurve_image (I := I) g hJ'o hcont' hγ' isCompact_Icc habJ'
  choose ε hε W hWopen hmemW Φ hflow hΦcont using
    fun y : TangentBundle I M => exists_geodesicLocalFlow (I := I) g y
  obtain ⟨T, hTK, hTcov⟩ := hK.elim_nhds_subcover W
    (fun y _ => (hWopen y).mem_nhds (hmemW y))
  have hTne : T.Nonempty := by
    have haK : geodesicVelocityCurve (I := I) γ a
        ∈ geodesicVelocityCurve (I := I) γ '' Icc a b :=
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr hab)
    obtain ⟨y₀, hy₀T, -⟩ := Set.mem_iUnion₂.mp (hTcov haK)
    exact ⟨y₀, hy₀T⟩
  set εmin : ℝ := T.inf' hTne ε with hεmindef
  have hεminpos : 0 < εmin := by
    obtain ⟨y₀, hy₀T, hinf⟩ := Finset.exists_mem_eq_inf' hTne ε
    rw [hεmindef, hinf]
    exact hε y₀
  obtain ⟨m, hm⟩ := exists_nat_gt ((b - a) / εmin)
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hm0' : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso
      have h1 : (0:ℝ) ≤ (b - a) / εmin := div_nonneg hba hεminpos.le
      rw [Nat.cast_zero] at hm
      linarith
    · exact h
  have hm0 : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr hm0'
  set step : ℝ := (b - a) / m with hstepdef
  have hstep0 : 0 ≤ step := div_nonneg hba hm0.le
  have hmstep : (m:ℝ) * step = b - a := by
    rw [hstepdef]
    field_simp
  have hmesh : step < εmin := by
    have h1 : b - a < (m:ℝ) * εmin := by
      have h2 := mul_lt_mul_of_pos_right hm hεminpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hεminpos)] at h2
    rw [hstepdef, div_lt_iff₀ hm0, mul_comm]
    exact h1
  have hsub : ∀ i : ℕ, i ≤ m → a + i * step ∈ Icc a b := by
    intro i hi
    constructor
    · have h1 : (0:ℝ) ≤ i * step := mul_nonneg (Nat.cast_nonneg i) hstep0
      linarith
    · have h1 : (i:ℝ) * step ≤ m * step := by
        apply mul_le_mul_of_nonneg_right _ hstep0
        exact_mod_cast hi
      linarith [hmstep]
  have hkey : ∀ i : ℕ, i ≤ m → UniformExtensionProp (I := I) g γ a (a + i * step) := by
    intro i
    induction i with
    | zero =>
      intro _
      have h := uniformExtensionProp_self (I := I) g γ a
      simpa using h
    | succ k ih =>
      intro hk
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hQ := ih hk'
      have htk := hsub k hk'
      have htk1 := hsub (k + 1) hk
      have hyK : geodesicVelocityCurve (I := I) γ (a + k * step)
          ∈ geodesicVelocityCurve (I := I) γ '' Icc a b :=
        Set.mem_image_of_mem _ htk
      obtain ⟨y, hyT, hyW⟩ := Set.mem_iUnion₂.mp (hTcov hyK)
      have hεy : step < ε y := lt_of_lt_of_le hmesh (Finset.inf'_le ε hyT)
      have harith : (a + k * step) + step = a + ((k+1 : ℕ) : ℝ) * step := by
        push_cast
        ring
      have hbridge := uniformExtensionProp_step (I := I) g hJ'o Set.ordConnected_Ioo
        hcont' hγ' (hε y) (hWopen y) (hflow y) (hΦcont y) hyW
        (habJ' htk) (by rw [harith]; exact habJ' htk1) hstep0 hεy
      rw [harith] at hbridge
      have hle1 : a ≤ a + k * step := htk.1
      have hle2 : a + k * step ≤ a + ((k+1:ℕ):ℝ) * step := by
        rw [← harith]
        linarith
      exact hQ.trans hle1 hle2 hbridge
  have hQab : UniformExtensionProp (I := I) g γ a b := by
    have h := hkey m (le_refl m)
    have hfin : a + (m:ℝ) * step = b := by
      rw [hmstep]
      ring
    rwa [hfin] at h
  exact hQab

theorem scratch_endpoint_of_control (g : RiemannianMetric I M)
    (hM : IsGeodesicallyComplete (I := I) g) (p : M) (v : TangentSpace I p)
    (hcontrol : UniformExtensionProp (I := I) g
      (geodesicMaximalCurve (I := I) g p v) 0 1) :
    ContinuousAt (fun z : TangentBundle I M =>
      geodesicMaximalCurve (I := I) g z.proj z.2 1) (⟨p, v⟩ : TangentBundle I M) := by
  have hdom : ∀ t : ℝ, t ∈ geodesicMaximalDomain (I := I) g p v :=
    fun t => mem_geodesicMaximalDomain_of_complete (I := I) g hM p v t
  have hdom_eq : geodesicMaximalDomain (I := I) g p v = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact hdom t
  have hspec := geodesicMaximalCurve_spec (I := I) g p v
  have hspec' : IsGeodesicWithInitialOn (I := I) g
      (geodesicMaximalCurve (I := I) g p v) Set.univ 0 p v := by
    rw [← hdom_eq]
    exact hspec
  have hcont : Continuous (geodesicMaximalCurve (I := I) g p v) := by
    exact continuousOn_univ.mp (by simpa [hdom_eq] using hspec.1)
  have hgeo : Geodesic.IsGeodesicOn (I := I) g
      (geodesicMaximalCurve (I := I) g p v) Set.univ := by
    simpa [hdom_eq] using hspec.2.2.2
  rw [continuousAt_def]
  intro U hU
  have hstateU : Bundle.TotalSpace.proj ⁻¹' U ∈
      𝓝 (geodesicVelocityCurve (I := I)
        (geodesicMaximalCurve (I := I) g p v) 1) := by
    have hproj : ContinuousAt (Bundle.TotalSpace.proj : TangentBundle I M → M)
        (geodesicVelocityCurve (I := I)
          (geodesicMaximalCurve (I := I) g p v) 1) :=
      (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt
    apply hproj.preimage_mem_nhds
    simpa only [geodesicVelocityCurve_proj] using hU
  obtain ⟨W, hW, hWspec⟩ := hcontrol (Bundle.TotalSpace.proj ⁻¹' U) hstateU
  have hstate0 : geodesicVelocityCurve (I := I)
      (geodesicMaximalCurve (I := I) g p v) 0 = (⟨p, v⟩ : TangentBundle I M) :=
    hspec'.geodesicVelocityCurve_eq
  rw [hstate0] at hW
  refine Filter.mem_of_superset hW ?_
  intro z hz
  obtain ⟨γz, Jz, hJzo, hJzc, hJzsub, hγz, hstatez⟩ := hWspec z hz
  have h0Jz : (0 : ℝ) ∈ Jz := hJzsub ⟨by norm_num, by norm_num⟩
  have h1Jz : (1 : ℝ) ∈ Jz := hJzsub ⟨by norm_num, by norm_num⟩
  have hzdom : (1 : ℝ) ∈ geodesicMaximalDomain (I := I) g z.proj z.2 :=
    mem_geodesicMaximalDomain_of_complete (I := I) g hM z.proj z.2 1
  have hmaxspec := geodesicMaximalCurve_spec (I := I) g z.proj z.2
  have hmax0 : geodesicMaximalCurve (I := I) g z.proj z.2 0 = z.proj :=
    hmaxspec.2.1
  have hmaxvel : HasDerivAt
      (fun s => extChartAt I z.proj
        (geodesicMaximalCurve (I := I) g z.proj z.2 s)) z.2 0 := hmaxspec.2.2.1
  have hmaxJ : IsGeodesicWithInitialOn (I := I) g
      (geodesicMaximalCurve (I := I) g z.proj z.2)
      (geodesicMaximalDomain (I := I) g z.proj z.2) 0 z.proj z.2 := hmaxspec
  have heq := geodesicWithInitialOn_eqOn (I := I) g
      (isOpen_geodesicMaximalDomain (I := I) g z.proj z.2)
      (ordConnected_geodesicMaximalDomain (I := I) g z.proj z.2)
      hJzo hJzc hmaxJ hγz
      (zero_mem_geodesicMaximalDomain (I := I) g z.proj z.2) h0Jz
  have hend := heq ⟨hzdom, h1Jz⟩
  have hstate_mem : geodesicVelocityCurve (I := I) γz 1 ∈
      Bundle.TotalSpace.proj ⁻¹' U := hstatez
  have hprojend : γz 1 ∈ U := hstate_mem
  rw [← hend] at hprojend
  exact hprojend

end PetersenLib
