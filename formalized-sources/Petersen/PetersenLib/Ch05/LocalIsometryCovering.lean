import PetersenLib.Ch05.IsometryUniqueness

/-!
# Petersen Ch. 5, §5.6.1 — Lemma 5.6.4: a complete local isometry covers

Blueprint node `lem:pet-ch5-local-isometry-covering`.
-/

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
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [CompleteSpace E'] [T2Space (TangentBundle I' M')] [T2Space M']

/-- **Math.** On a geodesically complete manifold every time lies in the maximal
existence domain of every geodesic initial datum. -/
theorem mem_geodesicMaximalDomain_of_complete (g : RiemannianMetric I M)
    (hg : IsGeodesicallyComplete (I := I) g) (p : M) (v : TangentSpace I p) (t : ℝ) :
    t ∈ geodesicMaximalDomain (I := I) g p v := by
  obtain ⟨γ, hcont, h0, hvel, hgeo⟩ := hg p v
  exact ⟨Set.univ, ⟨isOpen_univ, Set.ordConnected_univ, Set.mem_univ 0, γ,
    ⟨hcont.continuousOn, h0, hvel, fun s _ => hgeo s⟩⟩, Set.mem_univ t⟩

/-- **Math.** A geodesic on an open time set is the solution of its own initial-value
problem re-based at any time `t₁` of that set. -/
theorem isGeodesicWithInitialOn_restart (g : RiemannianMetric I M) {γ : ℝ → M} {J : Set ℝ}
    (hcont : ContinuousOn γ J) (hgeo : Geodesic.IsGeodesicOn (I := I) g γ J)
    {t₁ : ℝ} (ht₁ : t₁ ∈ J) :
    IsGeodesicWithInitialOn (I := I) g γ J t₁ (γ t₁)
      ((deriv (Geodesic.chartLocalCurve (I := I) γ t₁) t₁ : E) : TangentSpace I (γ t₁)) := by
  refine ⟨hcont, rfl, ?_, hgeo⟩
  obtain ⟨v, a, hv, -, -, -⟩ := hgeo t₁ ht₁
  have hd : deriv (Geodesic.chartLocalCurve (I := I) γ t₁) t₁ = v := hv.deriv
  rw [hd]
  exact hv

/-- **Math.** **Time reversal of a geodesic.**  A geodesic `γ` on an open, order-connected
time set `J`, run backwards from the time `t₁`, is the maximal geodesic of a suitable
initial datum at `m = γ t₁`: for every `s` with `t₁ - s ∈ J` the maximal geodesic of that
datum is defined at time `s` and takes the value `γ (t₁ - s)` there.

This is the tool that lets one run a geodesic *backwards* from a known endpoint, which is
what the covering argument needs. -/
theorem exists_geodesicMaximal_reverse (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} (hJo : IsOpen J) (hJc : J.OrdConnected)
    (hcont : ContinuousOn γ J) (hgeo : Geodesic.IsGeodesicOn (I := I) g γ J)
    {t₁ : ℝ} (ht₁ : t₁ ∈ J) {m : M} (hm : γ t₁ = m) {s : ℝ} (hs : t₁ - s ∈ J) :
    ∃ y : TangentSpace I m, s ∈ geodesicMaximalDomain (I := I) g m y ∧
      geodesicMaximalCurve (I := I) g m y s = γ (t₁ - s) := by
  subst hm
  set y : TangentSpace I (γ t₁) :=
    ((deriv (Geodesic.chartLocalCurve (I := I) γ t₁) t₁ : E) : TangentSpace I (γ t₁)) with hy
  have h1 : IsGeodesicWithInitialOn (I := I) g γ J t₁ (γ t₁) y :=
    isGeodesicWithInitialOn_restart (I := I) g hcont hgeo ht₁
  have h2 := h1.shift (-t₁)
  rw [add_neg_cancel] at h2
  have h3 := geodesicHomogeneity (I := I) g (-1 : ℝ) h2
  -- the reversed time set
  set J' : Set ℝ := {σ : ℝ | (-1 : ℝ) * σ ∈ {τ : ℝ | τ - -t₁ ∈ J}} with hJ'
  have hmemJ' : ∀ σ : ℝ, σ ∈ J' ↔ t₁ - σ ∈ J := by
    intro σ
    simp only [hJ', Set.mem_setOf_eq]
    constructor <;> intro h
    · have : (-1 : ℝ) * σ - -t₁ = t₁ - σ := by ring
      rwa [this] at h
    · have : (-1 : ℝ) * σ - -t₁ = t₁ - σ := by ring
      rwa [this]
  have hJ'o : IsOpen J' := by
    have : J' = (fun σ : ℝ => t₁ - σ) ⁻¹' J := by
      ext σ; rw [hmemJ']; rfl
    rw [this]
    exact hJo.preimage (by fun_prop)
  have hJ'c : J'.OrdConnected := by
    constructor
    intro a ha b hb c hc
    rw [hmemJ'] at ha hb ⊢
    exact hJc.out hb ha ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have h0J' : (0 : ℝ) ∈ J' := by rw [hmemJ']; simpa using ht₁
  have hsJ' : s ∈ J' := by rw [hmemJ']; exact hs
  refine ⟨-y, ⟨J', ⟨hJ'o, hJ'c, h0J', fun σ : ℝ => γ ((-1 : ℝ) * σ - -t₁), ?_⟩, hsJ'⟩, ?_⟩
  · have hsm : ((-1 : ℝ) • y) = -y := neg_one_smul ℝ y
    rw [hsm] at h3
    exact h3
  · have hsm : ((-1 : ℝ) • y) = -y := neg_one_smul ℝ y
    rw [hsm] at h3
    have := geodesicMaximalCurve_eqOn (I := I) g hJ'o hJ'c h0J' h3 hsJ'
    rw [this]
    show γ ((-1 : ℝ) * s - -t₁) = γ (t₁ - s)
    congr 1
    ring

variable {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {F : M → M'}

/-- **Math.** Petersen Ch. 5, Lemma 5.6.4 (openness half): the image of a **geodesically
complete** manifold under a local Riemannian isometry is **open**.

Around `F p` the intrinsic exponential image `exp_{F p}(B(0, ε))` is a neighbourhood of
`F p` (`exists_isOpen_image_geodesicMaximalCurve_mem_nhds`), and every point of it is hit:
given `u ∈ T_{F p}N`, completeness of `M` makes `exp_p((DF_p)⁻¹ u)` defined and exponential
naturality (Prop. 5.6.1 (2)) sends it to `exp_{F p} u`. -/
theorem completeLocalIsometry_isOpen_range
    (hF : IsLocalRiemannianIsometry gM gN F) (hM : IsGeodesicallyComplete (I := I) gM) :
    IsOpen (Set.range F) := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨p, rfl⟩
  obtain ⟨ε, hε, hdom, hnhds⟩ :=
    exists_isOpen_image_geodesicMaximalCurve_mem_nhds (I := I') gN (F p)
  refine Filter.mem_of_superset hnhds ?_
  rintro z ⟨u, -, rfl⟩
  obtain ⟨v, hv⟩ := (hF.bijective_mfderiv p).surjective u
  refine ⟨geodesicMaximalCurve (I := I) gM p v 1, ?_⟩
  have h1 : (1 : ℝ) ∈ geodesicMaximalDomain (I := I) gM p v :=
    mem_geodesicMaximalDomain_of_complete (I := I) gM hM p v 1
  rw [(localIsometry_expNaturality hF p v).2 1 h1, hv]

/-- **Math.** Petersen Ch. 5, Lemma 5.6.4 (closedness half): the image of a **geodesically
complete** manifold under a local Riemannian isometry is **closed**.

Let `q ∈ closure (range F)`.  The intrinsic exponential image `exp_q(B(0, ε))` is a
neighbourhood of `q`, so it meets `range F`: there are `x ∈ M` and `u ∈ T_qN` with
`exp_q u = F x`.  Running that geodesic **backwards** from `F x`
(`exists_geodesicMaximal_reverse`) produces `y ∈ T_{F x}N` with `exp_{F x} y = q`.  Lift
`y` through the linear isomorphism `DF_x` and run the lifted geodesic in `M` — completeness
says it is defined at time `1` — then exponential naturality gives
`F (exp_x ((DF_x)⁻¹ y)) = exp_{F x} y = q`. -/
theorem completeLocalIsometry_isClosed_range
    (hF : IsLocalRiemannianIsometry gM gN F) (hM : IsGeodesicallyComplete (I := I) gM) :
    IsClosed (Set.range F) := by
  rw [← closure_subset_iff_isClosed]
  intro q hq
  obtain ⟨ε, hε, hdom, hnhds⟩ :=
    exists_isOpen_image_geodesicMaximalCurve_mem_nhds (I := I') gN q
  obtain ⟨z, hzimg, x, hxz⟩ := mem_closure_iff_nhds.mp hq _ hnhds
  obtain ⟨u, hu, hu1⟩ := hzimg
  -- `exp_q u = F x`
  have hux : geodesicMaximalCurve (I := I') gN q u 1 = F x := by rw [hxz]; exact hu1
  have hspec := geodesicMaximalCurve_spec (I := I') gN q u
  have h1D : (1 : ℝ) ∈ geodesicMaximalDomain (I := I') gN q u := hdom u hu
  have h0D : (0 : ℝ) ∈ geodesicMaximalDomain (I := I') gN q u :=
    zero_mem_geodesicMaximalDomain (I := I') gN q u
  obtain ⟨y, -, hy2⟩ := exists_geodesicMaximal_reverse (I := I') gN
    (isOpen_geodesicMaximalDomain (I := I') gN q u)
    (ordConnected_geodesicMaximalDomain (I := I') gN q u)
    hspec.1 hspec.2.2.2 h1D hux (s := (1 : ℝ)) (by simpa using h0D)
  -- `exp_{F x} y = q`
  have hyq : geodesicMaximalCurve (I := I') gN (F x) y 1 = q := by
    rw [hy2]
    show geodesicMaximalCurve (I := I') gN q u (1 - 1) = q
    rw [sub_self]
    exact hspec.2.1
  obtain ⟨w, hw⟩ := (hF.bijective_mfderiv x).surjective y
  refine ⟨geodesicMaximalCurve (I := I) gM x w 1, ?_⟩
  have h1 : (1 : ℝ) ∈ geodesicMaximalDomain (I := I) gM x w :=
    mem_geodesicMaximalDomain_of_complete (I := I) gM hM x w 1
  rw [(localIsometry_expNaturality hF x w).2 1 h1, hw, hyq]

/-- **Math.** Petersen Ch. 5, Lemma 5.6.4 (surjectivity): a local Riemannian isometry out
of a **nonempty geodesically complete** manifold into a **connected** manifold is
**surjective**.  Its image is open, closed and nonempty, hence everything. -/
theorem completeLocalIsometry_surjective [Nonempty M] [PreconnectedSpace M']
    (hF : IsLocalRiemannianIsometry gM gN F) (hM : IsGeodesicallyComplete (I := I) gM) :
    Function.Surjective F := by
  have hclopen : IsClopen (Set.range F) :=
    ⟨completeLocalIsometry_isClosed_range hF hM, completeLocalIsometry_isOpen_range hF hM⟩
  have : Set.range F = Set.univ := hclopen.eq_univ (Set.range_nonempty F)
  exact Set.range_eq_univ.mp this

end PetersenLib

end
