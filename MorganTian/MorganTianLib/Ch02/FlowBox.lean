import MorganTianLib.Ch02.ForwardDifferenceFlow
import OpenGALib.Riemannian.Geodesic.UniformExistence
import OpenGALib.Riemannian.Manifold.DoCarmoCh2

/-!
# Morgan–Tian Ch. 2, §2.6 — the flow box of a smooth vector field near a compact set

Blueprint `lem:vector-field-flow-near-compact`: a smooth vector field `X` on a
manifold `M` admits, near any compact set `K`, a **local flow**: an open set
`U ⊇ K`, a time `η > 0`, and a map `Φ : U × (-η, η) → M`, jointly continuous,
with `Φ x 0 = x` and each `s ↦ Φ x s` an integral curve of `X`
(`SmoothVectorField.exists_localFlow_of_isCompact`). Together with the purely
topological maximum principle of `ForwardDifferenceFlow.lean` this proves the
**forward difference maximum property**, blueprint
`prop:forward-difference-maximum` (`SmoothVectorField.levelMax_le`).

## Construction

* Chart level (`exists_forall_hasDerivWithinAt_continuousOn_of_contDiffAt`):
  mathlib's ball-uniform Picard–Lindelöf
  (`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`),
  packaged with confinement to a prescribed neighbourhood by
  `Riemannian.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt`
  (DoCarmo), upgraded to joint continuity in `(x, t)` by
  `continuousOn_prod_of_continuousOn_lipschitzOnWith`.
* One chart (`SmoothVectorField.exists_localFlowAt`): the chart-level flow of
  the coordinate representation of `X` is pushed through `(extChartAt I z).symm`;
  the integral-curve property transfers by the `tangentCoordChange` computation
  of mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt`.
* Gluing (`SmoothVectorField.exists_localFlow_of_isCompact`): finitely many
  chart flow boxes cover `K`; on overlaps the flows agree by uniqueness of
  integral curves (`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`,
  which needs `M` Hausdorff), so the glued map is well defined and locally
  agrees with a continuous chart flow.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.6.
-/

open Set Filter Function Metric Riemannian
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib

/-! ### The chart-level flow box: uniform time, confinement, joint continuity -/

/-- **Math.** A `C¹` vector field `f` on a normed space has, near any point
`z₀` and inside any prescribed neighbourhood `U` of `z₀`, a **uniform-time
local flow**: initial conditions in a closed ball around `z₀` flow for a
uniform time `ε`, staying in `U`, jointly continuously in `(z, t)`. This is
the classical Picard–Lindelöf flow box; the Lipschitz-in-`z` estimate of
`Riemannian.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt`
upgrades to joint continuity on the product. -/
theorem exists_forall_hasDerivWithinAt_continuousOn_of_contDiffAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : F → F} {z₀ : F} (hf : ContDiffAt ℝ 1 f z₀) {U : Set F} (hU : U ∈ 𝓝 z₀) :
    ∃ (r ε : ℝ) (Z : F → ℝ → F), 0 < r ∧ 0 < ε ∧
      (∀ z ∈ closedBall z₀ r, Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z) (f (Z z t)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ U)) ∧
      ContinuousOn ↿Z (closedBall z₀ r ×ˢ Icc (-ε) ε) := by
  obtain ⟨r, ε, Z, L, hr, hε, hZ, hLip⟩ :=
    Riemannian.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf hU
  refine ⟨r, ε, Z, hr, hε, hZ, ?_⟩
  exact continuousOn_prod_of_continuousOn_lipschitzOnWith (↿Z) L
    (fun z hz => HasDerivWithinAt.continuousOn (hZ z hz).2.1) hLip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-! ### The chain rule along a manifold-differentiable curve -/

omit [CompleteSpace E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- **Math.** Chain rule: if `γ` is manifold-differentiable at `t₀` with
velocity `v ∈ T_{γ t₀}M` and `F : M → ℝ` is smooth, then `F ∘ γ` is
differentiable at `t₀` with derivative `dF_{γ t₀}(v)`. -/
theorem hasDerivAt_comp_of_hasMFDerivAt {F : M → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) {γ : ℝ → M} {t₀ : ℝ} {v : TangentSpace I (γ t₀)}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasDerivAt (fun s => F (γ s)) (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀) v) t₀ := by
  have hFd : HasMFDerivAt I 𝓘(ℝ, ℝ) F (γ t₀) (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀)) :=
    ((hF (γ t₀)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hFd.comp t₀ hγ
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  refine hcomp.congr_mfderiv ?_
  ext
  exact (congrArg (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀)) (one_smul ℝ v)).trans
    (one_smul ℝ (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀) v)).symm

/-! ### The flow box in one chart -/

/-- **Math.** **Flow box at a point** (blueprint
`lem:vector-field-flow-near-compact`, single-chart case): a smooth vector
field `X` on a boundaryless manifold has, near every point `z`, an open
neighbourhood `V ∋ z` and a time `ε > 0` such that every `x ∈ V` flows along
`X` for times in `(-ε, ε)`, jointly continuously in `(x, s)`. The flow is the
chart-level Picard–Lindelöf flow of the coordinate representation of `X`,
pushed back through the chart. -/
theorem exists_localFlowAt (X : SmoothVectorField I M) (z : M) :
    ∃ (ε : ℝ) (V : Set M) (Φ : M → ℝ → M), 0 < ε ∧ IsOpen V ∧ z ∈ V ∧
      (∀ x ∈ V, Φ x 0 = x) ∧
      (∀ x ∈ V, IsMIntegralCurveOn (Φ x) (fun q => X q) (Ioo (-ε) ε)) ∧
      ContinuousOn ↿Φ (V ×ˢ Ioo (-ε) ε) := by
  have hz_int : I.IsInteriorPoint z := BoundarylessManifold.isInteriorPoint
  -- differentiability of the coordinate representation of the vector field
  have hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, X x⟩ : TangentBundle I M)) z := (X.smooth z).of_le (by norm_num)
  rw [contMDiffAt_iff] at hv
  obtain ⟨-, hv⟩ := hv
  -- the chart-level flow box of the coordinate vector field, confined to the
  -- interior of the chart target
  have hUmem : interior (extChartAt I z).target ∈ 𝓝 (extChartAt I z z) :=
    isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp hz_int)
  obtain ⟨r, ε, Z, hr, hε, hZ, hZcont⟩ :=
    exists_forall_hasDerivWithinAt_continuousOn_of_contDiffAt
      ((hv.contDiffAt (range_mem_nhds_isInteriorPoint hz_int)).snd) hUmem
  -- the flow box: chart preimage of the ball of initial conditions
  refine ⟨ε, (extChartAt I z).source ∩ extChartAt I z ⁻¹' ball (extChartAt I z z) r,
    fun x s => (extChartAt I z).symm (Z (extChartAt I z x) s), hε,
    isOpen_extChartAt_preimage' z isOpen_ball, ?_, ?_, ?_, ?_⟩
  · exact ⟨mem_extChartAt_source z, mem_ball_self hr⟩
  · -- `Φ x 0 = x`
    rintro x ⟨hxs, hxr⟩
    show (extChartAt I z).symm (Z (extChartAt I z x) 0) = x
    rw [(hZ _ (ball_subset_closedBall hxr)).1, PartialEquiv.left_inv _ hxs]
  · -- each `Φ x` is an integral curve of `X` on `(-ε, ε)`
    rintro x ⟨hxs, hxr⟩ t ht
    obtain ⟨-, hode, hmem⟩ := hZ _ (ball_subset_closedBall hxr)
    -- the chart-level ODE at `t`, as a genuine `HasDerivAt`
    have h := (hode t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    set f := Z (extChartAt I z x) with hf_def
    set xₜ : M := (extChartAt I z).symm (f t) with hxₜ_def
    have h' : HasDerivAt f (x := t) <| fderivWithin ℝ
        (extChartAt I z ∘ (extChartAt I xₜ).symm) (range I)
        (extChartAt I xₜ xₜ) (X xₜ) := h
    rw [← tangentCoordChange_def] at h'
    have hf3 : f t ∈ interior (extChartAt I z).target :=
      hmem t (Ioo_subset_Icc_self ht)
    have hf3' : f t ∈ (extChartAt I z).target := interior_subset hf3
    have hft1 : xₜ ∈ (extChartAt I z).source := (extChartAt I z).map_target hf3'
    have hft2 := mem_extChartAt_source (I := I) xₜ
    -- transfer through the chart, as in mathlib's
    -- `exists_isMIntegralCurveAt_of_contMDiffAt`
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h'.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I z).symm) ∘ f) (X xₜ) t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := X xₜ) hft2,
      ← tangentCoordChange_comp (x := z) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h'
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
      mem_nhds_iff.mpr ⟨interior (extChartAt I z).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, hf3⟩
    rw [← (extChartAt I z).right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  · -- joint continuity: chart in, chart flow, chart out
    have h1 : ContinuousOn (fun p : M × ℝ => (extChartAt I z (p.1), p.2))
        (((extChartAt I z).source ∩ extChartAt I z ⁻¹' ball (extChartAt I z z) r)
          ×ˢ Ioo (-ε) ε) := by
      apply ContinuousOn.prodMk _ continuous_snd.continuousOn
      exact (continuousOn_extChartAt z).comp continuous_fst.continuousOn
        fun p hp => hp.1.1
    have hmaps : MapsTo (fun p : M × ℝ => (extChartAt I z (p.1), p.2))
        (((extChartAt I z).source ∩ extChartAt I z ⁻¹' ball (extChartAt I z z) r)
          ×ˢ Ioo (-ε) ε)
        (closedBall (extChartAt I z z) r ×ˢ Icc (-ε) ε) := fun p hp =>
      ⟨ball_subset_closedBall hp.1.2, Ioo_subset_Icc_self hp.2⟩
    have h2 : ContinuousOn
        (fun p : M × ℝ => Z (extChartAt I z (p.1)) p.2)
        (((extChartAt I z).source ∩ extChartAt I z ⁻¹' ball (extChartAt I z z) r)
          ×ˢ Ioo (-ε) ε) := hZcont.comp h1 hmaps
    apply (continuousOn_extChartAt_symm z).comp h2
    intro p hp
    exact interior_subset ((hZ _ (ball_subset_closedBall hp.1.2)).2.2 _
      (Ioo_subset_Icc_self hp.2))

/-! ### The flow box near a compact set -/

/-- **Math.** **Flow of a smooth vector field near a compact set** (blueprint
`lem:vector-field-flow-near-compact`): on a Hausdorff boundaryless manifold, a
smooth vector field `X` admits near any compact set `K` an open neighbourhood
`U ⊇ K`, a uniform time `η > 0`, and a jointly continuous local flow
`Φ : U × (-η, η) → M` with `Φ x 0 = x`, each `s ↦ Φ x s` an integral curve of
`X`. Finitely many chart flow boxes (`exists_localFlowAt`) cover `K`; on
overlaps the flows agree by uniqueness of integral curves, so the glued map is
well defined and locally continuous. -/
theorem exists_localFlow_of_isCompact [T2Space M] (X : SmoothVectorField I M)
    {K : Set M} (hK : IsCompact K) :
    ∃ (η : ℝ) (U : Set M) (Φ : M → ℝ → M), 0 < η ∧ IsOpen U ∧ K ⊆ U ∧
      (∀ x ∈ U, Φ x 0 = x) ∧
      (∀ x ∈ U, IsMIntegralCurveOn (Φ x) (fun q => X q) (Ioo (-η) η)) ∧
      ContinuousOn ↿Φ (U ×ˢ Ioo (-η) η) := by
  classical
  have hX1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, X x⟩ : TangentBundle I M)) := fun p =>
    (X.smooth p).of_le (by norm_num)
  -- a flow box at every point of `K`
  choose! ε V Φ hε hVopen hVmem happly hIC hcont using
    fun z => exists_localFlowAt (I := I) X z
  -- a finite subcover of `K` by the flow-box domains
  obtain ⟨T, hTK, hKT⟩ := hK.elim_nhds_subcover V
    fun z _ => (hVopen z).mem_nhds (hVmem z)
  by_cases hT : T = ∅
  · subst hT
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
      subset_empty_iff] at hKT
    exact ⟨1, ∅, fun x _ => x, one_pos, isOpen_empty, hKT.le, fun x hx => hx.elim,
      fun x hx => hx.elim, by simp [continuousOn_empty]⟩
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  -- the uniform time and the glued domain
  set η : ℝ := T.inf' ⟨z₀, hz₀⟩ ε with hη_def
  have hηpos : 0 < η := (Finset.lt_inf'_iff _).mpr fun z _ => hε z
  have hηle : ∀ z ∈ T, η ≤ ε z := fun z hz => Finset.inf'_le _ hz
  set U : Set M := ⋃ z ∈ T, V z with hU_def
  have hUopen : IsOpen U := isOpen_biUnion fun z _ => hVopen z
  -- the glued flow: through each `x ∈ U`, use any flow box containing `x`
  have hchoice : ∀ x : M, x ∈ U → ∃ z, z ∈ T ∧ x ∈ V z := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
    exact ⟨z, hz, hxz⟩
  set Ψ : M → ℝ → M := fun x => if hx : x ∈ U then Φ (hchoice x hx).choose x
    else fun _ => x with hΨ_def
  -- basic properties of the choice
  have hΨeq : ∀ x (hx : x ∈ U), Ψ x = Φ (hchoice x hx).choose x := fun x hx => by
    rw [hΨ_def]; exact dif_pos hx
  have hΨIC : ∀ x ∈ U, IsMIntegralCurveOn (Ψ x) (fun q => X q) (Ioo (-η) η) := by
    intro x hx
    obtain ⟨hzT, hxz⟩ := (hchoice x hx).choose_spec
    rw [hΨeq x hx]
    exact (hIC _ x hxz).mono (Ioo_subset_Ioo (neg_le_neg (hηle _ hzT)) (hηle _ hzT))
  have hΨ0 : ∀ x ∈ U, Ψ x 0 = x := by
    intro x hx
    obtain ⟨hzT, hxz⟩ := (hchoice x hx).choose_spec
    rw [hΨeq x hx]
    exact happly _ x hxz
  -- on any flow box of the cover, the glued flow agrees with the box flow, by
  -- uniqueness of integral curves
  have hagree : ∀ z ∈ T, ∀ x ∈ U, x ∈ V z →
      EqOn (Ψ x) (Φ z x) (Ioo (-η) η) := by
    intro z hzT x hxU hxV
    refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (Set.mem_Ioo.mpr ⟨neg_neg_iff_pos.mpr hηpos, hηpos⟩) hX1
      (hΨIC x hxU)
      ((hIC z x hxV).mono
        (Ioo_subset_Ioo (neg_le_neg (hηle _ hzT)) (hηle _ hzT))) ?_
    rw [hΨ0 x hxU, happly z x hxV]
  refine ⟨η, U, Ψ, hηpos, hUopen, hKT, hΨ0, hΨIC, ?_⟩
  -- joint continuity: near any `(x₀, s₀)`, the glued flow agrees with the
  -- continuous flow of a box containing `x₀`
  intro p hp
  obtain ⟨hpU, hps⟩ := hp
  obtain ⟨z, hzT, hpz⟩ := hchoice p.1 hpU
  have hopen : IsOpen ((U ∩ V z) ×ˢ Ioo (-η) η) :=
    (hUopen.inter (hVopen z)).prod isOpen_Ioo
  have hmem : p ∈ (U ∩ V z) ×ˢ Ioo (-η) η := ⟨⟨hpU, hpz⟩, hps⟩
  have hΦcont : ContinuousAt ↿(Φ z) p := by
    refine (hcont z).continuousAt ((((hVopen z).prod isOpen_Ioo).mem_nhds) ?_)
    exact ⟨hpz, Ioo_subset_Ioo (neg_le_neg (hηle _ hzT)) (hηle _ hzT) hps⟩
  refine (hΦcont.congr ?_).continuousWithinAt
  filter_upwards [hopen.mem_nhds hmem] with q hq
  exact (hagree z hzT q.1 hq.1.1 hq.1.2 hq.2).symm

/-! ### The forward difference maximum property -/

/-- **Math.** The flow box discharges the `IsLocalFlow` hypothesis bundle of
the maximum principle: if `X` is a smooth vector field with `X(tt) = 1` and
`F` is smooth, then near any compact set there is a local flow at unit
`tt`-speed along which `F` differentiates to `X(F)`. Blueprint
`lem:vector-field-flow-near-compact` in the form consumed by
`prop:forward-difference-maximum`. -/
theorem exists_isLocalFlow_of_isCompact [T2Space M] (X : SmoothVectorField I M)
    {tt F : M → ℝ} (htt : ContMDiff I 𝓘(ℝ, ℝ) ∞ tt)
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) (hXtt : ∀ x, X.dir tt x = 1)
    {K : Set M} (hK : IsCompact K) :
    ∃ (η : ℝ) (U : Set M) (Φ : M → ℝ → M), K ⊆ U ∧
      IsLocalFlow tt F (X.dir F) U η Φ := by
  obtain ⟨η, U, Φ, hη, hUopen, hKU, h0, hIC, hcont⟩ :=
    exists_localFlow_of_isCompact X hK
  have hMF : ∀ x ∈ U, ∀ s ∈ Ioo (-η) η, HasMFDerivAt 𝓘(ℝ, ℝ) I (Φ x) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (Φ x s))) := fun x hx s hs =>
    (hIC x hx s hs).hasMFDerivAt (Ioo_mem_nhds hs.1 hs.2)
  have hderivF : ∀ x ∈ U, ∀ s ∈ Ioo (-η) η,
      HasDerivAt (fun r => F (Φ x r)) (X.dir F (Φ x s)) s := fun x hx s hs =>
    hasDerivAt_comp_of_hasMFDerivAt hF (hMF x hx s hs)
  refine ⟨η, U, Φ, hKU, hη, hUopen, h0, ?_, hderivF, hcont⟩
  -- `tt` moves at unit speed along the flow: `(tt ∘ Φ x)' ≡ 1`, so
  -- `tt (Φ x s) - tt x - s` vanishes identically on the interval
  intro x hx s hs
  have hderiv : ∀ u ∈ Ioo (-η) η,
      HasDerivWithinAt (fun r => tt (Φ x r) - (tt x + r)) 0 (Ioo (-η) η) u := by
    intro u hu
    have h1 : HasDerivAt (fun r => tt (Φ x r)) 1 u := by
      have := hasDerivAt_comp_of_hasMFDerivAt htt (hMF x hx u hu)
      rwa [show mfderiv I 𝓘(ℝ, ℝ) tt (Φ x u) (X (Φ x u)) = 1 from hXtt (Φ x u)]
        at this
    have h2 : HasDerivAt (fun r : ℝ => tt x + r) 1 u :=
      (hasDerivAt_id u).const_add (tt x)
    simpa using (h1.sub h2).hasDerivWithinAt
  have h0mem : (0 : ℝ) ∈ Ioo (-η) η := ⟨neg_neg_iff_pos.mpr hη, hη⟩
  have hbound : ‖(tt (Φ x s) - (tt x + s)) - (tt (Φ x 0) - (tt x + 0))‖ ≤
      0 * ‖s - 0‖ :=
    (convex_Ioo (-η) η).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => tt (Φ x r) - (tt x + r)) (f' := fun _ => 0)
      hderiv (fun u _ => by simp) h0mem hs
  rw [zero_mul, h0 x hx] at hbound
  have hzero := norm_le_zero_iff.mp hbound
  linarith

/-- **Math.** **Forward difference maximum property** (Morgan–Tian,
Proposition 2.23; blueprint `prop:forward-difference-maximum`). Let `M` be a
smooth (Hausdorff, boundaryless) manifold, `X` a smooth vector field, and
`tt, F : M → ℝ` smooth with `X(tt) = 1`. Suppose the set `𝒵` of fibrewise
maximizers of `F` is compact and every fibre `tt⁻¹(t)`, `t ∈ [a, b]`, attains
its maximum. If `X(F) ≤ ψ(tt, F)` on `𝒵` with `ψ` `C¹`, and `G` solves
`G' = ψ(t, G)` with `F_max(a) ≤ G(a)`, then `F_max(t) ≤ G(t)` on `[a, b]`. -/
theorem levelMax_le_of_dir_le [T2Space M] (X : SmoothVectorField I M)
    {tt F : M → ℝ} (htt : ContMDiff I 𝓘(ℝ, ℝ) ∞ tt)
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) (hXtt : ∀ x, X.dir tt x = 1) {a b : ℝ}
    (hZc : IsCompact (levelMaximizers tt F))
    (hex : ∀ t ∈ Icc a b, ∃ x ∈ levelMaximizers tt F, tt x = t)
    {ψ : ℝ → ℝ → ℝ} (hψ : ContDiffOn ℝ 1 (uncurry ψ) (Icc a b ×ˢ (univ : Set ℝ)))
    (hψbound : ∀ x ∈ levelMaximizers tt F, X.dir F x ≤ ψ (tt x) (F x))
    {G : ℝ → ℝ} (hG : ContinuousOn G (Icc a b))
    (hG' : ∀ t ∈ Ico a b, HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (hab : levelMax tt F a ≤ G a) :
    ∀ t ∈ Icc a b, levelMax tt F t ≤ G t := by
  obtain ⟨η, U, Φ, hKU, hflow⟩ :=
    exists_isLocalFlow_of_isCompact X htt hF hXtt hZc
  exact levelMax_le_of_isLocalFlow hZc hKU hflow htt.continuous
    (X.dir_contMDiff hF).continuous hex hψ hψbound hG hG' hab

end MorganTianLib

end
