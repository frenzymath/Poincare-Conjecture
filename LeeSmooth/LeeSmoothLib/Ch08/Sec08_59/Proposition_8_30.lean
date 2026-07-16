import LeeSmoothLib.Ch08.Sec08_59.Definition_8_59_extra_1
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
import LeeSmoothLib.Ch08.Sec08_57.Proposition_8_16
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology ContDiff Manifold

noncomputable section

section

universe u𝕜 uE uE' uH uH' uM uN

-- Domain sampling pass:
-- * primary domain: smooth vector fields on manifolds and their Lie bracket;
-- * source-facing owner: `VectorField.f_related`;
-- * source-facing derived API for that owner: `f_related_iff_mfderiv_comp_eq`;
-- * core/canonical bracket owner: `VectorField.mlieBracket`, exposed via `⁅X, Y⁆`;
-- * smoothness API for the bracket: `ContMDiff.mlieBracket_vectorField`.
-- Primitive data is only the map `F` and the vector fields `Xᵢ`, `Yᵢ`; smoothness and
-- `f_related` are derived hypotheses, so this file should stay a thin bridge theorem over the
-- existing owners rather than introducing any local wrapper API. In particular, completeness of
-- the source model space belongs to one proof route for pullback naturality, not to the public
-- `f_related` statement itself.

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E' H'}
  [IsManifold I ∞ M]
  [IsManifold J ∞ N]

-- Semantic recall note: `lean_leansearch` confirmed the ambient bracket API
-- (`VectorField.mpullback_mlieBracketWithin`, `VectorField.mlieBracket`), and the item still uses
-- the chapter predicate `VectorField.f_related`, its characterization
-- `f_related_iff_mfderiv_comp_eq`, and `ContMDiff.mlieBracket_vectorField`.

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Proposition 8.30: applying `mfderiv% g` after an `F`-related vector field is just
the chain rule plus the defining pointwise relatedness identity. -/
lemma fRelated_mfderivCompEq
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ∞ P]
    {F : M → N}
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q}
    (hXY : VectorField.f_related F X Y) (p : M) {g : N → P}
    (hg : ContMDiffAt J K ∞ g (F p)) :
    mfderiv% (fun x ↦ g (F x)) p (X p) =
      mfderiv% g (F p) (Y (F p)) := by
  have hgDiff : MDifferentiableAt J K g (F p) :=
    hg.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hFDiff : MDifferentiableAt I J F p := by
    have hFcont : ContMDiffAt I J ∞ F p := hXY.contMDiff.contMDiffAt
    exact hFcont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  -- Differentiate `g ∘ F` and then rewrite the pushed-forward tangent vector via `f_related`.
  calc
    mfderiv% (fun x ↦ g (F x)) p (X p)
        = mfderiv% g (F p) (mfderiv I J F p (X p)) := by
            have hComp :
                mfderiv I K (g ∘ F) p =
                  (mfderiv J K g (F p)).comp (mfderiv I J F p) :=
              mfderiv_comp p hgDiff hFDiff
            simpa [Function.comp] using congrArg (fun A ↦ A (X p)) hComp
    _ = mfderiv% g (F p) (Y (F p)) := by
          rw [VectorField.f_related_apply hXY p]

/-- Helper for Proposition 8.30: if `g` is smooth and `Y` is a smooth vector field, then the
vector-space-valued field `q ↦ mfderiv% g q (Y q)` is smooth at the basepoint. -/
lemma contMDiffAt_mfderiv_applyField
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {g : N → E''}
    {Y : ∀ q : N, TangentSpace J q}
    {p : N}
    (hg : ContMDiffAt J 𝓘(𝕜, E'') ∞ g p)
    (hY : ContMDiffAt J J.tangent ∞ (T% Y) p) :
    ContMDiffAt J 𝓘(𝕜, E'') ∞
      (fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y q))) p := by
  let rhs : N → E' →L[𝕜] E'' :=
    fun x ↦ (mvfderiv J g x) ∘L ((trivializationAt E' (TangentSpace J) p).symmL 𝕜 x)
  have hBundleCoords :
      (fun x ↦
        ContinuousLinearMap.inCoordinates E' (TangentSpace J) E'' (fun _ : N ↦ E'') p x p x
          (mvfderiv J g x)) =ᶠ[𝓝 p] rhs := by
    -- Read the hom-bundle coordinates using the fixed tangent trivialization at `p`.
    have hbase :
        {x : N | x ∈ (trivializationAt E' (TangentSpace J) p).baseSet} ∈ 𝓝 p :=
      (trivializationAt E' (TangentSpace J) p).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' p)
    filter_upwards [hbase] with x hx
    rw [ContinuousLinearMap.inCoordinates_eq hx (by simp)]
    -- The codomain bundle is trivial, so its chart-side linear map is the identity.
    ext v
    simp [rhs, mvfderiv]
  have hTangentCoords :
      inTangentCoordinates J 𝓘(𝕜, E'') id g (fun q ↦ mfderiv% g q) p =ᶠ[𝓝 p] rhs := by
    -- Replace the fixed-base tangent coordinates from `mfderiv_const` by the tangent-bundle
    -- trivialization used in the hom-bundle application theorem.
    have hSource : (extChartAt J p).source ∈ 𝓝 p := extChartAt_source_mem_nhds p
    filter_upwards [hSource] with x hx
    have hEq :
        inTangentCoordinates J 𝓘(𝕜, E'') id g (fun q ↦ mfderiv% g q) p x =
          (mfderiv% (extChartAt 𝓘(𝕜, E'') (g p)) (g x)) ∘L (mfderiv% g x) ∘L
            (mfderiv[Set.range J] (extChartAt J p).symm (extChartAt J p x)) := by
      exact inTangentCoordinates_eq_mfderiv_comp (by simpa [extChartAt] using hx) (by simp)
    have hSymmL :
        (trivializationAt E' (TangentSpace J) p).symmL 𝕜 x =
          mfderiv[Set.range J] (extChartAt J p).symm (extChartAt J p x) := by
      have hSymmL' :
          (trivializationAt E' (TangentSpace J) p).symmL 𝕜 x =
            mfderiv[Set.range J] (extChartAt J p).symm (extChartAt J p x) :=
        TangentBundle.symmL_trivializationAt (by simpa [extChartAt] using hx)
      simpa [extChartAt] using hSymmL'
    simpa [rhs, mvfderiv, hSymmL] using hEq
  have hphi :
      ContMDiffAt J (J.prod 𝓘(𝕜, E' →L[𝕜] E'')) ∞
        (fun q ↦ Bundle.TotalSpace.mk' (E' →L[𝕜] E'') q (mvfderiv J g q)) p := by
    -- `mfderiv_const` gives smoothness of the derivative in fixed-base tangent coordinates.
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    exact (hg.mfderiv_const (by simp)).congr_of_eventuallyEq
      (hBundleCoords.trans hTangentCoords.symm)
  have happly := hphi.clm_bundle_apply hY
  -- Evaluate the smooth hom-bundle section on the smooth vector-field section `T% Y`.
  rw [Bundle.contMDiffAt_section] at happly
  simpa [mvfderiv] using happly

/-- Helper for Proposition 8.30: on the preferred chart at `p`, the chart-side derivative of
`g ∘ (extChartAt J p).symm` applied to the chart pullback of `Y` is the manifold derivative field
of `g` written in model-space coordinates. -/
private lemma chartPullbackDerivative_pointwise
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {g : N → E''}
    {Y : ∀ q : N, TangentSpace J q}
    {p : N}
    {x : E'}
    (hx : x ∈ (extChartAt J p).target)
    (hgx : MDifferentiableAt J 𝓘(𝕜, E'') g ((extChartAt J p).symm x)) :
    let ψ := extChartAt J p
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
    fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y' x) =
      NormedSpace.fromTangentSpace (g (ψ.symm x)) (mfderiv% g (ψ.symm x) (Y (ψ.symm x))) := by
  let ψ := extChartAt J p
  let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
  have hxRange : x ∈ Set.range J := extChartAt_target_subset_range p hx
  have hUnique : UniqueMDiffWithinAt 𝓘(𝕜, E') (Set.range J) x :=
    (J.uniqueDiffOn.uniqueDiffWithinAt hxRange).uniqueMDiffWithinAt
  have hψ :
      MDifferentiableWithinAt 𝓘(𝕜, E') J ψ.symm (Set.range J) x := by
    simpa [ψ] using mdifferentiableWithinAt_extChartAt_symm hx
  have hgWithin : MDifferentiableWithinAt J 𝓘(𝕜, E'') g Set.univ (ψ.symm x) :=
    hgx.mdifferentiableWithinAt
  have hComp :
      mfderiv[Set.range J] (g ∘ ψ.symm) x =
        (mfderiv% g (ψ.symm x)).comp (mfderiv[Set.range J] ψ.symm x) := by
    -- Differentiate the fixed-chart composition once in manifold form before returning to the
    -- vector-space derivative.
    simpa [ψ] using
      (mfderivWithin_comp x hgWithin hψ (show Set.range J ⊆ ψ.symm ⁻¹' Set.univ from
        by intro y hy; simp) hUnique)
  -- The chart pullback vector is exactly the inverse derivative applied to `Y`, so the chain rule
  -- collapses after cancelling the invertible chart-inverse derivative.
  have hPoint :
      mfderiv[Set.range J] (g ∘ ψ.symm) x (Y' x) =
        NormedSpace.fromTangentSpace (g (ψ.symm x)) (mfderiv% g (ψ.symm x) (Y (ψ.symm x))) := by
    dsimp [Y']
    rw [VectorField.mpullbackWithin_apply, hComp]
    change
      mfderiv% g (ψ.symm x)
          ((mfderiv[Set.range J] ψ.symm x)
            ((mfderiv[Set.range J] ψ.symm x).inverse (Y (ψ.symm x)))) =
        NormedSpace.fromTangentSpace (g (ψ.symm x)) (mfderiv% g (ψ.symm x) (Y (ψ.symm x)))
    rw [(isInvertible_mfderivWithin_extChartAt_symm hx).self_apply_inverse]
    rfl
  simpa [ψ, mfderivWithin_eq_fderivWithin] using hPoint

/-- Helper for Proposition 8.30: near the preferred chart at `p`, the chart-side derivative term
is eventually equal to the manifold derivative field of `g` pulled back along the chart inverse. -/
private lemma chartPullbackDerivative_eventuallyEq
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {g : N → E''}
    {Y : ∀ q : N, TangentSpace J q}
    {p : N}
    (hg : ContMDiffAt J 𝓘(𝕜, E'') ∞ g p) :
    let ψ := extChartAt J p
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
    (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y' x))
      =ᶠ[𝓝[Set.range J] (ψ p)] fun x ↦
        NormedSpace.fromTangentSpace (g (ψ.symm x)) (mfderiv% g (ψ.symm x) (Y (ψ.symm x))) := by
  let ψ := extChartAt J p
  let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
  have hgOne : ContMDiffAt J 𝓘(𝕜, E'') 1 g p := hg.of_le (by simp)
  have hMdiffNearP : ∀ᶠ q in 𝓝 p, MDifferentiableAt J 𝓘(𝕜, E'') g q := by
    have hContDiffNear :
        ∀ᶠ q in 𝓝 p, ContMDiffAt J 𝓘(𝕜, E'') 1 g q :=
      (show
        ContMDiffAt J 𝓘(𝕜, E'') 1 g p ↔ ∀ᶠ q in 𝓝 p, ContMDiffAt J 𝓘(𝕜, E'') 1 g q from
          contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hgOne
    filter_upwards [hContDiffNear] with q hq
    exact hq.mdifferentiableAt one_ne_zero
  have hMdiffSet : { q | MDifferentiableAt J 𝓘(𝕜, E'') g q } ∈ 𝓝 p := hMdiffNearP
  have hbase : ψ.symm (ψ p) = p := by
    simpa [ψ] using extChartAt_to_inv p
  have hMdiffSetAtBase :
      { q | MDifferentiableAt J 𝓘(𝕜, E'') g q } ∈ 𝓝 (ψ.symm (ψ p)) := by
    simpa [hbase] using hMdiffSet
  have hMdiffNearChart :
      ∀ᶠ x in 𝓝[Set.range J] (ψ p), MDifferentiableAt J 𝓘(𝕜, E'') g (ψ.symm x) :=
    (continuousAt_extChartAt_symm p).continuousWithinAt.preimage_mem_nhdsWithin
      hMdiffSetAtBase
  -- Combine target-membership and differentiability events, then apply the pointwise bridge.
  filter_upwards [extChartAt_target_mem_nhdsWithin p, hMdiffNearChart] with x hx hxDiff
  simpa [ψ, Y'] using chartPullbackDerivative_pointwise hx hxDiff

/-- Helper for Proposition 8.30: at the basepoint `ψ p`, the chart-side derivative term is the
manifold derivative of `g` applied to `Y p`, written in model-space coordinates. -/
private lemma chartPullbackDerivativeAtBase
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {g : N → E''}
    {Y : ∀ q : N, TangentSpace J q}
    {p : N}
    (hg : MDifferentiableAt J 𝓘(𝕜, E'') g p) :
    let ψ := extChartAt J p
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
    fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) (ψ p) (Y' (ψ p)) =
      NormedSpace.fromTangentSpace (g p) (mfderiv% g p (Y p)) := by
  let ψ := extChartAt J p
  let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
  -- Evaluate the pointwise normalization at the chart basepoint `ψ p`.
  have hAtBase :
      fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) (ψ p) (Y' (ψ p)) =
        NormedSpace.fromTangentSpace (g (ψ.symm (ψ p)))
          (mfderiv% g (ψ.symm (ψ p)) (Y (ψ.symm (ψ p)))) := by
    exact chartPullbackDerivative_pointwise (mem_extChartAt_target p) (by simpa [ψ] using hg)
  have hbase : ψ.symm (ψ p) = p := by
    simpa [ψ] using extChartAt_to_inv p
  have hRight :
      NormedSpace.fromTangentSpace (g (ψ.symm (ψ p)))
          (mfderiv% g (ψ.symm (ψ p)) (Y (ψ.symm (ψ p)))) =
        NormedSpace.fromTangentSpace (g p) (mfderiv% g p (Y p)) := by
    rw [hbase]
  simpa [ψ] using hAtBase.trans hRight

/-- Helper for Proposition 8.30: an eventual chart-space normalization near `ψ p` converts the
basepoint `fderivWithin` term into the manifold derivative of the normalized field. -/
private lemma chartPullbackDerivativeTermAtBase
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {U : E' → E''} {U'' : N → E''}
    {Z : ∀ q : N, TangentSpace J q}
    {p : N}
    (hU : U =ᶠ[𝓝[Set.range J] ((extChartAt J p) p)] fun x ↦ U'' ((extChartAt J p).symm x))
    (hU'' : MDifferentiableAt J 𝓘(𝕜, E'') U'' p) :
    let ψ := extChartAt J p
    let Z' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Z (Set.range J)
    fderivWithin 𝕜 U (Set.range J) (ψ p) (Z' (ψ p)) =
      NormedSpace.fromTangentSpace (U'' p) (mfderiv% U'' p (Z p)) := by
  let ψ := extChartAt J p
  let Z' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Z (Set.range J)
  have hDeriv :
      fderivWithin 𝕜 U (Set.range J) (ψ p) =
        fderivWithin 𝕜 (fun x ↦ U'' (ψ.symm x)) (Set.range J) (ψ p) :=
    Filter.EventuallyEq.fderivWithin_eq_of_mem hU (Set.mem_range_self _)
  have hEval :
      fderivWithin 𝕜 U (Set.range J) (ψ p) (Z' (ψ p)) =
        fderivWithin 𝕜 (fun x ↦ U'' (ψ.symm x)) (Set.range J) (ψ p) (Z' (ψ p)) :=
    congrArg (fun A : E' →L[𝕜] E'' ↦ A (Z' (ψ p))) hDeriv
  -- Replace the ambient chart-space function by the pulled-back manifold function and then apply
  -- the basepoint normalization already established for chart-side derivatives.
  calc
    fderivWithin 𝕜 U (Set.range J) (ψ p) (Z' (ψ p)) =
        fderivWithin 𝕜 (fun x ↦ U'' (ψ.symm x)) (Set.range J) (ψ p) (Z' (ψ p)) := hEval
    _ = NormedSpace.fromTangentSpace (U'' p) (mfderiv% U'' p (Z p)) := by
      simpa [ψ, Z'] using chartPullbackDerivativeAtBase hU''

omit [IsManifold J ∞ N] in
/-- Helper for Proposition 8.30: the preferred chart inverse is `C^2` within `range J` at the
basepoint chart coordinate. -/
private lemma extChartAtSymm_contMDiffWithinAt_two
    {p : N} :
    ContMDiffWithinAt 𝓘(𝕜, E') J 2 (extChartAt J p).symm (Set.range J) ((extChartAt J p) p) :=
  by
  -- The preferred chart inverse is smooth on `range J`, hence in particular `C²` at the basepoint.
  simpa using
    (show
      ContMDiffWithinAt 𝓘(𝕜, E') J 2 (extChartAt J p).symm (Set.range J) ((extChartAt J p) p) from
        contMDiffWithinAt_extChartAt_symm_range_self p)

/-- Helper for Proposition 8.30: at any source point of the preferred chart, the inverse of the
chart-inverse derivative is the derivative of the chart itself. -/
private lemma extChartAtSymm_inverse_eq_mfderiv
    {p z : N} (hz : z ∈ (extChartAt J p).source) :
    (mfderiv[Set.range J] (extChartAt J p).symm ((extChartAt J p) z)).inverse =
      mfderiv% (extChartAt J p) z := by
  -- Cancel the chart and chart-inverse derivatives using the standard preferred-chart identities.
  apply ContinuousLinearMap.inverse_eq
  · simpa using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hz
  · simpa using
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hz

/-- Helper for Proposition 8.30: the preferred chart basepoint lies in the closure of the
interior of `Set.range J`. -/
private lemma extChartAtBase_mem_closureInterior_range
    {p : N} :
    (extChartAt J p) p ∈ closure (interior (Set.range J)) := by
  -- The preferred chart basepoint is visibly in `range J`, and `range J` is the closure of its
  -- interior for a model with corners.
  exact J.range_subset_closure_interior (Set.mem_range_self _)

/-- Helper for Proposition 8.30: a fixed preferred chart is smooth at every point of its source. -/
private lemma contMDiffAt_extChartAt_of_mem_source
    {p q : N} (hq : q ∈ (extChartAt J p).source) :
    ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J p) q := by
  -- Rewrite the extended-chart source to the ordinary chart source and reuse the atlas API.
  have hqChart : q ∈ (chartAt H' p).source := by
    simpa [extChartAt_source] using hq
  have hChart : ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J p) q := contMDiffAt_extChartAt' hqChart
  simpa [extChartAt_source] using hChart

/-- Helper for Proposition 8.30: the fixed trivialization of the trivial `E''`-bundle acts by the
identity continuous linear map on every fiber. -/
private lemma trivialBundle_continuousLinearMapAt_id
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    (x y : E'') :
    (trivializationAt E'' (fun _ : E'' ↦ E'') x).continuousLinearMapAt 𝕜 y =
      (1 : E'' →L[𝕜] E'') := by
  -- The trivial bundle uses the canonical trivialization, whose fiber map is the identity.
  ext v
  simp

/-- Helper for Proposition 8.30: on the target of the preferred chart, the chart pullback field
is the explicit `mfderiv% ψ` expression written in model-space coordinates. -/
private lemma chartPullbackFieldPointwise
    {Y : ∀ q : N, TangentSpace J q}
    {p : N}
    {x : E'}
    (hx : x ∈ (extChartAt J p).target) :
    let ψ := extChartAt J p
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
    Y' x =
      NormedSpace.fromTangentSpace (ψ (ψ.symm x)) (mfderiv% ψ (ψ.symm x) (Y (ψ.symm x))) := by
  let ψ := extChartAt J p
  let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
  -- Route correction: use the target-membership chart inverse identities directly, so the
  -- pullback term is normalized in the exact `mpullbackWithin_apply` spelling at `x`.
  have hrightInv : ψ (ψ.symm x) = x := PartialEquiv.right_inv ψ hx
  have hInverse :
      (mfderiv[Set.range J] ψ.symm x).inverse = mfderiv% ψ (ψ.symm x) := by
    apply ContinuousLinearMap.inverse_eq
    · simpa [ψ, hrightInv] using
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hx
    · simpa [ψ, hrightInv] using
        mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx
  -- After replacing the inverse derivative by the chart derivative, the remaining coercion is
  -- exactly `fromTangentSpace` on the model manifold.
  simpa [Y', ψ, hrightInv, VectorField.mpullbackWithin_apply] using
    congrArg
      (fun L ↦
        NormedSpace.fromTangentSpace (ψ (ψ.symm x)) (L (Y (ψ.symm x))))
      hInverse

/-- Helper for Proposition 8.30: near the preferred chart of `p`, the chart pullback field itself
coincides with the explicit `mfderiv% ψ` expression in model-space coordinates. -/
private lemma chartPullbackField_eventuallyEqAtBase
    {Y : ∀ q : N, TangentSpace J q}
    {p : N} :
    let ψ := extChartAt J p
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
    Y' =ᶠ[𝓝[Set.range J] (ψ p)] fun x ↦
      NormedSpace.fromTangentSpace (ψ (ψ.symm x)) (mfderiv% ψ (ψ.symm x) (Y (ψ.symm x))) := by
  let ψ := extChartAt J p
  let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
  -- Upgrade the pointwise chart identity to an equality on a neighborhood within `range J`.
  filter_upwards [extChartAt_target_mem_nhdsWithin p] with x hx
  simpa [ψ, Y'] using chartPullbackFieldPointwise hx

/-- Helper for Proposition 8.30: the preferred-chart pullback of a smooth vector field is
differentable within `Set.range J` at the basepoint `ψ p`, without any completeness hypothesis on
the chart model space. -/
private lemma chartPullbackDifferentiableWithinAtBase
    {Y : ∀ q : N, TangentSpace J q}
    {p : N}
    (hY : ContMDiffAt J J.tangent ∞ (T% Y) p) :
    let ψ := extChartAt J p
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
    DifferentiableWithinAt 𝕜 Y' (Set.range J) (ψ p) := by
  let ψ := extChartAt J p
  let Y' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y (Set.range J)
  let Z : N → E' :=
    fun q ↦ NormedSpace.fromTangentSpace (ψ q) (mfderiv% ψ q (Y q))
  have hψCont : ContMDiffAt J 𝓘(𝕜, E') ∞ ψ p := by
    simpa [ψ] using
      (show ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J p) p from contMDiffAt_extChartAt)
  have hZ : ContMDiffAt J 𝓘(𝕜, E') ∞ Z p := by
    -- Smoothness of the explicit chart-side field comes from the derivative-field helper above.
    simpa [ψ, Z] using
      contMDiffAt_mfderiv_applyField hψCont hY
  have hZChart :
      ContMDiffWithinAt 𝓘(𝕜, E') 𝓘(𝕜, E') ∞ (fun x ↦ Z (ψ.symm x)) (Set.range J) (ψ p) := by
    -- Pull the smooth manifold-side field back along the preferred chart inverse.
    have hψ : ContMDiffWithinAt 𝓘(𝕜, E') J ∞ ψ.symm (Set.range J) (ψ p) := by
      simpa [ψ] using
        (show
          ContMDiffWithinAt 𝓘(𝕜, E') J ∞ (extChartAt J p).symm (Set.range J) ((extChartAt J p) p) from
            contMDiffWithinAt_extChartAt_symm_range_self p)
    exact hZ.comp_contMDiffWithinAt_of_eq hψ (by simp [ψ])
  have hExplicit :
      DifferentiableWithinAt 𝕜 (fun x ↦ Z (ψ.symm x)) (Set.range J) (ψ p) :=
    (hZChart.mdifferentiableWithinAt (by simp : (∞ : ℕ∞ω) ≠ 0)).differentiableWithinAt
  have hBase : ψ p ∈ Set.range J := Set.mem_range_self _
  have hFieldEq :
      Y' =ᶠ[𝓝[Set.range J] (ψ p)] fun x ↦
        NormedSpace.fromTangentSpace (ψ (ψ.symm x)) (mfderiv% ψ (ψ.symm x) (Y (ψ.symm x))) :=
    chartPullbackField_eventuallyEqAtBase
  -- Replace the pullback field by its explicit chart-side formula near the basepoint.
  exact
    (Filter.EventuallyEq.differentiableWithinAt_iff_of_mem hFieldEq hBase).2 hExplicit

/-- Helper for Proposition 8.30: at the preferred chart of `p`, the pullback of `⁅Y₁, Y₂⁆`
coincides with the Euclidean `lieBracketWithin` of the two chart pullbacks. -/
private lemma chartPullbackBracketAt_eq_lieBracketWithinAt
    {Y₁ Y₂ : ∀ q : N, TangentSpace J q}
    {p : N}
    (_hY₁ : ContMDiffAt J J.tangent ∞ (T% Y₁) p)
    (_hY₂ : ContMDiffAt J J.tangent ∞ (T% Y₂) p) :
    let ψ := extChartAt J p
    let Y₁' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₁ (Set.range J)
    let Y₂' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₂ (Set.range J)
    VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm ⁅Y₁, Y₂⁆ (Set.range J) (ψ p) =
      VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) (ψ p) := by
  let ψ := extChartAt J p
  let Y₁' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₁ (Set.range J)
  let Y₂' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₂ (Set.range J)
  letI : TopologicalSpace (TangentSpace 𝓘(𝕜, E') (ψ p)) := by
    change TopologicalSpace E'
    infer_instance
  letI : ChartedSpace E' (TangentSpace 𝓘(𝕜, E') (ψ p)) := by
    change ChartedSpace E' E'
    infer_instance
  letI : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E') (ψ p)) := by
    change NormedAddCommGroup E'
    infer_instance
  letI : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E') (ψ p)) := by
    change NormedSpace 𝕜 E'
    infer_instance
  have hψp : ψ.symm (ψ p) = p := by
    simpa [ψ] using extChartAt_to_inv p
  have hInv : (mfderiv[Set.range J] ψ.symm (ψ p)).inverse = mfderiv% ψ p := by
    -- Normalize the inverse derivative of the preferred chart inverse at the chart basepoint.
    apply ContinuousLinearMap.inverse_eq
    · simpa [ψ] using
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (mem_extChartAt_source p)
    · simpa [ψ] using
        mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (mem_extChartAt_source p)
  have hChartSet : ((Set.univ : Set E') ∩ Set.range (↑J)) = Set.range (↑J) := by
    ext y
    simp
  have hBracketRaw :
      ⁅Y₁, Y₂⁆ p =
        (mfderiv% ψ p).inverse
          (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' ((Set.univ : Set E') ∩ Set.range (↑J)) (ψ p)) := by
    simpa [VectorField.bracket_eq_mlieBracket, ψ, Y₁', Y₂', Set.preimage_univ] using
      (show VectorField.mlieBracketWithin J Y₁ Y₂ Set.univ p =
          (mfderiv% (extChartAt J p) p).inverse
            (VectorField.lieBracketWithin 𝕜
              (VectorField.mpullbackWithin 𝓘(𝕜, E') J (extChartAt J p).symm Y₁ (Set.range J))
              (VectorField.mpullbackWithin 𝓘(𝕜, E') J (extChartAt J p).symm Y₂ (Set.range J))
              (((extChartAt J p).symm ⁻¹' Set.univ : Set E') ∩ Set.range (↑J))
              ((extChartAt J p) p)) from
        VectorField.mlieBracketWithin_apply)
  have hLieSet :
      VectorField.lieBracketWithin 𝕜 Y₁' Y₂' ((Set.univ : Set E') ∩ Set.range (↑J)) (ψ p) =
        VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range (↑J)) (ψ p) := by
    simpa [hChartSet]
  have hBracketApply :
      ⁅Y₁, Y₂⁆ p =
        (mfderiv% ψ p).inverse (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) (ψ p)) := by
    calc
      ⁅Y₁, Y₂⁆ p =
          (mfderiv% ψ p).inverse
            (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' ((Set.univ : Set E') ∩ Set.range (↑J)) (ψ p)) :=
        hBracketRaw
      _ =
          (mfderiv% ψ p).inverse (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) (ψ p)) := by
            exact congrArg ((mfderiv% ψ p).inverse) hLieSet
  -- Rewrite the pullback of the manifold bracket into chart coordinates and cancel the chart
  -- derivative against the bracket formula at `p`.
  calc
    VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm ⁅Y₁, Y₂⁆ (Set.range J) (ψ p)
        = (mfderiv[Set.range J] ψ.symm (ψ p)).inverse (⁅Y₁, Y₂⁆ (ψ.symm (ψ p))) := by
            rw [VectorField.mpullbackWithin_apply]
    _ = mfderiv% ψ p (⁅Y₁, Y₂⁆ p) := by
          rw [hInv, hψp]
    _ = mfderiv% ψ p
          ((mfderiv% ψ p).inverse (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) (ψ p))) := by
            rw [hBracketApply]
    _ = VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) (ψ p) := by
          rw [(isInvertible_mfderiv_extChartAt (mem_extChartAt_source p)).self_apply_inverse]
          rfl

/-- Helper for Proposition 8.30: the manifold Lie bracket acts on a smooth map by the commutator
of the first-order differential operators induced by the vector fields. -/
private lemma mfderiv_apply_mlieBracket_eq_commutator
    [IsRCLikeNormedField 𝕜]
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {g : N → E''}
    {Y₁ Y₂ : ∀ q : N, TangentSpace J q}
    {p : N}
    (hg : ContMDiffAt J 𝓘(𝕜, E'') ∞ g p)
    (hY₁ : ContMDiffAt J J.tangent ∞ (T% Y₁) p)
    (hY₂ : ContMDiffAt J J.tangent ∞ (T% Y₂) p) :
    NormedSpace.fromTangentSpace (g p) (mfderiv% g p (⁅Y₁, Y₂⁆ p)) =
      NormedSpace.fromTangentSpace
          (NormedSpace.fromTangentSpace (g p) (mfderiv% g p (Y₂ p)))
          (mfderiv% (fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y₂ q))) p
            (Y₁ p)) -
      NormedSpace.fromTangentSpace
          (NormedSpace.fromTangentSpace (g p) (mfderiv% g p (Y₁ p)))
          (mfderiv% (fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y₁ q))) p
            (Y₂ p)) := by
  let ψ := extChartAt J p
  let Y₁' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₁ (Set.range J)
  let Y₂' := VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₂ (Set.range J)
  let U₁ : N → E'' := fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y₁ q))
  let U₂ : N → E'' := fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y₂ q))
  let x0 : E' := ψ p
  have hChart :
      ContDiffWithinAt 𝕜 ∞ (g ∘ ψ.symm) (Set.range J) x0 := by
    -- Compose the smooth map `g` with the preferred chart inverse on `range J`.
    have hψ : ContMDiffWithinAt 𝓘(𝕜, E') J ∞ ψ.symm (Set.range J) x0 := by
      simpa [ψ, x0] using
        (show
          ContMDiffWithinAt 𝓘(𝕜, E') J ∞ (extChartAt J p).symm (Set.range J) ((extChartAt J p) p) from
            contMDiffWithinAt_extChartAt_symm_range_self p)
    exact (hg.comp_contMDiffWithinAt_of_eq hψ (by simp [ψ, x0])).contDiffWithinAt
  have hY₁Diff : DifferentiableWithinAt 𝕜 Y₁' (Set.range J) x0 := by
    -- The preferred-chart pullback of `Y₁` is differentiable without adding completeness.
    simpa [ψ, Y₁', x0] using chartPullbackDifferentiableWithinAtBase hY₁
  have hY₂Diff : DifferentiableWithinAt 𝕜 Y₂' (Set.range J) x0 := by
    -- The same chart pullback differentiability holds for `Y₂`.
    simpa [ψ, Y₂', x0] using chartPullbackDifferentiableWithinAtBase hY₂
  have hBracket :
      fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x0
          (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) x0) =
        fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₂' x))
            (Set.range J) x0 (Y₁' x0) -
          fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₁' x))
            (Set.range J) x0 (Y₂' x0) := by
    -- Apply the vector-space Lie bracket identity to the preferred chart pullbacks.
    have hx0Closure : x0 ∈ closure (interior (Set.range J)) := extChartAtBase_mem_closureInterior_range
    exact
      VectorField.fderivWithin_apply_lieBracket hChart
        (by simpa [minSmoothness] using (by decide : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
        J.uniqueDiffOn hx0Closure
        (Set.mem_range_self _) hY₂Diff hY₁Diff
  have hLeft :
      NormedSpace.fromTangentSpace (g p) (mfderiv% g p (⁅Y₁, Y₂⁆ p)) =
        fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x0
          (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) x0) := by
    -- First normalize the left-hand side through the preferred chart derivative of the bracket.
    calc
      NormedSpace.fromTangentSpace (g p) (mfderiv% g p (⁅Y₁, Y₂⁆ p))
          =
            fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x0
              (VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm ⁅Y₁, Y₂⁆ (Set.range J) x0) := by
                simpa [ψ, x0] using
                  (show
                    fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x0
                        (VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm ⁅Y₁, Y₂⁆ (Set.range J) x0) =
                      NormedSpace.fromTangentSpace (g p) (mfderiv% g p (⁅Y₁, Y₂⁆ p)) from
                      chartPullbackDerivativeAtBase
                        (hg.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))).symm
      _ =
            fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x0
              (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) x0) := by
                rw [chartPullbackBracketAt_eq_lieBracketWithinAt hY₁ hY₂]
  have hU₁Diff :
      MDifferentiableAt J 𝓘(𝕜, E'') U₁ p := by
    -- The first derivative field is smooth by the hom-bundle application theorem.
    have hCont :
        ContMDiffAt J 𝓘(𝕜, E'') ∞ U₁ p :=
      contMDiffAt_mfderiv_applyField hg hY₁
    exact hCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hU₂Diff :
      MDifferentiableAt J 𝓘(𝕜, E'') U₂ p := by
    -- The second derivative field is smooth for the same reason.
    have hCont :
        ContMDiffAt J 𝓘(𝕜, E'') ∞ U₂ p :=
      contMDiffAt_mfderiv_applyField hg hY₂
    exact hCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hU₂Eq :
      (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₂' x))
        =ᶠ[𝓝[Set.range J] (ψ p)] fun x ↦ U₂ (ψ.symm x) := by
    simpa [ψ, Y₂', U₂] using
      (show
        (fun x ↦
          fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x
            (VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₂ (Set.range J) x))
          =ᶠ[𝓝[Set.range J] (ψ p)] fun x ↦ U₂ (ψ.symm x) from
            chartPullbackDerivative_eventuallyEq hg)
  have hU₁Eq :
      (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₁' x))
        =ᶠ[𝓝[Set.range J] (ψ p)] fun x ↦ U₁ (ψ.symm x) := by
    simpa [ψ, Y₁', U₁] using
      (show
        (fun x ↦
          fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x
            (VectorField.mpullbackWithin 𝓘(𝕜, E') J ψ.symm Y₁ (Set.range J) x))
          =ᶠ[𝓝[Set.range J] (ψ p)] fun x ↦ U₁ (ψ.symm x) from
            chartPullbackDerivative_eventuallyEq hg)
  have hTerm₁ :
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₂' x))
          (Set.range J) x0 (Y₁' x0) =
        NormedSpace.fromTangentSpace (U₂ p) (mfderiv% U₂ p (Y₁ p)) := by
    -- Transport the first second-order derivative term back to the manifold field `U₂`.
    simpa [ψ, x0, Y₂', Y₁', U₂] using
      chartPullbackDerivativeTermAtBase hU₂Eq hU₂Diff
  have hTerm₂ :
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₁' x))
          (Set.range J) x0 (Y₂' x0) =
        NormedSpace.fromTangentSpace (U₁ p) (mfderiv% U₁ p (Y₂ p)) := by
    -- Transport the second second-order derivative term back to the manifold field `U₁`.
    simpa [ψ, x0, Y₁', Y₂', U₁] using
      chartPullbackDerivativeTermAtBase hU₁Eq hU₁Diff
  -- After chart normalization, the manifold commutator is exactly the chart-space commutator.
  calc
    NormedSpace.fromTangentSpace (g p) (mfderiv% g p (⁅Y₁, Y₂⁆ p))
        =
          fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x0
            (VectorField.lieBracketWithin 𝕜 Y₁' Y₂' (Set.range J) x0) := hLeft
    _ =
          fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₂' x))
              (Set.range J) x0 (Y₁' x0) -
            fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 (g ∘ ψ.symm) (Set.range J) x (Y₁' x))
              (Set.range J) x0 (Y₂' x0) := hBracket
    _ =
          NormedSpace.fromTangentSpace (U₂ p) (mfderiv% U₂ p (Y₁ p)) -
            NormedSpace.fromTangentSpace (U₁ p) (mfderiv% U₁ p (Y₂ p)) := by
              rw [hTerm₁, hTerm₂]
    _ = _ := by
          rfl

end

section

universe uE uE' uH uH' uM uN

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I ∞ M]
  [IsManifold J ∞ N]

/-- Proposition 8.30 (Naturality of the Lie Bracket): if `F : M → N` is a smooth map between
real manifolds with or without boundary and the smooth vector fields `X₁`, `X₂` on `M` are
respectively `F`-related to the smooth vector fields `Y₁`, `Y₂` on `N`, then the Lie bracket
`[X₁, X₂]` is `F`-related to the Lie bracket `[Y₁, Y₂]`. -/
theorem f_related_mlieBracket
    {F : M → N}
    {X₁ X₂ : ∀ p : M, TangentSpace I p}
    {Y₁ Y₂ : ∀ q : N, TangentSpace J q}
    (hX₁ : ContMDiff I I.tangent ∞ (T% X₁))
    (hX₂ : ContMDiff I I.tangent ∞ (T% X₂))
    (hY₁ : ContMDiff J J.tangent ∞ (T% Y₁))
    (hY₂ : ContMDiff J J.tangent ∞ (T% Y₂))
    (h₁ : VectorField.f_related F X₁ Y₁)
    (h₂ : VectorField.f_related F X₂ Y₂) :
    VectorField.f_related F ⁅X₁, X₂⁆ ⁅Y₁, Y₂⁆ := by
  -- Reduce `f_related` for the bracket to the scalar test-function criterion from
  -- Proposition 8.16.
  refine (f_related_iff_mfderiv_comp_eq h₁.contMDiff).2 ?_
  intro p f hf
  let S₁ : M → ℝ := fun x ↦
    NormedSpace.fromTangentSpace (f (F x))
      (mfderiv% (fun z ↦ f (F z)) x (X₁ x))
  let S₂ : M → ℝ := fun x ↦
    NormedSpace.fromTangentSpace (f (F x))
      (mfderiv% (fun z ↦ f (F z)) x (X₂ x))
  let U₁ : N → ℝ := fun q ↦
    NormedSpace.fromTangentSpace (f q) (mfderiv% f q (Y₁ q))
  let U₂ : N → ℝ := fun q ↦
    NormedSpace.fromTangentSpace (f q) (mfderiv% f q (Y₂ q))
  -- Expand the source and target Lie brackets into the corresponding commutators of
  -- first-order derivative operators.
  have hSource :
      NormedSpace.fromTangentSpace (f (F p))
          (mfderiv% (fun x ↦ f (F x)) p (⁅X₁, X₂⁆ p)) =
        NormedSpace.fromTangentSpace (S₂ p) (mfderiv% S₂ p (X₁ p)) -
          NormedSpace.fromTangentSpace (S₁ p) (mfderiv% S₁ p (X₂ p)) := by
    simpa [S₁, S₂] using
      (mfderiv_apply_mlieBracket_eq_commutator
        (J := I)
        (g := fun x ↦ f (F x))
        (Y₁ := X₁)
        (Y₂ := X₂)
        (p := p)
        (hf.comp p h₁.contMDiff.contMDiffAt)
        (hX₁.contMDiffAt)
        (hX₂.contMDiffAt))
  have hTarget :
      NormedSpace.fromTangentSpace (f (F p))
          (mfderiv% f (F p) (⁅Y₁, Y₂⁆ (F p))) =
        NormedSpace.fromTangentSpace (U₂ (F p))
            (mfderiv% U₂ (F p) (Y₁ (F p))) -
          NormedSpace.fromTangentSpace (U₁ (F p))
            (mfderiv% U₁ (F p) (Y₂ (F p))) := by
    simpa [U₁, U₂] using
      (mfderiv_apply_mlieBracket_eq_commutator
        (J := J)
        (g := f)
        (Y₁ := Y₁)
        (Y₂ := Y₂)
        (p := F p)
        hf
        (hY₁.contMDiffAt)
        (hY₂.contMDiffAt))
  -- The scalar derivative fields on `N` are smooth, so they can serve as the second test
  -- functions used to transport the commutator terms through `h₁` and `h₂`.
  have hU₁ :
      ContMDiffAt J 𝓘(ℝ) ∞ U₁ (F p) := by
    simpa [U₁] using contMDiffAt_mfderiv_applyField hf hY₁.contMDiffAt
  have hU₂ :
      ContMDiffAt J 𝓘(ℝ) ∞ U₂ (F p) := by
    simpa [U₂] using contMDiffAt_mfderiv_applyField hf hY₂.contMDiffAt
  have hfOne : ContMDiffAt J 𝓘(ℝ) 1 f (F p) := hf.of_le (by simp)
  have hfDiffNear :
      ∀ᶠ q in 𝓝 (F p), MDifferentiableAt J 𝓘(ℝ) f q := by
    have hContNear :
        ∀ᶠ q in 𝓝 (F p), ContMDiffAt J 𝓘(ℝ) 1 f q :=
      (show
        ContMDiffAt J 𝓘(ℝ) 1 f (F p) ↔
          ∀ᶠ q in 𝓝 (F p), ContMDiffAt J 𝓘(ℝ) 1 f q from
            contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hfOne
    filter_upwards [hContNear] with q hq
    exact hq.mdifferentiableAt one_ne_zero
  have hSourceNear₁ :
      S₁ =ᶠ[𝓝 p] fun x ↦ U₁ (F x) := by
    have hNear :
        ∀ᶠ x in 𝓝 p, MDifferentiableAt J 𝓘(ℝ) f (F x) :=
      h₁.contMDiff.contMDiffAt.continuousAt.preimage_mem_nhds hfDiffNear
    filter_upwards [hNear] with x hx
    have hFdiff : MDifferentiableAt I J F x := by
      exact (h₁.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
    have hEval :
        mfderiv% (fun z ↦ f (F z)) x (X₁ x) =
          mfderiv% f (F x) (Y₁ (F x)) := by
      calc
        mfderiv% (fun z ↦ f (F z)) x (X₁ x)
            = mfderiv% f (F x) (mfderiv I J F x (X₁ x)) := by
                simpa [Function.comp] using
                  mfderiv_comp_apply (x := x) (g := f) (f := F) hx hFdiff (X₁ x)
        _ = mfderiv% f (F x) (Y₁ (F x)) := by
              rw [VectorField.f_related_apply h₁ x]
    simpa [S₁, U₁] using
      congrArg (NormedSpace.fromTangentSpace (f (F x))) hEval
  have hSourceNear₂ :
      S₂ =ᶠ[𝓝 p] fun x ↦ U₂ (F x) := by
    have hNear :
        ∀ᶠ x in 𝓝 p, MDifferentiableAt J 𝓘(ℝ) f (F x) :=
      h₂.contMDiff.contMDiffAt.continuousAt.preimage_mem_nhds hfDiffNear
    filter_upwards [hNear] with x hx
    have hFdiff : MDifferentiableAt I J F x := by
      exact (h₂.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
    have hEval :
        mfderiv% (fun z ↦ f (F z)) x (X₂ x) =
          mfderiv% f (F x) (Y₂ (F x)) := by
      calc
        mfderiv% (fun z ↦ f (F z)) x (X₂ x)
            = mfderiv% f (F x) (mfderiv I J F x (X₂ x)) := by
                simpa [Function.comp] using
                  mfderiv_comp_apply (x := x) (g := f) (f := F) hx hFdiff (X₂ x)
        _ = mfderiv% f (F x) (Y₂ (F x)) := by
              rw [VectorField.f_related_apply h₂ x]
    simpa [S₂, U₂] using
      congrArg (NormedSpace.fromTangentSpace (f (F x))) hEval
  -- The first derivative fields agree at the basepoint and in a neighborhood, so their
  -- derivatives along the related vector fields match as well.
  have hSourceAt₁ : S₁ p = U₁ (F p) := by
    have hFdiff : MDifferentiableAt I J F p := by
      exact h₁.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hEval :
        mfderiv% (fun z ↦ f (F z)) p (X₁ p) =
          mfderiv% f (F p) (Y₁ (F p)) := by
      calc
        mfderiv% (fun z ↦ f (F z)) p (X₁ p)
            = mfderiv% f (F p) (mfderiv I J F p (X₁ p)) := by
                simpa [Function.comp] using
                  mfderiv_comp_apply (x := p) (g := f) (f := F)
                    (hf.mdifferentiableAt (by simp)) hFdiff (X₁ p)
        _ = mfderiv% f (F p) (Y₁ (F p)) := by
              rw [VectorField.f_related_apply h₁ p]
    simpa [S₁, U₁] using
      congrArg (NormedSpace.fromTangentSpace (f (F p))) hEval
  have hSourceAt₂ : S₂ p = U₂ (F p) := by
    have hFdiff : MDifferentiableAt I J F p := by
      exact h₂.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hEval :
        mfderiv% (fun z ↦ f (F z)) p (X₂ p) =
          mfderiv% f (F p) (Y₂ (F p)) := by
      calc
        mfderiv% (fun z ↦ f (F z)) p (X₂ p)
            = mfderiv% f (F p) (mfderiv I J F p (X₂ p)) := by
                simpa [Function.comp] using
                  mfderiv_comp_apply (x := p) (g := f) (f := F)
                    (hf.mdifferentiableAt (by simp)) hFdiff (X₂ p)
        _ = mfderiv% f (F p) (Y₂ (F p)) := by
              rw [VectorField.f_related_apply h₂ p]
    simpa [S₂, U₂] using
      congrArg (NormedSpace.fromTangentSpace (f (F p))) hEval
  have hSourceDeriv₁ :
      mfderiv% S₁ p (X₂ p) = mfderiv% (fun x ↦ U₁ (F x)) p (X₂ p) := by
    have hmf :
        mfderiv I 𝓘(ℝ) S₁ p = mfderiv I 𝓘(ℝ) (fun x ↦ U₁ (F x)) p := by
      simpa [S₁, U₁] using Filter.EventuallyEq.mfderiv_eq hSourceNear₁
    simpa using congrArg (fun A ↦ A (X₂ p)) hmf
  have hSourceDeriv₂ :
      mfderiv% S₂ p (X₁ p) = mfderiv% (fun x ↦ U₂ (F x)) p (X₁ p) := by
    have hmf :
        mfderiv I 𝓘(ℝ) S₂ p = mfderiv I 𝓘(ℝ) (fun x ↦ U₂ (F x)) p := by
      simpa [S₂, U₂] using Filter.EventuallyEq.mfderiv_eq hSourceNear₂
    simpa using congrArg (fun A ↦ A (X₁ p)) hmf
  have hTerm₁ :
      NormedSpace.fromTangentSpace (S₂ p) (mfderiv% S₂ p (X₁ p)) =
        NormedSpace.fromTangentSpace (U₂ (F p))
          (mfderiv% U₂ (F p) (Y₁ (F p))) := by
    calc
      NormedSpace.fromTangentSpace (S₂ p) (mfderiv% S₂ p (X₁ p))
          = NormedSpace.fromTangentSpace (U₂ (F p)) (mfderiv% S₂ p (X₁ p)) := by
              rw [hSourceAt₂]
      _ = NormedSpace.fromTangentSpace (U₂ (F p)) (mfderiv% (fun x ↦ U₂ (F x)) p (X₁ p)) := by
            rw [hSourceDeriv₂]
      _ = NormedSpace.fromTangentSpace (U₂ (F p)) (mfderiv% U₂ (F p) (Y₁ (F p))) := by
            rw [fRelated_mfderivCompEq h₁ p hU₂]
  have hTerm₂ :
      NormedSpace.fromTangentSpace (S₁ p) (mfderiv% S₁ p (X₂ p)) =
        NormedSpace.fromTangentSpace (U₁ (F p))
          (mfderiv% U₁ (F p) (Y₂ (F p))) := by
    calc
      NormedSpace.fromTangentSpace (S₁ p) (mfderiv% S₁ p (X₂ p))
          = NormedSpace.fromTangentSpace (U₁ (F p)) (mfderiv% S₁ p (X₂ p)) := by
              rw [hSourceAt₁]
      _ = NormedSpace.fromTangentSpace (U₁ (F p)) (mfderiv% (fun x ↦ U₁ (F x)) p (X₂ p)) := by
            rw [hSourceDeriv₁]
      _ = NormedSpace.fromTangentSpace (U₁ (F p)) (mfderiv% U₁ (F p) (Y₂ (F p))) := by
            rw [fRelated_mfderivCompEq h₂ p hU₁]
  -- Compare the two commutator expansions after applying the canonical identification of the
  -- tangent space to `ℝ` with `ℝ` itself.
  apply (NormedSpace.fromTangentSpace (f (F p))).injective
  calc
    NormedSpace.fromTangentSpace (f (F p))
        (mfderiv% (fun x ↦ f (F x)) p (⁅X₁, X₂⁆ p))
      =
        NormedSpace.fromTangentSpace (S₂ p) (mfderiv% S₂ p (X₁ p)) -
          NormedSpace.fromTangentSpace (S₁ p) (mfderiv% S₁ p (X₂ p)) := hSource
    _ =
        NormedSpace.fromTangentSpace (U₂ (F p))
            (mfderiv% U₂ (F p) (Y₁ (F p))) -
          NormedSpace.fromTangentSpace (U₁ (F p))
            (mfderiv% U₁ (F p) (Y₂ (F p))) := by
              rw [hTerm₁, hTerm₂]
    _ =
        NormedSpace.fromTangentSpace (f (F p))
          (mfderiv% f (F p) (⁅Y₁, Y₂⁆ (F p))) := hTarget.symm

end
