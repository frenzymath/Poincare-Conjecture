import LeeSmoothLib.Ch03.Sec03_20.Problem_3_7
import LeeSmoothLib.Ch08.Sec08_56.Notation_8_56_extra_3
import LeeSmoothLib.Ch08.Sec08_56.Proposition_8_14
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open smooth_germ_derivation_at

noncomputable section

section

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

local notation "SmoothFunction" => C^∞⟮I, M; ℝ⟯
local notation "SmoothDerivation" => Derivation ℝ SmoothFunction SmoothFunction
local notation "SmoothVectorField" => Cₛ^∞⟮I; E, TangentSpace I⟯

-- Domain sampling pass:
-- * primary domain: smooth vector fields and derivations of the algebra of smooth functions;
-- * source-facing layer: every smooth derivation of `C^∞(M)` is induced by a smooth vector field;
-- * core/canonical owner: `ContMDiffSection.toDerivation`;
-- * bridge/view owners inspected in the local chapter/project API:
--   `Derivation.evalAt`, `smooth_germ_derivation_at.toTangentSpace`, and
--   `roughVectorField_smooth_iff_forall_smooth_apply_smooth`;
-- * owner abstraction choice: the main proposition should be surjectivity of
--   `ContMDiffSection.toDerivation`, while the pointwise tangent-vector reconstruction and the
--   smoothness criterion remain derived bridge steps.
-- Primitive data is only a global derivation `D : SmoothDerivation`; the pointwise tangent vector
-- at `p` is derived from `Derivation.evalAt p D` via
-- `smooth_germ_derivation_at.toTangentSpace`, and smoothness of the resulting rough field is
-- derived from Proposition 8.14. This owner chain is currently formalized only under
-- `[T2Space M] [SigmaCompactSpace M]`, so those hypotheses belong in the public statement.

omit [SigmaCompactSpace M] in
/-- Helper for Proposition 8.15: a point derivation depends only on the germ of a global smooth
function at its base point. -/
private theorem pointDerivation_congr_of_eventuallyEq
    (p : M) (v : PointDerivation I p) (f g : SmoothFunction) (hfg : f =ᶠ[nhds p] g) :
    v f = v g := by
  -- Shrink the eventual equality to an open neighborhood and invoke Proposition 3.8.
  have hEq : {x : M | f x = g x} ∈ nhds p := hfg
  rcases mem_nhds_iff.1 hEq with ⟨U, hUsub, hU_open, hpU⟩
  exact PointDerivation.congr_of_eqOn_nhds v f g U hU_open hpU fun x hx ↦ hUsub hx

/-- Helper for Proposition 8.15: globalizing model-space test functions turns a point derivation at
`p` into a chart-side point derivation at `extChartAt I p p`. -/
private theorem pointDerivationChartModel_map_add
    (p : M) (w : PointDerivation I p)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    w (globalizedChartPullback (H := H) (I := I) p (f + g))
      = w (globalizedChartPullback (H := H) (I := I) p f)
        + w (globalizedChartPullback (H := H) (I := I) p g) := by
  -- Replace the globalization of `f + g` by the sum of the globalizations, then use additivity.
  calc
    w (globalizedChartPullback (H := H) (I := I) p (f + g))
      = w
          (globalizedChartPullback (H := H) (I := I) p f
            + globalizedChartPullback (H := H) (I := I) p g) :=
        pointDerivation_congr_of_eventuallyEq (I := I) p w _ _
          (globalizedChartPullback_add_eventuallyEq (H := H) (I := I) p f g)
    _ = w (globalizedChartPullback (H := H) (I := I) p f)
          + w (globalizedChartPullback (H := H) (I := I) p g) := by
          exact w.map_add _ _

/-- Helper for Proposition 8.15: the chart-side point-derivation model is `ℝ`-linear in the test
function. -/
private theorem pointDerivationChartModel_map_smul
    (p : M) (w : PointDerivation I p)
    (c : ℝ) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    w (globalizedChartPullback (H := H) (I := I) p (c • f))
      = c * w (globalizedChartPullback (H := H) (I := I) p f) := by
  -- Replace the globalization of `c • f` by `c • globalizedChartPullback p f`, then use
  -- linearity of the point derivation.
  calc
    w (globalizedChartPullback (H := H) (I := I) p (c • f))
      = w (c • globalizedChartPullback (H := H) (I := I) p f) :=
        pointDerivation_congr_of_eventuallyEq (I := I) p w _ _
          (globalizedChartPullback_smul_eventuallyEq (H := H) (I := I) p c f)
    _ = c * w (globalizedChartPullback (H := H) (I := I) p f) := by
          exact w.map_smul c _

/-- Helper for Proposition 8.15: the chart-side point-derivation model satisfies the Leibniz rule
on globalized test functions. -/
private theorem pointDerivationChartModel_leibniz
    (p : M) (w : PointDerivation I p)
    (f g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    w (globalizedChartPullback (H := H) (I := I) p (f * g))
      = f (extChartAt I p p) * w (globalizedChartPullback (H := H) (I := I) p g)
        + g (extChartAt I p p) * w (globalizedChartPullback (H := H) (I := I) p f) := by
  -- First rewrite the product globalization into a product of globalizations, then apply the
  -- point-derivation Leibniz rule and evaluate the coefficients at `p`.
  have hf :
      globalizedChartPullback (H := H) (I := I) p f p = f (extChartAt I p p) := by
    simpa using (globalizedChartPullback_eventuallyEq (H := H) (I := I) p f).eq_of_nhds
  have hg :
      globalizedChartPullback (H := H) (I := I) p g p = g (extChartAt I p p) := by
    simpa using (globalizedChartPullback_eventuallyEq (H := H) (I := I) p g).eq_of_nhds
  calc
    w (globalizedChartPullback (H := H) (I := I) p (f * g))
      = w
          (globalizedChartPullback (H := H) (I := I) p f
            * globalizedChartPullback (H := H) (I := I) p g) :=
        pointDerivation_congr_of_eventuallyEq (I := I) p w _ _
          (globalizedChartPullback_mul_eventuallyEq (H := H) (I := I) p f g)
    _ = globalizedChartPullback (H := H) (I := I) p f p
          * w (globalizedChartPullback (H := H) (I := I) p g)
        + globalizedChartPullback (H := H) (I := I) p g p
          * w (globalizedChartPullback (H := H) (I := I) p f) := by
          simpa only [PointedContMDiffMap.smul_def] using
            w.leibniz
              (globalizedChartPullback (H := H) (I := I) p f)
              (globalizedChartPullback (H := H) (I := I) p g)
    _ = f (extChartAt I p p) * w (globalizedChartPullback (H := H) (I := I) p g)
          + g (extChartAt I p p) * w (globalizedChartPullback (H := H) (I := I) p f) := by
          rw [hf, hg]

/-- Helper for Proposition 8.15: a point derivation at `p` induces a model-space point derivation
at the chart point by evaluating globalized test functions. -/
private noncomputable def pointDerivationChartModel
    (p : M) (w : PointDerivation I p) :
    PointDerivation 𝓘(ℝ, E) (extChartAt I p p) :=
  Derivation.mk'
    { toFun := fun g ↦
        w (globalizedChartPullback (H := H) (I := I) p g)
      map_add' := pointDerivationChartModel_map_add (H := H) (I := I) p w
      map_smul' := pointDerivationChartModel_map_smul (H := H) (I := I) p w }
    (pointDerivationChartModel_leibniz (H := H) (I := I) p w)

/-- Helper for Proposition 8.15: evaluating the chart-side point derivation is just evaluation on
the chosen globalization of the model-space test function. -/
private theorem pointDerivationChartModel_apply
    (p : M) (w : PointDerivation I p) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    pointDerivationChartModel (H := H) (I := I) p w g
      = w (globalizedChartPullback (H := H) (I := I) p g) :=
  rfl

/-- Helper for Proposition 8.15: a chart-side representing vector reconstructs the original point
derivation after pulling it back through the preferred inverse chart. -/
private theorem chartRepresentingVector_gives_pointDerivation
    (p : M) (w : PointDerivation I p) (y : E)
    (hy : ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      pointDerivationChartModel (H := H) (I := I) p w g
        = fderiv ℝ g (extChartAt I p p) y) :
    let X : TangentSpace I p :=
      mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y
    TangentSpace.toPointDerivation X = w := by
  let q : E := extChartAt I p p
  let X : TangentSpace I p :=
    mfderiv[Set.range I] (extChartAt I p).symm q y
  ext f
  -- Write `f` near `p` as a globalized chart function so the representing hypothesis can be used.
  rcases writtenInExtChartAt_globalize_near_chartPoint (H := H) (I := I) p f with ⟨g, hg⟩
  have hpull :
      globalizedChartPullback (H := H) (I := I) p g =ᶠ[nhds p] f := by
    exact (globalizedChartPullback_eventuallyEq (H := H) (I := I) p g).trans <|
      pullback_extChartAt_eventuallyEq_of_eventuallyEq_writtenInExtChartAt
        (H := H) (I := I) p f g hg
  have hderiv :
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y =
        fderiv ℝ g q y :=
    fderivWithin_writtenInExtChartAt_eq_fderiv_of_eventuallyEq
      (H := H) (I := I) p f g hg y
  have hX_eq : X = y := by
    -- The inverse-chart derivative identifies the chosen tangent vector with the representing
    -- model-space vector.
    simpa [X, q] using
      congrArg
        (fun A : TangentSpace 𝓘(ℝ, E) q →L[ℝ] TangentSpace I p ↦ A y)
        (mfderivWithin_range_extChartAt_symm (I := I) (x := p))
  have hf_diff : MDifferentiableAt I 𝓘(ℝ) f p := by
    -- A global smooth function is differentiable at the base point.
    exact (f.contMDiff p).mdifferentiableAt (by norm_num)
  have hmfderiv :
      mfderiv I 𝓘(ℝ) f p =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q := by
    -- Rewrite the manifold derivative of `f` in chart coordinates.
    simpa [q] using
      (MDifferentiableAt.mfderiv (I := I) (I' := 𝓘(ℝ)) (f := f) (x := p) hf_diff)
  have hmfderiv_apply :
      mfderiv I 𝓘(ℝ) f p y =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := by
    -- Apply the identified linear maps to the representing vector `y`.
    simpa [q] using congrArg (fun A ↦ A y) hmfderiv
  have hX_apply :
      TangentSpace.toPointDerivation X f =
        fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := by
    -- Evaluate the tangent-vector derivation in chart coordinates.
    rw [TangentSpace.toPointDerivation_apply, hX_eq]
    simpa using hmfderiv_apply
  have hglobal :
      pointDerivationChartModel (H := H) (I := I) p w g = w f := by
    -- The chosen globalization agrees with `f` near `p`, so the point derivation sees the same
    -- germ.
    calc
      pointDerivationChartModel (H := H) (I := I) p w g
        = w (globalizedChartPullback (H := H) (I := I) p g) := by
            rw [pointDerivationChartModel_apply]
      _ = w f := pointDerivation_congr_of_eventuallyEq (I := I) p w _ _ hpull
  calc
    TangentSpace.toPointDerivation X f
      = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p f) (Set.range I) q y := hX_apply
    _ = fderiv ℝ g q y := hderiv
    _ = pointDerivationChartModel (H := H) (I := I) p w g := by
          symm
          exact hy g
    _ = w f := hglobal

/-- Helper for Proposition 8.15: any tangent vector realizing a given point derivation has chart
pushforward equal to the unique representing model-space vector. -/
private theorem chartPushforward_represents_pointDerivationChartModel
    (p : M) (w : PointDerivation I p) {X : TangentSpace I p}
    (hX : TangentSpace.toPointDerivation X = w) :
    ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
      pointDerivationChartModel (H := H) (I := I) p w g
        = fderiv ℝ g (extChartAt I p p) (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) := by
  intro g
  let q : E := extChartAt I p p
  let hpull : M → ℝ := fun x ↦ g (extChartAt I p x)
  let f := globalizedChartPullback (H := H) (I := I) p g
  have hf :
      f =ᶠ[nhds p] hpull :=
    globalizedChartPullback_eventuallyEq (H := H) (I := I) p g
  have hg_md : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g q := by
    -- Smooth model-space test functions are differentiable at the chart point.
    exact (g.contMDiff q).mdifferentiableAt (by norm_num)
  have hchart :
      HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) := by
    -- The preferred chart has the expected derivative at the base point.
    exact
      (mdifferentiableAt_extChartAt (I := I) (H := H) (x := p) (y := p)
        (mem_chart_source H p)).hasMFDerivAt
  have hpull_has :
      HasMFDerivAt I 𝓘(ℝ) hpull p
        ((fderiv ℝ g q).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p)) := by
    -- Differentiate the actual pullback `g ∘ extChartAt I p`.
    have hg_has :
        HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ) g q (fderiv ℝ g q) := by
      simpa [mfderiv_eq_fderiv] using hg_md.hasMFDerivAt
    simpa [hpull, Function.comp, q] using hg_has.comp p hchart
  have hf_mfderiv :
      mfderiv I 𝓘(ℝ) f p =
        (fderiv ℝ g q).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p) := by
    -- Transfer the derivative along the eventual equality defining the globalization.
    exact (hpull_has.congr_of_eventuallyEq hf).mfderiv
  have hX_apply :
      TangentSpace.toPointDerivation X f =
        fderiv ℝ g q (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) := by
    -- Evaluating the tangent-vector derivation amounts to applying the pushed-forward derivative.
    rw [TangentSpace.toPointDerivation_apply]
    simpa [q] using congrArg (fun A : TangentSpace I p →L[ℝ] ℝ ↦ A X) hf_mfderiv
  calc
    pointDerivationChartModel (H := H) (I := I) p w g
      = w f := by
          rw [pointDerivationChartModel_apply]
    _ = TangentSpace.toPointDerivation X f := by
          rw [← hX]
    _ = fderiv ℝ g q (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X) := hX_apply

/-- Helper for Proposition 8.15: every point derivation at `p` is induced by a unique tangent
vector in `TangentSpace I p`. -/
private theorem pointDerivation_existsUnique_tangentVector
    (p : M) (w : PointDerivation I p) :
    ∃! X : TangentSpace I p, TangentSpace.toPointDerivation X = w := by
  let wModel : PointDerivation 𝓘(ℝ, E) (extChartAt I p p) :=
    pointDerivationChartModel (H := H) (I := I) p w
  rcases model_point_derivation_existsUnique_vector (q := extChartAt I p p) wModel with
    ⟨y, hy, hyuniq⟩
  let X : TangentSpace I p :=
    mfderiv[Set.range I] (extChartAt I p).symm (extChartAt I p p) y
  refine ⟨X, ?_, ?_⟩
  · -- The tangent vector reconstructed from the chart representative induces the original point
    -- derivation.
    simpa [X] using
      chartRepresentingVector_gives_pointDerivation (H := H) (I := I) p w y hy
  · intro X' hX'
    have hpushX :
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X = y := by
      -- Pushing forward the inverse-chart vector recovers the representing chart vector.
      simpa [X] using
        smooth_germ_derivation_at.chart_pushforward_of_inverse_chart_vector
          (H := H) (I := I) p y
    have hreprX' :
        ∀ g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
          wModel g = fderiv ℝ g (extChartAt I p p)
            (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X') := by
      intro g
      -- Any competing tangent vector induces the same chart-side point derivation.
      simpa [wModel] using
        chartPushforward_represents_pointDerivationChartModel
          (H := H) (I := I) p w hX' g
    have hpushX' :
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) p X' = y :=
      hyuniq _ hreprX'
    -- Equal chart pushforwards force equality of the original tangent vectors.
    exact
      smooth_germ_derivation_at.tangent_eq_of_same_chart_pushforward
        (H := H) (I := I) p (hpushX'.trans hpushX.symm)

/-- Helper for Proposition 8.15: the rough field reconstructed pointwise from `Derivation.evalAt`
acts on every smooth function exactly as the original derivation. -/
private theorem roughField_apply_eq_derivation
    (D : SmoothDerivation) :
    ∀ f : SmoothFunction,
      VectorField.apply
          (fun p ↦
            (pointDerivation_existsUnique_tangentVector (H := H) (I := I) p
              (Derivation.evalAt p D)).choose)
          f
        = D f := by
  let X0 : ∀ p : M, TangentSpace I p := fun p ↦
    (pointDerivation_existsUnique_tangentVector (H := H) (I := I) p
      (Derivation.evalAt p D)).choose
  intro f
  ext p
  have hX0 :
      TangentSpace.toPointDerivation (X0 p) = Derivation.evalAt p D :=
    (pointDerivation_existsUnique_tangentVector (H := H) (I := I) p
      (Derivation.evalAt p D)).choose_spec.1
  -- Evaluate both sides at `p` through the point-derivation identification.
  calc
    VectorField.apply X0 f p = TangentSpace.toPointDerivation (X0 p) f := by
      rw [VectorField.apply_def, TangentSpace.toPointDerivation_apply]
    _ = Derivation.evalAt p D f := by rw [hX0]
    _ = D f p := by rw [Derivation.evalAt_apply]

/-- Proposition 8.15. In the chapter's finite-dimensional Hausdorff sigma-compact manifold setting,
a linear operator on `C^∞(M)` is a derivation if and only if it is given by applying some smooth
vector field to smooth functions. In owner form, the canonical bridge
`ContMDiffSection.toDerivation` from smooth vector fields to derivations of `C^∞(M)` is
surjective. -/
theorem smoothVectorField_toDerivation_surjective :
    Function.Surjective (ContMDiffSection.toDerivation : SmoothVectorField → SmoothDerivation) := by
  intro D
  let X0 : ∀ p : M, TangentSpace I p := fun p ↦
    (pointDerivation_existsUnique_tangentVector (H := H) (I := I) p
      (Derivation.evalAt p D)).choose
  have hApply : ∀ f : SmoothFunction, VectorField.apply X0 f = D f :=
    roughField_apply_eq_derivation (H := H) (I := I) D
  have hSmoothApply :
      ∀ f : SmoothFunction, ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X0 f) := by
    intro f
    -- Replace the rough-field action by the known smooth function `D f`.
    simpa [hApply f] using (D f).contMDiff
  have hX0 :
      ContMDiff I I.tangent ∞ (T% X0) := by
    -- Proposition 8.14 upgrades the pointwise reconstruction to a smooth vector field.
    exact
      (roughVectorField_smooth_iff_forall_smooth_apply_smooth (I := I) X0).2
        hSmoothApply
  let X : SmoothVectorField := ⟨X0, hX0⟩
  refine ⟨X, ?_⟩
  ext f p
  -- Compare both derivations pointwise through the reconstructed rough field identity.
  rw [ContMDiffSection.toDerivation_apply]
  exact congrFun (hApply f) p

/-- Proposition 8.15. In the same formal manifold setting, every derivation of `C^∞(M)` is the
derivation induced by some smooth vector field. -/
theorem exists_smoothVectorField_eq_derivation (D : SmoothDerivation) :
    ∃ X : SmoothVectorField, D = X.toDerivation := by
  rcases smoothVectorField_toDerivation_surjective D with ⟨X, hX⟩
  exact ⟨X, hX.symm⟩

end
