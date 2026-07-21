import PetersenLib.Ch03.CurvatureSymmetries

/-!
# Petersen Ch. 3, §3.4 Exercise 3.4.14 — the Ricci equations of a submanifold

For a submanifold with normal connection `∇^⊥` and (vector-valued) second
fundamental form `T`, Petersen's Exercise 3.4.14 introduces the **normal
curvature** `R^⊥(X,Y,V,W)` of the normal bundle and asks to show

* **(1)** `R^⊥` is tensorial and skew-symmetric in `X,Y` and in `V,W`;
* **(2)** the **Ricci equations**
  `R^M(X,Y,V,W) = R^⊥(X,Y,V,W) + g_M(T_XV,T_YW) − g_M(T_YV,T_XW)`.

## The general-codimension normal bundle, abstractly

`GaussCodazzi.lean` treats a hypersurface through a single unit normal *field*;
in codimension one the normal curvature `R^⊥` is trivial, so the Ricci equations
have no content there.  For general codimension the geometry that matters is the
orthogonal splitting `TM̄|_M = TM ⊕ NM` of the ambient tangent bundle into the
tangent and normal bundles of the submanifold.  We encode that splitting by its
**orthogonal projection onto the normal bundle**: a smooth field of orthogonal
projections `P : x ↦ (T_xM̄ →L NM_x)`, i.e. `P` is idempotent (`P∘P = P`) and
`g`-self-adjoint (`g(Pa,b) = g(a,Pb)`), and applying `P` to a smooth field yields
a smooth field.  *Normal fields* are the sections `V` fixed by `P` (`PV = V`);
the projection needs only be a splitting on an open set `U` (the neighbourhood on
which the submanifold is charted), exactly as `N` in `GaussCodazzi.lean` is a
global field but the tangency hypotheses hold only on `U`.

From `P` we build, following the projection technique of `GaussCodazzi.lean`:

* `normalCov D P p v V = P(∇_vV)` — the **normal connection** `∇^⊥`;
* `shapeTangent D P p v V = ∇_vV − P(∇_vV)` — the tangential part `(∇_vV)^⊤`,
  which is Petersen's `T_vV` for normal `V` (the shape operator, up to sign);
* `normalCurvature` / `normalCurvatureFour` — the normal curvature `R^⊥`.

The single computational lemma `cov_covField_metricInner_split` — the exact
analogue of `cov_cov_metricInner_split` in `GaussCodazzi.lean` — splits
`g(∇_A(∇_BV), W)` (for normal `W`) into a normal-curvature contribution and one
shape-form correction, and everything else is assembly.  The identity holds for
*any* smooth orthogonal splitting; no integrability of the tangent distribution
is needed.

Tensoriality of `R^⊥` (part (1)) is exhibited by the Ricci equations
themselves: `R^⊥ = R^M − (g(T_·V,T_·W) − …)` writes `R^⊥` as a difference of the
ambient `(0,4)`-curvature and a shape-form expression, both of which are genuine
tensors; the substantive content — the two skew-symmetries — is proved here.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), Exercise 3.4.14,
page 123.
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]

/-! ## The normal connection, the tangential shape form, and the normal curvature -/

/-- **Math.** The **normal connection** `∇^⊥_vV = (∇_vV)^⊥ = P(∇_vV)` for the
orthogonal projection `P` onto the normal bundle. -/
def normalCov (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (p : M) (v : TangentSpace I p) (V : Π x : M, TangentSpace I x) :
    TangentSpace I p :=
  P p (D.cov p v V)

/-- The normal covariant derivative along a field, as a field. -/
def normalCovField (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Y V : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun q => normalCov D P q (Y q) V

/-- **Math.** The **tangential shape form** `T_vV = (∇_vV)^⊤ = ∇_vV − P(∇_vV)`
(the tangential part of `∇_vV`): Petersen's second fundamental form `T` on normal
`V`. -/
def shapeTangent (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (p : M) (v : TangentSpace I p) (V : Π x : M, TangentSpace I x) :
    TangentSpace I p :=
  D.cov p v V - P p (D.cov p v V)

/-- The tangential shape form along a field, as a field. -/
def shapeTangentField (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Y V : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun q => shapeTangent D P q (Y q) V

/-- **Math.** The **normal curvature** `R^⊥(X,Y)V` of the normal connection
(Petersen, Exercise 3.4.14):
`R^⊥(X,Y)V = ∇^⊥_X∇^⊥_YV − ∇^⊥_Y∇^⊥_XV − ∇^⊥_{[X,Y]}V`. -/
def normalCurvature (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (X Y V : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => normalCov D P p (X p) (normalCovField D P Y V)
    - normalCov D P p (Y p) (normalCovField D P X V)
    - normalCov D P p (lieDerivativeVectorField I X Y p) V

/-- **Math.** The `(0,4)` **normal curvature** `R^⊥(X,Y,V,W) = g(R^⊥(X,Y)V, W)`. -/
def normalCurvatureFour (D : AffineConnection I M) (g : RiemannianMetric I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (X Y V W : Π x : M, TangentSpace I x) (p : M) : ℝ :=
  g.metricInner p (normalCurvature D P X Y V p) (W p)

/-! ## Smoothness of the projected fields -/

/-- Applying the normal projection to `∇_YV` yields a smooth field. -/
theorem isSmoothVectorField_normalCovField (D : AffineConnection I M)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hPsmooth : ∀ S : Π x : M, TangentSpace I x, IsSmoothVectorField S →
      IsSmoothVectorField (fun q => P q (S q)))
    {Y V : Π x : M, TangentSpace I x} (hY : IsSmoothVectorField Y)
    (hV : IsSmoothVectorField V) :
    IsSmoothVectorField (normalCovField D P Y V) :=
  hPsmooth (D.covField Y V) (D.smooth_cov hY hV)

/-- The tangential shape form `T_YV` is a smooth field. -/
theorem isSmoothVectorField_shapeTangentField (D : AffineConnection I M)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hPsmooth : ∀ S : Π x : M, TangentSpace I x, IsSmoothVectorField S →
      IsSmoothVectorField (fun q => P q (S q)))
    {Y V : Π x : M, TangentSpace I x} (hY : IsSmoothVectorField Y)
    (hV : IsSmoothVectorField V) :
    IsSmoothVectorField (shapeTangentField D P Y V) := by
  have hcov : IsSmoothVectorField (D.covField Y V) := D.smooth_cov hY hV
  have hnor : IsSmoothVectorField (normalCovField D P Y V) :=
    isSmoothVectorField_normalCovField D hPsmooth hY hV
  have hsub := ((⟨_, hcov⟩ : SmoothVectorField I M) - ⟨_, hnor⟩).smooth
  have e : (fun q => D.covField Y V q - normalCovField D P Y V q)
      = shapeTangentField D P Y V := by
    funext q
    simp only [shapeTangentField, shapeTangent, normalCovField, normalCov,
      AffineConnection.covField_apply]
  rw [← e]
  simpa using hsub

/-! ## The core split lemma (analogue of `cov_cov_metricInner_split`) -/

/-- **Eng.** The key computation for the Ricci equations: for `W` normal on `U`,
pairing the second covariant derivative `∇_A(∇_BV)` against `W` splits into the
iterated normal derivative and one shape-form correction,
`g(∇_A(∇_BV), W) = g(∇^⊥_A∇^⊥_BV, W) − g(T_BV, T_AW)`.  The proof mirrors
`cov_cov_metricInner_split` in `GaussCodazzi.lean`: split `∇_BV` into its normal
part `∇^⊥_BV` and tangential part `T_BV`, differentiate, and use that `T_BV ⊥ W`
holds identically near `p` (so its derivative pairs with `∇_AW` only through the
tangential part `T_AW`). -/
private theorem cov_covField_metricInner_split {g : RiemannianMetric I M}
    (D : RiemannianConnection I g)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hPsmooth : ∀ S : Π x : M, TangentSpace I x, IsSmoothVectorField S →
      IsSmoothVectorField (fun q => P q (S q)))
    {U : Set M} (hU : IsOpen U)
    (hPidem : ∀ q ∈ U, ∀ w, P q (P q w) = P q w)
    (hPsymm : ∀ q ∈ U, ∀ a b : TangentSpace I q,
      g.metricInner q (P q a) b = g.metricInner q a (P q b))
    {A B V W : Π x : M, TangentSpace I x} (hA : IsSmoothVectorField A)
    (hB : IsSmoothVectorField B) (hV : IsSmoothVectorField V)
    (hW : IsSmoothVectorField W)
    (hWnor : ∀ q ∈ U, P q (W q) = W q) {p : M} (hp : p ∈ U) :
    g.metricInner p (D.cov p (A p) (D.toAffineConnection.covField B V)) (W p)
      = g.metricInner p
          (normalCov D.toAffineConnection P p (A p)
            (normalCovField D.toAffineConnection P B V)) (W p)
        - g.metricInner p (shapeTangent D.toAffineConnection P p (B p) V)
            (shapeTangent D.toAffineConnection P p (A p) W) := by
  classical
  -- pairing any vector against the normal `W` factors through `P`
  have key : ∀ a : TangentSpace I p,
      g.metricInner p (P p a) (W p) = g.metricInner p a (W p) := by
    intro a; rw [hPsymm p hp a (W p), hWnor p hp]
  -- the tangential shape form is orthogonal to `W` on all of `U`
  have hf0 : ∀ q ∈ U,
      g.metricInner q (shapeTangentField D.toAffineConnection P B V q) (W q) = 0 := by
    intro q hq
    simp only [shapeTangentField, shapeTangent]
    rw [g.metricInner_sub_left]
    have : g.metricInner q (P q (D.cov q (B q) V)) (W q)
        = g.metricInner q (D.cov q (B q) V) (W q) := by
      rw [hPsymm q hq (D.cov q (B q) V) (W q), hWnor q hq]
    rw [this, sub_self]
  -- smoothness of the projected fields
  have hnor : IsSmoothVectorField (normalCovField D.toAffineConnection P B V) :=
    isSmoothVectorField_normalCovField D.toAffineConnection hPsmooth hB hV
  have htan : IsSmoothVectorField (shapeTangentField D.toAffineConnection P B V) :=
    isSmoothVectorField_shapeTangentField D.toAffineConnection hPsmooth hB hV
  -- `∇_BV` splits into normal + tangential parts as fields
  have hsplitField : D.toAffineConnection.covField B V
      = fun q => normalCovField D.toAffineConnection P B V q
        + shapeTangentField D.toAffineConnection P B V q := by
    funext q
    simp only [normalCovField, normalCov, shapeTangentField, shapeTangent,
      AffineConnection.covField_apply]
    abel
  -- differentiate the split, then pair with `W`
  have hcov_split : D.cov p (A p) (D.toAffineConnection.covField B V)
      = D.cov p (A p) (normalCovField D.toAffineConnection P B V)
        + D.cov p (A p) (shapeTangentField D.toAffineConnection P B V) := by
    rw [hsplitField]; exact D.toAffineConnection.add_field p (A p) hnor htan
  -- the normal-part contribution: `g(∇_A(∇^⊥_BV), W) = g(∇^⊥_A∇^⊥_BV, W)`
  have hnorm_term :
      g.metricInner p (D.cov p (A p) (normalCovField D.toAffineConnection P B V)) (W p)
        = g.metricInner p
            (normalCov D.toAffineConnection P p (A p)
              (normalCovField D.toAffineConnection P B V)) (W p) := (key _).symm
  -- the tangential-part contribution: differentiate `g(T_BV, W) ≡ 0`
  have hdd : directionalDerivative A
      (fun q => g.metricInner q (shapeTangentField D.toAffineConnection P B V q) (W q))
        p = 0 := by
    have hloc :
        (fun q => g.metricInner q (shapeTangentField D.toAffineConnection P B V q) (W q))
        =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hp] with q hq using hf0 q hq
    rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]; rfl
  have hcompat := D.metric_compat htan hW p (A p)
  rw [dirTangent_eq_directionalDerivative, hdd] at hcompat
  -- `g(T_BV, ∇_AW) = g(T_BV, T_AW)`: the normal part of `∇_AW` dies against `T_BV`
  have hTperp : g.metricInner p (shapeTangent D.toAffineConnection P p (B p) V)
      (P p (D.cov p (A p) W)) = 0 := by
    simp only [shapeTangent]
    rw [g.metricInner_sub_left]
    have h1 : g.metricInner p (P p (D.cov p (B p) V)) (P p (D.cov p (A p) W))
        = g.metricInner p (D.cov p (B p) V) (P p (D.cov p (A p) W)) := by
      rw [hPsymm p hp (D.cov p (B p) V) (P p (D.cov p (A p) W)),
        hPidem p hp (D.cov p (A p) W)]
    rw [h1, sub_self]
  have hsplitW : D.cov p (A p) W
      = shapeTangent D.toAffineConnection P p (A p) W + P p (D.cov p (A p) W) := by
    simp only [shapeTangent]; abel
  have hpair : g.metricInner p (shapeTangentField D.toAffineConnection P B V p)
        (D.cov p (A p) W)
      = g.metricInner p (shapeTangent D.toAffineConnection P p (B p) V)
          (shapeTangent D.toAffineConnection P p (A p) W) := by
    have e : shapeTangentField D.toAffineConnection P B V p
        = shapeTangent D.toAffineConnection P p (B p) V := rfl
    rw [e, hsplitW, g.metricInner_add_right, hTperp, add_zero]
  -- assemble
  have htan_term :
      g.metricInner p (D.cov p (A p) (shapeTangentField D.toAffineConnection P B V)) (W p)
        = -g.metricInner p (shapeTangent D.toAffineConnection P p (B p) V)
            (shapeTangent D.toAffineConnection P p (A p) W) := by
    have := hcompat
    rw [hpair] at this
    linarith [this]
  rw [hcov_split, g.metricInner_add_left, hnorm_term, htan_term]; ring

/-! ## Exercise 3.4.14 — the normal curvature and the Ricci equations -/

/-- **Math.** Skew-symmetry of the normal curvature in `X, Y` (Petersen,
Exercise 3.4.14(1)): `R^⊥(X,Y)V = −R^⊥(Y,X)V`, immediate from the definition and
`[Y,X] = −[X,Y]` (`P` is linear). -/
theorem normalCurvature_antisymm (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (X Y V : Π x : M, TangentSpace I x) (p : M) :
    normalCurvature D P X Y V p = -normalCurvature D P Y X V p := by
  simp only [normalCurvature]
  have hbr : normalCov D P p (lieDerivativeVectorField I Y X p) V
      = -normalCov D P p (lieDerivativeVectorField I X Y p) V := by
    simp only [normalCov]
    rw [show lieDerivativeVectorField I Y X p
        = -(lieDerivativeVectorField I X Y p) from
      VectorField.mlieBracket_swap_apply, D.cov_neg_direction, map_neg]
  rw [hbr]; abel

/-- **Math.** Skew-symmetry of the `(0,4)` normal curvature in `X, Y`. -/
theorem normalCurvatureFour_antisymm_left (D : AffineConnection I M)
    (g : RiemannianMetric I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (X Y V W : Π x : M, TangentSpace I x) (p : M) :
    normalCurvatureFour D g P X Y V W p = -normalCurvatureFour D g P Y X V W p := by
  simp only [normalCurvatureFour, normalCurvature_antisymm D P X Y V p,
    g.metricInner_neg_left]

/-- **Math.** **Exercise 3.4.14** (Petersen, `rem:pet-ch3-ex-14`): for tangent
fields `X, Y` and normal fields `V, W` of a submanifold — encoded through the
orthogonal projection `P` onto the normal bundle on an open set `U` — the normal
curvature `R^⊥` satisfies

* **(1)** skew-symmetry in `X,Y`: `R^⊥(X,Y,V,W) = −R^⊥(Y,X,V,W)`, and in `V,W`:
  `R^⊥(X,Y,V,W) = −R^⊥(X,Y,W,V)`;
* **(2)** the **Ricci equations**
  `R^M(X,Y,V,W) = R^⊥(X,Y,V,W) + g(T_XV,T_YW) − g(T_YV,T_XW)`,

where `T_vV = (∇_vV)^⊤` is the tangential shape form (`shapeTangent`).  The
skew-symmetry in `X,Y` needs no normality hypotheses; the Ricci equations need
`W` normal; the skew-symmetry in `V,W` needs both `V, W` normal and follows from
the Ricci equations together with the ambient antisymmetry `R^M(X,Y,V,W) =
−R^M(X,Y,W,V)`.  Tensoriality of `R^⊥` (also part (1)) is exhibited by the Ricci
equations, which write `R^⊥` as a difference of the tensor `R^M` and a shape-form
tensor. -/
theorem exercise3_4_14 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hPsmooth : ∀ S : Π x : M, TangentSpace I x, IsSmoothVectorField S →
      IsSmoothVectorField (fun q => P q (S q)))
    {U : Set M} (hU : IsOpen U)
    (hPidem : ∀ q ∈ U, ∀ w, P q (P q w) = P q w)
    (hPsymm : ∀ q ∈ U, ∀ a b : TangentSpace I q,
      g.metricInner q (P q a) b = g.metricInner q a (P q b))
    {X Y V W : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) (hV : IsSmoothVectorField V)
    (hW : IsSmoothVectorField W)
    (hVnor : ∀ q ∈ U, P q (V q) = V q) (hWnor : ∀ q ∈ U, P q (W q) = W q)
    {p : M} (hp : p ∈ U) :
    (normalCurvatureFour D.toAffineConnection g P X Y V W p
        = -normalCurvatureFour D.toAffineConnection g P Y X V W p
      ∧ normalCurvatureFour D.toAffineConnection g P X Y V W p
          = -normalCurvatureFour D.toAffineConnection g P X Y W V p)
    ∧ curvatureTensorFour D X Y V W p
        = normalCurvatureFour D.toAffineConnection g P X Y V W p
          + g.metricInner p (shapeTangent D.toAffineConnection P p (X p) V)
              (shapeTangent D.toAffineConnection P p (Y p) W)
          - g.metricInner p (shapeTangent D.toAffineConnection P p (Y p) V)
              (shapeTangent D.toAffineConnection P p (X p) W) := by
  -- pairing any vector against a normal field factors through `P`
  have key : ∀ (Z : Π x : M, TangentSpace I x),
      (∀ q ∈ U, P q (Z q) = Z q) → ∀ a : TangentSpace I p,
      g.metricInner p (P p a) (Z p) = g.metricInner p a (Z p) := by
    intro Z hZ a; rw [hPsymm p hp a (Z p), hZ p hp]
  -- **The Ricci equations (part 2)**, for arbitrary normal second/fourth slots
  have ricci : ∀ (V' W' : Π x : M, TangentSpace I x), IsSmoothVectorField V' →
      IsSmoothVectorField W' → (∀ q ∈ U, P q (W' q) = W' q) →
      curvatureTensorFour D X Y V' W' p
        = normalCurvatureFour D.toAffineConnection g P X Y V' W' p
          + g.metricInner p (shapeTangent D.toAffineConnection P p (X p) V')
              (shapeTangent D.toAffineConnection P p (Y p) W')
          - g.metricInner p (shapeTangent D.toAffineConnection P p (Y p) V')
              (shapeTangent D.toAffineConnection P p (X p) W') := by
    intro V' W' hV' hW' hW'nor
    have h₁ := cov_covField_metricInner_split D hPsmooth hU hPidem hPsymm
      hX hY hV' hW' hW'nor hp
    have h₂ := cov_covField_metricInner_split D hPsmooth hU hPidem hPsymm
      hY hX hV' hW' hW'nor hp
    -- the bracket term factors through `P`
    have h₃ : g.metricInner p
          (D.cov p (lieDerivativeVectorField I X Y p) V') (W' p)
        = g.metricInner p
            (normalCov D.toAffineConnection P p
              (lieDerivativeVectorField I X Y p) V') (W' p) :=
      (key W' hW'nor _).symm
    rw [curvatureTensorFour_apply, curvatureTensor_apply,
      g.metricInner_sub_left, g.metricInner_sub_left, h₁, h₂, h₃,
      normalCurvatureFour, normalCurvature, g.metricInner_sub_left,
      g.metricInner_sub_left]
    ring
  refine ⟨⟨normalCurvatureFour_antisymm_left D.toAffineConnection g P X Y V W p, ?_⟩,
    ricci V W hV hW hWnor⟩
  -- **Skew in `V,W` (part 1)** from the Ricci equations + ambient antisymmetry
  have rVW := ricci V W hV hW hWnor
  have rWV := ricci W V hW hV hVnor
  have hamb : curvatureTensorFour D X Y W V p = -curvatureTensorFour D X Y V W p :=
    curvatureTensorFour_antisymm_right D hX hY hW hV p
  have hcomm : ∀ a b : TangentSpace I p,
      g.metricInner p a b = g.metricInner p b a := fun a b => g.metricInner_comm p a b
  -- rearrange: `R^⊥(X,Y,V,W) + R^⊥(X,Y,W,V) = 0`
  rw [hamb] at rWV
  rw [hcomm (shapeTangent D.toAffineConnection P p (X p) W)
      (shapeTangent D.toAffineConnection P p (Y p) V),
    hcomm (shapeTangent D.toAffineConnection P p (Y p) W)
      (shapeTangent D.toAffineConnection P p (X p) V)] at rWV
  linarith [rVW, rWV]

end PetersenLib
