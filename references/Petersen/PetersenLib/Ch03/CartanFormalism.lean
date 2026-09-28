import PetersenLib.Ch03.RicciSectional

/-!
# Petersen Ch. 3, §3.4 — Cartan formalism (Exercise 3.4.28)

For a Riemannian manifold `(M, g)` with a smooth **orthonormal frame**
`E₁, …, Eₙ` (`n = dim M`), the Levi-Civita connection is encoded by the
**connection `1`-forms** `ωⁱⱼ`, defined by `∇_v Eⱼ = ωⁱⱼ(v) Eᵢ`, i.e.
`ωⁱⱼ(v) = g(∇_v Eⱼ, Eᵢ)`.  With the dual coframe `ωⁱ(v) = g(v, Eᵢ)`
(`ωⁱ(Eⱼ) = δⁱⱼ`), the connection forms satisfy the **Cartan structure
equations** (Petersen, Exercise 3.4.28):

* **skew-symmetry** `ωⁱⱼ = −ωʲᵢ` (`connectionForm_skew`), from metric
  compatibility applied to the constant `g(Eᵢ, Eⱼ) = δᵢⱼ`;
* **first structure equation** `dωⁱ = ∑ⱼ ωʲ ∧ ωⁱⱼ` (`firstStructureEquation`),
  from torsion-freeness and metric compatibility;
* **second structure equation** `dωⁱⱼ = ∑ₖ ωᵏⱼ ∧ ωⁱₖ + Ωⁱⱼ`
  (`secondStructureEquation`), where the **curvature forms**
  `Ωⁱⱼ(X,Y) = g(R(X,Y)Eⱼ, Eᵢ)` (`curvatureForm`) are the `𝔰𝔬(n)`-valued
  `2`-forms with `R(X,Y)Eⱼ = Ωⁱⱼ(X,Y) Eᵢ`.

The exterior derivative of a `1`-form is taken in its intrinsic (invariant)
form `dθ(X,Y) = X(θ(Y)) − Y(θ(X)) − θ([X,Y])` (`extDerivOneForm`), and the
wedge of two `1`-forms is `(α ∧ β)(X,Y) = α(X)β(Y) − α(Y)β(X)`
(`wedgeOneForm`); equality of the resulting `2`-forms is faithfully rendered as
equality of their values on every pair of smooth vector fields.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Exercise 3.4.28,
pages 111–112.
-/

open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ## The `1`-form calculus: wedge and (intrinsic) exterior derivative -/

/-- The **wedge product** of two `1`-forms `α, β` (each a pointwise functional
on the tangent spaces): `(α ∧ β)(u,v) = α(u)β(v) − α(v)β(u)`. -/
def wedgeOneForm (α β : ∀ p : M, TangentSpace I p → ℝ) :
    ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ :=
  fun p u v => α p u * β p v - α p v * β p u

/-- The **intrinsic exterior derivative** of a `1`-form `θ`, evaluated on two
smooth vector fields: `dθ(X,Y) = X(θ(Y)) − Y(θ(X)) − θ([X,Y])`.  This is the
coordinate-free formula; for smooth `θ` it agrees with the usual `dθ`. -/
def extDerivOneForm (θ : ∀ p : M, TangentSpace I p → ℝ)
    (X Y : Π x : M, TangentSpace I x) : M → ℝ :=
  fun p => dirTangent (fun q => θ q (Y q)) (X p)
    - dirTangent (fun q => θ q (X q)) (Y p)
    - θ p (lieDerivativeVectorField I X Y p)

/-! ## The frame forms: coframe, connection forms, curvature forms -/

/-- The **dual coframe** `ωⁱ(v) = g(v, Eᵢ)` of a `g`-orthonormal frame `E`.
For an orthonormal frame this is the coframe dual to `E`: `ωⁱ(Eⱼ) = δⁱⱼ`. -/
def coframe (g : RiemannianMetric I M)
    (e : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) : ∀ p : M, TangentSpace I p → ℝ :=
  fun p v => g.metricInner p v (e i p)

/-- The **connection `1`-form** `ωⁱⱼ`, `ωⁱⱼ(v) = g(∇_v Eⱼ, Eᵢ)`, so that
`∇_v Eⱼ = ∑ᵢ ωⁱⱼ(v) Eᵢ`.  Upper index `i`, lower index `j`. -/
def connectionForm (D : AffineConnection I M) (g : RiemannianMetric I M)
    (e : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)
    (i j : Fin (Module.finrank ℝ E)) : ∀ p : M, TangentSpace I p → ℝ :=
  fun p v => g.metricInner p (D.cov p v (e j)) (e i p)

/-- The **curvature `2`-form** `Ωⁱⱼ`, `Ωⁱⱼ(X,Y) = g(R(X,Y)Eⱼ, Eᵢ)`, so that
`R(X,Y)Eⱼ = ∑ᵢ Ωⁱⱼ(X,Y) Eᵢ`.  Upper index `i`, lower index `j`. -/
def curvatureForm {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    (e : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ :=
  fun p u v => curvatureTensorFourAt D p u v (e j p) (e i p)

/-! ## Parseval expansion in a smooth orthonormal frame -/

/-- **Parseval in a smooth `g`-orthonormal frame.** At a point `p`, the values
`E₁(p), …, Eₙ(p)` of a `g`-orthonormal frame form a `g`-orthonormal basis of
`T_pM`, so `∑ⱼ g(u, Eⱼ)·g(w, Eⱼ) = g(u, w)`. -/
theorem sum_metricInner_frame {g : RiemannianMetric I M} (p : M)
    (e : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)
    (hon : ∀ i j, g.metricInner p (e i p) (e j p) = if i = j then 1 else 0)
    (u w : TangentSpace I p) :
    ∑ j, g.metricInner p u (e j p) * g.metricInner p w (e j p)
      = g.metricInner p u w := by
  classical
  have hLI : LinearIndependent ℝ (fun j => e j p) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h0 := congrArg (fun z => g.metricInner p z (e k p)) hc
    simp only [g.metricInner_zero_left] at h0
    rw [metricInner_sum_smul_left] at h0
    rw [Finset.sum_eq_single k] at h0
    · rwa [hon, if_pos rfl, mul_one] at h0
    · intro x _ hx; rw [hon, if_neg hx, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I p) := by
    rw [Fintype.card_fin]
    rfl
  set b := basisOfLinearIndependentOfCardEqFinrank hLI hcard with hbdef
  have hbcoe : ⇑b = fun j => e j p := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hbon : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
    intro i j; simp only [hbcoe]; exact hon i j
  rw [metricInner_eq_sum_mul p b hbon u w]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hbcoe]
  rw [g.metricInner_comm p (e j p) w]

/-! ## Part (1): skew-symmetry and the first structure equation -/

variable {g : RiemannianMetric I M} (D : RiemannianConnection I g)
  (e : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)

/-- **Cartan Exercise 3.4.28(1), skew-symmetry.** For a smooth `g`-orthonormal
frame, the connection forms are skew: `ωⁱⱼ = −ωʲᵢ`, i.e.
`g(∇_v Eⱼ, Eᵢ) = −g(∇_v Eᵢ, Eⱼ)`.  Proof: differentiate the constant
`g(Eᵢ, Eⱼ) = δᵢⱼ` and use metric compatibility. -/
theorem connectionForm_skew (hsm : ∀ i, IsSmoothVectorField (e i))
    (hon : ∀ (q : M) i j, g.metricInner q (e i q) (e j q) = if i = j then 1 else 0)
    (i j : Fin (Module.finrank ℝ E)) (p : M) (v : TangentSpace I p) :
    connectionForm D.toAffineConnection g e i j p v
      = - connectionForm D.toAffineConnection g e j i p v := by
  have hconst : (fun q => g.metricInner q (e j q) (e i q))
      = fun _ : M => (if j = i then (1 : ℝ) else 0) := funext fun q => hon q j i
  have hd : dirTangent (fun q => g.metricInner q (e j q) (e i q)) v = 0 := by
    rw [hconst]
    show mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (if j = i then (1 : ℝ) else 0)) p v = 0
    rw [mfderiv_const, ContinuousLinearMap.zero_apply]
  have hmc := D.metric_compat (hsm j) (hsm i) p v
  rw [hd] at hmc
  simp only [connectionForm]
  rw [g.metricInner_comm p (e j p) (D.cov p v (e i))] at hmc
  linarith [hmc]

/-- **Cartan Exercise 3.4.28(1), first structure equation** `dωⁱ = ∑ⱼ ωʲ ∧ ωⁱⱼ`.
For a smooth `g`-orthonormal frame, the exterior derivative of the coframe is
expressed through the connection forms.  Proof: expand `dωⁱ(X,Y)` by metric
compatibility and torsion-freeness to `g(Y,∇_X Eᵢ) − g(X,∇_Y Eᵢ)`, then expand
the right-hand side with skew-symmetry and the frame Parseval identity. -/
theorem firstStructureEquation
    (hsm : ∀ i, IsSmoothVectorField (e i))
    (hon : ∀ (q : M) i j, g.metricInner q (e i q) (e j q) = if i = j then 1 else 0)
    {X Y : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) (i : Fin (Module.finrank ℝ E)) (p : M) :
    extDerivOneForm (coframe g e i) X Y p
      = ∑ j, wedgeOneForm (coframe g e j)
          (connectionForm D.toAffineConnection g e i j) p (X p) (Y p) := by
  -- LHS: `dωⁱ(X,Y) = g(Y, ∇_X Eᵢ) − g(X, ∇_Y Eᵢ)`.
  have hLHS : extDerivOneForm (coframe g e i) X Y p
      = g.metricInner p (Y p) (D.cov p (X p) (e i))
        - g.metricInner p (X p) (D.cov p (Y p) (e i)) := by
    simp only [extDerivOneForm, coframe]
    rw [D.metric_compat hY (hsm i) p (X p), D.metric_compat hX (hsm i) p (Y p),
      ← D.torsion_free hX hY p, g.metricInner_sub_left]
    ring
  -- skew-symmetry in the frame at `p`: `g(∇_v Eⱼ, Eᵢ) = −g(∇_v Eᵢ, Eⱼ)`.
  have hskew : ∀ (v : TangentSpace I p) (j : Fin (Module.finrank ℝ E)),
      g.metricInner p (D.cov p v (e j)) (e i p)
        = - g.metricInner p (D.cov p v (e i)) (e j p) := fun v j => by
    have h := connectionForm_skew D e hsm hon i j p v
    simpa only [connectionForm] using h
  -- RHS: rewrite each summand with skew-symmetry, then apply Parseval twice.
  have key : ∀ j : Fin (Module.finrank ℝ E),
      g.metricInner p (X p) (e j p) * g.metricInner p (D.cov p (Y p) (e j)) (e i p)
        - g.metricInner p (Y p) (e j p) * g.metricInner p (D.cov p (X p) (e j)) (e i p)
      = g.metricInner p (Y p) (e j p)
          * g.metricInner p (D.cov p (X p) (e i)) (e j p)
        - g.metricInner p (X p) (e j p)
          * g.metricInner p (D.cov p (Y p) (e i)) (e j p) := by
    intro j
    rw [hskew (Y p) j, hskew (X p) j]; ring
  have hRHS : ∑ j, wedgeOneForm (coframe g e j)
      (connectionForm D.toAffineConnection g e i j) p (X p) (Y p)
      = g.metricInner p (Y p) (D.cov p (X p) (e i))
        - g.metricInner p (X p) (D.cov p (Y p) (e i)) := by
    simp only [wedgeOneForm, coframe, connectionForm]
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_sub_distrib,
      sum_metricInner_frame p e (hon p) (Y p) (D.cov p (X p) (e i)),
      sum_metricInner_frame p e (hon p) (X p) (D.cov p (Y p) (e i))]
  rw [hLHS, hRHS]

/-! ## Part (2): the curvature forms and the second structure equation -/

/-- **Cartan Exercise 3.4.28(2), second structure equation**
`dωⁱⱼ = ∑ₖ ωᵏⱼ ∧ ωⁱₖ + Ωⁱⱼ`, relating the exterior derivative of the
connection forms to the curvature forms `Ωⁱⱼ(X,Y) = g(R(X,Y)Eⱼ, Eᵢ)`.  Proof:
expand `dωⁱⱼ(X,Y)` by metric compatibility into the curvature term
`g(R(X,Y)Eⱼ, Eᵢ)` plus a `∇E·∇E` correction; the wedge sum reproduces exactly
that correction via skew-symmetry and Parseval. -/
theorem secondStructureEquation
    (hsm : ∀ i, IsSmoothVectorField (e i))
    (hon : ∀ (q : M) i j, g.metricInner q (e i q) (e j q) = if i = j then 1 else 0)
    {X Y : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) (i j : Fin (Module.finrank ℝ E)) (p : M) :
    extDerivOneForm (connectionForm D.toAffineConnection g e j i) X Y p
      = (∑ k, wedgeOneForm (connectionForm D.toAffineConnection g e k i)
            (connectionForm D.toAffineConnection g e j k) p (X p) (Y p))
        + curvatureForm D e j i p (X p) (Y p) := by
  have hAY : IsSmoothVectorField (fun q => D.cov q (Y q) (e i)) := D.smooth_cov hY (hsm i)
  have hAX : IsSmoothVectorField (fun q => D.cov q (X q) (e i)) := D.smooth_cov hX (hsm i)
  have hskew : ∀ (v : TangentSpace I p) (a b : Fin (Module.finrank ℝ E)),
      g.metricInner p (D.cov p v (e a)) (e b p)
        = - g.metricInner p (D.cov p v (e b)) (e a p) := fun v a b => by
    have h := connectionForm_skew D e hsm hon b a p v
    simpa only [connectionForm] using h
  -- LHS: `dωⁱⱼ(X,Y) = g(R(X,Y)Eᵢ, Eⱼ) + g(∇_Y Eᵢ, ∇_X Eⱼ) − g(∇_X Eᵢ, ∇_Y Eⱼ)`.
  have hLHS : extDerivOneForm (connectionForm D.toAffineConnection g e j i) X Y p
      = g.metricInner p (curvatureTensor D.toAffineConnection X Y (e i) p) (e j p)
        + g.metricInner p (D.cov p (Y p) (e i)) (D.cov p (X p) (e j))
        - g.metricInner p (D.cov p (X p) (e i)) (D.cov p (Y p) (e j)) := by
    simp only [extDerivOneForm, connectionForm, curvatureTensor_apply]
    rw [D.metric_compat hAY (hsm j) p (X p), D.metric_compat hAX (hsm j) p (Y p),
      g.metricInner_sub_left, g.metricInner_sub_left,
      show (fun q => D.cov q (Y q) (e i)) = D.toAffineConnection.covField Y (e i) from rfl,
      show (fun q => D.cov q (X q) (e i)) = D.toAffineConnection.covField X (e i) from rfl]
    ring
  -- the curvature form as a metric pairing of the curvature tensor
  have hcurv : curvatureForm D e j i p (X p) (Y p)
      = g.metricInner p (curvatureTensor D.toAffineConnection X Y (e i) p) (e j p) := by
    simp only [curvatureForm, curvatureTensorFourAt]
    rw [curvatureTensorAt_apply D.toAffineConnection hX hY (hsm i) p]
  -- RHS wedge sum: each summand collapses by skew-symmetry, then Parseval twice.
  have key : ∀ k : Fin (Module.finrank ℝ E),
      g.metricInner p (D.cov p (X p) (e i)) (e k p)
          * g.metricInner p (D.cov p (Y p) (e k)) (e j p)
        - g.metricInner p (D.cov p (Y p) (e i)) (e k p)
          * g.metricInner p (D.cov p (X p) (e k)) (e j p)
      = g.metricInner p (D.cov p (Y p) (e i)) (e k p)
          * g.metricInner p (D.cov p (X p) (e j)) (e k p)
        - g.metricInner p (D.cov p (X p) (e i)) (e k p)
          * g.metricInner p (D.cov p (Y p) (e j)) (e k p) := by
    intro k
    rw [hskew (Y p) k j, hskew (X p) k j]; ring
  have hsum : (∑ k, wedgeOneForm (connectionForm D.toAffineConnection g e k i)
        (connectionForm D.toAffineConnection g e j k) p (X p) (Y p))
      = g.metricInner p (D.cov p (Y p) (e i)) (D.cov p (X p) (e j))
        - g.metricInner p (D.cov p (X p) (e i)) (D.cov p (Y p) (e j)) := by
    simp only [wedgeOneForm, connectionForm]
    rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_sub_distrib,
      sum_metricInner_frame p e (hon p) (D.cov p (Y p) (e i)) (D.cov p (X p) (e j)),
      sum_metricInner_frame p e (hon p) (D.cov p (X p) (e i)) (D.cov p (Y p) (e j))]
  rw [hLHS, hsum, hcurv]; ring

/-! ## The exercise, bundled -/

/-- **Exercise 3.4.28 (Cartan formalism).** For a smooth `g`-orthonormal frame
`E₁, …, Eₙ` with connection forms `ωⁱⱼ(v) = g(∇_v Eⱼ, Eᵢ)`, dual coframe
`ωⁱ(v) = g(v, Eᵢ)`, and curvature forms `Ωⁱⱼ(X,Y) = g(R(X,Y)Eⱼ, Eᵢ)`, the
connection forms are skew-symmetric and satisfy the two Cartan structure
equations:

* `(1)` `ωⁱⱼ = −ωʲᵢ` and `dωⁱ = ∑ⱼ ωʲ ∧ ωⁱⱼ`;
* `(2)` `dωⁱⱼ = ∑ₖ ωᵏⱼ ∧ ωⁱₖ + Ωⁱⱼ`.

(The surface specialization `(3)` is obtained by taking `n = 2`; the identity
`Ω¹₂ = sec · dvol` there additionally needs a Riemannian area form, not
formalized here.) -/
theorem exercise3_4_28
    (hsm : ∀ i, IsSmoothVectorField (e i))
    (hon : ∀ (q : M) i j, g.metricInner q (e i q) (e j q) = if i = j then 1 else 0) :
    (∀ (i j : Fin (Module.finrank ℝ E)) (p : M) (v : TangentSpace I p),
        connectionForm D.toAffineConnection g e i j p v
          = - connectionForm D.toAffineConnection g e j i p v)
    ∧ (∀ (i : Fin (Module.finrank ℝ E)) (X Y : Π x : M, TangentSpace I x),
        IsSmoothVectorField X → IsSmoothVectorField Y → ∀ p : M,
        extDerivOneForm (coframe g e i) X Y p
          = ∑ j, wedgeOneForm (coframe g e j)
              (connectionForm D.toAffineConnection g e i j) p (X p) (Y p))
    ∧ (∀ (i j : Fin (Module.finrank ℝ E)) (X Y : Π x : M, TangentSpace I x),
        IsSmoothVectorField X → IsSmoothVectorField Y → ∀ p : M,
        extDerivOneForm (connectionForm D.toAffineConnection g e j i) X Y p
          = (∑ k, wedgeOneForm (connectionForm D.toAffineConnection g e k i)
                (connectionForm D.toAffineConnection g e j k) p (X p) (Y p))
            + curvatureForm D e j i p (X p) (Y p)) :=
  ⟨fun i j p v => connectionForm_skew D e hsm hon i j p v,
   fun i _ _ hX hY p => firstStructureEquation D e hsm hon hX hY i p,
   fun i j _ _ hX hY p => secondStructureEquation D e hsm hon hX hY i j p⟩

end PetersenLib
