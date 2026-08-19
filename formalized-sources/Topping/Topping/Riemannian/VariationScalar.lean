import Topping.Riemannian.LieDerivative
import Topping.Riemannian.VariationCurvature
import Topping.RicciFlow.Evolution

/-!
# Variation of the Ricci and scalar curvatures, and the evolution they imply

Topping's Propositions 2.3.7 and 2.3.9 give the first variation of the Ricci
tensor and of the scalar curvature in the direction `h = ∂_tg`:

* `∂_t\Ric = -½Δ_{\mathcal L}h - ½\mathcal L_{(δG(h))^\#}g`  (2.3.6/2.3.7)
* `∂_tR = -⟨h,\Ric⟩ + δ²h - Δ(\tr h)`  (Prop. 2.3.9)

and Chapter 2 §5 specialises them to Ricci flow, where `h = -2\Ric`. This module
states both variations and then does the specialisation, which is the step that
turns §3 into §5: the general-`h` formulas are the hypotheses, the flow equation
is the substitution, and the evolution equations are the conclusions.

The scalar case is carried out in full. Substituting `h = -2\Ric` into 2.3.9:

* `-⟨h,\Ric⟩ = 2|\Ric|^2`, the reaction term, by `bilinInnerAt_neg_two_ricci`;
* `\tr h = -2R`, so `-Δ(\tr h) = 2ΔR`, by `bilinTraceAt_neg_two_ricci`;
* `δ²h = -2δ²\Ric = -ΔR`, by the contracted second Bianchi identity
  `dR = 2δ(\Ric)`: the divergence of `\Ric` is the one-form `½dR`, whose own
  divergence is `-½ΔR` in Topping's sign convention `δ = -\tr₁₂∇`.

The three contributions add to `ΔR + 2|\Ric|^2`, which is
`HasScalarCurvatureEvolutionOn` — the shared statement of I-0450. So
`hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn` is a genuine derivation
of Topping 2.5.4 from Topping 2.3.9, not a restatement, and it is what pins down
that the project's `δ`, `Δ` and `⟨·,·⟩` conventions are mutually consistent: an
error in any one of the three signs would break it.

The Ricci case is stated in both of the book's forms and the equivalence of the
two is recorded as the remaining obligation, since it needs the algebraic
identities 2.3.11/2.3.12 rewriting the lower-order terms of `Δ_{\mathcal L}`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The pointwise Ricci tensor as a bilinear form and as a tensor field -/

/-- **Math.** The Ricci tensor of `g` at `p`, as a plain bilinear form on
`T_pM`; this is the shape in which `-2\Ric` is a metric variation. -/
def ricciBilinAt (g : RiemannianMetric I M) (p : M) :
    TangentSpace I p → TangentSpace I p → ℝ :=
  fun v w => ricciTensorAt g p v w

/-! ### The contraction `⟨h,\Ric⟩` under the Ricci-flow substitution -/

/-- **Math.** `⟨-2\Ric,\Ric⟩ = -2|\Ric|^2`: the full metric contraction of the
Ricci tensor with itself is `|\Ric|^2`, so scaling one factor by `-2` scales the
contraction. Both sides are computed in the same orthonormal basis, where
`|\Ric|^2 = Σ_{ij}\Ric(e_i,e_j)^2` is the trace of the square of the Ricci
endomorphism. -/
theorem bilinInnerAt_neg_two_ricci (g : RiemannianMetric I M) (p : M) :
    bilinInnerAt g p (fun x y => -2 * ricciTensorAt g p x y) (ricciBilinAt g p) =
      -2 * ricciNormSqAt g p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  -- `|Ric|^2 = tr(Ric ∘ Ric) = Σ_{ij} Ric(e_i,e_j)^2` in an orthonormal basis.
  have hnorm : ricciNormSqAt g p =
      ∑ i, ∑ j, ricciTensorAt g p (e i) (e j) * ricciTensorAt g p (e i) (e j) := by
    rw [ricciNormSqAt, LinearMap.trace_eq_sum_inner _ e]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- `⟨e_i, Ric(Ric(e_i))⟩ = ⟨Ric(e_i), Ric(e_i)⟩ = Σ_j Ric(e_i,e_j)^2`.
    have hcomp : inner ℝ (e i)
        ((ricciEndomorphismAt g p ∘L ricciEndomorphismAt g p) (e i)) =
        inner ℝ (ricciEndomorphismAt g p (e i)) (ricciEndomorphismAt g p (e i)) := by
      rw [ContinuousLinearMap.comp_apply]
      exact (ricciEndomorphismAt_isSymmetric g p _ _).symm
    rw [show inner ℝ (e i)
        (((ricciEndomorphismAt g p ∘L ricciEndomorphismAt g p) : _ →ₗ[ℝ] _) (e i))
      = inner ℝ (e i)
        ((ricciEndomorphismAt g p ∘L ricciEndomorphismAt g p) (e i)) from rfl,
      hcomp, ← OrthonormalBasis.sum_inner_mul_inner e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (ricciEndomorphismAt g p (e i)) (e j),
      inner_ricciEndomorphismAt]
  rw [bilinInnerAt, hnorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ricciBilinAt]
  ring

/-! ### Variation of the scalar curvature (Topping Prop. 2.3.9) -/

/-- **Math.** Topping's variation of the scalar curvature,
`∂_tR = -⟨h,\Ric⟩ + δ²h - Δ(\tr h)`.

The three terms are: the contraction of `h` against the Ricci tensor; the
**double divergence** `δ²h = δ(δh)`, the divergence of the one-form `δh`, which
is a scalar; and the Laplacian of the trace of `h`. `h` enters as a covariant
`2`-tensor field through `covTensorOfBilin`, and `δ` is Topping's
`divergence = -\tr₁₂∇`. -/
def HasScalarVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) (J : Set ℝ) :
    Prop :=
  ∀ t ∈ J, ∀ p : M,
    HasDerivWithinAt (fun s => scalarCurvatureAt (g s) p)
      (-bilinInnerAt (g t) p (h t p) (ricciBilinAt (g t) p)
        + divergence (g t) (g t).leviCivitaConnection
            (divergence (g t) (g t).leviCivitaConnection
              (covTensorOfBilin (h t))) (fun i => i.elim0) p
        - metricLaplacianAt (g t)
            (fun q => trace₂ (g t) (covTensorOfBilin (h t)) q) p) J t

/-! ### The divergence of the Ricci tensor, in Topping's sign convention

Topping's `δ = -\tr₁₂∇` carries a minus sign that the Morgan--Tian `divRicciAt`
does not, so the contracted second Bianchi identity `dR = 2δ_{MT}(\Ric)` becomes
`δ(\Ric) = -½dR` here. Getting this sign right is what makes the specialisation
of Prop. 2.3.9 to Ricci flow come out as `ΔR + 2|\Ric|^2` rather than
`-ΔR + 2|\Ric|^2`. -/

/-- **Math.** Topping's covariant derivative of the Ricci tensor field agrees
with the Morgan--Tian `covRicci`: both are the Leibniz correction
`U(\Ric(X,Y)) - \Ric(∇_UX,Y) - \Ric(X,∇_UY)`, and `covDerivAlong` on a
`2`-tensor field expands to exactly that once the two-element sum over the slots
is written out. -/
theorem covDerivAlong_ricciTensorField (g : RiemannianMetric I M)
    (U X Y : SmoothVectorField I M) (p : M) :
    covDerivAlong g.leviCivitaConnection U (ricciTensorField g)
        (fun i => if i = 0 then X else Y) p =
      MorganTianLib.covRicci g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) U X Y p := by
  rw [covDerivAlong_apply, MorganTianLib.covRicci, Fin.sum_univ_two]
  have hric : ∀ A B : SmoothVectorField I M,
      ricciTensorField g (fun i => if i = 0 then A else B)
        = MorganTianLib.ricciField g g.leviCivitaConnection
            (isLeviCivita_leviCivitaConnection g) A B := by
    intro A B
    funext q
    rw [ricciTensorField, MorganTianLib.ricciField, ← ricciTensorAt_eq_ricciAt]
    simp
  -- Updating slot `0` replaces `X`, updating slot `1` replaces `Y`.
  have h0 : Function.update (fun i : Fin 2 => if i = 0 then X else Y) 0
      (g.leviCivitaConnection.cov U X)
      = fun i => if i = 0 then g.leviCivitaConnection.cov U X else Y := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · rw [Function.update_of_ne hi]; simp [hi]
  have h1 : Function.update (fun i : Fin 2 => if i = 0 then X else Y) 1
      (g.leviCivitaConnection.cov U Y)
      = fun i => if i = 0 then X else g.leviCivitaConnection.cov U Y := by
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      simp
    · have hi1 : i = 1 := by omega
      subst hi1; simp
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte, h0, h1, hric]
  ring

/-- **Math.** In Topping's convention the divergence of the Ricci tensor is
`-½dR`: the Morgan--Tian divergence is `+½dR` by the contracted second Bianchi
identity, and `δ = -\tr₁₂∇` flips the sign. -/
theorem divergence_ricciTensorField (g : RiemannianMetric I M)
    (Z : SmoothVectorField I M) (p : M) :
    divergence g g.leviCivitaConnection (ricciTensorField g) (fun _ => Z) p =
      -(1 / 2 : ℝ) * Z.dir (fun q => scalarCurvatureAt g q) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  rw [divergence_apply]
  -- Each summand is `(∇_{e_i}Ric)(e_i, Z)`, i.e. `covRicciAt` at `(e_i, e_i, Z p)`.
  have hsum : ∀ i, covDerivAlong g.leviCivitaConnection
      (MorganTianLib.extendVector p (e i)) (ricciTensorField g)
      (Fin.cons (MorganTianLib.extendVector p (e i)) (fun _ => Z)) p =
      MorganTianLib.covRicciAt g g.leviCivitaConnection
        (isLeviCivita_leviCivitaConnection g) p (e i) (e i) (Z p) := by
    intro i
    have hcons : (Fin.cons (MorganTianLib.extendVector p (e i)) (fun _ => Z) :
        Fin 2 → SmoothVectorField I M)
        = fun j => if j = 0 then MorganTianLib.extendVector p (e i) else Z := by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j; simp
    rw [hcons, covDerivAlong_ricciTensorField]
    -- `covRicciAt` at `(e i, e i, Z p)` is `covRicci` on any fields taking those
    -- values at `p`; here the first two are already the chosen extensions.
    have hZ := MorganTianLib.covRicciAt_eq g g.leviCivitaConnection
      (isLeviCivita_leviCivitaConnection g)
      (MorganTianLib.extendVector p (e i))
      (MorganTianLib.extendVector p (e i)) Z p
    simp only [MorganTianLib.extendVector_apply] at hZ
    exact hZ.symm
  rw [Finset.sum_congr rfl fun i _ => hsum i,
    ← MorganTianLib.divRicciAt_eq_sum_orthonormalBasis g g.leviCivitaConnection
      (isLeviCivita_leviCivitaConnection g) p (Z p) e,
    dir_scalarCurvatureAt_eq_two_divRicci g Z p]
  ring

/-! ### The divergence of an exact one-form

`δ(df) = -Δf`. In Topping's convention `δ = -\tr₁₂∇`, and `∇(df)` is the Hessian,
whose metric trace is the Laplacian; the sign is the one carried by `δ`. This is
the identity that turns the double divergence `δ²h` of Prop. 2.3.9 into a
Laplacian once `δh` has been recognised as a multiple of `dR`. -/

/-- **Math.** The differential `df` of a function, as a covariant `1`-tensor
field: `df(X) = X(f)`. -/
def differentialOneForm (f : M → ℝ) : CovTensorField I M 1 :=
  fun Y p => (Y 0).dir f p

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** An exact one-form is pointwise linear: `df(v) = df_p(v)` is the
differential, which is linear in `v` by construction. So the metric dual `(df)^\#`
does satisfy `⟨(df)^\#,v⟩ = df(v)` — the gradient really is the gradient — and this
is the canonical instance of `IsPointwiseLinear`.

Note this needs the value of `df` on a tangent vector to be independent of the
extension used to compute it, which holds because `dir` at `p` only sees the
vector at `p`. -/
theorem isPointwiseLinear_differentialOneForm (g : RiemannianMetric I M)
    (f : M → ℝ) (p : M) :
    IsPointwiseLinear g (differentialOneForm f) p := by
  have hval : ∀ v : TangentSpace I p,
      oneFormCovec g (differentialOneForm f) p v = Riemannian.dirTangent f v := by
    intro v
    rw [oneFormCovec, differentialOneForm, Riemannian.dirTangent,
      SmoothVectorField.dir, MorganTianLib.extendVector_apply]
  refine ⟨fun v w => ?_, fun c v => ?_⟩
  · rw [hval, hval, hval, Riemannian.dirTangent_add]
  · rw [hval, hval, Riemannian.dirTangent_smul]

omit [I.Boundaryless] in
/-- **Math.** `∇_X(df) = \Hess(f)(X,\cdot)`: the covariant derivative of the
exact one-form `df` is the Hessian of `f`, the Leibniz correction of
`covDerivAlong` being exactly the `-(∇_XY)(f)` of the Hessian. -/
theorem covDerivAlong_differentialOneForm (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (f : M → ℝ) (p : M) :
    covDerivAlong g.leviCivitaConnection X (differentialOneForm f)
        (fun _ => Y) p =
      MorganTianLib.hessian g.leviCivitaConnection f X Y p := by
  rw [covDerivAlong_apply, MorganTianLib.hessian]
  simp only [differentialOneForm, Finset.univ_unique, Finset.sum_singleton,
    Subsingleton.elim (default : Fin 1) 0, Function.update_self]
  rfl

omit [I.Boundaryless] in
/-- **Math.** `δ(df) = -Δf`: the divergence of an exact one-form is minus the
Laplace--Beltrami operator on the function. Tracing the previous lemma over an
orthonormal basis turns `∇(df)` into `\Hess(f)` and the trace of the Hessian is
`Δf`; the minus sign is the one in `δ = -\tr₁₂∇`. -/
theorem divergence_differentialOneForm (g : RiemannianMetric I M) (f : M → ℝ)
    (Y : Fin 0 → SmoothVectorField I M) (p : M) :
    divergence g g.leviCivitaConnection (differentialOneForm f) Y p =
      -metricLaplacianAt g f p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : ¬ Module.finrank ℝ E = 0 := NeZero.ne _
  rw [divergence_apply]
  simp only [metricLaplacianAt, hdim, ↓reduceDIte, MorganTianLib.laplacianAt,
    MorganTianLib.hessianAt]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Both sides are `Hess(f)(e_i, e_i)`; the `Fin.cons` tuple has the single
  -- remaining slot fed the same basis vector.
  have hcons : (Fin.cons (MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)) Y : Fin 1 → SmoothVectorField I M)
      = fun _ => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp
    · exact fun j => j.elim0
  rw [hcons, covDerivAlong_differentialOneForm]

/-! ### From the variation formula to the Ricci-flow evolution equation

This is the step that connects Topping's §3 to his §5. Substituting `h = -2\Ric`
into Prop. 2.3.9 and simplifying each of the three terms produces exactly
`∂_tR = ΔR + 2|\Ric|^2`. -/

/-- **Math.** Under the Ricci-flow substitution `h = -2\Ric`, the covariant
`2`-tensor field of `h` is `-2` times the Ricci tensor field. -/
theorem covTensorOfBilin_neg_two_ricci (g : RiemannianMetric I M) :
    covTensorOfBilin (fun p (x y : TangentSpace I p) => -2 * ricciTensorAt g p x y)
      = fun (Y : Fin 2 → SmoothVectorField I M) p =>
        -2 * ricciTensorField g Y p := by
  funext Y p
  rw [covTensorOfBilin, ricciTensorField]

/-- **Math.** The Ricci tensor field is differentiable in the base point. This
is `MorganTianLib.ricciField_mdifferentiableAt` transported across the bridge
`ricciTensorAt = ricciAt`: on any pair of smooth vector fields the Ricci tensor
is locally a finite sum of curvature components in a smooth orthonormal frame,
hence smooth. -/
theorem ricciTensorField_mdifferentiableAt (g : RiemannianMetric I M)
    (Y : Fin 2 → SmoothVectorField I M) (q : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (ricciTensorField g Y) q := by
  have hfun : ricciTensorField g Y
      = MorganTianLib.ricciField g g.leviCivitaConnection
          (isLeviCivita_leviCivitaConnection g) (Y 0) (Y 1) := by
    funext r
    rw [ricciTensorField, MorganTianLib.ricciField, ← ricciTensorAt_eq_ricciAt]
  rw [hfun]
  exact MorganTianLib.ricciField_mdifferentiableAt g g.leviCivitaConnection
    (isLeviCivita_leviCivitaConnection g) (Y 0) (Y 1) q

omit [I.Boundaryless] in
/-- **Math.** The divergence is homogeneous over constants, `δ(cA) = c·δA`. Both
the Leibniz derivative and the metric trace defining `δ` are linear, so a
constant factor passes through; differentiability of the components is needed to
differentiate `c·A`. -/
theorem divergence_const_mul (g : RiemannianMetric I M) (c : ℝ) {k : ℕ}
    {A : CovTensorField I M (k + 1)}
    (hA : ∀ (Y : Fin (k + 1) → SmoothVectorField I M) (q : M),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (A Y) q)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    divergence g g.leviCivitaConnection
        (fun (W : Fin (k + 1) → SmoothVectorField I M) q => c * A W q) Y p
      = c * divergence g g.leviCivitaConnection A Y p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [divergence_apply, covDerivAlong_apply]
  rw [mul_neg, Finset.mul_sum]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
  rw [(MorganTianLib.extendVector p
    (stdOrthonormalBasis ℝ (TangentSpace I p) i)).dir_const_mul c p (hA _ p),
    ← Finset.mul_sum, mul_sub]

/-- **Math.** `δ(-2\Ric) = dR`: the divergence of the Ricci-flow variation is the
differential of the scalar curvature. Two minus signs cancel — the `-2` of the
flow and the `-½` of `δ(\Ric)` — which is why the reaction term of the scalar
evolution ends up with the `+ΔR` of a genuine heat equation. -/
theorem divergence_covTensorOfBilin_neg_two_ricci (g : RiemannianMetric I M)
    (Z : SmoothVectorField I M) (p : M) :
    divergence g g.leviCivitaConnection
        (covTensorOfBilin
          (fun q (x y : TangentSpace I q) => -2 * ricciTensorAt g q x y))
        (fun _ => Z) p =
      Z.dir (fun q => scalarCurvatureAt g q) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [covTensorOfBilin_neg_two_ricci]
  -- `δ` is linear over constants: pull the `-2` out of the trace of `∇`.
  have hlin := divergence_const_mul (g := g) (c := -2)
    (A := ricciTensorField g) (ricciTensorField_mdifferentiableAt g)
    (fun _ => Z) p
  rw [hlin, divergence_ricciTensorField]
  ring


/-- **Math.** `\tr(-2\Ric) = -2R`: the metric trace of the Ricci-flow variation,
as a covariant `2`-tensor field, is `-2` times the scalar curvature. This
connects `trace₂` (which traces a tensor field by feeding it `extendVector`s) to
the pointwise `bilinTraceAt`, and is what lets the third term of Prop. 2.3.9 be
rewritten as a Laplacian of the scalar curvature. -/
theorem trace₂_covTensorOfBilin_neg_two_ricci (g : RiemannianMetric I M)
    (q : M) :
    trace₂ g (covTensorOfBilin
        (fun r (x y : TangentSpace I r) => -2 * ricciTensorAt g r x y)) q
      = -2 * scalarCurvatureAt g q := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← bilinTraceAt_neg_two_ricci g q, trace₂, traceFirstTwo, bilinTraceAt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [covTensorOfBilin]
  simp only [Fin.cons_zero, Fin.cons_one, MorganTianLib.extendVector_apply]

/-- **Math.** **Topping's scalar-curvature evolution, derived.** If the family
`g` obeys Topping's variation formula `∂_tR = -⟨h,\Ric⟩ + δ²h - Δ(\tr h)` in the
direction `h = -2\Ric`, then it satisfies `∂_tR = ΔR + 2|\Ric|^2`.

Note that Ricci flow is *not* a hypothesis here: it enters only through the choice
of direction. Nothing forces `g` to solve `∂_tg = -2\Ric`, so the statement is
marginally more general than the book's, which reads the same computation with the
flow equation in force. For a family that does satisfy `IsRicciFlowOn`,
`isMetricVariationOn_of_isRicciFlowOn` supplies exactly this direction, which is
how the two line up.

This is Prop. 2.5.4 from Prop. 2.3.9. Each of the three terms of 2.3.9 is
computed under the substitution `h = -2\Ric`:

* `-⟨h,\Ric⟩ = 2|\Ric|^2`, by `bilinInnerAt_neg_two_ricci`;
* `δ²h = δ(dR) = -ΔR`, by `divergence_covTensorOfBilin_neg_two_ricci` followed by
  `divergence_differentialOneForm`;
* `\tr h = -2R`, so `-Δ(\tr h) = 2ΔR`, by `bilinTraceAt_neg_two_ricci`.

Adding: `2|\Ric|^2 - ΔR + 2ΔR = ΔR + 2|\Ric|^2`.

The only hypothesis beyond the variation formula itself is smoothness of the
scalar curvature at each fixed time, which is what makes `Δ` linear over the
constant `-2`. Everything else is proved: differentiability of the Ricci tensor
field comes from `ricciTensorField_mdifferentiableAt` and the trace identity from
`trace₂_covTensorOfBilin_neg_two_ricci`. -/
theorem hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hvar : HasScalarVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) J)
    (hscal : ∀ t : ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => scalarCurvatureAt (g t) q)) :
    HasScalarCurvatureEvolutionOn g J := by
  intro t ht p
  have hv := hvar t ht p
  -- Term 1: `-⟨-2Ric, Ric⟩ = 2|Ric|^2`.
  have h1 : bilinInnerAt (g t) p
      (fun x y => -2 * ricciTensorAt (g t) p x y) (ricciBilinAt (g t) p)
      = -2 * ricciNormSqAt (g t) p :=
    bilinInnerAt_neg_two_ricci (g t) p
  -- Term 2: `δ²h = δ(dR) = -ΔR`.
  have h2 : divergence (g t) (g t).leviCivitaConnection
      (divergence (g t) (g t).leviCivitaConnection
        (covTensorOfBilin (fun q (x y : TangentSpace I q) =>
          -2 * ricciTensorAt (g t) q x y))) (fun i => i.elim0) p
      = -metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p := by
    have hone : divergence (g t) (g t).leviCivitaConnection
        (covTensorOfBilin (fun q (x y : TangentSpace I q) =>
          -2 * ricciTensorAt (g t) q x y))
        = differentialOneForm (fun q => scalarCurvatureAt (g t) q) := by
      funext Y q
      rw [differentialOneForm]
      have h := divergence_covTensorOfBilin_neg_two_ricci (g t) (Y 0) q
      -- `divergence` of a `2`-tensor is evaluated on the single field `Y 0`.
      rw [show (fun _ : Fin 1 => Y 0) = Y from funext fun j =>
        by rw [Subsingleton.elim j 0]] at h
      exact h
    rw [hone, divergence_differentialOneForm]
  -- Term 3: `tr h = -2R`, so `-Δ(tr h) = 2ΔR`.
  have h3 : metricLaplacianAt (g t)
      (fun q => trace₂ (g t)
        (covTensorOfBilin (fun r (x y : TangentSpace I r) =>
          -2 * ricciTensorAt (g t) r x y)) q) p
      = -2 * metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p := by
    rw [show (fun q => trace₂ (g t)
        (covTensorOfBilin (fun r (x y : TangentSpace I r) =>
          -2 * ricciTensorAt (g t) r x y)) q)
      = fun q => -2 * scalarCurvatureAt (g t) q from
      funext fun q => trace₂_covTensorOfBilin_neg_two_ricci (g t) q]
    exact metricLaplacianAt_const_mul (g t) (-2) (hscal t) p
  rw [h1, h2, h3] at hv
  -- `-(-2|Ric|^2) + (-ΔR) - (-2ΔR) = ΔR + 2|Ric|^2`.
  convert hv using 1
  ring

/-! ### Variation of the Ricci tensor (Topping Prop. 2.3.7) -/

/-- **Math.** Topping's variation of the Ricci tensor in the form (2.3.6),
`∂_t\Ric = -½Δ_{\mathcal L}h - ½\mathcal L_{(δG(h))^\#}g`.

The Lie-derivative term is the symmetric gradient of the vector field dual to the
one-form `δG(h)`, which is `symmetricGradient` applied to `(δG(h))^\#`; the
extension of that pointwise dual vector to a field is immaterial because
`symmetricGradient` is evaluated at the one point `p`. -/
def HasRicciVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) (J : Set ℝ) :
    Prop :=
  ∀ t ∈ J, ∀ (X W : SmoothVectorField I M) (p : M),
    HasDerivWithinAt
      (fun s => ricciTensorAt (g s) p (X p) (W p))
      (-(1 / 2 : ℝ) *
          lichnerowiczLaplacian (g t) (covTensorOfBilin (h t))
            (fun i => if i = 0 then X else W) p
        - (1 / 2 : ℝ) *
          symmetricGradient (g t)
            (MorganTianLib.extendVector p
              (oneFormSharp (g t)
                (divergence (g t) (g t).leviCivitaConnection
                  (gravitationTensor (g t) (covTensorOfBilin (h t)))) p))
            (fun i => if i = 0 then X else W) p) J t

/-- **Math.** Topping's second, pointwise form of the Ricci variation,
`∂_t\Ric(X,W) = Δ\Ric(X,W) - 2⟨\Ric(X),\Ric(W)⟩ + 2⟨\Rm(X,\cdot,W,\cdot),\Ric⟩`,
which is the form that specialises to the Ricci-flow evolution equation. The
middle term pairs the two Ricci endomorphisms; the last contracts the curvature
against `\Ric` over an orthonormal basis. -/
def HasRicciVariationPointwiseOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    Prop :=
  ∀ t ∈ J, ∀ (X W : SmoothVectorField I M) (p : M),
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(g t).toRiemannianMetric⟩
    HasDerivWithinAt
      (fun s => ricciTensorAt (g s) p (X p) (W p))
      (roughLaplacian (g t) (g t).leviCivitaConnection
          (ricciTensorField (g t)) (fun i => if i = 0 then X else W) p
        - 2 * inner ℝ (ricciEndomorphismAt (g t) p (X p))
            (ricciEndomorphismAt (g t) p (W p))
        + 2 * ∑ i, ∑ j,
            riemannCurvatureAt (g t) p (X p)
                (stdOrthonormalBasis ℝ (TangentSpace I p) i) (W p)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
              ricciTensorAt (g t) p
                (stdOrthonormalBasis ℝ (TangentSpace I p) i)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j)) J t

end Topping

end
