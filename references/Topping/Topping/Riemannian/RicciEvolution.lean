import Topping.Riemannian.VariationScalar

/-!
# The two forms of the Ricci evolution equation

Topping's Proposition 2.5.3 states the evolution of the Ricci tensor twice:
compactly as `∂_t\Ric = Δ_{\mathcal L}(\Ric)`, and then "or, pointwise" as

`∂_t\Ric(X,W) = Δ\Ric(X,W) - 2⟨\Ric(X),\Ric(W)⟩ + 2⟨\Rm(X,·,W,·),\Ric⟩`.

The two displays are the same equation, and this module proves it: the content is
that the Lichnerowicz Laplacian *of the Ricci tensor itself* has lower-order terms
which collapse to the book's pointwise expressions.

Both collapses are pure pointwise linear algebra:

* the two Ricci terms `-h(X,\Ric(W)) - h(W,\Ric(X))` of `Δ_{\mathcal L}`, taken at
  `h = \Ric`, become `-2⟨\Ric(X),\Ric(W)⟩`, because `\Ric(x,\Ric(w))` is the inner
  product of the two images under the Ricci endomorphism, and the two terms are
  exchanged by symmetry of that endomorphism;
* the curvature term `2\tr h(R(X,·)W,·)`, taken at `h = \Ric`, becomes
  `2⟨\Rm(X,·,W,·),\Ric⟩`, by expanding `R(X,e_i)W` in the orthonormal basis: its
  `e_j`-component is `\Rm(X,e_i,W,e_j)`, and the remaining `\Ric(e_j,e_i)` is
  symmetric.

The consequence, `hasRicciEvolutionOn_iff_pointwise`, is that the two Lean
predicates stating the two displays are *equivalent*, not merely both present.
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

/-! ### Expanding a tangent vector fed into the Ricci tensor -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Orthonormal expansion of a tangent vector,
`v = Σ_j ⟨e_j,v⟩e_j`. -/
theorem sum_inner_smul_stdOrthonormalBasis (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ j, (inner ℝ (stdOrthonormalBasis ℝ (TangentSpace I p) j) v) •
        (stdOrthonormalBasis ℝ (TangentSpace I p) j : TangentSpace I p) = v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  have hcoef : ∀ j, (inner ℝ (e j) v) • (e j : TangentSpace I p)
      = (e.repr v).ofLp j • e j := by
    intro j
    rw [e.repr_apply_apply v j]
  rw [Finset.sum_congr rfl fun j _ => hcoef j]
  exact e.sum_repr v

/-- **Math.** The Ricci tensor is linear in its first slot, so a vector fed into
it may be expanded over an orthonormal basis:
`\Ric(v,w) = Σ_j⟨e_j,v⟩\Ric(e_j,w)`. -/
theorem ricciTensorAt_expand_left (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciTensorAt g p v w =
      ∑ j, (inner ℝ (stdOrthonormalBasis ℝ (TangentSpace I p) j) v) *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) j) w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  conv_lhs => rw [← sum_inner_smul_stdOrthonormalBasis g p v]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-! ### The Ricci terms of the Lichnerowicz Laplacian at `h = Ric`

`Δ_{\mathcal L}` carries `-h(X,\Ric(W)) - h(W,\Ric(X))`. At `h = \Ric` each term
is `\Ric(x,\Ric(w))`, which is `⟨\Ric(x),\Ric(w)⟩` by the defining property of
the Ricci endomorphism; the two terms coincide by its symmetry, giving
`-2⟨\Ric(X),\Ric(W)⟩`. -/

/-- **Math.** `\Ric(x,\Ric(w)) = ⟨\Ric(x),\Ric(w)⟩`: feeding the Ricci
endomorphism's value into the Ricci bilinear form is the inner product of the two
images. -/
theorem ricciTensorAt_ricciEndomorphismAt (g : RiemannianMetric I M) (p : M)
    (x w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciTensorAt g p x (ricciEndomorphismAt g p w) =
      inner ℝ (ricciEndomorphismAt g p x) (ricciEndomorphismAt g p w) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← inner_ricciEndomorphismAt g p x (ricciEndomorphismAt g p w)]

/-- **Math.** The two Ricci terms of `Δ_{\mathcal L}` agree at `h = \Ric`:
`\Ric(x,\Ric(w)) = \Ric(w,\Ric(x))`, by symmetry of the Ricci endomorphism. -/
theorem ricciTensorAt_ricciEndomorphismAt_comm (g : RiemannianMetric I M) (p : M)
    (x w : TangentSpace I p) :
    ricciTensorAt g p x (ricciEndomorphismAt g p w) =
      ricciTensorAt g p w (ricciEndomorphismAt g p x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [ricciTensorAt_ricciEndomorphismAt, ricciTensorAt_ricciEndomorphismAt,
    real_inner_comm]

/-! ### The curvature term of the Lichnerowicz Laplacian at `h = Ric`

`Δ_{\mathcal L}` carries `2\tr h(R(X,·)W,·) = 2Σ_i h(R(X,e_i)W, e_i)`. At
`h = \Ric` the first slot is a curvature vector, and expanding it over the basis
turns the single sum into Topping's double sum
`Σ_{ij}\Rm(X,e_i,W,e_j)\Ric(e_j,e_i)`: the `e_j`-component of `R(X,e_i)W` is
exactly `\Rm(X,e_i,W,e_j)`.

This identifies the two displays' curvature terms, and it is the step where the
metric-dual reading of `\Rm` matters: `⟨R(x,y)z,w⟩ = \Rm(x,y,z,w)` is what
`riemannCurvatureAt` is, so the expansion coefficient and the curvature component
are the same number by definition rather than by a further lemma. -/

omit [I.Boundaryless] in
/-- **Math.** The `e_j`-component of the curvature vector `R(x,y)z` is the
curvature tensor component `\Rm(x,y,z,e_j)`: this is the definition of the
`(0,4)` curvature form as the metric lowering of the curvature operator. -/
theorem inner_curvatureOperatorAt_eq_riemannCurvatureAt (g : RiemannianMetric I M)
    (p : M) (x y z v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ v (g.leviCivitaConnection.curvatureOperatorAt p x y z) =
      riemannCurvatureAt g p x y z v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [riemannCurvatureAt, AffineConnection.curvatureFormAt]
  exact real_inner_comm _ _

/-- **Math.** Expanding the curvature vector `R(x,y)z` in the first slot of the
Ricci tensor gives Topping's curvature-Ricci contraction:
`\Ric(R(x,y)z, u) = Σ_j\Rm(x,y,z,e_j)\Ric(e_j,u)`. -/
theorem ricciTensorAt_curvatureOperatorAt_expand (g : RiemannianMetric I M)
    (p : M) (x y z u : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciTensorAt g p (g.leviCivitaConnection.curvatureOperatorAt p x y z) u =
      ∑ j, riemannCurvatureAt g p x y z (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) j) u := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [ricciTensorAt_expand_left g p _ u]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_curvatureOperatorAt_eq_riemannCurvatureAt]

/-- **Math.** The field-level curvature operator at `p` is the pointwise one on
the values of the fields, which is tensoriality of the curvature. -/
theorem curvatureOperator_apply_eq_curvatureOperatorAt (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    curvatureOperator g X Y Z p =
      g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (Z p) :=
  (g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl).symm

/-! ### The Lichnerowicz Laplacian of the Ricci tensor, expanded

This is Topping 2.5.3: the two displays of the Ricci evolution equation have the
same right-hand side. -/

/-- **Math.** **Topping's two forms of the Ricci evolution agree.** The
Lichnerowicz Laplacian *of the Ricci tensor* expands to the book's pointwise
expression:
`Δ_{\mathcal L}(\Ric)(X,W) = Δ\Ric(X,W) - 2⟨\Ric(X),\Ric(W)⟩
+ 2Σ_{ij}\Rm(X,e_i,W,e_j)\Ric(e_i,e_j)`.

The rough Laplacian term is untouched; the two Ricci terms of `Δ_{\mathcal L}`
collapse to `-2⟨\Ric(X),\Ric(W)⟩` because they are equal by symmetry of the Ricci
endomorphism; the curvature term expands from a single trace into the book's
double sum. -/
theorem lichnerowiczLaplacian_ricciTensorField_apply (g : RiemannianMetric I M)
    (X W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    lichnerowiczLaplacian g (ricciTensorField g)
        (fun i => if i = 0 then X else W) p =
      roughLaplacian g g.leviCivitaConnection (ricciTensorField g)
          (fun i => if i = 0 then X else W) p
        - 2 * inner ℝ (ricciEndomorphismAt g p (X p))
            (ricciEndomorphismAt g p (W p))
        + 2 * ∑ i, ∑ j,
            riemannCurvatureAt g p (X p)
                (stdOrthonormalBasis ℝ (TangentSpace I p) i) (W p)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
              ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  -- The two Ricci terms of `Δ_{\mathcal L}`, at `h = Ric`.
  have hR1 : ricciTensorField g
      (fun i : Fin 2 => if i = 0 then X else
        MorganTianLib.extendVector p (ricciEndomorphismAt g p (W p))) p
      = inner ℝ (ricciEndomorphismAt g p (X p))
          (ricciEndomorphismAt g p (W p)) := by
    rw [ricciTensorField]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte,
      MorganTianLib.extendVector_apply]
    exact ricciTensorAt_ricciEndomorphismAt g p (X p) (W p)
  have hR2 : ricciTensorField g
      (fun i : Fin 2 => if i = 0 then W else
        MorganTianLib.extendVector p (ricciEndomorphismAt g p (X p))) p
      = inner ℝ (ricciEndomorphismAt g p (X p))
          (ricciEndomorphismAt g p (W p)) := by
    rw [ricciTensorField]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte,
      MorganTianLib.extendVector_apply]
    rw [← ricciTensorAt_ricciEndomorphismAt_comm,
      ricciTensorAt_ricciEndomorphismAt]
  -- The curvature term: one trace becomes the book's double sum.
  have hcurv : ∀ i, ricciTensorField g
      (fun j : Fin 2 => if j = 0 then
          MorganTianLib.extendVector p
            (curvatureOperator g X (MorganTianLib.extendVector p (e i)) W p)
        else MorganTianLib.extendVector p (e i)) p
      = ∑ j, riemannCurvatureAt g p (X p) (e i) (W p) (e j) *
          ricciTensorAt g p (e i) (e j) := by
    intro i
    rw [ricciTensorField]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte,
      MorganTianLib.extendVector_apply]
    rw [curvatureOperator_apply_eq_curvatureOperatorAt]
    simp only [MorganTianLib.extendVector_apply]
    rw [ricciTensorAt_curvatureOperatorAt_expand]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ricciTensorAt_symm g p (e j) (e i)]
  rw [lichnerowiczLaplacian]
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte]
  rw [hR1, hR2, Finset.sum_congr rfl fun i _ => hcurv i]
  ring

/-! ### The two predicates are equivalent

`HasRicciEvolutionOn` states `∂_t\Ric = Δ_{\mathcal L}(\Ric)` and
`HasRicciVariationPointwiseOn` states the pointwise display. The expansion above
says their right-hand sides agree, so the predicates are equivalent — which is
what Topping's "or, pointwise" asserts. The only bookkeeping is that one predicate
quantifies over a `2`-tuple of fields and the other over two fields; a `2`-tuple
is determined by its two entries. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A `2`-tuple of vector fields is its pair of entries. -/
theorem funext_fin_two (Y : Fin 2 → SmoothVectorField I M) :
    Y = fun i => if i = 0 then Y 0 else Y 1 := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · have : i = 1 := by omega
    subst this; simp

/-- **Math.** **Topping 2.5.3: the compact and pointwise forms of the Ricci
evolution equation are the same statement.** `∂_t\Ric = Δ_{\mathcal L}(\Ric)` holds
on `J` iff `∂_t\Ric(X,W) = Δ\Ric(X,W) - 2⟨\Ric(X),\Ric(W)⟩
+ 2⟨\Rm(X,·,W,·),\Ric⟩` holds there.

This is what turns the book's "or, pointwise" into a theorem: the equivalence is
`lichnerowiczLaplacian_ricciTensorField_apply` applied under the derivative, and
nothing analytic is involved — the two right-hand sides are equal pointwise. -/
theorem hasRicciEvolutionOn_iff_pointwise (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) :
    HasRicciEvolutionOn g J ↔ HasRicciVariationPointwiseOn g J := by
  constructor
  · intro hev t ht X W p
    have h := hev t ht (fun i => if i = 0 then X else W) p
    rw [lichnerowiczLaplacian_ricciTensorField_apply] at h
    have hfun : (fun s => ricciTensorField (g s)
        (fun i : Fin 2 => if i = 0 then X else W) p)
        = fun s => ricciTensorAt (g s) p (X p) (W p) := by
      funext s
      rw [ricciTensorField]
      simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte]
    rw [hfun] at h
    exact h
  · intro hev t ht Y p
    have h := hev t ht (Y 0) (Y 1) p
    rw [← lichnerowiczLaplacian_ricciTensorField_apply] at h
    have hfun : (fun s => ricciTensorAt (g s) p (Y 0 p) (Y 1 p))
        = fun s => ricciTensorField (g s) Y p := by
      funext s
      rw [ricciTensorField]
    rw [hfun] at h
    rw [funext_fin_two Y]
    exact h

end Topping

end
