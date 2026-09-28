import PetersenLib.Ch01.HopfCoordinateMetrics

/-!
# The `Fin.snoc` ambient bridge `ℂ^{n+1} ⊕₂ ℂ ≅ ℂ^{n+2}`

Chapter 1 realizes the ambient complex space `ℂ^{n+2}` of the generalized Hopf fibration in two
different ways:

* as the `ℓ²`-product `WithLp 2 (EuclideanSpace ℂ (Fin (n+1)) × ℂ)` — the model in which the doubly
  warped parametrization `(t, z, w) ↦ (sin(t)·z, cos(t)·w)` of `S^{2n+3}` naturally lives
  (`sphereOddAsDoublyWarpedProduct`, Example 1.4.14);
* as the coordinate space `EuclideanSpace ℂ (Fin (n+2))` — the model in which `ℂP^{n+1}` is built
  (`ComplexProjectiveSpace`), because its affine charts index the homogeneous coordinates by
  `Fin (n+2)`.

The two are the *same* space: both norms are the `ℓ²` norm of the same `n+2` complex coordinates,
and `Fin.snoc` reindexes one list of coordinates as the other.  This file makes that identification
a `LinearIsometryEquiv` over `ℝ` (`snocLpEquiv`), records that it is in fact `ℂ`-linear
(`snocLpEquiv_complex_smul`, needed for it to intertwine the two circle actions), and uses it to
transport Example 1.4.14's source clause into the coordinate model (`genHopfAmbient`,
`pullbackForm_genHopfAmbient`) — which is where it can meet `ℂP^{n+1}`.

The transport is painless because *both* ambient models are single-chart vector-space models
`𝓘(ℝ, ·)`: no product `ModelWithCorners` ever appears, so the chain rule for the composite
`snocLpEquiv ∘ (doubly warped map)` applies directly, and the pullback form is unchanged because a
linear isometry preserves inner products (`pullbackForm_linearIsometryEquiv`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.4.14.
-/

open Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

variable {n : ℕ}

/-! ## Pullbacks along a linear isometry of the ambient space -/

section PullbackIsometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** Post-composing a map `f : M → V` with a linear isometry `L : V ≃ₗᵢ[ℝ] W` does not
change the pullback of the ambient inner product: by the chain rule `D(L ∘ f) = L ∘ Df`, and `L`
preserves inner products.

Both ambient spaces are modelled on the single chart `𝓘(ℝ, ·)`, so no product model with corners
appears and no instance has to be transported. -/
theorem pullbackForm_linearIsometryEquiv (L : V ≃ₗᵢ[ℝ] W) {f : M → V} {p : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, V) f p) (u v : TangentSpace I p) :
    pullbackForm (I := I) (innerProductSpaceMetric W) (fun x => L (f x)) p u v
      = pullbackForm (I := I) (innerProductSpaceMetric V) f p u v := by
  have hL : HasMFDerivAt 𝓘(ℝ, V) 𝓘(ℝ, W) L (f p) (L.toContinuousLinearEquiv : V →L[ℝ] W) :=
    (L.toContinuousLinearEquiv : V →L[ℝ] W).hasFDerivAt.hasMFDerivAt
  have hcomp : HasMFDerivAt I 𝓘(ℝ, W) (fun x => L (f x)) p
      ((L.toContinuousLinearEquiv : V →L[ℝ] W).comp (mfderiv I 𝓘(ℝ, V) f p)) :=
    HasMFDerivAt.comp p hL hf.hasMFDerivAt
  rw [pullbackForm_apply, pullbackForm_apply, innerProductSpaceMetric_apply,
    innerProductSpaceMetric_apply, hcomp.mfderiv]
  exact L.inner_map_map _ _

end PullbackIsometry

/-! ## Differentiability into the `ℓ²`-product -/

section MDiffToLp

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** A pair of differentiable maps assembles to a differentiable map into the `ℓ²`-product:
the companion of `mfderiv_toLp_prodMk`, proved the same way, by writing the map as
`lpInl ∘ f₁ + lpInr ∘ f₂`. -/
theorem mdifferentiableAt_toLp_prodMk {f₁ : M → E₁} {f₂ : M → E₂} {p : M}
    (h₁ : MDifferentiableAt I 𝓘(ℝ, E₁) f₁ p) (h₂ : MDifferentiableAt I 𝓘(ℝ, E₂) f₂ p) :
    MDifferentiableAt I 𝓘(ℝ, WithLp 2 (E₁ × E₂))
      (fun x => (WithLp.toLp 2 (f₁ x, f₂ x) : WithLp 2 (E₁ × E₂))) p := by
  have hfun : (fun x => (WithLp.toLp 2 (f₁ x, f₂ x) : WithLp 2 (E₁ × E₂)))
      = (fun x => ((lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)) (f₁ x)))
        + fun x => ((lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂)) (f₂ x)) := by
    funext x; exact toLp_eq_lpInl_add_lpInr _ _
  have hd₁ : HasMFDerivAt I 𝓘(ℝ, WithLp 2 (E₁ × E₂)) (fun x => (lpInl (f₁ x) : WithLp 2 (E₁ × E₂)))
      p ((lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)).comp (mfderiv I 𝓘(ℝ, E₁) f₁ p)) :=
    HasMFDerivAt.comp p (lpInl.hasFDerivAt.hasMFDerivAt) h₁.hasMFDerivAt
  have hd₂ : HasMFDerivAt I 𝓘(ℝ, WithLp 2 (E₁ × E₂)) (fun x => (lpInr (f₂ x) : WithLp 2 (E₁ × E₂)))
      p ((lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂)).comp (mfderiv I 𝓘(ℝ, E₂) f₂ p)) :=
    HasMFDerivAt.comp p (lpInr.hasFDerivAt.hasMFDerivAt) h₂.hasMFDerivAt
  rw [hfun]
  exact (hd₁.add hd₂).mdifferentiableAt

end MDiffToLp

/-! ## The `Fin.snoc` isometry -/

/-- **Eng.** The underlying map of the bridge: append the last coordinate,
`(v, c) ↦ (v₀, …, v_n, c)`. -/
def snocLpFun (x : WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ)) :
    EuclideanSpace ℂ (Fin (n + 2)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (fun i => x.fst i) x.snd)

/-- **Eng.** The inverse map: split off the last coordinate,
`w ↦ ((w₀, …, w_n), w_{n+1})`. -/
def unsnocLpFun (w : EuclideanSpace ℂ (Fin (n + 2))) :
    WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ) :=
  WithLp.toLp 2 ((WithLp.toLp 2 (fun i : Fin (n + 1) => w i.castSucc) :
    EuclideanSpace ℂ (Fin (n + 1))), w (Fin.last (n + 1)))

@[simp]
theorem snocLpFun_apply (x : WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ)) (k : Fin (n + 2)) :
    snocLpFun x k = Fin.snoc (α := fun _ => ℂ) (fun i => x.fst i) x.snd k := rfl

@[simp]
theorem unsnocLpFun_fst (w : EuclideanSpace ℂ (Fin (n + 2))) (i : Fin (n + 1)) :
    (unsnocLpFun w).fst i = w i.castSucc := rfl

@[simp]
theorem unsnocLpFun_snd (w : EuclideanSpace ℂ (Fin (n + 2))) :
    (unsnocLpFun w).snd = w (Fin.last (n + 1)) := rfl

/-- **Math.** The real inner product of `ℂ^{n+2}` splits along the last coordinate:
`⟪snoc v c, snoc v' c'⟫ = ⟪v, v'⟫ + ⟪c, c'⟫`.  This is the whole content of the bridge — the
`ℓ²`-product norm of `ℂ^{n+1} ⊕ ℂ` and the `ℓ²`-norm of `ℂ^{n+2}` are the same sum of squares of
the same `n+2` coordinates, the sum in the source being split off after the first `n+1`. -/
theorem inner_snocLpFun (x y : WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ)) :
    (inner ℝ (snocLpFun x) (snocLpFun y) : ℝ) = inner ℝ x y := by
  simp only [WithLp.prod_inner_apply, PiLp.inner_apply, snocLpFun_apply, WithLp.ofLp_fst,
    WithLp.ofLp_snd]
  rw [Fin.sum_univ_castSucc]
  simp

/-- **Math.** The `ℓ²`-product `ℂ^{n+1} ⊕₂ ℂ` is isometric to `ℂ^{n+2}`, via `Fin.snoc`:
`(v, c) ↦ (v₀, …, v_n, c)`.  It is a linear isometry because both norms are the `ℓ²` norm of the
same `n+2` complex coordinates (`inner_snocLpFun`).

This identifies the ambient space of the doubly warped `S^{2n+3}` (Example 1.4.14) with the ambient
space of `ℂP^{n+1}`. -/
def snocLpEquiv :
    WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (n + 2)) :=
  LinearEquiv.isometryOfInner
    { toFun := snocLpFun
      invFun := unsnocLpFun
      map_add' := by
        intro x y
        ext k
        refine Fin.lastCases ?_ ?_ k <;> simp
      map_smul' := by
        intro r x
        ext k
        refine Fin.lastCases ?_ ?_ k <;> simp
      left_inv := by
        intro x
        refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
        · ext i
          simp
        · simp
      right_inv := by
        intro w
        ext k
        refine Fin.lastCases ?_ ?_ k <;> simp }
    (fun x y => inner_snocLpFun x y)

/-- **Eng.** The coordinates of `snocLpEquiv x`: the first `n+1` are those of `x.fst`, the last one
is `x.snd`. -/
@[simp]
theorem snocLpEquiv_apply (x : WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ)) (k : Fin (n + 2)) :
    (snocLpEquiv x : EuclideanSpace ℂ (Fin (n + 2))) k
      = Fin.snoc (α := fun _ => ℂ) (fun i => x.fst i) x.snd k := rfl

/-- **Eng.** The coordinates of `snocLpEquiv (v, c)`: the first `n+1` are those of `v`, the last
one is `c`. -/
@[simp]
theorem snocLpEquiv_toLp_apply (v : EuclideanSpace ℂ (Fin (n + 1))) (c : ℂ) (k : Fin (n + 2)) :
    (snocLpEquiv (WithLp.toLp 2 (v, c)) : EuclideanSpace ℂ (Fin (n + 2))) k
      = Fin.snoc (α := fun _ => ℂ) (fun i => v i) c k := rfl

/-- **Math.** `snocLpEquiv` is `ℂ`-linear, not merely `ℝ`-linear: reindexing coordinates commutes
with multiplying them all by a complex scalar.  (This is what makes it intertwine the circle actions
`a · z = a z` on the two models, hence descend to the Hopf quotients.) -/
theorem snocLpEquiv_complex_smul (a : ℂ) (x : WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ)) :
    snocLpEquiv (a • x) = a • snocLpEquiv x := by
  ext k
  refine Fin.lastCases ?_ ?_ k <;> simp

/-! ## Example 1.4.14, source clause, in the coordinate model -/

/-- **Math.** The doubly warped parametrization of `S^{2n+3}`, read in the coordinate model
`ℂ^{n+2} = EuclideanSpace ℂ (Fin (n+2))`:

  `(t, z, w) ↦ (sin(t)·z₀, …, sin(t)·z_n, cos(t)·w)`,  `|z| = |w| = 1`.

It is `snocLpEquiv` applied to the `ℓ²`-product map of `sphereOddAsDoublyWarpedProduct`. -/
def genHopfAmbient (q : ℝ × sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 × sphere (0 : ℂ) 1) :
    EuclideanSpace ℂ (Fin (n + 2)) :=
  WithLp.toLp 2 (Fin.snoc (fun i => (Real.sin q.1 • (q.2.1 : EuclideanSpace ℂ (Fin (n + 1)))) i)
    (Real.cos q.1 * (q.2.2 : ℂ)))

/-- **Eng.** `genHopfAmbient` is the image under the `Fin.snoc` isometry of the doubly warped map
of `sphereOddAsDoublyWarpedProduct`.  The only thing to check is `cos(t) • w = cos(t) * w` in `ℂ`
(`Complex.real_smul`). -/
theorem genHopfAmbient_eq
    (q : ℝ × sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 × sphere (0 : ℂ) 1) :
    genHopfAmbient q
      = snocLpEquiv (WithLp.toLp 2 (Real.sin q.1 • (q.2.1 : EuclideanSpace ℂ (Fin (n + 1))),
          Real.cos q.1 • (q.2.2 : ℂ))) := by
  ext k
  simp only [genHopfAmbient, snocLpEquiv_toLp_apply, PiLp.toLp_apply, Complex.real_smul]

/-- **Math.** The generalized Hopf parametrization lands in the unit sphere `S^{2n+3} ⊆ ℂ^{n+2}`:
`|sin(t)·z|² + |cos(t)·w|² = sin²(t) + cos²(t) = 1`.  Transported from
`doublyWarpedSphereMap_mem_sphere` along the isometry. -/
theorem norm_genHopfAmbient
    (q : ℝ × sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 × sphere (0 : ℂ) 1) :
    ‖genHopfAmbient q‖ = 1 := by
  rw [genHopfAmbient_eq, snocLpEquiv.norm_map]
  exact mem_sphere_zero_iff_norm.mp (doublyWarpedSphereMap_mem_sphere q.1 q.2.1 q.2.2)

/-- **Math.** Petersen Example 1.4.14, source clause, in the coordinate model: the doubly warped
product

  `I × S^{2n+1} × S¹`,  `dt² + sin²(t) ds²_{2n+1} + cos²(t) dθ²`,  `t ∈ [0, π/2]`,

*is* the round sphere `S^{2n+3} ⊆ ℂ^{n+2} = EuclideanSpace ℂ (Fin (n+2))` — the very ambient space
in which `ℂP^{n+1}` is built.  This is `sphereOddAsDoublyWarpedProduct` transported along the
`Fin.snoc` isometry: the parametrization only gets its coordinates relabelled, and a linear isometry
changes neither the differential (up to that relabelling) nor the inner products it is fed to. -/
theorem pullbackForm_genHopfAmbient
    (p : ℝ × sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 × sphere (0 : ℂ) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1)))
        (innerProductSpaceMetric (EuclideanSpace ℂ (Fin (n + 2)))) genHopfAmbient p u v
      = doublyWarpedProductForm
          (sphereMetricUnit (n := 2 * n + 1) (EuclideanSpace ℂ (Fin (n + 1))))
          (sphereMetricUnit (n := 1) ℂ) Real.sin Real.cos p u v := by
  have hfun : (genHopfAmbient :
      ℝ × sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 × sphere (0 : ℂ) 1 →
        EuclideanSpace ℂ (Fin (n + 2)))
      = fun q => snocLpEquiv (WithLp.toLp 2
          (Real.sin q.1 • (q.2.1 : EuclideanSpace ℂ (Fin (n + 1))), Real.cos q.1 • (q.2.2 : ℂ))) :=
    funext genHopfAmbient_eq
  rw [hfun]
  exact (pullbackForm_linearIsometryEquiv snocLpEquiv
      (mdifferentiableAt_toLp_prodMk (mdifferentiableAt_sinSmul p)
        (mdifferentiableAt_cosSmul p)) u v).trans (sphereOddAsDoublyWarpedProduct p u v)

end PetersenLib
