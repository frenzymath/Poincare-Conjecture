import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.HomogeneousMetrics
import PetersenLib.Ch01.VolumeForm
import PetersenLib.Ch01.WarpedProducts
import PetersenLib.Ch01.SmoothnessCriterion
import PetersenLib.Ch01.IsometryGroups
import PetersenLib.Ch01.PolarCoordinates
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Petersen Ch. 1, §1.6 — Exercises 1.6.1–1.6.10

Formalizations of the first ten exercises of Petersen §1.6, wired against the
Ch. 1 infrastructure (`productMetric`, `pullbackMetric`, `IsRiemannianSubmersion`,
`localVolumeForm`/`volumeForm`, `warpedProductMetric`,
`rotationallySymmetricSmoothnessCriterion`, `IsometryGroup`).

* `exercise1_6_1` — Cartesian product metrics: `ℝⁿ⁺¹ = ℝⁿ × ℝ` isometrically
  (part 1, the recursion step of `(ℝⁿ, g_{ℝⁿ}) = (ℝ, dt²) × ⋯ × (ℝ, dt²)`),
  the flat square torus as a product of circles of circumference `1`
  (part 2), and the Riemannian embedding `T² → ℝ⁴` (part 3).
* `exercise1_6_2` — existence and uniqueness of the quotient metric of an
  isometric group action (uniqueness proved outright:
  `isRiemannianSubmersion_metric_unique`).
* `exercise1_6_3` — `vol M = k · vol N` for a `k`-fold Riemannian covering.
* `exercise1_6_4` — the volume form of `dr² + ρ²(r) g_N` is `ρⁿ⁻¹ dr ∧ vol_N`.
* `exercise1_6_5` — the dual coframe of an orthonormal frame is
  `σⁱ(X) = g(Eᵢ, X)` and `vol = ±σ¹ ∧ ⋯ ∧ σⁿ`.
* `exercise1_6_6` — in local coordinates `vol = ±√(det[gᵢⱼ]) dx¹ ∧ ⋯ ∧ dxⁿ`.
* `exercise1_6_7` — the "paper models" `dt² + a²t²dθ²` (plane for `a = 1`,
  cones for `a < 1`) unroll isometrically onto the Euclidean plane.
* `exercise1_6_8` — smoothness at `r = 0` of `dr² + ρ²(r) g_{Sⁿ⁻¹(R)}` forces
  `ρ̇(0) = 1/R` and `ρ^{(2k)}(0) = 0`.
* `exercise1_6_9` — `Iso(ℝⁿ)` as the matrix group `[[O, v], [0, 1]]` acting on
  the hyperplane `xⁿ⁺¹ = R`.
* `exercise1_6_10` — Sylvester bases for a nondegenerate symmetric bilinear
  form of index `p` (`bilinFormNegIndex`), the expansion of a vector in such
  a basis, and the trace formula `tr L = Σ g(L(eᵢ), eᵢ)/g(eᵢ, eᵢ)`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.6, Exercises
1.6.1–1.6.10.
-/

open Bundle Module MeasureTheory
open scoped ContDiff Manifold Topology Bundle Real RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## Exercise 1.6.1 — Cartesian product metrics

Petersen: on `M × N` one has the Cartesian product metric `g = g_M + g_N`.
(1) `(ℝⁿ, g_{ℝⁿ}) = (ℝ, dt²) × ⋯ × (ℝ, dt²)`; (2) the flat square torus is
`T² = ℝ²/ℤ² = (S¹, (1/2π)² dθ²) × (S¹, (1/2π)² dθ²)`; (3)
`F(θ₁, θ₂) = (1/2π)(cos θ₁, sin θ₁, cos θ₂, sin θ₂)` is a Riemannian
embedding `T² → ℝ⁴`. -/

section Exercise1

/-- **Eng.** The continuous linear projection `ℝⁿ⁺¹ → ℝⁿ` onto the first `n`
coordinates, `(euclideanCastSuccCLM n x) i = x i.castSucc`, used to split off
the last factor of Euclidean space in Exercise 1.6.1 (1). -/
def euclideanCastSuccCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm :
      (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
    (ContinuousLinearMap.pi fun i : Fin n => EuclideanSpace.proj (Fin.castSucc i))

@[simp]
theorem euclideanCastSuccCLM_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin n) : euclideanCastSuccCLM n x i = x i.castSucc :=
  rfl

/-- **Eng.** The continuous linear extension-by-zero `ℝⁿ → ℝⁿ⁺¹`
(`x` on the first `n` coordinates, `0` at the last), inverse ingredient of
the splitting of Exercise 1.6.1 (1). -/
def euclideanSnocZeroCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm :
      (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).comp
    (ContinuousLinearMap.pi fun j : Fin (n + 1) =>
      (Fin.lastCases 0 (fun i => EuclideanSpace.proj i) j :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))

@[simp]
theorem euclideanSnocZeroCLM_apply_castSucc (n : ℕ) (z : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : euclideanSnocZeroCLM n z i.castSucc = z i := by
  show (Fin.lastCases 0 (fun i => EuclideanSpace.proj i) (Fin.castSucc i) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) z = z i
  rw [Fin.lastCases_castSucc]
  rfl

@[simp]
theorem euclideanSnocZeroCLM_apply_last (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    euclideanSnocZeroCLM n z (Fin.last n) = 0 := by
  show (Fin.lastCases 0 (fun i => EuclideanSpace.proj i) (Fin.last n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) z = 0
  rw [Fin.lastCases_last]
  rfl

/-- **Eng.** The continuous linear inclusion `ℝ → ℝⁿ⁺¹` at the last
coordinate, inverse ingredient of the splitting of Exercise 1.6.1 (1). -/
def euclideanSingleLastCLM (n : ℕ) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm :
      (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).comp
    (ContinuousLinearMap.pi fun j : Fin (n + 1) =>
      (if j = Fin.last n then ContinuousLinearMap.id ℝ ℝ else 0))

@[simp]
theorem euclideanSingleLastCLM_apply (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    euclideanSingleLastCLM n t j = if j = Fin.last n then t else 0 := by
  show (if j = Fin.last n then ContinuousLinearMap.id ℝ ℝ else 0) t = _
  split <;> rfl

/-- **Math.** Exercise 1.6.1 (1), underlying diffeomorphism: splitting off
the last coordinate is a diffeomorphism from `ℝⁿ⁺¹` onto the product
manifold `ℝⁿ × ℝ`. -/
def euclideanSplitLastDiffeomorph (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)⟯
      (EuclideanSpace ℝ (Fin n) × ℝ) where
  toFun x := (euclideanCastSuccCLM n x, x (Fin.last n))
  invFun y := euclideanSnocZeroCLM n y.1 + euclideanSingleLastCLM n y.2
  left_inv x := by
    ext j
    rw [PiLp.add_apply]
    induction j using Fin.lastCases with
    | last => simp
    | cast i => simp
  right_inv y := by
    refine Prod.ext ?_ ?_
    · ext i
      show (euclideanSnocZeroCLM n y.1 + euclideanSingleLastCLM n y.2) i.castSucc = y.1 i
      rw [PiLp.add_apply]
      simp [(Fin.castSucc_lt_last i).ne]
    · show (euclideanSnocZeroCLM n y.1 + euclideanSingleLastCLM n y.2) (Fin.last n) = y.2
      rw [PiLp.add_apply]
      simp
  contMDiff_toFun :=
    (euclideanCastSuccCLM n).contMDiff.prodMk
      ((EuclideanSpace.proj (Fin.last n) :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)).contMDiff
  contMDiff_invFun :=
    ((euclideanSnocZeroCLM n).contMDiff.comp contMDiff_fst).add
      ((euclideanSingleLastCLM n).contMDiff.comp contMDiff_snd)

/-- **Math.** Petersen Exercise 1.6.1 (1): the recursion step of
`(ℝⁿ, g_{ℝⁿ}) = (ℝ, dt²) × ⋯ × (ℝ, dt²)`. Splitting off the last coordinate,
`x ↦ (x|_{first n}, xₙ₊₁)`, is a Riemannian isometry
`(ℝⁿ⁺¹, g_{ℝⁿ⁺¹}) → (ℝⁿ, g_{ℝⁿ}) × (ℝ, dt²)` (Cartesian product metric on
the right); iterating identifies Euclidean `n`-space with the `n`-fold
Riemannian product of `(ℝ, dt²)`. The proof is
`⟨u, v⟩_{ℝⁿ⁺¹} = Σᵢ uᵢvᵢ = Σ_{i<n} uᵢvᵢ + uₙ₊₁vₙ₊₁`, the differential of the
linear splitting being the splitting itself. -/
theorem exercise1_6_1_part1 (n : ℕ) :
    IsRiemannianIsometry (euclideanMetric (n + 1))
      (productMetric (euclideanMetric n) (innerProductSpaceMetric ℝ))
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
        (euclideanCastSuccCLM n x, x (Fin.last n))) := by
  refine ⟨⟨euclideanSplitLastDiffeomorph n, rfl⟩, fun p u v => ?_⟩
  -- the differential of the linear splitting is itself
  have hD : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
        (euclideanCastSuccCLM n x, x (Fin.last n))) p
      = (euclideanCastSuccCLM n).prod
          (EuclideanSpace.proj (Fin.last n) :
            EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) := by
    have hf : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⇑(euclideanCastSuccCLM n)) p :=
      (((euclideanCastSuccCLM n).contMDiff :
        ContMDiff _ _ ∞ _).mdifferentiable (by simp)) p
    have hg : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ)
        (⇑(EuclideanSpace.proj (Fin.last n) :
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) p :=
      ((((EuclideanSpace.proj (Fin.last n) :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)).contMDiff :
        ContMDiff _ _ ∞ _).mdifferentiable (by simp)) p
    have hfun : (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
        (euclideanCastSuccCLM n x, x (Fin.last n)))
        = fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          (euclideanCastSuccCLM n x,
            (EuclideanSpace.proj (Fin.last n) :
              EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) x) := rfl
    rw [hfun, mfderiv_prodMk hf hg]
    congr 1
    · rw [mfderiv_eq_fderiv]
      exact (euclideanCastSuccCLM n).fderiv
    · rw [mfderiv_eq_fderiv]
      exact (EuclideanSpace.proj (Fin.last n) :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).fderiv
  rw [hD, productMetric_apply]
  show (inner ℝ (u : EuclideanSpace ℝ (Fin (n + 1))) (v : EuclideanSpace ℝ (Fin (n + 1))) : ℝ)
      = (inner ℝ (euclideanCastSuccCLM n u) (euclideanCastSuccCLM n v) : ℝ)
        + (inner ℝ (EuclideanSpace.proj (Fin.last n) u)
            (EuclideanSpace.proj (Fin.last n) v) : ℝ)
  have hlast : (inner ℝ (EuclideanSpace.proj (Fin.last n) u)
      (EuclideanSpace.proj (Fin.last n) v) : ℝ)
      = WithLp.ofLp (v : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)
        * WithLp.ofLp (u : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) := by
    exact (RCLike.inner_apply _ _).trans (by rw [conj_trivial]; rfl)
  rw [hlast,
    show (inner ℝ (u : EuclideanSpace ℝ (Fin (n + 1)))
        (v : EuclideanSpace ℝ (Fin (n + 1))) : ℝ)
      = ∑ i, WithLp.ofLp (v : EuclideanSpace ℝ (Fin (n + 1))) i
          * WithLp.ofLp (u : EuclideanSpace ℝ (Fin (n + 1))) i from rfl,
    show (inner ℝ (euclideanCastSuccCLM n u) (euclideanCastSuccCLM n v) : ℝ)
      = ∑ i : Fin n,
          WithLp.ofLp (v : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc
            * WithLp.ofLp (u : EuclideanSpace ℝ (Fin (n + 1))) i.castSucc from rfl]
  exact Fin.sum_univ_castSucc
    (f := fun i => WithLp.ofLp (v : EuclideanSpace ℝ (Fin (n + 1))) i
      * WithLp.ofLp (u : EuclideanSpace ℝ (Fin (n + 1))) i)

/-! ### Part (3): the torus embeds Riemannianly in `ℝ⁴` -/

/-- **Math.** Petersen Exercise 1.6.1 (3): the embedding of the torus
`T² = S¹ × S¹` into `ℝ⁴ = ℂ ×₂ ℂ` (the `L²`-product, so that the ambient
norm is the Euclidean one), `(z, w) ↦ (z, w)`. Petersen's map
`F(θ₁, θ₂) = (1/2π)(cos θ₁, sin θ₁, cos θ₂, sin θ₂)` is this map for the
circles of circumference `1`; the formalized `flatTorus` is the product of
*unit* circles (see its docstring), for which the embedding is the plain
product of the two inclusions `S¹ ↪ ℂ`. -/
def torusEmbedding (p : Circle × Circle) : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 ((p.1 : ℂ), (p.2 : ℂ))

/-- The identification `ℂ × ℂ ≃ ℂ ×₂ ℂ` as a continuous linear map. -/
private def toL2CLM : (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm : (ℂ × ℂ) ≃L[ℝ] WithLp 2 (ℂ × ℂ))

/-- **Eng.** The torus embedding is smooth: it is the `L²`-repackaging of the
pair of smooth circle inclusions. -/
theorem contMDiff_torusEmbedding :
    ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) ∞ torusEmbedding := by
  have h : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun p : Circle × Circle => ((p.1 : ℂ), (p.2 : ℂ))) :=
    (contMDiff_circle_coe.comp contMDiff_fst).prodMk_space
      (contMDiff_circle_coe.comp contMDiff_snd)
  exact toL2CLM.contMDiff.comp h

/-- **Eng.** Pairing two maps into model vector spaces differentiates to the
product of the differentials — the vector-space-target analogue of
`HasMFDerivAt.prodMk` (whose target model would be `𝓘(ℝ, E').prod 𝓘(ℝ, F')`
rather than `𝓘(ℝ, E' × F')`). Structural, as for `prodMk`. -/
private theorem hasMFDerivAt_prodMk_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {f : M → E'} {g : M → F'} {x : M}
    {df : TangentSpace I x →L[ℝ] E'} {dg : TangentSpace I x →L[ℝ] F'}
    (hf : HasMFDerivAt I 𝓘(ℝ, E') f x df) (hg : HasMFDerivAt I 𝓘(ℝ, F') g x dg) :
    HasMFDerivAt I 𝓘(ℝ, E' × F') (fun y => (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- **Math.** The torus embedding has, at `p = (z, w)`, the manifold
derivative `(u₁, u₂) ↦ (Dι_z(u₁), Dι_w(u₂))` (as a map into `ℂ ×₂ ℂ`):
the pair of the differentials of the circle inclusions. -/
theorem hasMFDerivAt_torusEmbedding (p : Circle × Circle) :
    HasMFDerivAt ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) torusEmbedding p
      (toL2CLM.comp
        (((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.1).comp
            (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1))
              (EuclideanSpace ℝ (Fin 1)))).prod
          ((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.2).comp
            (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1))
              (EuclideanSpace ℝ (Fin 1)))))) := by
  have hι1 : HasMFDerivAt ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℂ)
      (fun q : Circle × Circle => (q.1 : ℂ)) p
      ((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 1)))) :=
    HasMFDerivAt.comp p
      (((contMDiff_circle_coe.mdifferentiable (by simp)) p.1).hasMFDerivAt)
      (hasMFDerivAt_fst p)
  have hι2 : HasMFDerivAt ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℂ)
      (fun q : Circle × Circle => (q.2 : ℂ)) p
      ((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.2).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 1)))) :=
    HasMFDerivAt.comp p
      (((contMDiff_circle_coe.mdifferentiable (by simp)) p.2).hasMFDerivAt)
      (hasMFDerivAt_snd p)
  exact HasMFDerivAt.comp p toL2CLM.hasMFDerivAt
    (hasMFDerivAt_prodMk_space hι1 hι2)

/-- **Math.** The differential of the torus embedding is the pair of the
differentials of the circle inclusions:
`D(ι × ι)(u₁, u₂) = (Dι(u₁), Dι(u₂))` under `T(S¹ × S¹) = TS¹ × TS¹`. -/
theorem mfderiv_torusEmbedding_apply (p : Circle × Circle)
    (u : TangentSpace ((𝓡 1).prod (𝓡 1)) p) :
    mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) torusEmbedding p u =
      WithLp.toLp 2
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.1 u.1,
          mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.2 u.2) := by
  rw [(hasMFDerivAt_torusEmbedding p).mfderiv]
  rfl

/-- **Math.** Petersen Exercise 1.6.1 (3): the torus embedding is a smooth
immersion — its differential `(Dι, Dι)` is injective componentwise. -/
theorem torusEmbedding_isSmoothImmersion :
    IsSmoothImmersion (I := (𝓡 1).prod (𝓡 1)) (I' := 𝓘(ℝ, WithLp 2 (ℂ × ℂ)))
      torusEmbedding := by
  refine ⟨contMDiff_torusEmbedding, fun p => fun u v huv => ?_⟩
  rw [mfderiv_torusEmbedding_apply, mfderiv_torusEmbedding_apply] at huv
  have h := WithLp.toLp_injective (V := ℂ × ℂ) 2 huv
  exact Prod.ext (mfderiv_circle_coe_injective p.1 (congrArg Prod.fst h))
    (mfderiv_circle_coe_injective p.2 (congrArg Prod.snd h))

/-- **Math.** Petersen Exercise 1.6.1 (3): the torus embedding preserves the
metric — the flat product metric of `T² = S¹ × S¹` is the pullback of the
Euclidean metric of `ℝ⁴ = ℂ ×₂ ℂ`, because the ambient inner product of the
`L²`-product splits as the sum of the two `ℂ`-inner products, which are the
two circle (pullback) metrics. -/
theorem torusEmbedding_preservesMetric :
    PreservesMetric flatTorus (innerProductSpaceMetric (WithLp 2 (ℂ × ℂ)))
      torusEmbedding := by
  intro p u v
  rw [show flatTorus = productMetric circleMetric circleMetric from rfl,
    productMetric_apply]
  rw [show circleMetric = pullbackMetric (innerProductSpaceMetric ℂ)
      (fun z : Circle => (z : ℂ)) isSmoothImmersion_circle_coe from rfl,
    pullbackMetric_apply, pullbackMetric_apply,
    innerProductSpaceMetric_apply, innerProductSpaceMetric_apply,
    innerProductSpaceMetric_apply,
    mfderiv_torusEmbedding_apply, mfderiv_torusEmbedding_apply]
  rfl

/-- **Eng.** The torus embedding is injective (so, `T²` being compact, a
topological embedding): the components recover the two circle points. -/
theorem torusEmbedding_injective : Function.Injective torusEmbedding := by
  intro p q hpq
  have h : ((p.1 : ℂ), (p.2 : ℂ)) = ((q.1 : ℂ), (q.2 : ℂ)) :=
    WithLp.toLp_injective (V := ℂ × ℂ) 2 hpq
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
    (Subtype.ext (congrArg Prod.snd h))

/-- **Math.** Petersen Exercise 1.6.1 — Cartesian product metrics.
(1) `(ℝⁿ⁺¹, g_{ℝⁿ⁺¹}) = (ℝⁿ, g_{ℝⁿ}) × (ℝ, dt²)` via splitting off the last
coordinate (`exercise1_6_1_part1`; iterating gives the `n`-fold product
`(ℝ, dt²) × ⋯ × (ℝ, dt²)`).
(2) The flat torus is the Riemannian product of two round circles — in this
development `flatTorus` is *defined* as the product metric on `S¹ × S¹`
(Petersen instead defines it as the quotient `ℝ²/ℤ²`, unavailable in
Mathlib; see the docstring of `flatTorus`), so this clause records the
product structure definitionally.
(3) `(z, w) ↦ (z, w)` is an injective Riemannian immersion — a Riemannian
embedding, as `T²` is compact — of the flat torus into Euclidean
`ℝ⁴ = ℂ ×₂ ℂ` (Petersen's
`F(θ₁, θ₂) = (1/2π)(cosθ₁, sinθ₁, cosθ₂, sinθ₂)`, for unit circles). -/
theorem exercise1_6_1 :
    (∀ n : ℕ, IsRiemannianIsometry (euclideanMetric (n + 1))
        (productMetric (euclideanMetric n) (innerProductSpaceMetric ℝ))
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          (euclideanCastSuccCLM n x, x (Fin.last n)))) ∧
      flatTorus = productMetric circleMetric circleMetric ∧
      IsRiemannianImmersion flatTorus
        (innerProductSpaceMetric (WithLp 2 (ℂ × ℂ))) torusEmbedding ∧
      Function.Injective torusEmbedding :=
  ⟨exercise1_6_1_part1, rfl,
    ⟨torusEmbedding_isSmoothImmersion, torusEmbedding_preservesMetric⟩,
    torusEmbedding_injective⟩

end Exercise1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## Exercise 1.6.2 — the quotient metric of an isometric group action

Petersen: if a group `G` acts by isometries on `(M, g)` so that `M/G` is a
smooth manifold and the quotient map a submersion, there is a *unique*
Riemannian metric on `M/G` making the quotient map a Riemannian submersion. -/

section Exercise2

/-- The metric of `(M, g)` at `x`, as an (algebraic) bilinear form on
`T_xM`, for use with Mathlib's `LinearMap.BilinForm` orthogonality API. -/
private def metricBilinForm (g : RiemannianMetric I M) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  LinearMap.mk₂ ℝ (fun u v => g.metricInner x u v)
    (g.metricInner_add_left x) (g.metricInner_smul_left x)
    (g.metricInner_add_right x) (g.metricInner_smul_right x)

@[simp]
private theorem metricBilinForm_apply (g : RiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    metricBilinForm g x u v = g.metricInner x u v := rfl

omit [IsManifold I' ∞ M'] in
/-- **Math.** Existence of horizontal lifts: if `Dq_p` is surjective, every
`u' ∈ T_{q(p)}M'` has a preimage `u ∈ T_pM` that is `g_M`-perpendicular to
`ker Dq_p` — decompose any preimage along
`T_pM = ker Dq_p ⊕ (ker Dq_p)^⊥`, which is a direct sum because the
positive-definite `g_M` restricts nondegenerately to the kernel. -/
private theorem exists_horizontal_lift [FiniteDimensional ℝ E]
    (gM : RiemannianMetric I M) {q : M → M'} (p : M)
    (hsub : Function.Surjective (mfderiv I I' q p))
    (u' : TangentSpace I' (q p)) :
    ∃ u : TangentSpace I p, mfderiv I I' q p u = u' ∧
      ∀ w : TangentSpace I p, mfderiv I I' q p w = 0 →
        gM.metricInner p u w = 0 := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  set B := metricBilinForm gM p with hB
  set K : Submodule ℝ (TangentSpace I p) :=
    LinearMap.ker (mfderiv I I' q p : TangentSpace I p →ₗ[ℝ] TangentSpace I' (q p))
    with hK
  have hrefl : B.IsRefl := fun u v huv => by
    rw [metricBilinForm_apply, gM.metricInner_comm]
    exact huv
  have hres : (B.restrict K).Nondegenerate := by
    constructor <;>
      · intro x hall
        by_contra hne
        have hx0 : (x : TangentSpace I p) ≠ 0 := fun h0 => hne (Subtype.ext h0)
        have hxx := hall x
        rw [LinearMap.BilinForm.restrict_apply] at hxx
        exact (gM.metricInner_self_pos p x hx0).ne' hxx
  have hcompl : IsCompl K (B.orthogonal K) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hres
  obtain ⟨w, hw⟩ := hsub u'
  have hmem : w ∈ K ⊔ B.orthogonal K := by
    rw [hcompl.sup_eq_top]; trivial
  obtain ⟨k, hk, u, hu, hku⟩ := Submodule.mem_sup.mp hmem
  refine ⟨u, ?_, fun v hv => ?_⟩
  · have hDk : mfderiv I I' q p k = 0 := LinearMap.mem_ker.mp hk
    have : mfderiv I I' q p (k + u) = u' := by rw [hku]; exact hw
    rwa [map_add, hDk, zero_add] at this
  · have hvK : v ∈ K := LinearMap.mem_ker.mpr hv
    have hBvu : B v u = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) v hvK
    rw [gM.metricInner_comm]
    exact hBvu

/-- **Math.** Petersen Exercise 1.6.2, uniqueness: two Riemannian metrics on
`M'` making the same surjective map `q : (M, g_M) → M'` a Riemannian
submersion agree. On each tangent plane the value is forced: lift the two
vectors horizontally (`exists_horizontal_lift`) and both metrics equal
`g_M` on the lifts. -/
theorem isRiemannianSubmersion_metric_unique [FiniteDimensional ℝ E]
    {gM : RiemannianMetric I M} {gN gN' : RiemannianMetric I' M'} {q : M → M'}
    (hsurj : Function.Surjective q)
    (h : IsRiemannianSubmersion gM gN q)
    (h' : IsRiemannianSubmersion gM gN' q) :
    gN = gN' := by
  refine RiemannianMetric.ext_inner fun y => ?_
  obtain ⟨p, rfl⟩ := hsurj y
  refine ContinuousLinearMap.ext fun u' => ContinuousLinearMap.ext fun v' => ?_
  obtain ⟨u, hu, huh⟩ := exists_horizontal_lift gM p (h.2.1 p) u'
  obtain ⟨v, hv, hvh⟩ := exists_horizontal_lift gM p (h.2.1 p) v'
  have e1 := h.2.2 p u v huh hvh
  have e2 := h'.2.2 p u v huh hvh
  rw [hu, hv] at e1 e2
  exact e1.symm.trans e2

/-- **Math.** Petersen Exercise 1.6.2: if a group `G` acts isometrically on
`(M, g_M)` so that the quotient `M/G` is a smooth manifold (represented by a
manifold `M'`, with `q : M → M'` the quotient map: smooth, surjective, with
surjective differentials, and with fibers exactly the `G`-orbits), then
there is a **unique** Riemannian metric on `M/G` making `q` a Riemannian
submersion.

This is exactly `PetersenLib.homogeneousQuotientMetric` (Petersen §1.3.2), of
which the exercise is the abstract-group form: the metric downstairs is `g_M`
transported through the horizontal lift of `Dq`, well defined across a fibre
because `G` acts by isometries permuting the fibres, and smooth because the
horizontal lift depends smoothly on `(g_p, Dq_p)`. -/
theorem exercise1_6_2 [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [I.Boundaryless] [I'.Boundaryless]
    {G : Type*} [Group G] [MulAction G M]
    (gM : RiemannianMetric I M)
    (hiso : ∀ γ : G, IsRiemannianIsometry gM gM (fun p : M => γ • p))
    (q : M → M') (hq : ContMDiff I I' ∞ q)
    (hsurj : Function.Surjective q)
    (hsub : ∀ p : M, Function.Surjective (mfderiv I I' q p))
    (hfib : ∀ p p' : M, q p = q p' ↔ ∃ γ : G, γ • p = p') :
    ∃! gN : RiemannianMetric I' M', IsRiemannianSubmersion gM gN q :=
  homogeneousQuotientMetric gM q hiso hq hsurj hsub hfib

end Exercise2

/-! ## Exercise 1.6.3 — volume of a finite Riemannian covering

Petersen: for a `k`-fold Riemannian covering `F : M → N`,
`vol M = k · vol N`. -/

section Exercise3

/-- The sheet decomposition of one evenly covered piece: if `A` is a
measurable subset of the base set of a trivialization of `F` with fiber
`F⁻¹(y)`, and `F` is measure preserving on measurable sets on which it is
injective, then `μM(F⁻¹(A)) = |F⁻¹(y)| · μN(A)`. The preimage decomposes
into disjoint sheets indexed by the fiber — each open in `F⁻¹(baseSet)`,
each mapped bijectively onto `A`. -/
private theorem measure_preimage_eq_card_mul_of_trivialization
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y]
    {F : X → Y}
    (μM : Measure X) (μN : Measure Y)
    (hpres : ∀ s : Set X, MeasurableSet s → Set.InjOn F s → μM s = μN (F '' s))
    {y : Y} [Finite (F ⁻¹' {y})] [DiscreteTopology (F ⁻¹' {y})]
    (T : Trivialization (F ⁻¹' {y}) F)
    {A : Set Y} (hFA : MeasurableSet (F ⁻¹' A)) (hAU : A ⊆ T.baseSet) :
    μM (F ⁻¹' A) = Nat.card (F ⁻¹' {y}) * μN A := by
  set S : (F ⁻¹' {y}) → Set X :=
    fun j => (T.source ∩ ⇑T ⁻¹' (Set.univ ×ˢ {j})) ∩ F ⁻¹' A with hS_def
  have hcoe : ⇑T.toOpenPartialHomeomorph = ⇑T := T.coe_coe
  have hSopen : ∀ j, IsOpen (T.source ∩ ⇑T ⁻¹' (Set.univ ×ˢ {j})) := by
    intro j
    have h := T.toOpenPartialHomeomorph.isOpen_inter_preimage
      (isOpen_univ.prod (isOpen_discrete ({j} : Set (F ⁻¹' {y}))))
    rwa [hcoe] at h
  have hSmeas : ∀ j, MeasurableSet (S j) := fun j =>
    (hSopen j).measurableSet.inter hFA
  -- `F` is injective on each sheet
  have hSinj : ∀ j, Set.InjOn F (S j) := by
    intro j x hx x' hx' hFxx'
    apply T.toOpenPartialHomeomorph.injOn hx.1.1 hx'.1.1
    show T.toOpenPartialHomeomorph x = T.toOpenPartialHomeomorph x'
    rw [hcoe]
    have h1 : (T x).1 = F x := T.coe_fst hx.1.1
    have h1' : (T x').1 = F x' := T.coe_fst hx'.1.1
    exact Prod.ext (by rw [h1, h1', hFxx'])
      (hx.1.2.2.trans hx'.1.2.2.symm)
  -- each sheet maps onto `A`
  have hSimg : ∀ j, F '' S j = A := by
    intro j
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro b hb
      have hbt : ((b, j) : Y × (F ⁻¹' {y})) ∈ T.target := by
        rw [T.target_eq]
        exact ⟨hAU hb, Set.mem_univ _⟩
      refine ⟨T.toOpenPartialHomeomorph.symm (b, j), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact T.toOpenPartialHomeomorph.map_target hbt
      · rw [Set.mem_preimage, ← hcoe, T.toOpenPartialHomeomorph.right_inv hbt]
        exact ⟨Set.mem_univ _, rfl⟩
      · rw [Set.mem_preimage, T.proj_symm_apply hbt]
        exact hb
      · exact T.proj_symm_apply hbt
  -- the sheets are pairwise disjoint and cover `F⁻¹(A)`
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro j j' hjj'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    exact hjj' (hx.1.2.2.symm.trans hx'.1.2.2)
  have hcover : ⋃ j, S j = F ⁻¹' A := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun j => Set.inter_subset_right
    · intro x hx
      have hxU : x ∈ T.source := by
        rw [T.mem_source]
        exact hAU hx
      exact Set.mem_iUnion.mpr ⟨(T x).2, ⟨hxU, ⟨Set.mem_univ _, rfl⟩⟩, hx⟩
  -- sum the `|F⁻¹(y)|` equal sheet measures
  have hsheet : ∀ j, μM (S j) = μN A := fun j => by
    rw [hpres (S j) (hSmeas j) (hSinj j), hSimg j]
  haveI : Fintype (F ⁻¹' {y}) := Fintype.ofFinite _
  rw [← hcover, measure_iUnion hdisj hSmeas, tsum_congr hsheet,
    tsum_eq_sum (s := Finset.univ) (fun j hj => absurd (Finset.mem_univ j) hj),
    Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Math.** Petersen Exercise 1.6.3: for a Riemannian `k`-fold covering map
`F : (M, g_M) → (N, g_N)` (a smooth covering map which is a local isometry,
`g_M = F^*g_N` — cf. `coveringInducedMetric`), the total volumes satisfy
`vol M = k · vol N`.

**Implementation.** Mathlib has no Riemannian volume measure yet (see the
design note on `integrateOnRiemannianManifold`), so the Riemannian measures
of `g_M` and `g_N` are represented by measure data `μM, μN`, and the
local-isometry property of `F` enters through the hypothesis `hpres`: `F`
is measure preserving on every measurable set on which it is injective —
which is exactly how the Riemannian measures of a covering by local
isometries behave, sheet by sheet. The measures are taken Borel
(`OpensMeasurableSpace M`, `BorelSpace M'`), the base is second countable
(both standing conventions for Petersen's manifolds and Riemannian
measures), and the covering is `k`-fold with `k ≥ 1` — for `k = 0` the
hypothesis `Nat.card (F⁻¹(y)) = 0` would also admit *infinite* fibers, for
which the statement fails (e.g. `ℝ → S¹`).

**Proof.** Decompose `N` into countably many disjoint measurable pieces,
each inside an evenly covered open set (second countability organizes the
cover); over each piece the preimage under `F` is a disjoint union of `k`
sheets, each mapped injectively and (by `hpres`) measure-preservingly onto
the piece (`measure_preimage_eq_card_mul_of_trivialization`); sum over the
pieces. -/
theorem exercise1_6_3 [MeasurableSpace M] [OpensMeasurableSpace M]
    [MeasurableSpace M'] [BorelSpace M'] [SecondCountableTopology M']
    (gM : RiemannianMetric I M) (gN : RiemannianMetric I' M') (F : M → M')
    (hcov : IsCoveringMap F) (hiso : PreservesMetric gM gN F)
    (k : ℕ) (hk0 : 0 < k) (hk : ∀ y : M', Nat.card (F ⁻¹' {y}) = k)
    (μM : Measure M) (μN : Measure M')
    (hpres : ∀ s : Set M, MeasurableSet s → Set.InjOn F s →
      μM s = μN (F '' s)) :
    μM Set.univ = k * μN Set.univ := by
  have hfib : ∀ y : M', Nonempty (F ⁻¹' {y}) ∧ Finite (F ⁻¹' {y}) := fun y =>
    Nat.card_pos_iff.mp (by rw [hk y]; exact hk0)
  rcases isEmpty_or_nonempty M' with hM' | hM'
  · -- empty base: the total space is empty too and both sides vanish
    haveI : IsEmpty M := ⟨fun x => hM'.false (F x)⟩
    rw [Set.univ_eq_empty_iff.mpr ‹IsEmpty M›, Set.univ_eq_empty_iff.mpr hM',
      measure_empty, measure_empty, mul_zero]
  -- trivializations at every point of the base
  let T : ∀ y : M', Trivialization (F ⁻¹' {y}) F := fun y =>
    haveI := (hfib y).1
    (hcov y).toTrivialization
  have hyT : ∀ y : M', y ∈ (T y).baseSet := fun y =>
    haveI := (hfib y).1
    (hcov y).mem_toTrivialization_baseSet
  -- a countable subcover of the base by trivialization base sets
  obtain ⟨tset, htc, htU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : M' => (T y).baseSet) (fun y => (T y).open_baseSet)
  have htuniv : ⋃ y ∈ tset, (T y).baseSet = Set.univ := by
    rw [htU]
    exact Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ⟨y, hyT y⟩
  have htne : tset.Nonempty := by
    rcases Set.eq_empty_or_nonempty tset with rfl | h
    · exact absurd (htuniv ▸ Set.mem_univ hM'.some) (by simp)
    · exact h
  obtain ⟨g, hg⟩ := Set.Countable.exists_eq_range htc htne
  -- disjointify into countably many measurable pieces
  set B : ℕ → Set M' := disjointed (fun i => (T (g i)).baseSet) with hB_def
  have hBmeas : ∀ i, MeasurableSet (B i) :=
    MeasurableSet.disjointed fun i => (T (g i)).open_baseSet.measurableSet
  have hBdisj : Pairwise (Function.onFun Disjoint B) := disjoint_disjointed _
  have hBsub : ∀ i, B i ⊆ (T (g i)).baseSet := disjointed_subset _
  have hBunion : ⋃ i, B i = Set.univ := by
    rw [hB_def, iUnion_disjointed]
    rw [hg, Set.biUnion_range] at htuniv
    exact htuniv
  have hFmeas : Measurable F := hcov.continuous.measurable
  -- each piece contributes `k` times its measure
  have hpiece : ∀ i, μM (F ⁻¹' B i) = k * μN (B i) := by
    intro i
    haveI := (hfib (g i)).2
    haveI : DiscreteTopology (F ⁻¹' {g i}) := (hcov (g i)).discreteTopology_fiber
    rw [measure_preimage_eq_card_mul_of_trivialization μM μN
      hpres (T (g i)) (hFmeas (hBmeas i)) (hBsub i), hk (g i)]
  calc μM Set.univ
      = μM (F ⁻¹' ⋃ i, B i) := by rw [hBunion, Set.preimage_univ]
    _ = μM (⋃ i, F ⁻¹' B i) := by rw [Set.preimage_iUnion]
    _ = ∑' i, μM (F ⁻¹' B i) :=
        measure_iUnion (fun i j hij => (hBdisj hij).preimage F)
          fun i => hFmeas (hBmeas i)
    _ = ∑' i, (k : ENNReal) * μN (B i) := tsum_congr hpiece
    _ = k * ∑' i, μN (B i) := ENNReal.tsum_mul_left
    _ = k * μN Set.univ := by rw [← measure_iUnion hBdisj hBmeas, hBunion]

end Exercise3

/-! ## Exercise 1.6.4 — the volume form of a warped product

Petersen: the volume form of `dr² + ρ²(r) g_N` on `I × N` (with
`dim N = n − 1`) is `ρⁿ⁻¹ dr ∧ vol_N`. -/

section Exercise4

/-- **Math.** The adapted frame of the warped product `dr² + ρ²(r) g_N` on
`ℝ × N` associated with a frame `E₁, …, Eₘ` on `N`: the radial field
`∂_r = (1, 0)` followed by the normalized fields `(0, ρ⁻¹ Eⱼ)`. If the `Eⱼ`
are `g_N`-orthonormal this frame is orthonormal for the warped metric
(`exercise1_6_4`). -/
def warpedFrame (ρ : ℝ → ℝ) {m : ℕ}
    (frameN : Fin m → ∀ x : M, TangentSpace I x) :
    Fin (m + 1) → ∀ p : ℝ × M, TangentSpace (𝓘(ℝ, ℝ).prod I) p := fun i p =>
  Fin.cases ((1 : ℝ), (0 : TangentSpace I p.2))
    (fun j => ((0 : ℝ), (ρ p.1)⁻¹ • frameN j p.2)) i

/-- **Math.** Petersen Exercise 1.6.4: the volume form of the warped product
`dr² + ρ²(r) g_N` on `ℝ × N` is `ρᵐ dr ∧ vol_N` (with `m = dim N`, i.e.
`ρⁿ⁻¹` for an `n`-dimensional total space). Relative to a `g_N`-orthonormal
frame `E₁, …, Eₘ` at the foot point:

1. the adapted frame `∂_r, ρ⁻¹E₁, …, ρ⁻¹Eₘ` (`warpedFrame`) is orthonormal
   for the warped metric, so its `localVolumeForm` *is* the volume form of
   the warped product there; and
2. evaluated on any `n = m + 1` tangent vectors `X₀, …, Xₘ`, it equals
   `ρᵐ` times the determinant whose `0`-th column is `dr(Xᵢ) = (Xᵢ)₁` and
   whose remaining columns are the `vol_N`-columns `g_N((Xᵢ)₂, Eⱼ)` — the
   evaluation of the wedge `dr ∧ vol_N` on `X₀, …, Xₘ`. -/
theorem exercise1_6_4 [FiniteDimensional ℝ E]
    (gN : RiemannianMetric I M) {m : ℕ} (ρ : ℝ → ℝ)
    (hρs : ContDiff ℝ ∞ ρ) (hρ : ∀ t, ρ t ≠ 0)
    (frameN : Fin m → ∀ x : M, TangentSpace I x) (p : ℝ × M)
    (hframe : ∀ j k, gN.metricInner p.2 (frameN j p.2) (frameN k p.2) =
      if j = k then 1 else 0) :
    (∀ i j, (warpedProductMetric gN (fun _ => 1) ρ contDiff_const hρs
        (fun _ => one_ne_zero) hρ).metricInner p
        (warpedFrame ρ frameN i p) (warpedFrame ρ frameN j p) =
        if i = j then 1 else 0) ∧
    (∀ X : Fin (m + 1) → TangentSpace (𝓘(ℝ, ℝ).prod I) p,
      localVolumeForm (warpedProductMetric gN (fun _ => 1) ρ contDiff_const hρs
          (fun _ => one_ne_zero) hρ) (warpedFrame ρ frameN) p X =
        ρ p.1 ^ m *
          (Matrix.of fun i j => (Fin.cases ((X i).1)
            (fun j' : Fin m =>
              gN.metricInner p.2 (X i).2 (frameN j' p.2)) j : ℝ)).det) := by
  have hfst : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod I) p,
      mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) Prod.fst p w = w.1 := fun w => by
    rw [mfderiv_fst]; rfl
  have hsnd : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod I) p,
      mfderiv (𝓘(ℝ, ℝ).prod I) I Prod.snd p w = w.2 := fun w => by
    rw [mfderiv_snd]; rfl
  -- the warped metric against the adapted frame, one column at a time
  have key : ∀ (u : TangentSpace (𝓘(ℝ, ℝ).prod I) p) (j : Fin (m + 1)),
      (warpedProductMetric gN (fun _ => 1) ρ contDiff_const hρs
        (fun _ => one_ne_zero) hρ).metricInner p u (warpedFrame ρ frameN j p) =
      (Fin.cases u.1
        (fun j' : Fin m =>
          ρ p.1 * gN.metricInner p.2 u.2 (frameN j' p.2)) j : ℝ) := by
    intro u j
    rw [warpedProductMetric_apply, warpedProductForm_apply, hfst, hsnd,
      hfst, hsnd]
    induction j using Fin.cases with
    | zero =>
      show (1 : ℝ) ^ 2 * (innerProductSpaceMetric ℝ).metricInner p.1 u.1 1 +
        ρ p.1 ^ 2 * gN.metricInner p.2 u.2 0 = u.1
      rw [gN.metricInner_zero_right, innerProductSpaceMetric_apply]
      show (1 : ℝ) ^ 2 * (1 * u.1) + ρ p.1 ^ 2 * 0 = u.1
      ring
    | succ j' =>
      show (1 : ℝ) ^ 2 * (innerProductSpaceMetric ℝ).metricInner p.1 u.1 0 +
        ρ p.1 ^ 2 * gN.metricInner p.2 u.2 ((ρ p.1)⁻¹ • frameN j' p.2) =
        ρ p.1 * gN.metricInner p.2 u.2 (frameN j' p.2)
      rw [(innerProductSpaceMetric ℝ).metricInner_zero_right,
        gN.metricInner_smul_right]
      field_simp
      ring
  constructor
  · intro i j
    rw [key]
    induction j using Fin.cases with
    | zero =>
      induction i using Fin.cases with
      | zero => simp [warpedFrame]
      | succ i' => simp [warpedFrame, Fin.succ_ne_zero]
    | succ j' =>
      induction i using Fin.cases with
      | zero =>
        show ρ p.1 * gN.metricInner p.2 0 (frameN j' p.2) = _
        rw [gN.metricInner_zero_left]
        simp [(Fin.succ_ne_zero j').symm]
      | succ i' =>
        show ρ p.1 * gN.metricInner p.2 ((ρ p.1)⁻¹ • frameN i' p.2)
            (frameN j' p.2) = _
        rw [gN.metricInner_smul_left, hframe]
        rcases eq_or_ne i' j' with rfl | hne
        · simp [mul_inv_cancel₀ (hρ p.1)]
        · simp [hne]
  · intro X
    rw [localVolumeForm]
    have hentry : (Matrix.of fun i j =>
        (warpedProductMetric gN (fun _ => 1) ρ contDiff_const hρs
          (fun _ => one_ne_zero) hρ).metricInner p (X i)
          (warpedFrame ρ frameN j p)) =
        Matrix.of fun i j =>
          (Fin.cases (1 : ℝ) (fun _ : Fin m => ρ p.1) j) *
          (Fin.cases ((X i).1)
            (fun j' : Fin m =>
              gN.metricInner p.2 (X i).2 (frameN j' p.2)) j : ℝ) := by
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply, key]
      induction j using Fin.cases with
      | zero => simp
      | succ j' => simp
    rw [hentry, Matrix.det_mul_row]
    congr 1
    rw [Fin.prod_univ_succ]
    simp

end Exercise4

/-! ## Exercise 1.6.5 — the dual coframe and the volume form

Petersen: for an orthonormal frame `E₁, …, Eₙ`, the dual coframe is
`σⁱ(X) = g(Eᵢ, X)`, and `vol = ±σ¹ ∧ ⋯ ∧ σⁿ`. -/

section Exercise5

/-- **Math.** Petersen Exercise 1.6.5, part 1 (as a reusable lemma): for a
`g`-orthonormal basis `E₁, …, Eₙ` of `T_xM`, the `i`-th coordinate
functional (the `i`-th member of the dual coframe) is `X ↦ g(Eᵢ, X)`. -/
theorem orthonormal_frame_coord (g : RiemannianMetric I M) {n : ℕ}
    (frame : Fin n → ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) (hb : ∀ i, b i = frame i x)
    (hframe : ∀ j k, g.metricInner x (frame j x) (frame k x) =
      if j = k then 1 else 0)
    (i : Fin n) (X : TangentSpace I x) :
    b.coord i X = g.metricInner x (frame i x) X := by
  have hlin : (b.coord i : TangentSpace I x →ₗ[ℝ] ℝ) =
      ((g.inner x (frame i x) : TangentSpace I x →L[ℝ] ℝ) :
        TangentSpace I x →ₗ[ℝ] ℝ) := by
    refine b.ext fun j => ?_
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    show _ = g.metricInner x (frame i x) (b j)
    rw [hb, hframe i j]
    simp [eq_comm]
  exact DFunLike.congr_fun hlin X

/-- **Math.** Petersen Exercise 1.6.5: for a `g`-orthonormal frame
`E₁, …, Eₙ` at `x` (a basis `b` of `T_xM` with `bᵢ = Eᵢ(x)`),

1. the **dual coframe** is `σⁱ(X) = g(Eᵢ, X)` — the coordinate functionals
   of the basis are computed by the metric pairings with the frame; and
2. the local volume form is `vol = σ¹ ∧ ⋯ ∧ σⁿ`: evaluated on any vectors
   `X₁, …, Xₙ` it is the determinant `det [σʲ(Xᵢ)]`, the defining formula
   for the wedge of the `n` coframe `1`-forms. (The sign `±` of Petersen's
   statement is the declaration of the frame as positively oriented, built
   into `localVolumeForm`; the opposite orientation flips a column ordering
   and hence the sign.) -/
theorem exercise1_6_5 (g : RiemannianMetric I M) {n : ℕ}
    (frame : Fin n → ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) (hb : ∀ i, b i = frame i x)
    (hframe : ∀ j k, g.metricInner x (frame j x) (frame k x) =
      if j = k then 1 else 0) :
    (∀ (i : Fin n) (X : TangentSpace I x),
      b.coord i X = g.metricInner x (frame i x) X) ∧
    (∀ X : Fin n → TangentSpace I x,
      localVolumeForm g frame x X =
        (Matrix.of fun i j => b.coord j (X i)).det) := by
  refine ⟨orthonormal_frame_coord g frame x b hb hframe, fun X => ?_⟩
  rw [localVolumeForm]
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply,
    orthonormal_frame_coord g frame x b hb hframe j (X i),
    g.metricInner_comm]

end Exercise5

/-! ## Exercise 1.6.6 — the volume form in local coordinates

Petersen: in local coordinates `x¹, …, xⁿ`,
`vol = ±√(det [gᵢⱼ]) dx¹ ∧ ⋯ ∧ dxⁿ` with `gᵢⱼ = g(∂ᵢ, ∂ⱼ)`. -/

section Exercise6

/-- **Eng.** The metric inner product distributes over finite sums in the
second slot (the bundled `g.inner x u` is linear). -/
private theorem metricInner_sum_right (g : RiemannianMetric I M) (x : M)
    {ι : Type*} (s : Finset ι) (u : TangentSpace I x)
    (f : ι → TangentSpace I x) :
    g.metricInner x u (∑ i ∈ s, f i) = ∑ i ∈ s, g.metricInner x u (f i) :=
  map_sum (g.inner x u) f s

/-- **Math.** Petersen Exercise 1.6.6: in local coordinates `x¹, …, xⁿ`
with coordinate fields `∂₁, …, ∂ₙ` (at the point `x`, a family
`part : Fin n → T_xM` forming a basis `bp`), the volume form is
`vol = ±√(det [gᵢⱼ]) dx¹ ∧ ⋯ ∧ dxⁿ`, where `gᵢⱼ = g(∂ᵢ, ∂ⱼ)`. Relative to
a `g`-orthonormal frame `E` at `x` (a basis `b` with `bᵢ = Eᵢ(x)`,
declared positive — `localVolumeForm g frame x` is the volume form):

1. `vol(∂₁, …, ∂ₙ)² = det [gᵢⱼ]` — so `vol(∂₁, …, ∂ₙ) = ±√(det [gᵢⱼ])`,
   the sign being the orientation of the coordinates; the proof is the
   Gram factorization `[gᵢⱼ] = A Aᵀ` for `A = [g(∂ᵢ, Eⱼ)]`; and
2. for any vectors `X₁, …, Xₙ`,
   `vol(X₁, …, Xₙ) = det [dxᵏ(Xᵢ)] · vol(∂₁, …, ∂ₙ)` — the two top forms
   `vol` and `dx¹ ∧ ⋯ ∧ dxⁿ = det [dxᵏ(·)]` are proportional with factor
   `vol(∂) = ±√(det [gᵢⱼ])`. -/
theorem exercise1_6_6 (g : RiemannianMetric I M) {n : ℕ}
    (frame : Fin n → ∀ x : M, TangentSpace I x) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) (hb : ∀ i, b i = frame i x)
    (hframe : ∀ j k, g.metricInner x (frame j x) (frame k x) =
      if j = k then 1 else 0)
    (part : Fin n → TangentSpace I x)
    (bp : Basis (Fin n) ℝ (TangentSpace I x)) (hbp : ∀ i, bp i = part i) :
    localVolumeForm g frame x part ^ 2 =
      (Matrix.of fun i j => g.metricInner x (part i) (part j)).det ∧
    (∀ X : Fin n → TangentSpace I x,
      localVolumeForm g frame x X =
        (Matrix.of fun i k => bp.coord k (X i)).det *
          localVolumeForm g frame x part) := by
  have hcoord := orthonormal_frame_coord g frame x b hb hframe
  -- the metric pairing with the frame expands any vector in the frame
  have hexp : ∀ u v : TangentSpace I x,
      g.metricInner x u v =
        ∑ k, g.metricInner x (frame k x) v * g.metricInner x u (frame k x) := by
    intro u v
    conv_lhs => rw [← b.sum_repr v]
    rw [metricInner_sum_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [g.metricInner_smul_right, hb, ← Basis.coord_apply, hcoord]
  constructor
  · -- Gram factorization: `[gᵢⱼ] = A Aᵀ` for `A = [g(∂ᵢ, Eⱼ)]`
    set A : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of fun i j => g.metricInner x (part i) (frame j x) with hA
    have hgram : (Matrix.of fun i j => g.metricInner x (part i) (part j)) =
        A * A.transpose := by
      ext i j
      rw [Matrix.mul_apply, Matrix.of_apply, hexp (part i) (part j)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hA, Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply,
        g.metricInner_comm x (frame k x) (part j)]
      ring
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, localVolumeForm, ← hA,
      sq]
  · intro X
    -- expand each `Xᵢ` in the coordinate basis: `[g(Xᵢ, Eⱼ)] = C · A`
    set A : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of fun i j => g.metricInner x (part i) (frame j x) with hA
    set C : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of fun i k => bp.coord k (X i) with hC
    have hmat : (Matrix.of fun i j => g.metricInner x (X i) (frame j x)) =
        C * A := by
      ext i j
      rw [Matrix.mul_apply, Matrix.of_apply]
      conv_lhs => rw [show X i = ∑ k, bp.repr (X i) k • bp k from
        (bp.sum_repr (X i)).symm]
      rw [g.metricInner_comm, metricInner_sum_right]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [g.metricInner_smul_right, hC, hA, Matrix.of_apply, Matrix.of_apply,
        hbp, ← Basis.coord_apply, g.metricInner_comm]
    rw [localVolumeForm, hmat, Matrix.det_mul, localVolumeForm, ← hA]

end Exercise6

/-! ## Exercise 1.6.7 — paper models of `dt² + a²t²dθ²`

Petersen: construct paper models of the metrics `dt² + a²t²dθ²`: for
`a = 1` this is the Euclidean plane, for `a < 1` a cone; describe `a > 1`. -/

section Exercise7

/-- **Math.** Petersen Exercise 1.6.7, the unrolling map of the paper
model: `Φ_a(t, θ) = (t cos(aθ), t sin(aθ))`, i.e. the polar-coordinates
map precomposed with `θ ↦ aθ`. It wraps the abstract cone
(`dt² + a²t²dθ²`-cylinder) onto the Euclidean plane. -/
def coneUnrollingMap (a : ℝ) (q : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  polarCoordinatesMap (q.1, a * q.2)

/-- **Math.** Petersen Exercise 1.6.7 (paper models): the pullback of the
Euclidean plane metric under the unrolling map
`Φ_a(t, θ) = (t cos(aθ), t sin(aθ))` is exactly `dt² + a²t² dθ²` — so the
abstract metric `dt² + a²t²dθ²` is realized by "rolling flat paper":

* for `a = 1`, `Φ₁` is the polar-coordinates map and the metric is the
  Euclidean plane (Example 1.4.2 / `polarCoordinateMetric`);
* for `a < 1`, `Φ_a` maps the strip `θ ∈ [0, 2π)` onto a sector of angle
  `2πa`; gluing its edges builds the cone from a plane sector of paper;
* for `a > 1`, a full turn `θ ∈ [0, 2π)` wraps more than once around the
  origin: the "cone" of angle excess cannot be assembled from flat paper
  without overlap (it is still locally flat, by this very computation).

Since `Φ_a` is injective and metric-preserving on suitable strips
`{t > 0, θ₀ < θ < θ₀ + 2π/max(a,1)}`, each such piece of the cone is
isometric to a Euclidean sector, which is the paper model. -/
theorem exercise1_6_7 (a : ℝ) (p : ℝ × ℝ) (u v : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
    pullbackForm (euclideanMetric 2) (coneUnrollingMap a) p u v =
      u.1 * v.1 + a ^ 2 * p.1 ^ 2 * (u.2 * v.2) := by
  -- `Φ_a = P ∘ L` for the linear map `L(t, θ) = (t, aθ)`
  set L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (a • ContinuousLinearMap.snd ℝ ℝ ℝ)
    with hL
  have hLapply : ∀ q : ℝ × ℝ, L q = (q.1, a * q.2) := fun q => rfl
  have hmfC : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (coneUnrollingMap a) p = (polarJacobian (L p)).comp L := by
    rw [mfderiv_eq_fderiv]
    have hd : HasFDerivAt (coneUnrollingMap a) ((polarJacobian (L p)).comp L)
        p := (hasFDerivAt_polarCoordinatesMap (L p)).comp p L.hasFDerivAt
    exact hd.fderiv
  have hmfP : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      polarCoordinatesMap (L p) = polarJacobian (L p) := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_polarCoordinatesMap (L p)).fderiv
  have hpolar := polarCoordinateMetric (L p) (L u) (L v)
  rw [pullbackForm_apply, hmfP] at hpolar
  rw [pullbackForm_apply, hmfC]
  have hgoal : (euclideanMetric 2).metricInner (coneUnrollingMap a p)
      (((polarJacobian (L p)).comp L) u) (((polarJacobian (L p)).comp L) v)
      = (L u).1 * (L v).1 + (L p).1 ^ 2 * ((L u).2 * (L v).2) := hpolar
  refine hgoal.trans ?_
  show u.1 * v.1 + p.1 ^ 2 * ((a * u.2) * (a * v.2)) = _
  ring

end Exercise7

/-! ## Exercise 1.6.8 — smoothness for the sphere of radius `R`

Petersen: for `dr² + ρ²(r) g_{Sⁿ⁻¹(R)}` with `ρ(0) = 0`, smoothness at
`r = 0` forces `ρ̇(0) = 1/R` and `ρ^{(2k)}(0) = 0`. -/

section Exercise8

/-- **Math.** Petersen Exercise 1.6.8: the rotationally symmetric metric
`dr² + ρ²(r) g_{Sⁿ⁻¹(R)}` over the sphere of radius `R` extends smoothly
across `r = 0` if and only if `ρ(0) = 0`, `ρ̇(0) = 1/R`, and all
even-order derivatives of `ρ` vanish at `0`.

Since `g_{Sⁿ⁻¹(R)} = R² ds²_{n−1}`, the metric is
`dr² + (Rρ(r))² ds²_{n−1}`, and the exercise is the smoothness criterion
`rotationallySymmetricSmoothnessCriterion` (for ambient dimension `n ≥ 1`)
applied to `ρ̃ = Rρ`: its
conditions `ρ̃(0) = 0`, `ρ̃̇(0) = 1`, `ρ̃^{(2l)}(0) = 0` translate to
`ρ(0) = 0`, `ρ̇(0) = 1/R`, `ρ^{(2l)}(0) = 0`. "Extends smoothly" is
expressed, as in the criterion, through the two coefficient functions of
the Cartesian form of the metric (`rotSymCartesianForm`). -/
theorem exercise1_6_8 {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ t : ℝ, 0 < t → 0 < ρ t) :
    (∃ (ε : ℝ) (_ : 0 < ε) (F₁ F₂ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ F₁ (Metric.ball 0 ε) ∧
      ContDiffOn ℝ ∞ F₂ (Metric.ball 0 ε) ∧
      0 < F₁ 0 ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Metric.ball 0 ε → x ≠ 0 →
        F₁ x = (R * ρ ‖x‖) ^ 2 / ‖x‖ ^ 2 ∧
        F₂ x = 1 / ‖x‖ ^ 2 - (R * ρ ‖x‖) ^ 2 / ‖x‖ ^ 4) ↔
    (ρ 0 = 0 ∧ deriv ρ 0 = 1 / R ∧
      ∀ l : ℕ, 1 ≤ l → iteratedDeriv (2 * l) ρ 0 = 0) := by
  have hcrit := rotationallySymmetricSmoothnessCriterion (n := n) hn
    (fun t => R * ρ t) (contDiff_const.mul hρ)
    (fun t ht => mul_pos hR (hpos t ht))
  rw [hcrit]
  have hd : deriv (fun t => R * ρ t) 0 = R * deriv ρ 0 :=
    deriv_const_mul R (hρ.differentiable (by simp)).differentiableAt
  have hiter : ∀ l : ℕ, iteratedDeriv (2 * l) (fun t => R * ρ t) 0 =
      R * iteratedDeriv (2 * l) ρ 0 := fun l =>
    iteratedDeriv_const_mul R
      (hρ.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _))
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by simpa [hR.ne'] using h0, ?_, fun l hl => ?_⟩
    · rw [hd] at h1
      field_simp
      linarith [h1]
    · have := h2 l hl
      rw [hiter l] at this
      exact (mul_eq_zero.mp this).resolve_left hR.ne'
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by simp [h0], ?_, fun l hl => ?_⟩
    · rw [hd, h1]
      field_simp
    · rw [hiter l, h2 l hl, mul_zero]

end Exercise8

/-! ## Exercise 1.6.9 — `Iso(ℝⁿ)` as a matrix group

Petersen: viewing `ℝⁿ` as the hyperplane `xⁿ⁺¹ = R` in `ℝⁿ⁺¹`, the
isometry group `Iso(ℝⁿ)` is identified with the group of matrices
`[[O, v], [0, 1]]`, `O ∈ O(n)`, `v ∈ ℝⁿ` — exactly the linear maps of
`ℝⁿ⁺¹` preserving the hyperplane and the degenerate bilinear form
`x¹y¹ + ⋯ + xⁿyⁿ` (on the direction space of the hyperplane). -/

section Exercise9

/-- **Math.** Petersen Exercise 1.6.9, the matrix-group characterization: a
linear map `L` of `ℝⁿ⁺¹ = ℝⁿ × ℝ` preserves the hyperplane `xⁿ⁺¹ = R` and
the degenerate form `x¹y¹ + ⋯ + xⁿyⁿ` on its direction space
`{xⁿ⁺¹ = 0}` if and only if it is the block matrix `[[O, v/R], [0, 1]]`
for an orthogonal `O ∈ O(n)` and a vector `v ∈ ℝⁿ`
(`L(x, s) = (O x + (s/R) v, s)` — so `L` acts on the hyperplane as the
Euclidean isometry `x ↦ O x + v`). -/
theorem euclideanIsometry_matrix_char {n : ℕ} (R : ℝ) (hR : R ≠ 0)
    (L : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)) :
    ((∀ x : EuclideanSpace ℝ (Fin n), (L (x, R)).2 = R) ∧
      ∀ w w' : EuclideanSpace ℝ (Fin n),
        ⟪(L (w, 0)).1, (L (w', 0)).1⟫ = ⟪w, w'⟫) ↔
    ∃ (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
      (v : EuclideanSpace ℝ (Fin n)),
      ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        L (x, s) = (O x + (s / R) • v, s) := by
  constructor
  · rintro ⟨h1, h2⟩
    -- the linear part on the direction space of the hyperplane
    set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      (LinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp
        (L.comp (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)) with hT
    have hTapp : ∀ w, T w = (L (w, 0)).1 := fun w => rfl
    have hTinner : ∀ w w', ⟪T w, T w'⟫ = ⟪w, w'⟫ := by
      intro w w'
      rw [hTapp, hTapp]
      exact h2 w w'
    set O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
      (T.isometryOfInner hTinner).toLinearIsometryEquiv rfl with hO
    have hOapp : ∀ w, O w = (L (w, 0)).1 := fun w => rfl
    -- decompose `(x, s)` along the hyperplane direction and `(0, R)`
    have hdecomp : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        ((x, s) : EuclideanSpace ℝ (Fin n) × ℝ) =
          (x, 0) + (s / R) • ((0 : EuclideanSpace ℝ (Fin n)), R) := by
      intro x s
      refine Prod.ext (by simp) ?_
      show s = 0 + (s / R) * R
      rw [zero_add, div_mul_cancel₀ s hR]
    have hsnd0 : ∀ x : EuclideanSpace ℝ (Fin n), (L (x, 0)).2 = 0 := by
      intro x
      have hxR : ((x, R) : EuclideanSpace ℝ (Fin n) × ℝ) = (x, 0) + (0, R) := by
        refine Prod.ext (by simp) ?_
        show R = 0 + R
        rw [zero_add]
      have := h1 x
      rw [hxR, map_add] at this
      have h0R := h1 0
      have h00 : ((0, R) : EuclideanSpace ℝ (Fin n) × ℝ) = ((0 : EuclideanSpace ℝ (Fin n)), 0) + (0, R) := by
        refine Prod.ext (by simp) ?_
        show R = 0 + R
        rw [zero_add]
      -- `(L (x, 0)).2 + (L (0, R)).2 = R` and `(L (0, R)).2 = R`
      have hL0R : (L (0, R)).2 = R := h1 0
      rw [Prod.snd_add] at this
      linarith [this, hL0R]
    refine ⟨O, (L (0, R)).1, fun x s => ?_⟩
    rw [hdecomp x s, map_add, map_smul]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, hOapp]
      show (L (x, 0)).1 + (s / R) • (L (0, R)).1 = (L (x, 0)).1 + (s / R) • (L (0, R)).1
      rfl
    · rw [Prod.snd_add, hsnd0 x]
      show 0 + (s / R) * (L (0, R)).2 = s
      rw [h1 0, zero_add, div_mul_cancel₀ s hR]
  · rintro ⟨O, v, hL⟩
    constructor
    · intro x
      rw [hL x R]
    · intro w w'
      rw [hL w 0, hL w' 0]
      simp [zero_div, LinearIsometryEquiv.inner_map_map]

/-- **Math.** Petersen Exercise 1.6.9: viewing `ℝⁿ` as the hyperplane
`xⁿ⁺¹ = R` in `ℝⁿ⁺¹ = ℝⁿ × ℝ`:

1. the linear maps of `ℝⁿ⁺¹` preserving the hyperplane and the degenerate
   form `x¹y¹ + ⋯ + xⁿyⁿ` on its direction space are exactly the block
   matrices `[[O, v/R], [0, 1]]`, `O ∈ O(n)`, `v ∈ ℝⁿ`
   (`euclideanIsometry_matrix_char`); and
2. `Iso(ℝⁿ)` is identified with this matrix group: a permutation `F` of
   `ℝⁿ` is a Riemannian isometry iff it is induced on the hyperplane by
   such a matrix, `F(x) = (L(x, R))₁`.

(The identification is a group isomorphism: composition of the induced
maps corresponds to matrix multiplication, both being composition of
maps of `ℝⁿ⁺¹`.) -/
theorem exercise1_6_9 {n : ℕ} (R : ℝ) (hR : R ≠ 0) :
    (∀ L : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) × ℝ),
      ((∀ x : EuclideanSpace ℝ (Fin n), (L (x, R)).2 = R) ∧
        ∀ w w' : EuclideanSpace ℝ (Fin n),
          ⟪(L (w, 0)).1, (L (w', 0)).1⟫ = ⟪w, w'⟫) ↔
      ∃ (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (v : EuclideanSpace ℝ (Fin n)),
        ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
          L (x, s) = (O x + (s / R) • v, s)) ∧
    (∀ F : Equiv.Perm (EuclideanSpace ℝ (Fin n)),
      F ∈ IsometryGroup (euclideanMetric n) ↔
      ∃ L : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin n) × ℝ),
        ((∀ x : EuclideanSpace ℝ (Fin n), (L (x, R)).2 = R) ∧
          ∀ w w' : EuclideanSpace ℝ (Fin n),
            ⟪(L (w, 0)).1, (L (w', 0)).1⟫ = ⟪w, w'⟫) ∧
        ∀ x, F x = (L (x, R)).1) := by
  refine ⟨euclideanIsometry_matrix_char R hR, fun F => ?_⟩
  constructor
  · intro hF
    obtain ⟨v, O, hFvO⟩ := (isometryGroup_euclideanSpace F).mp hF
    -- the block matrix `[[O, v/R], [0, 1]]`
    set L : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) × ℝ) :=
      ((O.toLinearEquiv :
          EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap.comp
        (LinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
        (LinearMap.toSpanSingleton ℝ (EuclideanSpace ℝ (Fin n)) v).comp
          (R⁻¹ • LinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)).prod
        (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) with hLdef
    have hLapp : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        L (x, s) = (O x + (s / R) • v, s) := by
      intro x s
      refine Prod.ext ?_ rfl
      show O x + (R⁻¹ * s) • v = O x + (s / R) • v
      rw [div_eq_mul_inv, mul_comm]
    refine ⟨L, (euclideanIsometry_matrix_char R hR L).mpr ⟨O, v, hLapp⟩,
      fun x => ?_⟩
    rw [hLapp x R, hFvO x, div_self hR, one_smul]
    exact add_comm v (O x)
  · rintro ⟨L, hcond, hFL⟩
    obtain ⟨O, v, hL⟩ := (euclideanIsometry_matrix_char R hR L).mp hcond
    refine (isometryGroup_euclideanSpace F).mpr ⟨v, O, fun x => ?_⟩
    rw [hFL x, hL x R, div_self hR, one_smul]
    exact add_comm (O x) v

end Exercise9

/-! ## Exercise 1.6.10 — Sylvester bases for a nondegenerate form

Petersen: for a symmetric nondegenerate bilinear form `g` of index `p` on
an `n`-dimensional `V`: (1) there is a basis `e₁, …, eₙ` with
`g(eᵢ, eⱼ) = 0` for `i ≠ j`, `g(eᵢ, eᵢ) = 1` for `i ≤ n − p` and `= −1`
for `i > n − p` (so `V ≅ ℝ^{p,q}`); (2) every vector expands as
`v = Σᵢ g(v, eᵢ)/g(eᵢ, eᵢ) · eᵢ`; (3) for `L : V → V` linear,
`tr L = Σᵢ g(L(eᵢ), eᵢ)/g(eᵢ, eᵢ)`. -/

section Exercise10

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Petersen Exercise 1.6.10 (2), for any `g`-orthogonal basis
with nonisotropic vectors: the coordinates of `w` are
`g(w, eᵢ)/g(eᵢ, eᵢ)` — pair `w = Σ wʲ eⱼ` with `eᵢ` and use
orthogonality. -/
theorem orthogonal_basis_repr (g : LinearMap.BilinForm ℝ V) {N : ℕ}
    (e : Basis (Fin N) ℝ V)
    (horth : ∀ i j, i ≠ j → g (e i) (e j) = 0)
    (hne : ∀ i, g (e i) (e i) ≠ 0) (w : V) (i : Fin N) :
    e.repr w i = g w (e i) / g (e i) (e i) := by
  have hpair : g w (e i) = e.repr w i * g (e i) (e i) := by
    conv_lhs => rw [← e.sum_repr w]
    rw [LinearMap.BilinForm.sum_left]
    rw [Finset.sum_eq_single i]
    · rw [LinearMap.BilinForm.smul_left]
    · intro j _ hj
      rw [LinearMap.BilinForm.smul_left, horth j i hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hpair, mul_div_assoc, div_self (hne i), mul_one]

/-- **Math.** Petersen Exercise 1.6.10 (3), for any `g`-orthogonal basis
with nonisotropic vectors: `tr L = Σᵢ g(L(eᵢ), eᵢ)/g(eᵢ, eᵢ)` — the trace
is the sum of the diagonal matrix entries `(L(eᵢ))ⁱ`, computed by
`orthogonal_basis_repr`. -/
theorem orthogonal_basis_trace (g : LinearMap.BilinForm ℝ V) {N : ℕ}
    (e : Basis (Fin N) ℝ V)
    (horth : ∀ i j, i ≠ j → g (e i) (e j) = 0)
    (hne : ∀ i, g (e i) (e i) ≠ 0) (T : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ V T = ∑ i, g (T (e i)) (e i) / g (e i) (e i) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ e T, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    orthogonal_basis_repr g e horth hne]

/-- **Math.** Petersen Exercise 1.6.10: for a symmetric **nondegenerate**
bilinear form `g` on an `n`-dimensional real vector space `V` there are
`p ≤ n` and a **Sylvester basis** `e₁, …, eₙ`:

1. `g(eᵢ, eⱼ) = 0` for `i ≠ j`, `g(eᵢ, eᵢ) = 1` for the first `n − p`
   indices and `−1` for the last `p` — an isomorphism `V ≅ ℝ^{p,q}`,
   `q = n − p` (by Sylvester's law of inertia `p` is unique — it is the
   index of `g`, the maximal dimension of a negative-definite subspace,
   cf. `pseudoRiemannianIndex`; uniqueness is not formalized here);
2. `v = Σᵢ (g(v, eᵢ)/g(eᵢ, eᵢ)) eᵢ` — i.e.
   `v = Σ_{i ≤ n−p} g(v, eᵢ) eᵢ − Σ_{i > n−p} g(v, eᵢ) eᵢ`
   (`orthogonal_basis_repr`); and
3. `tr L = Σᵢ g(L(eᵢ), eᵢ)/g(eᵢ, eᵢ)` for every linear `L : V → V`
   (`orthogonal_basis_trace`).

The construction: diagonalize `g`
(`LinearMap.BilinForm.exists_orthogonal_basis`, diagonal entries nonzero
by nondegeneracy), normalize each vector by `|g(vᵢ, vᵢ)|^{-1/2}`, and
permute the `+1`-vectors to the front. -/
theorem exercise1_6_10 [FiniteDimensional ℝ V]
    (g : LinearMap.BilinForm ℝ V) (hsymm : g.IsSymm) (hnd : g.Nondegenerate) :
    ∃ (p : ℕ) (e : Basis (Fin (finrank ℝ V)) ℝ V),
      p ≤ finrank ℝ V ∧
      (∀ i j, i ≠ j → g (e i) (e j) = 0) ∧
      (∀ i : Fin (finrank ℝ V),
        g (e i) (e i) = if (i : ℕ) < finrank ℝ V - p then 1 else -1) ∧
      (∀ w : V, w = ∑ i, (g w (e i) / g (e i) (e i)) • e i) ∧
      (∀ T : V →ₗ[ℝ] V,
        LinearMap.trace ℝ V T = ∑ i, g (T (e i)) (e i) / g (e i) (e i)) := by
  classical
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  set N := finrank ℝ V with hN
  -- a `g`-orthogonal basis, with nonisotropic vectors by nondegeneracy
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := g)
    (LinearMap.BilinForm.isSymm_iff.mp hsymm)
  have hvne : ∀ i, g (v i) (v i) ≠ 0 := by
    intro i h0
    have hall : ∀ w, g (v i) w = 0 := by
      intro w
      conv_lhs => rw [← v.sum_repr w]
      rw [map_sum, Finset.sum_eq_zero]
      intro j _
      rw [map_smul, smul_eq_mul]
      rcases eq_or_ne i j with rfl | hij
      · rw [h0, mul_zero]
      · rw [hv hij, mul_zero]
    exact v.ne_zero i (hnd.1 (v i) hall)
  -- normalize to `g(uᵢ, uᵢ) = ±1`
  have hsq : ∀ i, 0 < Real.sqrt |g (v i) (v i)| := fun i =>
    Real.sqrt_pos.mpr (abs_pos.mpr (hvne i))
  have hcunit : ∀ i, IsUnit ((Real.sqrt |g (v i) (v i)|)⁻¹) := fun i =>
    isUnit_iff_ne_zero.mpr (inv_ne_zero (hsq i).ne')
  set u : Basis (Fin N) ℝ V := v.unitsSMul fun i => (hcunit i).unit with hu
  have huapp : ∀ i, u i = (Real.sqrt |g (v i) (v i)|)⁻¹ • v i := by
    intro i
    rw [hu, Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec]
  have hudiag : ∀ i, g (u i) (u i) =
      if 0 < g (v i) (v i) then 1 else -1 := by
    intro i
    rw [huapp, LinearMap.BilinForm.smul_left, map_smul, smul_eq_mul,
      ← mul_assoc, ← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]
    rcases lt_or_gt_of_ne (hvne i) with hneg | hpos
    · rw [if_neg (not_lt.mpr hneg.le), abs_of_neg hneg, inv_neg, neg_mul,
        inv_mul_cancel₀ (hvne i)]
    · rw [if_pos hpos, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  have huorth : ∀ i j, i ≠ j → g (u i) (u j) = 0 := by
    intro i j hij
    rw [huapp, huapp, LinearMap.BilinForm.smul_left, map_smul, smul_eq_mul,
      hv hij, mul_zero, mul_zero]
  -- permute the `+1`-vectors to the front
  set Pos : Finset (Fin N) :=
    Finset.univ.filter (fun i => 0 < g (v i) (v i)) with hPosDef
  set k := Pos.card with hk
  have hkN : k ≤ N := (Finset.card_le_univ Pos).trans_eq (Fintype.card_fin N)
  have hks : k + (N - k) = N := Nat.add_sub_cancel' hkN
  have hcardc : Posᶜ.card = N - k := by
    rw [Finset.card_compl, Fintype.card_fin]
  set e₁ : Fin k ≃ {x // x ∈ Pos} := (Pos.orderIsoOfFin rfl).toEquiv with he₁
  set e₂ : Fin (N - k) ≃ {x : Fin N // ¬ x ∈ Pos} :=
    (Posᶜ.orderIsoOfFin hcardc).toEquiv.trans
      (Equiv.subtypeEquivRight fun x => Finset.mem_compl) with he₂
  set φ : Fin N ≃ Fin N :=
    ((finCongr hks.symm).trans finSumFinEquiv.symm).trans
      ((e₁.sumCongr e₂).trans (Equiv.sumCompl fun x => x ∈ Pos)) with hφdef
  have hφ : ∀ i : Fin N, ((i : ℕ) < k ↔ φ i ∈ Pos) := by
    intro i
    have hφi : φ i = (Equiv.sumCompl fun x => x ∈ Pos)
        ((e₁.sumCongr e₂) (finSumFinEquiv.symm (finCongr hks.symm i))) := rfl
    rcases hsplit : finSumFinEquiv.symm (finCongr hks.symm i) with a | b
    · have hval : (i : ℕ) = (a : ℕ) := by
        have := congrArg finSumFinEquiv hsplit
        rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_left] at this
        have hcoe := congrArg Fin.val this
        simpa using hcoe
      have hmem : φ i ∈ Pos := by
        rw [hφi, hsplit]
        exact (e₁ a).2
      exact ⟨fun _ => hmem, fun _ => hval ▸ a.isLt⟩
    · have hval : (i : ℕ) = k + (b : ℕ) := by
        have := congrArg finSumFinEquiv hsplit
        rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_right] at this
        have hcoe := congrArg Fin.val this
        simpa using hcoe
      have hmem : φ i ∉ Pos := by
        rw [hφi, hsplit]
        exact (e₂ b).2
      constructor
      · intro hlt
        exact absurd hval (by omega)
      · intro hp
        exact absurd hp hmem
  set e : Basis (Fin N) ℝ V := u.reindex φ.symm with he
  have heapp : ∀ i, e i = u (φ i) := by
    intro i
    rw [he, Basis.reindex_apply, Equiv.symm_symm]
  have hediag : ∀ i : Fin N,
      g (e i) (e i) = if (i : ℕ) < k then 1 else -1 := by
    intro i
    rw [heapp, hudiag]
    rcases lt_or_ge (i : ℕ) k with hlt | hge
    · rw [if_pos hlt,
        if_pos (by simpa [hPosDef, Finset.mem_filter] using (hφ i).mp hlt)]
    · have hnot : ¬ (i : ℕ) < k := not_lt.mpr hge
      rw [if_neg hnot, if_neg]
      intro hpos
      exact hnot ((hφ i).mpr (by simpa [hPosDef, Finset.mem_filter] using hpos))
  have heorth : ∀ i j, i ≠ j → g (e i) (e j) = 0 := by
    intro i j hij
    rw [heapp, heapp]
    exact huorth _ _ fun h => hij (φ.injective h)
  have hene : ∀ i, g (e i) (e i) ≠ 0 := by
    intro i
    rw [hediag i]
    split <;> norm_num
  refine ⟨N - k, e, Nat.sub_le N k, heorth, ?_, fun w => ?_, ?_⟩
  · intro i
    rw [hediag i, Nat.sub_sub_self hkN]
  · conv_lhs => rw [← e.sum_repr w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [orthogonal_basis_repr g e heorth hene]
  · exact orthogonal_basis_trace g e heorth hene

end Exercise10

end PetersenLib
