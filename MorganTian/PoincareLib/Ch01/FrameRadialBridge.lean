import PoincareLib.Ch01.FrameCurvContinuity
import PoincareLib.Ch01.RadialJacobiExists
import PoincareLib.Ch01.RadialComparison

/-!
# Poincaré Ch. 1, §1.4 — from a geodesic on `M` to the radial Jacobi datum

This file closes the last gap of the comparison chain: it **produces**, from a
geodesic `γ` on an honest Riemannian manifold, the abstract datum
`IsRadialJacobi ℛ 𝒥 𝒥' b C` that `JacobiRiccati` / `RadialComparison` /
`VolumeElement` consume, and it identifies `𝒥` with the geometry.

The mechanism.  `FrameJacobiSystem` reduces the Jacobi equation along `γ` to the
closed scalar system `c'' = frameCurv · c` in a parallel `g`-orthonormal frame
`E₁, …, Eₙ`.  Coefficient vectors are collected in **Euclidean `n`-space**
`𝔼 = EuclideanSpace ℝ (Fin n)`, `n = dim M`, with its standard orthonormal basis
`b₁, …, bₙ` (`EuclideanSpace.basisFun`):

* `frameVec g γ e V t = ∑ᵢ ⟨V t, Eᵢ(t)⟩_g • bᵢ` — the coefficient vector of a
  field along `γ`.  The frame being `g`-orthonormal and `b` orthonormal, this is a
  **linear isometry of `(T_{γt}M, g)` onto `𝔼`** (`metricInner_eq_inner_frameVec`),
  so it converts metric statements about `J` into norm statements about
  `frameVec J`, and back.
* `frameCurvOp g γ e t = ∑ᵢⱼ (−frameCurvᵢⱼ(t)) • (⟨bⱼ, ·⟩ • bᵢ)` — the Jacobi
  operator `R_{γ'} = ℛ(·, γ')γ'` of the frame, as an operator on `𝔼`.  The sign is
  the one that turns the frame system `c'' = frameCurv · c` into the convention
  `𝒥'' + ℛ𝒥 = 0` of `IsJacobiSolOn`; so `frameCurvOp` is Morgan–Tian's
  `⟨ℛ(Eⱼ, γ')γ', Eᵢ⟩`, the operator whose quadratic form is the unnormalized
  sectional curvature.

Main results:

* `frameCurvOp_symm` / `continuousOn_frameCurvOp` — the `curv_symm` and
  `curv_cont` fields of `IsRadialJacobi`, i.e. the curvature symmetry
  `R_{ijkl} = R_{klij}` and (the hard one) continuity of the curvature
  coefficient along a chart-crossing geodesic;
* `isJacobiSolOn_frameVec` — a Jacobi field along `γ`, read in the frame, solves
  the abstract second-order ODE on the *closed* interval;
* `exists_isRadialJacobi_of_geodesic` — **the producer**: the datum exists, and
  every Jacobi field vanishing at the centre is a column of `𝒥`:
  `frameVec J t = 𝒥 t (frameVec ∇J 0)` (ODE uniqueness);
* `metricInner_jacobi_le_snK` — **the sectional-curvature comparison on the
  manifold** (`thm:sectional-curvature-comparison`, metric half):
  `|J(r)|_g ≤ sn_k(r) · |∇J(0)|_g`, i.e. `g_{ij}(r, θ) ≤ sn_k²(r)` in geodesic
  polar coordinates.

Blueprint: `lem:geodesic-polar-form`, `lem:jacobi-frame-reduction`,
`lem:radial-comparison`, `thm:sectional-curvature-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4, §1.6.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- The **coefficient space** of the parallel frame: Euclidean `n`-space,
`n = dim M`.  (Not the model space `E` itself: `E` carries two independent
`NormedSpace ℝ E` instances in this development — the one from
`ModelWithCorners` and the one from `InnerProductSpace` — so its orthonormal
basis is not available.  `EuclideanSpace` has canonical instances.) -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The standard orthonormal basis of the coefficient space. -/
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-- Orthonormality of the standard basis of the coefficient space, in `ite`
form. -/
theorem basisFun_inner (i j : Fin (Module.finrank ℝ E)) :
    ⟪(𝔟 i : 𝔼), 𝔟 j⟫ = if i = j then (1 : ℝ) else 0 := by
  classical
  exact orthonormal_iff_ite.mp
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).orthonormal i j

/-! ### Parseval on the manifold -/

/-- **Math.** **Parseval for a `g`-orthonormal frame.**  In a `g`-orthonormal
family `e₁, …, eₙ` of `T_qM` (`n = dim M`, so the family is a basis),

`⟨v, w⟩_g = ∑ᵢ ⟨v, eᵢ⟩_g ⟨w, eᵢ⟩_g`.

Expand `v` in the frame (`metricInner_orthonormal_expansion`) and use linearity of
`g` in the first slot.  This is what makes the coefficient map an isometry. -/
theorem metricInner_parseval (g : RiemannianMetric I M) {q : M}
    {e : Fin (Module.finrank ℝ E) → TangentSpace I q}
    (horth : ∀ i j, g.metricInner q (e i) (e j) = if i = j then 1 else 0)
    (v w : TangentSpace I q) :
    g.metricInner q v w = ∑ i, g.metricInner q v (e i) * g.metricInner q w (e i) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hv : v = ∑ i, g.metricInner q v (e i) • e i :=
    metricInner_orthonormal_expansion (I := I) g horth v
  have hstep : (inner ℝ v w : ℝ)
      = ∑ i, g.metricInner q v (e i) * (inner ℝ (e i) w : ℝ) := by
    conv_lhs => rw [hv]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  refine hstep.trans (Finset.sum_congr rfl fun i _ => ?_)
  congr 1
  show (inner ℝ (e i) w : ℝ) = g.metricInner q w (e i)
  exact g.symm q _ _

/-! ### The coefficient vector of a field along `γ` -/

/-- **Math.** The **coefficient vector** of a field `V` along `γ`, in the
coefficient space: `frameVec V t = ∑ᵢ ⟨V t, Eᵢ(t)⟩_g • bᵢ`. -/
def frameVec (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (V : ℝ → E) (t : ℝ) : 𝔼 :=
  ∑ i, frameCoeff (I := I) g γ e V i t • (𝔟 i : 𝔼)

/-- `frameVec` as a pointwise sum of functions, the form the termwise
differentiation lemma `HasDerivAt.sum` produces. -/
theorem frameVec_eq_sumFun (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (V : ℝ → E) :
    frameVec (I := I) g γ e V
      = ∑ i, (fun s => frameCoeff (I := I) g γ e V i s • (𝔟 i : 𝔼)) := by
  funext s
  simp [frameVec, Finset.sum_apply]

/-- The coordinates of `frameVec` are the frame coefficients. -/
theorem inner_basisFun_frameVec (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (V : ℝ → E) (t : ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪(𝔟 i : 𝔼), frameVec (I := I) g γ e V t⟫
      = frameCoeff (I := I) g γ e V i t := by
  classical
  simp only [frameVec, inner_sum, real_inner_smul_right, basisFun_inner (E := E),
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Math.** **The coefficient map is a `g`-isometry.**  For fields `V, W` along
`γ` and a `g`-orthonormal frame,

`⟨V t, W t⟩_g = ⟨frameVec V t, frameVec W t⟩`.

Both sides are `∑ᵢ ⟨V, Eᵢ⟩ ⟨W, Eᵢ⟩`: on the left by Parseval for the frame
(`metricInner_parseval`), on the right by orthonormality of the standard basis of
the coefficient space.  Every metric quantity of a field along `γ` can therefore
be computed on its coefficient vector — which is where the ODE theory lives. -/
theorem metricInner_eq_inner_frameVec {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0)
    (V W : ℝ → E) :
    g.metricInner (γ t) (V t : TangentSpace I (γ t)) (W t)
      = ⟪frameVec (I := I) g γ e V t, frameVec (I := I) g γ e W t⟫ := by
  classical
  rw [metricInner_parseval (I := I) g (e := fun i => (e i t : TangentSpace I (γ t))) horth]
  simp only [frameVec, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    basisFun_inner (E := E), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, frameCoeff]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ### The Jacobi operator of the frame, as an operator on the coefficient space -/

/-- **Math.** The **Jacobi operator in the frame**: the operator on the
coefficient space whose matrix in the standard basis is `−frameCurv`,

`ℛ(t) = ∑ᵢⱼ (−ℛᵢⱼ(t)) • (⟨bⱼ, ·⟩ • bᵢ)`.

The sign: the frame system of `FrameJacobiSystem` is `c'' = frameCurv · c`, while
`IsJacobiSolOn` is stated as `y'' + R y = 0`; so `R = −frameCurv`, which is
Morgan–Tian's `⟨ℛ(Eⱼ, γ')γ', Eᵢ⟩`. -/
def frameCurvOp (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) : 𝔼 →L[ℝ] 𝔼 :=
  ∑ i, ∑ j, (-(frameCurv (I := I) g γ e i j t)) •
    ((innerSL ℝ (𝔟 j : 𝔼)).smulRight (𝔟 i : 𝔼))

theorem frameCurvOp_apply (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (x : 𝔼) :
    frameCurvOp (I := I) g γ e t x
      = ∑ i, (∑ j, (-(frameCurv (I := I) g γ e i j t)) * ⟪(𝔟 j : 𝔼), x⟫) • (𝔟 i : 𝔼) := by
  classical
  rw [frameCurvOp]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul, ← Finset.sum_smul]

/-- **Math.** The bilinear form of the frame Jacobi operator, in coordinates. -/
theorem inner_frameCurvOp_apply (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (x y : 𝔼) :
    ⟪frameCurvOp (I := I) g γ e t x, y⟫
      = ∑ i, ∑ j, (-(frameCurv (I := I) g γ e i j t))
          * ⟪(𝔟 j : 𝔼), x⟫ * ⟪(𝔟 i : 𝔼), y⟫ := by
  classical
  rw [frameCurvOp_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, Finset.sum_mul]

/-- **Math.** **The frame Jacobi operator is self-adjoint** — the `curv_symm`
field of `IsRadialJacobi`.  Its matrix `−frameCurv` is symmetric, by
self-adjointness of the Jacobi operator on the manifold (`frameCurv_symm`), i.e.
by the curvature symmetry `R_{ijkl} = R_{klij}`. -/
theorem frameCurvOp_symm (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (x y : 𝔼) :
    ⟪frameCurvOp (I := I) g γ e t x, y⟫ = ⟪x, frameCurvOp (I := I) g γ e t y⟫ := by
  classical
  rw [inner_frameCurvOp_apply, real_inner_comm, inner_frameCurvOp_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [frameCurv_symm (I := I) g γ e j i]
  ring

/-- **Math.** **Continuity of the frame Jacobi operator** — the `curv_cont` field
of `IsRadialJacobi`, and the last analytic input of the comparison chain.  The
operator is a finite sum of *fixed* rank-one operators with the curvature
coefficients as scalars, so it inherits the continuity of those coefficients
along the geodesic (`continuousOn_frameCurv`). -/
theorem continuousOn_frameCurvOp {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {a b : ℝ}
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ContinuousOn (frameCurvOp (I := I) g γ e) (Icc a b) := by
  classical
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  exact ((continuousOn_frameCurv hPar hgeo hγc i j).neg).smul continuousOn_const

/-! ### The Jacobi field, read in the frame, solves the abstract ODE -/

/-- The coefficient vector of a field vanishing at time `t` vanishes. -/
theorem frameVec_eq_zero {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {V : ℝ → E} {t : ℝ} (hV : V t = 0) :
    frameVec (I := I) g γ e V t = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hc : ∀ i, frameCoeff (I := I) g γ e V i t = 0 := by
    intro i
    show g.metricInner (γ t) (V t : TangentSpace I (γ t)) (e i t) = 0
    rw [show (V t : TangentSpace I (γ t)) = 0 from hV]
    show (inner ℝ (0 : TangentSpace I (γ t)) (e i t : TangentSpace I (γ t)) : ℝ) = 0
    exact inner_zero_left _
  simp [frameVec, hc]

/-- **Math.** **A Jacobi field along `γ`, read in the frame, solves the abstract
second-order ODE** `y'' + ℛ y = 0` on `[0, B]`, with `ℛ = frameCurvOp` the frame
Jacobi operator.

`FrameJacobiSystem` gives the two halves of the scalar system at *interior* times
of `[a, b]`, while `IsJacobiSolOn` asks for (one-sided) derivatives on the
*closed* interval `[0, B]`.  The gap is closed by requiring the geodesic and the
Jacobi field to be defined on a strictly larger interval, `a < 0` and `B < b` —
which is exactly the geometric situation (a radial geodesic extends a little past
the ball).  Then every `t ∈ [0, B]` is interior to `[a, b]`, the two-sided
`HasDerivAt` is available, and it restricts.

Assembling the scalar system into the coefficient vector uses only that the sum
`∑ᵢ cᵢ(t) • bᵢ` differentiates termwise, and that `frameCurvOp` acting on
`frameVec J` reproduces the curvature term `∑ⱼ ℛᵢⱼ cⱼ` — with the sign flip
`ℛ = −frameCurv` built into `frameCurvOp`. -/
theorem isJacobiSolOn_frameVec {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {J DJ : ℝ → E} {a b B : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (ha : a < 0) (hBb : B < b) :
    IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 B
      (frameVec (I := I) g γ e J) (frameVec (I := I) g γ e DJ) := by
  classical
  have hsub : ∀ t ∈ Icc (0 : ℝ) B, t ∈ Ioo a b := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hBb⟩
  constructor
  · -- `y' = v`: termwise, from `c i' = d i`
    intro t ht
    have hterm : ∀ i ∈ Finset.univ, HasDerivAt
        (fun s => frameCoeff (I := I) g γ e J i s • (𝔟 i : 𝔼))
        (frameCoeff (I := I) g γ e DJ i t • (𝔟 i : 𝔼)) t := fun i _ =>
      (hJac.hasDerivAt_frameCoeff_fst hPar hgeo hγc i (hsub t ht)).smul_const _
    rw [frameVec_eq_sumFun (I := I) g γ e J]
    exact (HasDerivAt.sum hterm).hasDerivWithinAt
  · -- `v' = −ℛ y`: termwise, from `d i' = ∑ⱼ ℛᵢⱼ cⱼ`, plus the sign flip
    intro t ht
    have hterm : ∀ i ∈ Finset.univ, HasDerivAt
        (fun s => frameCoeff (I := I) g γ e DJ i s • (𝔟 i : 𝔼))
        ((∑ j, frameCurv (I := I) g γ e i j t * frameCoeff (I := I) g γ e J j t)
          • (𝔟 i : 𝔼)) t := fun i _ =>
      (hJac.hasDerivAt_frameCoeff_snd hPar hgeo hγc horth i (hsub t ht)).smul_const _
    have hval : -(frameCurvOp (I := I) g γ e t) (frameVec (I := I) g γ e J t)
        = ∑ i, (∑ j, frameCurv (I := I) g γ e i j t
            * frameCoeff (I := I) g γ e J j t) • (𝔟 i : 𝔼) := by
      rw [frameCurvOp_apply]
      simp only [inner_basisFun_frameVec, neg_mul, neg_smul, neg_neg, Finset.sum_neg_distrib]
    rw [frameVec_eq_sumFun (I := I) g γ e DJ, hval]
    exact (HasDerivAt.sum hterm).hasDerivWithinAt

/-! ### The producer: a geodesic yields the radial Jacobi datum -/

/-- **Math.** **The radial Jacobi datum of a geodesic** — the theorem the whole
comparison chain was waiting for.

Along any geodesic `γ : [a, b] → M` (crossing arbitrarily many charts) and for
`0` and `B` interior to `[a, b]`, there are a parallel `g`-orthonormal frame `e`
and a matrix Jacobi field `(𝒥, 𝒥')` with `𝒥(0) = 0`, `𝒥'(0) = 1` solving
`𝒥'' + ℛ𝒥 = 0` for the frame Jacobi operator `ℛ = frameCurvOp`, i.e. an honest
`IsRadialJacobi ℛ 𝒥 𝒥' B C` — **and** every Jacobi field `J` along `γ` vanishing
at the centre is one of its columns:

`frameVec J t = 𝒥 t (frameVec ∇J 0)`   for `t ∈ [0, B]`.

The three inputs: `curv_symm` is the curvature symmetry `R_{ijkl} = R_{klij}`
(`frameCurvOp_symm`); `curv_cont` is `continuousOn_frameCurvOp` (the analytic
heart — the curvature coefficient is continuous along a chart-crossing geodesic);
`curv_bound` then comes free from compactness of `[0, B]`.  Existence of `𝒥` is
the linear-ODE existence `exists_isRadialJacobi`, and the column identity is ODE
uniqueness (`IsJacobiSolOn.eqOn_of_left`) applied to `frameVec J` and to the
column `𝒥 · (frameVec ∇J 0)` (`IsJacobiSolOn.apply`) — two solutions of the same
linear system with the same initial data `(0, frameVec ∇J 0)`.

Blueprint: `lem:geodesic-polar-form`(3), `lem:jacobi-frame-reduction`,
`lem:radial-shape-riccati`. -/
theorem exists_isRadialJacobi_of_geodesic {g : RiemannianMetric I M} {γ : ℝ → M}
    {a b B : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (ha : a < 0) (hB0 : 0 ≤ B) (hBb : B < b) :
    ∃ (e : Fin (Module.finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C
        ∧ ∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) B,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0) := by
  classical
  obtain ⟨e, hPar, horth⟩ := exists_orthonormalParallelFrameAlong (I := I) hab hgeo hγc
  have hIcc : Icc (0 : ℝ) B ⊆ Icc a b := Icc_subset_Icc ha.le hBb.le
  have hcont : ContinuousOn (frameCurvOp (I := I) g γ e) (Icc (0 : ℝ) B) :=
    (continuousOn_frameCurvOp hPar hgeo hγc).mono hIcc
  have hsymm : ∀ t ∈ Icc (0 : ℝ) B, ∀ X Y : 𝔼,
      ⟪frameCurvOp (I := I) g γ e t X, Y⟫ = ⟪X, frameCurvOp (I := I) g γ e t Y⟫ :=
    fun t _ X Y => frameCurvOp_symm (I := I) g γ e t X Y
  obtain ⟨𝒥, 𝒥', C, hRJ⟩ := exists_isRadialJacobi_of_continuousOn hB0 hsymm hcont
  refine ⟨e, 𝒥, 𝒥', C, hPar, horth, hRJ, fun J DJ hJac hJ0 => ?_⟩
  -- the two solutions of the same linear system with the same initial data
  set w : 𝔼 := frameVec (I := I) g γ e DJ 0 with hw
  have hsol₁ : IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 B
      (frameVec (I := I) g γ e J) (frameVec (I := I) g γ e DJ) :=
    isJacobiSolOn_frameVec hJac hPar hgeo hγc horth ha hBb
  have hsol₂ : IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 B
      (fun t => 𝒥 t w) (fun t => 𝒥' t w) := hRJ.sol.apply w
  have hy : frameVec (I := I) g γ e J 0 = 𝒥 0 w := by
    rw [frameVec_eq_zero hJ0, hRJ.fst_zero]
    simp
  have hv : frameVec (I := I) g γ e DJ 0 = 𝒥' 0 w := by
    rw [hRJ.snd_one]
    simp [hw]
  exact fun t ht => (IsJacobiSolOn.eqOn_of_left hcont hsol₁ hsol₂ hy hv).1 ht

/-! ### The curvature hypothesis, transported to the frame -/

/-- Parseval in the coefficient space. -/
theorem sum_inner_basisFun_mul (x y : 𝔼) :
    ∑ i, ⟪(𝔟 i : 𝔼), x⟫ * ⟪(𝔟 i : 𝔼), y⟫ = ⟪x, y⟫ :=
  Eq.trans
    (Finset.sum_congr rfl fun i _ => by rw [real_inner_comm x (𝔟 i : 𝔼)])
    ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).sum_inner_mul_inner x y)

/-- **Math.** Linearity of the curvature `(0,4)`-form in its **last** slot (with
equal middle slots), from linearity in the first slot and self-adjointness of the
Jacobi operator `ℛ(X, u, u, Y) = ℛ(Y, u, u, X)`. -/
theorem curvatureFormAt_sum_right (g : RiemannianMetric I M) (p : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I p)
    (x u : TangentSpace I p) :
    curvatureFormAt g g.leviCivitaConnection p x u u (∑ i ∈ s, c i • v i)
      = ∑ i ∈ s, c i * curvatureFormAt g g.leviCivitaConnection p x u u (v i) := by
  rw [curvatureFormAt_jacobi_symm (I := I) g p u x (∑ i ∈ s, c i • v i),
    curvatureFormAt_sum_left (I := I) g p s c v u u x]
  exact Finset.sum_congr rfl fun i _ => by
    rw [curvatureFormAt_jacobi_symm (I := I) g p u (v i) x]

/-- **Math.** The **lift** of a coefficient vector to a tangent vector at `γ t`:
`x ↦ ∑ᵢ xᵢ • Eᵢ(t)`.  It is the inverse of the coefficient map `frameVec`. -/
def frameLift (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (x : 𝔼) : TangentSpace I (γ t) :=
  ∑ i, ⟪(𝔟 i : 𝔼), x⟫ • (e i t : TangentSpace I (γ t))

/-- **Math.** The lift is a `g`-isometry of the coefficient space onto `T_{γt}M`:
`⟨lift x, lift y⟩_g = ⟨x, y⟩`, by orthonormality of the frame. -/
theorem metricInner_frameLift {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) (x y : 𝔼) :
    g.metricInner (γ t) (frameLift (I := I) g γ e t x) (frameLift (I := I) g γ e t y)
      = ⟪x, y⟫ := by
  classical
  show g.metricInner (γ t) (∑ i, ⟪(𝔟 i : 𝔼), x⟫ • (e i t : TangentSpace I (γ t)))
      (∑ i, ⟪(𝔟 i : 𝔼), y⟫ • (e i t : TangentSpace I (γ t))) = _
  have h1 : g.metricInner (γ t) (∑ i, ⟪(𝔟 i : 𝔼), x⟫ • (e i t : TangentSpace I (γ t)))
        (∑ i, ⟪(𝔟 i : 𝔼), y⟫ • (e i t : TangentSpace I (γ t)))
      = ∑ i, ⟪(𝔟 i : 𝔼), x⟫ * g.metricInner (γ t) (e i t : TangentSpace I (γ t))
          (∑ j, ⟪(𝔟 j : 𝔼), y⟫ • (e j t : TangentSpace I (γ t))) :=
    metricInner_sum_smul_left (I := I) g (γ t) Finset.univ (fun i => ⟪(𝔟 i : 𝔼), x⟫)
      (fun i => (e i t : TangentSpace I (γ t))) _
  have h2 : ∀ i, g.metricInner (γ t) (e i t : TangentSpace I (γ t))
        (∑ j, ⟪(𝔟 j : 𝔼), y⟫ • (e j t : TangentSpace I (γ t)))
      = ∑ j, ⟪(𝔟 j : 𝔼), y⟫
          * g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) := fun i =>
    metricInner_sum_smul_right (I := I) g (γ t) Finset.univ (fun j => ⟪(𝔟 j : 𝔼), y⟫)
      (e i t : TangentSpace I (γ t)) (fun j => (e j t : TangentSpace I (γ t)))
  rw [h1]
  simp only [h2, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact sum_inner_basisFun_mul (E := E) x y

/-- **Math.** **The quadratic form of the frame Jacobi operator is the curvature
form of the lifted vector**:

`⟨ℛ(t) x, x⟩ = −ℛ(X, γ', γ', X)`,  `X = lift x = ∑ᵢ xᵢ Eᵢ(t)`.

Bilinearity of the curvature form in its first and last slots
(`curvatureFormAt_sum_left`, `curvatureFormAt_sum_right`) is what collapses the
double sum over the frame into a single evaluation.  This is the dictionary that
turns a *geometric* curvature bound into the *algebraic* hypothesis
`−k‖x‖² ≤ ⟨ℛ x, x⟩` that `RadialComparison` consumes. -/
theorem inner_frameCurvOp_self (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (x : 𝔼) :
    ⟪frameCurvOp (I := I) g γ e t x, x⟫
      = - curvatureFormAt g g.leviCivitaConnection (γ t)
          (frameLift (I := I) g γ e t x)
          (mfderivVelocity (I := I) (E := E) γ t)
          (mfderivVelocity (I := I) (E := E) γ t)
          (frameLift (I := I) g γ e t x) := by
  classical
  -- expand the last slot (defeq: `frameLift` *is* the sum `∑ᵢ xᵢ • Eᵢ`)
  have h1 : curvatureFormAt g g.leviCivitaConnection (γ t)
        (frameLift (I := I) g γ e t x)
        (mfderivVelocity (I := I) (E := E) γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (frameLift (I := I) g γ e t x)
      = ∑ i, ⟪(𝔟 i : 𝔼), x⟫ * curvatureFormAt g g.leviCivitaConnection (γ t)
          (frameLift (I := I) g γ e t x)
          (mfderivVelocity (I := I) (E := E) γ t) (mfderivVelocity (I := I) (E := E) γ t)
          (e i t) :=
    curvatureFormAt_sum_right (I := I) g (γ t) Finset.univ (fun i => ⟪(𝔟 i : 𝔼), x⟫)
      (fun i => (e i t : TangentSpace I (γ t))) (frameLift (I := I) g γ e t x)
      (mfderivVelocity (I := I) (E := E) γ t)
  -- expand the first slot; the resulting coefficient is `frameCurv` by definition
  have h2 : ∀ i, curvatureFormAt g g.leviCivitaConnection (γ t)
        (frameLift (I := I) g γ e t x)
        (mfderivVelocity (I := I) (E := E) γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (e i t)
      = ∑ j, ⟪(𝔟 j : 𝔼), x⟫ * frameCurv (I := I) g γ e i j t := fun i =>
    curvatureFormAt_sum_left (I := I) g (γ t) Finset.univ (fun j => ⟪(𝔟 j : 𝔼), x⟫)
      (fun j => (e j t : TangentSpace I (γ t)))
      (mfderivVelocity (I := I) (E := E) γ t) (mfderivVelocity (I := I) (E := E) γ t) (e i t)
  rw [inner_frameCurvOp_apply, h1]
  simp only [h2, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Morgan–Tian's hypothesis `−k ≤ K(P)` gives the Jacobi-operator bound -/

section AlgBound

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** An algebraic curvature form vanishes on a degenerate pair:
`B(x,y,x,y) = 0` whenever `x, y` are linearly dependent.  (Extracted from the
degenerate branch of `alg_curvature_le_of_sectionalCurvature_le`, where it was
inlined; it is the half of that argument that has nothing to do with the
bound.) -/
theorem alg_curvature_self_eq_zero_of_not_linearIndependent
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) {x y : V}
    (hli : ¬ LinearIndependent ℝ ![x, y]) : B x y x y = 0 := by
  rw [linearIndependent_fin2] at hli
  push_neg at hli
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hli
  by_cases hy0 : y = 0
  · subst hy0
    have h1 : B x 0 x 0 = -B 0 x x 0 := hB.antisymm₁₂ x 0 x 0
    have h2 : B 0 x x 0 = 0 := by
      have h3 := hB.smul_left 0 (0 : V) x x 0
      simpa using h3
    rw [h1, h2, neg_zero]
  · obtain ⟨a, hxa⟩ := hli hy0
    subst hxa
    have hyy : B y y (a • y) y = 0 := by
      have h4 := hB.antisymm₁₂ y y (a • y) y
      linarith
    have h5 := hB.smul_left a y y (a • y) y
    rw [h5, hyy, mul_zero]

/-- **Math.** **Sectional lower bound ⇒ curvature-form lower bound**: if every
sectional curvature of an algebraic curvature form is `≥ −k`, then
`B(x,y,x,y) ≥ −k·|x ∧ y|²`.  The `≥` companion of
`alg_curvature_le_of_sectionalCurvature_le`: clear the (positive) denominator on
a genuine plane; both sides vanish on a degenerate pair. -/
theorem alg_curvature_ge_of_sectionalCurvature_ge
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) {k : ℝ}
    (hk : ∀ x y : V, -k ≤ Riemannian.sectionalCurvature B x y) (x y : V) :
    -(k * wedgeSq x y) ≤ B x y x y := by
  by_cases hli : LinearIndependent ℝ ![x, y]
  · have hw : 0 < wedgeSq x y := (wedgeSq_pos_iff_linearIndependent x y).mpr hli
    have h : -k ≤ B x y x y / wedgeSq x y := hk x y
    have h2 := mul_le_mul_of_nonneg_right h hw.le
    rw [div_mul_cancel₀ _ (ne_of_gt hw)] at h2
    linarith
  · rw [alg_curvature_self_eq_zero_of_not_linearIndependent hB hli,
      (by
        rcases lt_or_eq_of_le (wedgeSq_nonneg x y) with hlt | heq
        · exact absurd ((wedgeSq_pos_iff_linearIndependent x y).mp hlt) hli
        · exact heq.symm : wedgeSq x y = 0),
      mul_zero, neg_zero]

end AlgBound

/-- **Math.** **Morgan–Tian's hypothesis, converted.**  If every sectional
curvature at `p` is `≥ −k` (`k ≥ 0`) and `u` is a *unit* vector, then the Jacobi
operator `R_u = ℛ(·, u)u` is bounded above by `k`:

`ℛ(X, u, u, X) ≤ k ⟨X, X⟩_g`   for all `X ∈ T_pM`.

Two steps: antisymmetry in the last pair turns `ℛ(X,u,u,X)` into
`−ℛ(X,u,X,u)`, and `ℛ(X,u,X,u) ≥ −k |X ∧ u|²` is the sectional bound with the
denominator cleared (`alg_curvature_ge_of_sectionalCurvature_ge`); then
`|X ∧ u|² = ⟨X,X⟩⟨u,u⟩ − ⟨X,u⟩² ≤ ⟨X,X⟩` for unit `u`, using `k ≥ 0`.

This is exactly the hypothesis of `metricInner_jacobi_le_snK`, so the comparison
theorem may be stated with Morgan–Tian's own hypothesis `−k ≤ K(P)`. -/
theorem curvatureFormAt_jacobi_le_of_sectionalCurvatureAt_ge
    (g : RiemannianMetric I M) (p : M) {k : ℝ} (hk : 0 ≤ k)
    (hsec : ∀ v w : TangentSpace I p,
      -k ≤ sectionalCurvatureAt g g.leviCivitaConnection p v w)
    {u : TangentSpace I p} (hu : g.metricInner p u u = 1) (X : TangentSpace I p) :
    curvatureFormAt g g.leviCivitaConnection p X u u X ≤ k * g.metricInner p X X := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hLC : (g.leviCivitaConnection).IsLeviCivita g :=
    (g.leviCivitaConnection).isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  have hB : IsAlgCurvatureForm (curvatureFormAt g g.leviCivitaConnection p) :=
    isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p
  have h1 : curvatureFormAt g g.leviCivitaConnection p X u u X
      = - curvatureFormAt g g.leviCivitaConnection p X u X u := by
    have h := hB.antisymm₃₄ X u X u
    linarith
  have h2 : -(k * wedgeSq X u) ≤ curvatureFormAt g g.leviCivitaConnection p X u X u :=
    alg_curvature_ge_of_sectionalCurvature_ge hB (fun v w => hsec v w) X u
  have huu : (inner ℝ u u : ℝ) = 1 := hu
  have hXX : (inner ℝ X X : ℝ) = g.metricInner p X X := rfl
  have h3 : wedgeSq X u ≤ g.metricInner p X X := by
    have hsq : 0 ≤ (inner ℝ X u : ℝ) * (inner ℝ X u : ℝ) := mul_self_nonneg _
    show (inner ℝ X X : ℝ) * (inner ℝ u u : ℝ)
        - (inner ℝ X u : ℝ) * (inner ℝ X u : ℝ) ≤ g.metricInner p X X
    rw [huu, mul_one, hXX]
    linarith
  have h4 : 0 ≤ wedgeSq X u := wedgeSq_nonneg X u
  rw [h1]
  nlinarith [h2, h3, h4, hk]

/-! ### The sectional-curvature comparison, on the manifold -/

/-- **Math.** **The sectional-curvature comparison theorem, metric half**
(`thm:sectional-curvature-comparison`).  Let `γ` be a geodesic through `p = γ(0)`
and `J` a Jacobi field along it with `J(0) = 0` — i.e. the variation field of the
geodesic spray, whose norm *is* the metric `g_{ij}(r, θ)` in geodesic polar
coordinates.  Assume

* the Jacobi operator along `γ` is bounded above by `k ≥ 0`,
  `ℛ(X, γ', γ', X) ≤ k ⟨X, X⟩_g`, which is exactly what a sectional curvature
  bound `K(P) ≥ −k` gives for a unit-speed geodesic; and
* `γ` has no conjugate point of `p` before `r₀` (the matrix Jacobi field `𝒥` is
  invertible on `(0, r₀)`), so geodesic polar coordinates are valid there.

Then

`|J(r)|_g ≤ sn_k(r) · |∇J(0)|_g`  for `0 < r < r₀`,

i.e. `g_{ij}(r, θ) ≤ sn_k²(r)`: the metric grows no faster than in the constant
curvature `−k` model.  This is Morgan–Tian's first conclusion in `SCC`.

The proof is the abstract Riccati comparison `RadialComparison.norm_jacobi_sq_le`,
transported through the frame: the coefficient map is a `g`-isometry
(`metricInner_eq_inner_frameVec`), `J` is the column `𝒥 · (∇J(0))` of the matrix
Jacobi field (`exists_isRadialJacobi_of_geodesic`), and the curvature hypothesis
converts by `inner_frameCurvOp_self`.

Blueprint: `thm:sectional-curvature-comparison`, `lem:radial-comparison`. -/
theorem metricInner_jacobi_le_snK {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {J DJ : ℝ → E}
    {𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼} {a b B C k r₀ : ℝ}
    (hRJ : IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C) (hB : 0 < B)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hIcc : Icc (0 : ℝ) B ⊆ Icc a b)
    (hid : ∀ t ∈ Icc (0 : ℝ) B,
      frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
    (hk : 0 ≤ k) (hr₀ : r₀ ≤ B)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hcurv : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : TangentSpace I (γ r),
      curvatureFormAt g g.leviCivitaConnection (γ r) X
          (mfderivVelocity (I := I) (E := E) γ r)
          (mfderivVelocity (I := I) (E := E) γ r) X
        ≤ k * g.metricInner (γ r) X X) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      g.metricInner (γ r) (J r : TangentSpace I (γ r)) (J r)
        ≤ snK k r ^ 2 * g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0) := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne _))
  haveI : Nontrivial 𝔼 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin (Module.finrank ℝ E))›
    refine nontrivial_of_ne (𝔟 i : 𝔼) 0 fun h => ?_
    have h1 : ‖(𝔟 i : 𝔼)‖ = 1 :=
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).orthonormal.1 i
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  -- the curvature hypothesis, in the frame
  have hcurv' : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ x : 𝔼,
      -(k * ‖x‖ ^ 2) ≤ ⟪frameCurvOp (I := I) g γ e r x, x⟫ := by
    intro r hr x
    have hrIcc : r ∈ Icc (0 : ℝ) B := ⟨hr.1.le, hr.2.le.trans hr₀⟩
    have hnorm : g.metricInner (γ r) (frameLift (I := I) g γ e r x)
        (frameLift (I := I) g γ e r x) = ‖x‖ ^ 2 := by
      rw [metricInner_frameLift (I := I) (horth r (hIcc hrIcc)) x x,
        real_inner_self_eq_norm_sq]
    rw [inner_frameCurvOp_self (I := I) g γ e r x, neg_le_neg_iff, ← hnorm]
    exact hcurv r hr _
  -- the abstract comparison, applied to the column `w = ∇J(0)`
  set w : 𝔼 := frameVec (I := I) g γ e DJ 0 with hw
  have hcomp := norm_jacobi_sq_le hRJ hB hk hr₀ hunit hcurv' w
  intro r hr
  have hrIcc : r ∈ Icc (0 : ℝ) B := ⟨hr.1.le, hr.2.le.trans hr₀⟩
  have h0Icc : (0 : ℝ) ∈ Icc (0 : ℝ) B := ⟨le_rfl, hB.le⟩
  -- transport both sides through the frame isometry
  have hJr : g.metricInner (γ r) (J r : TangentSpace I (γ r)) (J r) = ‖𝒥 r w‖ ^ 2 := by
    rw [metricInner_eq_inner_frameVec (I := I) (horth r (hIcc hrIcc)) J J,
      real_inner_self_eq_norm_sq, hid r hrIcc]
  have hDJ0 : g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0) = ‖w‖ ^ 2 := by
    rw [metricInner_eq_inner_frameVec (I := I) (horth 0 (hIcc h0Icc)) DJ DJ,
      real_inner_self_eq_norm_sq]
  rw [hJr, hDJ0]
  exact hcomp r hr

/-- **Math.** **The sectional-curvature comparison theorem with Morgan–Tian's own
hypothesis** (`thm:sectional-curvature-comparison`, metric half).  Fix `k ≥ 0`
and let `γ` be a **unit-speed** geodesic with `γ(0) = p`, along which every
sectional curvature satisfies `−k ≤ K(P)` and which has no conjugate point of `p`
before `r₀`.  Then every Jacobi field `J` along `γ` vanishing at `p` satisfies

`|J(r)|²_g ≤ sn_k²(r) · |∇J(0)|²_g`   for `0 < r < r₀`.

Since (by the Gauss Lemma) the coordinate fields `∂_{θⁱ}` of geodesic polar
coordinates restrict to exactly such Jacobi fields, this is Morgan–Tian's
`g_{ij}(r, θ) ≤ sn_k²(r)`.

This is `metricInner_jacobi_le_snK` with the hypothesis discharged by
`curvatureFormAt_jacobi_le_of_sectionalCurvatureAt_ge`.

Blueprint: `thm:sectional-curvature-comparison`. -/
theorem metricInner_jacobi_le_snK_of_sectionalCurvature {g : RiemannianMetric I M}
    {γ : ℝ → M} {e : Fin (Module.finrank ℝ E) → ℝ → E} {J DJ : ℝ → E}
    {𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼} {a b B C k r₀ : ℝ}
    (hRJ : IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' B C) (hB : 0 < B)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hIcc : Icc (0 : ℝ) B ⊆ Icc a b)
    (hid : ∀ t ∈ Icc (0 : ℝ) B,
      frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
    (hk : 0 ≤ k) (hr₀ : r₀ ≤ B)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hspeed : ∀ r ∈ Ioo (0 : ℝ) r₀,
      g.metricInner (γ r) (mfderivVelocity (I := I) (E := E) γ r)
        (mfderivVelocity (I := I) (E := E) γ r) = 1)
    (hsec : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ v w : TangentSpace I (γ r),
      -k ≤ sectionalCurvatureAt g g.leviCivitaConnection (γ r) v w) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      g.metricInner (γ r) (J r : TangentSpace I (γ r)) (J r)
        ≤ snK k r ^ 2 * g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0) :=
  metricInner_jacobi_le_snK hRJ hB horth hIcc hid hk hr₀ hunit
    (fun r hr X => curvatureFormAt_jacobi_le_of_sectionalCurvatureAt_ge (I := I) g (γ r) hk
      (hsec r hr) (hspeed r hr) X)

end PoincareLib

end
