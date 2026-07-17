import PoincareLib.Ch01.FrameCurvatureBridge
import PoincareLib.Ch01.ParallelIsometry
import PoincareLib.Ch01.OrthoFrame

/-!
# Poincaré Ch. 1, §1.4 — the Jacobi equation as a closed scalar system

`FrameJacobi` and `FrameCurvatureBridge` prove the two halves of the scalar
Jacobi equation at the **manifold** level, against a field `V` parallel along a
geodesic `γ` that may cross arbitrarily many charts:

* `d/dt ⟨J, V⟩_g = ⟨∇J, V⟩_g`                     (curvature-free half)
* `d/dt ⟨∇J, V⟩_g = ℛ(J, γ', γ', V)`              (curvature half)

Individually these still refer to the *manifold* vector `J(t) ∈ T_{γ t}M`, so
they are not yet an ODE.  This file closes the system.  Feeding in a **parallel
`g`-orthonormal frame** `E₁, …, Eₙ` along `γ` (`exists_parallelFrameAlong`: the
Gram matrix of a parallel family is constant, so orthonormality at `γ a`
propagates), and writing

`c i t = ⟨J t, Eᵢ t⟩_g`,   `d i t = ⟨∇J t, Eᵢ t⟩_g`,

the two halves become

`c i' = d i`,   `d i' = ∑ j, ℛᵢⱼ(t) · c j`,   `ℛᵢⱼ(t) = ℛ(Eⱼ, γ', γ', Eᵢ)(t)`,

a genuine **closed linear second-order system** `c'' = ℛ c` in the coefficients
alone — the scalar form of `∇²J + ℛ(J, γ')γ' = 0`, and the shape consumed by
`IsRadialJacobi`.

The step that closes it is the orthonormal expansion `J = ∑ j ⟨J, Eⱼ⟩ Eⱼ`
(`metricInner_orthonormal_expansion`) together with linearity of the curvature
`(0,4)`-form in its first slot (`IsAlgCurvatureForm.sum_left`), which is what
turns the *vector* `J` in the curvature slot into its *coefficients*.

Main results:

* `metricInner_orthonormal_expansion` — the manifold-level orthonormal
  expansion, for an arbitrary `g`-orthonormal family (`OrthoFrame` has this only
  for the one bundled frame `orthoFrameField`);
* `curvatureFormAt_jacobi_symm` — **self-adjointness of the Jacobi operator on
  the manifold**, `ℛ(X, u, u, Y) = ℛ(Y, u, u, X)`.  `JacobiOperator` proves this
  only for *chart* vectors; the intrinsic statement is what `IsRadialJacobi`'s
  `curv_symm` field actually wants;
* `IsJacobiFieldAlongOn.hasDerivAt_frameCoeff_fst` / `_snd` — **the closed
  scalar Jacobi system**;
* `frameCurv_symm` — the coefficient matrix `ℛᵢⱼ` is symmetric.

Blueprint: `lem:geodesic-polar-form`(2,3), `lem:jacobi-frame-reduction`,
`lem:jacobi-operator-symmetric`, `lem:parallel-frame`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Filter Riemannian Riemannian.Tensor
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The manifold-level orthonormal expansion -/

/-- **Math.** A `g`-orthonormal family at `q` is an `Orthonormal` family for the
fibre inner product installed by `Bundle.RiemannianBundle ⟨g.toRiemannianMetric⟩`
— which is definitionally `g.metricInner q`. -/
theorem metricInner_orthonormal_family (g : RiemannianMetric I M) {q : M}
    {e : Fin (Module.finrank ℝ E) → TangentSpace I q}
    (horth : ∀ i j, g.metricInner q (e i) (e j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Orthonormal ℝ e := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [orthonormal_iff_ite]
  intro i j
  exact horth i j

/-- **Math.** **Orthonormal expansion, on the manifold.**  For *any*
`g`-orthonormal family `e₁, …, eₙ` of `T_qM` (`n = dim M`), every tangent vector
is the sum of its coordinates:

`v = ∑ i ⟨v, eᵢ⟩_g • eᵢ`.

`OrthoFrame.orthoFrameField_expansion` is this statement for the single bundled
frame `orthoFrameField`; here the family is arbitrary, which is what lets us feed
in a **parallel** frame along a geodesic.  An orthonormal family of `dim M`
vectors is automatically a basis, and in an orthonormal basis the coordinates of
`v` are its inner products.

Note the statement needs no `RiemannianBundle` instance: it mentions only `+` and
`•` on `T_qM`.  The instance is introduced inside the proof, where the
`Orthonormal`/`OrthonormalBasis` API lives. -/
theorem metricInner_orthonormal_expansion (g : RiemannianMetric I M) {q : M}
    {e : Fin (Module.finrank ℝ E) → TangentSpace I q}
    (horth : ∀ i j, g.metricInner q (e i) (e j) = if i = j then 1 else 0)
    (v : TangentSpace I q) :
    v = ∑ i, g.metricInner q v (e i) • e i := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hOrth : Orthonormal ℝ e := metricInner_orthonormal_family (I := I) g horth
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I q) := Fintype.card_fin _
  -- the family is an orthonormal basis of `T_qM`
  let bas : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I q) :=
    (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis (by
      rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hOrth)
  have hbas : ∀ i, bas i = e i := by
    intro i
    show (basisOfOrthonormalOfCardEqFinrank hOrth hcard).toOrthonormalBasis _ i = e i
    rw [Module.Basis.coe_toOrthonormalBasis]
    exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank hOrth hcard) i
  have h := bas.sum_repr' v
  simp only [hbas] at h
  refine h.symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  show inner ℝ (e i) v = g.metricInner q v (e i)
  exact g.symm q _ _

/-! ### Self-adjointness of the Jacobi operator, intrinsically -/

section SelfAdjoint

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **The Jacobi operator is self-adjoint, on the manifold.**  For
tangent vectors `X, Y, u ∈ T_pM`,

`ℛ(X, u, u, Y) = ℛ(Y, u, u, X)`,

i.e. `⟨R_u(X), Y⟩_g = ⟨X, R_u(Y)⟩_g` for `R_u(X) = ℛ(X, u)u`.

`JacobiOperator.chartCurvature_inner_symm` proves this for *chart* vectors, by
first pushing through the chart bridge; the argument there in fact establishes
the intrinsic statement en route (its `hswap` step) and then converts back.  This
is that intrinsic core, extracted: no chart is involved, so it applies directly to
a frame along a geodesic that leaves every chart — which is the situation
`IsRadialJacobi`'s `curv_symm` field is stated in.

It is Morgan–Tian's pair symmetry `R_{ijkl} = R_{klij}` combined with
antisymmetry in the last pair:
`ℛ(X,u,u,Y) = -ℛ(X,u,Y,u) = -ℛ(Y,u,X,u) = ℛ(Y,u,u,X)`.

Blueprint: `claim:curvature-symmetries-bianchi`, `lem:jacobi-operator-symmetric`,
`lem:geodesic-polar-form`(2). -/
theorem curvatureFormAt_jacobi_symm (g : RiemannianMetric I M) (p : M)
    (u X Y : TangentSpace I p) :
    curvatureFormAt g g.leviCivitaConnection p X u u Y
      = curvatureFormAt g g.leviCivitaConnection p Y u u X := by
  classical
  set nabla := g.leviCivitaConnection with hnabla
  have hLC : nabla.IsLeviCivita g :=
    nabla.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB : IsAlgCurvatureForm (curvatureFormAt g nabla p) :=
    isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  have h1 : curvatureFormAt g nabla p X u u Y
      = - curvatureFormAt g nabla p X u Y u := hB.antisymm₃₄ X u u Y
  have h2 : curvatureFormAt g nabla p X u Y u
      = curvatureFormAt g nabla p Y u X u := hB.pairSwap X u Y u
  have h3 : curvatureFormAt g nabla p Y u u X
      = - curvatureFormAt g nabla p Y u X u := hB.antisymm₃₄ Y u u X
  rw [h1, h2, ← h3]

/-- **Math.** Linearity of the curvature `(0,4)`-form in its first slot, in the
finite-sum form needed to replace a vector by its frame coordinates:
`ℛ(∑ i cᵢ • vᵢ, y, z, t) = ∑ i cᵢ · ℛ(vᵢ, y, z, t)`. -/
theorem curvatureFormAt_sum_left (g : RiemannianMetric I M) (p : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I p)
    (y z w : TangentSpace I p) :
    curvatureFormAt g g.leviCivitaConnection p (∑ i ∈ s, c i • v i) y z w
      = ∑ i ∈ s, c i * curvatureFormAt g g.leviCivitaConnection p (v i) y z w := by
  classical
  set nabla := g.leviCivitaConnection with hnabla
  have hLC : nabla.IsLeviCivita g :=
    nabla.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB : IsAlgCurvatureForm (curvatureFormAt g nabla p) :=
    isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  exact hB.sum_left s c v y z w

end SelfAdjoint

/-! ### The closed scalar Jacobi system -/

section System

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **A parallel orthonormal frame exists along any geodesic.**  Along a
geodesic `γ : [a,b] → M` — which may cross arbitrarily many charts — there is a
family `E₁, …, Eₙ` of fields parallel along `γ` that is `g`-orthonormal at *every*
`γ t`.

Take any orthonormal basis of `(T_{γ a}M, g)` (`stdOrthonormalBasis`, using the
fibre inner product `Bundle.RiemannianBundle ⟨g.toRiemannianMetric⟩`, which is
definitionally `g.metricInner`) and parallel-transport it
(`exists_parallelFrameAlong`).  Parallel transport is a `g`-isometry — the Gram
matrix of a parallel family is constant along `γ` — so orthonormality at the
initial point propagates to every time.

This discharges the frame hypotheses of `hasDerivAt_frameCoeff_fst/_snd`, making
the scalar Jacobi system available along *any* geodesic with no side conditions.

Blueprint: `lem:parallel-frame`, `lem:geodesic-polar-form`(3). -/
theorem exists_orthonormalParallelFrameAlong
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ∃ e : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
        ∧ ∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
              = if i = j then 1 else 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  -- an orthonormal basis of the initial tangent space `(T_{γ a}M, g)`
  let bas : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I (γ a)) :=
    stdOrthonormalBasis ℝ (TangentSpace I (γ a))
  have h0 : ∀ i j, g.metricInner (γ a) (bas i : TangentSpace I (γ a)) (bas j)
      = if i = j then 1 else 0:= by
    intro i j
    exact orthonormal_iff_ite.mp bas.orthonormal i j
  -- parallel-transport it along `γ`; the Gram matrix stays constant
  obtain ⟨e, hinit, hpar, hgram⟩ :=
    exists_parallelFrameAlong (I := I) hab hgeo hγc (fun i => (bas i : TangentSpace I (γ a)))
  refine ⟨e, hpar, fun t ht i j => ?_⟩
  rw [hgram i j t ht]
  exact h0 i j

/-- **Math.** The `i`-th coordinate of a field `V` along `γ` in the frame `e`:
`c i t = ⟨V t, eᵢ t⟩_g`. -/
def frameCoeff (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (V : ℝ → E)
    (i : Fin (Module.finrank ℝ E)) (t : ℝ) : ℝ :=
  g.metricInner (γ t) (V t : TangentSpace I (γ t)) (e i t)

/-- **Math.** The coefficient matrix of the Jacobi operator in the frame `e`:
`ℛᵢⱼ(t) = ℛ(eⱼ, γ', γ', eᵢ)(t)`.  (In Morgan–Tian's sign convention this is
`-⟨R(eⱼ, γ')γ', eᵢ⟩`, so the scalar system reads `c'' = ℛ c`.) -/
def frameCurv (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) : ℝ :=
  curvatureFormAt g g.leviCivitaConnection (γ t) (e j t)
    (mfderivVelocity (I := I) (E := E) γ t) (mfderivVelocity (I := I) (E := E) γ t) (e i t)

/-- **Math.** The coefficient matrix `ℛᵢⱼ` is **symmetric**, by self-adjointness
of the Jacobi operator (`curvatureFormAt_jacobi_symm`).  This is the `curv_symm`
hypothesis of `IsRadialJacobi`, read in the frame. -/
theorem frameCurv_symm (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (i j : Fin (Module.finrank ℝ E)) (t : ℝ) :
    frameCurv (I := I) g γ e i j t = frameCurv (I := I) g γ e j i t :=
  curvatureFormAt_jacobi_symm (I := I) g (γ t) _ (e j t) (e i t)

/-- **Math.** **First half of the scalar system**: `c i' = d i`, i.e. the
coordinate of `J` differentiates to the coordinate of `∇J`, because the frame is
parallel.  This is `IsJacobiFieldAlongOn.hasDerivAt_metricInner_parallel` read in
the frame. -/
theorem IsJacobiFieldAlongOn.hasDerivAt_frameCoeff_fst
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    {e : Fin (Module.finrank ℝ E) → ℝ → E}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (i : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (frameCoeff (I := I) g γ e J i)
      (frameCoeff (I := I) g γ e DJ i t) t :=
  hJac.hasDerivAt_metricInner_parallel (hPar i) hgeo hγc ht

/-- **Math.** **Second half of the scalar system, and the step that closes it**:

`d i'(t) = ∑ j, ℛᵢⱼ(t) · c j(t)`.

`FrameCurvatureBridge` gives `d i' = ℛ(J, γ', γ', eᵢ)`, whose first slot still
holds the *manifold vector* `J(t)`.  Expanding `J(t) = ∑ j ⟨J, eⱼ⟩ • eⱼ` in the
orthonormal frame (`metricInner_orthonormal_expansion`) and using linearity of the
curvature form in that slot (`curvatureFormAt_sum_left`) replaces `J` by its
coordinates, leaving a closed linear system in `c` alone.

Together with `hasDerivAt_frameCoeff_fst` this is `c'' = ℛ c`: the scalar form of
the Jacobi equation `∇²J + ℛ(J, γ')γ' = 0` along a geodesic that may cross
arbitrarily many charts.

Blueprint: `lem:geodesic-polar-form`(3), `lem:jacobi-frame-reduction`. -/
theorem IsJacobiFieldAlongOn.hasDerivAt_frameCoeff_snd
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    {e : Fin (Module.finrank ℝ E) → ℝ → E}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (i : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (frameCoeff (I := I) g γ e DJ i)
      (∑ j, frameCurv (I := I) g γ e i j t * frameCoeff (I := I) g γ e J j t) t := by
  classical
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  -- the curvature half of the Jacobi equation, at the manifold level
  have hbridge := hJac.hasDerivAt_metricInner_snd_parallel (hPar i) hgeo hγc ht
  -- expand `J t` in the (orthonormal) frame at time `t`
  have hexp : (J t : TangentSpace I (γ t))
      = ∑ j, g.metricInner (γ t) (J t : TangentSpace I (γ t)) (e j t) • e j t :=
    metricInner_orthonormal_expansion (I := I) g (horth t htI) (J t)
  -- replace the vector `J t` in the curvature slot by its coordinates
  have hval : curvatureFormAt g g.leviCivitaConnection (γ t)
        (J t : TangentSpace I (γ t))
        (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) (e i t)
      = ∑ j, frameCurv (I := I) g γ e i j t * frameCoeff (I := I) g γ e J j t := by
    -- `congrArg` on `hexp` produces the expanded sum *exactly* as `hexp` states it,
    -- and `Eq.trans` then only needs definitional (not syntactic) agreement — which
    -- `rw` would demand and fail on, the `•` elaborating at `E` on one side and at
    -- `TangentSpace I (γ t)` on the other.
    refine (congrArg (fun w : TangentSpace I (γ t) =>
      curvatureFormAt g g.leviCivitaConnection (γ t) w
        (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) (e i t)) hexp).trans ?_
    refine (curvatureFormAt_sum_left (I := I) g (γ t) Finset.univ
      (fun j => g.metricInner (γ t) (J t : TangentSpace I (γ t)) (e j t))
      (fun j => (e j t : TangentSpace I (γ t)))
      (mfderivVelocity (I := I) (E := E) γ t)
      (mfderivVelocity (I := I) (E := E) γ t) (e i t)).trans ?_
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [← hval]
  exact hbridge

/-- **Math.** **The Jacobi equation along a geodesic is a closed linear scalar
system** (`lem:geodesic-polar-form`(3), frame form).  Along *any* geodesic
`γ : [a,b] → M` — crossing arbitrarily many charts — there is a parallel
`g`-orthonormal frame `E₁, …, Eₙ` in which every Jacobi field `J` has coordinates
`c i = ⟨J, Eᵢ⟩`, `d i = ⟨∇J, Eᵢ⟩` satisfying, at interior times,

`c i' = d i`,   `d i' = ∑ j, ℛᵢⱼ · c j`,   `ℛᵢⱼ = ℛ(Eⱼ, γ', γ', Eᵢ)`  symmetric,

i.e. `c'' = ℛ c`: the Jacobi equation `∇²J + ℛ(J, γ')γ' = 0` has become an ODE in
the coordinates alone, with no manifold vectors and no charts left in it.  This is
the statement the matrix theory of `IsRadialJacobi` consumes (there `𝒥` is the
matrix whose columns are these coordinate vectors).

Blueprint: `lem:geodesic-polar-form`(3), `lem:jacobi-frame-reduction`. -/
theorem IsJacobiFieldAlongOn.exists_frameJacobiSystem
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b) (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ∃ e : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
              = if i = j then 1 else 0)
        ∧ (∀ i j t, frameCurv (I := I) g γ e i j t = frameCurv (I := I) g γ e j i t)
        ∧ (∀ i, ∀ t ∈ Ioo a b,
            HasDerivAt (frameCoeff (I := I) g γ e J i)
              (frameCoeff (I := I) g γ e DJ i t) t)
        ∧ ∀ i, ∀ t ∈ Ioo a b,
            HasDerivAt (frameCoeff (I := I) g γ e DJ i)
              (∑ j, frameCurv (I := I) g γ e i j t
                * frameCoeff (I := I) g γ e J j t) t := by
  obtain ⟨e, hpar, horth⟩ := exists_orthonormalParallelFrameAlong (I := I) hab hgeo hγc
  exact ⟨e, hpar, horth, fun i j t => frameCurv_symm (I := I) g γ e i j t,
    fun i t ht => hJac.hasDerivAt_frameCoeff_fst hpar hgeo hγc i ht,
    fun i t ht => hJac.hasDerivAt_frameCoeff_snd hpar hgeo hγc horth i ht⟩

end System

end PoincareLib

end
