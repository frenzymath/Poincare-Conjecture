import PoincareLib.Ch01.IndexFormConjugate
import PoincareLib.Ch01.ParallelIsometry

/-!
# Poincaré Ch. 1 — the dictionary between frame coordinates and fields along `γ`

`FrameRadialBridge` reads a field `V` along a geodesic `γ` in a parallel
`g`-orthonormal frame `e₁, …, eₙ`, producing its coefficient vector
`frameVec V t ∈ 𝔼 = EuclideanSpace ℝ (Fin n)`, and it reads the Jacobi operator
`ℛ(·, γ′)γ′` as the operator `frameCurvOp` on `𝔼`.  Half 1 of
`prop:minimal-geodesic-no-conjugate` (`IndexFormConjugate`) therefore delivers its
negative direction as a *pair of coefficient functions* `(W, DW) : ℝ → 𝔼`, whose
index is the abstract `indexForm (frameCurvOp g γ e) 0 1 W DW W DW`.

Half 2 (a minimizing geodesic has nonnegative index) will instead produce an
honest **field along `γ`**, through the second variation of energy.  This file is
the dictionary in the direction the two halves must be glued:

* `frameLift_frameVec` / `frameVec_frameLift_apply` — the coefficient map
  `frameVec` and the lift `frameLift` are mutually inverse (`frameLift ∘ frameVec
  = id` on fields, `frameVec ∘ frameLift = id` on coefficients);
* `indexIntegrand_frameVec` — **the core**: the *metric* index integrand of a
  field `V` with covariant derivative `DV`,

  `⟨∇V, ∇V⟩_g + ℛ(V, γ′, γ′, V)`

  (Morgan–Tian's `⟨∇_X Y, ∇_X Y⟩ − ⟨ℛ(Y, X)X, Y⟩`; the sign is the one of
  `frameCurv`, cf. `inner_frameCurvOp_self`) *is* the abstract integrand
  `indexIntegrand (frameCurvOp g γ e)` of the coefficient functions;
* `frameCurvOp_selfAdjoint` — the `hR` hypothesis of `IndexForm`
  (`exists_indexForm_neg` and friends), in the exact shape they ask for;
* `hasDerivWithinAt_frameVec_frameLift` and
  `hasDerivWithinAt_metricInner_frameLift_parallel` — the derivative dictionary:
  in a **parallel** frame, the field `V = ∑ᵢ Wᵢ eᵢ` has coefficient functions `W`
  (so `d/dt` of the coefficients is `DW`), and the field `DV = ∑ᵢ (DW)ᵢ eᵢ` is its
  covariant derivative in the only sense the workspace makes available at the
  manifold level, namely the first-order identity
  `d/dt ⟨V, P⟩_g = ⟨DV, P⟩_g` against every parallel field `P`.

Blueprint: `claim:second-variation-minimal-geodesic`, `prop:minimal-geodesic-no-conjugate`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3–§1.4.
-/

open Set Riemannian Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-! ### The two round trips -/

/-- **Math.** **The lift undoes the coefficient map.**  For a `g`-orthonormal frame
`e₁, …, eₙ` at `γ t` and any field `V` along `γ`,

`∑ᵢ ⟨V t, Eᵢ(t)⟩_g Eᵢ(t) = V t`,

i.e. `frameLift t (frameVec V t) = V t`.  This is the orthonormal expansion
`metricInner_orthonormal_expansion` (the frame is `n = dim M` orthonormal vectors,
hence a basis), read through `inner_basisFun_frameVec`, which says the coordinates
of `frameVec V t` are exactly the frame coefficients `⟨V t, Eᵢ(t)⟩_g`. -/
theorem frameLift_frameVec {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) (V : ℝ → E) :
    frameLift (I := I) g γ e t (frameVec (I := I) g γ e V t)
      = (V t : TangentSpace I (γ t)) := by
  classical
  show ∑ i, ⟪(𝔟 i : 𝔼), frameVec (I := I) g γ e V t⟫ • (e i t : TangentSpace I (γ t)) = _
  simp only [inner_basisFun_frameVec, frameCoeff]
  exact (metricInner_orthonormal_expansion (I := I) g
    (e := fun i => (e i t : TangentSpace I (γ t))) horth (V t)).symm

/-- **Math.** **The coefficient map undoes the lift.**  The frame coordinates of the
field `t ↦ ∑ᵢ Wᵢ(t) Eᵢ(t)` are `W` itself: `frameVec (frameLift ∘ W) t = W t`.
Immediate from `frameVec_frameLift`. -/
theorem frameVec_frameLift_apply {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) (W : ℝ → 𝔼) :
    frameVec (I := I) g γ e (fun u => frameLift (I := I) g γ e u (W u)) t = W t :=
  frameVec_frameLift (I := I) horth (W t) _ rfl

/-! ### The index integrand, on the manifold and in the frame -/

/-- **Math.** **The metric index integrand is the frame index integrand.**  Let `V`
be a field along the geodesic `γ` with covariant derivative `DV`, both read in a
`g`-orthonormal frame at time `t`.  Then Morgan–Tian's integrand

`⟨∇_X V, ∇_X V⟩_g − ⟨ℛ(V, X)X, V⟩_g = ⟨DV, DV⟩_g + ℛ(V, γ′, γ′, V)`

(the second form is the first: `frameCurv` — hence `curvatureFormAt … V γ′ γ′ V` —
is Morgan–Tian's `−⟨ℛ(V, γ′)γ′, V⟩`, see the sign discussion in `FrameRadialBridge`)
equals the **abstract** index integrand of the coefficient functions,

`indexIntegrand (frameCurvOp g γ e) (frameVec V) (frameVec DV) (frameVec V) (frameVec DV) t`.

Two ingredients, and nothing else: the coefficient map is a `g`-isometry
(`metricInner_eq_inner_frameVec`), which handles the kinetic term; and the
quadratic form of `frameCurvOp` is minus the curvature form of the lifted vector
(`inner_frameCurvOp_self`), which — since the lift undoes the coefficient map
(`frameLift_frameVec`) — is minus the curvature form of `V t` itself.

This is the dictionary that lets the two halves of
`prop:minimal-geodesic-no-conjugate` be compared: half 1 produces a *coefficient*
pair of strictly negative abstract index, half 2 will produce a *field* of
nonnegative metric index, and by this identity they are the same number. -/
theorem indexIntegrand_frameVec {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {V DV : ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) :
    g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        + curvatureFormAt g g.leviCivitaConnection (γ t) (V t : TangentSpace I (γ t))
            (mfderivVelocity (I := I) (E := E) γ t)
            (mfderivVelocity (I := I) (E := E) γ t) (V t)
      = indexIntegrand (frameCurvOp (I := I) g γ e)
          (frameVec (I := I) g γ e V) (frameVec (I := I) g γ e DV)
          (frameVec (I := I) g γ e V) (frameVec (I := I) g γ e DV) t := by
  classical
  have hcurv : ⟪frameCurvOp (I := I) g γ e t (frameVec (I := I) g γ e V t),
        frameVec (I := I) g γ e V t⟫
      = - curvatureFormAt g g.leviCivitaConnection (γ t) (V t : TangentSpace I (γ t))
          (mfderivVelocity (I := I) (E := E) γ t)
          (mfderivVelocity (I := I) (E := E) γ t) (V t) := by
    rw [inner_frameCurvOp_self (I := I) g γ e t (frameVec (I := I) g γ e V t),
      frameLift_frameVec (I := I) horth V]
  rw [indexIntegrand, hcurv, ← metricInner_eq_inner_frameVec (I := I) horth DV DV]
  ring

/-! ### Self-adjointness, in the shape the index-form lemmas want -/

/-- **Math.** **The frame Jacobi operator is self-adjoint**, in the exact shape of
the hypothesis `hR` of `IndexForm` (`indexForm_symm`, `indexForm_add_smul`,
`exists_indexForm_neg`): `⟨ℛ(t) x, x'⟩ = ⟨x, ℛ(t) x'⟩` for all `t` and all `x, x'`.
This is the curvature symmetry `R_{ijkl} = R_{klij}`; it is `frameCurvOp_symm` with
the arguments reordered. -/
theorem frameCurvOp_selfAdjoint (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) :
    ∀ t : ℝ, ∀ x x' : 𝔼,
      ⟪frameCurvOp (I := I) g γ e t x, x'⟫ = ⟪x, frameCurvOp (I := I) g γ e t x'⟫ :=
  fun t x x' => frameCurvOp_symm (I := I) g γ e t x x'

/-! ### The derivative dictionary in a parallel frame -/

/-- **Math.** **The frame coordinates of a lifted field differentiate to the
derivative of the coordinates.**  If `W : ℝ → 𝔼` has derivative `dw` at `t` within
`[a, b]`, then the field `V = ∑ᵢ Wᵢ Eᵢ` has coefficient functions `frameVec V = W`
on `[a, b]` (`frameVec_frameLift_apply`), so `frameVec V` has the same derivative
`dw`.  (No parallelism is needed for *this* statement — only orthonormality of the
frame at each time; parallelism enters in
`hasDerivWithinAt_metricInner_frameLift_parallel`, which is what makes `∑ᵢ (DW)ᵢ Eᵢ`
the *covariant* derivative of `V`.) -/
theorem hasDerivWithinAt_frameVec_frameLift {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {W : ℝ → 𝔼} {dw : 𝔼} {a b t : ℝ}
    (horth : ∀ s ∈ Icc a b, ∀ i j,
      g.metricInner (γ s) (e i s : TangentSpace I (γ s)) (e j s) = if i = j then 1 else 0)
    (ht : t ∈ Icc a b) (hW : HasDerivWithinAt W dw (Icc a b) t) :
    HasDerivWithinAt (frameVec (I := I) g γ e (fun u => frameLift (I := I) g γ e u (W u)))
      dw (Icc a b) t :=
  hW.congr (fun s hs => frameVec_frameLift_apply (I := I) (horth s hs) W)
    (frameVec_frameLift_apply (I := I) (horth t ht) W)

/-- **Math.** **The covariant derivative of a lifted field, in a parallel frame.**
Let `e` be a **parallel** `g`-orthonormal frame along the geodesic `γ`, let
`W : ℝ → 𝔼` be differentiable at `t ∈ [a, b]` with derivative `dw`, and put

`V(s) = ∑ᵢ Wᵢ(s) Eᵢ(s)`,  `DV(t) = ∑ᵢ (dw)ᵢ Eᵢ(t)`.

Then, for every field `P` parallel along `γ`,

`d/dt ⟨V, P⟩_g = ⟨DV(t), P(t)⟩_g`.

This is the defining first-order property of the covariant derivative (compare
`IsJacobiFieldAlongOn.hasDerivAt_metricInner_parallel`, which is the same identity
for a Jacobi pair): it says that `∑ᵢ (dw)ᵢ Eᵢ` *is* `∇_{γ′} V` at `t`, in the only
sense available at the manifold level in this development.

Proof.  Expand `⟨V(s), P(s)⟩_g = ∑ᵢ Wᵢ(s) ⟨Eᵢ(s), P(s)⟩_g`
(`metricInner_sum_smul_left`).  Each pairing `⟨Eᵢ, P⟩_g` of two parallel fields is
**constant** on `[a, b]` (`IsParallelAlongOn.metricInner_eq` — parallel transport is
an isometry).  So the function is `s ↦ ∑ᵢ Wᵢ(s) cᵢ`, a fixed linear functional of
`W(s)`, whose derivative is `∑ᵢ (dw)ᵢ cᵢ = ⟨DV(t), P(t)⟩_g`. -/
theorem hasDerivWithinAt_metricInner_frameLift_parallel {g : RiemannianMetric I M}
    {γ : ℝ → M} {e : Fin (Module.finrank ℝ E) → ℝ → E} {P : ℝ → E} {W : ℝ → 𝔼} {dw : 𝔼}
    {a b t : ℝ}
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hP : IsParallelAlongOn (I := I) g γ P a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ s ∈ Icc a b, ContinuousAt γ s)
    (ht : t ∈ Icc a b) (hW : HasDerivWithinAt W dw (Icc a b) t) :
    HasDerivWithinAt
      (fun s => g.metricInner (γ s)
        (frameLift (I := I) g γ e s (W s)) (P s) : ℝ → ℝ)
      (g.metricInner (γ t) (frameLift (I := I) g γ e t dw) (P t)) (Icc a b) t := by
  classical
  -- the constants `cᵢ = ⟨Eᵢ, P⟩_g`
  set c : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    g.metricInner (γ a) (e i a : TangentSpace I (γ a)) (P a) with hc
  have hconst : ∀ s ∈ Icc a b, ∀ i,
      g.metricInner (γ s) (e i s : TangentSpace I (γ s)) (P s) = c i := fun s hs i =>
    (hPar i).metricInner_eq hP hgeo hγc s hs
  -- the expansion `⟨V s, P s⟩_g = ∑ᵢ ⟪bᵢ, W s⟫ cᵢ`, valid on `[a, b]`
  have hexp : ∀ s ∈ Icc a b,
      g.metricInner (γ s) (frameLift (I := I) g γ e s (W s)) (P s)
        = ∑ i, ⟪(𝔟 i : 𝔼), W s⟫ * c i := by
    intro s hs
    have h1 : g.metricInner (γ s) (frameLift (I := I) g γ e s (W s)) (P s)
        = ∑ i, ⟪(𝔟 i : 𝔼), W s⟫
            * g.metricInner (γ s) (e i s : TangentSpace I (γ s)) (P s) :=
      metricInner_sum_smul_left (I := I) g (γ s) Finset.univ
        (fun i => ⟪(𝔟 i : 𝔼), W s⟫) (fun i => (e i s : TangentSpace I (γ s))) (P s)
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hconst s hs i]
  -- the value at `t` of the derivative, in the same coordinates
  have hval : g.metricInner (γ t) (frameLift (I := I) g γ e t dw) (P t)
      = ∑ i, ⟪(𝔟 i : 𝔼), dw⟫ * c i := by
    have h1 : g.metricInner (γ t) (frameLift (I := I) g γ e t dw) (P t)
        = ∑ i, ⟪(𝔟 i : 𝔼), dw⟫
            * g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (P t) :=
      metricInner_sum_smul_left (I := I) g (γ t) Finset.univ
        (fun i => ⟪(𝔟 i : 𝔼), dw⟫) (fun i => (e i t : TangentSpace I (γ t))) (P t)
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hconst t ht i]
  -- the coordinate function `s ↦ ∑ᵢ ⟪bᵢ, W s⟫ cᵢ` is a fixed continuous linear
  -- functional of `W s`, so it differentiates by the chain rule
  have hlin : HasDerivWithinAt (fun s => ∑ i, ⟪(𝔟 i : 𝔼), W s⟫ * c i)
      (∑ i, ⟪(𝔟 i : 𝔼), dw⟫ * c i) (Icc a b) t := by
    refine HasDerivWithinAt.fun_sum fun i _ => ?_
    have h : HasDerivWithinAt (fun s => (⟪(𝔟 i : 𝔼), W s⟫ : ℝ))
        (⟪(𝔟 i : 𝔼), dw⟫ : ℝ) (Icc a b) t := by
      simpa using (hasDerivWithinAt_const t (Icc a b) (𝔟 i : 𝔼)).inner ℝ hW
    exact h.mul_const (c i)
  rw [hval]
  exact hlin.congr (fun s hs => hexp s hs) (hexp t ht)

end PoincareLib

end
