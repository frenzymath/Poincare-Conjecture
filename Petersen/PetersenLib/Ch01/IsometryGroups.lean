import PetersenLib.Ch01.RiemannianManifolds
import PetersenLib.Ch01.Sphere
import PetersenLib.Ch01.HyperbolicSpace
import PetersenLib.Ch01.ArcLength
import PetersenLib.Ch01.Exercises2
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Petersen Ch. 1, §1.3.1 — Isometry groups

The isometry group `Iso(M, g)` of a Riemannian manifold, realized as a
subgroup of the permutation group `Equiv.Perm M` (`IsometryGroup`), the
isotropy (stabilizer) subgroup at a point (`IsotropyGroup`), homogeneity
(`IsHomogeneous`), and Petersen's Examples 1.3.1–1.3.3 describing the
Riemannian isometries of Euclidean space
(`isometryGroup_euclideanSpace`), of the sphere (`isometryGroup_sphere`),
and of hyperbolic space (`isometryGroup_hyperbolicSpace`, together with
the Lorentz/Minkowski groups `minkowskiIsometryGroup` = `O(n₁, n₂)` and
`orthochronousMinkowskiGroup` = `O⁺(n, 1)`, the hyperbolic translations
`hyperbolicTranslation`, and homogeneity
`isHomogeneous_hyperbolicSpace`).

The subgroup axioms carry the mathematical content of the definition:
* composition of Riemannian isometries is a Riemannian isometry — the chain
  rule `mfderiv_comp` composes the differentials, so the pullback identities
  chain (`IsRiemannianIsometry.comp`);
* the inverse of a Riemannian isometry is a Riemannian isometry — the
  differential of `F⁻¹` at `p` is inverse to the differential of `F` at
  `F⁻¹ p`, so the metric identity transports back
  (`IsRiemannianIsometry.perm_inv`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.3.1.
-/

open Bundle Metric Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' ∞ M'']

/-! ## Closure of Riemannian isometries under composition and inverse -/

/-- **Math.** Petersen §1.3.1: the composition of Riemannian isometries is a
Riemannian isometry. The underlying diffeomorphisms compose, and by the chain
rule `D(G ∘ F)_p = DG_{F(p)} ∘ DF_p`, so the two pullback identities chain:
`g_M(u, v) = g_N(DF u, DF v) = g_P(DG (DF u), DG (DF v))`. -/
theorem IsRiemannianIsometry.comp {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {gP : RiemannianMetric I'' M''}
    {G : M' → M''} {F : M → M'} (hG : IsRiemannianIsometry gN gP G)
    (hF : IsRiemannianIsometry gM gN F) :
    IsRiemannianIsometry gM gP (G ∘ F) := by
  obtain ⟨⟨ΦF, hΦF⟩, hFpres⟩ := hF
  obtain ⟨⟨ΦG, hΦG⟩, hGpres⟩ := hG
  have hFd : MDifferentiable I I' F := by
    rw [← hΦF]; exact ΦF.mdifferentiable (by simp)
  have hGd : MDifferentiable I' I'' G := by
    rw [← hΦG]; exact ΦG.mdifferentiable (by simp)
  refine ⟨⟨ΦF.trans ΦG, by rw [Diffeomorph.coe_trans, hΦG, hΦF]⟩, fun p u v => ?_⟩
  have hcomp : mfderiv I I'' (G ∘ F) p
      = (mfderiv I' I'' G (F p)).comp (mfderiv I I' F p) :=
    mfderiv_comp p (hGd (F p)) (hFd p)
  rw [hcomp]
  exact (hFpres p u v).trans (hGpres (F p) _ _)

/-- **Math.** Petersen §1.3.1: the inverse of a Riemannian isometry
`F : (M, g) → (M, g)` (a self-isometry, viewed as a permutation of `M`) is
again a Riemannian isometry. The underlying diffeomorphism inverts, and since
`DF_{F⁻¹(p)} ∘ D(F⁻¹)_p = D(F ∘ F⁻¹)_p = id` by the chain rule, applying the
pullback identity of `F` at `F⁻¹(p)` to the vectors `D(F⁻¹)u, D(F⁻¹)v` gives
`g(D(F⁻¹)u, D(F⁻¹)v) = g(u, v)`. -/
theorem IsRiemannianIsometry.perm_inv {g : RiemannianMetric I M}
    {F : Equiv.Perm M} (h : IsRiemannianIsometry g g ⇑F) :
    IsRiemannianIsometry g g ⇑F⁻¹ := by
  obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := h
  have hFd : MDifferentiable I I ⇑F := by
    rw [← hΦ]; exact Φ.mdifferentiable (by simp)
  have hsymm_eq : ⇑F⁻¹ = ⇑Φ.symm := by
    funext x
    rw [Equiv.Perm.coe_inv, Equiv.symm_apply_eq, ← hΦ, Φ.apply_symm_apply]
  have hFinvd : MDifferentiable I I ⇑F⁻¹ := by
    rw [hsymm_eq]; exact Φ.symm.mdifferentiable (by simp)
  refine ⟨⟨Φ.symm, hsymm_eq.symm⟩, fun p u v => ?_⟩
  -- The differentials of `F` at `F⁻¹ p` and of `F⁻¹` at `p` cancel.
  have hid : (⇑F ∘ ⇑F⁻¹ : M → M) = id := by
    funext x; simp
  have hcomp : mfderiv I I (⇑F ∘ ⇑F⁻¹) p
      = (mfderiv I I ⇑F (F⁻¹ p)).comp (mfderiv I I ⇑F⁻¹ p) :=
    mfderiv_comp p (hFd (F⁻¹ p)) (hFinvd p)
  have hcancel : ∀ w : TangentSpace I p,
      mfderiv I I ⇑F (F⁻¹ p) (mfderiv I I ⇑F⁻¹ p w) = w := by
    intro w
    have h1 : ((mfderiv I I ⇑F (F⁻¹ p)).comp (mfderiv I I ⇑F⁻¹ p)) w = w := by
      rw [← hcomp, hid, mfderiv_id]; rfl
    exact h1
  -- Transport the metric along the point identity `F (F⁻¹ p) = p`.
  have hpoint : ∀ {x y : M}, x = y → ∀ a b : E,
      g.metricInner x a b = g.metricInner y a b := by
    rintro x y rfl a b; rfl
  have hq : F (F⁻¹ p) = p := by simp
  have key := hpres (F⁻¹ p) (mfderiv I I ⇑F⁻¹ p u) (mfderiv I I ⇑F⁻¹ p v)
  rw [key, hcancel u, hcancel v]
  exact hpoint hq.symm u v

/-! ## The isometry group, isotropy groups, and homogeneity
(Petersen §1.3.1) -/

/-- **Math.** Petersen §1.3.1: the **isometry group** `Iso(M, g)` of a
Riemannian manifold `(M, g)`: the subgroup of the permutation group of `M`
consisting of the Riemannian isometries `F : (M, g) → (M, g)`. Closure under
composition is the chain rule (`IsRiemannianIsometry.comp`); closure under
inverse is `IsRiemannianIsometry.perm_inv`; the identity is an isometry. -/
def IsometryGroup (g : RiemannianMetric I M) : Subgroup (Equiv.Perm M) where
  carrier := {F : Equiv.Perm M | IsRiemannianIsometry g g ⇑F}
  one_mem' := by
    show IsRiemannianIsometry g g ⇑(1 : Equiv.Perm M)
    rw [Equiv.Perm.coe_one]
    exact isRiemannianIsometry_id g
  mul_mem' := by
    intro F G hF hG
    have hF' : IsRiemannianIsometry g g ⇑F := hF
    have hG' : IsRiemannianIsometry g g ⇑G := hG
    show IsRiemannianIsometry g g ⇑(F * G)
    rw [Equiv.Perm.coe_mul]
    exact hF'.comp hG'
  inv_mem' := by
    intro F hF
    have hF' : IsRiemannianIsometry g g ⇑F := hF
    show IsRiemannianIsometry g g ⇑F⁻¹
    exact hF'.perm_inv

@[simp]
theorem mem_isometryGroup {g : RiemannianMetric I M} {F : Equiv.Perm M} :
    F ∈ IsometryGroup g ↔ IsRiemannianIsometry g g ⇑F :=
  Iff.rfl

/-- **Math.** Petersen §1.3.1: the **isotropy group** (or **stabilizer**)
`Iso_p(M, g)` at `p ∈ M`: the subgroup of `Iso(M, g)` of isometries fixing
`p`. Realized, like `IsometryGroup`, as a subgroup of `Equiv.Perm M`. -/
def IsotropyGroup (g : RiemannianMetric I M) (p : M) : Subgroup (Equiv.Perm M) where
  carrier := {F : Equiv.Perm M | F ∈ IsometryGroup g ∧ F p = p}
  one_mem' := ⟨(IsometryGroup g).one_mem, rfl⟩
  mul_mem' := by
    intro F G hF hG
    exact ⟨(IsometryGroup g).mul_mem hF.1 hG.1,
      by rw [Equiv.Perm.mul_apply, hG.2, hF.2]⟩
  inv_mem' := by
    intro F hF
    refine ⟨(IsometryGroup g).inv_mem hF.1, ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hF.2.symm

@[simp]
theorem mem_isotropyGroup {g : RiemannianMetric I M} {p : M} {F : Equiv.Perm M} :
    F ∈ IsotropyGroup g p ↔ F ∈ IsometryGroup g ∧ F p = p :=
  Iff.rfl

/-- **Math.** Petersen §1.3.1: the isotropy group at any point is a subgroup
of the isometry group. -/
theorem isotropyGroup_le_isometryGroup (g : RiemannianMetric I M) (p : M) :
    IsotropyGroup g p ≤ IsometryGroup g :=
  fun _ hF => hF.1

/-- **Math.** Petersen §1.3.1: `(M, g)` is **homogeneous** if its isometry
group acts transitively on `M`: for all `p, q ∈ M` there is an isometry `F`
with `F p = q`. -/
def IsHomogeneous (g : RiemannianMetric I M) : Prop :=
  ∀ p q : M, ∃ F ∈ IsometryGroup g, F p = q

/-! ## Example 1.3.1: isometries of Euclidean space -/

section Translation

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** Petersen Example 1.3.1 (ingredient): translation `x ↦ v + x` of
an inner product space, as a smooth diffeomorphism with inverse
`x ↦ -v + x`. -/
def translationDiffeomorph (v : V) : V ≃ₘ⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V where
  toFun x := v + x
  invFun x := -v + x
  left_inv x := neg_add_cancel_left v x
  right_inv x := add_neg_cancel_left v x
  contMDiff_toFun := contMDiff_iff_contDiff.mpr (contDiff_const.add contDiff_id)
  contMDiff_invFun := contMDiff_iff_contDiff.mpr (contDiff_const.add contDiff_id)

/-- **Math.** Petersen Example 1.3.1 (ingredient): translations are Riemannian
isometries of an inner product space with its canonical metric — the
differential of `x ↦ v + x` at every point is the identity. -/
theorem translation_isRiemannianIsometry (v : V) :
    IsRiemannianIsometry (innerProductSpaceMetric V) (innerProductSpaceMetric V)
      (fun x => v + x) := by
  refine ⟨⟨translationDiffeomorph V v, rfl⟩, fun p u w => ?_⟩
  have hmf : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (fun x => v + x) p
      = ContinuousLinearMap.id ℝ V := by
    have hd : HasFDerivAt (fun x : V => v + x) (ContinuousLinearMap.id ℝ V) p :=
      (hasFDerivAt_id p).const_add v
    rw [mfderiv_eq_fderiv]
    exact hd.fderiv
  rw [hmf]
  simp only [innerProductSpaceMetric_apply]
  rfl

end Translation

/-- **Math.** Petersen Example 1.3.1: the isometry group of Euclidean space
is `Iso(ℝⁿ, g_eu) = ℝⁿ ⋊ O(n)`: a permutation `F` of `ℝⁿ` is a Riemannian
isometry iff it has the form `F(x) = v + O x` for a translation vector
`v ∈ ℝⁿ` and an orthogonal transformation `O ∈ O(n)` (a linear isometry).

The "if" direction is proved by composing the translation isometry with the
linear-isometry isometry. Petersen proves the "only if" direction from the
uniqueness principle for Riemannian isometries (Prop. 5.6.2, a Chapter 5
result); we instead give an elementary Chapter-1 proof through arc length
and the Mazur–Ulam theorem: a Riemannian isometry preserves the length of
curves (Exercise 1.6.17), and since straight segments realize the Euclidean
distance while every curve dominates it (Exercise 1.6.19), `F` and `F⁻¹`
are distance-nonincreasing, so `F` is a metric isometry; by Mazur–Ulam a
surjective distance-preserving self-map of a normed space is affine,
`F(x) = F(0) + O(x)` with `O` a linear isometry. -/
theorem isometryGroup_euclideanSpace {n : ℕ} (F : Equiv.Perm (EuclideanSpace ℝ (Fin n))) :
    F ∈ IsometryGroup (euclideanMetric n) ↔
      ∃ (v : EuclideanSpace ℝ (Fin n))
        (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
        ∀ x, F x = v + O x := by
  constructor
  · intro hF
    -- Any Riemannian isometry of Euclidean space is distance-nonincreasing:
    -- the image of the segment from `x` to `y` is a curve from `G x` to `G y`
    -- of length `dist x y`.
    have key : ∀ G : Equiv.Perm (EuclideanSpace ℝ (Fin n)),
        G ∈ IsometryGroup (euclideanMetric n) →
        ∀ x y : EuclideanSpace ℝ (Fin n), dist (G x) (G y) ≤ dist x y := by
      intro G hG x y
      have hG' : IsRiemannianIsometry (euclideanMetric n) (euclideanMetric n)
        ⇑G := hG
      obtain ⟨Φ, hΦ⟩ := hG'.1
      have hGsmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ⇑G := by
        rw [← hΦ]
        exact Φ.contMDiff
      -- the segment from `x` to `y`
      set c : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • (y - x) with hc_def
      have hc : ContDiff ℝ ∞ c := contDiff_const.add (contDiff_id.smul contDiff_const)
      have hc0 : c 0 = x := by simp [hc_def]
      have hc1 : c 1 = y := by simp [hc_def]
      have hcM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ c :=
        contMDiff_iff_contDiff.mpr hc
      have hGc : ContDiff ℝ ∞ (⇑G ∘ c) :=
        contMDiff_iff_contDiff.mp (hGsmooth.comp hcM)
      -- the segment has length `dist x y`
      have hderiv : ∀ t : ℝ, deriv c t = y - x := by
        intro t
        have hd : HasDerivAt (fun s : ℝ => x + s • (y - x)) ((1 : ℝ) • (y - x)) t :=
          ((hasDerivAt_id t).smul_const (y - x)).const_add x
        rw [one_smul] at hd
        exact hd.deriv
      have hlen : arcLength (euclideanMetric n) c 0 1 = dist x y := by
        show arcLength
          (innerProductSpaceMetric (EuclideanSpace ℝ (Fin n))) c 0 1 = dist x y
        rw [arcLength_eq_integral_norm_deriv, dist_eq_norm, norm_sub_rev]
        simp [hderiv]
      -- distance ≤ length of the image curve = length of the segment
      have h1 : dist (G x) (G y) ≤ arcLength (euclideanMetric n) (⇑G ∘ c) 0 1 := by
        have h := dist_le_arcLength (F := EuclideanSpace ℝ (Fin n)) hGc zero_le_one
        simpa [Function.comp, hc0, hc1] using h
      have h2 : arcLength (euclideanMetric n) (⇑G ∘ c) 0 1
          = arcLength (euclideanMetric n) c 0 1 :=
        hG'.preservesMetric.arcLength (hGsmooth.mdifferentiable (by simp))
          (hcM.mdifferentiable (by simp)) 0 1
      calc dist (G x) (G y) ≤ arcLength (euclideanMetric n) (⇑G ∘ c) 0 1 := h1
        _ = arcLength (euclideanMetric n) c 0 1 := h2
        _ = dist x y := hlen
    -- `F` and `F⁻¹` are both distance-nonincreasing, so `F` is an isometry
    have hdist : ∀ x y : EuclideanSpace ℝ (Fin n), dist (F x) (F y) = dist x y := by
      intro x y
      refine le_antisymm (key F hF x y) ?_
      have h := key F⁻¹ ((IsometryGroup (euclideanMetric n)).inv_mem hF) (F x) (F y)
      simpa using h
    -- Mazur–Ulam: a surjective metric isometry of a normed space is affine
    set e : EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n) :=
      { toEquiv := F, isometry_toFun := Isometry.of_dist_eq hdist } with he_def
    refine ⟨F 0, e.toRealLinearIsometryEquiv, fun x => ?_⟩
    have h := e.toRealLinearIsometryEquiv_apply x
    rw [h]
    show F x = F 0 + (e x - e 0)
    simp [he_def]
  · rintro ⟨v, O, hFvO⟩
    have hcoe : ⇑F = (fun x => v + x) ∘ ⇑O := funext fun x => by
      simp [hFvO x]
    have hiso : IsRiemannianIsometry (euclideanMetric n) (euclideanMetric n)
        ((fun x => v + x) ∘ ⇑O) :=
      (translation_isRiemannianIsometry _ v).comp
        (linearIsometryEquiv_isRiemannianIsometry O)
    show IsRiemannianIsometry (euclideanMetric n) (euclideanMetric n) ⇑F
    rw [hcoe]
    exact hiso

/-! ## Example 1.3.2: isometries of the sphere -/

section SphereIsometries

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n + 1)]

/-- **Math.** Petersen Example 1.3.2 (ingredient): tangent vectors to the
sphere are orthogonal to the position vector — the ambient image `Dι(u)` of
any tangent vector `u ∈ T_x Sⁿ(R)` lies in `x^⊥`. This is the "first column
is orthogonal to the others" step of Petersen's argument for
`Iso(Sⁿ(R)) = O(n+1)`: the function `‖·‖²` is constant (`= R²`) on the
sphere, so its derivative `2⟪x, Dι(u)⟫` along any tangent vector
vanishes. -/
theorem inner_coe_mfderiv_coe_sphere (r : ℝ) [Fact (0 < r)] (x : sphere (0 : V) r)
    (u : TangentSpace (𝓡 n) x) :
    ⟪(x : V), mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x u⟫ = 0 := by
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x :=
    (contMDiff_coe_sphere_radius (m := 1) r x).mdifferentiableAt one_ne_zero
  have hg : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (fun y : V => ‖y‖ ^ 2) ((x : V)) :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (hasStrictFDerivAt_norm_sq (x : V)).hasFDerivAt.differentiableAt
  -- chain rule for `‖·‖² ∘ ι`
  have hcomp := mfderiv_comp x hg hι
  -- but `‖·‖² ∘ ι` is constant on the sphere
  have hconst : ((fun y : V => ‖y‖ ^ 2) ∘ ((↑) : sphere (0 : V) r → V))
      = fun _ => r ^ 2 := by
    funext p
    simp only [Function.comp_apply, mem_sphere_zero_iff_norm.mp p.2]
  have hzero : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      ((fun y : V => ‖y‖ ^ 2) ∘ ((↑) : sphere (0 : V) r → V)) x u = 0 := by
    rw [hconst, mfderiv_const]
    simp
  have hfd : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (fun y : V => ‖y‖ ^ 2) ((x : V))
      = 2 • innerSL ℝ (x : V) := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_norm_sq_apply (x : V)
  have happ : (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (fun y : V => ‖y‖ ^ 2) ((x : V)))
      ((mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x) u) = 0 := by
    rw [← ContinuousLinearMap.comp_apply, ← hcomp]
    exact hzero
  rw [hfd] at happ
  -- re-read the identity at the plain ambient types (`TangentSpace` is defeq)
  have happ2 : (2 • innerSL ℝ (x : V))
      (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x u : V) = 0 := happ
  have h2 : (2 : ℝ)
      * ⟪(x : V), mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x u⟫ = 0 := by
    simpa using happ2
  linarith

/-- **Math.** Petersen Example 1.3.2 (ingredient): a map of the sphere
`Sⁿ(R) → Sⁿ(R)` that is the restriction of an ambient linear isometry
`O ∈ O(n+1)` is smooth. The rescaled map `x ↦ R⁻¹ • O(x)` takes values in
the unit sphere, is smooth into it by `ContMDiff.codRestrict_sphere`, and
scaling back by `R` (`sphereHomeomorphUnitSphere`) recovers `f`. -/
theorem contMDiff_restrict_sphere_of_linearIsometryEquiv {r : ℝ} [Fact (0 < r)]
    (O : V ≃ₗᵢ[ℝ] V) {f : sphere (0 : V) r → sphere (0 : V) r}
    (hf : ∀ x : sphere (0 : V) r, (f x : V) = O x) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ f := by
  have hr : (0 : ℝ) < r := Fact.out
  have hmem : ∀ x : sphere (0 : V) r, r⁻¹ • O (x : V) ∈ sphere (0 : V) 1 := by
    intro x
    rw [mem_sphere_zero_iff_norm, norm_smul, O.norm_map, mem_sphere_zero_iff_norm.mp x.2,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, V) ∞ fun x : sphere (0 : V) r => r⁻¹ • O (x : V) := by
    have hO : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) ∞
        ⇑(r⁻¹ • (O.toContinuousLinearEquiv : V →L[ℝ] V)) :=
      ContinuousLinearMap.contMDiff _
    exact (hO.comp (contMDiff_coe_sphere_radius r)).congr fun x => by simp
  have hG : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Set.codRestrict _ (sphere (0 : V) 1) hmem) :=
    hsmooth.codRestrict_sphere hmem
  have hfun : f = ⇑(sphereHomeomorphUnitSphere r).symm
      ∘ Set.codRestrict _ (sphere (0 : V) 1) hmem := by
    funext x
    refine Subtype.ext ?_
    show (f x : V) = r • (r⁻¹ • O (x : V))
    rw [hf x, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [hfun]
  exact (contMDiff_sphereHomeomorphUnitSphere_symm r).comp hG

/-- **Math.** Petersen Example 1.3.2 (ingredient): if a smooth self-map `f`
of `Sⁿ(R)` is the restriction of an ambient linear isometry `O`, then the
ambient image of its differential is computed by `O`:
`Dι_{f(x)}(Df_x(u)) = O(Dι_x(u))` — the chain rule applied to the two
factorizations of `ι ∘ f = O ∘ ι`. -/
theorem mfderiv_coe_sphere_restrict_of_linearIsometryEquiv {r : ℝ} [Fact (0 < r)]
    (O : V ≃ₗᵢ[ℝ] V) {f : sphere (0 : V) r → sphere (0 : V) r}
    (hsmooth : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hf : ∀ x : sphere (0 : V) r, (f x : V) = O x) (x : sphere (0 : V) r)
    (u : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x u)
      = O (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x u) := by
  set OL : V →L[ℝ] V := (O.toContinuousLinearEquiv : V →L[ℝ] V) with hOL
  have hι : ∀ y : sphere (0 : V) r,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) y := fun y =>
    (contMDiff_coe_sphere_radius (m := 1) r y).mdifferentiableAt one_ne_zero
  have hfd : MDifferentiableAt (𝓡 n) (𝓡 n) f x :=
    (hsmooth x).mdifferentiableAt (by simp)
  have hOd : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V) ⇑OL ((x : V)) :=
    (ContinuousLinearMap.contMDiff (n := 1) OL).mdifferentiableAt one_ne_zero
  have heq : (((↑) : sphere (0 : V) r → V) ∘ f) = ⇑OL ∘ ((↑) : sphere (0 : V) r → V) := by
    funext y
    simp [hf y, hOL]
  have h1 : mfderiv (𝓡 n) 𝓘(ℝ, V) (((↑) : sphere (0 : V) r → V) ∘ f) x
      = (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) (f x)).comp
          (mfderiv (𝓡 n) (𝓡 n) f x) :=
    mfderiv_comp x (hι (f x)) hfd
  have h2 : mfderiv (𝓡 n) 𝓘(ℝ, V) (⇑OL ∘ ((↑) : sphere (0 : V) r → V)) x
      = (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) ⇑OL ((x : V))).comp
          (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x) :=
    mfderiv_comp x hOd (hι x)
  have hOm : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) ⇑OL ((x : V)) = OL := by
    rw [mfderiv_eq_fderiv]
    exact ContinuousLinearMap.fderiv OL
  have hcomp : (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) (f x)).comp
        (mfderiv (𝓡 n) (𝓡 n) f x)
      = OL.comp (mfderiv (𝓡 n) 𝓘(ℝ, V) ((↑) : sphere (0 : V) r → V) x) := by
    rw [← h1, heq, h2, hOm]
  have := congrArg (fun T : TangentSpace (𝓡 n) x →L[ℝ] V => T u) hcomp
  simpa [hOL] using this

/-- **Math.** Petersen Example 1.3.2, the fully proved "⊇" direction, as a
standalone sorry-free lemma: the restriction to `Sⁿ(R)` of an orthogonal
transformation `O ∈ O(n+1)` is a Riemannian isometry of
`(Sⁿ(R), g_{Sⁿ(R)})`. The restriction is smooth
(`contMDiff_restrict_sphere_of_linearIsometryEquiv`, likewise for the
inverse permutation via `O⁻¹`), hence a diffeomorphism of the sphere; and
since `Dι ∘ DF = O ∘ Dι`
(`mfderiv_coe_sphere_restrict_of_linearIsometryEquiv`) and the sphere
carries the metric induced from the ambient space, `O` preserving the
ambient inner product forces `F` to preserve `g_{Sⁿ(R)}`. -/
theorem mem_isometryGroup_sphere_of_linearIsometryEquiv {r : ℝ} [Fact (0 < r)]
    (F : Equiv.Perm (sphere (0 : V) r)) {O : V ≃ₗᵢ[ℝ] V}
    (hO : ∀ x : sphere (0 : V) r, (F x : V) = O x) :
    F ∈ IsometryGroup (sphereMetric (n := n) V r) := by
  have hOinv : ∀ y : sphere (0 : V) r, ((F⁻¹ y : sphere (0 : V) r) : V) = O.symm y := by
    intro y
    have h1 : (F (F⁻¹ y) : V) = O (F⁻¹ y) := hO _
    have h2 : F (F⁻¹ y) = y := by simp
    rw [h2] at h1
    rw [← O.symm_apply_apply (F⁻¹ y : V), ← h1]
  have hFs : ContMDiff (𝓡 n) (𝓡 n) ∞ ⇑F :=
    contMDiff_restrict_sphere_of_linearIsometryEquiv O hO
  have hFinv : ContMDiff (𝓡 n) (𝓡 n) ∞ ⇑F⁻¹ :=
    contMDiff_restrict_sphere_of_linearIsometryEquiv O.symm hOinv
  have hFinv' : ContMDiff (𝓡 n) (𝓡 n) ∞ ⇑(F : Equiv.Perm (sphere (0 : V) r)).symm := hFinv
  show IsRiemannianIsometry (sphereMetric (n := n) V r) (sphereMetric (n := n) V r) ⇑F
  refine ⟨⟨⟨(F : Equiv.Perm (sphere (0 : V) r)), hFs, hFinv'⟩, rfl⟩, fun p u v => ?_⟩
  have hkey := mfderiv_coe_sphere_restrict_of_linearIsometryEquiv O hFs hO
  rw [sphereMetric_apply, sphereMetric_apply, hkey p u, hkey p v, O.inner_map_map]

/-- **Math.** The scaled lower bound for curves on the sphere of radius `r`:
`r · arccos(⟪c a, c b⟫/r²) ≤ L(c)` — the radius-`r` version of
`arccos_inner_le_arcLength` (Exercise 1.6.20 (4)), by rescaling the curve to
the unit sphere. -/
theorem mul_arccos_le_arcLength_of_norm_eq {r : ℝ} (hr : 0 < r)
    {c : ℝ → V} (hc : ContDiff ℝ ∞ c) {a b : ℝ} (hab : a ≤ b)
    (hsphere : ∀ t, ‖c t‖ = r) :
    r * Real.arccos (⟪c a, c b⟫ / r ^ 2)
      ≤ arcLength (innerProductSpaceMetric V) c a b := by
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hc' : ContDiff ℝ ∞ (fun t => r⁻¹ • c t) := hc.const_smul r⁻¹
  have hsphere' : ∀ t, ‖r⁻¹ • c t‖ = 1 := by
    intro t
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, hsphere t,
      inv_mul_cancel₀ hr.ne']
  have h := arccos_inner_le_arcLength hc' hab hsphere'
  have hinner : ⟪r⁻¹ • c a, r⁻¹ • c b⟫ = ⟪c a, c b⟫ / r ^ 2 := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [hinner] at h
  have hL : arcLength (innerProductSpaceMetric V) (fun t => r⁻¹ • c t) a b
      = r⁻¹ * arcLength (innerProductSpaceMetric V) c a b := by
    rw [arcLength_eq_integral_norm_deriv, arcLength_eq_integral_norm_deriv,
      ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    have hd : deriv (fun t => r⁻¹ • c t) t = r⁻¹ • deriv c t :=
      (((hcd t).hasDerivAt).const_smul r⁻¹).deriv
    rw [hd, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
  rw [hL] at h
  calc r * Real.arccos (⟪c a, c b⟫ / r ^ 2)
      ≤ r * (r⁻¹ * arcLength (innerProductSpaceMetric V) c a b) :=
        mul_le_mul_of_nonneg_left h hr.le
    _ = arcLength (innerProductSpaceMetric V) c a b := by
        field_simp

/-- **Math.** A Riemannian isometry of the round sphere does not decrease
ambient inner products: comparing the great circle from `x` to `y` (of
induced length `r·∡(x,y)`, Exercise 1.6.20 (1)) with the lower bound
`r·∡(F x, F y) ≤ L(F ∘ γ) = L(γ)` (Exercises 1.6.17/1.6.20 (4) and metric
preservation) shows the angle cannot increase, i.e.
`⟪x, y⟫ ≤ ⟪F x, F y⟫`. -/
theorem inner_le_inner_of_mem_isometryGroup_sphere {r : ℝ} [Fact (0 < r)]
    {F : Equiv.Perm (sphere (0 : V) r)}
    (hF : F ∈ IsometryGroup (sphereMetric (n := n) V r))
    (x y : sphere (0 : V) r) :
    ⟪(x : V), (y : V)⟫ ≤ ⟪(F x : V), (F y : V)⟫ := by
  have hr : (0 : ℝ) < r := Fact.out
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hxs : ‖(x : V)‖ = r := mem_sphere_zero_iff_norm.mp x.2
  have hys : ‖(y : V)‖ = r := mem_sphere_zero_iff_norm.mp y.2
  have hFxs : ‖(F x : V)‖ = r := mem_sphere_zero_iff_norm.mp (F x).2
  have hFys : ‖(F y : V)‖ = r := mem_sphere_zero_iff_norm.mp (F y).2
  have hbound : |⟪(x : V), (y : V)⟫| ≤ r ^ 2 := by
    have h := abs_real_inner_le_norm (x : V) (y : V)
    rw [hxs, hys] at h
    nlinarith [h]
  rcases eq_or_lt_of_le (le_of_abs_le hbound) with htop | htop
  · -- `⟪x, y⟫ = r²` forces `x = y`
    have hyx : ⟪(y : V), (x : V)⟫ = r ^ 2 := by
      rw [real_inner_comm]
      exact htop
    have hsq : ‖(x : V) - (y : V)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hxs, hys,
        htop, hyx]
      ring
    have hxy : x = y := Subtype.ext
      (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)))
    rw [hxy, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hys,
      hFys]
  rcases eq_or_lt_of_le (neg_le_of_abs_le hbound) with hbot | hbot
  · -- `⟪x, y⟫ = −r²`: Cauchy–Schwarz on the images suffices
    have h := abs_real_inner_le_norm (F x : V) (F y : V)
    rw [hFxs, hFys] at h
    have h2 := neg_le_of_abs_le h
    nlinarith [h2]
  -- main case: `−r² < ⟪x, y⟫ < r²`, the great-circle comparison
  set xh : V := r⁻¹ • (x : V) with hxh_def
  set yh : V := r⁻¹ • (y : V) with hyh_def
  clear_value xh yh
  have hxh : ‖xh‖ = 1 := by
    rw [hxh_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, hxs,
      inv_mul_cancel₀ hr.ne']
  have hyh : ‖yh‖ = 1 := by
    rw [hyh_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, hys,
      inv_mul_cancel₀ hr.ne']
  have hth : ⟪xh, yh⟫ = ⟪(x : V), (y : V)⟫ / r ^ 2 := by
    rw [hxh_def, hyh_def, real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hne1 : yh ≠ xh := by
    intro h
    rw [h, real_inner_self_eq_norm_sq, hxh] at hth
    have : ⟪(x : V), (y : V)⟫ = r ^ 2 := by
      field_simp at hth
      linarith [hth]
    linarith [htop]
  have hne2 : yh ≠ -xh := by
    intro h
    rw [h, inner_neg_right, real_inner_self_eq_norm_sq, hxh] at hth
    have : ⟪(x : V), (y : V)⟫ = -r ^ 2 := by
      field_simp at hth
      linarith [hth]
    linarith [hbot]
  -- polar decomposition `yh = cos θ • xh + sin θ • v`
  have hmem_target : yh ∈ {z : V | ‖z‖ = 1 ∧ z ≠ xh ∧ z ≠ -xh} :=
    ⟨hyh, hne1, hne2⟩
  obtain ⟨⟨θ, v⟩, hbox, hGq⟩ := (exercise1_6_20_polar hxh).2.1.2.2 hmem_target
  obtain ⟨hθ, hv_perp, hv_norm⟩ := hbox
  have hGq' : Real.cos θ • xh + Real.sin θ • v = yh := hGq
  -- the great circle and its data
  obtain ⟨hnorm1, -, -, -, hspeed1, -⟩ :=
    exercise1_6_20_greatCircle hxh hv_norm hv_perp
  set ch : ℝ → V := fun s => Real.cos s • xh + Real.sin s • v with hch_def
  have hch_smooth : ContDiff ℝ ∞ ch :=
    (Real.contDiff_cos.smul contDiff_const).add
      (Real.contDiff_sin.smul contDiff_const)
  have hch_sphere : ∀ s, ch s ∈ sphere (0 : V) 1 := by
    intro s
    rw [mem_sphere_zero_iff_norm]
    exact hnorm1 s
  -- restrict to the unit sphere, then transport to radius `r`
  have hγ1_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (Set.codRestrict ch (sphere (0 : V) 1) hch_sphere) :=
    hch_smooth.contMDiff.codRestrict_sphere hch_sphere
  set γ : ℝ → sphere (0 : V) r := fun s =>
    (sphereHomeomorphUnitSphere r).symm
      (Set.codRestrict ch (sphere (0 : V) 1) hch_sphere s) with hγ_def
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ :=
    (contMDiff_sphereHomeomorphUnitSphere_symm r).comp hγ1_smooth
  have hγ_coe : ∀ s, (γ s : V) = r • ch s := by
    intro s
    rw [hγ_def]
    rw [sphereHomeomorphUnitSphere_symm_apply_coe, Set.val_codRestrict_apply]
  have hγ0 : γ 0 = x := by
    apply Subtype.ext
    rw [hγ_coe 0]
    show r • ch 0 = (x : V)
    have : ch 0 = xh := by
      rw [hch_def]
      simp
    rw [this, hxh_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hγθ : γ θ = y := by
    apply Subtype.ext
    rw [hγ_coe θ]
    show r • ch θ = (y : V)
    have : ch θ = yh := hGq'
    rw [this, hyh_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  -- isometry data of `F`
  have hFiso : IsRiemannianIsometry (sphereMetric (n := n) V r)
      (sphereMetric (n := n) V r) ⇑F := mem_isometryGroup.mp hF
  obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := hFiso
  have hFsm : ContMDiff (𝓡 n) (𝓡 n) ∞ ⇑F := by
    rw [← hΦ]
    exact Φ.contMDiff
  have hFd : MDifferentiable (𝓡 n) (𝓡 n) ⇑F := hFsm.mdifferentiable (by simp)
  have hγd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) γ :=
    hγ_smooth.mdifferentiable (by simp)
  -- length chain
  have himm := sphereMetric_isRiemannianImmersion (E := V) (n := n) r
  have hcoe_γ : ((↑) : sphere (0 : V) r → V) ∘ γ = fun s => r • ch s := by
    funext s
    exact hγ_coe s
  have hL1 : arcLength (innerProductSpaceMetric V)
        (((↑) : sphere (0 : V) r → V) ∘ γ) 0 θ
      = arcLength (sphereMetric (n := n) V r) γ 0 θ :=
    exercise1_6_17 himm hγd 0 θ
  have hLc : arcLength (innerProductSpaceMetric V) (fun s => r • ch s) 0 θ
      = r * θ := by
    rw [arcLength_eq_integral_norm_deriv]
    have hsp : ∀ s, ‖deriv (fun u => r • ch u) s‖ = r := by
      intro s
      have hd : deriv (fun u => r • ch u) s = r • deriv ch s :=
        ((((hch_smooth.differentiable (by simp)) s).hasDerivAt).const_smul
          r).deriv
      rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hspeed1 s, mul_one]
    simp only [hsp]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
  have hL2 : arcLength (sphereMetric (n := n) V r) (⇑F ∘ γ) 0 θ
      = arcLength (sphereMetric (n := n) V r) γ 0 θ :=
    PreservesMetric.arcLength hpres hFd hγd 0 θ
  have hL3 : arcLength (innerProductSpaceMetric V)
        (((↑) : sphere (0 : V) r → V) ∘ (⇑F ∘ γ)) 0 θ
      = arcLength (sphereMetric (n := n) V r) (⇑F ∘ γ) 0 θ :=
    exercise1_6_17 himm ((hFsm.comp hγ_smooth).mdifferentiable (by simp)) 0 θ
  -- the ambient image curve
  set amb : ℝ → V := fun s => ((F (γ s) : V)) with hamb_def
  have hamb_eq : ((↑) : sphere (0 : V) r → V) ∘ (⇑F ∘ γ) = amb := rfl
  have hamb_smooth : ContDiff ℝ ∞ amb := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) ∞ amb :=
      (contMDiff_coe_sphere_radius r).comp (hFsm.comp hγ_smooth)
    exact contMDiff_iff_contDiff.mp h1
  have hamb_sphere : ∀ s, ‖amb s‖ = r := fun s =>
    mem_sphere_zero_iff_norm.mp (F (γ s)).2
  have hkey := mul_arccos_le_arcLength_of_norm_eq hr hamb_smooth hθ.1.le
    hamb_sphere
  have hamb0 : amb 0 = (F x : V) := by
    simp only [hamb_def, hγ0]
  have hambθ : amb θ = (F y : V) := by
    simp only [hamb_def, hγθ]
  rw [hamb0, hambθ] at hkey
  have hchain : r * Real.arccos (⟪(F x : V), (F y : V)⟫ / r ^ 2) ≤ r * θ := by
    calc r * Real.arccos (⟪(F x : V), (F y : V)⟫ / r ^ 2)
        ≤ arcLength (innerProductSpaceMetric V) amb 0 θ := hkey
      _ = arcLength (sphereMetric (n := n) V r) (⇑F ∘ γ) 0 θ := by
          rw [← hamb_eq]
          exact hL3
      _ = arcLength (sphereMetric (n := n) V r) γ 0 θ := hL2
      _ = arcLength (innerProductSpaceMetric V)
            (((↑) : sphere (0 : V) r → V) ∘ γ) 0 θ := hL1.symm
      _ = arcLength (innerProductSpaceMetric V) (fun s => r • ch s) 0 θ := by
          rw [hcoe_γ]
      _ = r * θ := hLc
  have harccos_le : Real.arccos (⟪(F x : V), (F y : V)⟫ / r ^ 2) ≤ θ :=
    le_of_mul_le_mul_left hchain hr
  -- identify `θ` with the angle between `x` and `y`
  have hv_perp' : ⟪xh, v⟫ = 0 := hv_perp
  have hcosθ : Real.cos θ = ⟪(x : V), (y : V)⟫ / r ^ 2 := by
    rw [← hth, ← hGq', inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hxh, hv_perp']
    ring
  have hθ_eq : θ = Real.arccos (⟪(x : V), (y : V)⟫ / r ^ 2) := by
    rw [← hcosθ, Real.arccos_cos hθ.1.le hθ.2.le]
  rw [hθ_eq] at harccos_le
  -- undo `arccos` by cosine monotonicity
  have hFb : |⟪(F x : V), (F y : V)⟫ / r ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_pos hr2, div_le_one hr2]
    have h := abs_real_inner_le_norm (F x : V) (F y : V)
    rw [hFxs, hFys] at h
    nlinarith [h]
  have hxb : |⟪(x : V), (y : V)⟫ / r ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_pos hr2, div_le_one hr2]
    exact hbound
  have hcos_le := Real.cos_le_cos_of_nonneg_of_le_pi
    (Real.arccos_nonneg _) (Real.arccos_le_pi _) harccos_le
  rw [Real.cos_arccos (neg_le_of_abs_le hxb) (le_of_abs_le hxb),
    Real.cos_arccos (neg_le_of_abs_le hFb) (le_of_abs_le hFb)] at hcos_le
  have h := mul_le_mul_of_nonneg_right hcos_le hr2.le
  rw [div_mul_cancel₀ _ hr2.ne', div_mul_cancel₀ _ hr2.ne'] at h
  exact h

/-- **Math.** A Riemannian isometry of the round sphere **preserves ambient
inner products**: both `F` and `F⁻¹` do not decrease them
(`inner_le_inner_of_mem_isometryGroup_sphere`), so they are preserved. This
replaces Petersen's appeal to the uniqueness principle (Prop. 5.6.2) by the
length-minimization characterization of great circles (Exercise 1.6.20). -/
theorem inner_eq_inner_of_mem_isometryGroup_sphere {r : ℝ} [Fact (0 < r)]
    {F : Equiv.Perm (sphere (0 : V) r)}
    (hF : F ∈ IsometryGroup (sphereMetric (n := n) V r))
    (x y : sphere (0 : V) r) :
    ⟪(F x : V), (F y : V)⟫ = ⟪(x : V), (y : V)⟫ := by
  have hFinv : F⁻¹ ∈ IsometryGroup (sphereMetric (n := n) V r) :=
    (IsometryGroup (sphereMetric (n := n) V r)).inv_mem hF
  have h1 := inner_le_inner_of_mem_isometryGroup_sphere hF x y
  have h2 := inner_le_inner_of_mem_isometryGroup_sphere hFinv (F x) (F y)
  have hz : ∀ z : sphere (0 : V) r, F⁻¹ (F z) = z := fun z =>
    Equiv.symm_apply_apply F z
  rw [hz x, hz y] at h2
  linarith [h1, h2]

/-- **Math.** Petersen Example 1.3.2: the isometry group of the sphere is
`Iso(Sⁿ(R), g_{Sⁿ(R)}) = O(n+1) = Iso_0(ℝⁿ⁺¹, g_eu)`: a permutation `F` of
`Sⁿ(R) ⊆ V` (`dim V = n + 1`) is a Riemannian isometry iff it is the
restriction of an orthogonal transformation `O ∈ O(n+1)` (a linear isometry
of the ambient space).

The "if" direction is `mem_isometryGroup_sphere_of_linearIsometryEquiv`.

For the "only if" direction, Petersen's text assembles
`O = [R⁻¹ F(Re₁) | DF|_{Re₁}(e₂) | ⋯ | DF|_{Re₁}(e_{n+1})]` and appeals to
the uniqueness principle for Riemannian isometries (Prop. 5.6.2, out of
Ch. 1 scope) to force `F = O`. Here the uniqueness principle is replaced by
the **length-minimization characterization of great circles**
(Exercise 1.6.20): a Riemannian isometry preserves induced arc length,
hence spherical angles, hence ambient inner products
(`inner_eq_inner_of_mem_isometryGroup_sphere`); the map
`eᵢ ↦ R⁻¹ F(R eᵢ)` on an orthonormal basis then extends to the required
orthogonal transformation, and equality of all inner products against the
image basis forces `F = O` on the sphere.

Petersen additionally notes `Iso_p(Sⁿ(R)) ≅ O(n)` and `Sⁿ ≃ O(n+1)/O(n)`;
these quotient identifications are not formalized here. -/
theorem isometryGroup_sphere {r : ℝ} [Fact (0 < r)]
    (F : Equiv.Perm (sphere (0 : V) r)) :
    F ∈ IsometryGroup (sphereMetric (n := n) V r) ↔
      ∃ O : V ≃ₗᵢ[ℝ] V, ∀ x : sphere (0 : V) r, (F x : V) = O x := by
  constructor
  · intro hF
    have hr : (0 : ℝ) < r := Fact.out
    haveI : FiniteDimensional ℝ V :=
      FiniteDimensional.of_finrank_eq_succ (Fact.out : finrank ℝ V = n + 1)
    have hinner : ∀ x y : sphere (0 : V) r,
        ⟪(F x : V), (F y : V)⟫ = ⟪(x : V), (y : V)⟫ :=
      inner_eq_inner_of_mem_isometryGroup_sphere hF
    set b := stdOrthonormalBasis ℝ V with hb_def
    have hmem : ∀ i, r • (b i) ∈ sphere (0 : V) r := by
      intro i
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, b.orthonormal.1 i, mul_one]
    set σ : Fin (finrank ℝ V) → sphere (0 : V) r := fun i => ⟨r • b i, hmem i⟩
      with hσ_def
    set f : V →ₗ[ℝ] V :=
      (b.toBasis).constr ℝ (fun i => r⁻¹ • ((F (σ i) : V))) with hf_def
    have hfb : ∀ i, f (b i) = r⁻¹ • ((F (σ i) : V)) := by
      intro i
      have h := Basis.constr_basis (b.toBasis) ℝ
        (fun i => r⁻¹ • ((F (σ i) : V))) i
      rwa [OrthonormalBasis.coe_toBasis] at h
    -- the image family is orthonormal
    have hforth : Orthonormal ℝ (⇑f ∘ ⇑b.toBasis) := by
      rw [OrthonormalBasis.coe_toBasis, orthonormal_iff_ite]
      intro i j
      rw [Function.comp_apply, Function.comp_apply, hfb i, hfb j,
        real_inner_smul_left, real_inner_smul_right, hinner (σ i) (σ j)]
      have hσc : ∀ k, ((σ k : sphere (0 : V) r) : V) = r • b k := fun k => rfl
      rw [hσc i, hσc j, real_inner_smul_left, real_inner_smul_right]
      have hb_ite := orthonormal_iff_ite.mp b.orthonormal i j
      rw [hb_ite]
      have : r⁻¹ * (r⁻¹ * (r * (r * (if i = j then (1 : ℝ) else 0))))
          = if i = j then (1 : ℝ) else 0 := by
        field_simp
      rw [this]
    -- the linear isometry and its equivalence upgrade
    set L : V →ₗᵢ[ℝ] V := f.isometryOfOrthonormal
      (by rw [OrthonormalBasis.coe_toBasis]; exact b.orthonormal) hforth
      with hL_def
    set O : V ≃ₗᵢ[ℝ] V := L.toLinearIsometryEquiv rfl with hO_def
    have hO_apply : ∀ w : V, O w = f w := fun w => rfl
    refine ⟨O, fun x => ?_⟩
    -- compare coefficients in the orthonormal basis `O ∘ b`
    set b' : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V := b.map O with hb'_def
    have hb'_apply : ∀ i, b' i = O (b i) := by
      intro i
      rw [hb'_def, OrthonormalBasis.map_apply]
    have hcoeff : ∀ i, ⟪b' i, (F x : V)⟫ = ⟪b' i, O x⟫ := by
      intro i
      have hObi : O (b i) = r⁻¹ • ((F (σ i) : V)) := by
        rw [hO_apply, hfb i]
      have hσc : ((σ i : sphere (0 : V) r) : V) = r • b i := rfl
      have hLHS : ⟪b' i, (F x : V)⟫ = ⟪b i, (x : V)⟫ := by
        rw [hb'_apply i, hObi, real_inner_smul_left, hinner (σ i) x, hσc,
          real_inner_smul_left, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
      have hRHS : ⟪b' i, O x⟫ = ⟪b i, (x : V)⟫ := by
        rw [hb'_apply i]
        exact O.inner_map_map (b i) (x : V)
      rw [hLHS, hRHS]
    -- equal coefficients in an orthonormal basis force equality
    have hrepr : b'.repr (F x : V) = b'.repr (O x) := by
      ext i
      rw [b'.repr_apply_apply, b'.repr_apply_apply]
      exact hcoeff i
    exact b'.repr.injective hrepr
  · rintro ⟨O, hO⟩
    exact mem_isometryGroup_sphere_of_linearIsometryEquiv F hO

end SphereIsometries

/-! ## Example 1.3.3: isometries of hyperbolic space

The Lorentz group `O(n, 1)` and its orthochronous subgroup `O⁺(n, 1)`.
Following `minkowskiMetric` (Petersen Example 1.1.6), Minkowski space
`ℝ^{n₁,n₂}` is formalized as a product `F₁ × F₂` of real inner product
spaces; `O(n, 1)` is the case `F₁ = EuclideanSpace ℝ (Fin n)`, `F₂ = ℝ`.
These groups belong mathematically to Example 1.3.3, hence live here rather
than in `Ch01/Minkowski.lean`. -/

section MinkowskiGroups

variable (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂]

/-- **Math.** Petersen Example 1.3.3: the (generalized) **Lorentz group**
`O(n₁, n₂) = {L : ℝ^{n₁,n₂} → ℝ^{n₁,n₂} linear | g(Lv, Lv) = g(v, v)}` of
linear transformations preserving the Minkowski quadratic form, realized as
a subgroup of the continuous linear automorphisms of `F₁ × F₂`. By
polarization (`minkowskiForm_map_map`) its members preserve the Minkowski
bilinear form itself. -/
def minkowskiIsometryGroup : Subgroup ((F₁ × F₂) ≃L[ℝ] (F₁ × F₂)) where
  carrier := {L | ∀ v : F₁ × F₂,
    minkowskiForm F₁ F₂ (L v) (L v) = minkowskiForm F₁ F₂ v v}
  one_mem' _ := rfl
  mul_mem' := by
    intro L L' hL hL' v
    have h : (L * L') v = L (L' v) := rfl
    rw [h, hL (L' v), hL' v]
  inv_mem' := by
    intro L hL v
    have h : (L⁻¹ : (F₁ × F₂) ≃L[ℝ] (F₁ × F₂)) v = L.symm v := rfl
    rw [h, ← hL (L.symm v), L.apply_symm_apply]

@[simp]
theorem mem_minkowskiIsometryGroup {L : (F₁ × F₂) ≃L[ℝ] (F₁ × F₂)} :
    L ∈ minkowskiIsometryGroup F₁ F₂ ↔
      ∀ v : F₁ × F₂, minkowskiForm F₁ F₂ (L v) (L v) = minkowskiForm F₁ F₂ v v :=
  Iff.rfl

/-- **Math.** Polarization: an element of `O(n₁, n₂)` preserves the Minkowski
*bilinear* form, not merely the quadratic form: expanding
`g(L(v+w), L(v+w)) = g(v+w, v+w)` by bilinearity and cancelling the squares
leaves `2g(Lv, Lw) = 2g(v, w)`. -/
theorem minkowskiForm_map_map {L : (F₁ × F₂) ≃L[ℝ] (F₁ × F₂)}
    (hL : L ∈ minkowskiIsometryGroup F₁ F₂) (v w : F₁ × F₂) :
    minkowskiForm F₁ F₂ (L v) (L w) = minkowskiForm F₁ F₂ v w := by
  have h1 := hL (v + w)
  have h2 := hL v
  have h3 := hL w
  have expand : ∀ a b : F₁ × F₂,
      minkowskiForm F₁ F₂ (a + b) (a + b)
        = minkowskiForm F₁ F₂ a a + minkowskiForm F₁ F₂ a b
          + (minkowskiForm F₁ F₂ b a + minkowskiForm F₁ F₂ b b) := by
    intro a b
    simp only [map_add, ContinuousLinearMap.add_apply]
    ring
  rw [map_add, expand, expand] at h1
  have hsym1 := minkowskiForm_comm F₁ F₂ (L v) (L w)
  have hsym2 := minkowskiForm_comm F₁ F₂ v w
  linarith

/-- **Math.** On `ℝ^{n,1} = F₁ × ℝ` the Minkowski square norm is
`g(v, v) = ‖v₁‖² - (v^{n+1})²`. -/
theorem minkowskiForm_self_real (v : F₁ × ℝ) :
    minkowskiForm F₁ ℝ v v = ‖v.1‖ ^ 2 - v.2 ^ 2 := by
  rw [minkowskiForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    Real.norm_eq_abs, sq_abs]

/-- **Math.** Petersen Example 1.3.3: the **orthochronous Lorentz group**
`O⁺(n, 1) ⊆ O(n, 1)`: those Minkowski isometries of `ℝ^{n,1} = F₁ × ℝ`
that preserve the condition `x^{n+1} > 0` on timelike vectors (i.e. map the
upper time cone into itself). Closure under inverse: `w = L⁻¹(v)` is again
timelike, so `w^{n+1} ≠ 0`; were `w^{n+1} < 0`, then `-w` would lie in the
upper cone with `L(-w) = -v`, contradicting `v^{n+1} > 0`. -/
def orthochronousMinkowskiGroup : Subgroup ((F₁ × ℝ) ≃L[ℝ] (F₁ × ℝ)) where
  carrier := {L | L ∈ minkowskiIsometryGroup F₁ ℝ ∧
    ∀ v : F₁ × ℝ, minkowskiForm F₁ ℝ v v < 0 → 0 < v.2 → 0 < (L v).2}
  one_mem' := ⟨(minkowskiIsometryGroup F₁ ℝ).one_mem, fun _ _ hv2 => hv2⟩
  mul_mem' := by
    rintro L L' ⟨hL, hLc⟩ ⟨hL', hLc'⟩
    refine ⟨(minkowskiIsometryGroup F₁ ℝ).mul_mem hL hL', fun v hv hv2 => ?_⟩
    have h : (L * L') v = L (L' v) := rfl
    rw [h]
    exact hLc (L' v) (by rw [hL' v]; exact hv) (hLc' v hv hv2)
  inv_mem' := by
    rintro L ⟨hL, hLc⟩
    refine ⟨(minkowskiIsometryGroup F₁ ℝ).inv_mem hL, fun v hv hv2 => ?_⟩
    have hsymm : (L⁻¹ : (F₁ × ℝ) ≃L[ℝ] (F₁ × ℝ)) v = L.symm v := rfl
    rw [hsymm]
    have hLw : L (L.symm v) = v := L.apply_symm_apply v
    have hwt : minkowskiForm F₁ ℝ (L.symm v) (L.symm v) < 0 := by
      rw [← hL (L.symm v), hLw]
      exact hv
    have hw2 : (L.symm v).2 ≠ 0 := by
      intro h0
      rw [minkowskiForm_self_real, h0] at hwt
      nlinarith [sq_nonneg ‖(L.symm v).1‖]
    rcases lt_or_gt_of_ne hw2 with hneg | hpos
    · exfalso
      have hmwt : minkowskiForm F₁ ℝ (-L.symm v) (-L.symm v) < 0 := by
        simpa only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] using hwt
      have hmw2 : 0 < (-L.symm v).2 := by
        simpa only [Prod.snd_neg] using neg_pos.mpr hneg
      have hupper := hLc (-L.symm v) hmwt hmw2
      rw [map_neg, hLw] at hupper
      rw [Prod.snd_neg] at hupper
      linarith
    · exact hpos

@[simp]
theorem mem_orthochronousMinkowskiGroup {L : (F₁ × ℝ) ≃L[ℝ] (F₁ × ℝ)} :
    L ∈ orthochronousMinkowskiGroup F₁ ↔
      L ∈ minkowskiIsometryGroup F₁ ℝ ∧
        ∀ v : F₁ × ℝ, minkowskiForm F₁ ℝ v v < 0 → 0 < v.2 → 0 < (L v).2 :=
  Iff.rfl

end MinkowskiGroups

section HyperbolicIsometries

/-- **Math.** Petersen Example 1.3.3 (ingredient): an orthochronous Lorentz
transformation maps the hyperboloid branch `Hⁿ(R)` into itself: it preserves
the defining equation (the Minkowski square norm `-R²`), and since points of
`Hⁿ(R)` are upper timelike vectors it preserves `x^{n+1} > 0`. -/
theorem orthochronous_maps_hyperboloid {n : ℕ} {R : ℝ} [Fact (0 < R)]
    {L : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)}
    (hL : L ∈ orthochronousMinkowskiGroup (EuclideanSpace ℝ (Fin n)))
    (p : hyperboloid n R) :
    ‖(L p.1).1‖ ^ 2 - (L p.1).2 ^ 2 = -R ^ 2 ∧ 0 < (L p.1).2 := by
  have hR : (0 : ℝ) < R := Fact.out
  obtain ⟨hL1, hL2⟩ := hL
  have hp : minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ p.1 p.1 = -R ^ 2 := by
    rw [minkowskiForm_self_real]
    exact p.2.1
  have hneg : minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ p.1 p.1 < 0 := by
    rw [hp]
    nlinarith
  exact ⟨by rw [← minkowskiForm_self_real, hL1 p.1, hp], hL2 p.1 hneg p.2.2⟩

/-- **Math.** Petersen Example 1.3.3 (ingredient): a self-map of `Hⁿ(R)`
that is the restriction of an ambient (continuous) linear automorphism is
smooth: in the single global chart `(x, t) ↦ x` of the hyperboloid it reads
as `x ↦ (L(x, √(‖x‖² + R²)))₁`, a composition of smooth maps. -/
theorem contMDiff_restrict_hyperboloid {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (L : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ))
    {f : hyperboloid n R → hyperboloid n R}
    (hf : ∀ p : hyperboloid n R, (f p).1 = L p.1) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f := by
  set c := chartAt (EuclideanSpace ℝ (Fin n)) (Classical.arbitrary (hyperboloid n R)) with hc
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun p : hyperboloid n R => (L p.1).1) := by
    have h1 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        ⇑((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp
          (L : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ))) :=
      ContinuousLinearMap.contMDiff _
    exact (h1.comp (hyperboloidInclusion_contMDiff n R)).congr fun p => rfl
  have hcs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      ⇑c.symm := by
    have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        ⇑c.symm c.target := contMDiffOn_chart_symm
    rw [show c.target = Set.univ from rfl] at h2
    exact contMDiffOn_univ.mp h2
  refine (hcs.comp hg).congr fun p => ?_
  have h3 : c (f p) = (L p.1).1 := by
    show (f p).1.1 = (L p.1).1
    rw [hf p]
  show f p = c.symm ((L p.1).1)
  rw [← h3]
  exact (c.left_inv trivial).symm

/-- **Math.** Petersen Example 1.3.3 (ingredient): if a smooth self-map `f`
of `Hⁿ(R)` is the restriction of an ambient linear map `L`, then the ambient
image of its differential is computed by `L`:
`Dι_{f(p)}(Df_p(u)) = L(Dι_p(u))` — the chain rule applied to the two
factorizations of `ι ∘ f = L ∘ ι`. -/
theorem mfderiv_hyperboloidInclusion_restrict {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (L : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ))
    {f : hyperboloid n R → hyperboloid n R}
    (hsmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hf : ∀ p : hyperboloid n R, (f p).1 = L p.1) (p : hyperboloid n R)
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (hyperboloidInclusion n R) (f p)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f p u)
      = L (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
          (hyperboloidInclusion n R) p u) := by
  set LL : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
    (L : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)) with hLL
  have hι : ∀ y : hyperboloid n R,
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (hyperboloidInclusion n R) y := fun y =>
    (hyperboloidInclusion_contMDiff n R y).mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f p :=
    (hsmooth p).mdifferentiableAt (by simp)
  have hLd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ⇑LL (hyperboloidInclusion n R p) :=
    (ContinuousLinearMap.contMDiff (n := 1) LL).mdifferentiableAt one_ne_zero
  have heq : (hyperboloidInclusion n R ∘ f) = ⇑LL ∘ hyperboloidInclusion n R := by
    funext y
    exact hf y
  have h1 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (hyperboloidInclusion n R ∘ f) p
      = (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
          (hyperboloidInclusion n R) (f p)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f p) :=
    mfderiv_comp p (hι (f p)) hfd
  have h2 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (⇑LL ∘ hyperboloidInclusion n R) p
      = (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
          ⇑LL (hyperboloidInclusion n R p)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
          (hyperboloidInclusion n R) p) :=
    mfderiv_comp p hLd (hι p)
  have hLm : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
      ⇑LL (hyperboloidInclusion n R p) = LL := by
    rw [mfderiv_eq_fderiv]
    exact ContinuousLinearMap.fderiv LL
  have hcomp : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (hyperboloidInclusion n R) (f p)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f p)
      = LL.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
          (hyperboloidInclusion n R) p) := by
    rw [← h1, heq, h2, hLm]
  have := congrArg
    (fun T : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × ℝ) => T u) hcomp
  simpa [hLL] using this

/-- **Math.** Petersen Example 1.3.3 (ingredient): tangent vectors to
`Hⁿ(R)` are Minkowski-orthogonal to the position vector: with
`Dι_p(u) = (u, ⟪p₁, u⟫/p_t)` (the tangency relation of Example 1.1.7),
`g(p, Dι_p(u)) = ⟪p₁, u⟫ - p_t ⋅ ⟪p₁, u⟫/p_t = 0`. This is the "last
column is Minkowski-orthogonal to the others" step of Petersen's matrix
construction. -/
theorem minkowskiForm_coe_mfderiv_hyperboloidInclusion {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (p : hyperboloid n R) (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) :
    minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ p.1
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (hyperboloidInclusion n R) p u) = 0 := by
  have h1 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (hyperboloidInclusion n R) p u
      = ((u : EuclideanSpace ℝ (Fin n)), (⟪p.1.1, u⟫ / p.1.2 : ℝ)) := by
    rw [mfderiv_hyperboloidInclusion]
    exact hyperboloidInclusionDeriv_apply n R p u
  rw [h1, minkowskiForm_apply]
  have h2 : ⟪(p.1.2 : ℝ), (⟪p.1.1, u⟫ / p.1.2 : ℝ)⟫ = p.1.2 * (⟪p.1.1, u⟫ / p.1.2) :=
    mul_comm _ _
  rw [h2, mul_div_cancel₀ _ (hyperboloid_t_pos p).ne']
  simp

/-- **Math.** Petersen Example 1.3.3, the fully proved "if" direction (as a
standalone, sorry-free lemma so that `isHomogeneous_hyperbolicSpace` can
draw on it): the restriction to `Hⁿ(R)` of an orthochronous Minkowski
isometry `L ∈ O⁺(n, 1)` is a Riemannian isometry of `(Hⁿ(R), g_{Hⁿ(R)})`.

`L` maps the branch to itself (`orthochronous_maps_hyperboloid`), its
restriction is smooth in the global chart
(`contMDiff_restrict_hyperboloid`, likewise for the inverse permutation via
`L⁻¹`), and since `Dι ∘ DF = L ∘ Dι`
(`mfderiv_hyperboloidInclusion_restrict`) while the hyperbolic metric is
induced from the Minkowski form, polarized form-preservation
(`minkowskiForm_map_map`) forces `F` to preserve `g_{Hⁿ(R)}`. -/
theorem mem_isometryGroup_hyperbolicSpace_of_orthochronous {n : ℕ} {R : ℝ}
    [Fact (0 < R)] (F : Equiv.Perm (hyperboloid n R))
    {L : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)}
    (hL : L ∈ orthochronousMinkowskiGroup (EuclideanSpace ℝ (Fin n)))
    (hFL : ∀ x : hyperboloid n R, (F x).1 = L x.1) :
    F ∈ IsometryGroup (hyperbolicSpace n R) := by
  have hFinvL : ∀ y : hyperboloid n R,
      (F⁻¹ y).1 = (L⁻¹ : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × ℝ)) y.1 := by
    intro y
    have h1 : (F (F⁻¹ y)).1 = L (F⁻¹ y).1 := hFL _
    have h2 : F (F⁻¹ y) = y := by simp
    rw [h2] at h1
    show (F⁻¹ y).1 = L.symm y.1
    rw [h1, L.symm_apply_apply]
  have hFs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ⇑F :=
    contMDiff_restrict_hyperboloid L hFL
  have hFinv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ⇑F⁻¹ :=
    contMDiff_restrict_hyperboloid L⁻¹ hFinvL
  have hFinv' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ⇑(F : Equiv.Perm (hyperboloid n R)).symm := hFinv
  show IsRiemannianIsometry (hyperbolicSpace n R) (hyperbolicSpace n R) ⇑F
  refine ⟨⟨⟨(F : Equiv.Perm (hyperboloid n R)), hFs, hFinv'⟩, rfl⟩, fun p u v => ?_⟩
  have hkey := mfderiv_hyperboloidInclusion_restrict L hFs hFL
  rw [hyperbolicSpace_metricInner, hyperbolicSpace_metricInner, hkey p u, hkey p v,
    minkowskiForm_map_map (EuclideanSpace ℝ (Fin n)) ℝ hL.1]

/-! ### Hyperbolic distance realization

The mirror of the sphere development above: the induced arc length on
`Hⁿ(R)` is the ambient Minkowski integral, the hyperbola realizes the
hyperbolic distance `R·arcosh(−η(x,y)/R²)`, and every curve is at least that
long (`mul_arcosh_le_length_hyperboloid`, from Exercise 1.6.21 (4)); hence a
Riemannian isometry of `Hⁿ(R)` preserves Minkowski pairings of hyperboloid
points (`minkowskiForm_eq_of_mem_isometryGroup_hyperbolicSpace`) — the
ingredient replacing the uniqueness principle (Petersen Prop. 5.6.2) in the
classification of `Iso(Hⁿ(R))`. -/

section HyperbolicDistance

variable {n : ℕ} {R : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "η" => minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ

/-- **Eng.** The defining equation of the hyperboloid, in Minkowski-form
terms: `η(p, p) = −R²`. -/
theorem hyperboloid_minkowskiForm_self (p : hyperboloid n R) :
    η p.1 p.1 = -R ^ 2 := by
  have h := p.2.1
  simp only [minkowskiForm_apply]
  rw [real_inner_self_eq_norm_sq]
  have h2 : ⟪p.1.2, p.1.2⟫ = p.1.2 ^ 2 := by
    have h3 : ⟪p.1.2, p.1.2⟫ = p.1.2 * p.1.2 := rfl
    rw [h3]
    ring
  rw [h2]
  linarith

/-- **Eng.** A curve into the hyperboloid whose ambient (subtype-value) curve
is smooth is a smooth curve into the manifold `Hⁿ(R)` — read through the
single global chart, it is the (smooth) spatial part. -/
theorem contMDiff_hyperboloid_mk [Fact (0 < R)] {f : ℝ → E × ℝ}
    {γ : ℝ → hyperboloid n R} (hf : ContDiff ℝ ∞ f)
    (hγf : ∀ s, (γ s).1 = f s) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ := by
  -- through the global chart: the map is `chart.symm ∘ (spatial part)`
  set x₀ : hyperboloid n R := γ 0 with hx₀_def
  have hchart : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm
      (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target :=
    contMDiffOn_chart_symm
  have htarget : (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target = Set.univ :=
    rfl
  rw [htarget, contMDiffOn_univ] at hchart
  have hsp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun s => (f s).1) :=
    ((contDiff_fst.comp hf).contMDiff : ContMDiff 𝓘(ℝ, ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ fun s => (f s).1)
  refine (hchart.comp hsp).congr fun s => ?_
  -- the chart inverse of the spatial part is the point itself
  apply Subtype.ext
  have hsq : Real.sqrt (‖(f s).1‖ ^ 2 + R ^ 2) = (f s).2 := by
    have h := hyperboloid_sqrt_eq (γ s)
    rwa [hγf s] at h
  show (γ s).1 = ((f s).1, Real.sqrt (‖(f s).1‖ ^ 2 + R ^ 2))
  rw [hγf s, hsq]

/-- **Math.** The induced arc length on `Hⁿ(R)` is the ambient Minkowski
integral: `L_{Hⁿ(R)}(γ) = ∫ √η(ċ, ċ)` for the ambient curve `c = ι ∘ γ` —
the hyperbolic analogue of measuring sphere curves ambiently
(Exercise 1.6.17; here the ambient "metric" is the Minkowski pseudo-metric,
so the identity is proved by unfolding the pullback). -/
theorem arcLength_hyperbolicSpace_eq_integral [Fact (0 < R)]
    {γ : ℝ → hyperboloid n R}
    (hγ : MDifferentiable 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) γ)
    (a b : ℝ) :
    arcLength (hyperbolicSpace n R) γ a b
      = ∫ t in a..b, Real.sqrt
          (η (deriv (fun s => (γ s).1) t) (deriv (fun s => (γ s).1) t)) := by
  simp only [PetersenLib.arcLength]
  congr 1
  funext t
  congr 1
  rw [hyperbolicSpace_metricInner]
  have hι : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) (hyperboloidInclusion n R) (γ t) :=
    (hyperboloidInclusion_contMDiff n R (γ t)).mdifferentiableAt (by simp)
  have h1 : velocity (hyperboloidInclusion n R ∘ γ) t
      = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) (hyperboloidInclusion n R) (γ t)
          (velocity γ t) :=
    velocity_comp t hι (hγ t)
  rw [← h1, velocity_eq_deriv]
  rfl

/-- **Math.** The scaled arcosh lower bound for ambient curves on the
hyperboloid branch of "radius" `R`:
`R · arcosh(−η(c a, c b)/R²) ≤ ∫ √η(ċ, ċ)` — the radius-`R` version of
`arcosh_neg_minkowskiForm_le_length`, by rescaling to the unit branch. -/
theorem mul_arcosh_le_length_hyperboloid (hR : 0 < R)
    {c : ℝ → E × ℝ} (hc : ContDiff ℝ ∞ c) {a b : ℝ} (hab : a ≤ b)
    (hH : ∀ t, η (c t) (c t) = -R ^ 2 ∧ 0 < (c t).2) :
    R * Real.arcosh (-(η (c a) (c b)) / R ^ 2)
      ≤ ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) := by
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hc' : ContDiff ℝ ∞ (fun t => R⁻¹ • c t) := hc.const_smul R⁻¹
  have hsmul : ∀ u v : E × ℝ, η (R⁻¹ • u) (R⁻¹ • v) = η u v / R ^ 2 := by
    intro u v
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]
    field_simp
  have hH' : ∀ t, η (R⁻¹ • c t) (R⁻¹ • c t) = -1 ∧ 0 < (R⁻¹ • c t).2 := by
    intro t
    constructor
    · rw [hsmul, (hH t).1]
      field_simp
    · show 0 < R⁻¹ * (c t).2
      exact mul_pos (inv_pos.mpr hR) (hH t).2
  have h := arcosh_neg_minkowskiForm_le_length hc' hab hH'
  have hend : -(η (R⁻¹ • c a) (R⁻¹ • c b)) = -(η (c a) (c b)) / R ^ 2 := by
    rw [hsmul]
    ring
  rw [hend] at h
  have hint : (∫ t in a..b, Real.sqrt
        (η (deriv (fun s => R⁻¹ • c s) t) (deriv (fun s => R⁻¹ • c s) t)))
      = R⁻¹ * ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    have hd : deriv (fun s => R⁻¹ • c s) t = R⁻¹ • deriv c t :=
      (((hcd t).hasDerivAt).const_smul R⁻¹).deriv
    rw [hd, hsmul]
    rw [div_eq_mul_inv, mul_comm, Real.sqrt_mul (by positivity)]
    congr 1
    rw [Real.sqrt_inv, Real.sqrt_sq hR.le]
  rw [hint] at h
  calc R * Real.arcosh (-(η (c a) (c b)) / R ^ 2)
      ≤ R * (R⁻¹ * ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t))) :=
        mul_le_mul_of_nonneg_left h hR.le
    _ = ∫ t in a..b, Real.sqrt (η (deriv c t) (deriv c t)) := by
        field_simp

/-- **Math.** A Riemannian isometry of hyperbolic space does not decrease the
Minkowski pairing: comparing the hyperbola from `x` to `y` (of induced length
`R·d(x,y)`, Exercise 1.6.21 (1)) with the arcosh lower bound for the image
curve shows the hyperbolic distance cannot increase, i.e.
`η(x, y) ≤ η(F x, F y)`, equivalently `−η(F x, F y) ≤ −η(x, y)`. -/
theorem minkowskiForm_le_of_mem_isometryGroup_hyperbolicSpace
    [Fact (0 < R)] {F : Equiv.Perm (hyperboloid n R)}
    (hF : F ∈ IsometryGroup (hyperbolicSpace n R)) (x y : hyperboloid n R) :
    η x.1 y.1 ≤ η (F x).1 (F y).1 := by
  have hR : (0 : ℝ) < R := Fact.out
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  -- unit-branch representatives
  set xh : E × ℝ := R⁻¹ • x.1 with hxh_def
  set yh : E × ℝ := R⁻¹ • y.1 with hyh_def
  have hsmul : ∀ u v : E × ℝ, η (R⁻¹ • u) (R⁻¹ • v) = η u v / R ^ 2 := by
    intro u v
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]
    field_simp
  have hxh_self : η xh xh = -1 := by
    rw [hxh_def, hsmul, hyperboloid_minkowskiForm_self]
    field_simp
  have hyh_self : η yh yh = -1 := by
    rw [hyh_def, hsmul, hyperboloid_minkowskiForm_self]
    field_simp
  have hxh_pos : 0 < xh.2 := by
    rw [hxh_def]
    exact mul_pos (inv_pos.mpr hR) (hyperboloid_t_pos x)
  have hyh_pos : 0 < yh.2 := by
    rw [hyh_def]
    exact mul_pos (inv_pos.mpr hR) (hyperboloid_t_pos y)
  have hth : η xh yh = η x.1 y.1 / R ^ 2 := by
    rw [hxh_def, hyh_def, hsmul]
  clear_value xh yh
  -- degenerate case: `η(x, y) = −R²` forces `x = y`
  have hu_ge : 1 ≤ -(η xh yh) :=
    one_le_neg_minkowskiForm_of_sheet hxh_self hxh_pos hyh_self hyh_pos
  rcases eq_or_lt_of_le hu_ge with heq1 | hu_gt
  · -- `−η(xh, yh) = 1`: definiteness gives `xh = yh`, hence `x = y`
    have hxy : xh = yh := by
      have hyx' : η yh xh = -1 := by
        rw [minkowskiForm_comm (EuclideanSpace ℝ (Fin n)) ℝ yh xh]
        linarith [heq1]
      have htang : η xh (yh - xh) = 0 := by
        rw [map_sub, hxh_self]
        have : η xh yh = -1 := by linarith [heq1]
        rw [this]
        ring
      have hnull : η (yh - xh) (yh - xh) = 0 := by
        simp only [map_sub, ContinuousLinearMap.sub_apply]
        have h1 : η xh yh = -1 := by linarith [heq1]
        rw [h1, hyx', hxh_self, hyh_self]
        ring
      have hz := minkowskiForm_tangent_eq_zero hxh_self hxh_pos htang hnull
      exact (sub_eq_zero.mp hz).symm
    have hxy' : x = y := by
      apply Subtype.ext
      have h1 : R • xh = R • yh := by rw [hxy]
      rw [hxh_def, hyh_def, smul_smul, smul_smul,
        mul_inv_cancel₀ hR.ne', one_smul, one_smul] at h1
      exact h1
    rw [hxy', hyperboloid_minkowskiForm_self,
      hyperboloid_minkowskiForm_self]
  -- main case: `−η(xh, yh) > 1`; hyperbola comparison
  have hyx_ne : yh ≠ xh := by
    intro h
    rw [h, hxh_self] at hu_gt
    norm_num at hu_gt
  obtain ⟨⟨θ, w⟩, hbox, hGq⟩ :=
    ((exercise1_6_21_polar hxh_self hxh_pos).2.1.2.2 :
      Set.SurjOn _ _ {z : E × ℝ | η z z = -1 ∧ 0 < z.2 ∧ z ≠ xh})
      ⟨hyh_self, hyh_pos, hyx_ne⟩
  obtain ⟨hθ, hw_tang, hw_unit⟩ := hbox
  have hθ' : (0 : ℝ) < θ := hθ
  have hw_tang' : η xh w = 0 := hw_tang
  have hw_unit' : η w w = 1 := hw_unit
  have hGq' : Real.cosh θ • xh + Real.sinh θ • w = yh := hGq
  -- the unit-speed hyperbola and its data
  obtain ⟨hon, htpos, -, hderiv, -, hspeed⟩ :=
    exercise1_6_21_hyperbola hxh_self hxh_pos hw_unit' hw_tang'
  set ch : ℝ → E × ℝ := fun s => Real.cosh s • xh + Real.sinh s • w
    with hch_def
  have hch_smooth : ContDiff ℝ ∞ ch :=
    (Real.contDiff_cosh.smul contDiff_const).add
      (Real.contDiff_sinh.smul contDiff_const)
  -- the ambient radius-`R` hyperbola
  set c : ℝ → E × ℝ := fun s => R • ch s with hc_def
  have hc_smooth : ContDiff ℝ ∞ c := hch_smooth.const_smul R
  have hc_H : ∀ s, η (c s) (c s) = -R ^ 2 ∧ 0 < (c s).2 := by
    intro s
    constructor
    · rw [hc_def]
      simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        smul_eq_mul]
      rw [hon s]
      ring
    · show 0 < R * (ch s).2
      exact mul_pos hR (htpos s)
  have hc_mem : ∀ s, ‖(c s).1‖ ^ 2 - (c s).2 ^ 2 = -R ^ 2 ∧ 0 < (c s).2 := by
    intro s
    refine ⟨?_, (hc_H s).2⟩
    have h := (hc_H s).1
    simp only [minkowskiForm_apply] at h
    rw [real_inner_self_eq_norm_sq] at h
    have h2 : ⟪(c s).2, (c s).2⟫ = (c s).2 ^ 2 := by
      have h3 : ⟪(c s).2, (c s).2⟫ = (c s).2 * (c s).2 := rfl
      rw [h3]
      ring
    rw [h2] at h
    linarith
  -- the manifold-valued hyperbola
  set γ : ℝ → hyperboloid n R := fun s => ⟨c s, hc_mem s⟩ with hγ_def
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ :=
    contMDiff_hyperboloid_mk hc_smooth (fun s => rfl)
  have hγd : MDifferentiable 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) γ :=
    hγ_smooth.mdifferentiable (by simp)
  have hγ0 : γ 0 = x := by
    apply Subtype.ext
    show c 0 = x.1
    rw [hc_def]
    show R • ch 0 = x.1
    have : ch 0 = xh := by
      rw [hch_def]
      simp
    rw [this, hxh_def, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hγθ : γ θ = y := by
    apply Subtype.ext
    show c θ = y.1
    rw [hc_def]
    show R • ch θ = y.1
    have : ch θ = yh := hGq'
    rw [this, hyh_def, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  -- isometry data of `F`
  have hFiso : IsRiemannianIsometry (hyperbolicSpace n R)
      (hyperbolicSpace n R) ⇑F := mem_isometryGroup.mp hF
  obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := hFiso
  have hFsm : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ ⇑F := by
    rw [← hΦ]
    exact Φ.contMDiff
  have hFd : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ⇑F := hFsm.mdifferentiable (by simp)
  -- induced length of the hyperbola
  have hL_γ := arcLength_hyperbolicSpace_eq_integral hγd 0 θ
  have hγ_coe : (fun s => (γ s).1) = c := rfl
  rw [hγ_coe] at hL_γ
  have hspeed_c : ∀ t, Real.sqrt (η (deriv c t) (deriv c t)) = R := by
    intro t
    have hdc : deriv c t = R • deriv ch t :=
      ((((hch_smooth.differentiable (by simp)) t).hasDerivAt).const_smul
        R).deriv
    rw [hdc]
    have hsc : η (R • deriv ch t) (R • deriv ch t)
        = R ^ 2 * η (deriv ch t) (deriv ch t) := by
      simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [hsc, hspeed t, mul_one, Real.sqrt_sq hR.le]
  have hLc : (∫ t in 0..θ, Real.sqrt (η (deriv c t) (deriv c t)))
      = R * θ := by
    simp only [hspeed_c]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
  -- metric preservation transfers the length to the image curve
  have hL2 : arcLength (hyperbolicSpace n R) (⇑F ∘ γ) 0 θ
      = arcLength (hyperbolicSpace n R) γ 0 θ :=
    PreservesMetric.arcLength hpres hFd hγd 0 θ
  set amb : ℝ → E × ℝ := fun s => (F (γ s)).1 with hamb_def
  have hL3 := arcLength_hyperbolicSpace_eq_integral
    ((hFsm.comp hγ_smooth).mdifferentiable (by simp)) 0 θ
  have hFγ_coe : (fun s => ((⇑F ∘ γ) s).1) = amb := rfl
  rw [hFγ_coe] at hL3
  have hamb_smooth : ContDiff ℝ ∞ amb := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ amb :=
      (hyperboloidInclusion_contMDiff n R).comp (hFsm.comp hγ_smooth)
    exact contMDiff_iff_contDiff.mp h1
  have hamb_H : ∀ s, η (amb s) (amb s) = -R ^ 2 ∧ 0 < (amb s).2 := fun s =>
    ⟨hyperboloid_minkowskiForm_self (F (γ s)), hyperboloid_t_pos (F (γ s))⟩
  have hkey := mul_arcosh_le_length_hyperboloid hR hamb_smooth hθ'.le hamb_H
  have hamb0 : amb 0 = (F x).1 := by
    simp only [hamb_def, hγ0]
  have hambθ : amb θ = (F y).1 := by
    simp only [hamb_def, hγθ]
  rw [hamb0, hambθ] at hkey
  have hchain : R * Real.arcosh (-(η (F x).1 (F y).1) / R ^ 2) ≤ R * θ := by
    calc R * Real.arcosh (-(η (F x).1 (F y).1) / R ^ 2)
        ≤ ∫ t in 0..θ, Real.sqrt (η (deriv amb t) (deriv amb t)) := hkey
      _ = arcLength (hyperbolicSpace n R) (⇑F ∘ γ) 0 θ := hL3.symm
      _ = arcLength (hyperbolicSpace n R) γ 0 θ := hL2
      _ = ∫ t in 0..θ, Real.sqrt (η (deriv c t) (deriv c t)) := hL_γ
      _ = R * θ := hLc
  have harcosh_le : Real.arcosh (-(η (F x).1 (F y).1) / R ^ 2) ≤ θ :=
    le_of_mul_le_mul_left hchain hR
  -- identify `θ` with the hyperbolic distance parameter of `x` and `y`
  have hcoshθ : Real.cosh θ = -(η x.1 y.1) / R ^ 2 := by
    have h1 : η xh yh = -Real.cosh θ := by
      rw [← hGq', map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      rw [hxh_self, hw_tang']
      ring
    rw [hth] at h1
    rw [neg_div]
    linarith [h1]
  have hθ_eq : θ = Real.arcosh (-(η x.1 y.1) / R ^ 2) := by
    rw [← hcoshθ, Real.arcosh_cosh hθ'.le]
  rw [hθ_eq] at harcosh_le
  -- undo `arcosh` by monotonicity
  have hu'_ge : (1 : ℝ) ≤ -(η (F x).1 (F y).1) / R ^ 2 := by
    have hFx_self : η (R⁻¹ • (F x).1) (R⁻¹ • (F x).1) = -1 := by
      rw [hsmul, hyperboloid_minkowskiForm_self]
      field_simp
    have hFy_self : η (R⁻¹ • (F y).1) (R⁻¹ • (F y).1) = -1 := by
      rw [hsmul, hyperboloid_minkowskiForm_self]
      field_simp
    have hFx_pos : 0 < (R⁻¹ • (F x).1).2 :=
      mul_pos (inv_pos.mpr hR) (hyperboloid_t_pos (F x))
    have hFy_pos : 0 < (R⁻¹ • (F y).1).2 :=
      mul_pos (inv_pos.mpr hR) (hyperboloid_t_pos (F y))
    have h := one_le_neg_minkowskiForm_of_sheet hFx_self hFx_pos hFy_self
      hFy_pos
    rw [hsmul] at h
    rw [neg_div]
    exact h
  have hu_ge2 : (1 : ℝ) ≤ -(η x.1 y.1) / R ^ 2 := by
    rw [hth] at hu_ge
    rw [neg_div]
    exact hu_ge
  have hle := (Real.arcosh_le_arcosh (by linarith) (by linarith)).mp
    harcosh_le
  have h := mul_le_mul_of_nonneg_right hle hR2.le
  rw [div_mul_cancel₀ _ hR2.ne', div_mul_cancel₀ _ hR2.ne'] at h
  linarith [h]

/-- **Math.** A Riemannian isometry of hyperbolic space **preserves Minkowski
pairings of hyperboloid points**: both `F` and `F⁻¹` do not decrease them, so
they are preserved. Replaces the uniqueness principle (Petersen Prop. 5.6.2)
by the length-minimization characterization of hyperbolas
(Exercise 1.6.21). -/
theorem minkowskiForm_eq_of_mem_isometryGroup_hyperbolicSpace
    [Fact (0 < R)] {F : Equiv.Perm (hyperboloid n R)}
    (hF : F ∈ IsometryGroup (hyperbolicSpace n R)) (x y : hyperboloid n R) :
    η (F x).1 (F y).1 = η x.1 y.1 := by
  have hFinv : F⁻¹ ∈ IsometryGroup (hyperbolicSpace n R) :=
    (IsometryGroup (hyperbolicSpace n R)).inv_mem hF
  have h1 := minkowskiForm_le_of_mem_isometryGroup_hyperbolicSpace hF x y
  have h2 := minkowskiForm_le_of_mem_isometryGroup_hyperbolicSpace hFinv
    (F x) (F y)
  have hz : ∀ z : hyperboloid n R, F⁻¹ (F z) = z := fun z =>
    Equiv.symm_apply_apply F z
  rw [hz x, hz y] at h2
  linarith [h1, h2]

end HyperbolicDistance

/-! ### The linear extension of a hyperbolic isometry

Petersen's matrix construction, with the uniqueness principle (Petersen
Prop. 5.6.2, out of Ch. 1 scope) replaced by bilinear algebra: a Riemannian
isometry `F` of `Hⁿ(R)` preserves all Minkowski pairings of hyperboloid
points (`minkowskiForm_eq_of_mem_isometryGroup_hyperbolicSpace`). The
`n + 1` hyperboloid points `W₀ = (0, R)` and `Wᵢ = (R sinh 1 · eᵢ, R cosh 1)`
form a basis of `ℝ^{n,1}` (`hyperboloidSpanningBasis`), so `Wₖ ↦ F(Wₖ)`
extends to a linear map agreeing with `F` on the basis; pairing
preservation extends bilinearly, nondegeneracy of the Minkowski form makes
the extension bijective and forces it to agree with `F` on the whole
hyperboloid, and orthochronicity follows because every upper timelike
vector is a positive multiple of a hyperboloid point. -/

section HyperbolicLinearExtension

variable {n : ℕ} {R : ℝ}

local notation "η" => minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ

/-- **Math.** Petersen Example 1.3.3 (ingredient): the spanning family of
hyperboloid points, `W₀ = (0, R)` and `Wᵢ = (R sinh 1 · eᵢ, R cosh 1)` for
`i = 1, …, n`. These are `n + 1` points of `Hⁿ(R)` forming a basis of
`ℝ^{n,1}` (`hyperboloidSpanningBasis`). -/
def hyperboloidSpanningFamily (n : ℕ) (R : ℝ) :
    Fin n ⊕ Unit → EuclideanSpace ℝ (Fin n) × ℝ :=
  Sum.elim
    (fun i => ((R * Real.sinh 1) • EuclideanSpace.single i (1 : ℝ), R * Real.cosh 1))
    fun _ => (0, R)

/-- **Math.** The spanning family lies on the hyperboloid:
`‖R sinh 1 · eᵢ‖² − (R cosh 1)² = R²(sinh²1 − cosh²1) = −R²` and
`‖0‖² − R² = −R²`, with positive last coordinates `R cosh 1` and `R`. -/
theorem hyperboloidSpanningFamily_mem (hR : 0 < R) (k : Fin n ⊕ Unit) :
    ‖(hyperboloidSpanningFamily n R k).1‖ ^ 2
        - (hyperboloidSpanningFamily n R k).2 ^ 2 = -R ^ 2
      ∧ 0 < (hyperboloidSpanningFamily n R k).2 := by
  cases k with
  | inl i =>
    constructor
    · simp only [hyperboloidSpanningFamily, Sum.elim_inl, norm_smul,
        Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one,
        mul_pow, sq_abs]
      nlinarith [Real.cosh_sq 1]
    · simp only [hyperboloidSpanningFamily, Sum.elim_inl]
      exact mul_pos hR (Real.cosh_pos 1)
  | inr u =>
    constructor
    · simp [hyperboloidSpanningFamily]
    · simpa [hyperboloidSpanningFamily] using hR

/-- The spanning family, as points of `Hⁿ(R)`. -/
def hyperboloidSpanningPoint (n : ℕ) (R : ℝ) [Fact (0 < R)]
    (k : Fin n ⊕ Unit) : hyperboloid n R :=
  ⟨hyperboloidSpanningFamily n R k, hyperboloidSpanningFamily_mem Fact.out k⟩

@[simp]
theorem hyperboloidSpanningPoint_coe [Fact (0 < R)] (k : Fin n ⊕ Unit) :
    (hyperboloidSpanningPoint n R k).1 = hyperboloidSpanningFamily n R k :=
  rfl

/-- **Math.** The spanning family is linearly independent: the first
components force the coefficients of the `Wᵢ` (the `eᵢ` are independent and
`R sinh 1 ≠ 0`), and the second component then forces the coefficient of
`W₀` (as `R ≠ 0`). -/
theorem linearIndependent_hyperboloidSpanningFamily (hR : 0 < R) :
    LinearIndependent ℝ (hyperboloidSpanningFamily n R) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsplit : (∑ i : Fin n, g (Sum.inl i) • hyperboloidSpanningFamily n R (Sum.inl i))
      + ∑ u : Unit, g (Sum.inr u) • hyperboloidSpanningFamily n R (Sum.inr u) = 0 := by
    rw [Fintype.sum_sum_type] at hg
    exact hg
  have h1 : ∑ i : Fin n,
      (g (Sum.inl i) * (R * Real.sinh 1)) • EuclideanSpace.single i (1 : ℝ) = 0 := by
    have h := congrArg Prod.fst hsplit
    simpa [hyperboloidSpanningFamily, Prod.fst_sum, smul_smul] using h
  have hRs : R * Real.sinh 1 ≠ 0 :=
    (mul_pos hR (Real.sinh_pos_iff.mpr one_pos)).ne'
  have hgl : ∀ j : Fin n, g (Sum.inl j) = 0 := by
    have hli := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    intro j
    have hz := hli (fun i => g (Sum.inl i) * (R * Real.sinh 1))
      (by simpa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using h1) j
    exact (mul_eq_zero.mp hz).resolve_right hRs
  have h2 : (∑ i : Fin n, g (Sum.inl i) * (R * Real.cosh 1)) + g (Sum.inr ()) * R = 0 := by
    have h := congrArg Prod.snd hsplit
    simpa [hyperboloidSpanningFamily, Prod.snd_sum, smul_eq_mul] using h
  have hgr : g (Sum.inr ()) = 0 := by
    rw [Finset.sum_eq_zero fun i _ => by rw [hgl i, zero_mul], zero_add] at h2
    exact (mul_eq_zero.mp h2).resolve_right hR.ne'
  intro k
  cases k with
  | inl i => exact hgl i
  | inr u => cases u; exact hgr

/-- **Math.** Petersen Example 1.3.3 (ingredient): the spanning family of
hyperboloid points is a **basis** of `ℝ^{n,1}` — `n + 1` linearly
independent vectors in the `(n + 1)`-dimensional Minkowski space. -/
noncomputable def hyperboloidSpanningBasis (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    Basis (Fin n ⊕ Unit) ℝ (EuclideanSpace ℝ (Fin n) × ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_hyperboloidSpanningFamily (n := n) (R := R) Fact.out)
    (by simp [Module.finrank_prod, finrank_euclideanSpace])

@[simp]
theorem hyperboloidSpanningBasis_apply [Fact (0 < R)] (k : Fin n ⊕ Unit) :
    hyperboloidSpanningBasis n R k = hyperboloidSpanningFamily n R k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

/-- **Math.** Petersen Example 1.3.3, the "only if" direction: a Riemannian
isometry of `Hⁿ(R)` is the restriction of an orthochronous Minkowski
isometry. Since `F` preserves Minkowski pairings of hyperboloid points
(`minkowskiForm_eq_of_mem_isometryGroup_hyperbolicSpace`), the linear map
`L₀` sending the spanning basis `Wₖ` to `F(Wₖ)` (`Basis.constr`) preserves
the Minkowski form (bilinear extension, `LinearMap.ext_basis`), is
injective by nondegeneracy (`minkowskiForm_self_flip_ne_zero`) hence
bijective in finite dimension, agrees with `F` everywhere on `Hⁿ(R)` (pair
the difference against the image basis `L₀(Wₖ) = F(Wₖ)` and use
nondegeneracy again), and is orthochronous because every upper timelike
vector is a positive multiple of a hyperboloid point. -/
theorem exists_orthochronous_of_mem_isometryGroup_hyperbolicSpace [Fact (0 < R)]
    {F : Equiv.Perm (hyperboloid n R)}
    (hF : F ∈ IsometryGroup (hyperbolicSpace n R)) :
    ∃ L ∈ orthochronousMinkowskiGroup (EuclideanSpace ℝ (Fin n)),
      ∀ x : hyperboloid n R, (F x).1 = L x.1 := by
  have hR : (0 : ℝ) < R := Fact.out
  set B : Basis (Fin n ⊕ Unit) ℝ (EuclideanSpace ℝ (Fin n) × ℝ) :=
    hyperboloidSpanningBasis n R with hBdef
  set W : Fin n ⊕ Unit → hyperboloid n R := hyperboloidSpanningPoint n R with hWdef
  have hBW : ∀ k, B k = (W k).1 := fun k => hyperboloidSpanningBasis_apply k
  set L₀ : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
    B.constr ℝ fun k => (F (W k)).1 with hL₀def
  have hL₀B : ∀ k, L₀ (B k) = (F (W k)).1 := fun k => B.constr_basis ℝ _ k
  -- `L₀` preserves the Minkowski form: bilinear extension from basis pairs
  have hpair : ∀ v u, η (L₀ v) (L₀ u) = η v u := by
    let ηₗ : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun v u => η v u)
        (fun v v' u => by
          show (η (v + v')) u = (η v) u + (η v') u
          rw [map_add, ContinuousLinearMap.add_apply])
        (fun c v u => by
          show (η (c • v)) u = c • (η v) u
          rw [map_smul, ContinuousLinearMap.smul_apply])
        (fun v u u' => map_add (η v) u u')
        (fun c v u => map_smul (η v) c u)
    have hext : ηₗ.compl₁₂ L₀ L₀ = ηₗ := by
      refine LinearMap.ext_basis B B fun i j => ?_
      simp only [LinearMap.compl₁₂_apply, LinearMap.mk₂_apply, ηₗ]
      rw [hL₀B i, hL₀B j, hBW i, hBW j]
      exact minkowskiForm_eq_of_mem_isometryGroup_hyperbolicSpace hF (W i) (W j)
    intro v u
    have h := LinearMap.congr_fun (LinearMap.congr_fun hext v) u
    simpa [LinearMap.compl₁₂_apply, LinearMap.mk₂_apply, ηₗ] using h
  -- injective by nondegeneracy, hence bijective in finite dimension
  have hinj : Function.Injective L₀ := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have hv0 : L₀ v = 0 := LinearMap.mem_ker.mp hv
    by_contra hne
    refine minkowskiForm_self_flip_ne_zero (EuclideanSpace ℝ (Fin n)) ℝ hne ?_
    rw [← hpair v (v.1, -v.2), hv0]
    simp
  have hbij : Function.Bijective L₀ :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  set L₀e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
    LinearEquiv.ofBijective L₀ hbij with hL₀e
  -- `F` agrees with `L₀` on the whole hyperboloid
  have hagree : ∀ x : hyperboloid n R, (F x).1 = L₀ x.1 := by
    intro x
    have hzk : ∀ k, η ((F x).1 - L₀ x.1) (L₀ (B k)) = 0 := by
      intro k
      have e1 : η (F x).1 (L₀ (B k)) = η x.1 (B k) := by
        rw [hL₀B k, hBW k]
        exact minkowskiForm_eq_of_mem_isometryGroup_hyperbolicSpace hF x (W k)
      have e2 : η (L₀ x.1) (L₀ (B k)) = η x.1 (B k) := hpair _ _
      rw [map_sub, ContinuousLinearMap.sub_apply, e1, e2, sub_self]
    have hzall : ∀ u, η ((F x).1 - L₀ x.1) u = 0 := by
      intro u
      have hrepr := (B.map L₀e).sum_repr u
      calc η ((F x).1 - L₀ x.1) u
          = η ((F x).1 - L₀ x.1) (∑ k, (B.map L₀e).repr u k • (B.map L₀e) k) := by
            rw [hrepr]
        _ = ∑ k, (B.map L₀e).repr u k * η ((F x).1 - L₀ x.1) ((B.map L₀e) k) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun k _ => by rw [map_smul]; rfl
        _ = 0 := Finset.sum_eq_zero fun k _ => by
            have hbk : (B.map L₀e) k = L₀ (B k) := by rw [Basis.map_apply]; rfl
            rw [hbk, hzk k, mul_zero]
    by_contra hne
    have hnz : (F x).1 - L₀ x.1 ≠ 0 := sub_ne_zero_of_ne hne
    exact minkowskiForm_self_flip_ne_zero (EuclideanSpace ℝ (Fin n)) ℝ hnz
      (hzall (((F x).1 - L₀ x.1).1, -((F x).1 - L₀ x.1).2))
  -- upgrade to a continuous linear equivalence and conclude
  set L : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
    L₀e.toContinuousLinearEquiv with hLdef
  have hLapp : ∀ v, L v = L₀ v := fun v => rfl
  refine ⟨L, ?_, fun x => (hagree x).trans (hLapp x.1).symm⟩
  rw [mem_orthochronousMinkowskiGroup]
  constructor
  · intro v
    rw [hLapp v]
    exact hpair v v
  · -- orthochronicity: normalize the timelike vector onto the hyperboloid
    intro v hvt hv2
    have hvv : η v v < 0 := hvt
    set s : ℝ := Real.sqrt (-(η v v)) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
    have hs2 : s ^ 2 = -(η v v) := Real.sq_sqrt (by linarith)
    set c : ℝ := R / s with hc
    have hcpos : 0 < c := div_pos hR hspos
    have hsc : η (c • v) (c • v) = c ^ 2 * η v v := by
      simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      ring
    have hcv_eq : ‖(c • v).1‖ ^ 2 - (c • v).2 ^ 2 = -R ^ 2 := by
      rw [← minkowskiForm_self_real (EuclideanSpace ℝ (Fin n)) (c • v), hsc, hc, div_pow]
      rw [hs2]
      field_simp
      rw [div_self (ne_of_lt hvv)]
    have hcv_pos : 0 < (c • v).2 := by
      have h : (c • v).2 = c * v.2 := rfl
      rw [h]
      exact mul_pos hcpos hv2
    have hLcv : 0 < (L₀ (c • v)).2 := by
      have h := hagree ⟨c • v, hcv_eq, hcv_pos⟩
      rw [← h]
      exact hyperboloid_t_pos (F ⟨c • v, hcv_eq, hcv_pos⟩)
    rw [map_smul L₀ c v] at hLcv
    have h2 : (c • L₀ v).2 = c * (L₀ v).2 := rfl
    rw [h2] at hLcv
    have hfinal : 0 < (L₀ v).2 := by nlinarith [hLcv, hcpos]
    rw [hLapp v]
    exact hfinal

end HyperbolicLinearExtension

/-- **Math.** Petersen Example 1.3.3: the isometry group of hyperbolic space
is realized inside the orthochronous Lorentz group:
`Iso(Hⁿ(R)) = O⁺(n, 1)`. A permutation `F` of the hyperboloid branch
`Hⁿ(R) ⊂ ℝ^{n,1}` is a Riemannian isometry of `(Hⁿ(R), g_{Hⁿ(R)})` iff it is
the restriction of an orthochronous Minkowski isometry `L ∈ O⁺(n, 1)`.

The "if" direction is
`mem_isometryGroup_hyperbolicSpace_of_orthochronous`. The "only if"
direction is `exists_orthochronous_of_mem_isometryGroup_hyperbolicSpace`:
in place of Petersen's matrix construction (which invokes the uniqueness
principle Prop. 5.6.2, out of Ch. 1 scope), the isometry preserves
Minkowski pairings of hyperboloid points by the length-minimization
property of hyperbolas (Exercise 1.6.21), and extends linearly over the
spanning basis `hyperboloidSpanningBasis` of hyperboloid points.

Petersen additionally notes that the isotropy group of `Re_{n+1}` is
identified with `O(n)`; that quotient identification is not formalized
here. Transitivity of `O⁺(n, 1)` on `Hⁿ(R)` is
`isHomogeneous_hyperbolicSpace` below. -/
theorem isometryGroup_hyperbolicSpace {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (F : Equiv.Perm (hyperboloid n R)) :
    F ∈ IsometryGroup (hyperbolicSpace n R) ↔
      ∃ L ∈ orthochronousMinkowskiGroup (EuclideanSpace ℝ (Fin n)),
        ∀ x : hyperboloid n R, (F x).1 = L x.1 := by
  constructor
  · exact exists_orthochronous_of_mem_isometryGroup_hyperbolicSpace
  · rintro ⟨L, hL, hFL⟩
    exact mem_isometryGroup_hyperbolicSpace_of_orthochronous F hL hFL

/-! ### Transitivity of `O⁺(n, 1)` on `Hⁿ(R)`

The **hyperbolic translation** (Lorentz boost) taking the base point
`(0, R) = Re_{n+1}` to a prescribed point `p ∈ Hⁿ(R)`: with
`a = ⟪p₁, x⟫`, it is

  `T_p(x, t) = (x + (a / (R(p_t + R)) + t/R) p₁, (a + t p_t)/R)`,

the standard boost fixing the orthogonal complement of `p₁` (written in the
singularity-free form valid also at `p₁ = 0`, where it is the identity). -/

/-- **Math.** Petersen Example 1.3.3 (ingredient): the hyperbolic
translation (Lorentz boost) associated to a point `q = (q₁, q_t)` of
`Hⁿ(R)`, as a continuous linear map on ambient Minkowski space. It maps
`(0, R) ↦ q` and preserves the Minkowski form
(`minkowskiForm_hyperbolicTranslationCLM`). -/
def hyperbolicTranslationCLM {n : ℕ} (R : ℝ) (q : EuclideanSpace ℝ (Fin n) × ℝ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ
    + ((R * (q.2 + R))⁻¹ • ((innerSL ℝ q.1).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ))
        + R⁻¹ • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ).smulRight q.1).prod
  (R⁻¹ • ((innerSL ℝ q.1).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
      + q.2 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ))

@[simp]
theorem hyperbolicTranslationCLM_apply {n : ℕ} (R : ℝ)
    (q v : EuclideanSpace ℝ (Fin n) × ℝ) :
    hyperbolicTranslationCLM R q v
      = (v.1 + ((R * (q.2 + R))⁻¹ * ⟪q.1, v.1⟫ + R⁻¹ * v.2) • q.1,
          R⁻¹ * (⟪q.1, v.1⟫ + q.2 * v.2)) := by
  simp [hyperbolicTranslationCLM, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_add]

/-- **Math.** The boost at the reflected point `(-q₁, q_t)` inverts the
boost at `q` — the two-by-two boost block `[[q_t/R, ‖q₁‖/R], [‖q₁‖/R, q_t/R]]`
has determinant `(q_t² - ‖q₁‖²)/R² = 1`. -/
theorem hyperbolicTranslationCLM_neg_comp {n : ℕ} {R : ℝ} (hR : 0 < R)
    {q : EuclideanSpace ℝ (Fin n) × ℝ} (hq : ‖q.1‖ ^ 2 - q.2 ^ 2 = -R ^ 2)
    (hqt : 0 < q.2) (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    hyperbolicTranslationCLM R (-q.1, q.2) (hyperbolicTranslationCLM R q v) = v := by
  obtain ⟨x, t⟩ := v
  have hs : ⟪q.1, q.1⟫ = q.2 ^ 2 - R ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    linarith
  have hRne : R ≠ 0 := hR.ne'
  have hDne : q.2 + R ≠ 0 := by positivity
  simp only [hyperbolicTranslationCLM_apply, inner_neg_left, inner_add_right,
    real_inner_smul_right, hs]
  refine Prod.ext ?_ ?_
  · show _ + _ • (-q.1) = x
    match_scalars <;> (field_simp; try ring)
  · show R⁻¹ * _ = t
    field_simp
    ring

/-- **Math.** Petersen Example 1.3.3: the hyperbolic translation taking the
base point `(0, R) ∈ Hⁿ(R)` to `p ∈ Hⁿ(R)`, as a continuous linear
automorphism of Minkowski space; the inverse is the boost at the reflected
point `(-p₁, p_t)`. -/
def hyperbolicTranslation {n : ℕ} {R : ℝ} [Fact (0 < R)] (p : hyperboloid n R) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (hyperbolicTranslationCLM R p.1)
    (hyperbolicTranslationCLM R (-p.1.1, p.1.2))
    (fun v => hyperbolicTranslationCLM_neg_comp Fact.out p.2.1 p.2.2 v)
    (fun v => by
      have h := hyperbolicTranslationCLM_neg_comp (q := (-p.1.1, p.1.2)) Fact.out
        (by simpa using p.2.1) p.2.2 v
      simpa only [neg_neg, Prod.mk.eta] using h)

@[simp]
theorem hyperbolicTranslation_apply {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (p : hyperboloid n R) (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    hyperbolicTranslation p v = hyperbolicTranslationCLM R p.1 v :=
  rfl

/-- **Math.** The boost preserves the Minkowski form — the hyperbolic
`cosh²−sinh² = 1` computation, using `‖q₁‖² = q_t² - R²`. -/
theorem minkowskiForm_hyperbolicTranslationCLM {n : ℕ} {R : ℝ} (hR : 0 < R)
    {q : EuclideanSpace ℝ (Fin n) × ℝ} (hq : ‖q.1‖ ^ 2 - q.2 ^ 2 = -R ^ 2)
    (hqt : 0 < q.2) (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ (hyperbolicTranslationCLM R q v)
        (hyperbolicTranslationCLM R q v)
      = minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ v v := by
  obtain ⟨x, t⟩ := v
  have hs : ⟪q.1, q.1⟫ = q.2 ^ 2 - R ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    linarith
  have hnq : ‖q.1‖ ^ 2 = q.2 ^ 2 - R ^ 2 := by linarith
  have hRne : R ≠ 0 := hR.ne'
  have hDne : q.2 + R ≠ 0 := by positivity
  rw [hyperbolicTranslationCLM_apply, minkowskiForm_self_real, minkowskiForm_self_real]
  have hexp : ‖x + ((R * (q.2 + R))⁻¹ * ⟪q.1, x⟫ + R⁻¹ * t) • q.1‖ ^ 2
      = ‖x‖ ^ 2 + 2 * (((R * (q.2 + R))⁻¹ * ⟪q.1, x⟫ + R⁻¹ * t) * ⟪q.1, x⟫)
        + ((R * (q.2 + R))⁻¹ * ⟪q.1, x⟫ + R⁻¹ * t) ^ 2 * ‖q.1‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm x q.1, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs]
  show ‖x + _ • q.1‖ ^ 2 - (R⁻¹ * (⟪q.1, x⟫ + q.2 * t)) ^ 2 = ‖x‖ ^ 2 - t ^ 2
  rw [hexp, hnq]
  field_simp
  ring

/-- **Math.** The boost maps the upper time cone into itself: for an upper
timelike `v = (x, t)` — so `‖x‖ < t` — Cauchy–Schwarz and `‖q₁‖ < q_t` give
`⟪q₁, x⟫ + q_t t ≥ -‖q₁‖‖x‖ + q_t t > 0`. -/
theorem hyperbolicTranslationCLM_snd_pos {n : ℕ} {R : ℝ} (hR : 0 < R)
    {q : EuclideanSpace ℝ (Fin n) × ℝ} (hq : ‖q.1‖ ^ 2 - q.2 ^ 2 = -R ^ 2)
    (hqt : 0 < q.2) {v : EuclideanSpace ℝ (Fin n) × ℝ}
    (hv : minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ v v < 0) (hv2 : 0 < v.2) :
    0 < (hyperbolicTranslationCLM R q v).2 := by
  rw [minkowskiForm_self_real] at hv
  rw [hyperbolicTranslationCLM_apply]
  have habs := abs_real_inner_le_norm q.1 v.1
  have h1 : -(‖q.1‖ * ‖v.1‖) ≤ ⟪q.1, v.1⟫ := neg_le_of_abs_le habs
  have hxlt : ‖v.1‖ < v.2 := by nlinarith [norm_nonneg v.1]
  have hqlt : ‖q.1‖ < q.2 := by nlinarith [norm_nonneg q.1, sq_nonneg R]
  have hprod : ‖q.1‖ * ‖v.1‖ < q.2 * v.2 := by
    nlinarith [norm_nonneg q.1, norm_nonneg v.1]
  have hpos : 0 < ⟪q.1, v.1⟫ + q.2 * v.2 := by linarith
  show 0 < R⁻¹ * (⟪q.1, v.1⟫ + q.2 * v.2)
  exact mul_pos (inv_pos.mpr hR) hpos

/-- **Math.** The hyperbolic translation at `p` is an orthochronous
Minkowski isometry: `T_p ∈ O⁺(n, 1)`. -/
theorem hyperbolicTranslation_mem {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (p : hyperboloid n R) :
    hyperbolicTranslation p ∈ orthochronousMinkowskiGroup (EuclideanSpace ℝ (Fin n)) := by
  have hR : (0 : ℝ) < R := Fact.out
  constructor
  · intro v
    rw [hyperbolicTranslation_apply]
    exact minkowskiForm_hyperbolicTranslationCLM hR p.2.1 p.2.2 v
  · intro v hv hv2
    rw [hyperbolicTranslation_apply]
    exact hyperbolicTranslationCLM_snd_pos hR p.2.1 p.2.2 hv hv2

/-- **Math.** The hyperbolic translation takes the base point
`Re_{n+1} = (0, R)` to `p`. -/
theorem hyperbolicTranslation_apply_base {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (p : hyperboloid n R) :
    hyperbolicTranslation p ((0 : EuclideanSpace ℝ (Fin n)), R) = p.1 := by
  have hR : (0 : ℝ) < R := Fact.out
  rw [hyperbolicTranslation_apply, hyperbolicTranslationCLM_apply]
  refine Prod.ext ?_ ?_
  · show (0 : EuclideanSpace ℝ (Fin n))
        + ((R * (p.1.2 + R))⁻¹ * ⟪p.1.1, (0 : EuclideanSpace ℝ (Fin n))⟫ + R⁻¹ * R) • p.1.1
      = p.1.1
    rw [inner_zero_right, mul_zero, zero_add, inv_mul_cancel₀ hR.ne', zero_add, one_smul]
  · show R⁻¹ * (⟪p.1.1, (0 : EuclideanSpace ℝ (Fin n))⟫ + p.1.2 * R) = p.1.2
    rw [inner_zero_right, zero_add, mul_comm p.1.2 R, ← mul_assoc,
      inv_mul_cancel₀ hR.ne', one_mul]

/-- **Math.** Petersen Example 1.3.3: `O⁺(n, 1)` acts transitively on
`Hⁿ(R)`: the boost `T_q ∘ T_p⁻¹` is orthochronous and maps `p` to `q`
through the base point `(0, R)`. -/
theorem exists_orthochronous_apply_eq {n : ℕ} {R : ℝ} [Fact (0 < R)]
    (p q : hyperboloid n R) :
    ∃ L ∈ orthochronousMinkowskiGroup (EuclideanSpace ℝ (Fin n)), L p.1 = q.1 := by
  refine ⟨hyperbolicTranslation q * (hyperbolicTranslation p)⁻¹,
    mul_mem (hyperbolicTranslation_mem q) (inv_mem (hyperbolicTranslation_mem p)), ?_⟩
  have h1 : ((hyperbolicTranslation p)⁻¹ :
        (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)) p.1
      = ((0 : EuclideanSpace ℝ (Fin n)), R) := by
    show (hyperbolicTranslation p).symm p.1 = _
    rw [ContinuousLinearEquiv.symm_apply_eq]
    exact (hyperbolicTranslation_apply_base p).symm
  show hyperbolicTranslation q
      (((hyperbolicTranslation p)⁻¹ :
        (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)) p.1) = q.1
  rw [h1]
  exact hyperbolicTranslation_apply_base q

/-- **Math.** Petersen Example 1.3.3: hyperbolic space is **homogeneous** —
`O⁺(n, 1)` acts transitively on `Hⁿ(R)` by Riemannian isometries
(`mem_isometryGroup_hyperbolicSpace_of_orthochronous` applied to the
restriction of the transitive boost `exists_orthochronous_apply_eq`).
Sorry-free: it only uses the fully proved direction of Example 1.3.3. -/
theorem isHomogeneous_hyperbolicSpace (n : ℕ) (R : ℝ) [Fact (0 < R)] :
    IsHomogeneous (hyperbolicSpace n R) := by
  intro p q
  obtain ⟨L, hL, hLpq⟩ := exists_orthochronous_apply_eq p q
  refine ⟨⟨fun x => ⟨L x.1, orthochronous_maps_hyperboloid hL x⟩,
      fun x => ⟨(L⁻¹ : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
          (EuclideanSpace ℝ (Fin n) × ℝ)) x.1,
        orthochronous_maps_hyperboloid (inv_mem hL) x⟩,
      fun x => Subtype.ext (L.symm_apply_apply x.1),
      fun x => Subtype.ext (L.apply_symm_apply x.1)⟩,
    mem_isometryGroup_hyperbolicSpace_of_orthochronous _ hL fun _ => rfl,
    Subtype.ext hLpq⟩

end HyperbolicIsometries

end PetersenLib
