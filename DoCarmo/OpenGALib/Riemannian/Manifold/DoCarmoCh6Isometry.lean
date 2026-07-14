import OpenGALib.Riemannian.Manifold.DoCarmoCh6Koszul
import OpenGALib.Riemannian.Manifold.DoCarmoCh6Eigen
import OpenGALib.Riemannian.Manifold.DoCarmoCh4SectionalPair
import OpenGALib.Riemannian.Manifold.EuclideanOpens
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# do Carmo Chapter 6 §2 — isometries of immersed patches and the Theorema Egregium

do Carmo's Remark 2.7: for a surface `M² ⊆ ℝ³` the product `λ₁λ₂` of the
principal curvatures — the Gaussian curvature — is *intrinsic*: it is invariant
under isometries of the surface. In the identified picture of `DCImmersedPatch`
(where a patch is a tangent distribution on an open subset of the flat ambient
space), an isometry between two patches is a diffeomorphism `φ` of the ambient
opens carrying the tangent distribution of one patch onto that of the other and
preserving the induced inner product on tangent vectors (`DCPatchIsometry`).

This file builds the naturality theory of such isometries:

* `opensMapExt`, `opensFDeriv` — the model-space representative `φ̂` of a map
  between Euclidean opens and its derivative `dφ_p`, with the chain rule
  (`fderiv_extendZero_comp`) and inverse-function identities
  (`opensFDeriv_symm_comp`);
* `opensPushforward` — the pushforward `φ_*X = dφ ∘ X ∘ φ⁻¹` of a smooth
  vector field along a diffeomorphism of Euclidean opens, with naturality of
  the directional derivative (`dir_opensPushforward`) and of the Lie bracket
  (`DCLieBracket_opensPushforward`, by Schwarz symmetry of `d²φ̂`);
* `DCPatchIsometry` — the leafwise isometry, under which the pushforward
  preserves tangent fields and their inner products, and — via the Koszul
  formula `inducedCov_koszul`, since every ingredient of the Koszul right-hand
  side is leafwise-intrinsic — intertwines the induced connections
  (`inducedCov_opensPushforward`) and their curvatures
  (`inducedCurvature_opensPushforward`, `inducedCurvature_inner_opensPushforward`);
* `gaussFormAt` — the pointwise Gauss quadrilinear form
  `(x,y,z,t) ↦ ⟨B(y,t),B(x,z)⟩ − ⟨B(x,t),B(y,z)⟩` on the tangent plane, an
  algebraic curvature form (`isAlgCurvatureForm_gaussFormAt`) computing
  `⟨R(X,Y)Z,T⟩` in a flat ambient (`inducedCurvature_inner_eq_gaussFormAt`);
* `DCPatchIsometry.theorema_egregium` — **Theorema Egregium**: for isometric
  two-dimensional hypersurface patches in flat ambients, the product of the
  principal curvatures is the same at corresponding points.

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2, Remark 2.7.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open TopologicalSpace

/- As in `DoCarmoCh6Sphere`: the file works through the canonical identification
`TangentSpace 𝓘(ℝ, F) q = F` on open submanifolds of the vector-space model. -/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Riemannian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  {s : Opens F} {t : Opens G}

/-! ### Maps between Euclidean opens and their derivatives -/

/-- **Math.** The model-space representative `φ̂ : F → G` of a map `φ` between
Euclidean opens: the zero-extension of `p ↦ φ(p)` read in the ambient vector
spaces. On `s` it agrees with `φ`; its `fderiv` at points of `s` is the
derivative of `φ`. -/
def opensMapExt (φ : ↥s → ↥t) : F → G :=
  s.extendZero fun p => ((φ p : ↥t) : G)

omit [InnerProductSpace ℝ F] [CompleteSpace F] [InnerProductSpace ℝ G] [CompleteSpace G] in
@[simp] theorem opensMapExt_val (φ : ↥s → ↥t) (q : ↥s) :
    opensMapExt φ q.val = ((φ q : ↥t) : G) :=
  s.extendZero_val _ q

omit [InnerProductSpace ℝ F] [CompleteSpace F] [InnerProductSpace ℝ G] [CompleteSpace G] in
theorem opensMapExt_apply_of_mem (φ : ↥s → ↥t) {x : F} (hx : x ∈ s) :
    opensMapExt φ x = ((φ ⟨x, hx⟩ : ↥t) : G) :=
  s.extendZero_apply_of_mem _ hx

omit [CompleteSpace F] [CompleteSpace G] in
theorem contMDiff_val_comp {φ : ↥s → ↥t}
    (hφ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ φ) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ (fun p => ((φ p : ↥t) : G)) :=
  contMDiff_subtype_val.comp hφ

omit [CompleteSpace F] [CompleteSpace G] in
theorem contDiffAt_opensMapExt {φ : ↥s → ↥t}
    (hφ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ φ) (p : ↥s) :
    ContDiffAt ℝ ∞ (opensMapExt φ) p.val :=
  contMDiffAt_opens_iff_extendZero.mp (contMDiff_val_comp hφ p)

/-- **Math.** The derivative `dφ_p : F → G` of a map between Euclidean opens,
computed on the model-space representative. -/
def opensFDeriv (φ : ↥s → ↥t) (p : ↥s) : F →L[ℝ] G :=
  fderiv ℝ (opensMapExt φ) p.val

section ChainRule

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']

omit [InnerProductSpace ℝ F] [CompleteSpace F] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedSpace ℝ G'] in
/-- **Math.** Zero-extensions compose along maps of opens, near points of the domain. -/
theorem extendZero_comp_eventuallyEq (g : ↥t → G') (φ : ↥s → ↥t) (p : ↥s) :
    s.extendZero (fun x => g (φ x))
      =ᶠ[𝓝 p.val] fun x => t.extendZero g (opensMapExt φ x) := by
  filter_upwards [s.isOpen.mem_nhds p.2] with x hx
  rw [s.extendZero_apply_of_mem _ hx, opensMapExt_apply_of_mem φ hx,
    t.extendZero_val]

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** The chain rule for maps of Euclidean opens:
`d(g ∘ φ)_p = dg_{φ(p)} ∘ dφ_p`, on model-space representatives. -/
theorem fderiv_extendZero_comp {g : ↥t → G'}
    (hg : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, G') ∞ g) {φ : ↥s → ↥t}
    (hφ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ φ) (p : ↥s) :
    fderiv ℝ (s.extendZero fun x => g (φ x)) p.val
      = (fderiv ℝ (t.extendZero g) ((φ p : ↥t) : G)).comp (opensFDeriv φ p) := by
  rw [(extendZero_comp_eventuallyEq g φ p).fderiv_eq]
  have hgd : DifferentiableAt ℝ (t.extendZero g) (opensMapExt φ p.val) := by
    rw [opensMapExt_val]
    exact (contMDiffAt_opens_iff_extendZero.mp (hg (φ p))).differentiableAt
      (by simp)
  have hφd : DifferentiableAt ℝ (opensMapExt φ) p.val :=
    (contDiffAt_opensMapExt hφ p).differentiableAt (by simp)
  rw [show (fun x => t.extendZero g (opensMapExt φ x))
      = (t.extendZero g) ∘ (opensMapExt φ) from rfl,
    fderiv_comp p.val hgd hφd, opensMapExt_val]
  rfl

end ChainRule

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** Derivatives of inverse maps compose to the identity:
`dψ_{φ(p)} ∘ dφ_p = id` for `ψ ∘ φ = id`. -/
theorem opensFDeriv_symm_comp {φ : ↥s → ↥t} {ψ : ↥t → ↥s}
    (hφ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ ψ)
    (hinv : ∀ p, ψ (φ p) = p) (p : ↥s) :
    (opensFDeriv ψ (φ p)).comp (opensFDeriv φ p) = ContinuousLinearMap.id ℝ F := by
  have h1 : fderiv ℝ (s.extendZero fun x => ((ψ (φ x) : ↥s) : F)) p.val
      = (fderiv ℝ (t.extendZero fun y => ((ψ y : ↥s) : F)) ((φ p : ↥t) : G)).comp
          (opensFDeriv φ p) :=
    fderiv_extendZero_comp (g := fun y => ((ψ y : ↥s) : F))
      (contMDiff_val_comp hψ) hφ p
  have h2 : (fun x : ↥s => ((ψ (φ x) : ↥s) : F)) = fun x : ↥s => (x : F) := by
    funext x
    rw [hinv]
  have h3 : s.extendZero (fun x : ↥s => (x : F)) =ᶠ[𝓝 p.val] id := by
    filter_upwards [s.isOpen.mem_nhds p.2] with x hx
    rw [s.extendZero_apply_of_mem _ hx]
    rfl
  rw [h2, h3.fderiv_eq, fderiv_id] at h1
  exact h1.symm

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** Pointwise form of `opensFDeriv_symm_comp`: `dψ_{φ(p)}(dφ_p v) = v`. -/
theorem opensFDeriv_symm_apply {φ : ↥s → ↥t} {ψ : ↥t → ↥s}
    (hφ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ ψ)
    (hinv : ∀ p, ψ (φ p) = p) (p : ↥s) (v : F) :
    opensFDeriv ψ (φ p) (opensFDeriv φ p v) = v := by
  have h := congrArg (fun L : F →L[ℝ] F => L v) (opensFDeriv_symm_comp hφ hψ hinv p)
  simpa using h

/-! ### Pushforward of vector fields along a diffeomorphism of Euclidean opens -/

section Pushforward

variable (φ : ↥s ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, G)⟯ ↥t)

/-- **Math.** The **pushforward** `φ_*X = dφ ∘ X ∘ φ⁻¹` of a smooth vector
field along a diffeomorphism of Euclidean opens: `(φ_*X)(q) = dφ_{φ⁻¹q}(X(φ⁻¹q))`. -/
def opensPushforward (X : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    SmoothVectorField 𝓘(ℝ, G) ↥t :=
  SmoothVectorField.ofOpens
    (fun q => opensFDeriv (⇑φ) (φ.symm q) (X (φ.symm q))) <| by
    refine contMDiff_opens_of_contDiffAt
      (φ := fun y => fderiv ℝ (opensMapExt (⇑φ)) (opensMapExt (⇑φ.symm) y)
        (s.extendZero (⇑X) (opensMapExt (⇑φ.symm) y))) (fun q => ?_) (fun q => ?_)
    · simp only [opensMapExt_val, TopologicalSpace.Opens.extendZero_val]
      rfl
    · have h1 : ContDiffAt ℝ ∞ (opensMapExt (⇑φ.symm)) q.val :=
        contDiffAt_opensMapExt φ.symm.contMDiff q
      have h2 : ContDiffAt ℝ ∞ (fderiv ℝ (opensMapExt (⇑φ)))
          (opensMapExt (⇑φ.symm) q.val) := by
        rw [opensMapExt_val]
        exact (contDiffAt_opensMapExt φ.contMDiff (φ.symm q)).fderiv_right
          (by simp)
      have h3 : ContDiffAt ℝ ∞ (s.extendZero (⇑X)) (opensMapExt (⇑φ.symm) q.val) := by
        rw [opensMapExt_val]
        exact X.contDiffAt_extendZero (φ.symm q)
      exact (h2.comp q.val h1).clm_apply (h3.comp q.val h1)

omit [CompleteSpace F] [CompleteSpace G] in
@[simp] theorem opensPushforward_apply (X : SmoothVectorField 𝓘(ℝ, F) ↥s)
    (q : ↥t) :
    opensPushforward φ X q = opensFDeriv (⇑φ) (φ.symm q) (X (φ.symm q)) := rfl

omit [CompleteSpace F] [CompleteSpace G] in
theorem opensPushforward_apply_image (X : SmoothVectorField 𝓘(ℝ, F) ↥s)
    (p : ↥s) :
    opensPushforward φ X (φ p) = opensFDeriv (⇑φ) p (X p) := by
  rw [opensPushforward_apply, φ.symm_apply_apply]

omit [CompleteSpace F] [CompleteSpace G] in
theorem opensPushforward_add (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    opensPushforward φ (X + Y) = opensPushforward φ X + opensPushforward φ Y := by
  ext q
  simp only [opensPushforward_apply, SmoothVectorField.add_apply, map_add]

omit [CompleteSpace F] [CompleteSpace G] in
theorem opensPushforward_sub (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    opensPushforward φ (X - Y) = opensPushforward φ X - opensPushforward φ Y := by
  ext q
  simp only [opensPushforward_apply, SmoothVectorField.sub_apply, map_sub]

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** `dφ⁻¹_{φ(p)}(dφ_p v) = v` for a diffeomorphism of opens. -/
theorem opensFDeriv_diffeomorph_symm_apply (p : ↥s) (v : F) :
    opensFDeriv (⇑φ.symm) (φ p) (opensFDeriv (⇑φ) p v) = v :=
  opensFDeriv_symm_apply φ.contMDiff φ.symm.contMDiff φ.symm_apply_apply p v

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** `dφ⁻¹_q (dφ_{φ⁻¹q} v) = v`, the previous identity at `p = φ⁻¹(q)`. -/
theorem opensFDeriv_diffeomorph_symm_apply' (q : ↥t) (v : F) :
    opensFDeriv (⇑φ.symm) q (opensFDeriv (⇑φ) (φ.symm q) v) = v := by
  have h := opensFDeriv_diffeomorph_symm_apply φ (φ.symm q) v
  rwa [φ.apply_symm_apply] at h

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** `dφ_{φ⁻¹q}(dφ⁻¹_q w) = w` for a diffeomorphism of opens. -/
theorem opensFDeriv_diffeomorph_apply_symm (q : ↥t) (w : G) :
    opensFDeriv (⇑φ) (φ.symm q) (opensFDeriv (⇑φ.symm) q w) = w :=
  opensFDeriv_symm_apply φ.symm.contMDiff φ.contMDiff φ.apply_symm_apply q w

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** Naturality of the directional derivative under pushforward:
`(φ_*X)(h ∘ φ⁻¹) = (Xh) ∘ φ⁻¹`. -/
theorem dir_opensPushforward (X : SmoothVectorField 𝓘(ℝ, F) ↥s)
    {h : ↥s → ℝ} (hh : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ h) (q : ↥t) :
    (opensPushforward φ X).dir (fun r => h (φ.symm r)) q = X.dir h (φ.symm q) := by
  have hcomp : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, ℝ) ∞ (fun r : ↥t => h (φ.symm r)) :=
    hh.comp φ.symm.contMDiff
  rw [SmoothVectorField.dir_opens_eq _ hcomp q,
    SmoothVectorField.dir_opens_eq X hh (φ.symm q),
    fderiv_extendZero_comp hh φ.symm.contMDiff q]
  simp only [ContinuousLinearMap.comp_apply, opensPushforward_apply]
  rw [opensFDeriv_diffeomorph_symm_apply' φ]

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** The model-space derivative of the pushforward field, by the chain and
product rules: `d(φ̂_*X)_q = (dφ ∘ dX̂ + d²φ̂(·)(X̂)) ∘ dφ⁻¹` at `p = φ⁻¹(q)`. -/
theorem fderiv_extendZero_opensPushforward (X : SmoothVectorField 𝓘(ℝ, F) ↥s)
    (q : ↥t) :
    fderiv ℝ (t.extendZero ⇑(opensPushforward φ X)) q.val
      = ((opensFDeriv (⇑φ) (φ.symm q)).comp
            (fderiv ℝ (s.extendZero ⇑X) ((φ.symm q : ↥s) : F))
          + (fderiv ℝ (fderiv ℝ (opensMapExt (⇑φ))) ((φ.symm q : ↥s) : F)).flip
              (X (φ.symm q))).comp
        (opensFDeriv (⇑φ.symm) q) := by
  have hev : t.extendZero ⇑(opensPushforward φ X) =ᶠ[𝓝 q.val]
      (fun x => fderiv ℝ (opensMapExt (⇑φ)) x (s.extendZero (⇑X) x))
        ∘ (opensMapExt (⇑φ.symm)) := by
    filter_upwards [t.isOpen.mem_nhds q.2] with y hy
    rw [t.extendZero_apply_of_mem _ hy, Function.comp_apply,
      opensMapExt_apply_of_mem (⇑φ.symm) hy, s.extendZero_val,
      opensPushforward_apply]
    rfl
  have hψd : DifferentiableAt ℝ (opensMapExt (⇑φ.symm)) q.val :=
    (contDiffAt_opensMapExt φ.symm.contMDiff q).differentiableAt (by simp)
  have hcd : DifferentiableAt ℝ (fderiv ℝ (opensMapExt (⇑φ)))
      ((φ.symm q : ↥s) : F) :=
    ((contDiffAt_opensMapExt φ.contMDiff (φ.symm q)).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)
  have hXd : DifferentiableAt ℝ (s.extendZero ⇑X) ((φ.symm q : ↥s) : F) :=
    (X.contDiffAt_extendZero (φ.symm q)).differentiableAt (by simp)
  rw [hev.fderiv_eq, fderiv_comp q.val ?_ hψd]
  · rw [opensMapExt_val, fderiv_clm_apply hcd hXd, s.extendZero_val]
    rfl
  · rw [opensMapExt_val]
    exact hcd.clm_apply hXd

/-- **Math.** **Naturality of the Lie bracket under pushforward**:
`[φ_*X, φ_*Y] = φ_*[X, Y]`, pointwise. The second-derivative terms of `φ̂`
cancel by Schwarz symmetry. -/
theorem DCLieBracket_opensPushforward (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s)
    (q : ↥t) :
    DCLieBracket (opensPushforward φ X) (opensPushforward φ Y) q
      = opensFDeriv (⇑φ) (φ.symm q) (DCLieBracket X Y (φ.symm q)) := by
  rw [DCLieBracket_opens_eq_fderiv, DCLieBracket_opens_eq_fderiv X Y (φ.symm q),
    fderiv_extendZero_opensPushforward φ Y q,
    fderiv_extendZero_opensPushforward φ X q]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, opensPushforward_apply]
  rw [opensFDeriv_diffeomorph_symm_apply' φ, opensFDeriv_diffeomorph_symm_apply' φ]
  have hsch : IsSymmSndFDerivAt ℝ (opensMapExt (⇑φ)) ((φ.symm q : ↥s) : F) :=
    (contDiffAt_opensMapExt φ.contMDiff (φ.symm q)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.mpr le_top)
  rw [hsch (X (φ.symm q)) (Y (φ.symm q)), map_sub]
  abel

/-- **Math.** Field-level form of the bracket naturality:
`[φ_*X, φ_*Y] = φ_*[X, Y]` as bundled bracket fields. -/
theorem bracketField_opensPushforward (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    bracketField (opensPushforward φ X) (opensPushforward φ Y)
      = opensPushforward φ (bracketField X Y) := by
  ext q
  rw [bracketField_apply, DCLieBracket_opensPushforward, opensPushforward_apply,
    bracketField_apply]

end Pushforward

omit [CompleteSpace F] in
/-- **Math.** The scalar field `p ↦ ⟨X(p), Z(p)⟩` of a Euclidean-opens metric
is smooth. -/
theorem metricInner_field_contMDiff_opens (X Z : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      fun p => (opensEuclideanMetric s).metricInner p (X p) (Z p) := by
  rw [contMDiff_opens_iff_extendZero]
  intro q
  rw [extendZero_inner_fields]
  exact (X.contDiffAt_extendZero q).inner ℝ (Z.contDiffAt_extendZero q)

/-! ### Isometries of immersed patches -/

section PatchIsometry

/-- **Math.** do Carmo Ch. 6 §2 (Remark 2.7): an **isometry between immersed
patches** in the identified picture — a diffeomorphism `φ` of the ambient opens
whose derivative carries the tangent distribution of `D` onto that of `D'`
(both directions) and preserves the inner product *of tangent vectors*. Nothing
is required of `dφ` transverse to the distribution: the isometry is leafwise,
exactly do Carmo's isometry of the immersed manifolds after the identification
of each with its image. -/
structure DCPatchIsometry
    (D : DCImmersedPatch 𝓘(ℝ, F) ↥s (opensEuclideanMetric s))
    (D' : DCImmersedPatch 𝓘(ℝ, G) ↥t (opensEuclideanMetric t)) where
  /-- The underlying diffeomorphism of the ambient opens. -/
  diffeo : ↥s ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, G)⟯ ↥t
  /-- `dφ_p` carries `T_pM` into `T_{φ(p)}M'`. -/
  fderiv_mem_tang : ∀ (p : ↥s), ∀ v ∈ D.tang p,
    opensFDeriv (⇑diffeo) p v ∈ D'.tang (diffeo p)
  /-- `dφ⁻¹_q` carries `T_qM'` into `T_{φ⁻¹(q)}M`. -/
  fderiv_symm_mem_tang : ∀ (q : ↥t), ∀ w ∈ D'.tang q,
    opensFDeriv (⇑diffeo.symm) q w ∈ D.tang (diffeo.symm q)
  /-- `dφ_p` preserves the inner product of tangent vectors. -/
  inner_fderiv : ∀ (p : ↥s), ∀ v ∈ D.tang p, ∀ w ∈ D.tang p,
    (opensEuclideanMetric t).metricInner (diffeo p)
        (opensFDeriv (⇑diffeo) p v) (opensFDeriv (⇑diffeo) p w)
      = (opensEuclideanMetric s).metricInner p v w

namespace DCPatchIsometry

variable {D : DCImmersedPatch 𝓘(ℝ, F) ↥s (opensEuclideanMetric s)}
  {D' : DCImmersedPatch 𝓘(ℝ, G) ↥t (opensEuclideanMetric t)}
  (Φ : DCPatchIsometry D D')

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** The pushforward of a tangent field along a patch isometry is a
tangent field. -/
theorem isTangentField_opensPushforward {X : SmoothVectorField 𝓘(ℝ, F) ↥s}
    (hX : D.IsTangentField X) :
    D'.IsTangentField (opensPushforward Φ.diffeo X) := fun q => by
  rw [opensPushforward_apply]
  have h := Φ.fderiv_mem_tang (Φ.diffeo.symm q) _ (hX (Φ.diffeo.symm q))
  rwa [Φ.diffeo.apply_symm_apply] at h

omit [CompleteSpace F] [CompleteSpace G] in
/-- **Math.** A patch isometry preserves the inner product of tangent fields,
pointwise: `⟨φ_*X, φ_*Y⟩(q) = ⟨X, Y⟩(φ⁻¹q)`. -/
theorem metricInner_opensPushforward {X Y : SmoothVectorField 𝓘(ℝ, F) ↥s}
    (hX : D.IsTangentField X) (hY : D.IsTangentField Y) (q : ↥t) :
    (opensEuclideanMetric t).metricInner q (opensPushforward Φ.diffeo X q)
        (opensPushforward Φ.diffeo Y q)
      = (opensEuclideanMetric s).metricInner (Φ.diffeo.symm q)
          (X (Φ.diffeo.symm q)) (Y (Φ.diffeo.symm q)) := by
  rw [opensPushforward_apply, opensPushforward_apply]
  have h := Φ.inner_fderiv (Φ.diffeo.symm q) _ (hX (Φ.diffeo.symm q))
    _ (hY (Φ.diffeo.symm q))
  rwa [Φ.diffeo.apply_symm_apply] at h

variable [FiniteDimensional ℝ F]

local instance : LocallyCompactSpace ↥s := s.isOpen.locallyCompactSpace

/-- **Math.** **Naturality of the induced connection under isometries**:
`∇'_{φ_*X}(φ_*Y) = φ_*(∇_X Y)` for tangent fields `X, Y`. Both sides are
tangent fields; testing against tangent vectors, the Koszul formula
(`inducedCov_koszul`) expresses each side through directional derivatives of
inner products of tangent fields, inner products with Lie brackets of tangent
fields — all preserved by the isometry (`dir_opensPushforward`,
`DCLieBracket_opensPushforward`, `metricInner_opensPushforward`). -/
theorem inducedCov_opensPushforward {X Y : SmoothVectorField 𝓘(ℝ, F) ↥s}
    (hX : D.IsTangentField X) (hY : D.IsTangentField Y) :
    D'.inducedCov opensEuclideanConnection (opensPushforward Φ.diffeo X)
        (opensPushforward Φ.diffeo Y)
      = opensPushforward Φ.diffeo (D.inducedCov opensEuclideanConnection X Y) := by
  have hLC : (opensEuclideanConnection (F := F) (s := s)).IsLeviCivita
      (opensEuclideanMetric s) := opensEuclideanConnection_isLeviCivita
  have hLC' : (opensEuclideanConnection (F := G) (s := t)).IsLeviCivita
      (opensEuclideanMetric t) := opensEuclideanConnection_isLeviCivita
  have hXt' := Φ.isTangentField_opensPushforward hX
  have hYt' := Φ.isTangentField_opensPushforward hY
  ext q
  have hp : Φ.diffeo (Φ.diffeo.symm q) = q := Φ.diffeo.apply_symm_apply q
  -- both sides are tangent at `q`
  have hmem₁ : D'.inducedCov opensEuclideanConnection
      (opensPushforward Φ.diffeo X) (opensPushforward Φ.diffeo Y) q ∈ D'.tang q :=
    D'.isTangentField_inducedCov _ _ _ q
  have hmem₂ : opensPushforward Φ.diffeo
      (D.inducedCov opensEuclideanConnection X Y) q ∈ D'.tang q :=
    Φ.isTangentField_opensPushforward (D.isTangentField_inducedCov _ _ _) q
  refine D'.eq_of_inner_eq_of_mem_tang hmem₁ hmem₂ fun w hw => ?_
  -- the test vector comes from a tangent field pushed forward from below
  have hz : opensFDeriv (⇑Φ.diffeo.symm) q w ∈ D.tang (Φ.diffeo.symm q) :=
    Φ.fderiv_symm_mem_tang q w hw
  have hZt : D.IsTangentField
      (D.tangentExtension (Φ.diffeo.symm q) (opensFDeriv (⇑Φ.diffeo.symm) q w)) :=
    D.isTangentField_tangentExtension _ _
  have hZp : D.tangentExtension (Φ.diffeo.symm q) (opensFDeriv (⇑Φ.diffeo.symm) q w)
      (Φ.diffeo.symm q) = opensFDeriv (⇑Φ.diffeo.symm) q w :=
    D.tangentExtension_apply_self hz
  have hZt' := Φ.isTangentField_opensPushforward hZt
  have hpushZ : opensPushforward Φ.diffeo
      (D.tangentExtension (Φ.diffeo.symm q) (opensFDeriv (⇑Φ.diffeo.symm) q w)) q
      = w := by
    rw [opensPushforward_apply, hZp]
    exact opensFDeriv_diffeomorph_apply_symm Φ.diffeo q w
  -- Koszul formula on both sides
  have hk' := D'.inducedCov_koszul opensEuclideanConnection hLC'.1 hLC'.2
    hYt' hXt' hZt' q
  have hk := D.inducedCov_koszul opensEuclideanConnection hLC.1 hLC.2
    hY hX hZt (Φ.diffeo.symm q)
  -- transport the three directional-derivative terms
  have hdir : ∀ (U V W : SmoothVectorField 𝓘(ℝ, F) ↥s),
      D.IsTangentField V → D.IsTangentField W →
      (opensPushforward Φ.diffeo U).dir
        (fun r => (opensEuclideanMetric t).metricInner r
          (opensPushforward Φ.diffeo V r) (opensPushforward Φ.diffeo W r)) q
      = U.dir (fun r => (opensEuclideanMetric s).metricInner r (V r) (W r))
          (Φ.diffeo.symm q) := by
    intro U V W hV hW
    have hfun : (fun r => (opensEuclideanMetric t).metricInner r
        (opensPushforward Φ.diffeo V r) (opensPushforward Φ.diffeo W r))
        = fun r => (opensEuclideanMetric s).metricInner (Φ.diffeo.symm r)
            (V (Φ.diffeo.symm r)) (W (Φ.diffeo.symm r)) := by
      funext r
      exact Φ.metricInner_opensPushforward hV hW r
    rw [hfun]
    exact dir_opensPushforward Φ.diffeo U (metricInner_field_contMDiff_opens V W) q
  -- transport the three bracket terms
  have hbr : ∀ (U V W : SmoothVectorField 𝓘(ℝ, F) ↥s),
      D.IsTangentField U → D.IsTangentField V → D.IsTangentField W →
      (opensEuclideanMetric t).metricInner q
        (DCLieBracket (opensPushforward Φ.diffeo U) (opensPushforward Φ.diffeo V) q)
        (opensPushforward Φ.diffeo W q)
      = (opensEuclideanMetric s).metricInner (Φ.diffeo.symm q)
          (DCLieBracket U V (Φ.diffeo.symm q)) (W (Φ.diffeo.symm q)) := by
    intro U V W hU hV hW
    rw [DCLieBracket_opensPushforward, opensPushforward_apply]
    have h := Φ.inner_fderiv (Φ.diffeo.symm q) _
      (D.lieBracket_mem U V hU hV (Φ.diffeo.symm q)) _ (hW (Φ.diffeo.symm q))
    rwa [hp] at h
  have h₁ := hdir Y X (D.tangentExtension (Φ.diffeo.symm q)
    (opensFDeriv (⇑Φ.diffeo.symm) q w)) hX hZt
  have h₂ := hdir X (D.tangentExtension (Φ.diffeo.symm q)
    (opensFDeriv (⇑Φ.diffeo.symm) q w)) Y hZt hY
  have h₃ := hdir (D.tangentExtension (Φ.diffeo.symm q)
    (opensFDeriv (⇑Φ.diffeo.symm) q w)) Y X hY hX
  have h₄ := hbr Y (D.tangentExtension (Φ.diffeo.symm q)
    (opensFDeriv (⇑Φ.diffeo.symm) q w)) X hY hZt hX
  have h₅ := hbr X (D.tangentExtension (Φ.diffeo.symm q)
    (opensFDeriv (⇑Φ.diffeo.symm) q w)) Y hX hZt hY
  have h₆ := hbr Y X (D.tangentExtension (Φ.diffeo.symm q)
    (opensFDeriv (⇑Φ.diffeo.symm) q w)) hY hX hZt
  -- the two Koszul right-hand sides agree, so the inner products agree
  have hinner : (opensEuclideanMetric t).metricInner q
      (opensPushforward Φ.diffeo (D.tangentExtension (Φ.diffeo.symm q)
        (opensFDeriv (⇑Φ.diffeo.symm) q w)) q)
      (D'.inducedCov opensEuclideanConnection (opensPushforward Φ.diffeo X)
        (opensPushforward Φ.diffeo Y) q)
      = (opensEuclideanMetric s).metricInner (Φ.diffeo.symm q)
        (D.tangentExtension (Φ.diffeo.symm q)
          (opensFDeriv (⇑Φ.diffeo.symm) q w) (Φ.diffeo.symm q))
        (D.inducedCov opensEuclideanConnection X Y (Φ.diffeo.symm q)) := by
    linarith [hk', hk, h₁, h₂, h₃, h₄, h₅, h₆]
  -- and the same holds against the pushed-forward covariant derivative
  have hpush : (opensEuclideanMetric t).metricInner q
      (opensPushforward Φ.diffeo (D.tangentExtension (Φ.diffeo.symm q)
        (opensFDeriv (⇑Φ.diffeo.symm) q w)) q)
      (opensPushforward Φ.diffeo (D.inducedCov opensEuclideanConnection X Y) q)
      = (opensEuclideanMetric s).metricInner (Φ.diffeo.symm q)
        (D.tangentExtension (Φ.diffeo.symm q)
          (opensFDeriv (⇑Φ.diffeo.symm) q w) (Φ.diffeo.symm q))
        (D.inducedCov opensEuclideanConnection X Y (Φ.diffeo.symm q)) := by
    rw [opensPushforward_apply, opensPushforward_apply]
    have h := Φ.inner_fderiv (Φ.diffeo.symm q) _ (hZt (Φ.diffeo.symm q)) _
      (D.isTangentField_inducedCov opensEuclideanConnection X Y (Φ.diffeo.symm q))
    rwa [hp] at h
  calc (opensEuclideanMetric t).metricInner q
        (D'.inducedCov opensEuclideanConnection (opensPushforward Φ.diffeo X)
          (opensPushforward Φ.diffeo Y) q) w
      = (opensEuclideanMetric t).metricInner q
          (opensPushforward Φ.diffeo (D.tangentExtension (Φ.diffeo.symm q)
            (opensFDeriv (⇑Φ.diffeo.symm) q w)) q)
          (D'.inducedCov opensEuclideanConnection (opensPushforward Φ.diffeo X)
            (opensPushforward Φ.diffeo Y) q) := by
        rw [hpushZ, (opensEuclideanMetric t).metricInner_comm]
    _ = (opensEuclideanMetric t).metricInner q
          (opensPushforward Φ.diffeo (D.tangentExtension (Φ.diffeo.symm q)
            (opensFDeriv (⇑Φ.diffeo.symm) q w)) q)
          (opensPushforward Φ.diffeo
            (D.inducedCov opensEuclideanConnection X Y) q) := by
        rw [hinner, hpush]
    _ = (opensEuclideanMetric t).metricInner q
          (opensPushforward Φ.diffeo
            (D.inducedCov opensEuclideanConnection X Y) q) w := by
        rw [hpushZ, (opensEuclideanMetric t).metricInner_comm]

/-- **Math.** **Naturality of the induced curvature under isometries**:
`R'(φ_*X, φ_*Y)(φ_*Z) = φ_*(R(X,Y)Z)` for tangent fields. -/
theorem inducedCurvature_opensPushforward {X Y Z : SmoothVectorField 𝓘(ℝ, F) ↥s}
    (hX : D.IsTangentField X) (hY : D.IsTangentField Y)
    (hZ : D.IsTangentField Z) :
    D'.inducedCurvature opensEuclideanConnection (opensPushforward Φ.diffeo X)
        (opensPushforward Φ.diffeo Y) (opensPushforward Φ.diffeo Z)
      = opensPushforward Φ.diffeo
          (D.inducedCurvature opensEuclideanConnection X Y Z) := by
  unfold DCImmersedPatch.inducedCurvature
  rw [Φ.inducedCov_opensPushforward hX hZ, Φ.inducedCov_opensPushforward hY hZ,
    Φ.inducedCov_opensPushforward hY
      (D.isTangentField_inducedCov opensEuclideanConnection X Z),
    Φ.inducedCov_opensPushforward hX
      (D.isTangentField_inducedCov opensEuclideanConnection Y Z),
    bracketField_opensPushforward,
    Φ.inducedCov_opensPushforward (D.isTangentField_bracketField hX hY) hZ,
    ← opensPushforward_sub, ← opensPushforward_add]

/-- **Math.** **Isometry invariance of the sectional numerator**
`⟨R(X,Y)X, Y⟩`: at corresponding points, for tangent fields,
`⟨R'(φ_*X, φ_*Y)(φ_*X), φ_*Y⟩(φ p) = ⟨R(X,Y)X, Y⟩(p)`. For `X, Y` orthonormal
at `p` this is the isometry invariance of the sectional curvature of the patch. -/
theorem inducedCurvature_inner_opensPushforward
    {X Y : SmoothVectorField 𝓘(ℝ, F) ↥s}
    (hX : D.IsTangentField X) (hY : D.IsTangentField Y) (p : ↥s) :
    (opensEuclideanMetric t).metricInner (Φ.diffeo p)
        (D'.inducedCurvature opensEuclideanConnection
          (opensPushforward Φ.diffeo X) (opensPushforward Φ.diffeo Y)
          (opensPushforward Φ.diffeo X) (Φ.diffeo p))
        (opensPushforward Φ.diffeo Y (Φ.diffeo p))
      = (opensEuclideanMetric s).metricInner p
          (D.inducedCurvature opensEuclideanConnection X Y X p) (Y p) := by
  rw [Φ.inducedCurvature_opensPushforward hX hY hX,
    opensPushforward_apply_image, opensPushforward_apply_image]
  exact Φ.inner_fderiv p _
    (D.inducedCurvature_mem opensEuclideanConnection X Y X p) _ (hY p)

end DCPatchIsometry

end PatchIsometry

/-! ### The pointwise Gauss form of a patch -/

section GaussForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)
  (nabla : AffineConnection I M)

/-- **Math.** The pointwise **Gauss form** of the patch at `p`, on the tangent
plane `T_pM`:

`A(x, y, z, t) = ⟨B(y,t), B(x,z)⟩ − ⟨B(x,t), B(y,z)⟩`.

By the Gauss equation (`prop:dc-ch6-3-1`), in a *flat* ambient this quadrilinear
form computes `⟨R(X,Y)Z, T⟩` of the induced curvature from pointwise data. -/
def gaussFormAt (p : M) (x y z t : ↥(D.tang p)) : ℝ :=
  g.metricInner p (D.secondFundFormAt nabla p ↑y ↑t)
      (D.secondFundFormAt nabla p ↑x ↑z)
    - g.metricInner p (D.secondFundFormAt nabla p ↑x ↑t)
      (D.secondFundFormAt nabla p ↑y ↑z)

/-- **Math.** The Gauss form is an **algebraic curvature form** on the tangent
plane: multilinear, antisymmetric in each pair, and satisfying the first Bianchi
identity — by bilinearity and symmetry of the second fundamental form. -/
theorem isAlgCurvatureForm_gaussFormAt (hsym : nabla.IsSymmetric) (p : M) :
    letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
    letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
    IsAlgCurvatureForm (D.gaussFormAt nabla p) := by
  letI : NormedAddCommGroup (TangentSpace I p) := g.fiberNormedAddCommGroup p
  letI : InnerProductSpace ℝ (TangentSpace I p) := g.fiberInnerProductSpace p
  have hsymB : ∀ u v : ↥(D.tang p),
      D.secondFundFormAt nabla p ↑u ↑v = D.secondFundFormAt nabla p ↑v ↑u :=
    fun u v => D.secondFundFormAt_symm nabla hsym u.2 v.2
  constructor
  · intro x₁ x₂ y z t
    simp only [gaussFormAt, Submodule.coe_add, D.secondFundFormAt_add_left,
      g.metricInner_add_left, g.metricInner_add_right]
    ring
  · intro a x y z t
    simp only [gaussFormAt, Submodule.coe_smul, D.secondFundFormAt_smul_left,
      g.metricInner_smul_left, g.metricInner_smul_right]
    ring
  · intro x y z t
    simp only [gaussFormAt]
    ring
  · intro x y z t
    have c₁ := g.metricInner_comm p (D.secondFundFormAt nabla p ↑y ↑z)
      (D.secondFundFormAt nabla p ↑x ↑t)
    have c₂ := g.metricInner_comm p (D.secondFundFormAt nabla p ↑x ↑z)
      (D.secondFundFormAt nabla p ↑y ↑t)
    simp only [gaussFormAt]
    linarith
  · intro x y z t
    simp only [gaussFormAt]
    rw [hsymB y x, hsymB z x, hsymB z y]
    ring

end DCImmersedPatch

end GaussForm

/-! ### Flat ambient: the Gauss form computes the induced curvature -/

section FlatGauss

variable [FiniteDimensional ℝ F]

local instance : LocallyCompactSpace ↥s := s.isOpen.locallyCompactSpace

/-- **Math.** In the flat Euclidean ambient the pairing `⟨R(X,Y)Z, T⟩` of the
induced curvature is computed by the pointwise Gauss form — the Gauss equation
with `R̄ ≡ 0`. In particular it depends only on the values of the four tangent
fields at the point. -/
theorem inducedCurvature_inner_eq_gaussFormAt
    (D : DCImmersedPatch 𝓘(ℝ, F) ↥s (opensEuclideanMetric s))
    {X Y Z T : SmoothVectorField 𝓘(ℝ, F) ↥s}
    (_hX : D.IsTangentField X) (_hY : D.IsTangentField Y)
    (hZ : D.IsTangentField Z) (hT : D.IsTangentField T) (q : ↥s)
    (x y z t : ↥(D.tang q))
    (hx : (x : TangentSpace 𝓘(ℝ, F) q) = X q)
    (hy : (y : TangentSpace 𝓘(ℝ, F) q) = Y q)
    (hz : (z : TangentSpace 𝓘(ℝ, F) q) = Z q)
    (ht : (t : TangentSpace 𝓘(ℝ, F) q) = T q) :
    (opensEuclideanMetric s).metricInner q
        (D.inducedCurvature opensEuclideanConnection X Y Z q) (T q)
      = D.gaussFormAt opensEuclideanConnection q x y z t := by
  have hg := D.gauss_equation opensEuclideanConnection
    opensEuclideanConnection_isLeviCivita.2 X Y Z hT q
  rw [opensEuclideanConnection_curvature X Y Z, SmoothVectorField.zero_apply,
    (opensEuclideanMetric s).metricInner_zero_left] at hg
  have b₁ := D.secondFundFormAt_apply_apply opensEuclideanConnection hT Y q
  have b₂ := D.secondFundFormAt_apply_apply opensEuclideanConnection hZ X q
  have b₃ := D.secondFundFormAt_apply_apply opensEuclideanConnection hT X q
  have b₄ := D.secondFundFormAt_apply_apply opensEuclideanConnection hZ Y q
  simp only [DCImmersedPatch.gaussFormAt, hx, hy, hz, ht]
  rw [b₁, b₂, b₃, b₄]
  linarith

end FlatGauss

/-! ### The Theorema Egregium -/

section TheoremaEgregium

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

local instance : LocallyCompactSpace ↥s := s.isOpen.locallyCompactSpace
local instance : LocallyCompactSpace ↥t := t.isOpen.locallyCompactSpace

namespace DCPatchIsometry

variable {D : DCImmersedPatch 𝓘(ℝ, F) ↥s (opensEuclideanMetric s)}
  {D' : DCImmersedPatch 𝓘(ℝ, G) ↥t (opensEuclideanMetric t)}
  (Φ : DCPatchIsometry D D')

/-- **Math.** **Theorema Egregium** (do Carmo Ch. 6, Rem. 2.7). Let `D, D'` be
two-dimensional hypersurface patches in flat Euclidean ambients — at `p` the
normal space of `D` is spanned by a unit normal `η`, and at `φ(p)` that of `D'`
by `η'` — and let `φ` be an isometry of the patches. Then the **Gaussian
curvature**, the product of the principal curvatures, is the same at
corresponding points:

`λ_i(p) · λ_j(p) = λ'_k(φ(p)) · λ'_l(φ(p))` for `i ≠ j`, `k ≠ l`.

By the Gauss formula for a hypersurface (`rem:dc-ch6-2-6`, with flat ambient)
each side is the sectional curvature of the corresponding tangent plane, and
sectional curvature is built from the induced connection, which the isometry
intertwines (`inducedCov_opensPushforward`) — Gauss's *egregium*: an extrinsic
product of curvatures is intrinsic. -/
theorem theorema_egregium (hdim' : D'.dim = 2) (p : ↥s)
    {η : TangentSpace 𝓘(ℝ, F) p} (hη : η ∈ D.normalSpace p)
    (hunit : (opensEuclideanMetric s).metricInner p η η = 1)
    (hcodim : ∀ w ∈ D.normalSpace p, ∃ c : ℝ, w = c • η)
    {η' : TangentSpace 𝓘(ℝ, G) (Φ.diffeo p)}
    (hη' : η' ∈ D'.normalSpace (Φ.diffeo p))
    (hunit' : (opensEuclideanMetric t).metricInner (Φ.diffeo p) η' η' = 1)
    (hcodim' : ∀ w ∈ D'.normalSpace (Φ.diffeo p), ∃ c : ℝ, w = c • η')
    {i j : Fin D.dim} (hij : i ≠ j) {k l : Fin D'.dim} (hkl : k ≠ l) :
    D.principalCurvatures opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita p hη i
      * D.principalCurvatures opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita p hη j
    = D'.principalCurvatures opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' k
      * D'.principalCurvatures opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' l := by
  -- Gauss formula at `p` (flat ambient): `λᵢλⱼ = ⟨R(E₁,E₂)E₁, E₂⟩(p)`
  have hgp := D.hypersurface_gauss opensEuclideanConnection
    opensEuclideanConnection_isLeviCivita p hη hunit hcodim hij
  rw [opensEuclideanConnection_curvature, SmoothVectorField.zero_apply,
    (opensEuclideanMetric s).metricInner_zero_left, sub_zero] at hgp
  -- Gauss formula at `φ(p)`: `λ'ₖλ'ₗ = ⟨R'(E'₁,E'₂)E'₁, E'₂⟩(φ p)`
  have hgq := D'.hypersurface_gauss opensEuclideanConnection
    opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' hunit' hcodim' hkl
  rw [opensEuclideanConnection_curvature, SmoothVectorField.zero_apply,
    (opensEuclideanMetric t).metricInner_zero_left, sub_zero] at hgq
  -- tangency of all the extension fields involved
  have hE₁t : D.IsTangentField (D.tangentExtension p
      (D.principalDirection opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita p hη i)) :=
    D.isTangentField_tangentExtension _ _
  have hE₂t : D.IsTangentField (D.tangentExtension p
      (D.principalDirection opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita p hη j)) :=
    D.isTangentField_tangentExtension _ _
  have hΦE₁t := Φ.isTangentField_opensPushforward hE₁t
  have hΦE₂t := Φ.isTangentField_opensPushforward hE₂t
  have hE'₁t : D'.IsTangentField (D'.tangentExtension (Φ.diffeo p)
      (D'.principalDirection opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' k)) :=
    D'.isTangentField_tangentExtension _ _
  have hE'₂t : D'.IsTangentField (D'.tangentExtension (Φ.diffeo p)
      (D'.principalDirection opensEuclideanConnection
        opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' l)) :=
    D'.isTangentField_tangentExtension _ _
  -- the isometry transports the sectional numerator
  have hpair := Φ.inducedCurvature_inner_opensPushforward hE₁t hE₂t p
  -- flat pointwise Gauss form at `φ(p)`, on the pushed-forward values …
  have hflatU := inducedCurvature_inner_eq_gaussFormAt D' hΦE₁t hΦE₂t hΦE₁t
    hΦE₂t (Φ.diffeo p)
    ⟨_, hΦE₁t (Φ.diffeo p)⟩ ⟨_, hΦE₂t (Φ.diffeo p)⟩
    ⟨_, hΦE₁t (Φ.diffeo p)⟩ ⟨_, hΦE₂t (Φ.diffeo p)⟩ rfl rfl rfl rfl
  -- … and on the values of the primed principal-direction extensions
  have hflatV := inducedCurvature_inner_eq_gaussFormAt D' hE'₁t hE'₂t hE'₁t
    hE'₂t (Φ.diffeo p)
    ⟨_, hE'₁t (Φ.diffeo p)⟩ ⟨_, hE'₂t (Φ.diffeo p)⟩
    ⟨_, hE'₁t (Φ.diffeo p)⟩ ⟨_, hE'₂t (Φ.diffeo p)⟩ rfl rfl rfl rfl
  -- orthonormality of the pushed-forward pair
  have hu : ∀ a b : Fin D.dim,
      (opensEuclideanMetric t).metricInner (Φ.diffeo p)
        (opensPushforward Φ.diffeo (D.tangentExtension p
          (D.principalDirection opensEuclideanConnection
            opensEuclideanConnection_isLeviCivita p hη a)) (Φ.diffeo p))
        (opensPushforward Φ.diffeo (D.tangentExtension p
          (D.principalDirection opensEuclideanConnection
            opensEuclideanConnection_isLeviCivita p hη b)) (Φ.diffeo p))
      = if a = b then 1 else 0 := by
    intro a b
    rw [opensPushforward_apply_image, opensPushforward_apply_image,
      Φ.inner_fderiv p _ (D.isTangentField_tangentExtension _ _ p)
        _ (D.isTangentField_tangentExtension _ _ p),
      D.tangentExtension_apply_self (D.principalDirection_mem
        opensEuclideanConnection opensEuclideanConnection_isLeviCivita p hη a),
      D.tangentExtension_apply_self (D.principalDirection_mem
        opensEuclideanConnection opensEuclideanConnection_isLeviCivita p hη b)]
    exact D.metricInner_principalDirection opensEuclideanConnection
      opensEuclideanConnection_isLeviCivita p hη a b
  -- orthonormality of the primed principal-direction values
  have hv : ∀ a b : Fin D'.dim,
      (opensEuclideanMetric t).metricInner (Φ.diffeo p)
        (D'.tangentExtension (Φ.diffeo p)
          (D'.principalDirection opensEuclideanConnection
            opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' a) (Φ.diffeo p))
        (D'.tangentExtension (Φ.diffeo p)
          (D'.principalDirection opensEuclideanConnection
            opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' b) (Φ.diffeo p))
      = if a = b then 1 else 0 := by
    intro a b
    rw [D'.tangentExtension_apply_self (D'.principalDirection_mem
        opensEuclideanConnection opensEuclideanConnection_isLeviCivita
        (Φ.diffeo p) hη' a),
      D'.tangentExtension_apply_self (D'.principalDirection_mem
        opensEuclideanConnection opensEuclideanConnection_isLeviCivita
        (Φ.diffeo p) hη' b)]
    exact D'.metricInner_principalDirection opensEuclideanConnection
      opensEuclideanConnection_isLeviCivita (Φ.diffeo p) hη' a b
  -- the Gauss form takes equal values on the two orthonormal pairs
  letI : NormedAddCommGroup (TangentSpace 𝓘(ℝ, G) (Φ.diffeo p)) :=
    (opensEuclideanMetric t).fiberNormedAddCommGroup (Φ.diffeo p)
  letI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, G) (Φ.diffeo p)) :=
    (opensEuclideanMetric t).fiberInnerProductSpace (Φ.diffeo p)
  have hAform := D'.isAlgCurvatureForm_gaussFormAt opensEuclideanConnection
    opensEuclideanConnection_isSymmetric (Φ.diffeo p)
  have hfr : Module.finrank ℝ ↥(D'.tang (Φ.diffeo p)) = 2 := by
    rw [D'.finrank_tang]
    exact hdim'
  have hswap := hAform.apply_eq_of_orthonormal_of_finrank_eq_two hfr
    (u₁ := ⟨_, hΦE₁t (Φ.diffeo p)⟩) (u₂ := ⟨_, hΦE₂t (Φ.diffeo p)⟩)
    (v₁ := ⟨_, hE'₁t (Φ.diffeo p)⟩) (v₂ := ⟨_, hE'₂t (Φ.diffeo p)⟩)
    (by have h := hu i i; rw [if_pos rfl] at h; exact h)
    (by have h := hu j j; rw [if_pos rfl] at h; exact h)
    (by simpa [hij] using hu i j)
    (by have h := hv k k; rw [if_pos rfl] at h; exact h)
    (by have h := hv l l; rw [if_pos rfl] at h; exact h)
    (by simpa [hkl] using hv k l)
  linarith [hgp, hgq, hpair, hflatU, hflatV, hswap]

end DCPatchIsometry

end TheoremaEgregium

end Riemannian
