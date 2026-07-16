import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import OpenGALib.Riemannian.Manifold.DoCarmoCh1
import OpenGALib.Riemannian.Manifold.DoCarmoCh6ConstantCurvature
import OpenGALib.Riemannian.Manifold.EuclideanFlat

/-!
# Open subsets of Euclidean space as ambient Riemannian manifolds

do Carmo's classical examples of Chapter 6 (the sphere `Sⁿ ⊂ ℝⁿ⁺¹` of
Example 2.8, hypersurfaces of Example 2.4) take place in an *open subset* of
Euclidean space: the sphere-of-radius-`‖p‖` foliation of the punctured space
`ℝⁿ⁺¹ ∖ {0}` is the immersed-patch picture of `Sⁿ`, and no distribution of
constant rank extends over the origin. This file provides the missing
restriction layer: an open subset `s : Opens F` of a real (inner-product)
vector space `F`, as a manifold modelled on `𝓘(ℝ, F)` via mathlib's
`Opens.instChartedSpace`, carries

* an identification of all its calculus with the flat calculus of `F` through
  the zero-extension `Opens.extendZero` of functions off `s`:
  - `contMDiffAt_opens_iff_extendZero` — smoothness of `f : ↥s → G` is
    smoothness of the extension near points of `s`;
  - `contMDiff_section_opens_iff` — smoothness of a tangent-bundle section is
    plain smoothness of the raw map `↥s → F` (the tangent bundle of `↥s` is
    canonically trivial: all charts of `↥s` are equal);
  - `mfderiv_subtype_val_opens` / `mfderiv_opens_eq_fderiv_extendZero` — the
    inclusion has identity differential, and the manifold differential of any
    `f : ↥s → G` is the flat `fderiv` of its extension;
  - `DCLieBracket_opens_eq_fderiv` — the manifold Lie bracket on `↥s` is the
    classical commutator `[X, Y] = dŶ(X) − dX̂(Y)` of the extensions, by
    naturality of the Lie bracket under the inclusion (whose differential is
    the identity);

* the restricted Euclidean structure:
  - `opensEuclideanMetric` — the Euclidean metric of `F` restricted to `↥s`
    (do Carmo Ch. 1, Ex. 2.4, on the open piece);
  - `opensEuclideanConnection` — the flat connection `∇_X Y = dŶ(X)`; it is
    the Levi-Civita connection of the restricted metric, its curvature
    vanishes, and `↥s` has constant sectional curvature `0`
    (`opensEuclideanConnection_isConstantCurvature_zero`) — the ambient data
    consumed by the Ch. 6 fundamental equations.

Reference: do Carmo, *Riemannian Geometry*, Ch. 1 §2, Ch. 2 §2, Ch. 6 §2.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open TopologicalSpace

noncomputable section

/-! ## The zero-extension of functions off an open set -/

namespace TopologicalSpace.Opens

variable {F : Type*} [TopologicalSpace F] {G : Type*} [Zero G]

/-- **Math.** The **zero-extension** of `f : ↥s → G` to the ambient space: the
junk value `0` off `s`. Near points of `s` it carries exactly the germ of `f`,
which is all that manifold calculus on `↥s` sees. -/
noncomputable def extendZero (s : Opens F) (f : ↥s → G) : F → G :=
  Function.extend (Subtype.val : ↥s → F) f 0

@[simp] theorem extendZero_val (s : Opens F) (f : ↥s → G) (q : ↥s) :
    s.extendZero f q.val = f q :=
  Subtype.val_injective.extend_apply f 0 q

theorem extendZero_comp_val (s : Opens F) (f : ↥s → G) :
    s.extendZero f ∘ (Subtype.val : ↥s → F) = f := by
  funext q
  exact s.extendZero_val f q

theorem extendZero_apply_of_mem (s : Opens F) (f : ↥s → G) {x : F} (hx : x ∈ s) :
    s.extendZero f x = f ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩

theorem extendZero_apply_of_notMem (s : Opens F) (f : ↥s → G) {x : F}
    (hx : x ∉ s) : s.extendZero f x = 0 := by
  refine Function.extend_apply' f (0 : F → G) x ?_
  rintro ⟨q, rfl⟩
  exact hx q.2

end TopologicalSpace.Opens

namespace Riemannian

/-! ## Charts of an open subset of a vector space

For `s : Opens F` with `F` a normed space modelled on itself, mathlib's
`Opens.instChartedSpace` gives every point the *same* chart — the restriction
of the identity chart of `F` to `s`. In particular the charted space is
locally constant, and the extended chart at any point is the inclusion
`Subtype.val`. -/

section Charts

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Opens F}

/-- **Math.** All charts of an open subset of a vector space are equal (to the
restriction of the identity chart), hence locally constant. This activates the
chart-parametric smoothness lemmas of `TangentSmooth`. -/
instance instIsLocallyConstantChartedSpaceOpens :
    IsLocallyConstantChartedSpace F ↥s where
  chartAt_eventually_eq _ := Filter.Eventually.of_forall fun _ => rfl

/-- **Math.** The extended chart of `↥s` at any basepoint is the inclusion
`Subtype.val`, as a function. -/
theorem extChartAt_opens_coe (q : ↥s) :
    ⇑(extChartAt 𝓘(ℝ, F) q) = (Subtype.val : ↥s → F) := rfl

/-- **Math.** The differential of the inclusion `↥s ↪ F` is the identity: the
tangent space of the open subset *is* the tangent space of the ambient
space. -/
theorem mfderiv_subtype_val_opens (q : ↥s) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) q
      = ContinuousLinearMap.id ℝ F := by
  have h : (Subtype.val : ↥s → F) = ⇑(extChartAt 𝓘(ℝ, F) q) :=
    (extChartAt_opens_coe q).symm
  rw [h]
  exact mfderiv_extChartAt_self

theorem contMDiff_subtype_val_opens :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (Subtype.val : ↥s → F) :=
  contMDiff_subtype_val

end Charts

/-! ## Smoothness on `↥s` through the zero-extension -/

section SmoothnessBridge

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Opens F}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n : ℕ∞ω}

/-- **Math.** Smoothness of `f : ↥s → G` at `q` is plain smoothness of its
zero-extension at `q ∈ F`: manifold calculus on the open subset is the flat
calculus of the germs. -/
theorem contMDiffAt_opens_iff_extendZero {f : ↥s → G} {q : ↥s} :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, G) n f q ↔ ContDiffAt ℝ n (s.extendZero f) q.val := by
  have hfun : f = fun x : ↥s => s.extendZero f x.val := by
    funext x
    rw [s.extendZero_val]
  constructor
  · intro hf
    have : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, G) n (fun x : ↥s => s.extendZero f x.val) q := by
      rwa [← hfun]
    rw [contMDiffAt_subtype_iff] at this
    exact contMDiffAt_iff_contDiffAt.mp this
  · intro hf
    rw [hfun]
    rw [contMDiffAt_subtype_iff]
    exact contMDiffAt_iff_contDiffAt.mpr hf

/-- **Math.** Global form of `contMDiffAt_opens_iff_extendZero`. -/
theorem contMDiff_opens_iff_extendZero {f : ↥s → G} :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) n f ↔ ∀ q : ↥s, ContDiffAt ℝ n (s.extendZero f) q.val := by
  constructor
  · intro hf q
    exact contMDiffAt_opens_iff_extendZero.mp (hf q)
  · intro hf q
    exact contMDiffAt_opens_iff_extendZero.mpr (hf q)

/-- **Math.** A map on `↥s` given by an ambient formula `φ : F → G` smooth near
the points of `s` is smooth: the zero-extension agrees with `φ` near `s`. -/
theorem contMDiff_opens_of_contDiffAt {f : ↥s → G} {φ : F → G}
    (hfφ : ∀ q : ↥s, f q = φ q.val)
    (hφ : ∀ q : ↥s, ContDiffAt ℝ n φ q.val) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) n f := by
  intro q
  rw [contMDiffAt_opens_iff_extendZero]
  refine (hφ q).congr_of_eventuallyEq ?_
  filter_upwards [s.isOpen.mem_nhds q.2] with x hx
  rw [s.extendZero_apply_of_mem _ hx, hfφ]

/-- **Math.** Near a point of `s`, the zero-extension of a map given by an
ambient formula has the formula's derivative. -/
theorem fderiv_extendZero_of_formula {f : ↥s → G} {φ : F → G}
    (hfφ : ∀ q : ↥s, f q = φ q.val) (q : ↥s) :
    fderiv ℝ (s.extendZero f) q.val = fderiv ℝ φ q.val := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [s.isOpen.mem_nhds q.2] with x hx
  rw [s.extendZero_apply_of_mem _ hx, hfφ]

/-- **Math.** The manifold differential of `f : ↥s → G` at `q` is the flat
derivative of its zero-extension: `df_q = d(f̂)_{q}`. -/
theorem mfderiv_opens_eq_fderiv_extendZero {f : ↥s → G} {q : ↥s}
    (hf : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, G) 1 f q) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) f q = fderiv ℝ (s.extendZero f) q.val := by
  have hext : ContDiffAt ℝ 1 (s.extendZero f) q.val :=
    contMDiffAt_opens_iff_extendZero.mp hf
  have hval : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) q :=
    (contMDiff_subtype_val_opens q).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hextm : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, G) (s.extendZero f) q.val :=
    (contMDiffAt_iff_contDiffAt.mpr hext).mdifferentiableAt one_ne_zero
  have hcomp : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) (s.extendZero f ∘ (Subtype.val : ↥s → F)) q
      = (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) (s.extendZero f) q.val).comp
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) q) :=
    mfderiv_comp q hextm hval
  rw [s.extendZero_comp_val f] at hcomp
  rw [hcomp, mfderiv_subtype_val_opens]
  ext v
  show mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) (s.extendZero f) q.val v
    = fderiv ℝ (s.extendZero f) q.val v
  rw [mfderiv_eq_fderiv]
  rfl

/-! ### Tangent-bundle sections over `↥s` -/

/-- **Math.** A tangent-bundle section over the open subset `↥s` is smooth iff
the raw map `↥s → F` is: the tangent bundle of `↥s` is canonically trivial,
all charts being equal. -/
theorem contMDiff_section_opens_iff {X : ↥s → F} :
    ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) n
      (fun q => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, F) ↥s))
      ↔ ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) n X := by
  constructor
  · intro hX
    -- compose the section with the (smooth) bundle trivialization projection
    intro q
    have hq := hX q
    rw [Bundle.contMDiffAt_section] at hq
    -- the trivialized form agrees with `X` since all coordinate changes are the identity
    have hagree : (fun x : ↥s =>
        (trivializationAt F (TangentSpace 𝓘(ℝ, F)) q ⟨x, X x⟩).2) = X := by
      funext x
      exact (tangentBundleCore 𝓘(ℝ, F) ↥s).coordChange_self (achart F x) x
        (mem_chart_source F x) (X x)
    rwa [hagree] at hq
  · intro hX q
    rw [Bundle.contMDiffAt_section]
    have hagree : (fun x : ↥s =>
        (trivializationAt F (TangentSpace 𝓘(ℝ, F)) q ⟨x, X x⟩).2) = X := by
      funext x
      exact (tangentBundleCore 𝓘(ℝ, F) ↥s).coordChange_self (achart F x) x
        (mem_chart_source F x) (X x)
    rw [hagree]
    exact hX q

/-- **Math.** Build a bundled smooth vector field on the open subset from a raw
smooth map `↥s → F`. -/
def SmoothVectorField.ofOpens (X : ↥s → F)
    (hX : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ X) : SmoothVectorField 𝓘(ℝ, F) ↥s where
  toFun := X
  smooth := contMDiff_section_opens_iff.mpr hX

@[simp] theorem SmoothVectorField.ofOpens_apply (X : ↥s → F)
    (hX : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ X) (q : ↥s) :
    SmoothVectorField.ofOpens X hX q = X q := rfl

/-- **Math.** The raw map of a smooth vector field on `↥s` is smooth. -/
theorem SmoothVectorField.contMDiff_opens (X : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (⇑X : ↥s → F) :=
  contMDiff_section_opens_iff.mp X.smooth

/-- **Math.** The zero-extension of (the raw map of) a smooth vector field on
`↥s` is smooth near every point of `s`. -/
theorem SmoothVectorField.contDiffAt_extendZero (X : SmoothVectorField 𝓘(ℝ, F) ↥s)
    (q : ↥s) : ContDiffAt ℝ ∞ (s.extendZero ⇑X) q.val :=
  contMDiffAt_opens_iff_extendZero.mp (X.contMDiff_opens q)

/-- **Math.** The directional derivative of a scalar `f : ↥s → ℝ` along a
field `X`, computed flatly: `X(f)(q) = d(f̂)_{q}(X q)`. -/
theorem SmoothVectorField.dir_opens_eq (X : SmoothVectorField 𝓘(ℝ, F) ↥s)
    {f : ↥s → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (q : ↥s) :
    X.dir f q = fderiv ℝ (s.extendZero f) q.val (X q) := by
  show mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f q (X q) = _
  rw [mfderiv_opens_eq_fderiv_extendZero
    ((hf q).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))]
  rfl

end SmoothnessBridge

/-! ## The Lie bracket on `↥s` is the flat commutator -/

section LieBracket

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {s : Opens F}

omit [CompleteSpace F] in
/-- **Math.** `(id)⁻¹ = id` for the junk-valued `ContinuousLinearMap.inverse`,
in point-applied form (stated so it can be consumed at the `TangentSpace`-typed
instances, which are definitionally those of `F`). -/
private theorem inverse_id_apply (v : F) :
    (ContinuousLinearMap.id ℝ F).inverse v = v := by
  rw [ContinuousLinearMap.inverse_id]
  rfl

/-- **Math.** On an open subset of a vector space the manifold Lie bracket is
the classical commutator of the zero-extensions:
`[X, Y](q) = d(Ŷ)_q(X q) − d(X̂)_q(Y q)`. Proved by naturality of the Lie
bracket under the inclusion `↥s ↪ F`, whose differential is the identity. -/
theorem DCLieBracket_opens_eq_fderiv (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) (q : ↥s) :
    DCLieBracket X Y q
      = fderiv ℝ (s.extendZero ⇑Y) q.val (X q)
        - fderiv ℝ (s.extendZero ⇑X) q.val (Y q) := by
  classical
  set V : ∀ x : F, TangentSpace 𝓘(ℝ, F) x := s.extendZero ⇑X with hV
  set W : ∀ x : F, TangentSpace 𝓘(ℝ, F) x := s.extendZero ⇑Y with hW
  -- differentiability of the extended sections within `s`
  have hVd : MDifferentiableWithinAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun x => Bundle.TotalSpace.mk' F x (V x)) (s : Set F) q.val := by
    have := (contMDiffAt_vectorSpace_iff_contDiffAt
      (V := V) (n := (1 : ℕ∞ω)) (x := q.val)).mpr
      ((X.contDiffAt_extendZero q).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
    exact (this.mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
  have hWd : MDifferentiableWithinAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun x => Bundle.TotalSpace.mk' F x (W x)) (s : Set F) q.val := by
    have := (contMDiffAt_vectorSpace_iff_contDiffAt
      (V := W) (n := (1 : ℕ∞ω)) (x := q.val)).mpr
      ((Y.contDiffAt_extendZero q).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
    exact (this.mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
  -- naturality of the bracket under the inclusion
  have hnat := VectorField.mpullback_mlieBracketWithin
    (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F)) (f := (Subtype.val : ↥s → F))
    (V := V) (W := W) (x₀ := q) (s := (Set.univ : Set ↥s)) (t := (s : Set F))
    (n := ∞) hVd hWd uniqueMDiffOn_univ
    (contMDiff_subtype_val_opens q) (Set.mem_univ q)
    (by rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr le_top)
    (by
      have : (Subtype.val : ↥s → F) ⁻¹' (s : Set F) = Set.univ := by
        ext x; simpa using x.2
      rw [this]
      exact Filter.univ_mem)
  -- the pullbacks of the extensions are the original fields
  have hpbV : VectorField.mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) V = ⇑X := by
    funext x
    show (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) x).inverse (V x.val) = X x
    rw [mfderiv_subtype_val_opens]
    have h1 : (ContinuousLinearMap.id ℝ F).inverse (V x.val) = V x.val :=
      inverse_id_apply (F := F) (V x.val)
    have h2 : V x.val = X x := s.extendZero_val (f := ((⇑X : ↥s → F))) x
    exact h1.trans h2
  have hpbW : VectorField.mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) W = ⇑Y := by
    funext x
    show (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) x).inverse (W x.val) = Y x
    rw [mfderiv_subtype_val_opens]
    have h1 : (ContinuousLinearMap.id ℝ F).inverse (W x.val) = W x.val :=
      inverse_id_apply (F := F) (W x.val)
    have h2 : W x.val = Y x := s.extendZero_val (f := ((⇑Y : ↥s → F))) x
    exact h1.trans h2
  rw [hpbV, hpbW] at hnat
  -- identify the left side with the flat commutator
  have hlhs : VectorField.mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F)
      (VectorField.mlieBracketWithin 𝓘(ℝ, F) V W (s : Set F)) q
      = fderiv ℝ (s.extendZero ⇑Y) q.val (X q)
        - fderiv ℝ (s.extendZero ⇑X) q.val (Y q) := by
    show (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (Subtype.val : ↥s → F) q).inverse
      (VectorField.mlieBracketWithin 𝓘(ℝ, F) V W (s : Set F) q.val) = _
    rw [mfderiv_subtype_val_opens]
    have h1 : (ContinuousLinearMap.id ℝ F).inverse
        (VectorField.mlieBracketWithin 𝓘(ℝ, F) V W (s : Set F) q.val)
        = VectorField.mlieBracketWithin 𝓘(ℝ, F) V W (s : Set F) q.val :=
      inverse_id_apply (F := F) _
    refine h1.trans ?_
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    show fderivWithin ℝ W (s : Set F) q.val (V q.val)
        - fderivWithin ℝ V (s : Set F) q.val (W q.val) = _
    rw [fderivWithin_of_isOpen s.isOpen q.2, fderivWithin_of_isOpen s.isOpen q.2,
      hV, hW]
    rw [s.extendZero_val ⇑X q, s.extendZero_val ⇑Y q]
  -- conclude: the bracket within `univ` is the bracket
  have hrhs : VectorField.mlieBracketWithin 𝓘(ℝ, F) ⇑X ⇑Y (Set.univ : Set ↥s) q
      = DCLieBracket X Y q := by
    show VectorField.mlieBracketWithin 𝓘(ℝ, F) ⇑X ⇑Y Set.univ q
      = VectorField.mlieBracket 𝓘(ℝ, F) ⇑X ⇑Y q
    rfl
  rw [← hrhs, ← hnat, hlhs]

end LieBracket

/-! ## The restricted Euclidean metric -/

section Metric

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {s : Opens F}

/-- **Math.** On an open subset of a vector space, the pointwise coordinate map
of the tangent-bundle trivialization is the identity: all charts are equal, so
the coordinate change is `coordChange_self`. -/
@[simp] theorem continuousLinearMapAt_trivializationAt_opens (b₀ b : ↥s) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) b₀).continuousLinearMapAt ℝ b
      = ContinuousLinearMap.id ℝ F := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (show b ∈ (chartAt F b₀).source from mem_chart_source F b)]
  ext v
  exact (tangentBundleCore 𝓘(ℝ, F) ↥s).coordChange_self (achart F b) b
    (mem_chart_source F b) v

/-- **Math.** On an open subset of a vector space, the pointwise inverse
coordinate map of the tangent-bundle trivialization is the identity. -/
@[simp] theorem symmL_trivializationAt_opens (b₀ b : ↥s) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) b₀).symmL ℝ b
      = ContinuousLinearMap.id ℝ F := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (show b ∈ (chartAt F b₀).source from mem_chart_source F b)]
  ext v
  exact (tangentBundleCore 𝓘(ℝ, F) ↥s).coordChange_self (achart F b₀) b
    (mem_chart_source F b) v

/-- **Math.** Value form of `symmL_trivializationAt_opens`: the raw inverse of
the tangent trivialization is the identity on fibres. -/
@[simp] theorem trivializationAt_symm_opens (b₀ b : ↥s) (v : F) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) b₀).symm b v = v := by
  have h : (trivializationAt F (TangentSpace 𝓘(ℝ, F)) b₀).symmL ℝ b v
      = ContinuousLinearMap.id ℝ F v := by
    rw [symmL_trivializationAt_opens]
    rfl
  rw [Bundle.Trivialization.symmL_apply] at h
  exact h

/-- **Math.** do Carmo Ch. 1, Ex. 2.4, restricted: an open subset of Euclidean
space is a Riemannian manifold, each tangent space `T_q(↥s) = F` carrying the
ambient inner product. This is the restriction of `DCEuclideanMetric` to `↥s`
— the ambient datum for the hypersurface examples of Ch. 6. -/
def opensEuclideanMetric (s : Opens F) : RiemannianMetric 𝓘(ℝ, F) ↥s where
  inner _ := (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ)
  symm _ v w := real_inner_comm _ _
  pos _ v hv := real_inner_self_pos.2 hv
  isVonNBounded _ := by
    change Bornology.IsVonNBounded ℝ {v : F | ⟪v, v⟫ < 1}
    have h : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← h]
    exact NormedSpace.isVonNBounded_ball ℝ F 1
  contMDiff := by
    intro x
    rw [Bundle.contMDiffAt_section]
    have h : (fun b : ↥s =>
        (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
          (fun y : ↥s => TangentSpace 𝓘(ℝ, F) y →L[ℝ] TangentSpace 𝓘(ℝ, F) y →L[ℝ] ℝ)
          x ⟨b, (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ)⟩).2)
        = fun _ : ↥s => (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ) := by
      funext b
      ext v w
      rw [hom_trivializationAt_apply]
      rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial ↥s ℝ)
        (show b ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet from
          FiberBundle.mem_baseSet_trivializationAt' b)
        (show b ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet from
          FiberBundle.mem_baseSet_trivializationAt' b)
        (by simp)]
      have htriv : trivializationAt ℝ (Bundle.Trivial ↥s ℝ) x
          = Bundle.Trivial.trivialization ↥s ℝ :=
        Bundle.Trivial.eq_trivialization ↥s ℝ _
      simp only [htriv, Bundle.Trivial.linearMapAt_trivialization]
      simp
      rfl
    rw [h]
    exact contMDiffAt_const

/-- **Math.** The restricted Euclidean metric is the ambient inner product on
every tangent space. -/
theorem opensEuclideanMetric_apply (q : ↥s) (v w : TangentSpace 𝓘(ℝ, F) q) :
    (opensEuclideanMetric s).metricInner q v w = @inner ℝ F _ v w :=
  rfl

end Metric

/-! ## The flat connection on an open subset -/

section Connection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] {s : Opens F}

/-- **Math.** The **flat covariant derivative** on the open subset:
`(∇_X Y)(q) = d(Ŷ)_q(X q)`, the ordinary directional derivative of the
zero-extension of `Y` along `X`. -/
def opensEuclideanCov (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    SmoothVectorField 𝓘(ℝ, F) ↥s :=
  SmoothVectorField.ofOpens (fun q => fderiv ℝ (s.extendZero ⇑Y) q.val (X q)) (by
    intro q
    have hY : ContDiffAt ℝ ∞ (fun x : F => fderiv ℝ (s.extendZero ⇑Y) x) q.val :=
      (Y.contDiffAt_extendZero q).fderiv_right (by simp)
    have hval : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (Subtype.val : ↥s → F) q :=
      contMDiff_subtype_val_opens q
    have hfd : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F →L[ℝ] F) ∞
        (fun p : ↥s => fderiv ℝ (s.extendZero ⇑Y) p.val) q :=
      hY.comp_contMDiffAt (x := q) hval
    exact hfd.clm_apply (X.contMDiff_opens q))

omit [CompleteSpace F] in
@[simp] theorem opensEuclideanCov_apply (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s)
    (q : ↥s) :
    opensEuclideanCov X Y q = fderiv ℝ (s.extendZero ⇑Y) q.val (X q) := rfl

/-! ### Zero-extension algebra for bundled fields -/

omit [CompleteSpace F] in
theorem extendZero_add_field (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    s.extendZero ⇑(X + Y)
      = s.extendZero (⇑X : ↥s → F) + s.extendZero (⇑Y : ↥s → F) := by
  funext x
  rw [Pi.add_apply]
  by_cases hx : x ∈ s
  · rw [s.extendZero_apply_of_mem _ hx, s.extendZero_apply_of_mem _ hx,
      s.extendZero_apply_of_mem _ hx]
    rfl
  · rw [s.extendZero_apply_of_notMem _ hx, s.extendZero_apply_of_notMem _ hx,
      s.extendZero_apply_of_notMem _ hx, add_zero]

omit [CompleteSpace F] in
theorem extendZero_smul_field {f : ↥s → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    (Y : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    s.extendZero ⇑(SmoothVectorField.smul f hf Y)
      = fun x => s.extendZero f x • s.extendZero (⇑Y : ↥s → F) x := by
  funext x
  by_cases hx : x ∈ s
  · rw [s.extendZero_apply_of_mem _ hx, s.extendZero_apply_of_mem _ hx,
      s.extendZero_apply_of_mem _ hx]
    rfl
  · rw [s.extendZero_apply_of_notMem _ hx, s.extendZero_apply_of_notMem _ hx,
      s.extendZero_apply_of_notMem _ hx, smul_zero]

omit [CompleteSpace F] in
theorem extendZero_inner_fields (Y Z : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    s.extendZero (fun q => (opensEuclideanMetric s).metricInner q (Y q) (Z q))
      = fun x => ⟪s.extendZero (⇑Y : ↥s → F) x, s.extendZero (⇑Z : ↥s → F) x⟫ := by
  funext x
  by_cases hx : x ∈ s
  · rw [s.extendZero_apply_of_mem _ hx, s.extendZero_apply_of_mem _ hx,
      s.extendZero_apply_of_mem _ hx]
    rfl
  · rw [s.extendZero_apply_of_notMem _ hx, s.extendZero_apply_of_notMem _ hx,
      s.extendZero_apply_of_notMem _ hx, inner_zero_left]

/-- **Math.** do Carmo Ch. 2 §2 on an open subset of Euclidean space: the
directional derivative `∇_X Y = dŶ(X)` is an affine connection. -/
def opensEuclideanConnection : AffineConnection 𝓘(ℝ, F) ↥s where
  cov := opensEuclideanCov
  add_left := by
    intro X Y Z
    ext q
    show fderiv ℝ (s.extendZero ⇑Z) q.val (X q + Y q)
      = fderiv ℝ (s.extendZero ⇑Z) q.val (X q) + fderiv ℝ (s.extendZero ⇑Z) q.val (Y q)
    exact (fderiv ℝ (s.extendZero ⇑Z) q.val).map_add _ _
  smul_left := by
    intro f hf X Z
    ext q
    show fderiv ℝ (s.extendZero ⇑Z) q.val (f q • X q)
      = f q • fderiv ℝ (s.extendZero ⇑Z) q.val (X q)
    exact (fderiv ℝ (s.extendZero ⇑Z) q.val).map_smul _ _
  add_right := by
    intro X Y Z
    ext q
    show fderiv ℝ (s.extendZero ⇑(Y + Z)) q.val (X q)
      = opensEuclideanCov X Y q + opensEuclideanCov X Z q
    rw [extendZero_add_field]
    rw [fderiv_add ((Y.contDiffAt_extendZero q).differentiableAt (by simp))
      ((Z.contDiffAt_extendZero q).differentiableAt (by simp))]
    rfl
  leibniz := by
    intro f hf X Y q
    have hfd : DifferentiableAt ℝ (s.extendZero f) q.val :=
      (contMDiffAt_opens_iff_extendZero.mp (hf q)).differentiableAt (by simp)
    have hYd : DifferentiableAt ℝ (s.extendZero (⇑Y : ↥s → F)) q.val :=
      (Y.contDiffAt_extendZero q).differentiableAt (by simp)
    show fderiv ℝ (s.extendZero ⇑(SmoothVectorField.smul f hf Y)) q.val (X q)
      = f q • opensEuclideanCov X Y q + (X.dir f q) • (Y q)
    rw [extendZero_smul_field hf Y]
    have h : fderiv ℝ (fun x => s.extendZero f x • s.extendZero (⇑Y : ↥s → F) x) q.val
        = s.extendZero f q.val • fderiv ℝ (s.extendZero (⇑Y : ↥s → F)) q.val
          + (fderiv ℝ (s.extendZero f) q.val).smulRight
              (s.extendZero (⇑Y : ↥s → F) q.val) :=
      fderiv_smul hfd hYd
    rw [h]
    rw [X.dir_opens_eq hf q]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [s.extendZero_val, s.extendZero_val]
    rfl

@[simp] theorem opensEuclideanConnection_cov_apply
    (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) (q : ↥s) :
    (opensEuclideanConnection (F := F) (s := s)).cov X Y q
      = fderiv ℝ (s.extendZero ⇑Y) q.val (X q) := rfl

/-- **Math.** The flat connection on `↥s` is **symmetric**:
`∇_X Y − ∇_Y X = dŶ(X) − dX̂(Y) = [X, Y]`. -/
theorem opensEuclideanConnection_isSymmetric :
    (opensEuclideanConnection (F := F) (s := s)).IsSymmetric := by
  intro X Y q
  rw [opensEuclideanConnection_cov_apply, opensEuclideanConnection_cov_apply,
    DCLieBracket_opens_eq_fderiv]

/-- **Math.** The flat connection on `↥s` is **compatible with the restricted
Euclidean metric**: `X⟪Y, Z⟫ = ⟪dŶ(X), Z⟫ + ⟪Y, dẐ(X)⟫`, the product rule for
the inner product. -/
theorem opensEuclideanConnection_isMetricCompatible :
    (opensEuclideanConnection (F := F) (s := s)).IsMetricCompatible
      (opensEuclideanMetric s) := by
  intro X Y Z q
  have hYd : DifferentiableAt ℝ (s.extendZero (⇑Y : ↥s → F)) q.val :=
    (Y.contDiffAt_extendZero q).differentiableAt (by simp)
  have hZd : DifferentiableAt ℝ (s.extendZero (⇑Z : ↥s → F)) q.val :=
    (Z.contDiffAt_extendZero q).differentiableAt (by simp)
  have hsc : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun p => (opensEuclideanMetric s).metricInner p (Y p) (Z p)) := by
    intro p
    rw [contMDiffAt_opens_iff_extendZero, extendZero_inner_fields]
    exact ((Y.contDiffAt_extendZero p).inner ℝ (Z.contDiffAt_extendZero p))
  rw [X.dir_opens_eq hsc q, extendZero_inner_fields]
  have hinner : fderiv ℝ
      (fun x => ⟪s.extendZero (⇑Y : ↥s → F) x, s.extendZero (⇑Z : ↥s → F) x⟫)
      q.val (X q)
      = ⟪s.extendZero (⇑Y : ↥s → F) q.val,
          fderiv ℝ (s.extendZero (⇑Z : ↥s → F)) q.val (X q)⟫
        + ⟪fderiv ℝ (s.extendZero (⇑Y : ↥s → F)) q.val (X q),
            s.extendZero (⇑Z : ↥s → F) q.val⟫ :=
    fderiv_inner_apply (𝕜 := ℝ) hYd hZd (X q)
  rw [hinner, s.extendZero_val, s.extendZero_val]
  show @inner ℝ F _ (Y q) (fderiv ℝ (s.extendZero ⇑Z) q.val (X q))
      + @inner ℝ F _ (fderiv ℝ (s.extendZero ⇑Y) q.val (X q)) (Z q)
    = @inner ℝ F _ (fderiv ℝ (s.extendZero ⇑Y) q.val (X q)) (Z q)
      + @inner ℝ F _ (Y q) (fderiv ℝ (s.extendZero ⇑Z) q.val (X q))
  ring

/-- **Math.** do Carmo Ch. 2 §2: the directional derivative is the
**Levi-Civita connection** of the restricted Euclidean metric. -/
theorem opensEuclideanConnection_isLeviCivita :
    (opensEuclideanConnection (F := F) (s := s)).IsLeviCivita
      (opensEuclideanMetric s) :=
  ⟨opensEuclideanConnection_isSymmetric, opensEuclideanConnection_isMetricCompatible⟩

/-- **Math.** do Carmo Ch. 4, Example 4.1, restricted: the curvature of an open
subset of Euclidean space **vanishes**. The second-order terms cancel by
symmetry of the second derivative (Schwarz), the first-order terms against the
bracket term. -/
theorem opensEuclideanConnection_curvature (X Y Z : SmoothVectorField 𝓘(ℝ, F) ↥s) :
    (opensEuclideanConnection (F := F) (s := s)).curvature X Y Z = 0 := by
  ext q
  rw [AffineConnection.curvature_apply, SmoothVectorField.zero_apply]
  have hZ' : DifferentiableAt ℝ (fderiv ℝ (s.extendZero (⇑Z : ↥s → F))) q.val :=
    ((Z.contDiffAt_extendZero q).fderiv_right (m := ∞)
      (by simp)).differentiableAt (by simp)
  -- second covariant derivatives via the product rule for `x ↦ dẐ_x(V̂ x)`
  have hsecond : ∀ V W : SmoothVectorField 𝓘(ℝ, F) ↥s,
      ((opensEuclideanConnection (F := F) (s := s)).cov W
        ((opensEuclideanConnection (F := F) (s := s)).cov V Z) q : F)
        = fderiv ℝ (fderiv ℝ (s.extendZero (⇑Z : ↥s → F))) q.val (W q) (V q)
          + fderiv ℝ (s.extendZero (⇑Z : ↥s → F)) q.val
              (fderiv ℝ (s.extendZero (⇑V : ↥s → F)) q.val (W q)) := by
    intro V W
    have hVd : DifferentiableAt ℝ (s.extendZero (⇑V : ↥s → F)) q.val :=
      (V.contDiffAt_extendZero q).differentiableAt (by simp)
    -- the extension of `∇_V Z` agrees near `q` with `x ↦ dẐ_x(V̂ x)`
    have hev : s.extendZero ⇑((opensEuclideanConnection (F := F) (s := s)).cov V Z)
        =ᶠ[𝓝 q.val]
          (fun x => fderiv ℝ (s.extendZero (⇑Z : ↥s → F)) x
            (s.extendZero (⇑V : ↥s → F) x)) := by
      filter_upwards [s.isOpen.mem_nhds q.2] with x hx
      rw [s.extendZero_apply_of_mem _ hx, s.extendZero_apply_of_mem _ hx]
      rfl
    show fderiv ℝ (s.extendZero
        ⇑((opensEuclideanConnection (F := F) (s := s)).cov V Z)) q.val (W q) = _
    rw [hev.fderiv_eq]
    rw [fderiv_clm_apply hZ' hVd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [s.extendZero_val]
    exact add_comm _ _
  -- the bracket term
  have hbr : ((opensEuclideanConnection (F := F) (s := s)).cov
        (bracketField X Y) Z q : F)
      = fderiv ℝ (s.extendZero (⇑Z : ↥s → F)) q.val
          (fderiv ℝ (s.extendZero (⇑Y : ↥s → F)) q.val (X q))
        - fderiv ℝ (s.extendZero (⇑Z : ↥s → F)) q.val
          (fderiv ℝ (s.extendZero (⇑X : ↥s → F)) q.val (Y q)) := by
    have h1 : ((bracketField X Y) q : F)
        = fderiv ℝ (s.extendZero (⇑Y : ↥s → F)) q.val (X q)
          - fderiv ℝ (s.extendZero (⇑X : ↥s → F)) q.val (Y q) := by
      rw [bracketField_apply]
      exact DCLieBracket_opens_eq_fderiv X Y q
    show fderiv ℝ (s.extendZero ⇑Z) q.val ((bracketField X Y) q) = _
    rw [h1]
    exact (fderiv ℝ (s.extendZero (⇑Z : ↥s → F)) q.val).map_sub _ _
  have hschwarz : fderiv ℝ (fderiv ℝ (s.extendZero (⇑Z : ↥s → F))) q.val
      (Y q) (X q)
      = fderiv ℝ (fderiv ℝ (s.extendZero (⇑Z : ↥s → F))) q.val (X q) (Y q) :=
    ((Z.contDiffAt_extendZero q).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.mpr le_top)) (Y q) (X q)
  show ((opensEuclideanConnection (F := F) (s := s)).cov Y
      ((opensEuclideanConnection (F := F) (s := s)).cov X Z) q : F)
      - (opensEuclideanConnection (F := F) (s := s)).cov X
          ((opensEuclideanConnection (F := F) (s := s)).cov Y Z) q
      + (opensEuclideanConnection (F := F) (s := s)).cov (bracketField X Y) Z q
    = (0 : F)
  rw [hsecond X Y, hsecond Y X, hbr, hschwarz]
  abel

/-- **Math.** An open subset of Euclidean space has **constant sectional
curvature `0`** in the four-field form used by the Ch. 6 fundamental
equations. -/
theorem opensEuclideanConnection_isConstantCurvature_zero :
    (opensEuclideanConnection (F := F) (s := s)).IsConstantCurvature
      (opensEuclideanMetric s) 0 := by
  intro X Y Z W q
  rw [opensEuclideanConnection_curvature X Y Z, SmoothVectorField.zero_apply,
    (opensEuclideanMetric s).metricInner_zero_left]
  ring

end Connection

end Riemannian
