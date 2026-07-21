import PetersenLib.Ch03.SectionalCurvature
import PetersenLib.Ch01.MetricConstructions

/-!
# Petersen Ch. 3, §3.4 Exercise 3.4.9 — Product metrics have vanishing mixed curvature

For Riemannian manifolds `(M₁, g₁)`, `(M₂, g₂)` with product metric
`(M₁ × M₂, g₁ + g₂)`, a vector field `X` on `M₁` and `Y` on `M₂` — regarded on
`M₁ × M₂` as the *lifts* `liftFst X (p₁,p₂) = (X p₁, 0)` and
`liftSnd Y (p₁,p₂) = (0, Y p₂)` — satisfy `∇_{liftFst X} (liftSnd Y) = 0`, and
hence `sec(liftFst X, liftSnd Y) = 0`: product metrics always have vanishing
mixed curvatures.

## Design notes

The Levi-Civita connection of a product metric **splits**:
`∇^{M₁×M₂}_{liftFst U} (liftFst V) = liftFst (∇^{M₁}_U V)` and the cross terms
`∇_{liftFst · } (liftSnd ·)` vanish. Everything is reduced to a short list of
product-manifold vector-field facts:

* the two **Lie-bracket facts** are proved *without* any chart computation,
  through the commutator-on-functions identity `lieDerivative_vectorField_eq_bracket`
  (`D_{[V,W]}f = D_V D_W f − D_W D_V f`) together with the separating test
  `tangentVector_eq_zero_of_forall_mfderiv`, testing against pullbacks `h ∘ π₁`
  and `h ∘ π₂`;
* the connection statements follow from Koszul's formula
  (`RiemannianConnection.koszul`) tested against first-factor and second-factor
  lifts, each of which annihilates all six Koszul terms.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.4 Exercise 3.4.9.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NeZero (Module.finrank ℝ E₁)] [CompleteSpace E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [SigmaCompactSpace M₁] [T2Space M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NeZero (Module.finrank ℝ E₂)] [CompleteSpace E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [SigmaCompactSpace M₂] [T2Space M₂]

/-- `NeZero (finrank (E₁ × E₂))` from `NeZero (finrank E₁)`. -/
instance : NeZero (Module.finrank ℝ (E₁ × E₂)) := by
  refine ⟨?_⟩
  rw [Module.finrank_prod]
  have h1 : Module.finrank ℝ E₁ ≠ 0 := NeZero.ne _
  omega

/-! ## Lifts of vector fields to a product -/

variable (I₂) in
/-- **Math.** The lift of a vector field `V` on `M₁` to `M₁ × M₂`:
`liftFst V (p₁,p₂) = (V p₁, 0) ∈ T_{p₁}M₁ × T_{p₂}M₂ = T_{(p₁,p₂)}(M₁ × M₂)`. -/
def liftFst (V : Π x : M₁, TangentSpace I₁ x) :
    Π x : M₁ × M₂, TangentSpace (I₁.prod I₂) x :=
  fun x => (V x.1, (0 : TangentSpace I₂ x.2))

variable (I₁) in
/-- **Math.** The lift of a vector field `W` on `M₂` to `M₁ × M₂`:
`liftSnd W (p₁,p₂) = (0, W p₂)`. -/
def liftSnd (W : Π x : M₂, TangentSpace I₂ x) :
    Π x : M₁ × M₂, TangentSpace (I₁.prod I₂) x :=
  fun x => ((0 : TangentSpace I₁ x.1), W x.2)

@[simp] theorem liftFst_apply (V : Π x : M₁, TangentSpace I₁ x) (x : M₁ × M₂) :
    liftFst I₂ V x = (V x.1, (0 : TangentSpace I₂ x.2)) := rfl

@[simp] theorem liftSnd_apply (W : Π x : M₂, TangentSpace I₂ x) (x : M₁ × M₂) :
    liftSnd I₁ W x = ((0 : TangentSpace I₁ x.1), W x.2) := rfl

/-! ## Smoothness of lifts -/

theorem isSmoothVectorField_liftFst {V : Π x : M₁, TangentSpace I₁ x}
    (hV : IsSmoothVectorField V) :
    IsSmoothVectorField (liftFst (M₂ := M₂) I₂ V) := by
  have hfst : ContMDiff (I₁.prod I₂) I₁.tangent ∞
      (fun x : M₁ × M₂ => (⟨x.1, V x.1⟩ : TangentBundle I₁ M₁)) :=
    hV.comp contMDiff_fst
  have hsnd : ContMDiff (I₁.prod I₂) I₂.tangent ∞
      (fun x : M₁ × M₂ => (⟨x.2, 0⟩ : TangentBundle I₂ M₂)) :=
    (contMDiff_zeroSection ℝ (TangentSpace I₂)).comp contMDiff_snd
  exact (contMDiff_equivTangentBundleProd_symm (I := I₁) (M := M₁) (I' := I₂) (M' := M₂)).comp
    (hfst.prodMk hsnd)

theorem isSmoothVectorField_liftSnd {W : Π x : M₂, TangentSpace I₂ x}
    (hW : IsSmoothVectorField W) :
    IsSmoothVectorField (liftSnd (M₁ := M₁) I₁ W) := by
  have hfst : ContMDiff (I₁.prod I₂) I₁.tangent ∞
      (fun x : M₁ × M₂ => (⟨x.1, 0⟩ : TangentBundle I₁ M₁)) :=
    (contMDiff_zeroSection ℝ (TangentSpace I₁)).comp contMDiff_fst
  have hsnd : ContMDiff (I₁.prod I₂) I₂.tangent ∞
      (fun x : M₁ × M₂ => (⟨x.2, W x.2⟩ : TangentBundle I₂ M₂)) :=
    hW.comp contMDiff_snd
  exact (contMDiff_equivTangentBundleProd_symm (I := I₁) (M := M₁) (I' := I₂) (M' := M₂)).comp
    (hfst.prodMk hsnd)

/-! ## Directional derivatives of pullback functions along lifts -/

/-- **G2.** `D_{liftFst V}(h ∘ π₁) = (D_V h) ∘ π₁`: differentiating an `M₁`-pullback
along a first-factor lift is the `M₁`-derivative, pulled back. -/
theorem directionalDerivative_liftFst_comp_fst
    {V : Π x : M₁, TangentSpace I₁ x} {h : M₁ → ℝ}
    (hh : MDifferentiable I₁ 𝓘(ℝ) h) (x : M₁ × M₂) :
    directionalDerivative (liftFst I₂ V) (h ∘ Prod.fst) x
      = directionalDerivative V h x.1 := by
  rw [directionalDerivative_apply, directionalDerivative_apply,
    mfderiv_comp x (hh x.1) (mdifferentiableAt_fst)]
  simp only [ContinuousLinearMap.comp_apply, liftFst_apply]
  congr 1
  rw [mfderiv_fst]
  rfl

/-- **F4.** `D_{liftFst V}(h ∘ π₂) = 0`: a first-factor lift annihilates an
`M₂`-pullback. -/
theorem directionalDerivative_liftFst_comp_snd
    {V : Π x : M₁, TangentSpace I₁ x} {h : M₂ → ℝ}
    (hh : MDifferentiable I₂ 𝓘(ℝ) h) (x : M₁ × M₂) :
    directionalDerivative (liftFst I₂ V) (h ∘ Prod.snd) x = 0 := by
  have hz : mfderiv (I₁.prod I₂) I₂ Prod.snd x (liftFst I₂ V x)
      = (0 : TangentSpace I₂ x.2) := by rw [mfderiv_snd]; rfl
  rw [directionalDerivative_apply, mfderiv_comp x (hh x.2) (mdifferentiableAt_snd)]
  show mfderiv I₂ 𝓘(ℝ) h x.2 (mfderiv (I₁.prod I₂) I₂ Prod.snd x (liftFst I₂ V x)) = 0
  rw [hz, map_zero]

/-- **G2'.** `D_{liftSnd W}(h ∘ π₂) = (D_W h) ∘ π₂`. -/
theorem directionalDerivative_liftSnd_comp_snd
    {W : Π x : M₂, TangentSpace I₂ x} {h : M₂ → ℝ}
    (hh : MDifferentiable I₂ 𝓘(ℝ) h) (x : M₁ × M₂) :
    directionalDerivative (liftSnd I₁ W) (h ∘ Prod.snd) x
      = directionalDerivative W h x.2 := by
  rw [directionalDerivative_apply, directionalDerivative_apply,
    mfderiv_comp x (hh x.2) (mdifferentiableAt_snd)]
  simp only [ContinuousLinearMap.comp_apply, liftSnd_apply]
  congr 1
  rw [mfderiv_snd]
  rfl

/-- **F4'.** `D_{liftSnd W}(h ∘ π₁) = 0`. -/
theorem directionalDerivative_liftSnd_comp_fst
    {W : Π x : M₂, TangentSpace I₂ x} {h : M₁ → ℝ}
    (hh : MDifferentiable I₁ 𝓘(ℝ) h) (x : M₁ × M₂) :
    directionalDerivative (liftSnd I₁ W) (h ∘ Prod.fst) x = 0 := by
  have hz : mfderiv (I₁.prod I₂) I₁ Prod.fst x (liftSnd I₁ W x)
      = (0 : TangentSpace I₁ x.1) := by rw [mfderiv_fst]; rfl
  rw [directionalDerivative_apply, mfderiv_comp x (hh x.1) (mdifferentiableAt_fst)]
  show mfderiv I₁ 𝓘(ℝ) h x.1 (mfderiv (I₁.prod I₂) I₁ Prod.fst x (liftSnd I₁ W x)) = 0
  rw [hz, map_zero]

end PetersenLib
