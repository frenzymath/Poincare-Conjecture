/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import PetersenLib.Ch03.AlgebraicCurvatureForm
import PetersenLib.Ch03.CurvaturePointwise
import PetersenLib.Ch03.SectionalCurvature

/-!
# Complex sectional curvature (Petersen, Exercise 3.4.17)

Petersen §3.4, Exercise 3.4.17 introduces the **complexified tangent bundle**
`T_ℂM = TM ⊗ ℂ`.  A complex tangent vector is `v = v₁ + i v₂` with
`v₁, v₂ ∈ TM`; conjugation is `v̄ = v₁ - i v₂`.  A real Riemannian metric `g`
extends `ℂ`-bilinearly to `g_ℂ` and induces the **Hermitian form**
`h(v, w) = g_ℂ(v, w̄)`.  A vector is **isotropic** if `g_ℂ(v, v) = 0`, and the
**complex sectional curvature** of Hermitian-orthonormal `v, w` is
`R_ℂ(v, w, w̄, v̄)`, the value of the `ℂ`-4-linear extension of the `(0,4)`
curvature tensor.

This file develops the pointwise linear algebra of the exercise over an abstract
real vector space `V` (played by each tangent space `T_pM`), with:

* `gExt G` — the `ℂ`-bilinear extension of a real symmetric form `G`, on complex
  vectors given as component pairs;
* `hermExt G` — the induced Hermitian form `h(v, w) = g_ℂ(v, w̄)`;
* `IsIsotropicPair G` — the isotropy condition `g_ℂ(v, v) = 0`;
* `curvExt R` — the `ℂ`-4-linear extension of a real 4-linear form `R`
  (built by extending one slot at a time, `cExt`).

The exercise's claims are then:

* **(1)** `isIsotropicPair_of_orthogonal_eq_length` — `v = v₁ + i v₂` is isotropic
  when `v₁ ⟂ v₂` and `|v₁| = |v₂|`.
* **(2)** `orthonormal_of_isotropic_hermOrthonormalPlane` — if an isotropic plane
  is spanned by isotropic Hermitian-orthonormal `v, w`, then `v₁, v₂, w₁, w₂`
  are pairwise orthogonal of common squared length `1/2` (Petersen's
  "orthonormal", up to the `√2` normalisation coming from `h(v,v) = 1`).
* **(3)** `curvExt_conjPair_im_eq_zero` — the complex sectional curvature
  `R_ℂ(v, w, w̄, v̄)` is always a **real** number.

The manifold-level packaging `exercise3_4_17` bundles (1)–(3) for the pointwise
curvature form `curvatureTensorFourAt D p` and metric `g.metricInner p`.

Parts (4) (quarter-pinching ⟹ positivity) and (5) (curvature-operator
positivity) of the exercise are the Berger inequalities; they are not formalised
here (they need the full real expansion of `R_ℂ` together with Berger's estimate)
and are flagged in the blueprint.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), Exercise 3.4.17,
pages 124–125.
-/

noncomputable section

namespace PetersenLib

open scoped ComplexConjugate ContDiff Manifold Topology Bundle
open Complex

set_option linter.unusedSectionVars false

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## Complexification of a real vector space via component pairs

A complex vector `v = v₁ + i v₂` is encoded by the ordered pair `(v₁, v₂)`.  We
keep the two real components explicit in every definition so that all identities
reduce to real algebra plus the arithmetic of `ℂ`. -/

/-- **Math.** The `ℂ`-bilinear extension `g_ℂ` of a real bilinear form `G`,
evaluated on the complex vectors `v₁ + i v₂` and `w₁ + i w₂`:
`g_ℂ(v, w) = (G(v₁,w₁) - G(v₂,w₂)) + i (G(v₁,w₂) + G(v₂,w₁))`. -/
def gExt (G : V → V → ℝ) (v₁ v₂ w₁ w₂ : V) : ℂ :=
  ((G v₁ w₁ - G v₂ w₂ : ℝ) : ℂ) + ((G v₁ w₂ + G v₂ w₁ : ℝ) : ℂ) * Complex.I

/-- **Math.** The Hermitian form `h(v, w) = g_ℂ(v, w̄)` induced by `G`
(Petersen: `g(v,w) = g_ℂ(v, w̄) = g(v₁,w₁)+g(v₂,w₂)+i(g(v₂,w₁)-g(v₁,w₂))`). -/
def hermExt (G : V → V → ℝ) (v₁ v₂ w₁ w₂ : V) : ℂ :=
  ((G v₁ w₁ + G v₂ w₂ : ℝ) : ℂ) + ((G v₂ w₁ - G v₁ w₂ : ℝ) : ℂ) * Complex.I

/-- **Math.** A complex vector `v = v₁ + i v₂` is **isotropic** if the
`ℂ`-bilinear form vanishes on it, `g_ℂ(v, v) = 0`. -/
def IsIsotropicPair (G : V → V → ℝ) (v₁ v₂ : V) : Prop :=
  gExt G v₁ v₂ v₁ v₂ = 0

/-! ### Part (1): isotropy from orthogonal, equal-length real parts -/

/-- **Math.** Petersen Exercise 3.4.17(1): if `v₁, v₂` are orthogonal and of
the same length then `v = v₁ + i v₂` is isotropic. -/
theorem isIsotropicPair_of_orthogonal_eq_length (G : V → V → ℝ)
    (hSymm : ∀ x y, G x y = G y x) {v₁ v₂ : V}
    (hOrth : G v₁ v₂ = 0) (hLen : G v₁ v₁ = G v₂ v₂) :
    IsIsotropicPair G v₁ v₂ := by
  have himg : G v₁ v₂ + G v₂ v₁ = 0 := by rw [hSymm v₂ v₁, hOrth]; ring
  have hre : G v₁ v₁ - G v₂ v₂ = 0 := by rw [hLen]; ring
  simp only [IsIsotropicPair, gExt, hre, himg, Complex.ofReal_zero, zero_mul, add_zero]

/-- **Math.** Conversely, an isotropic `v = v₁ + i v₂` has orthogonal real parts
of equal length: this reads off the vanishing of the real and imaginary parts of
`g_ℂ(v,v)`. -/
theorem orthogonal_eq_length_of_isIsotropicPair (G : V → V → ℝ)
    (hSymm : ∀ x y, G x y = G y x) {v₁ v₂ : V}
    (hIso : IsIsotropicPair G v₁ v₂) :
    G v₁ v₂ = 0 ∧ G v₁ v₁ = G v₂ v₂ := by
  simp only [IsIsotropicPair, gExt] at hIso
  have hre : G v₁ v₁ - G v₂ v₂ = 0 := by
    have := congrArg Complex.re hIso
    simpa using this
  have himg : G v₁ v₂ + G v₂ v₁ = 0 := by
    have := congrArg Complex.im hIso
    simpa using this
  rw [hSymm v₂ v₁] at himg
  refine ⟨by linarith, by linarith⟩

/-! ### Part (2): an isotropic Hermitian-orthonormal plane gives an orthogonal
real frame of common squared length `1/2` -/

/-- **Math.** Petersen Exercise 3.4.17(2): if an isotropic plane is spanned by
two isotropic, Hermitian-orthonormal vectors `v = v₁ + i v₂`, `w = w₁ + i w₂`,
then the four real vectors `v₁, v₂, w₁, w₂` are pairwise orthogonal and all have
the same squared length `1/2`.  (Petersen calls this "orthonormal"; the `1/2`
is the `√2`-normalisation forced by `h(v,v) = 1`.) -/
theorem orthonormal_of_isotropic_hermOrthonormalPlane (G : V → V → ℝ)
    (hSymm : ∀ x y, G x y = G y x) {v₁ v₂ w₁ w₂ : V}
    (hIsoV : IsIsotropicPair G v₁ v₂) (hIsoW : IsIsotropicPair G w₁ w₂)
    (hPlane : gExt G v₁ v₂ w₁ w₂ = 0)
    (hNormV : hermExt G v₁ v₂ v₁ v₂ = 1) (hNormW : hermExt G w₁ w₂ w₁ w₂ = 1)
    (hOrthVW : hermExt G v₁ v₂ w₁ w₂ = 0) :
    (G v₁ v₂ = 0 ∧ G w₁ w₂ = 0 ∧
      G v₁ w₁ = 0 ∧ G v₁ w₂ = 0 ∧ G v₂ w₁ = 0 ∧ G v₂ w₂ = 0) ∧
    (G v₁ v₁ = 1 / 2 ∧ G v₂ v₂ = 1 / 2 ∧ G w₁ w₁ = 1 / 2 ∧ G w₂ w₂ = 1 / 2) := by
  obtain ⟨hVo, hVl⟩ := orthogonal_eq_length_of_isIsotropicPair G hSymm hIsoV
  obtain ⟨hWo, hWl⟩ := orthogonal_eq_length_of_isIsotropicPair G hSymm hIsoW
  -- span isotropic: real and imaginary parts of `g_ℂ(v, w) = 0`
  have hPre : G v₁ w₁ - G v₂ w₂ = 0 := by
    have := congrArg Complex.re hPlane; simpa [gExt] using this
  have hPim : G v₁ w₂ + G v₂ w₁ = 0 := by
    have := congrArg Complex.im hPlane; simpa [gExt] using this
  -- Hermitian norms
  have hVn : G v₁ v₁ + G v₂ v₂ = 1 := by
    have := congrArg Complex.re hNormV; simpa [hermExt] using this
  have hWn : G w₁ w₁ + G w₂ w₂ = 1 := by
    have := congrArg Complex.re hNormW; simpa [hermExt] using this
  -- Hermitian orthogonality of `v, w`
  have hOre : G v₁ w₁ + G v₂ w₂ = 0 := by
    have := congrArg Complex.re hOrthVW; simpa [hermExt] using this
  have hOim : G v₂ w₁ - G v₁ w₂ = 0 := by
    have := congrArg Complex.im hOrthVW; simpa [hermExt] using this
  refine ⟨⟨hVo, hWo, ?_, ?_, ?_, ?_⟩, ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · linarith          -- G v₁ w₁ = 0
  · linarith          -- G v₁ w₂ = 0
  · linarith          -- G v₂ w₁ = 0
  · linarith          -- G v₂ w₂ = 0

/-! ### Part (3): the complex sectional curvature is real

We build the `ℂ`-4-linear extension `R_ℂ` of a real 4-linear form `R` by
extending one argument at a time (`cExt`), and show that
`R_ℂ(v, w, w̄, v̄)` is always real. -/

/-- One-slot `ℂ`-linear extension: `cExt f (a₁, a₂) = f a₁ + i · f a₂`,
extending a `ℂ`-valued function of a real vector to the complex vector
`a₁ + i a₂`. -/
def cExt (f : V → ℂ) (a₁ a₂ : V) : ℂ := f a₁ + Complex.I * f a₂

/-- **Math.** The `ℂ`-4-linear extension `R_ℂ` of a real 4-linear form `R`,
evaluated on the complex vectors `v₁ + i v₂`, `w₁ + i w₂`, `x₁ + i x₂`,
`y₁ + i y₂`.  Built by extending each slot with `cExt`. -/
def curvExt (R : V → V → V → V → ℝ) (v₁ v₂ w₁ w₂ x₁ x₂ y₁ y₂ : V) : ℂ :=
  cExt (fun a => cExt (fun b => cExt (fun c =>
    cExt (fun d => ((R a b c d : ℝ) : ℂ)) y₁ y₂) x₁ x₂) w₁ w₂) v₁ v₂

/-- Pulling a global sign out of the `ℂ`-4-linear extension. -/
theorem curvExt_neg (R : V → V → V → V → ℝ) (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : V) :
    curvExt (fun a b c d => -R a b c d) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂
      = - curvExt R a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ := by
  simp only [curvExt, cExt]; push_cast; ring

/-- The extension is antisymmetric in the first pair of complex slots
(inherited from `hR.antisymm₁₂`). -/
theorem curvExt_antisymm₁₂ {R : V → V → V → V → ℝ} (hR : IsAlgCurvatureForm R)
    (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : V) :
    curvExt R a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ = - curvExt R b₁ b₂ a₁ a₂ c₁ c₂ d₁ d₂ := by
  have key : curvExt R b₁ b₂ a₁ a₂ c₁ c₂ d₁ d₂
      = curvExt (fun a b c d => R b a c d) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ := by
    simp only [curvExt, cExt]; ring
  have hfun : (fun a b c d => R b a c d) = fun a b c d => -R a b c d := by
    funext a b c d; exact hR.antisymm₁₂ b a c d
  rw [key, hfun, curvExt_neg]; ring

/-- The extension is antisymmetric in the second pair of complex slots
(inherited from `hR.antisymm₃₄`). -/
theorem curvExt_antisymm₃₄ {R : V → V → V → V → ℝ} (hR : IsAlgCurvatureForm R)
    (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : V) :
    curvExt R a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ = - curvExt R a₁ a₂ b₁ b₂ d₁ d₂ c₁ c₂ := by
  have key : curvExt R a₁ a₂ b₁ b₂ d₁ d₂ c₁ c₂
      = curvExt (fun a b c d => R a b d c) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ := by
    simp only [curvExt, cExt]; ring
  have hfun : (fun a b c d => R a b d c) = fun a b c d => -R a b c d := by
    funext a b c d; exact hR.antisymm₃₄ a b d c
  rw [key, hfun, curvExt_neg]; ring

/-- Pair-swap symmetry of the extension (inherited from `hR.pairSwap`). -/
theorem curvExt_pairSwap {R : V → V → V → V → ℝ} (hR : IsAlgCurvatureForm R)
    (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : V) :
    curvExt R a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ = curvExt R c₁ c₂ d₁ d₂ a₁ a₂ b₁ b₂ := by
  have key : curvExt R c₁ c₂ d₁ d₂ a₁ a₂ b₁ b₂
      = curvExt (fun a b c d => R c d a b) a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ := by
    simp only [curvExt, cExt]; ring
  have hfun : (fun a b c d => R c d a b) = fun a b c d => R a b c d := by
    funext a b c d; exact hR.pairSwap c d a b
  rw [key, hfun]

/-- **Math.** Conjugating the extension is the same as negating the imaginary
component of every complex slot: `conj (R_ℂ(v,w,x,y)) = R_ℂ(v̄, w̄, x̄, ȳ)`.
Uses that `R` is real and multilinear. -/
theorem curvExt_conj {R : V → V → V → V → ℝ} (hR : IsAlgCurvatureForm R)
    (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : V) :
    curvExt R a₁ (-a₂) b₁ (-b₂) c₁ (-c₂) d₁ (-d₂)
      = starRingEnd ℂ (curvExt R a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂) := by
  have hN1 : ∀ x y z t : V, R (-x) y z t = -R x y z t := fun x y z t => by
    rw [← neg_one_smul ℝ x, hR.smul_left]; ring
  have hN2 : ∀ x y z t : V, R x (-y) z t = -R x y z t := fun x y z t => by
    rw [← neg_one_smul ℝ y, hR.smul_two]; ring
  have hN3 : ∀ x y z t : V, R x y (-z) t = -R x y z t := fun x y z t => by
    rw [← neg_one_smul ℝ z, hR.smul_three]; ring
  have hN4 : ∀ x y z t : V, R x y z (-t) = -R x y z t := fun x y z t => by
    rw [← neg_one_smul ℝ t, hR.smul_four]; ring
  simp only [curvExt, cExt, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal,
    hN1, hN2, hN3, hN4]
  push_cast
  ring

/-- **Math.** Petersen Exercise 3.4.17(3): the complex sectional curvature
`R_ℂ(v, w, w̄, v̄)` is always a **real** number.  Follows from the reality and
symmetries of `R` via `conj(R_ℂ(v,w,w̄,v̄)) = R_ℂ(v,w,w̄,v̄)`. -/
theorem curvExt_conjPair_im_eq_zero {R : V → V → V → V → ℝ}
    (hR : IsAlgCurvatureForm R) (v₁ v₂ w₁ w₂ : V) :
    (curvExt R v₁ v₂ w₁ w₂ w₁ (-w₂) v₁ (-v₂)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  rw [← curvExt_conj hR]
  simp only [neg_neg]
  rw [curvExt_pairSwap hR, curvExt_antisymm₁₂ hR, curvExt_antisymm₃₄ hR]
  ring

/-! ## Manifold-level packaging (Exercise 3.4.17) -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Petersen Exercise 3.4.17, formalised pointwise at a tangent space
`T_pM` for the metric `g` and the `(0,4)`-curvature tensor of a Riemannian
connection `D`.  Bundling the three structural claims:

* **(1)** if `v₁ ⟂ v₂` and `|v₁| = |v₂|` then `v = v₁ + i v₂` is isotropic;
* **(2)** an isotropic plane spanned by isotropic Hermitian-orthonormal
  `v = v₁ + i v₂`, `w = w₁ + i w₂` has `v₁, v₂, w₁, w₂` pairwise orthogonal of
  common squared length `1/2` (Petersen's "orthonormal");
* **(3)** the complex sectional curvature `R_ℂ(v, w, w̄, v̄)` is always real.

Parts (4) (quarter-pinching ⟹ positivity) and (5) (curvature-operator
positivity) are the Berger inequalities and are not formalised here. -/
theorem exercise3_4_17 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    (p : M) :
    (∀ v₁ v₂ : TangentSpace I p, g.metricInner p v₁ v₂ = 0 →
        g.metricInner p v₁ v₁ = g.metricInner p v₂ v₂ →
        IsIsotropicPair (g.metricInner p) v₁ v₂) ∧
    (∀ v₁ v₂ w₁ w₂ : TangentSpace I p,
        IsIsotropicPair (g.metricInner p) v₁ v₂ →
        IsIsotropicPair (g.metricInner p) w₁ w₂ →
        gExt (g.metricInner p) v₁ v₂ w₁ w₂ = 0 →
        hermExt (g.metricInner p) v₁ v₂ v₁ v₂ = 1 →
        hermExt (g.metricInner p) w₁ w₂ w₁ w₂ = 1 →
        hermExt (g.metricInner p) v₁ v₂ w₁ w₂ = 0 →
        (g.metricInner p v₁ v₂ = 0 ∧ g.metricInner p w₁ w₂ = 0 ∧
          g.metricInner p v₁ w₁ = 0 ∧ g.metricInner p v₁ w₂ = 0 ∧
          g.metricInner p v₂ w₁ = 0 ∧ g.metricInner p v₂ w₂ = 0) ∧
        (g.metricInner p v₁ v₁ = 1 / 2 ∧ g.metricInner p v₂ v₂ = 1 / 2 ∧
          g.metricInner p w₁ w₁ = 1 / 2 ∧ g.metricInner p w₂ w₂ = 1 / 2)) ∧
    (∀ v₁ v₂ w₁ w₂ : TangentSpace I p,
        (curvExt (fun x y z t => curvatureTensorFourAt D p x y z t)
          v₁ v₂ w₁ w₂ w₁ (-w₂) v₁ (-v₂)).im = 0) := by
  have hSymm : ∀ x y : TangentSpace I p,
      g.metricInner p x y = g.metricInner p y x := fun x y => g.metricInner_comm p x y
  have hR := isAlgCurvatureForm_curvatureTensorFourAt D p
  refine ⟨?_, ?_, ?_⟩
  · intro v₁ v₂ h1 h2
    exact isIsotropicPair_of_orthogonal_eq_length _ hSymm h1 h2
  · intro v₁ v₂ w₁ w₂ hIsoV hIsoW hPlane hNormV hNormW hOrthVW
    exact orthonormal_of_isotropic_hermOrthonormalPlane _ hSymm hIsoV hIsoW hPlane
      hNormV hNormW hOrthVW
  · intro v₁ v₂ w₁ w₂
    exact curvExt_conjPair_im_eq_zero hR v₁ v₂ w₁ w₂

end Manifold

end PetersenLib
