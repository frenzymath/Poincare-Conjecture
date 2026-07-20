import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Sphere

/-!
# do Carmo Chapter 6, Example 2.4 — the Gauss spherical mapping

For a hypersurface patch (codimension `1`) in an open subset `A` of Euclidean
space `F = ℝⁿ⁺¹`, with a smooth **unit normal field** `N`, do Carmo's *Gauss
spherical mapping* `g : M → S₁ⁿ` sends `q` to the endpoint of the translate
of `N(q)` to the origin — i.e. `g(q) = N(q)` as a point of `F`
(`gaussMap`). We prove the content of do Carmo's Example 2.4:

* `gaussMap_norm` — `g` takes values in the unit sphere;
* `normalSpace_eq_span_of_unit_normal` — codimension `1`: the normal space at
  each point is exactly the line `ℝ·N(p)`;
* `fderiv_gaussMap_mem_sphereTang` — `dg_q(v)` is tangent to the unit-sphere
  leaf of the concentric-sphere foliation through `g(q)` (do Carmo's
  "`T_qM` and `T_{g(q)}S₁ⁿ` are parallel", in the identified picture of
  `spherePatch`);
* `fderiv_gaussMap_mem_tang` — `dg_q(v) ∈ T_qM`;
* `fderiv_gaussMap_eq_neg_shapeOperatorAt` — **do Carmo's identity**
  `dg_q(x) = −S_η(x)`, `η = N(q)`: the derivative of the Gauss spherical
  mapping is the negated shape operator.

The final application of Example 2.4 (a compact connected orientable `Mⁿ`
immersed in `ℝⁿ⁺¹` with nowhere-zero Gauss–Kronecker curvature is
diffeomorphic to `Sⁿ`) needs covering-space theory and remains a documented
gap, as flagged in the blueprint.

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2, Example 2.4.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open TopologicalSpace

/- As in `DoCarmoCh6Sphere`: the whole file works through the canonical
identification `TangentSpace 𝓘(ℝ, F) q = F` on the open submanifold. -/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Riemannian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {A : Opens F}

/- Fiber instances on the vector-space model, as in `DoCarmoCh6Sphere` (local:
mathlib deliberately has no canonical norm on tangent fibers, but here the
metric IS the restricted ambient inner product). -/
noncomputable local instance (q : ↥A) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, F) q) :=
  inferInstanceAs (NormedAddCommGroup F)

noncomputable local instance (q : ↥A) :
    InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, F) q) :=
  inferInstanceAs (InnerProductSpace ℝ F)

/-- **Math.** do Carmo Ch. 6, Ex. 2.4: the **Gauss spherical mapping** of a
patch with unit normal field `N` — translate `N(q)` to the origin of `F` and
take its endpoint: `g(q) = N(q)` as a point of `F`. -/
def gaussMap (N : SmoothVectorField 𝓘(ℝ, F) ↥A) : ↥A → F :=
  fun q => (N q : F)

variable {N : SmoothVectorField 𝓘(ℝ, F) ↥A}

/-- **Math.** A unit field does not vanish. -/
theorem apply_ne_zero_of_inner_self_eq_one
    (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1) (q : ↥A) :
    (N q : F) ≠ 0 := by
  intro h
  have := hunit q
  rw [h, inner_zero_left] at this
  exact zero_ne_one this

/-- **Math.** The Gauss spherical mapping takes values in the unit sphere
`S₁ⁿ = {x ∈ F : |x| = 1}`. -/
theorem gaussMap_norm (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1)
    (q : ↥A) : ‖gaussMap N q‖ = 1 := by
  have h := hunit q
  rw [real_inner_self_eq_norm_mul_norm] at h
  have h0 : (0 : ℝ) ≤ ‖(N q : F)‖ := norm_nonneg _
  have hfac : (‖(N q : F)‖ - 1) * (‖(N q : F)‖ + 1) = 0 := by
    linear_combination h
  show ‖(N q : F)‖ = 1
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · exfalso; linarith

/-- **Math.** Differentiating `⟨N, N⟩ ≡ 1`: the derivative of a unit field is
orthogonal to the field, `⟨N(p), dN̂_p(v)⟩ = 0` — do Carmo's "using
`⟨N, N⟩ = 1`" step in Example 2.4. -/
theorem inner_fderiv_extendZero_of_inner_self_eq_one
    (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1) (p : ↥A) (v : F) :
    ⟪A.extendZero ⇑N p.val, fderiv ℝ (A.extendZero ⇑N) p.val v⟫ = 0 := by
  have hNd : DifferentiableAt ℝ (A.extendZero ⇑N) p.val :=
    (N.contDiffAt_extendZero p).differentiableAt (by simp)
  -- the scalar `x ↦ ⟨N̂(x), N̂(x)⟩` is constant `1` near `p`
  have hev : (fun x : F => ⟪A.extendZero ⇑N x, A.extendZero ⇑N x⟫)
      =ᶠ[𝓝 p.val] (fun _ => (1 : ℝ)) := by
    filter_upwards [A.isOpen.mem_nhds p.2] with x hx
    rw [A.extendZero_apply_of_mem _ hx]
    exact hunit ⟨x, hx⟩
  have hfd : fderiv ℝ (fun x : F => ⟪A.extendZero ⇑N x, A.extendZero ⇑N x⟫)
      p.val = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply 1
  have hprod := fderiv_inner_apply (𝕜 := ℝ) hNd hNd v
  rw [hfd] at hprod
  simp only [ContinuousLinearMap.zero_apply] at hprod
  have hcomm := real_inner_comm (fderiv ℝ (A.extendZero ⇑N) p.val v)
    (A.extendZero ⇑N p.val)
  linarith [hprod, hcomm]

section Hypersurface

variable [FiniteDimensional ℝ F]

local instance : LocallyCompactSpace ↥A := A.isOpen.locallyCompactSpace

noncomputable local instance (q : ↥A) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, F) q) :=
  inferInstanceAs (FiniteDimensional ℝ F)

variable {D : DCImmersedPatch 𝓘(ℝ, F) ↥A (opensEuclideanMetric A)}

/-- **Math.** do Carmo Ch. 6, Ex. 2.4, the codimension-`1` normal line: for a
hypersurface patch (`dim M + 1 = dim F`) with unit normal field `N`, the
normal space at each point is exactly the line spanned by `N(p)`. -/
theorem normalSpace_eq_span_of_unit_normal
    (hdim : D.dim + 1 = Module.finrank ℝ F) (hN : D.IsNormalField N)
    (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1) (p : ↥A) :
    D.normalSpace p = ℝ ∙ (N p) := by
  have hle : ℝ ∙ (N p) ≤ D.normalSpace p :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (hN p)
  -- the normal space sits inside `(T_pM)^⊥`, which has dimension `1`
  have hle2 : D.normalSpace p ≤ (D.tang p)ᗮ := by
    intro v hv
    refine (Submodule.mem_orthogonal _ _).mpr fun u hu => ?_
    exact D.inner_eq_zero_of_mem_tang_of_mem_normalSpace hu hv
  have hsum := Submodule.finrank_add_finrank_orthogonal (K := D.tang p)
  have hfr : Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) p) = Module.finrank ℝ F :=
    rfl
  rw [D.finrank_tang p, hfr] at hsum
  have horth : Module.finrank ℝ ↥((D.tang p)ᗮ) = 1 := by omega
  have hspan : Module.finrank ℝ ↥(ℝ ∙ (N p)) = 1 :=
    finrank_span_singleton (apply_ne_zero_of_inner_self_eq_one hunit p)
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [hspan]
  calc Module.finrank ℝ ↥(D.normalSpace p)
      ≤ Module.finrank ℝ ↥((D.tang p)ᗮ) := Submodule.finrank_mono hle2
    _ = 1 := horth

/-- **Math.** Codimension-`1` tangency criterion: a vector orthogonal to the
unit normal is tangent. -/
theorem mem_tang_of_inner_unit_normal_eq_zero
    (hdim : D.dim + 1 = Module.finrank ℝ F) (hN : D.IsNormalField N)
    (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1) {p : ↥A}
    {v : TangentSpace 𝓘(ℝ, F) p} (hv : ⟪(N p : F), (v : F)⟫ = 0) :
    v ∈ D.tang p := by
  -- decompose `v = vᵀ + vᴺ` through the constant extension
  have hvsplit : v = D.tangentProj (vectorFieldExtension p v) p
      + D.normalProj (vectorFieldExtension p v) p := by
    rw [D.normalProj_apply]
    rw [vectorFieldExtension_apply_self]
    abel
  have hT : D.tangentProj (vectorFieldExtension p v) p ∈ D.tang p :=
    D.tangentProj_mem _ p
  have hNrm : D.normalProj (vectorFieldExtension p v) p ∈ D.normalSpace p :=
    D.isNormalField_normalProj _ p
  -- the normal component is a multiple of `N(p)` orthogonal to `N(p)`
  rw [normalSpace_eq_span_of_unit_normal hdim hN hunit p] at hNrm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hNrm
  -- pair the splitting against `N(p)`
  have hTperp : ⟪(N p : F),
      (D.tangentProj (vectorFieldExtension p v) p : F)⟫ = 0 := by
    have := D.inner_eq_zero_of_mem_tang_of_mem_normalSpace hT (hN p)
    rw [opensEuclideanMetric_apply] at this
    rw [real_inner_comm]
    exact this
  have hc0 : c = 0 := by
    have hpair : ⟪(N p : F), (v : F)⟫
        = ⟪(N p : F), (D.tangentProj (vectorFieldExtension p v) p : F)⟫
          + c * ⟪(N p : F), (N p : F)⟫ := by
      conv_lhs => rw [hvsplit, ← hc]
      rw [inner_add_right, real_inner_smul_right]
    rw [hv, hTperp, hunit p, mul_one, zero_add] at hpair
    linarith [hpair]
  rw [hc0, zero_smul] at hc
  rw [hvsplit, ← hc, add_zero]
  exact hT

/-- **Math.** The derivative of the Gauss spherical mapping is tangent to the
patch: `dg_q(v) ∈ T_qM` (its value is orthogonal to the unit normal, and the
patch has codimension `1`). -/
theorem fderiv_gaussMap_mem_tang
    (hdim : D.dim + 1 = Module.finrank ℝ F) (hN : D.IsNormalField N)
    (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1) (p : ↥A) (v : F) :
    fderiv ℝ (A.extendZero ⇑N) p.val v ∈ D.tang p := by
  refine mem_tang_of_inner_unit_normal_eq_zero hdim hN hunit ?_
  have h := inner_fderiv_extendZero_of_inner_self_eq_one hunit p v
  rwa [A.extendZero_val] at h

/-- **Math.** do Carmo Ch. 6, Ex. 2.4, the main identity: **the derivative of
the Gauss spherical mapping is the negated shape operator**,

`dg_q(x) = ∇̄ₓN = (∇̄ₓN)ᵀ = −S_η(x)`, `η = N(q)`,

for `x` the value at `q` of a smooth field `X`. In the identified picture the
derivative of `g` along `X` at `q` is the directional derivative
`dN̂_q(X_q)`, which is tangent by codimension `1`, and equals the negated
shape operator by the Weingarten identity (Prop. 2.3). -/
theorem fderiv_gaussMap_eq_neg_shapeOperatorAt
    (hdim : D.dim + 1 = Module.finrank ℝ F) (hN : D.IsNormalField N)
    (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1)
    (X : SmoothVectorField 𝓘(ℝ, F) ↥A) (p : ↥A) :
    fderiv ℝ (A.extendZero ⇑N) p.val (X p)
      = -D.shapeOperatorAt opensEuclideanConnection p (N p) (X p) := by
  have hcov : (opensEuclideanConnection.cov X N p : F)
      = fderiv ℝ (A.extendZero ⇑N) p.val (X p) := rfl
  have hmem : opensEuclideanConnection.cov X N p ∈ D.tang p := by
    show (opensEuclideanConnection.cov X N p : F) ∈ D.tang p
    rw [hcov]
    exact fderiv_gaussMap_mem_tang hdim hN hunit p (X p)
  have hW := D.shapeOperatorAt_eq_shapeOperator opensEuclideanConnection
    (opensEuclideanConnection_isLeviCivita (s := A)).2 (hN p) hN rfl X
  rw [hW, DCImmersedPatch.shapeOperator, SmoothVectorField.neg_apply,
    D.tangentProj_apply_of_mem hmem, neg_neg]
  exact hcov.symm

omit [FiniteDimensional ℝ F] in
/-- **Math.** do Carmo Ch. 6, Ex. 2.4, "`T_qM` and `T_{g(q)}S₁ⁿ` are
parallel": the derivative of the Gauss spherical mapping is tangent to the
unit-sphere leaf of the concentric-sphere foliation (`spherePatch`) through
`g(q)`. -/
theorem fderiv_gaussMap_mem_sphereTang
    (hunit : ∀ q : ↥A, ⟪(N q : F), (N q : F)⟫ = 1) (p : ↥A) (v : F) :
    fderiv ℝ (A.extendZero ⇑N) p.val v
      ∈ sphereTang (F := F)
          ⟨gaussMap N p, apply_ne_zero_of_inner_self_eq_one hunit p⟩ := by
  refine (Submodule.mem_orthogonal (𝕜 := ℝ) (E := F) _ _).mpr fun u hu => ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  have h := inner_fderiv_extendZero_of_inner_self_eq_one hunit p v
  rw [A.extendZero_val] at h
  show ⟪a • (gaussMap N p), fderiv ℝ (A.extendZero ⇑N) p.val v⟫ = 0
  rw [real_inner_smul_left]
  have hg : gaussMap N p = (N p : F) := rfl
  rw [hg, h, mul_zero]

end Hypersurface

end Riemannian
