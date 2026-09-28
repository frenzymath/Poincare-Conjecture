import MorganTianLib.Ch01.RadialComparison
import MorganTianLib.Ch01.MatrixCalculus
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Morgan–Tian Ch. 1, §1.4 — the radial volume element

The volume element of the metric in geodesic polar coordinates is, in the
parallel frame of `lem:geodesic-polar-form`(3),

  `λ(r) = det 𝒥(r)`,

the determinant of the matrix Jacobi field. This file proves the identity that
drives the whole volume-comparison chain,

  `λ'(r) = λ(r) · Tr A(r)`,  equivalently  `∂_r log λ = Tr(A)`,

which is the assertion of `lem:geodesic-polar-form`(4). Combined with the trace
comparison `Tr A(r) ≤ (n−1)·sn_k'(r)/sn_k(r)` of `lem:radial-comparison`(3), it
gives `∂_r log(λ/sn_k^{n−1}) ≤ 0` — the monotonicity of the volume element
underlying `lem:volume-element-comparison`, `thm:ricci-curvature-comparison` and
`thm:bishop-gromov`.

The proof is **Jacobi's formula** `d(det)_A(B) = det A · tr(A⁻¹B)`
(`MorganTianLib.detCMM_linearDeriv_eq_smul_trace`), transported from matrices to
the endomorphism algebra `E →L[ℝ] E` through the matrix of a basis: the
determinant and trace of an endomorphism are those of its matrix, and
`𝒥(r)⁻¹𝒥'(r)` has the same trace as `A(r) = 𝒥'(r)𝒥(r)⁻¹`.

Blueprint: `lem:radial-volume-element`, `lem:geodesic-polar-form`(4).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E] [FiniteDimensional ℝ E]

variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

/-- The **radial volume element** `λ(r) = det 𝒥(r)` of
`lem:geodesic-polar-form`(4): in a parallel orthonormal frame it is the
determinant of the matrix Jacobi field, i.e.
`√(det g(r,θ)/det ĝ(θ))`. -/
def volumeElement (𝒥 : ℝ → E →L[ℝ] E) (r : ℝ) : ℝ :=
  LinearMap.det ((𝒥 r : E →L[ℝ] E) : E →ₗ[ℝ] E)

/-- The matrix of an endomorphism, as a continuous linear map into the
row-product type carrying the canonical `Pi` norm (the domain of `detCMM`). -/
private def toMat (bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    (E →L[ℝ] E) →L[ℝ] (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.toMatrix bE bE).toLinearMap).comp (ContinuousLinearMap.coeLM ℝ))

private theorem toMat_apply (bE : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (f : E →L[ℝ] E) :
    toMat bE f = LinearMap.toMatrix bE bE (f : E →ₗ[ℝ] E) := rfl

/-- **Math.** **Jacobi's formula for the matrix Jacobi field** — the derivative
of the radial volume element:
$$\lambda'(r) = \lambda(r)\,\operatorname{Tr} A(r),\qquad
\lambda(r)=\det{\mathcal J}(r),\quad A(r)={\mathcal J}'(r){\mathcal J}(r)^{-1},$$
equivalently `∂_r log λ = Tr(A)`. This is the differential identity of
`lem:geodesic-polar-form`(4).

Proof: pass to the matrix of `𝒥(r)` in a basis. The determinant is
Fréchet-differentiable with `d(det)_M(B) = det M · tr(M⁻¹B)` (Jacobi's formula,
`detCMM_linearDeriv_eq_smul_trace`), so the chain rule gives
`λ' = det 𝒥 · Tr(𝒥⁻¹𝒥')`; and `Tr(𝒥⁻¹𝒥') = Tr(𝒥'𝒥⁻¹) = Tr A` by the
cyclicity of the trace.

Blueprint: `lem:radial-volume-element`. -/
theorem hasDerivAt_volumeElement (h : IsRadialJacobi ℛ 𝒥 𝒥' b C)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) b) (hu : IsUnit (𝒥 r)) :
    HasDerivAt (volumeElement 𝒥)
      (volumeElement 𝒥 r * LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r)) r := by
  classical
  set m := Module.finrank ℝ E with hm
  set bE := Module.finBasis ℝ E with hbE
  -- The matrix curve, kept at type `Matrix` so that `*`, `⁻¹`, `det`, `trace`
  -- all use the matrix instances (the `Pi` ones would be pointwise!).
  set Mf : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun s => LinearMap.toMatrix bE bE ((𝒥 s : E →L[ℝ] E) : E →ₗ[ℝ] E) with hMf
  set Md : Matrix (Fin m) (Fin m) ℝ :=
    LinearMap.toMatrix bE bE ((𝒥' r : E →L[ℝ] E) : E →ₗ[ℝ] E) with hMd
  -- keep the inverse opaque, so that `↑(Jinv * f) = ↑Jinv * ↑f` holds by `rfl`
  set Jinv : E →L[ℝ] E := Ring.inverse (𝒥 r) with hJinv
  set Mi : Matrix (Fin m) (Fin m) ℝ :=
    LinearMap.toMatrix bE bE ((Jinv : E →L[ℝ] E) : E →ₗ[ℝ] E) with hMi
  -- taking matrices turns composition into matrix multiplication
  have hmul : ∀ f g : E →L[ℝ] E,
      LinearMap.toMatrix bE bE ((f * g : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = LinearMap.toMatrix bE bE (f : E →ₗ[ℝ] E)
          * LinearMap.toMatrix bE bE (g : E →ₗ[ℝ] E) := by
    intro f g
    exact LinearMap.toMatrix_comp bE bE bE _ _
  have hone : LinearMap.toMatrix bE bE ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 :=
    LinearMap.toMatrix_id _
  -- the matrix curve is differentiable, with derivative `Md`
  have htIcc : Icc (0 : ℝ) b ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
  have hy : HasDerivAt 𝒥 (𝒥' r) r :=
    (h.sol.hasDerivWithinAt_fst r ⟨hr.1.le, hr.2.le⟩).hasDerivAt htIcc
  have hMfd : HasDerivAt (fun s => ((Mf s : Matrix (Fin m) (Fin m) ℝ) :
      Fin m → Fin m → ℝ)) ((Md : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ) r :=
    (toMat bE).hasFDerivAt.comp_hasDerivAt r hy
  -- invertibility, in matrix form
  have hcancel : 𝒥 r * Jinv = 1 := Ring.mul_inverse_cancel _ hu
  have hcancel' : Jinv * 𝒥 r = 1 := Ring.inverse_mul_cancel _ hu
  have hprod : Mf r * Mi = 1 := by rw [hMf, hMi, ← hmul, hcancel, hone]
  have hprod' : Mi * Mf r = 1 := by rw [hMf, hMi, ← hmul, hcancel', hone]
  have hdet : IsUnit (Mf r).det := by
    refine isUnit_iff_exists_inv.mpr ⟨Mi.det, ?_⟩
    rw [← Matrix.det_mul, hprod, Matrix.det_one]
  have hinvM : (Mf r)⁻¹ = Mi := Matrix.inv_eq_left_inv hprod'
  -- chain rule with the determinant, then Jacobi's formula
  have hchain : HasDerivAt (fun s => Matrix.det (Mf s))
      (detCMM.linearDeriv (Mf r) Md) r :=
    (hasFDerivAt_det (Mf r)).comp_hasDerivAt r hMfd
  rw [detCMM_linearDeriv_eq_smul_trace (Mf r) Md hdet, hinvM] at hchain
  -- identify determinant and trace with their basis-free counterparts
  have hdetEq : ∀ s : ℝ, Matrix.det (Mf s) = volumeElement 𝒥 s := by
    intro s
    rw [hMf, volumeElement, LinearMap.det_toMatrix]
  have htraceEq : (Mi * Md).trace = LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r) := by
    -- `Tr(𝒥⁻¹ 𝒥') = Tr(𝒥' 𝒥⁻¹) = Tr A` by cyclicity of the trace
    have h1 : ((Jinv * 𝒥' r : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = (Jinv : E →ₗ[ℝ] E) * ((𝒥' r : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
    have h2 : ((𝒥' r * Jinv : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = ((𝒥' r : E →L[ℝ] E) : E →ₗ[ℝ] E) * (Jinv : E →ₗ[ℝ] E) := rfl
    have hshape : shapeOp 𝒥 𝒥' r = 𝒥' r * Jinv := rfl
    rw [hMi, hMd, ← hmul, ← LinearMap.trace_eq_matrix_trace ℝ bE, hshape, h1, h2,
      LinearMap.trace_mul_comm]
  -- assemble
  have hfun : (fun s => Matrix.det (Mf s)) = volumeElement 𝒥 := funext hdetEq
  rw [hfun, hdetEq r, htraceEq, smul_eq_mul] at hchain
  exact hchain

end MorganTianLib

end
