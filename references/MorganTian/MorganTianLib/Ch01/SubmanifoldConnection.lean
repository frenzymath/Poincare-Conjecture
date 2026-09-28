import DoCarmoLib.Riemannian.Manifold.EuclideanOpens

/-!
# Morgan--Tian Ch. 1: the Euclidean submanifold connection

This file states the Gauss formula and its geodesic consequence in the
identified-patch model used by `DCImmersedPatch`.  Local smooth tangent
extensions of a curve's velocity let the flat ambient derivative compute the
curve's genuine Euclidean second derivative.
-/

open Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open TopologicalSpace
open Filter

noncomputable section

namespace MorganTianLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]
  {s : Opens F}

omit [CompleteSpace F] in
/-- A curve is geodesic in an identified Euclidean submanifold patch when its
induced covariant acceleration vanishes for every local smooth tangent
extension of its velocity. -/
def IsEuclideanSubmanifoldGeodesic
    (D : DCImmersedPatch 𝓘(ℝ, F) ↥s (opensEuclideanMetric s))
    (γ : ℝ → ↥s) : Prop :=
  ∀ t (V : SmoothVectorField 𝓘(ℝ, F) ↥s), D.IsTangentField V →
    (fun τ ↦ deriv (fun r ↦ (γ r : F)) τ) =ᶠ[𝓝 t]
      (fun τ ↦ (V (γ τ) : F)) →
    D.inducedCov opensEuclideanConnection V V (γ t) = 0

private theorem euclideanCurve_secondDeriv_eq_cov
    (V : SmoothVectorField 𝓘(ℝ, F) ↥s) (γ : ℝ → ↥s) (t : ℝ)
    (hγ' : HasDerivAt (fun τ ↦ (γ τ : F))
      (deriv (fun τ ↦ (γ τ : F)) t) t)
    (hV : (fun τ ↦ deriv (fun r ↦ (γ r : F)) τ) =ᶠ[𝓝 t]
      (fun τ ↦ (V (γ τ) : F))) :
    deriv (deriv (fun τ ↦ (γ τ : F))) t =
      ((opensEuclideanConnection (F := F) (s := s)).cov V V (γ t) : F) := by
  have hVt : deriv (fun τ ↦ (γ τ : F)) t = (V (γ t) : F) :=
    hV.self_of_nhds
  have hγV : HasDerivAt (fun τ ↦ (γ τ : F)) (V (γ t) : F) t :=
    hγ'.congr_deriv hVt
  have hVdiff : HasFDerivAt (s.extendZero (⇑V : ↥s → F))
      (fderiv ℝ (s.extendZero (⇑V : ↥s → F)) (γ t : F)) (γ t : F) :=
    ((V.contDiffAt_extendZero (γ t)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt
      (fun τ ↦ s.extendZero (⇑V : ↥s → F) (γ τ : F))
      (fderiv ℝ (s.extendZero (⇑V : ↥s → F)) (γ t : F) (V (γ t) : F)) t :=
    hVdiff.comp_hasDerivAt t hγV
  have hcomp' : HasDerivAt (fun τ ↦ (V (γ τ) : F))
      (fderiv ℝ (s.extendZero (⇑V : ↥s → F)) (γ t : F) (V (γ t) : F)) t := by
    simpa only [s.extendZero_val] using hcomp
  rw [(hcomp'.congr_of_eventuallyEq hV).deriv,
    opensEuclideanConnection_cov_apply]

omit [CompleteSpace F] in
private theorem inducedCov_apply_eq_zero_iff_normal
    (D : DCImmersedPatch 𝓘(ℝ, F) ↥s (opensEuclideanMetric s))
    (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s) (p : ↥s) :
    D.inducedCov opensEuclideanConnection X Y p = 0 ↔
      (opensEuclideanConnection.cov X Y p ∈ D.normalSpace p) := by
  constructor
  · intro hproj
    rw [DCImmersedPatch.mem_normalSpace_iff]
    intro v hv
    have horth := D.inner_tangentProj_sub
      (opensEuclideanConnection.cov X Y) p v hv
    change D.tangentProj (opensEuclideanConnection.cov X Y) p = 0 at hproj
    rw [hproj, sub_zero] at horth
    exact horth
  · intro hnormal
    change D.tangentProj (opensEuclideanConnection.cov X Y) p = 0
    exact D.tangentProj_apply_of_mem_normalSpace hnormal

/-- **Math.** Let an embedded submanifold of Euclidean space be represented by
an identified immersed patch `D`, with its induced Euclidean metric and
orthogonal tangential projection.  For arbitrary tangent fields `X` and `Y`,
its Levi-Civita covariant derivative is the tangential projection of the flat
directional derivative of `Y` along `X`.
For a smooth curve whose velocity admits local smooth tangent extensions, the
curve is a geodesic exactly when its Euclidean second derivative is normal at
every point.

Blueprint: `lem:submanifold-connection`. -/
theorem euclideanSubmanifold_connection_and_geodesic
    (D : DCImmersedPatch 𝓘(ℝ, F) ↥s (opensEuclideanMetric s))
    (X Y : SmoothVectorField 𝓘(ℝ, F) ↥s)
    (γ : ℝ → ↥s)
    (hγ' : ∀ t, HasDerivAt (fun τ ↦ (γ τ : F))
      (deriv (fun τ ↦ (γ τ : F)) t) t)
    (hγext : ∀ t, ∃ V : SmoothVectorField 𝓘(ℝ, F) ↥s,
      D.IsTangentField V ∧
      (fun τ ↦ deriv (fun r ↦ (γ r : F)) τ) =ᶠ[𝓝 t]
        (fun τ ↦ (V (γ τ) : F))) :
    D.IsTangentField X → D.IsTangentField Y →
      (∀ p, D.inducedCov opensEuclideanConnection X Y p =
          D.tangentProj (opensEuclideanConnection.cov X Y) p ∧
        (opensEuclideanConnection.cov X Y p : F) =
          fderiv ℝ (s.extendZero (⇑Y : ↥s → F)) (p : F) (X p : F)) ∧
      (IsEuclideanSubmanifoldGeodesic D γ ↔
        ∀ t, deriv (deriv (fun τ ↦ (γ τ : F))) t ∈ D.normalSpace (γ t)) := by
  intro _ _
  constructor
  · intro p
    exact ⟨rfl, opensEuclideanConnection_cov_apply X Y p⟩
  · constructor
    · intro hgeo t
      obtain ⟨V, hVtang, hV⟩ := hγext t
      rw [euclideanCurve_secondDeriv_eq_cov V γ t (hγ' t) hV]
      exact (inducedCov_apply_eq_zero_iff_normal D V V (γ t)).mp
        (hgeo t V hVtang hV)
    · intro hnormal t V _ hV
      apply (inducedCov_apply_eq_zero_iff_normal D V V (γ t)).mpr
      rw [← euclideanCurve_secondDeriv_eq_cov V γ t (hγ' t) hV]
      exact hnormal t

end MorganTianLib

end
