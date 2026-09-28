import MorganTianLib.Ch04.HamiltonMaximumCore
import MorganTianLib.Ch02.LaplacianExtremum
import MorganTianLib.Ch03.RicciFlow.ShiMetricBridge

/-!
# Morgan--Tian Ch. 4 - scalar contact and the tensor barrier

The finite-dimensional barrier in `HamiltonMaximumCore` asks for a scalar
maximum inequality for the diffusion operator.  On a Riemannian manifold that
inequality is a direct consequence of the scalar Laplacian maximum lemma once
the support-normal contact identity has been produced.  This file records that
analytic implication explicitly.

The contact identity and the smoothness of the scalarization are hypotheses,
not certificates: constructing them for a Levi--Civita tensor bundle is the
remaining geometric producer for the source theorem.
-/

open Set Filter Function
open Riemannian
open scoped InnerProductSpace Topology ContDiff Manifold Bundle NNReal

noncomputable section

namespace MorganTianLib

section ScalarContact

variable {D V H M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [FiniteDimensional ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ D H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M]

/-- **Math.** The scalar contact identity for a vector-valued diffusion operator.  It is
the invariant statement that pairing the operator with a fixed normal agrees
with the Riemannian scalar Laplacian of the paired field. -/
def ScalarLaplacianContact
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (L : ℝ → (M → V) → M → V) : Prop :=
  ∀ (t : ℝ) (f : M → V) (n : V) (x : M),
    ⟪n, L t f x⟫_ℝ =
      laplacianAt g nabla (fun y : M => ⟪n, f y⟫_ℝ) x

omit [CompleteSpace D] [FiniteDimensional ℝ D] [FiniteDimensional ℝ V]
    [IsManifold I ∞ M] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] in
/-- **Math.** A smooth vector-valued field has smooth scalarizations by a fixed
inner-product normal. -/
theorem contMDiff_inner_const_left
    {f : M → V} (n : V) (hf : ContMDiff I 𝓘(ℝ, V) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => ⟪n, f y⟫_ℝ) := by
  let φ : V →L[ℝ] ℝ := innerSL ℝ n
  have hφ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) ∞ φ := φ.contMDiff
  have hcomp := hφ.comp hf
  change ContMDiff I 𝓘(ℝ, ℝ) ∞ ((fun w : V => ⟪n, w⟫_ℝ) ∘ f)
  exact hcomp

omit [CompleteSpace D] [FiniteDimensional ℝ V] [CompactSpace M] [Nonempty M] in
/-- **Math.** At a spatial maximum, a diffusion operator satisfying the scalar contact
identity has nonpositive pairing with the active normal. -/
theorem scalarLaplacian_nonpositive_at_max
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (L : ℝ → (M → V) → M → V)
    (hcontact : ScalarLaplacianContact g nabla L)
    (hsmooth : ∀ (_t : ℝ) (f : M → V),
      ContMDiff I 𝓘(ℝ, V) ∞ f)
    {t : ℝ} {f : M → V} {n : V} {x : M}
    (hmax : IsMaxOn (fun y : M => ⟪n, f y⟫_ℝ) (univ : Set M) x) :
    ⟪n, L t f x⟫_ℝ ≤ 0 := by
  have hlocal : IsLocalMax (fun y : M => ⟪n, f y⟫_ℝ) x :=
    isLocalMaxOn_univ_iff.mp hmax.localize
  have hlap := laplacianAt_nonpos_of_isLocalMax g nabla
    (contMDiff_inner_const_left n (hsmooth t f)) hlocal
  rw [hcontact t f n x]
  exact hlap.2

omit [CompleteSpace D] [FiniteDimensional ℝ V] [CompactSpace M] [Nonempty M] in
/-- **Math.** Local form of the preceding contact implication.  The open-set hypotheses
are retained so this lemma can feed the localized tensor barrier when its
geometric boundary producer is available. -/
theorem scalarLaplacian_nonpositive_at_local_max
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (L : ℝ → (M → V) → M → V)
    (hcontact : ScalarLaplacianContact g nabla L)
    {U : Set M} (hU : IsOpen U)
    {t : ℝ} {f : M → V} {n : V} {x : M} (hx : x ∈ U)
    (hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => ⟪n, f y⟫_ℝ) U)
    (hmax : IsLocalMaxOn (fun y : M => ⟪n, f y⟫_ℝ) U x) :
    ⟪n, L t f x⟫_ℝ ≤ 0 := by
  have hlap := laplacianAt_nonpos_of_isLocalMaxOn g nabla hU hsmooth hx hmax
  rw [hcontact t f n x]
  exact hlap.2

/-!
The next theorem is the checked bridge from the geometric contact producer to
the finite-dimensional Hamilton barrier.  All regularity and PDE assumptions
remain those of the core theorem; only its abstract `hL` premise is discharged
by `scalarLaplacian_nonpositive_at_max`.
-/
omit [CompleteSpace D] in
theorem hamilton_tensor_maximum_principle_compact_scalar_contact
    {Z : Set V} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) (hZcompact : IsCompact Z)
    {ψ : V → V} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    (hψ : LipschitzWith K ψ)
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (L : ℝ → (M → V) → M → V)
    (hcontact : ScalarLaplacianContact g nabla L)
    (hsmooth : ∀ (_t : ℝ) (f : M → V),
      ContMDiff I 𝓘(ℝ, V) ∞ f)
    (u : M → ℝ → V) {a b : ℝ}
    (hF : Continuous ↿(hamiltonSupportValueFamily Z u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamily Z u L ψ))
    (hpde : ∀ x : M, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : M => u y s) x + ψ (u x s)) s)
    (hinit : ∀ x : M, u x a ∈ Z) :
    ∀ x : M, ∀ t ∈ Icc a b, u x t ∈ Z := by
  exact hamilton_tensor_maximum_principle_compact
    (X := M) (Z := Z) (ψ := ψ) (K := K)
    hZne hZclosed hZconv hZcompact hpres hψ L
    (by
      intro t f n x hmax
      exact scalarLaplacian_nonpositive_at_max g nabla L hcontact hsmooth hmax)
    u hF hF' hpde hinit

end ScalarContact

section ScalarMinimum

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! The minimum-sign companion is the scalar input needed when a curvature
evolution inequality is evaluated at a spatial minimum.  It is obtained by
negating the function, so it does not assume any Ricci-flow-specific
minimum-attainment or time-regularity hypothesis. -/

omit [CompleteSpace E] in
/-- **Math.** At a local minimum of a smooth scalar field, the Riemannian
Laplacian is nonnegative. -/
theorem laplacianAt_nonneg_of_isLocalMin
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmin : IsLocalMin f q) :
    0 ≤ laplacianAt g nabla f q := by
  have hmax : IsLocalMax (fun x : M => -f x) q := hmin.neg
  have hneg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => -f x) := hf.neg
  have hle : laplacianAt g nabla (fun x : M => -f x) q ≤ 0 :=
    (laplacianAt_nonpos_of_isLocalMax g nabla hneg hmax).2
  have hlin := laplacianAt_const_mul (E := E) (I := I) (M := M)
    (f := f) g nabla (-1 : ℝ) hf q
  have hle'' : laplacianAt g nabla (fun x => (-1 : ℝ) * f x) q ≤ 0 := by
    simpa only [neg_one_mul] using hle
  rw [hlin] at hle''
  have hle' : -(laplacianAt g nabla f q) ≤ 0 := by
    simpa using hle''
  linarith

end ScalarMinimum

end MorganTianLib
