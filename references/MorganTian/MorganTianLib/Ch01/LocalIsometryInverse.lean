import MorganTianLib.Ch01.LocalIsometryFacades

/-!
# Local inverses of local isometries

A local diffeomorphism is represented in mathlib by a `PartialDiffeomorph`: its
forward and inverse functions are genuine inverses only on the open `source`
and `target`.  Consequently, the metric-preservation assertion for a local
inverse must also be localized to its target; the arbitrarily extended total
function need not preserve the metric away from that set.

`IsLocalIsometryOn` is the set-localized form of the chapter's
`IsLocalIsometry`.  The main theorem exhibits, through each point, a partial
diffeomorphism agreeing with the original map whose forward branch and inverse
branch are local isometries on their respective open domains.  This is the
precise formal content of blueprint remark
`rem:local-isometry-local-inverse`.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib.LocalIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M : Type*} [MetricSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]

/-- **Math.** A map is a local isometry on `s` when it is a local diffeomorphism at each
point of `s` and its differential preserves the Riemannian metric there. -/
def IsLocalIsometryOn (gN : Riemannian.RiemannianMetric I N)
    (gM : Riemannian.RiemannianMetric I' M) (F : N → M) (s : Set N) : Prop :=
  IsLocalDiffeomorphOn I I' ∞ F s ∧
    ∀ p ∈ s, ∀ u v : TangentSpace I p,
      gN.metricInner p u v =
        gM.metricInner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v)

variable {gN : Riemannian.RiemannianMetric I N}
  {gM : Riemannian.RiemannianMetric I' M} {F : N → M}

/-- **Math.** A local isometry is a local isometry on every subset of its domain. -/
theorem IsLocalIsometry.isLocalIsometryOn
    (hF : IsLocalIsometry gN gM F) (s : Set N) :
    IsLocalIsometryOn gN gM F s :=
  ⟨hF.1.isLocalDiffeomorphOn s, fun p _ ↦ hF.2 p⟩

/-- **Math.** **Local inverses of local isometries.** Through every `x` there is a
`PartialDiffeomorph` `Φ` agreeing with the local isometry on its open source.
Both `Φ` and `Φ.symm` preserve the metric and are local diffeomorphisms on
their open source and target, respectively.

The inverse metric identity follows by applying metric preservation of `F` to
`d(Φ⁻¹)u` and `d(Φ⁻¹)v`, then differentiating
`F ∘ Φ⁻¹ = id` on the target. -/
theorem IsLocalIsometry.exists_isometry_restriction
    (hF : IsLocalIsometry gN gM F) (x : N) :
    ∃ Φ : PartialDiffeomorph I I' N M ∞,
      x ∈ Φ.source ∧
      EqOn F Φ Φ.source ∧
      IsLocalIsometryOn gN gM (Φ : N → M) Φ.source ∧
      IsLocalIsometryOn gM gN (Φ.symm : M → N) Φ.target := by
  obtain ⟨Φ, hx, hEq⟩ := hF.1 x
  refine ⟨Φ, hx, hEq, ?_, ?_⟩
  · constructor
    · intro z
      exact Φ.isLocalDiffeomorphAt I I' ∞ z.property
    · intro z hz u v
      have hnear : F =ᶠ[𝓝 z] (Φ : N → M) := by
        filter_upwards [Φ.open_source.mem_nhds hz] with z' hz'
        exact hEq hz'
      have hpres := hF.2 z u v
      rw [hnear.mfderiv_eq] at hpres
      rw [hEq hz] at hpres
      exact hpres
  · constructor
    · intro y
      exact Φ.symm.isLocalDiffeomorphAt I' I ∞ y.property
    · intro y hy u v
      have hz : Φ.symm y ∈ Φ.source := Φ.map_target hy
      have hFz : F (Φ.symm y) = y := by
        calc
          F (Φ.symm y) = Φ (Φ.symm y) := hEq hz
          _ = y := Φ.right_inv hy
      have hInvDiff : MDifferentiableAt I' I (Φ.symm : M → N) y :=
        Φ.symm.mdifferentiableAt (by simp) hy
      have hFDiff : MDifferentiableAt I I' F (Φ.symm y) :=
        (hF.1 (Φ.symm y)).mdifferentiableAt (by simp)
      have hcompEq : F ∘ (Φ.symm : M → N) =ᶠ[𝓝 y] id := by
        filter_upwards [Φ.open_target.mem_nhds hy] with y' hy'
        have hz' : Φ.symm y' ∈ Φ.source := Φ.map_target hy'
        calc
          F (Φ.symm y') = Φ (Φ.symm y') := hEq hz'
          _ = y' := Φ.right_inv hy'
          _ = id y' := rfl
      have hchain (w : TangentSpace I' y) :
          mfderiv I I' F (Φ.symm y)
              (mfderiv I' I (Φ.symm : M → N) y w) = w := by
        have hcomp := mfderiv_comp_apply y hFDiff hInvDiff w
        rw [hcompEq.mfderiv_eq, mfderiv_id] at hcomp
        exact hcomp.symm
      have hpres := hF.2 (Φ.symm y)
        (mfderiv I' I (Φ.symm : M → N) y u)
        (mfderiv I' I (Φ.symm : M → N) y v)
      rw [hchain u, hchain v] at hpres
      rw [hFz] at hpres
      exact hpres.symm

/-- **Math.** The diffeomorphism underlying a bijective local isometry. -/
def IsIsometry.toDiffeomorph (hF : IsIsometry gN gM F) :
    Diffeomorph I I' N M ∞ :=
  hF.2.1.diffeomorphOfBijective hF.1

/-- **Math.** The inverse of an isometry is again an isometry. -/
theorem IsIsometry.symm (hF : IsIsometry gN gM F) :
    IsIsometry gM gN (hF.toDiffeomorph.symm : M → N) := by
  let Φ : Diffeomorph I I' N M ∞ := hF.toDiffeomorph
  have hpres : Riemannian.DCPreservesMetric gN gM (Φ : N → M) := by
    have hΦ : (Φ : N → M) = F := by
      rfl
    rw [hΦ]
    exact hF.2.2
  refine ⟨Φ.symm.bijective, Φ.symm.isLocalDiffeomorph, ?_⟩
  intro y u v
  have hcompEq : (Φ : N → M) ∘ (Φ.symm : M → N) = id :=
    funext Φ.apply_symm_apply
  have hchain (w : TangentSpace I' y) :
      mfderiv I I' (Φ : N → M) (Φ.symm y)
          (mfderiv I' I (Φ.symm : M → N) y w) = w := by
    have hcomp := mfderiv_comp_apply y
      (Φ.mdifferentiable (by simp) (Φ.symm y))
      (Φ.symm.mdifferentiable (by simp) y) w
    rw [hcompEq, mfderiv_id] at hcomp
    exact hcomp.symm
  have hp := hpres (Φ.symm y)
    (mfderiv I' I (Φ.symm : M → N) y u)
    (mfderiv I' I (Φ.symm : M → N) y v)
  rw [hchain u, hchain v] at hp
  rw [Φ.apply_symm_apply] at hp
  exact hp.symm

end MorganTianLib.LocalIsometry
