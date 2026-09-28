import HanLinLectureNotes.Ch01.Harmonic
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Han--Lin Chapter 1: maximum principles
-/

open Filter InnerProductSpace Laplacian Metric Set Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch01

lemma deriv_deriv_nonpos_of_isLocalMax {g : Real -> Real} {a : Real}
    (h : IsLocalMax g a) (hg : ContinuousAt g a) :
    deriv (deriv g) a <= 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hmin : IsLocalMin g a :=
    isLocalMin_of_deriv_deriv_pos hpos h.deriv_eq_zero hg
  have hconst : g =ᶠ[𝓝 a] fun _ => g a := by
    filter_upwards [h, hmin] with s h1 h2
    exact le_antisymm h1 h2
  have h2 : deriv (deriv g) a = deriv (deriv fun _ => g a) a :=
    hconst.deriv.deriv_eq
  rw [h2] at hpos
  simp [deriv_const'] at hpos

lemma secondDirectional_nonpos_of_isLocalMax
    {n : Nat} {u : EuclideanSpace Real (Fin n) -> Real}
    {p : EuclideanSpace Real (Fin n)} (hu : ContDiffAt Real 2 u p)
    (hmax : IsLocalMax u p) (v : EuclideanSpace Real (Fin n)) :
    fderiv Real (fderiv Real u) p v v <= 0 := by
  let g : Real -> Real := fun s => u (p + s • v)
  have hA : Continuous fun s : Real => p + s • v := by fun_prop
  have hA0 : p + (0 : Real) • v = p := by simp
  have hAcont : ContinuousAt (fun s : Real => p + s • v) 0 := hA.continuousAt
  have hline_tendsto : Tendsto (fun s : Real => p + s • v) (𝓝 0) (𝓝 p) := by
    have hAt := hAcont
    change Tendsto (fun s : Real => p + s • v) (𝓝 0)
      (𝓝 (p + (0 : Real) • v)) at hAt
    rw [hA0] at hAt
    exact hAt
  have hev : ∀ᶠ s in 𝓝 (0 : Real), ContDiffAt Real 2 u (p + s • v) :=
    hline_tendsto.eventually (hu.eventually (by simp))
  have hderiv_g : deriv g =ᶠ[𝓝 (0 : Real)]
      fun s => fderiv Real u (p + s • v) v := by
    filter_upwards [hev] with s hs
    have hline : HasDerivAt (fun t : Real => p + t • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    exact (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hline |>.deriv
  have hF : HasDerivAt (fun s : Real => fderiv Real u (p + s • v) v)
      (fderiv Real (fderiv Real u) p v v) 0 := by
    have hline : HasDerivAt (fun s : Real => p + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : Real)).smul_const v).const_add p
    have hFd : DifferentiableAt Real (fderiv Real u) p :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hFd' : HasFDerivAt (fderiv Real u) (fderiv Real (fderiv Real u) p)
        (p + (0 : Real) • v) := by
      rw [hA0]
      exact hFd.hasFDerivAt
    have hcomp : HasDerivAt (fun s : Real => fderiv Real u (p + s • v))
        (fderiv Real (fderiv Real u) p v) 0 := hFd'.comp_hasDerivAt 0 hline
    simpa using hcomp.clm_apply (hasDerivAt_const (0 : Real) v)
  have hgg : deriv (deriv g) 0 = fderiv Real (fderiv Real u) p v v := by
    rw [hderiv_g.deriv_eq]
    exact hF.deriv
  have hgmax : IsLocalMax g 0 := by
    have hm := hline_tendsto.eventually hmax
    filter_upwards [hm] with s hs
    simpa [g] using hs
  have hgcont : ContinuousAt g 0 := by
    have hup : ContinuousAt u p := hu.continuousAt
    have hc := hup.comp_of_eq hAcont hA0
    simpa [g, Function.comp_def] using hc
  have hnonpos := deriv_deriv_nonpos_of_isLocalMax hgmax hgcont
  rwa [hgg] at hnonpos

lemma laplacian_nonpos_of_isLocalMax
    {n : Nat} {u : EuclideanSpace Real (Fin n) -> Real}
    {p : EuclideanSpace Real (Fin n)} (hu : ContDiffAt Real 2 u p)
    (hmax : IsLocalMax u p) : Δ u p <= 0 := by
  let b := EuclideanSpace.basisFun (Fin n) Real
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  apply Finset.sum_nonpos
  intro i _
  rw [iteratedFDeriv_two_apply]
  exact secondDirectional_nonpos_of_isLocalMax hu hmax (b i)

lemma laplacian_norm_sq {n : Nat} (x : EuclideanSpace Real (Fin n)) :
    Δ (fun y : EuclideanSpace Real (Fin n) => ‖y‖ ^ 2) x = 2 * n := by
  let b := EuclideanSpace.basisFun (Fin n) Real
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y : EuclideanSpace Real (Fin n) => ‖y‖ ^ 2) b]
  have houter :
      fderiv Real (fderiv Real (fun y : EuclideanSpace Real (Fin n) => ‖y‖ ^ 2)) x =
        (2 : Nat) • innerSL Real := by
    rw [fderiv_norm_sq]
    have hev :
        ((2 : Nat) • (⇑(innerSL Real) : EuclideanSpace Real (Fin n) ->
          EuclideanSpace Real (Fin n) →L[Real] Real)) =ᶠ[𝓝 x]
        ⇑((2 : Nat) • innerSL Real) := by
      filter_upwards [] with y
      rfl
    calc
      fderiv Real ((2 : Nat) • ⇑(innerSL Real)) x =
          fderiv Real (⇑((2 : Nat) • innerSL Real)) x :=
        Filter.EventuallyEq.fderiv_eq (𝕜 := Real) hev
      _ = (2 : Nat) • innerSL Real :=
        ((2 : Nat) • innerSL Real).hasFDerivAt.fderiv
  simp_rw [iteratedFDeriv_two_apply, houter]
  simp only [Fin.isValue, Matrix.cons_val_zero, smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, nsmul_eq_mul, Nat.cast_ofNat]
  change (∑ i : Fin n, (2 : Real) * inner Real (b i) (b i)) = 2 * n
  have hone (i : Fin n) : inner Real (b i) (b i) = 1 := by
    have hi := orthonormal_iff_ite.mp b.orthonormal i i
    rw [if_pos rfl] at hi
    exact hi
  simp_rw [hone]
  simp
  ring

private lemma exists_boundary_ge_subharmonic {n : Nat} [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    (hC2 : ContDiffOn Real 2 u (ball 0 1))
    (hcont : ContinuousOn u (closedBall 0 1))
    (hlap : forall x, x ∈ ball 0 1 -> 0 <= Δ u x) :
    forall x, x ∈ ball 0 1 -> exists y, y ∈ sphere 0 1 ∧ u x <= u y := by
  intro x hx
  by_contra hcontra
  push Not at hcontra
  have hsphere_ne : (sphere (0 : EuclideanSpace Real (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨z, hz, hzmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace Real (Fin n)) 1).exists_isMaxOn hsphere_ne
    (hcont.mono sphere_subset_closedBall)
  rw [isMaxOn_iff] at hzmax
  let eps : Real := (u x - u z) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith [hcontra z hz]
  let vfun : EuclideanSpace Real (Fin n) -> Real :=
    u + eps • fun y => ‖y‖ ^ 2
  have hvcont : ContinuousOn vfun (closedBall 0 1) := by
    exact hcont.add
      ((contDiff_norm_sq Real (n := 1)).continuous.const_smul eps).continuousOn
  have hvboundary : forall y, y ∈ closedBall 0 1 \ ball 0 1 -> vfun y < vfun x := by
    intro y hy
    have hysphere : y ∈ sphere (0 : EuclideanSpace Real (Fin n)) 1 := by
      rw [← closedBall_sdiff_ball]
      exact hy
    have hynorm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hysphere
    calc
      vfun y = u y + eps := by simp [vfun, hynorm]
      _ <= u z + eps := add_le_add_left (hzmax y hysphere) eps
      _ < u x := by dsimp [eps]; linarith [hcontra z hz]
      _ <= vfun x := by
        change u x <= u x + eps * ‖x‖ ^ 2
        exact le_add_of_nonneg_right (mul_nonneg heps.le (sq_nonneg ‖x‖))
  obtain ⟨p, hp, hpmax⟩ := (isCompact_closedBall
    (0 : EuclideanSpace Real (Fin n)) 1).exists_isLocalMax_mem_open
    ball_subset_closedBall hvcont (ball_subset_closedBall hx) hvboundary isOpen_ball
  have hup : ContDiffAt Real 2 u p :=
    (hC2 p hp).contDiffAt (isOpen_ball.mem_nhds hp)
  have hsq : ContDiffAt Real 2
      (fun y : EuclideanSpace Real (Fin n) => ‖y‖ ^ 2) p :=
    (contDiff_norm_sq Real (n := 2)).contDiffAt
  have hvp : ContDiffAt Real 2 vfun p := by
    exact hup.add (hsq.const_smul eps)
  have hnonpos : Δ vfun p <= 0 := laplacian_nonpos_of_isLocalMax hvp hpmax
  have hlapv : Δ vfun p = Δ u p + eps * (2 * n) := by
    have hsmul :
        (eps • (fun y : EuclideanSpace Real (Fin n) => ‖y‖ ^ 2)) =
        (fun y : EuclideanSpace Real (Fin n) => eps • ‖y‖ ^ 2) := rfl
    rw [show vfun = u + eps • (fun y : EuclideanSpace Real (Fin n) => ‖y‖ ^ 2) by
      rfl, hsmul, hup.laplacian_add (hsq.const_smul eps), ← hsmul,
      laplacian_smul eps hsq, laplacian_norm_sq]
    simp [smul_eq_mul]
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hstrict : 0 < eps * (2 * (n : Real)) := mul_pos heps (by positivity)
  have hnonneg := hlap p hp
  rw [hlapv] at hnonpos
  linarith

/-- Han--Lin Theorem 1.29. A subharmonic function on the unit ball is bounded
above by one of its boundary values. -/
theorem subharmonic_maximum_principle {n : Nat} [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    (hC2 : ContDiffOn Real 2 u (ball 0 1))
    (hcont : ContinuousOn u (closedBall 0 1))
    (hlap : forall x, x ∈ ball 0 1 -> 0 <= Δ u x) :
    exists z, z ∈ sphere 0 1 ∧ forall x, x ∈ ball 0 1 -> u x <= u z := by
  have hsphere_ne : (sphere (0 : EuclideanSpace Real (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨z, hz, hzmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace Real (Fin n)) 1).exists_isMaxOn hsphere_ne
    (hcont.mono sphere_subset_closedBall)
  rw [isMaxOn_iff] at hzmax
  refine ⟨z, hz, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_boundary_ge_subharmonic hC2 hcont hlap x hx
  exact hxy.trans (hzmax y hy)

/-- Han--Lin Corollary 1.30. Ordering the Laplacians and boundary values orders
the functions throughout the unit ball. -/
theorem comparison_principle {n : Nat} [Nonempty (Fin n)]
    {u v : EuclideanSpace Real (Fin n) -> Real}
    (huC2 : ContDiffOn Real 2 u (ball 0 1))
    (hvC2 : ContDiffOn Real 2 v (ball 0 1))
    (hucont : ContinuousOn u (closedBall 0 1))
    (hvcont : ContinuousOn v (closedBall 0 1))
    (hlap : forall x, x ∈ ball 0 1 -> Δ v x <= Δ u x)
    (hboundary : forall x, x ∈ sphere 0 1 -> u x <= v x) :
    forall x, x ∈ ball 0 1 -> u x <= v x := by
  let w : EuclideanSpace Real (Fin n) -> Real := u - v
  have hwC2 : ContDiffOn Real 2 w (ball 0 1) := huC2.sub hvC2
  have hwcont : ContinuousOn w (closedBall 0 1) := hucont.sub hvcont
  have hwlap : forall x, x ∈ ball 0 1 -> 0 <= Δ w x := by
    intro x hx
    have hux : ContDiffAt Real 2 u x :=
      (huC2 x hx).contDiffAt (isOpen_ball.mem_nhds hx)
    have hvx : ContDiffAt Real 2 v x :=
      (hvC2 x hx).contDiffAt (isOpen_ball.mem_nhds hx)
    rw [show w = u - v by rfl, hux.laplacian_sub hvx]
    linarith [hlap x hx]
  obtain ⟨z, hz, hmax⟩ := subharmonic_maximum_principle hwC2 hwcont hwlap
  intro x hx
  have hxz := hmax x hx
  have hz0 := hboundary z hz
  dsimp [w] at hxz
  linarith

end HanLinLectureNotes.Ch01
