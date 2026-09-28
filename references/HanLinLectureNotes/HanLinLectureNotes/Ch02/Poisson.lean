import HanLinLectureNotes.Ch02.MaximumPrinciple
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Han--Lin Chapter 2: Poisson barriers

This module develops the quadratic half-ball barrier, the compact comparison
argument, and the orthogonal rotation step proving Lemma 2.17.
-/

open Filter InnerProductSpace Metric Set Topology
open Laplacian
open scoped ContDiff RealInnerProductSpace InnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The Euclidean Laplacian is invariant under a linear isometry of a ball. -/
lemma laplacian_comp_linearIsometryEquiv_on_ball {n : Nat} {R : Real}
    {u : Euclidean n -> Real} (Q : Euclidean n ≃ₗᵢ[Real] Euclidean n)
    (hu : ContDiffOn Real 2 u (ball (0 : Euclidean n) R))
    {x : Euclidean n} (hx : x ∈ ball (0 : Euclidean n) R) :
    Δ (u ∘ Q) x = Δ u (Q x) := by
  let s : Set (Euclidean n) := ball (0 : Euclidean n) R
  let q : Euclidean n →L[Real] Euclidean n :=
    Q.toContinuousLinearEquiv.toContinuousLinearMap
  have hq_apply (y : Euclidean n) : q y = Q y := rfl
  have hsopen : IsOpen s := isOpen_ball
  have hsuniq : UniqueDiffOn Real s := hsopen.uniqueDiffOn
  have hpre : ⇑q ⁻¹' s = s := by
    ext y
    simp only [Set.mem_preimage, s, mem_ball, dist_zero_right, hq_apply, Q.norm_map]
  have hpreuniq : UniqueDiffOn Real (⇑q ⁻¹' s) := by
    rw [hpre]
    exact hsuniq
  have hQx : q x ∈ s := by
    simpa only [s, mem_ball, dist_zero_right, hq_apply, Q.norm_map] using hx
  have huQ : ContDiffOn Real 2 (u ∘ q) s := by
    rw [← hpre]
    exact hu.comp_continuousLinearMap q
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right q
    (s := s) (n := (2 : ENat)) (f := u) hu hsuniq hpreuniq hQx
      (i := 2) (by norm_num)
  rw [hpre] at hcomp
  have hleft :
      Δ (u ∘ Q) x =
        ∑ i : Fin n,
          (iteratedFDeriv Real 2 (u ∘ q) x) ![
            (EuclideanSpace.basisFun (Fin n) Real i),
            (EuclideanSpace.basisFun (Fin n) Real i)] := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (u ∘ Q) (EuclideanSpace.basisFun (Fin n) Real)]
    rfl
  have hright :
      Δ u (Q x) =
        ∑ i : Fin n,
          (iteratedFDeriv Real 2 u (q x)) ![
            ((EuclideanSpace.basisFun (Fin n) Real).map Q i),
            ((EuclideanSpace.basisFun (Fin n) Real).map Q i)] := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      u ((EuclideanSpace.basisFun (Fin n) Real).map Q)]
    rfl
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro i hi
  have huQx : ContDiffAt Real 2 (u ∘ q) x :=
    (huQ x hx).contDiffAt (hsopen.mem_nhds hx)
  have hux : ContDiffAt Real 2 u (q x) :=
    (hu (q x) hQx).contDiffAt (hsopen.mem_nhds hQx)
  have hli := iteratedFDerivWithin_eq_iteratedFDeriv hsuniq huQx hx
  have hri := iteratedFDerivWithin_eq_iteratedFDeriv hsuniq hux hQx
  rw [← hli, ← hri]
  have hc := DFunLike.congr_fun hcomp
    ![(EuclideanSpace.basisFun (Fin n) Real i),
      (EuclideanSpace.basisFun (Fin n) Real i)]
  have hv :
      ![Q (EuclideanSpace.basisFun (Fin n) Real i),
        Q (EuclideanSpace.basisFun (Fin n) Real i)] =
        (fun j : Fin 2 => Q (![EuclideanSpace.basisFun (Fin n) Real i,
          EuclideanSpace.basisFun (Fin n) Real i] j)) := by
    funext j
    fin_cases j <;> rfl
  simp only [OrthonormalBasis.map_apply]
  rw [hv]
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    hq_apply] using hc

/-- Reflection in the hyperplane perpendicular to the `i`-th coordinate
reverses that coordinate. -/
lemma coordinate_hyperplaneReflection_apply {n : Nat} (i : Fin n)
    (x : Euclidean n) :
    (((Real ∙ (EuclideanSpace.basisFun (Fin n) Real i))ᗮ.reflection x i : Real)) =
      -(x i) := by
  let e : Euclidean n := EuclideanSpace.basisFun (Fin n) Real i
  let K : Submodule Real (Euclidean n) := (Real ∙ e)ᗮ
  let rho : Euclidean n ≃ₗᵢ[Real] Euclidean n := K.reflection
  have he : rho e = -e := by
    dsimp [rho, K, e]
    exact Submodule.reflection_orthogonalComplement_singleton_eq_neg _
  have hinner : inner Real (rho x) e = -inner Real x e := by
    rw [rho.inner_map_eq_flip, Submodule.reflection_symm]
    rw [show rho e = -e by exact he]
    simp
  rw [← EuclideanSpace.inner_basisFun_real (Fin n) x i]
  rw [← EuclideanSpace.inner_basisFun_real (Fin n) (rho x) i]
  exact hinner

/-- Reflection in the coordinate hyperplane perpendicular to `e_i`. -/
def coordinateHyperplaneReflection {n : Nat} (i : Fin n) :
    Euclidean n ≃ₗᵢ[Real] Euclidean n :=
  (Real ∙ (EuclideanSpace.basisFun (Fin n) Real i))ᗮ.reflection

lemma norm_coordinateHyperplaneReflection {n : Nat} (i : Fin n)
    (x : Euclidean n) :
    ‖coordinateHyperplaneReflection i x‖ = ‖x‖ :=
  (coordinateHyperplaneReflection i).norm_map x

lemma coordinateHyperplaneReflection_coordinate {n : Nat} (i : Fin n)
    (x : Euclidean n) :
    (coordinateHyperplaneReflection i x i : Real) = -(x i) := by
  exact coordinate_hyperplaneReflection_apply i x

lemma coordinateHyperplaneReflection_eq_self_of_coordinate_eq_zero
    {n : Nat} (i : Fin n) {x : Euclidean n} (hx : x i = 0) :
    coordinateHyperplaneReflection i x = x := by
  apply Submodule.reflection_mem_subspace_eq_self
  apply (Submodule.mem_orthogonal_singleton_iff_inner_left).2
  rw [EuclideanSpace.inner_basisFun_real]
  simp [hx]

private lemma laplacian_nonpos_of_isLocalMax_poisson
    {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    (hu : ContDiffAt Real 2 u p) (hmax : IsLocalMax u p) :
    Δ u p <= 0 := by
  let b := EuclideanSpace.basisFun (Fin n) Real
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  apply Finset.sum_nonpos
  intro i _
  rw [iteratedFDeriv_two_apply]
  exact secondDirectional_nonpos_of_isLocalMax hu hmax (b i)

/-- A compact-domain comparison principle for the Laplacian.  The auxiliary
function `phi` supplies the strict perturbation needed for a weak inequality. -/
lemma nonpositive_on_compact_of_laplacian_nonneg
    {n : Nat} [Nonempty (Fin n)] {Omega K : Set (Euclidean n)}
    {v phi : Euclidean n -> Real} {C : Real}
    (hOpen : IsOpen Omega) (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hsub : Omega ⊆ K) (hvcont : ContinuousOn v K)
    (hvC2 : ContDiffOn Real 2 v Omega)
    (hLapv : forall x, x ∈ Omega -> 0 <= Δ v x)
    (hboundary : forall x, x ∈ K -> x ∉ Omega -> v x <= 0)
    (hphiC2 : ContDiff Real 2 phi) (hphiCont : ContinuousOn phi K)
    (hLapphi : forall x, x ∈ Omega -> 0 < Δ phi x)
    (hphiBoundary : forall x, x ∈ K -> x ∉ Omega -> phi x <= 0)
    (hphiLower : forall x, x ∈ K -> -C <= phi x) (hC : 0 < C) :
    forall x, x ∈ K -> v x <= 0 := by
  intro x hx
  by_contra hxpos
  have hxpos' : 0 < v x := lt_of_not_ge hxpos
  have heps : 0 < v x / (2 * C) := by positivity
  let eps : Real := v x / (2 * C)
  let q : Euclidean n -> Real := v + eps • phi
  have hqcont : ContinuousOn q K :=
    hvcont.add (hphiCont.const_smul eps)
  have hqboundary : forall y, y ∈ K -> y ∉ Omega -> q y <= 0 := by
    intro y hyK hyO
    exact add_nonpos (hboundary y hyK hyO)
      (mul_nonpos_of_nonneg_of_nonpos heps.le (hphiBoundary y hyK hyO))
  have hqx : 0 < q x := by
    dsimp [q, eps]
    have hlow := hphiLower x hx
    have hmul := mul_le_mul_of_nonneg_left hlow heps.le
    have heq : v x / (2 * C) * (-C) = -(v x / 2) := by
      field_simp [ne_of_gt hC]
    rw [heq] at hmul
    nlinarith
  obtain ⟨p, hpK, hpmax⟩ := hKcompact.exists_isMaxOn hKne hqcont
  have hqp : 0 < q p := lt_of_lt_of_le hqx (hpmax hx)
  have hpO : p ∈ Omega := by
    by_contra hpO
    exact (not_lt_of_ge (hqboundary p hpK hpO)) hqp
  have hKnhds : K ∈ 𝓝 p :=
    mem_of_superset (hOpen.mem_nhds hpO) hsub
  have hlocal : IsLocalMax q p := hpmax.isLocalMax hKnhds
  have hvp : ContDiffAt Real 2 v p :=
    (hvC2 p hpO).contDiffAt (hOpen.mem_nhds hpO)
  have hqC2 : ContDiffAt Real 2 q p := by
    dsimp [q]
    exact hvp.add (hphiC2.contDiffAt.const_smul eps)
  have hnonpos : Δ q p <= 0 :=
    laplacian_nonpos_of_isLocalMax_poisson hqC2 hlocal
  have hpos : 0 < Δ q p := by
    change 0 < Δ (v + fun y => eps • phi y) p
    rw [hvp.laplacian_add (hphiC2.contDiffAt.const_smul eps)]
    have hsmul : (fun y => eps • phi y) = eps • phi := rfl
    rw [hsmul, InnerProductSpace.laplacian_smul eps hphiC2.contDiffAt]
    simp only [smul_eq_mul]
    have hv := hLapv p hpO
    have hphi := hLapphi p hpO
    nlinarith
  linarith

/-- The Euclidean squared norm has constant Laplacian `2 n`. -/
lemma laplacian_norm_sq_poisson {n : Nat} (x : Euclidean n) :
    Δ (fun y : Euclidean n => ‖y‖ ^ 2) x = 2 * n := by
  let b := EuclideanSpace.basisFun (Fin n) Real
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y : Euclidean n => ‖y‖ ^ 2) b]
  have houter :
      fderiv Real (fderiv Real (fun y : Euclidean n => ‖y‖ ^ 2)) x =
        (2 : Nat) • innerSL Real := by
    rw [fderiv_norm_sq]
    have hev :
        ((2 : Nat) • (⇑(innerSL Real) : Euclidean n ->
          Euclidean n →L[Real] Real)) =ᶠ[𝓝 x]
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

/-- The Laplacian of one Euclidean coordinate is zero. -/
lemma laplacian_coordinate_poisson {n : Nat} (i : Fin n) (x : Euclidean n) :
    Δ (fun y : Euclidean n => (y i : Real)) x = 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y : Euclidean n => (y i : Real))
      (EuclideanSpace.basisFun (Fin n) Real)]
  simp only [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  have hglobal : fderiv Real (fun y : Euclidean n => (y i : Real)) =
      fun _ => (EuclideanSpace.proj i : Euclidean n →L[Real] Real) := by
    funext y
    rw [show (fun z : Euclidean n => (z i : Real)) =
      (EuclideanSpace.proj i : Euclidean n →L[Real] Real) by rfl]
    exact (EuclideanSpace.proj i : Euclidean n →L[Real] Real).fderiv
  rw [hglobal]
  simp

/-- The square of one Euclidean coordinate has Laplacian `2`. -/
lemma laplacian_coordinate_sq_poisson {n : Nat} (i : Fin n) (x : Euclidean n) :
    Δ (fun y : Euclidean n => (y i : Real) ^ 2) x = 2 := by
  have hC : ContDiffAt Real 2
      (fun y : Euclidean n => (y i : Real) ^ 2) x := by fun_prop
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y : Euclidean n => (y i : Real) ^ 2)
      (EuclideanSpace.basisFun (Fin n) Real)]
  simp only [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  have hsecond (v w : Euclidean n) :
      fderiv Real
          (fun y => fderiv Real (fun z : Euclidean n => (z i : Real) ^ 2) y v)
          x w = 2 * (w i) * (v i) := by
    have hfirst (y : Euclidean n) :
        fderiv Real (fun z : Euclidean n => (z i : Real) ^ 2) y v =
          (2 * (y i)) * (v i) := by
      have hc : HasFDerivAt (fun z : Euclidean n => (z i : Real))
          (EuclideanSpace.proj i : Euclidean n →L[Real] Real) y := by
        rw [show (fun z : Euclidean n => (z i : Real)) =
          (EuclideanSpace.proj i : Euclidean n →L[Real] Real) by rfl]
        exact (EuclideanSpace.proj i : Euclidean n →L[Real] Real).hasFDerivAt
      have hs := hc.pow 2
      rw [hs.fderiv]
      norm_num
    rw [show (fun y => fderiv Real
        (fun z : Euclidean n => (z i : Real) ^ 2) y v) =
        (fun y => (2 * (y i)) * (v i)) by
          funext y
          rw [hfirst]]
    have hc : HasFDerivAt (fun y : Euclidean n => (y i : Real))
        (EuclideanSpace.proj i : Euclidean n →L[Real] Real) x := by
      rw [show (fun y : Euclidean n => (y i : Real)) =
        (EuclideanSpace.proj i : Euclidean n →L[Real] Real) by rfl]
      exact (EuclideanSpace.proj i : Euclidean n →L[Real] Real).hasFDerivAt
    have hd := (hc.const_mul (2 : Real)).mul_const (v i)
    rw [hd.fderiv]
    change (v i) * (2 * (w i)) = _
    ring
  calc
    (∑ j : Fin n, (fderiv Real (fderiv Real
      (fun y : Euclidean n => (y i : Real) ^ 2)) x
        (EuclideanSpace.single j 1)) (EuclideanSpace.single j 1)) =
      ∑ j : Fin n, 2 * ((EuclideanSpace.single j 1 : Euclidean n) i) *
        ((EuclideanSpace.single j 1 : Euclidean n) i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← fderiv_apply_eq_fderiv_fderiv hC]
          rw [hsecond]
    _ = 2 := by simp

/-- The quadratic barrier used on the upper half-ball in Lemma 2.17. -/
def poissonBarrier {n : Nat} (R M F : Real) (i : Fin n) : Euclidean n -> Real :=
  (M / R ^ 2) • (fun x : Euclidean n => ‖x‖ ^ 2) +
    (R * F / 2 + (n : Real) * M / R) •
      (fun x : Euclidean n => (x i : Real)) +
    (-F / 2 - (n : Real) * M / R ^ 2) •
      (fun x : Euclidean n => (x i : Real) ^ 2)

/-- The Poisson quadratic barrier is smooth. -/
lemma poissonBarrier_contDiff {n : Nat} (R M F : Real) (i : Fin n) :
    ContDiff Real 2 (poissonBarrier R M F i) := by
  have hnorm : ContDiff Real 2 (fun x : Euclidean n => ‖x‖ ^ 2) :=
    contDiff_norm_sq Real
  have hcoord : ContDiff Real 2
      (fun x : Euclidean n => (x i : Real)) := by fun_prop
  have hcoordsq : ContDiff Real 2
      (fun x : Euclidean n => (x i : Real) ^ 2) := by fun_prop
  unfold poissonBarrier
  exact ((hnorm.const_smul (M / R ^ 2)).add
      (hcoord.const_smul (R * F / 2 + (n : Real) * M / R))).add
    (hcoordsq.const_smul (-F / 2 - (n : Real) * M / R ^ 2))

/-- The barrier has Laplacian `-F`, independently of the point and radius. -/
lemma laplacian_poissonBarrier {n : Nat} (R M F : Real) (i : Fin n)
    (x : Euclidean n) :
    Δ (poissonBarrier R M F i) x = -F := by
  have hnorm : ContDiffAt Real 2 (fun y : Euclidean n => ‖y‖ ^ 2) x :=
    (contDiff_norm_sq Real (n := 2)).contDiffAt
  have hcoord : ContDiffAt Real 2
      (fun y : Euclidean n => (y i : Real)) x := by fun_prop
  have hcoordsq : ContDiffAt Real 2
      (fun y : Euclidean n => (y i : Real) ^ 2) x := by fun_prop
  have hA : ContDiffAt Real 2
      ((M / R ^ 2) • (fun y : Euclidean n => ‖y‖ ^ 2)) x :=
    hnorm.const_smul (M / R ^ 2)
  have hB : ContDiffAt Real 2
      ((R * F / 2 + (n : Real) * M / R) •
        (fun y : Euclidean n => (y i : Real))) x :=
    hcoord.const_smul (R * F / 2 + (n : Real) * M / R)
  have hAB : ContDiffAt Real 2
      ((M / R ^ 2) • (fun y : Euclidean n => ‖y‖ ^ 2) +
        (R * F / 2 + (n : Real) * M / R) •
          (fun y : Euclidean n => (y i : Real))) x := hA.add hB
  have hC : ContDiffAt Real 2
      ((-F / 2 - (n : Real) * M / R ^ 2) •
        (fun y : Euclidean n => (y i : Real) ^ 2)) x :=
    hcoordsq.const_smul (-F / 2 - (n : Real) * M / R ^ 2)
  change Δ ((M / R ^ 2) • (fun y : Euclidean n => ‖y‖ ^ 2) +
      (R * F / 2 + (n : Real) * M / R) •
        (fun y : Euclidean n => (y i : Real)) +
      (-F / 2 - (n : Real) * M / R ^ 2) •
        (fun y : Euclidean n => (y i : Real) ^ 2)) x = -F
  rw [hAB.laplacian_add hC]
  rw [hA.laplacian_add hB]
  rw [laplacian_smul (M / R ^ 2) hnorm,
    laplacian_smul (R * F / 2 + (n : Real) * M / R) hcoord,
    laplacian_smul (-F / 2 - (n : Real) * M / R ^ 2) hcoordsq]
  rw [laplacian_norm_sq_poisson, laplacian_coordinate_poisson,
    laplacian_coordinate_sq_poisson]
  norm_num
  ring

/-- On the sphere, the barrier reduces to the one-variable quadratic used in
the upper-half-ball boundary estimate. -/
lemma poissonBarrier_on_sphere {n : Nat} (R M F : Real) (i : Fin n)
    (hR : R ≠ 0) {x : Euclidean n} (hx : x ∈ sphere 0 R) :
    poissonBarrier R M F i x =
      M + (x i) * (R - x i) *
        (F / 2 + (n : Real) * M / R ^ 2) := by
  have hnorm : ‖x‖ = R := mem_sphere_zero_iff_norm.mp hx
  rw [poissonBarrier]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hnorm]
  field_simp [hR]
  ring

/-- On the upper half of the sphere, nonnegative boundary and forcing bounds
make the barrier at least the boundary bound `M`. -/
lemma le_poissonBarrier_on_upper_sphere {n : Nat} {R M F : Real}
    (hR : 0 < R) (hM : 0 <= M) (hF : 0 <= F) (i : Fin n)
    {x : Euclidean n} (hx : x ∈ sphere 0 R) (hxi : 0 <= x i) :
    M <= poissonBarrier R M F i x := by
  have hnorm : ‖x‖ = R := mem_sphere_zero_iff_norm.mp hx
  have hcoord_abs : |x i| <= ‖x‖ := by
    rw [← EuclideanSpace.inner_basisFun_real (Fin n) x i]
    calc
      |inner Real x (EuclideanSpace.basisFun (Fin n) Real i)| <=
          ‖x‖ * ‖EuclideanSpace.basisFun (Fin n) Real i‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖x‖ := by simp
  have hcoord_le : x i <= R := by
    rw [← hnorm]
    exact (le_abs_self (x i)).trans hcoord_abs
  have hcoef : 0 <= F / 2 + (n : Real) * M / R ^ 2 := by
    exact add_nonneg (div_nonneg hF (by norm_num))
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hM) (sq_nonneg R))
  have hproduct :
      0 <= (x i) * (R - x i) * (F / 2 + (n : Real) * M / R ^ 2) :=
    mul_nonneg (mul_nonneg hxi (sub_nonneg.mpr hcoord_le)) hcoef
  rw [poissonBarrier_on_sphere R M F i hR.ne' hx]
  exact le_add_of_nonneg_right hproduct

/-- The barrier's derivative at the centre in its distinguished coordinate is
`R F / 2 + n M / R`. -/
lemma fderiv_poissonBarrier_at_zero_apply_single {n : Nat} (R M F : Real)
    (i : Fin n) :
    fderiv Real (poissonBarrier R M F i) 0
        (EuclideanSpace.single i 1) =
      R * F / 2 + (n : Real) * M / R := by
  have hnormdiff : DifferentiableAt Real
      (fun x : Euclidean n => ‖x‖ ^ 2) 0 :=
    ((contDiff_norm_sq Real (n := 2)).differentiable (by norm_num)) 0
  have hnorm_deriv :
      fderiv Real (fun x : Euclidean n => ‖x‖ ^ 2) 0 = 0 := by
    rw [fderiv_norm_sq]
    ext v
    simp
  have hnorm : HasFDerivAt (fun x : Euclidean n => ‖x‖ ^ 2)
      (0 : Euclidean n →L[Real] Real) (0 : Euclidean n) := by
    simpa only [hnorm_deriv] using hnormdiff.hasFDerivAt
  have hcoord : HasFDerivAt (fun x : Euclidean n => (x i : Real))
      (EuclideanSpace.proj i : Euclidean n →L[Real] Real) 0 := by
    rw [show (fun x : Euclidean n => (x i : Real)) =
      (EuclideanSpace.proj i : Euclidean n →L[Real] Real) by rfl]
    exact (EuclideanSpace.proj i : Euclidean n →L[Real] Real).hasFDerivAt
  have hcoordsq : HasFDerivAt (fun x : Euclidean n => (x i : Real) ^ 2)
      (0 : Euclidean n →L[Real] Real) (0 : Euclidean n) := by
    have h := hcoord.pow 2
    simpa using h
  have hA := hnorm.const_smul (M / R ^ 2)
  have hB := hcoord.const_smul (R * F / 2 + (n : Real) * M / R)
  have hC := hcoordsq.const_smul (-F / 2 - (n : Real) * M / R ^ 2)
  have hsum : HasFDerivAt (poissonBarrier R M F i)
      ((R * F / 2 + (n : Real) * M / R) •
        (EuclideanSpace.proj i : Euclidean n →L[Real] Real)) 0 := by
    simpa only [poissonBarrier, zero_add, add_zero, zero_smul, smul_zero] using
      (hA.add hB).add hC
  rw [hsum.fderiv]
  simp

/-- Upper directional estimate in the distinguished coordinate of the
upper-half-ball argument for Lemma 2.17. -/
lemma poisson_coordinate_fderiv_le
    {n : Nat} [Nonempty (Fin n)] {R M F : Real}
    (hR : 0 < R) (hM : 0 <= M) (hF : 0 <= F)
    {u f : Euclidean n -> Real}
    (huC2 : ContDiffOn Real 2 u (ball (0 : Euclidean n) R))
    (hucont : ContinuousOn u (closedBall (0 : Euclidean n) R))
    (_hfcont : ContinuousOn f (closedBall (0 : Euclidean n) R))
    (hLap : forall x, x ∈ ball (0 : Euclidean n) R -> Δ u x = f x)
    (hboundary : forall x, x ∈ sphere (0 : Euclidean n) R -> |u x| <= M)
    (hforce : forall x, x ∈ ball (0 : Euclidean n) R -> |f x| <= F)
    (i : Fin n) :
    fderiv Real u 0 (EuclideanSpace.basisFun (Fin n) Real i) <=
      R * F / 2 + (n : Real) * M / R := by
  let e : Euclidean n := EuclideanSpace.basisFun (Fin n) Real i
  let rho : Euclidean n ≃ₗᵢ[Real] Euclidean n :=
    coordinateHyperplaneReflection i
  let Omega : Set (Euclidean n) :=
    ball (0 : Euclidean n) R ∩ {x | 0 < x i}
  let K : Set (Euclidean n) :=
    closedBall (0 : Euclidean n) R ∩ {x | 0 <= x i}
  have hcoordcont : Continuous (fun x : Euclidean n => (x i : Real)) := by
    fun_prop
  have hOmegaOpen : IsOpen Omega := by
    exact isOpen_ball.inter (isOpen_lt continuous_const hcoordcont)
  have hKclosed : IsClosed {x : Euclidean n | 0 <= x i} :=
    isClosed_le continuous_const hcoordcont
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall (0 : Euclidean n) R).inter_right hKclosed
  have hKne : K.Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · simp [hR.le]
    · change 0 <= (0 : Euclidean n) i
      simp
  have hOmegaSubK : Omega ⊆ K := by
    intro x hx
    refine ⟨ball_subset_closedBall hx.1, ?_⟩
    change 0 <= x i
    exact le_of_lt hx.2
  have hrho_norm (x : Euclidean n) : ‖rho x‖ = ‖x‖ := by
    exact norm_coordinateHyperplaneReflection i x
  have hrho_coord (x : Euclidean n) : (rho x i : Real) = -(x i) := by
    exact coordinateHyperplaneReflection_coordinate i x
  have hrho_flat {x : Euclidean n} (hx : x i = 0) : rho x = x := by
    exact coordinateHyperplaneReflection_eq_self_of_coordinate_eq_zero i hx
  let rclm : Euclidean n →L[Real] Euclidean n :=
    rho.toContinuousLinearEquiv.toContinuousLinearMap
  have hrclm_apply (x : Euclidean n) : rclm x = rho x := rfl
  have hrclm_ball : ⇑rclm ⁻¹' ball (0 : Euclidean n) R = ball 0 R := by
    ext x
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, hrclm_apply]
    rw [hrho_norm]
  have huroC2 : ContDiffOn Real 2 (u ∘ rho) (ball (0 : Euclidean n) R) := by
    have h := huC2.comp_continuousLinearMap rclm
    rw [hrclm_ball] at h
    convert h using 1
    funext x
    rfl
  have hKball : K ⊆ closedBall (0 : Euclidean n) R := fun x hx => hx.1
  have hucontK : ContinuousOn u K := hucont.mono hKball
  have hKrho : MapsTo rho K (closedBall (0 : Euclidean n) R) := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right, hrho_norm] using
      (mem_closedBall.mp hx.1)
  have hurocontK : ContinuousOn (u ∘ rho) K :=
    hucont.comp rho.continuous.continuousOn hKrho
  let v : Euclidean n -> Real := (2 : Real)⁻¹ • (u - u ∘ rho)
  let w : Euclidean n -> Real := poissonBarrier R M F i
  let q : Euclidean n -> Real := v - w
  have hvC2ball : ContDiffOn Real 2 v (ball (0 : Euclidean n) R) := by
    dsimp [v]
    exact (huC2.sub huroC2).const_smul (2 : Real)⁻¹
  have hvC2 : ContDiffOn Real 2 v Omega :=
    hvC2ball.mono (fun x hx => hx.1)
  have hvcontK : ContinuousOn v K := by
    dsimp [v]
    exact (hucontK.sub hurocontK).const_smul (2 : Real)⁻¹
  have hwC2 : ContDiff Real 2 w := by
    simpa only [w] using poissonBarrier_contDiff R M F i
  have hqC2 : ContDiffOn Real 2 q Omega := by
    dsimp [q]
    exact hvC2.sub hwC2.contDiffOn
  have hqcontK : ContinuousOn q K := by
    dsimp [q]
    exact hvcontK.sub hwC2.continuous.continuousOn
  have hrho_sphere {x : Euclidean n} (hx : x ∈ sphere 0 R) :
      rho x ∈ sphere 0 R := by
    rw [mem_sphere_zero_iff_norm] at hx ⊢
    rw [hrho_norm, hx]
  have hrho_ball_mem {x : Euclidean n} (hx : x ∈ ball 0 R) :
      rho x ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right] at hx ⊢
    simpa [hrho_norm] using hx
  have hv_lap_lower : forall x, x ∈ Omega -> -F <= Δ v x := by
    intro x hx
    have hxin : x ∈ ball (0 : Euclidean n) R := hx.1
    have hrxin : rho x ∈ ball (0 : Euclidean n) R := hrho_ball_mem hxin
    have hux : ContDiffAt Real 2 u x :=
      (huC2 x hxin).contDiffAt (isOpen_ball.mem_nhds hxin)
    have hurx : ContDiffAt Real 2 (u ∘ rho) x :=
      (huroC2 x hxin).contDiffAt (isOpen_ball.mem_nhds hxin)
    have hcomp := laplacian_comp_linearIsometryEquiv_on_ball rho huC2 hxin
    have hvformula :
        Δ v x = (2 : Real)⁻¹ * (Δ u x - Δ u (rho x)) := by
      dsimp [v]
      have hsub : ContDiffAt Real 2 (u - u ∘ rho) x := hux.sub hurx
      have hscale := InnerProductSpace.laplacian_smul (2 : Real)⁻¹ hsub
      rw [hscale, hux.laplacian_sub hurx, hcomp]
      simp only [smul_eq_mul]
    have hfx_lower : -F <= f x := neg_le_of_abs_le (hforce x hxin)
    have hfrx_upper : f (rho x) <= F := le_of_abs_le (hforce (rho x) hrxin)
    rw [hLap x hxin, hLap (rho x) hrxin] at hvformula
    nlinarith [hvformula]
  have hq_lap_nonneg : forall x, x ∈ Omega -> 0 <= Δ q x := by
    intro x hx
    have hvx : ContDiffAt Real 2 v x :=
      (hvC2 x hx).contDiffAt (hOmegaOpen.mem_nhds hx)
    have hwx : ContDiffAt Real 2 w x := hwC2.contDiffAt
    have hqformula := hvx.laplacian_sub hwx
    dsimp [q, w] at hqformula
    rw [laplacian_poissonBarrier R M F i x] at hqformula
    have hvlower := hv_lap_lower x hx
    linarith
  have hq_boundary : forall x, x ∈ K -> x ∉ Omega -> q x <= 0 := by
    intro x hxK hxO
    have hxclosed : x ∈ closedBall (0 : Euclidean n) R := hxK.1
    have hxcoord : 0 <= x i := hxK.2
    by_cases hxball : x ∈ ball (0 : Euclidean n) R
    · have hxzero : x i = 0 := by
        by_contra hxne
        have hxpos : 0 < x i := lt_of_le_of_ne hxcoord (Ne.symm hxne)
        exact hxO ⟨hxball, hxpos⟩
      have hfixed : rho x = x := hrho_flat hxzero
      have hvzero : v x = 0 := by simp [v, hfixed]
      have hw_nonneg : 0 <= w x := by
        dsimp [w, poissonBarrier]
        simp only [hxzero]
        norm_num
        exact mul_nonneg (div_nonneg hM (sq_nonneg R)) (sq_nonneg ‖x‖)
      dsimp [q]
      rw [hvzero]
      linarith
    · have hxsphere : x ∈ sphere (0 : Euclidean n) R := by
        rw [mem_sphere_zero_iff_norm]
        have hle : ‖x‖ <= R := by
          simpa only [mem_closedBall, dist_zero_right] using hxclosed
        have hnlt : ¬‖x‖ < R := by
          intro hlt
          exact hxball (by simpa only [mem_ball, dist_zero_right] using hlt)
        exact le_antisymm hle (le_of_not_gt hnlt)
      have hxrho_sphere : rho x ∈ sphere (0 : Euclidean n) R :=
        hrho_sphere hxsphere
      have huv : |u x - u (rho x)| <= 2 * M := by
        calc
          |u x - u (rho x)| <= |u x| + |u (rho x)| := abs_sub _ _
          _ <= M + M := add_le_add (hboundary x hxsphere)
            (hboundary (rho x) hxrho_sphere)
          _ = 2 * M := by ring
      have hv_le : v x <= M := by
        have hvabs : |v x| <= M := by
          dsimp [v]
          calc
            |(2 : Real)⁻¹ * (u x - u (rho x))| =
                (2 : Real)⁻¹ * |u x - u (rho x)| := by
                  rw [abs_mul]
                  norm_num
            _ <= (2 : Real)⁻¹ * (2 * M) :=
              mul_le_mul_of_nonneg_left huv (by norm_num)
            _ = M := by ring
        exact (le_abs_self _).trans hvabs
      have hw_le : M <= w x := by
        dsimp [w]
        exact le_poissonBarrier_on_upper_sphere hR hM hF i hxsphere hxcoord
      dsimp [q]
      linarith
  let phi : Euclidean n -> Real := fun x => ‖x‖ ^ 2 - R ^ 2
  have hphiC2 : ContDiff Real 2 phi := by
    dsimp [phi]
    exact (contDiff_norm_sq Real).sub contDiff_const
  have hphiCont : ContinuousOn phi K := hphiC2.continuous.continuousOn
  have hphiLap : forall x, x ∈ Omega -> 0 < Δ phi x := by
    intro x hx
    have hnorm : ContDiffAt Real 2
        (fun y : Euclidean n => ‖y‖ ^ 2) x :=
      (contDiff_norm_sq Real (n := 2)).contDiffAt
    have hconst : ContDiffAt Real 2 (fun _ : Euclidean n => R ^ 2) x :=
      contDiffAt_const
    have h := hnorm.laplacian_sub hconst
    change 0 < Δ ((fun y : Euclidean n => ‖y‖ ^ 2) -
      (fun _ : Euclidean n => R ^ 2)) x
    rw [h, laplacian_norm_sq_poisson]
    simp
    have hn : 0 < (n : Real) := by
      exact_mod_cast (Fin.pos_iff_nonempty.mpr inferInstance)
    exact Fin.pos_iff_nonempty.mpr inferInstance
  have hphiBoundary : forall x, x ∈ K -> x ∉ Omega -> phi x <= 0 := by
    intro x hxK hxO
    have hxclosed := hxK.1
    have hxcoord := hxK.2
    by_cases hxball : x ∈ ball (0 : Euclidean n) R
    · have hxzero : x i = 0 := by
        by_contra hxne
        have hxpos : 0 < x i := lt_of_le_of_ne hxcoord (Ne.symm hxne)
        exact hxO ⟨hxball, hxpos⟩
      have hnorm : ‖x‖ <= R := by
        simpa only [mem_closedBall, dist_zero_right] using hxclosed
      dsimp [phi]
      have hprod : 0 <= ‖x‖ * (R - ‖x‖) :=
        mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hnorm)
      nlinarith [hprod]
    · have hxsphere : x ∈ sphere (0 : Euclidean n) R := by
        rw [mem_sphere_zero_iff_norm]
        have hle : ‖x‖ <= R := by
          simpa only [mem_closedBall, dist_zero_right] using hxclosed
        have hnlt : ¬‖x‖ < R := by
          intro hlt
          exact hxball (by simpa only [mem_ball, dist_zero_right] using hlt)
        exact le_antisymm hle (le_of_not_gt hnlt)
      simp [phi, mem_sphere_zero_iff_norm.mp hxsphere]
  have hphiLower : forall x, x ∈ K -> -(R ^ 2) <= phi x := by
    intro x hx
    dsimp [phi]
    nlinarith [sq_nonneg ‖x‖]
  have hcomp := nonpositive_on_compact_of_laplacian_nonneg hOmegaOpen hKcompact
    hKne hOmegaSubK hqcontK hqC2 hq_lap_nonneg hq_boundary hphiC2 hphiCont
      hphiLap hphiBoundary hphiLower (by positivity : 0 < R ^ 2)
  have hq_nonpos : forall x, x ∈ K -> q x <= 0 := hcomp
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    exact (EuclideanSpace.basisFun (Fin n) Real).orthonormal.norm_eq_one i
  have hline_memOmega {t : Real} (ht : 0 < t) (htR : t < R) :
      t • e ∈ Omega := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, he_norm, Real.norm_eq_abs,
        abs_of_pos ht]
      simpa only [mul_one] using htR
    · dsimp [e]
      simpa [smul_eq_mul] using ht
  have hline_le {t : Real} (ht : 0 < t) (htR : t < R) :
      v (t • e) <= w (t • e) := by
    have hto := hline_memOmega ht htR
    have hq := hq_nonpos (t • e) (hOmegaSubK hto)
    dsimp [q] at hq
    linarith
  have hv_zero : v 0 = 0 := by
    have hrho_zero : rho (0 : Euclidean n) = 0 := rho.map_zero
    simp [v, hrho_zero]
  have hw_zero : w 0 = 0 := by
    simp [w, poissonBarrier]
  have hzero_ball : (0 : Euclidean n) ∈ ball 0 R := by
    simp [hR]
  have hv0C2 : ContDiffAt Real 2 v 0 :=
    (hvC2ball 0 hzero_ball).contDiffAt (isOpen_ball.mem_nhds hzero_ball)
  have hw0C2 : ContDiffAt Real 2 w 0 := hwC2.contDiffAt
  have hline : HasDerivAt (fun t : Real => t • e) e 0 := by
    simpa using (hasDerivAt_id (0 : Real)).smul_const e
  have hvF : HasFDerivAt v (fderiv Real v 0) 0 := by
    exact (hv0C2.differentiableAt (by norm_num)).hasFDerivAt
  have hwF : HasFDerivAt w (fderiv Real w 0) 0 := by
    exact (hw0C2.differentiableAt (by norm_num)).hasFDerivAt
  have hlv : HasDerivAt (v ∘ (fun t : Real => t • e))
      (fderiv Real v 0 e) 0 := by
    have hvF0 : HasFDerivAt v (fderiv Real v 0) ((0 : Real) • e) := by
      simpa using hvF
    have h := HasFDerivAt.comp (0 : Real) hvF0 hline.hasFDerivAt
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h.hasDerivAt
  have hlw : HasDerivAt (w ∘ (fun t : Real => t • e))
      (fderiv Real w 0 e) 0 := by
    have hwF0 : HasFDerivAt w (fderiv Real w 0) ((0 : Real) • e) := by
      simpa using hwF
    have h := HasFDerivAt.comp (0 : Real) hwF0 hline.hasFDerivAt
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h.hasDerivAt
  have hineq :
      (fun t : Real => t⁻¹ * (v (t • e) - v 0)) ≤ᶠ[𝓝[>] (0 : Real)]
        (fun t : Real => t⁻¹ * (w (t • e) - w 0)) := by
    have hsmall : ∀ᶠ t : Real in 𝓝[>] (0 : Real), t < R := by
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds hR)
    filter_upwards [hsmall, self_mem_nhdsWithin] with t htR ht
    have hle := hline_le ht htR
    have hinv : 0 <= t⁻¹ := inv_nonneg.mpr ht.le
    rw [hv_zero, hw_zero]
    simp only [sub_zero]
    exact mul_le_mul_of_nonneg_left hle hinv
  have hlimv :
      Tendsto (fun t : Real => t⁻¹ * (v (t • e) - v 0))
        (𝓝[>] (0 : Real)) (𝓝 (fderiv Real v 0 e)) := by
    simpa [smul_eq_mul, zero_add] using hlv.tendsto_slope_zero_right
  have hlimw :
      Tendsto (fun t : Real => t⁻¹ * (w (t • e) - w 0))
        (𝓝[>] (0 : Real)) (𝓝 (fderiv Real w 0 e)) := by
    simpa [smul_eq_mul, zero_add] using hlw.tendsto_slope_zero_right
  have hderiv_le : fderiv Real v 0 e <= fderiv Real w 0 e :=
    le_of_tendsto_of_tendsto hlimv hlimw hineq
  have hrho_e : rho e = -e := by
    dsimp [rho, e]
    exact Submodule.reflection_orthogonalComplement_singleton_eq_neg _
  have hveq : fderiv Real v 0 e = fderiv Real u 0 e := by
    have h0u : ContDiffAt Real 2 u 0 :=
      (huC2 0 hzero_ball).contDiffAt (isOpen_ball.mem_nhds hzero_ball)
    have h0rho : ContDiffAt Real 2 (u ∘ rho) 0 :=
      (huroC2 0 hzero_ball).contDiffAt (isOpen_ball.mem_nhds hzero_ball)
    have huF : HasFDerivAt u (fderiv Real u 0) 0 :=
      (h0u.differentiableAt (by norm_num)).hasFDerivAt
    have huFrho : HasFDerivAt u (fderiv Real u 0) (rho (0 : Euclidean n)) := by
      simpa using huF
    have hcompF := HasFDerivAt.comp (0 : Euclidean n) huFrho
      (rho.hasFDerivAt (x := (0 : Euclidean n)))
    have hvF' := (huF.sub hcompF).const_smul (2 : Real)⁻¹
    have hvfderiv := hvF'.fderiv
    have happ := congrArg (fun L => L e) hvfderiv
    rw [happ]
    change (2 : Real)⁻¹ *
        ((fderiv Real u 0) e - (fderiv Real u 0) (rho e)) =
      (fderiv Real u 0) e
    rw [hrho_e]
    rw [map_neg]
    ring
  have hwderiv : fderiv Real w 0 e =
      R * F / 2 + (n : Real) * M / R := by
    dsimp [w, e]
    simpa only [EuclideanSpace.basisFun_apply] using
      fderiv_poissonBarrier_at_zero_apply_single R M F i
  rw [hveq, hwderiv] at hderiv_le
  exact hderiv_le

lemma poisson_coordinate_fderiv_abs_le
    {n : Nat} [Nonempty (Fin n)] {R M F : Real}
    (hR : 0 < R) (hM : 0 <= M) (hF : 0 <= F)
    {u f : Euclidean n -> Real}
    (huC2 : ContDiffOn Real 2 u (ball (0 : Euclidean n) R))
    (hucont : ContinuousOn u (closedBall (0 : Euclidean n) R))
    (hfcont : ContinuousOn f (closedBall (0 : Euclidean n) R))
    (hLap : forall x, x ∈ ball (0 : Euclidean n) R -> Δ u x = f x)
    (hboundary : forall x, x ∈ sphere (0 : Euclidean n) R -> |u x| <= M)
    (hforce : forall x, x ∈ ball (0 : Euclidean n) R -> |f x| <= F)
    (i : Fin n) :
    |fderiv Real u 0 (EuclideanSpace.basisFun (Fin n) Real i)| <=
      R * F / 2 + (n : Real) * M / R := by
  have hup := poisson_coordinate_fderiv_le hR hM hF huC2 hucont hfcont
    hLap hboundary hforce i
  have hnegLap : forall x, x ∈ ball (0 : Euclidean n) R ->
      Δ (-u) x = (-f) x := by
    intro x hx
    rw [InnerProductSpace.laplacian_neg]
    change -(Δ u x) = -f x
    rw [hLap x hx]
  have hneg := poisson_coordinate_fderiv_le hR hM hF huC2.neg hucont.neg
    hfcont.neg hnegLap (by
      intro x hx
      simpa only [Pi.neg_apply, abs_neg] using hboundary x hx) (by
      intro x hx
      simpa only [Pi.neg_apply, abs_neg] using hforce x hx) i
  have hlow : -(R * F / 2 + (n : Real) * M / R) <=
      fderiv Real u 0 (EuclideanSpace.basisFun (Fin n) Real i) := by
    have hfun : (fun x : Euclidean n => -u x) = -u := rfl
    rw [hfun, fderiv_neg] at hneg
    change -(fderiv Real u 0 (EuclideanSpace.basisFun (Fin n) Real i)) <=
      R * F / 2 + (n : Real) * M / R at hneg
    linarith
  exact abs_le.mpr ⟨hlow, hup⟩

/-- The coordinate estimate is invariant under orthogonal changes of
coordinates, hence controls the full derivative norm. -/
theorem poisson_fderiv_norm_le_of_bounds
    {n : Nat} [Nonempty (Fin n)] {R M F : Real}
    (hR : 0 < R) (hM : 0 <= M) (hF : 0 <= F)
    {u f : Euclidean n -> Real}
    (huC2 : ContDiffOn Real 2 u (ball (0 : Euclidean n) R))
    (hucont : ContinuousOn u (closedBall (0 : Euclidean n) R))
    (hfcont : ContinuousOn f (closedBall (0 : Euclidean n) R))
    (hLap : forall x, x ∈ ball (0 : Euclidean n) R -> Δ u x = f x)
    (hboundary : forall x, x ∈ sphere (0 : Euclidean n) R -> |u x| <= M)
    (hforce : forall x, x ∈ ball (0 : Euclidean n) R -> |f x| <= F) :
    ‖fderiv Real u 0‖ <= R * F / 2 + (n : Real) * M / R := by
  let B : Real := R * F / 2 + (n : Real) * M / R
  have hB : 0 <= B := by
    dsimp [B]
    exact add_nonneg (div_nonneg (mul_nonneg hR.le hF) (by norm_num))
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hM) hR.le)
  refine (fderiv Real u 0).opNorm_le_bound hB ?_
  intro v
  by_cases hv : v = 0
  · simp [hv]
  let d : Euclidean n := ‖v‖⁻¹ • v
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hd_norm : ‖d‖ = 1 := by
    dsimp [d]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hvnorm]
  let i : Fin n := Classical.choice inferInstance
  let e : Euclidean n := EuclideanSpace.basisFun (Fin n) Real i
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    exact (EuclideanSpace.basisFun (Fin n) Real).orthonormal.norm_eq_one i
  let Q : Euclidean n ≃ₗᵢ[Real] Euclidean n :=
    (Real ∙ (e - d))ᗮ.reflection
  have hQe : Q e = d := by
    dsimp [Q]
    exact Submodule.reflection_sub (he_norm.trans hd_norm.symm)
  let qclm : Euclidean n →L[Real] Euclidean n :=
    Q.toContinuousLinearEquiv.toContinuousLinearMap
  have hqclm_apply (x : Euclidean n) : qclm x = Q x := rfl
  have hpre_ball : ⇑qclm ⁻¹' ball (0 : Euclidean n) R = ball 0 R := by
    ext x
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, hqclm_apply,
      Q.norm_map]
  have huQC2 : ContDiffOn Real 2 (u ∘ Q) (ball (0 : Euclidean n) R) := by
    have h := huC2.comp_continuousLinearMap qclm
    rw [hpre_ball] at h
    convert h using 1
    funext x
    rfl
  have hQclosed : MapsTo Q (closedBall (0 : Euclidean n) R)
      (closedBall (0 : Euclidean n) R) := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right, Q.norm_map] using hx
  have huQcont : ContinuousOn (u ∘ Q) (closedBall (0 : Euclidean n) R) :=
    hucont.comp Q.continuous.continuousOn hQclosed
  have hfQcont : ContinuousOn (f ∘ Q) (closedBall (0 : Euclidean n) R) :=
    hfcont.comp Q.continuous.continuousOn hQclosed
  have hQball {x : Euclidean n} (hx : x ∈ ball (0 : Euclidean n) R) :
      Q x ∈ ball (0 : Euclidean n) R := by
    simpa only [mem_ball, dist_zero_right, Q.norm_map] using hx
  have hQsphere {x : Euclidean n} (hx : x ∈ sphere (0 : Euclidean n) R) :
      Q x ∈ sphere (0 : Euclidean n) R := by
    simpa only [mem_sphere, dist_zero_right, Q.norm_map] using hx
  have hLapQ : forall x, x ∈ ball (0 : Euclidean n) R ->
      Δ (u ∘ Q) x = (f ∘ Q) x := by
    intro x hx
    rw [laplacian_comp_linearIsometryEquiv_on_ball Q huC2 hx]
    exact hLap (Q x) (hQball hx)
  have hboundaryQ : forall x, x ∈ sphere (0 : Euclidean n) R ->
      |(u ∘ Q) x| <= M := by
    intro x hx
    exact hboundary (Q x) (hQsphere hx)
  have hforceQ : forall x, x ∈ ball (0 : Euclidean n) R ->
      |(f ∘ Q) x| <= F := by
    intro x hx
    exact hforce (Q x) (hQball hx)
  have hcoord := poisson_coordinate_fderiv_abs_le hR hM hF huQC2 huQcont
    hfQcont hLapQ hboundaryQ hforceQ i
  have hzero_ball : (0 : Euclidean n) ∈ ball 0 R := by simp [hR]
  have hu0C2 : ContDiffAt Real 2 u 0 :=
    (huC2 0 hzero_ball).contDiffAt (isOpen_ball.mem_nhds hzero_ball)
  have huF : HasFDerivAt u (fderiv Real u 0) 0 :=
    (hu0C2.differentiableAt (by norm_num)).hasFDerivAt
  have huFQ : HasFDerivAt (u ∘ Q)
      ((fderiv Real u 0).comp qclm) 0 := by
    have huF0 : HasFDerivAt u (fderiv Real u 0) (Q (0 : Euclidean n)) := by
      simpa using huF
    exact HasFDerivAt.comp (0 : Euclidean n) huF0
      (Q.hasFDerivAt (x := (0 : Euclidean n)))
  have hdir : |fderiv Real u 0 d| <= B := by
    rw [huFQ.fderiv] at hcoord
    change |fderiv Real u 0 (Q e)| <= B at hcoord
    rwa [hQe] at hcoord
  have hv_eq : v = ‖v‖ • d := by
    dsimp [d]
    rw [smul_smul, mul_inv_cancel₀ hvnorm, one_smul]
  change ‖fderiv Real u 0 v‖ <= B * ‖v‖
  calc
    ‖fderiv Real u 0 v‖ = ‖fderiv Real u 0 (‖v‖ • d)‖ := by rw [← hv_eq]
    _ = ‖v‖ * |fderiv Real u 0 d| := by
      rw [map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg v), Real.norm_eq_abs]
    _ <= ‖v‖ * B := mul_le_mul_of_nonneg_left hdir (norm_nonneg v)
    _ = B * ‖v‖ := mul_comm _ _

/-- Han--Lin Lemma 2.17.  A solution of the Poisson equation on a ball has
its derivative at the center bounded by the boundary maximum of the solution
and the interior supremum of the forcing term. -/
theorem poisson_fderiv_norm_le
    {n : Nat} [Nonempty (Fin n)] {R : Real} (hR : 0 < R)
    {u f : Euclidean n -> Real}
    (huC2 : ContDiffOn Real 2 u (ball (0 : Euclidean n) R))
    (hucont : ContinuousOn u (closedBall (0 : Euclidean n) R))
    (hfcont : ContinuousOn f (closedBall (0 : Euclidean n) R))
    (hLap : forall x, x ∈ ball (0 : Euclidean n) R -> Δ u x = f x) :
    ‖fderiv Real u 0‖ <=
      (n : Real) / R *
          sSup ((fun x : Euclidean n => ‖u x‖) '' sphere 0 R) +
        R / 2 * sSup ((fun x : Euclidean n => ‖f x‖) '' ball 0 R) := by
  let M : Real :=
    sSup ((fun x : Euclidean n => ‖u x‖) '' sphere 0 R)
  let F : Real :=
    sSup ((fun x : Euclidean n => ‖f x‖) '' ball 0 R)
  have hsphere : (sphere (0 : Euclidean n) R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have hMcompact :
      IsCompact ((fun x : Euclidean n => ‖u x‖) '' sphere 0 R) :=
    (isCompact_sphere (0 : Euclidean n) R).image_of_continuousOn
      (hucont.mono sphere_subset_closedBall).norm
  have hMne : ((fun x : Euclidean n => ‖u x‖) '' sphere 0 R).Nonempty :=
    hsphere.image (fun x : Euclidean n => ‖u x‖)
  have hMgreatest :
      IsGreatest ((fun x : Euclidean n => ‖u x‖) '' sphere 0 R) M := by
    simpa only [M] using hMcompact.isGreatest_sSup hMne
  have hM : 0 <= M := by
    obtain ⟨x, hx⟩ := hsphere
    exact (norm_nonneg (u x)).trans (hMgreatest.2 ⟨x, hx, rfl⟩)
  have hclosedFcompact :
      IsCompact ((fun x : Euclidean n => ‖f x‖) '' closedBall 0 R) :=
    (isCompact_closedBall (0 : Euclidean n) R).image_of_continuousOn
      hfcont.norm
  have hclosedFne :
      ((fun x : Euclidean n => ‖f x‖) '' closedBall 0 R).Nonempty := by
    exact ⟨‖f 0‖, 0, mem_closedBall_self hR.le, rfl⟩
  have hclosedFgreatest :
      IsGreatest ((fun x : Euclidean n => ‖f x‖) '' closedBall 0 R)
        (sSup ((fun x : Euclidean n => ‖f x‖) '' closedBall 0 R)) :=
    hclosedFcompact.isGreatest_sSup hclosedFne
  have hFbdd :
      BddAbove ((fun x : Euclidean n => ‖f x‖) '' ball 0 R) := by
    refine ⟨sSup ((fun x : Euclidean n => ‖f x‖) '' closedBall 0 R), ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hclosedFgreatest.2 ⟨x, ball_subset_closedBall hx, rfl⟩
  have hzero_ball : (0 : Euclidean n) ∈ ball 0 R := mem_ball_self hR
  have hF : 0 <= F := by
    exact (norm_nonneg (f 0)).trans
      (le_csSup hFbdd ⟨0, hzero_ball, rfl⟩)
  have hboundary : forall x, x ∈ sphere (0 : Euclidean n) R -> |u x| <= M := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact hMgreatest.2 ⟨x, hx, rfl⟩
  have hforce : forall x, x ∈ ball (0 : Euclidean n) R -> |f x| <= F := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_csSup hFbdd ⟨x, hx, rfl⟩
  have hbound := poisson_fderiv_norm_le_of_bounds hR hM hF huC2 hucont
    hfcont hLap hboundary hforce
  change ‖fderiv Real u 0‖ <= (n : Real) / R * M + R / 2 * F
  calc
    ‖fderiv Real u 0‖ <= R * F / 2 + (n : Real) * M / R := hbound
    _ = (n : Real) / R * M + R / 2 * F := by ring

end HanLinLectureNotes.Ch02
