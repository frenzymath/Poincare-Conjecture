import HanLinLectureNotes.Ch02.HopfMaximum

/-!
# Han--Lin Chapter 2: positive supersolution transform

This file develops the quotient transformation used to remove a zero-order
sign obstruction by dividing by a positive supersolution.
-/

open Filter InnerProductSpace Metric Set Topology
open scoped ContDiff

noncomputable section

namespace HanLinLectureNotes.Ch02

lemma fderiv_fderiv_mul_apply
    {n : Nat} {u v : Euclidean n → Real} {p ei ej : Euclidean n}
    (hu : ContDiffAt Real 2 u p) (hv : ContDiffAt Real 2 v p) :
    fderiv Real (fun y => fderiv Real (fun z => u z * v z) y ej) p ei =
      u p * fderiv Real (fun y => fderiv Real v y ej) p ei +
      v p * fderiv Real (fun y => fderiv Real u y ej) p ei +
      fderiv Real u p ei * fderiv Real v p ej +
      fderiv Real v p ei * fderiv Real u p ej := by
  have heu : ∀ᶠ y in 𝓝 p, ContDiffAt Real 2 u y :=
    hu.eventually (by norm_num)
  have hev : ∀ᶠ y in 𝓝 p, ContDiffAt Real 2 v y :=
    hv.eventually (by norm_num)
  have heq :
      (fun y => fderiv Real (fun z => u z * v z) y ej) =ᶠ[𝓝 p]
        fun y => u y * fderiv Real v y ej + v y * fderiv Real u y ej := by
    filter_upwards [heu, hev] with y huy hvy
    rw [fderiv_fun_mul (huy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [heq.fderiv_eq]
  have hdu : DifferentiableAt Real u p := hu.differentiableAt (by norm_num)
  have hdv : DifferentiableAt Real v p := hv.differentiableAt (by norm_num)
  have hDdu : DifferentiableAt Real (fun y => fderiv Real u y ej) p := by
    have hdiff : DifferentiableAt Real (fderiv Real u) p :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    exact (hdiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ej p)).differentiableAt
  have hDdv : DifferentiableAt Real (fun y => fderiv Real v y ej) p := by
    have hdiff : DifferentiableAt Real (fderiv Real v) p :=
      (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    exact (hdiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ej p)).differentiableAt
  have hadd := fderiv_fun_add
    (f := fun y => u y * fderiv Real v y ej)
    (g := fun y => v y * fderiv Real u y ej)
    (hdu.mul hDdv) (hdv.mul hDdu)
  rw [hadd, fderiv_fun_mul hdu hDdv, fderiv_fun_mul hdv hDdu]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Drift coefficient produced by writing `u = w v`.  The transpose term
keeps the formula valid without assuming that the leading matrix is symmetric. -/
def positiveSupersolutionDrift {n : Nat}
    (a : Euclidean n → Matrix (Fin n) (Fin n) Real)
    (b : Euclidean n → Fin n → Real) (w : Euclidean n → Real) :
    Euclidean n → Fin n → Real :=
  fun x i => b x i + (∑ j, (a x i j + a x j i) *
    fderiv Real w x (EuclideanSpace.basisFun (Fin n) Real j)) / w x

/-- Zero-order coefficient produced by division by a positive supersolution. -/
def positiveSupersolutionZeroOrder {n : Nat}
    (a : Euclidean n → Matrix (Fin n) (Fin n) Real)
    (b : Euclidean n → Fin n → Real) (c w : Euclidean n → Real) :
    Euclidean n → Real :=
  fun x => nondivergenceOperator a b c w x / w x

lemma sum_leading_product_cross {n : Nat}
    (A : Fin n → Fin n → Real) (dw dv : Fin n → Real) :
    (∑ i, ∑ j, A i j * (dw i * dv j + dv i * dw j)) =
      ∑ i, (∑ j, (A i j + A j i) * dw j) * dv i := by
  have hswap :
      (∑ i, ∑ j, A i j * dw i * dv j) =
        ∑ i, ∑ j, A j i * dw j * dv i := by
    rw [Finset.sum_comm]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [add_comm]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simpa only [mul_assoc] using hswap

lemma nondivergenceOperator_mul_eq_positiveSupersolution
    {n : Nat} {w v : Euclidean n → Real} {x : Euclidean n}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hw : ContDiffAt Real 2 w x) (hv : ContDiffAt Real 2 v x)
    (hwne : w x ≠ 0) :
    nondivergenceOperator a b c (fun y => w y * v y) x =
      w x * nondivergenceOperator a (positiveSupersolutionDrift a b w)
        (positiveSupersolutionZeroOrder a b c w) v x := by
  rw [nondivergenceOperator_eq_coordinate (hw.mul hv)]
  rw [nondivergenceOperator_eq_coordinate hv]
  simp only [positiveSupersolutionZeroOrder]
  rw [nondivergenceOperator_eq_coordinate hw]
  have hfirst : ∀ i,
      fderiv Real (fun y => w y * v y) x
          (EuclideanSpace.basisFun (Fin n) Real i) =
        w x * fderiv Real v x (EuclideanSpace.basisFun (Fin n) Real i) +
        v x * fderiv Real w x (EuclideanSpace.basisFun (Fin n) Real i) := by
    intro i
    rw [fderiv_fun_mul (hw.differentiableAt (by norm_num))
      (hv.differentiableAt (by norm_num))]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [fderiv_fderiv_mul_apply hw hv, hfirst]
  simp only [positiveSupersolutionDrift]
  simp only [mul_add, Finset.mul_sum, div_eq_mul_inv]
  field_simp [hwne]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  have hsecondV :
      (∑ i, ∑ j, a x i j *
        (w x * fderiv Real (fun y => fderiv Real v y
          (EuclideanSpace.basisFun (Fin n) Real j)) x
          (EuclideanSpace.basisFun (Fin n) Real i))) =
      ∑ i, ∑ j, w x * a x i j *
        fderiv Real (fun y => fderiv Real v y
          (EuclideanSpace.basisFun (Fin n) Real j)) x
          (EuclideanSpace.basisFun (Fin n) Real i) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsecondW :
      (∑ i, ∑ j, a x i j *
        (v x * fderiv Real (fun y => fderiv Real w y
          (EuclideanSpace.basisFun (Fin n) Real j)) x
          (EuclideanSpace.basisFun (Fin n) Real i))) =
      v x * (∑ i, ∑ j, a x i j *
        fderiv Real (fun y => fderiv Real w y
          (EuclideanSpace.basisFun (Fin n) Real j)) x
          (EuclideanSpace.basisFun (Fin n) Real i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfirstV :
      (∑ i, b x i *
        (w x * fderiv Real v x (EuclideanSpace.basisFun (Fin n) Real i))) =
      ∑ i, w x * b x i *
        fderiv Real v x (EuclideanSpace.basisFun (Fin n) Real i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hfirstW :
      (∑ i, b x i *
        (v x * fderiv Real w x (EuclideanSpace.basisFun (Fin n) Real i))) =
      v x * ∑ i, b x i *
        fderiv Real w x (EuclideanSpace.basisFun (Fin n) Real i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsecondV, hsecondW, hfirstV, hfirstW]
  have hcross := sum_leading_product_cross
    (fun i j => a x i j)
    (fun i => fderiv Real w x (EuclideanSpace.basisFun (Fin n) Real i))
    (fun i => fderiv Real v x (EuclideanSpace.basisFun (Fin n) Real i))
  simp only [mul_add, add_mul, Finset.sum_add_distrib] at hcross
  simp only [add_mul, Finset.sum_add_distrib]
  linear_combination hcross

lemma continuousOn_nondivergenceOperator
    {n : Nat} {O : Set (Euclidean n)} {w : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hO : IsOpen O) (ha : ContinuousOn a O) (hb : ContinuousOn b O)
    (hc : ContinuousOn c O) (hw : ContDiffOn Real 2 w O) :
    ContinuousOn (nondivergenceOperator a b c w) O := by
  let e : Fin n → Euclidean n :=
    fun i => EuclideanSpace.basisFun (Fin n) Real i
  have hDcd : ContDiffOn Real 1 (fderiv Real w) O :=
    hw.fderiv_of_isOpen hO (by norm_num)
  have hD : ContinuousOn (fderiv Real w) O := hDcd.continuousOn
  have hDD : ContinuousOn (fderiv Real (fderiv Real w)) O :=
    (hDcd.fderiv_of_isOpen hO (m := 0) (by norm_num)).continuousOn
  have haij : ∀ i j, ContinuousOn (fun x => a x i j) O :=
    fun i j => (continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn ha)
  have hbi : ∀ i, ContinuousOn (fun x => b x i) O :=
    fun i => (continuous_apply i).comp_continuousOn hb
  have hDi : ∀ i, ContinuousOn (fun x => fderiv Real w x (e i)) O :=
    fun i => hD.clm_apply continuousOn_const
  have hDDij : ∀ i j, ContinuousOn
      (fun x => fderiv Real (fderiv Real w) x (e i) (e j)) O :=
    fun i j => (hDD.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hexpr : ContinuousOn
      (fun x =>
        (∑ i, ∑ j, a x i j * fderiv Real (fderiv Real w) x (e i) (e j)) +
        ∑ i, b x i * fderiv Real w x (e i) + c x * w x) O := by
    exact ((continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun j _ => (haij i j).mul (hDDij i j)).add
        (continuousOn_finsetSum _ fun i _ => (hbi i).mul (hDi i))).add
      (hc.mul hw.continuousOn)
  apply hexpr.congr
  intro x hx
  have hwx := (hw x hx).contDiffAt (hO.mem_nhds hx)
  rw [nondivergenceOperator_eq_coordinate hwx]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact fderiv_apply_eq_fderiv_fderiv hwx

lemma continuousOn_positiveSupersolutionDrift
    {n : Nat} {O : Set (Euclidean n)} {w : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real}
    (hO : IsOpen O) (ha : ContinuousOn a O) (hb : ContinuousOn b O)
    (hw : ContDiffOn Real 2 w O) (hwne : ∀ x ∈ O, w x ≠ 0) :
    ContinuousOn (positiveSupersolutionDrift a b w) O := by
  have hD : ContinuousOn (fderiv Real w) O :=
    (hw.fderiv_of_isOpen hO (m := 1) (by norm_num)).continuousOn
  rw [continuousOn_pi]
  intro i
  have hbi : ContinuousOn (fun x => b x i) O :=
    (continuous_apply i).comp_continuousOn hb
  have hsum : ContinuousOn
      (fun x => ∑ j, (a x i j + a x j i) *
        fderiv Real w x (EuclideanSpace.basisFun (Fin n) Real j)) O := by
    apply continuousOn_finsetSum
    intro j hj
    have haij : ContinuousOn (fun x => a x i j) O :=
      (continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn ha)
    have haji : ContinuousOn (fun x => a x j i) O :=
      (continuous_apply i).comp_continuousOn
        ((continuous_apply j).comp_continuousOn ha)
    exact (haij.add haji).mul (hD.clm_apply continuousOn_const)
  exact hbi.add (hsum.div hw.continuousOn hwne)

lemma continuousOn_positiveSupersolutionZeroOrder
    {n : Nat} {O : Set (Euclidean n)} {w : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hO : IsOpen O) (ha : ContinuousOn a O) (hb : ContinuousOn b O)
    (hc : ContinuousOn c O) (hw : ContDiffOn Real 2 w O)
    (hwne : ∀ x ∈ O, w x ≠ 0) :
    ContinuousOn (positiveSupersolutionZeroOrder a b c w) O :=
  (continuousOn_nondivergenceOperator hO ha hb hc hw).div
    hw.continuousOn hwne

lemma nondivergenceOperator_congr_on_open
    {n : Nat} {O : Set (Euclidean n)} (hO : IsOpen O)
    {f g : Euclidean n → Real} (hfg : EqOn f g O)
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    {x : Euclidean n} (hx : x ∈ O) :
    nondivergenceOperator a b c f x = nondivergenceOperator a b c g x := by
  have hdf : EqOn (fderiv Real f) (fderiv Real g) O := by
    intro y hy
    exact (hfg.eventuallyEq_of_mem (hO.mem_nhds hy)).fderiv_eq
  have hfx : fderiv Real f x = fderiv Real g x :=
    (hfg.eventuallyEq_of_mem (hO.mem_nhds hx)).fderiv_eq
  have hffx : fderiv Real (fderiv Real f) x =
      fderiv Real (fderiv Real g) x :=
    (hdf.eventuallyEq_of_mem (hO.mem_nhds hx)).fderiv_eq
  unfold nondivergenceOperator hessianMatrix secondDerivativeBilin
  rw [hfx, hffx, hfg hx]

/-- Interior conclusion of Han--Lin Theorem 2.13.  Division by a positive
supersolution turns the original equation into one whose zero-order
coefficient is nonpositive, so the strong maximum principle applies. -/
theorem positive_supersolution_interior_max_constant
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u w : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a Omega)
    (hb : ContinuousOn b Omega)
    (hc_cont : ContinuousOn c Omega)
    (huC2 : ContDiffOn Real 2 u Omega)
    (hwC2 : ContDiffOn Real 2 w Omega)
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a b c u x)
    (hLw : ∀ x ∈ Omega, nondivergenceOperator a b c w x ≤ 0)
    (hwpos : ∀ x ∈ Omega, 0 < w x)
    {x0 : Euclidean n} (hx0 : x0 ∈ Omega)
    (hmax : ∀ x ∈ Omega, u x / w x ≤ u x0 / w x0)
    (hmax0 : 0 ≤ u x0 / w x0) :
    ∀ x ∈ Omega, u x / w x = u x0 / w x0 := by
  let v : Euclidean n → Real := fun x => u x / w x
  have hwne : ∀ x ∈ Omega, w x ≠ 0 :=
    fun x hx => ne_of_gt (hwpos x hx)
  have hvC2 : ContDiffOn Real 2 v Omega := by
    simpa only [v, Pi.div_apply] using! huC2.div hwC2 hwne
  have hproduct : EqOn (fun y => w y * v y) u Omega := by
    intro y hy
    simp only [v]
    field_simp [hwne y hy]
  have hBcont : ContinuousOn (positiveSupersolutionDrift a b w) Omega :=
    continuousOn_positiveSupersolutionDrift hOmega_open ha hb hwC2 hwne
  have hqcont : ContinuousOn
      (positiveSupersolutionZeroOrder a b c w) Omega :=
    continuousOn_positiveSupersolutionZeroOrder hOmega_open ha hb hc_cont
      hwC2 hwne
  have hqnonpos : ∀ x ∈ Omega,
      positiveSupersolutionZeroOrder a b c w x ≤ 0 := by
    intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (hLw x hx) (hwpos x hx).le
  have hLv : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a
      (positiveSupersolutionDrift a b w)
      (positiveSupersolutionZeroOrder a b c w) v x := by
    intro x hx
    have hwAt := (hwC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
    have hvAt := (hvC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
    have hmul := nondivergenceOperator_mul_eq_positiveSupersolution
      (a := a) (b := b) (c := c) hwAt hvAt (hwne x hx)
    have hcongr := nondivergenceOperator_congr_on_open hOmega_open
      hproduct (a := a) (b := b) (c := c) hx
    have hnonneg : 0 ≤ w x * nondivergenceOperator a
        (positiveSupersolutionDrift a b w)
        (positiveSupersolutionZeroOrder a b c w) v x := by
      rw [← hmul, hcongr]
      exact hLu x hx
    exact nonneg_of_mul_nonneg_right hnonneg (hwpos x hx)
  have hconst := strong_maximum_principle_interior hOmega_open
    hOmega_connected ha hBcont hqcont hvC2 hvC2.continuousOn
      helliptic hLv hqnonpos hx0 (by simpa [v] using hmax)
      (by simpa [v] using hmax0)
  simpa [v] using hconst

theorem positive_supersolution_comparison
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u v w : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (hvC2 : ContDiffOn Real 2 v Omega)
    (hwC2 : ContDiffOn Real 2 w Omega)
    (hu_cont : ContinuousOn u (closure Omega))
    (hv_cont : ContinuousOn v (closure Omega))
    (hw_cont : ContinuousOn w (closure Omega))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLuv : ∀ x ∈ Omega,
      nondivergenceOperator a b c v x ≤ nondivergenceOperator a b c u x)
    (hLw : ∀ x ∈ Omega, nondivergenceOperator a b c w x ≤ 0)
    (hwpos : ∀ x ∈ closure Omega, 0 < w x)
    (hboundary : ∀ x ∈ frontier Omega, u x ≤ v x) :
    ∀ x ∈ closure Omega, u x ≤ v x := by
  let d : Euclidean n → Real := u + (-1 : Real) • v
  let q : Euclidean n → Real := fun x => d x / w x
  have hwne_closure : ∀ x ∈ closure Omega, w x ≠ 0 :=
    fun x hx => ne_of_gt (hwpos x hx)
  have hdC2 : ContDiffOn Real 2 d Omega := by
    simpa only [d] using! huC2.add (hvC2.const_smul (-1 : Real))
  have hd_cont : ContinuousOn d (closure Omega) := by
    simpa only [d] using! hu_cont.add (hv_cont.const_smul (-1 : Real))
  have hq_cont : ContinuousOn q (closure Omega) := by
    simpa only [q, Pi.div_apply] using!
      hd_cont.div hw_cont hwne_closure
  have hLd : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a b c d x := by
    intro x hx
    have huAt := (huC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
    have hvAt := (hvC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
    have hadd := nondivergenceOperator_add_const_smul
      (a := a) (b := b) (c := c) (-1 : Real) huAt hvAt
    simp only [d]
    rw [hadd]
    have huv := hLuv x hx
    linarith
  intro x hx
  by_contra huv
  have hdux : 0 < d x := by
    simp only [d, Pi.add_apply, neg_smul, one_smul]
    exact sub_pos.mpr (lt_of_not_ge huv)
  have hqx : 0 < q x := by
    simp only [q]
    exact div_pos hdux (hwpos x hx)
  have hcompact : IsCompact (closure Omega) :=
    isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hOmega_bounded.closure⟩
  have hclosure_ne : (closure Omega).Nonempty :=
    hOmega_connected.nonempty.mono subset_closure
  obtain ⟨x0, hx0, hx0max⟩ :=
    hcompact.exists_isMaxOn hclosure_ne hq_cont
  have hq0pos : 0 < q x0 :=
    lt_of_lt_of_le hqx ((isMaxOn_iff.mp hx0max) x hx)
  have hx0notfrontier : x0 ∉ frontier Omega := by
    intro hx0frontier
    have hd0 : d x0 ≤ 0 := by
      simp only [d, Pi.add_apply, neg_smul, one_smul]
      exact sub_nonpos.mpr (hboundary x0 hx0frontier)
    have hq0nonpos : q x0 ≤ 0 := by
      simp only [q]
      exact div_nonpos_of_nonpos_of_nonneg hd0 (hwpos x0 hx0).le
    linarith
  have hx0Omega : x0 ∈ Omega := by
    by_contra hx0not
    apply hx0notfrontier
    rw [hOmega_open.frontier_eq]
    exact ⟨hx0, hx0not⟩
  have hqconst : ∀ y ∈ Omega, q y = q x0 := by
    have hconst := positive_supersolution_interior_max_constant
      hOmega_open hOmega_connected
      (ha.mono fun y hy => subset_closure hy)
      (hb.mono fun y hy => subset_closure hy)
      (hc_cont.mono fun y hy => subset_closure hy)
      hdC2 hwC2 helliptic hLd hLw
      (fun y hy => hwpos y (subset_closure hy)) hx0Omega
      (fun y hy => (isMaxOn_iff.mp hx0max) y (subset_closure hy)) hq0pos.le
    simpa only [q] using hconst
  set E : Set (Euclidean n) := closure Omega ∩ q ⁻¹' {q x0} with hE
  have hEclosed : IsClosed E := by
    rw [hE]
    exact hq_cont.preimage_isClosed_of_isClosed isClosed_closure
      isClosed_singleton
  have hOmegaE : Omega ⊆ E := by
    intro y hy
    rw [hE, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨subset_closure hy, hqconst y hy⟩
  have hclosureE : closure Omega ⊆ E := by
    rw [← hEclosed.closure_eq]
    exact closure_mono hOmegaE
  obtain ⟨zout, hzout⟩ := exists_not_mem_closure_of_bounded hOmega_bounded
  have hOmega_ne_univ : Omega ≠ univ := by
    intro hOmega
    apply hzout
    simp [hOmega]
  have hfrontier_ne : (frontier Omega).Nonempty :=
    nonempty_frontier_iff.mpr ⟨hOmega_connected.nonempty, hOmega_ne_univ⟩
  obtain ⟨z, hzfrontier⟩ := hfrontier_ne
  have hqz : q z = q x0 := by
    have hzE := hclosureE (frontier_subset_closure hzfrontier)
    rw [hE, mem_inter_iff, mem_preimage, mem_singleton_iff] at hzE
    exact hzE.2
  have hdz : d z ≤ 0 := by
    simp only [d, Pi.add_apply, neg_smul, one_smul]
    exact sub_nonpos.mpr (hboundary z hzfrontier)
  have hqznonpos : q z ≤ 0 := by
    simp only [q]
    exact div_nonpos_of_nonpos_of_nonneg hdz
      (hwpos z (frontier_subset_closure hzfrontier)).le
  rw [hqz] at hqznonpos
  linarith

theorem positive_supersolution_dirichlet_unique
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u v w : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (hvC2 : ContDiffOn Real 2 v Omega)
    (hwC2 : ContDiffOn Real 2 w Omega)
    (hu_cont : ContinuousOn u (closure Omega))
    (hv_cont : ContinuousOn v (closure Omega))
    (hw_cont : ContinuousOn w (closure Omega))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLuv : ∀ x ∈ Omega,
      nondivergenceOperator a b c u x = nondivergenceOperator a b c v x)
    (hLw : ∀ x ∈ Omega, nondivergenceOperator a b c w x ≤ 0)
    (hwpos : ∀ x ∈ closure Omega, 0 < w x)
    (hboundary : ∀ x ∈ frontier Omega, u x = v x) :
    ∀ x ∈ closure Omega, u x = v x := by
  have huv := positive_supersolution_comparison hOmega_open hOmega_bounded
    hOmega_connected ha hb hc_cont huC2 hvC2 hwC2 hu_cont hv_cont hw_cont
      helliptic (fun x hx => (hLuv x hx).ge) hLw hwpos
      (fun x hx => (hboundary x hx).le)
  have hvu := positive_supersolution_comparison hOmega_open hOmega_bounded
    hOmega_connected ha hb hc_cont hvC2 huC2 hwC2 hv_cont hu_cont hw_cont
      helliptic (fun x hx => (hLuv x hx).le) hLw hwpos
      (fun x hx => (hboundary x hx).ge)
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

/-- Han--Lin Remark 2.14.  A positive supersolution supplies both the
comparison principle and, consequently, uniqueness for equal Dirichlet data. -/
theorem positive_supersolution_comparison_and_dirichlet_uniqueness
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u v w : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (hvC2 : ContDiffOn Real 2 v Omega)
    (hwC2 : ContDiffOn Real 2 w Omega)
    (hu_cont : ContinuousOn u (closure Omega))
    (hv_cont : ContinuousOn v (closure Omega))
    (hw_cont : ContinuousOn w (closure Omega))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLuv : ∀ x ∈ Omega,
      nondivergenceOperator a b c v x ≤ nondivergenceOperator a b c u x)
    (hLw : ∀ x ∈ Omega, nondivergenceOperator a b c w x ≤ 0)
    (hwpos : ∀ x ∈ closure Omega, 0 < w x)
    (hboundary : ∀ x ∈ frontier Omega, u x ≤ v x) :
    (∀ x ∈ closure Omega, u x ≤ v x) ∧
      ((∀ x ∈ Omega,
        nondivergenceOperator a b c u x = nondivergenceOperator a b c v x) →
       (∀ x ∈ frontier Omega, u x = v x) →
       ∀ x ∈ closure Omega, u x = v x) := by
  constructor
  · exact positive_supersolution_comparison hOmega_open hOmega_bounded
      hOmega_connected ha hb hc_cont huC2 hvC2 hwC2 hu_cont hv_cont hw_cont
        helliptic hLuv hLw hwpos hboundary
  · intro hoperator hdata
    exact positive_supersolution_dirichlet_unique hOmega_open hOmega_bounded
      hOmega_connected ha hb hc_cont huC2 hvC2 hwC2 hu_cont hv_cont hw_cont
        helliptic hoperator hLw hwpos hdata

end HanLinLectureNotes.Ch02
