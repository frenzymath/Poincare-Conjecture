import MorganTianLib.Ch03.RicciFlow.CurvatureEvolution
import MorganTianLib.Ch03.RicciFlow.RiemannVariationTensorial
import MorganTianLib.Ch01.CovariantTensorExpansion

/-!
# Morgan--Tian Ch. 3: arbitrary-vector curvature variation

The coordinate producer in `RiemannVariationIntrinsic` is stated on chart
basis components.  This module performs the finite-dimensional basis lift to
fixed tangent vectors.  The right-hand side is kept in the intrinsic
`ricciFlowRiemannVariationIntrinsic` representation; no new certificate or
conditional wrapper is introduced.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Geodesic

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Chart coefficients and the basis component

The coefficient is the coordinate of a tangent vector in the chart frame. -/

noncomputable def curvatureChartTangentCoeff (alpha p : M)
    (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I p) : ℝ :=
  Riemannian.Geodesic.chartCoord (E := E) i
    (chartFiberCoord (I := I) alpha ⟨p, v⟩)

/-! The chart coefficient is a continuous linear coordinate on the tangent
fibre.  This small producer is the time-dependent-slot bridge used below. -/
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] in
theorem hasDerivAt_curvatureChartTangentCoeff
    (alpha p : M) {x : ℝ → TangentSpace I p} {t : ℝ}
    {x' : TangentSpace I p} (hx : HasDerivAt x x' t)
    (hp : p ∈ (chartAt H alpha).source)
    (i : Fin (Module.finrank ℝ E)) :
    HasDerivAt (fun s => curvatureChartTangentCoeff (I := I) alpha p i (x s))
      (curvatureChartTangentCoeff (I := I) alpha p i x') t := by
  letI : NormedAddCommGroup (TangentSpace I p) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I p) := inferInstanceAs (NormedSpace ℝ E)
  let hb' : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  let phi := (trivializationAt E (TangentSpace I) alpha).continuousLinearEquivAt ℝ p hb'
  have hphi : HasDerivAt (fun s => phi (x s)) (phi x') t :=
    phi.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hx
  have hcoord : HasDerivAt (fun s =>
      (Geodesic.chartCoordFunctional (E := E) i) (phi (x s)))
      ((Geodesic.chartCoordFunctional (E := E) i) (phi x')) t :=
    (Geodesic.chartCoordFunctional (E := E) i).hasFDerivAt.comp_hasDerivAt t hphi
  simpa only [curvatureChartTangentCoeff, chartFiberCoord_def, phi,
    Bundle.Trivialization.continuousLinearEquivAt_apply,
    Geodesic.chartCoordFunctional_apply, Function.comp_def] using hcoord

theorem hasDerivAt_curvatureFormAt_chartBasis_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha p : M)
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)
        (Tensor.chartBasisVecFiber (I := I) alpha l p))
      (ricciFlowRiemannVariationIntrinsic (g t)
        ![extendVector p (Tensor.chartBasisVecFiber (I := I) alpha i p),
          extendVector p (Tensor.chartBasisVecFiber (I := I) alpha j p),
          extendVector p (Tensor.chartBasisVecFiber (I := I) alpha k p),
          extendVector p (Tensor.chartBasisVecFiber (I := I) alpha l p)] p) t := by
  have hp' : p ∈ (extChartAt I alpha).source := by
    rw [extChartAt_source]
    exact hp
  have hy : extChartAt I alpha p ∈ (extChartAt I alpha).target :=
    (extChartAt I alpha).map_source hp'
  obtain ⟨X, hX, hderiv⟩ :=
    exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_intrinsic_of_isRicciFlowOn
      hflow alpha i j k l ht hy
  have hp_eq : (extChartAt I alpha).symm (extChartAt I alpha p) = p :=
    (extChartAt I alpha).left_inv hp'
  rw [hp_eq] at hX hderiv
  have hXval (a : Fin (Module.finrank ℝ E)) :
      X a p = Tensor.chartBasisVecFiber (I := I) alpha a p := by
    exact (hX a).self_of_nhds
  have hcoeff :
      (fun s => chartRiemannCoefOnE (I := I) (g s) alpha i j k l
        (extChartAt I alpha p)) =
      (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)
        (Tensor.chartBasisVecFiber (I := I) alpha l p)) := by
    funext s
    have h := chartRiemannCoefOnE_eq_curvatureFormAt_chartBasis
      (g s) alpha i j k l hy
    rw [hp_eq] at h
    exact h
  have hT := isCovariantTensor4_ricciFlowRiemannVariationIntrinsic (g t)
  have hframe :
      ricciFlowRiemannVariationIntrinsic (g t) ![X i, X j, X k, X l] p =
      ricciFlowRiemannVariationIntrinsic (g t)
        ![extendVector p (Tensor.chartBasisVecFiber (I := I) alpha i p),
          extendVector p (Tensor.chartBasisVecFiber (I := I) alpha j p),
          extendVector p (Tensor.chartBasisVecFiber (I := I) alpha k p),
          extendVector p (Tensor.chartBasisVecFiber (I := I) alpha l p)] p := by
    apply covariantTensor4_congr_apply
      (fun A B C D => ricciFlowRiemannVariationIntrinsic (g t) ![A, B, C, D]) hT
    · simp [hXval i]
    · simp [hXval j]
    · simp [hXval k]
    · simp [hXval l]
  rw [← hcoeff]
  exact hderiv.congr_deriv hframe

/-! ### The finite chart-basis lift -/

/-! The decomposition below is the fibrewise inverse-trivialization identity.
It is restated locally so this variation module does not acquire the large
curve-covariant-derivative dependency merely for a finite-dimensional linear
algebra fact. -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] in
theorem sum_chartCoord_smul_chartBasisVecFiber_for_curvatureVariation
    (x : M) {b : M} (hb : b ∈ (chartAt H x).source) (v : TangentSpace I b) :
    ∑ i, Riemannian.Geodesic.chartCoord (E := E) i
        (chartFiberCoord (I := I) x ⟨b, v⟩)
        • Tensor.chartBasisVecFiber (I := I) x i b = v := by
  have hb' : b ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  set φ := (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ b hb'
    with hφ
  apply φ.injective
  rw [map_sum]
  have hframe : ∀ i, φ (Tensor.chartBasisVecFiber (I := I) x i b) =
      (Module.finBasis ℝ E) i := by
    intro i
    rw [Bundle.Trivialization.continuousLinearEquivAt_apply]
    exact Tensor.trivializationAt_chartBasisVec_snd (I := I) x i hb'
  have hv : φ v = chartFiberCoord (I := I) x ⟨b, v⟩ := by
    rw [Bundle.Trivialization.continuousLinearEquivAt_apply]
    rfl
  simp only [map_smul, hframe, hv]
  exact (Module.finBasis ℝ E).sum_repr (chartFiberCoord (I := I) x ⟨b, v⟩)

theorem hasDerivAt_curvatureFormAt_chartExpansion_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha p : M)
    (x y z w : TangentSpace I p) {t : ℝ}
    (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p x y z w)
      (∑ i, curvatureChartTangentCoeff (I := I) alpha p i x *
        ∑ j, curvatureChartTangentCoeff (I := I) alpha p j y *
          ∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
            ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
              ricciFlowRiemannVariationIntrinsic (g t)
                ![extendVector p (Tensor.chartBasisVecFiber (I := I) alpha i p),
                  extendVector p (Tensor.chartBasisVecFiber (I := I) alpha j p),
                  extendVector p (Tensor.chartBasisVecFiber (I := I) alpha k p),
                  extendVector p (Tensor.chartBasisVecFiber (I := I) alpha l p)] p) t := by
  classical
  let e : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => Tensor.chartBasisVecFiber (I := I) alpha i p
  have hdecomp (v : TangentSpace I p) :
      ∑ i, curvatureChartTangentCoeff (I := I) alpha p i v • e i = v := by
    simpa only [curvatureChartTangentCoeff, e] using
      (sum_chartCoord_smul_chartBasisVecFiber_for_curvatureVariation
        (I := I) alpha hp v)
  have hcomponent (i j k l : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p
          (e i) (e j) (e k) (e l))
        (ricciFlowRiemannVariationIntrinsic (g t)
          ![extendVector p (e i), extendVector p (e j),
            extendVector p (e k), extendVector p (e l)] p) t := by
    simpa only [e] using
      (hasDerivAt_curvatureFormAt_chartBasis_of_isRicciFlowOn
        hflow alpha p i j k l ht hp)
  have hl (i j k : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
          curvatureFormAt (g s) (g s).leviCivitaConnection p
            (e i) (e j) (e k) (e l))
        (∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
          ricciFlowRiemannVariationIntrinsic (g t)
            ![extendVector p (e i), extendVector p (e j),
              extendVector p (e k), extendVector p (e l)] p) t := by
    exact HasDerivAt.fun_sum fun l _ =>
      (hcomponent i j k l).const_mul
        (curvatureChartTangentCoeff (I := I) alpha p l w)
  have hk (i j : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
          ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
            curvatureFormAt (g s) (g s).leviCivitaConnection p
              (e i) (e j) (e k) (e l))
        (∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
          ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
            ricciFlowRiemannVariationIntrinsic (g t)
              ![extendVector p (e i), extendVector p (e j),
                extendVector p (e k), extendVector p (e l)] p) t := by
    exact HasDerivAt.fun_sum fun k _ =>
      (hl i j k).const_mul
        (curvatureChartTangentCoeff (I := I) alpha p k z)
  have hj (i : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ j, curvatureChartTangentCoeff (I := I) alpha p j y *
          ∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
            ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
              curvatureFormAt (g s) (g s).leviCivitaConnection p
                (e i) (e j) (e k) (e l))
        (∑ j, curvatureChartTangentCoeff (I := I) alpha p j y *
          ∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
            ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
              ricciFlowRiemannVariationIntrinsic (g t)
                ![extendVector p (e i), extendVector p (e j),
                  extendVector p (e k), extendVector p (e l)] p) t := by
    exact HasDerivAt.fun_sum fun j _ =>
      (hk i j).const_mul
        (curvatureChartTangentCoeff (I := I) alpha p j y)
  have hi :
      HasDerivAt
        (fun s => ∑ i, curvatureChartTangentCoeff (I := I) alpha p i x *
          ∑ j, curvatureChartTangentCoeff (I := I) alpha p j y *
            ∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
              ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
                curvatureFormAt (g s) (g s).leviCivitaConnection p
                  (e i) (e j) (e k) (e l))
        (∑ i, curvatureChartTangentCoeff (I := I) alpha p i x *
          ∑ j, curvatureChartTangentCoeff (I := I) alpha p j y *
            ∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
              ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
                ricciFlowRiemannVariationIntrinsic (g t)
                  ![extendVector p (e i), extendVector p (e j),
                    extendVector p (e k), extendVector p (e l)] p) t := by
    exact HasDerivAt.fun_sum fun i _ =>
      (hj i).const_mul
        (curvatureChartTangentCoeff (I := I) alpha p i x)
  have heq :
      (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p x y z w) =
      (fun s => ∑ i, curvatureChartTangentCoeff (I := I) alpha p i x *
        ∑ j, curvatureChartTangentCoeff (I := I) alpha p j y *
          ∑ k, curvatureChartTangentCoeff (I := I) alpha p k z *
            ∑ l, curvatureChartTangentCoeff (I := I) alpha p l w *
              curvatureFormAt (g s) (g s).leviCivitaConnection p
                (e i) (e j) (e k) (e l)) := by
    funext s
    conv_lhs =>
      rw [← hdecomp x, ← hdecomp y, ← hdecomp z, ← hdecomp w]
    rw [curvatureFormAt_sum₄]
    simp_rw [Finset.mul_sum]
    ring_nf
  rw [heq]
  simpa only [e] using hi

/-- **Math.** Along a Ricci flow, the time derivative of the curvature tensor
on arbitrary fixed tangent vectors is the intrinsic Riemann variation tensor
evaluated on any chosen smooth extensions of those vectors. -/
theorem hasDerivAt_curvatureFormAt_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha p : M)
    (x y z w : TangentSpace I p) {t : ℝ}
    (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p x y z w)
      (ricciFlowRiemannVariationIntrinsic (g t)
        ![extendVector p x, extendVector p y, extendVector p z, extendVector p w] p) t := by
  classical
  have hderiv := hasDerivAt_curvatureFormAt_chartExpansion_of_isRicciFlowOn
    hflow alpha p x y z w ht hp
  apply hderiv.congr_deriv
  let e : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => Tensor.chartBasisVecFiber (I := I) alpha i p
  have hdecomp (v : TangentSpace I p) :
      ∑ i, curvatureChartTangentCoeff (I := I) alpha p i v • e i = v := by
    simpa only [curvatureChartTangentCoeff, e] using
      (sum_chartCoord_smul_chartBasisVecFiber_for_curvatureVariation
        (I := I) alpha hp v)
  have hexpand := covariantTensor4At_sum₄
    (fun A B C D q => ricciFlowRiemannVariationIntrinsic (g t) ![A, B, C, D] q)
    (isCovariantTensor4_ricciFlowRiemannVariationIntrinsic (g t)) p Finset.univ
    (fun i => curvatureChartTangentCoeff (I := I) alpha p i x)
    (fun i => curvatureChartTangentCoeff (I := I) alpha p i y)
    (fun i => curvatureChartTangentCoeff (I := I) alpha p i z)
    (fun i => curvatureChartTangentCoeff (I := I) alpha p i w) e
  simpa only [hdecomp, e] using hexpand.symm

/-! A local scalar product rule keeps the moving-slot proof below readable
without exposing an algebra-only API from this geometric module. -/
private theorem hasDerivAt_fiveProduct
    {f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ} {d₁ d₂ d₃ d₄ d₅ : ℝ} {t : ℝ}
    (h₁ : HasDerivAt f₁ d₁ t) (h₂ : HasDerivAt f₂ d₂ t)
    (h₃ : HasDerivAt f₃ d₃ t) (h₄ : HasDerivAt f₄ d₄ t)
    (h₅ : HasDerivAt f₅ d₅ t) :
    HasDerivAt (f₁ * f₂ * f₃ * f₄ * f₅)
      (d₁ * f₂ t * f₃ t * f₄ t * f₅ t
        + f₁ t * d₂ * f₃ t * f₄ t * f₅ t
        + f₁ t * f₂ t * d₃ * f₄ t * f₅ t
        + f₁ t * f₂ t * f₃ t * d₄ * f₅ t
        + f₁ t * f₂ t * f₃ t * f₄ t * d₅) t := by
  have h := ((((h₁.mul h₂).mul h₃).mul h₄).mul h₅)
  apply h.congr_deriv
  simp only [Pi.mul_apply]
  ring_nf

/-! **Math.** This is the moving-slot version of the fixed chart-basis
variation theorem.  The four curves live in one tangent fibre, so their
coordinate coefficients vary while the chart frame remains fixed. -/
theorem hasDerivAt_curvatureFormAt_along_curves_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha p : M)
    (x y z w : ℝ → TangentSpace I p)
    {x' y' z' w' : TangentSpace I p} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t)
    (hz : HasDerivAt z z' t) (hw : HasDerivAt w w' t)
    (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p
        (x s) (y s) (z s) (w s))
      (ricciFlowRiemannVariationIntrinsic (g t)
          ![extendVector p (x t), extendVector p (y t),
            extendVector p (z t), extendVector p (w t)] p
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            x' (y t) (z t) (w t)
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            (x t) y' (z t) (w t)
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            (x t) (y t) z' (w t)
        + curvatureFormAt (g t) (g t).leviCivitaConnection p
            (x t) (y t) (z t) w') t := by
  classical
  letI : NormedAddCommGroup (TangentSpace I p) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace I p) := inferInstanceAs (NormedSpace ℝ E)
  let e : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => Tensor.chartBasisVecFiber (I := I) alpha i p
  let cx : Fin (Module.finrank ℝ E) → ℝ → ℝ :=
    fun i s => curvatureChartTangentCoeff (I := I) alpha p i (x s)
  let cy : Fin (Module.finrank ℝ E) → ℝ → ℝ :=
    fun i s => curvatureChartTangentCoeff (I := I) alpha p i (y s)
  let cz : Fin (Module.finrank ℝ E) → ℝ → ℝ :=
    fun i s => curvatureChartTangentCoeff (I := I) alpha p i (z s)
  let cw : Fin (Module.finrank ℝ E) → ℝ → ℝ :=
    fun i s => curvatureChartTangentCoeff (I := I) alpha p i (w s)
  let Rijkl : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ → ℝ :=
    fun i j k l s => curvatureFormAt (g s) (g s).leviCivitaConnection p
      (e i) (e j) (e k) (e l)
  have hdecomp (v : TangentSpace I p) :
      ∑ i, curvatureChartTangentCoeff (I := I) alpha p i v • e i = v := by
    simpa only [e, curvatureChartTangentCoeff] using
      (sum_chartCoord_smul_chartBasisVecFiber_for_curvatureVariation
        (I := I) alpha hp v)
  have hcx (i : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun s => cx i s)
        (curvatureChartTangentCoeff (I := I) alpha p i x') t := by
    simpa only [cx] using hasDerivAt_curvatureChartTangentCoeff alpha p hx hp i
  have hcy (i : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun s => cy i s)
        (curvatureChartTangentCoeff (I := I) alpha p i y') t := by
    simpa only [cy] using hasDerivAt_curvatureChartTangentCoeff alpha p hy hp i
  have hcz (i : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun s => cz i s)
        (curvatureChartTangentCoeff (I := I) alpha p i z') t := by
    simpa only [cz] using hasDerivAt_curvatureChartTangentCoeff alpha p hz hp i
  have hcw (i : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun s => cw i s)
        (curvatureChartTangentCoeff (I := I) alpha p i w') t := by
    simpa only [cw] using hasDerivAt_curvatureChartTangentCoeff alpha p hw hp i
  have hR (i j k l : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (Rijkl i j k l)
        (ricciFlowRiemannVariationIntrinsic (g t)
          ![extendVector p (e i), extendVector p (e j),
            extendVector p (e k), extendVector p (e l)] p) t := by
    simpa only [Rijkl, e] using
      (hasDerivAt_curvatureFormAt_chartBasis_of_isRicciFlowOn
        hflow alpha p i j k l ht hp)
  let Dijkl : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j k l =>
      (curvatureChartTangentCoeff (I := I) alpha p i x') * cy j t * cz k t *
          cw l t * Rijkl i j k l t
        + cx i t * (curvatureChartTangentCoeff (I := I) alpha p j y') *
            cz k t * cw l t * Rijkl i j k l t
        + cx i t * cy j t * (curvatureChartTangentCoeff (I := I) alpha p k z') *
            cw l t * Rijkl i j k l t
        + cx i t * cy j t * cz k t *
            (curvatureChartTangentCoeff (I := I) alpha p l w') *
            Rijkl i j k l t
        + cx i t * cy j t * cz k t * cw l t *
            (ricciFlowRiemannVariationIntrinsic (g t)
              ![extendVector p (e i), extendVector p (e j),
                extendVector p (e k), extendVector p (e l)] p)
  have hterm (i j k l : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (cx i * cy j * cz k * cw l * Rijkl i j k l)
        (Dijkl i j k l) t := by
    simpa only [Dijkl] using
      (hasDerivAt_fiveProduct (hcx i) (hcy j) (hcz k) (hcw l) (hR i j k l))
  have hsum_l (i j k : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ l, (cx i * cy j * cz k * cw l * Rijkl i j k l) s)
        (∑ l, Dijkl i j k l) t := by
    exact HasDerivAt.fun_sum fun l _ => hterm i j k l
  have hsum_k (i j : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ k, ∑ l, (cx i * cy j * cz k * cw l * Rijkl i j k l) s)
        (∑ k, ∑ l, Dijkl i j k l) t := by
    exact HasDerivAt.fun_sum fun k _ => hsum_l i j k
  have hsum_j (i : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ j, ∑ k, ∑ l,
          (cx i * cy j * cz k * cw l * Rijkl i j k l) s)
        (∑ j, ∑ k, ∑ l, Dijkl i j k l) t := by
    exact HasDerivAt.fun_sum fun j _ => hsum_k i j
  have hsum_i :
      HasDerivAt
        (fun s => ∑ i, ∑ j, ∑ k, ∑ l,
          (cx i * cy j * cz k * cw l * Rijkl i j k l) s)
        (∑ i, ∑ j, ∑ k, ∑ l, Dijkl i j k l) t := by
    exact HasDerivAt.fun_sum fun i _ => hsum_j i
  have heq :
      (fun s => curvatureFormAt (g s) (g s).leviCivitaConnection p
        (x s) (y s) (z s) (w s)) =
      (fun s => ∑ i, ∑ j, ∑ k, ∑ l,
        (cx i * cy j * cz k * cw l * Rijkl i j k l) s) := by
    funext s
    conv_lhs =>
      rw [← hdecomp (x s), ← hdecomp (y s), ← hdecomp (z s), ← hdecomp (w s)]
    rw [curvatureFormAt_sum₄]
    simp only [Rijkl, cx, cy, cz, cw, Pi.mul_apply]
  rw [heq]
  apply hsum_i.congr_deriv
  have hVexpand :
      ricciFlowRiemannVariationIntrinsic (g t)
          ![extendVector p (x t), extendVector p (y t),
            extendVector p (z t), extendVector p (w t)] p =
        ∑ i, ∑ j, ∑ k, ∑ l, cx i t * cy j t * cz k t * cw l t *
          ricciFlowRiemannVariationIntrinsic (g t)
            ![extendVector p (e i), extendVector p (e j),
              extendVector p (e k), extendVector p (e l)] p := by
    have hexpand := covariantTensor4At_sum₄
      (fun A B C D q => ricciFlowRiemannVariationIntrinsic (g t) ![A, B, C, D] q)
      (isCovariantTensor4_ricciFlowRiemannVariationIntrinsic (g t)) p
      Finset.univ (fun i => cx i t) (fun j => cy j t) (fun k => cz k t)
      (fun l => cw l t) e
    convert hexpand using 1 <;>
      simp only [hdecomp, e, cx, cy, cz, cw, Finset.mul_sum]
    all_goals ring_nf
  have hRx :
      curvatureFormAt (g t) (g t).leviCivitaConnection p x' (y t) (z t) (w t) =
        ∑ i, ∑ j, ∑ k, ∑ l, curvatureChartTangentCoeff (I := I) alpha p i x' *
          curvatureChartTangentCoeff (I := I) alpha p j (y t) *
          curvatureChartTangentCoeff (I := I) alpha p k (z t) *
          curvatureChartTangentCoeff (I := I) alpha p l (w t) * Rijkl i j k l t := by
    have hexpand := curvatureFormAt_sum₄ (g t) (g t).leviCivitaConnection p
      Finset.univ
      (fun i => curvatureChartTangentCoeff (I := I) alpha p i x')
      (fun j => curvatureChartTangentCoeff (I := I) alpha p j (y t))
      (fun k => curvatureChartTangentCoeff (I := I) alpha p k (z t))
      (fun l => curvatureChartTangentCoeff (I := I) alpha p l (w t)) e
    simpa only [hdecomp, e, Rijkl] using hexpand
  have hRy :
      curvatureFormAt (g t) (g t).leviCivitaConnection p (x t) y' (z t) (w t) =
        ∑ i, ∑ j, ∑ k, ∑ l, cx i t *
          curvatureChartTangentCoeff (I := I) alpha p j y' *
          cz k t * cw l t * Rijkl i j k l t := by
    have hexpand := curvatureFormAt_sum₄ (g t) (g t).leviCivitaConnection p
      Finset.univ (fun i => cx i t)
      (fun j => curvatureChartTangentCoeff (I := I) alpha p j y')
      (fun k => cz k t) (fun l => cw l t) e
    simpa only [hdecomp, e, cx, cz, cw, Rijkl] using hexpand
  have hRz :
      curvatureFormAt (g t) (g t).leviCivitaConnection p (x t) (y t) z' (w t) =
        ∑ i, ∑ j, ∑ k, ∑ l, cx i t * cy j t *
          curvatureChartTangentCoeff (I := I) alpha p k z' * cw l t * Rijkl i j k l t := by
    have hexpand := curvatureFormAt_sum₄ (g t) (g t).leviCivitaConnection p
      Finset.univ (fun i => cx i t) (fun j => cy j t)
      (fun k => curvatureChartTangentCoeff (I := I) alpha p k z')
      (fun l => cw l t) e
    simpa only [hdecomp, e, cx, cy, cw, Rijkl] using hexpand
  have hRw :
      curvatureFormAt (g t) (g t).leviCivitaConnection p (x t) (y t) (z t) w' =
        ∑ i, ∑ j, ∑ k, ∑ l, cx i t * cy j t * cz k t *
          curvatureChartTangentCoeff (I := I) alpha p l w' * Rijkl i j k l t := by
    have hexpand := curvatureFormAt_sum₄ (g t) (g t).leviCivitaConnection p
      Finset.univ (fun i => cx i t) (fun j => cy j t) (fun k => cz k t)
      (fun l => curvatureChartTangentCoeff (I := I) alpha p l w') e
    simpa only [hdecomp, e, cx, cy, cz, Rijkl] using hexpand
  simp only [Dijkl, Finset.sum_add_distrib]
  rw [← hVexpand, ← hRx, ← hRy, ← hRz, ← hRw]
  ring_nf

end MorganTianLib

end

#print axioms MorganTianLib.hasDerivAt_curvatureFormAt_chartBasis_of_isRicciFlowOn
#print axioms MorganTianLib.hasDerivAt_curvatureFormAt_chartExpansion_of_isRicciFlowOn
#print axioms MorganTianLib.hasDerivAt_curvatureFormAt_of_isRicciFlowOn
#print axioms MorganTianLib.hasDerivAt_curvatureChartTangentCoeff
#print axioms MorganTianLib.hasDerivAt_curvatureFormAt_along_curves_of_isRicciFlowOn
