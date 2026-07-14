import OpenGALib.Riemannian.Connection.ChartCurvatureForm
import OpenGALib.Riemannian.Manifold.DoCarmoCh8HyperbolicChristoffel
import OpenGALib.Riemannian.Manifold.DoCarmoCh6ConstantCurvature

/-!
# Hyperbolic space `Hⁿ` has constant sectional curvature `-1` (do Carmo Ch. 8 §3)

`prop:dc-ch8-3-const-curv`.
-/

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Hyperbolic

open Riemannian Riemannian.Tensor

variable {n : ℕ} [NeZero n]

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- **Eng.** `Hⁿ` is a locally compact space: an open subset of the (proper,
hence locally compact) Euclidean space. -/
instance instLocallyCompactUpperHalfSpace (e : Fin n) :
    LocallyCompactSpace ↥(upperHalfSpace e) :=
  (upperHalfSpace e).isOpen.locallyCompactSpace

/-- **Eng.** `Hⁿ` is σ-compact: locally compact and second countable. This
supplies the hypothesis of the chart-frame curvature machinery. -/
instance instSigmaCompactUpperHalfSpace (e : Fin n) :
    SigmaCompactSpace ↥(upperHalfSpace e) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

/-! ## Constant-Gram contraction facts -/

/-- **Math.** The constant abstract-basis Gram matrix is symmetric. -/
theorem finBasisGram_symm (a b : Fin (Module.finrank ℝ E)) :
    finBasisGram (n := n) a b = finBasisGram (n := n) b a := by
  rw [finBasisGram, finBasisGram, real_inner_comm]

/-- **Math.** `cₐ = (finBasisₐ)ₑ`, the `e`-th coordinate of the `a`-th abstract
basis vector — do Carmo's `fₐ·xₑ`. -/
def finBasisCoord (e : Fin n) (a : Fin (Module.finrank ℝ E)) : ℝ :=
  ((Module.finBasis ℝ E) a) e

/-- **Math.** Abbreviation `D m = ∑ l Bᵐˡ cₗ`, the constant coefficient of `Bᵢⱼ`
in the closed-form Christoffel symbol (`cₗ = (finBasisₗ)ₑ`). -/
def Dvec (e : Fin n) (m : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ l, (finBasisGramMatrix (n := n))⁻¹ m l * ((Module.finBasis ℝ E) l e)

/-- **Math.** The constant Christoffel coefficient `Kᵏᵢⱼ = −cᵢδᵏⱼ − cⱼδᵏᵢ + DᵏBᵢⱼ`:
the hyperbolic chart Christoffel symbol factors as `Γᵏᵢⱼ(y) = yₑ⁻¹·Kᵏᵢⱼ`. -/
def Kcoef (e : Fin n) (a b m : Fin (Module.finrank ℝ E)) : ℝ :=
  -finBasisCoord (n := n) e a * (if m = b then (1 : ℝ) else 0)
    - finBasisCoord (n := n) e b * (if m = a then (1 : ℝ) else 0)
    + Dvec (n := n) e m * finBasisGram (n := n) a b

/-- **Math.** Inverse-Gram/Gram contraction `∑ₛ Dₛ B_{sx} = cₓ` (= `∑ₛ Bˢˡcₗ B_{sx}`),
the "lowered `D`" identity, using `B*B⁻¹ = 1` and `B` symmetric. -/
theorem Dvec_gram_contract (e : Fin n)
    (hunit : IsUnit (finBasisGramMatrix (n := n)).det)
    (x : Fin (Module.finrank ℝ E)) :
    ∑ s, Dvec (n := n) e s * finBasisGram (n := n) s x = ((Module.finBasis ℝ E) x) e := by
  classical
  have hstep : ∀ l : Fin (Module.finrank ℝ E),
      ∑ s, (finBasisGramMatrix (n := n))⁻¹ s l * finBasisGram (n := n) s x
        = (if x = l then (1 : ℝ) else 0) := by
    intro l
    calc ∑ s, (finBasisGramMatrix (n := n))⁻¹ s l * finBasisGram (n := n) s x
        = ∑ s, finBasisGramMatrix (n := n) x s * (finBasisGramMatrix (n := n))⁻¹ s l := by
          apply Finset.sum_congr rfl; intro s _
          rw [finBasisGram_symm s x]
          show (finBasisGramMatrix (n := n))⁻¹ s l * finBasisGramMatrix (n := n) x s = _
          ring
      _ = (finBasisGramMatrix (n := n) * (finBasisGramMatrix (n := n))⁻¹) x l := (Matrix.mul_apply).symm
      _ = (1 : Matrix _ _ ℝ) x l := by rw [Matrix.mul_nonsing_inv _ hunit]
      _ = if x = l then 1 else 0 := by rw [Matrix.one_apply]
  calc ∑ s, Dvec (n := n) e s * finBasisGram (n := n) s x
      = ∑ s, ∑ l, ((finBasisGramMatrix (n := n))⁻¹ s l * ((Module.finBasis ℝ E) l e))
          * finBasisGram (n := n) s x := by
        apply Finset.sum_congr rfl; intro s _; rw [Dvec, Finset.sum_mul]
    _ = ∑ l, ∑ s, ((finBasisGramMatrix (n := n))⁻¹ s l * ((Module.finBasis ℝ E) l e))
          * finBasisGram (n := n) s x := Finset.sum_comm
    _ = ∑ l, ((Module.finBasis ℝ E) l e)
          * ∑ s, (finBasisGramMatrix (n := n))⁻¹ s l * finBasisGram (n := n) s x := by
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    _ = ∑ l, ((Module.finBasis ℝ E) l e) * (if x = l then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro l _; rw [hstep l]
    _ = ((Module.finBasis ℝ E) x) e := by simp

/-- **Math.** The normalization `∑ₛ Dₛ cₛ = 1` (= `∑ₛₗ Bˢˡ cₗ cₛ = 1`), the single
nontrivial conformal input `|dσ|²_{g₀} = 1` of `prop:dc-ch8-3-const-curv`,
repackaged from `finBasis_inv_gram_coord`. -/
theorem Dvec_coord_contract (e : Fin n)
    (hunit : IsUnit (finBasisGramMatrix (n := n)).det) :
    ∑ s, Dvec (n := n) e s * ((Module.finBasis ℝ E) s e) = 1 := by
  rw [← finBasis_inv_gram_coord (n := n) e hunit]
  apply Finset.sum_congr rfl; intro s _
  rw [Dvec, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro l _; ring

/-! ## The finite-sum curvature contraction (pure algebra) -/

/-- **Math.** The pure finite-sum identity behind `prop:dc-ch8-3-const-curv`:
contracting the coordinate curvature coefficient
`R^m_{ijk} = ∂ⱼΓ^m_{ik} − ∂ᵢΓ^m_{jk} + Σₛ(Γ^s_{ik}Γ^m_{js} − Γ^s_{jk}Γ^m_{is})`
(with `Γ^m_{ab} = t⁻¹·Kc a b m`) against the chart Gram matrix `B_{ml}` and
stripping the conformal factors yields
`Σₘ R^m_{ijk}·B_{ml} = −(B_{ik}B_{jl} − B_{jk}B_{il})`. The `Kc` are the constant
Christoffel coefficients `−cₐδ^m_b − c_bδ^m_a + DₘB_{ab}`, `B` the constant Gram,
`D` its inverse contracted with `c`, subject to `∑ₛDₛB_{sx}=cₓ` and `∑ₛDₛcₛ=1`.
This is do Carmo's conformal cancellation `T = ½φg₀`, isolated as linear algebra. -/
theorem const_curv_frame_algebra {N : ℕ}
    (c : Fin N → ℝ) (B : Fin N → Fin N → ℝ) (D : Fin N → ℝ)
    (Kc : Fin N → Fin N → Fin N → ℝ)
    (hKc : ∀ a b m, Kc a b m
        = -c a * (if m = b then (1 : ℝ) else 0) - c b * (if m = a then (1 : ℝ) else 0)
          + D m * B a b)
    (Bsymm : ∀ a b, B a b = B b a)
    (hDB : ∀ x, ∑ s, D s * B s x = c x)
    (hDc : ∑ s, D s * c s = 1)
    (i j k l : Fin N) :
    ∑ m, (-c j * Kc i k m + c i * Kc j k m
          + ∑ s, (Kc i k s * Kc j s m - Kc j k s * Kc i s m)) * B m l
      = -(B i k * B j l - B j k * B i l) := by
  classical
  -- Kronecker sum helper
  have hite : ∀ (b : Fin N) (f : Fin N → ℝ),
      ∑ m, (if m = b then (1 : ℝ) else 0) * f m = f b := by
    intro b f
    rw [show (∑ m, (if m = b then (1 : ℝ) else 0) * f m)
        = ∑ m, (if m = b then f m else 0) from
      Finset.sum_congr rfl (fun m _ => by by_cases h : m = b <;> simp [h])]
    simp
  -- general contraction of a `Kc a b ·` row against an arbitrary weight `f`
  have hLc2 : ∀ (a b : Fin N) (f : Fin N → ℝ),
      ∑ s, Kc a b s * f s = -c a * f b - c b * f a + B a b * ∑ s, D s * f s := by
    intro a b f
    rw [show (∑ s, Kc a b s * f s)
        = (-c a) * ∑ s, (if s = b then (1 : ℝ) else 0) * f s
          + (-c b) * ∑ s, (if s = a then (1 : ℝ) else 0) * f s
          + B a b * ∑ s, D s * f s from by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun s _ => by rw [hKc]; ring)]
    rw [hite b f, hite a f]; ring
  -- lowered Christoffel row `∑ Kc a b m · B m l`
  have hMrow : ∀ a b : Fin N,
      ∑ m, Kc a b m * B m l = -c a * B b l - c b * B a l + c l * B a b := by
    intro a b
    rw [hLc2 a b fun m => B m l, hDB l]; ring
  -- the `D`-contraction of a lowered Christoffel row equals `-B q l`
  have hDL : ∀ q : Fin N,
      ∑ s, D s * (-c q * B s l - c s * B q l + c l * B q s) = -B q l := by
    intro q
    calc ∑ s, D s * (-c q * B s l - c s * B q l + c l * B q s)
        = (-c q) * (∑ s, D s * B s l) + (-(B q l)) * (∑ s, D s * c s)
            + c l * (∑ s, D s * B s q) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun s _ => by rw [Bsymm q s]; ring)
      _ = -B q l := by rw [hDB l, hDc, hDB q]; ring
  -- split the outer sum into two linear pieces and the quadratic piece
  rw [show (∑ m, (-c j * Kc i k m + c i * Kc j k m
        + ∑ s, (Kc i k s * Kc j s m - Kc j k s * Kc i s m)) * B m l)
      = (-c j) * (∑ m, Kc i k m * B m l) + c i * (∑ m, Kc j k m * B m l)
        + ∑ m, (∑ s, (Kc i k s * Kc j s m - Kc j k s * Kc i s m)) * B m l from by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)]
  rw [hMrow i k, hMrow j k]
  -- swap the quadratic double sum and contract the inner `m`-sum
  rw [show (∑ m, (∑ s, (Kc i k s * Kc j s m - Kc j k s * Kc i s m)) * B m l)
      = ∑ s, (Kc i k s * (∑ m, Kc j s m * B m l) - Kc j k s * (∑ m, Kc i s m * B m l)) from by
      rw [show (∑ m, (∑ s, (Kc i k s * Kc j s m - Kc j k s * Kc i s m)) * B m l)
          = ∑ m, ∑ s, (Kc i k s * Kc j s m - Kc j k s * Kc i s m) * B m l from
        Finset.sum_congr rfl (fun m _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [show (∑ m, (Kc i k s * Kc j s m - Kc j k s * Kc i s m) * B m l)
          = ∑ m, (Kc i k s * (Kc j s m * B m l) - Kc j k s * (Kc i s m * B m l)) from
        Finset.sum_congr rfl (fun m _ => by ring)]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]]
  simp only [hMrow]
  rw [Finset.sum_sub_distrib,
    hLc2 i k fun s => -c j * B s l - c s * B j l + c l * B j s,
    hLc2 j k fun s => -c i * B s l - c s * B i l + c l * B i s,
    hDL j, hDL i, Bsymm j i]
  ring

/-! ## The chart-frame curvature `(0,4)` value of the hyperbolic metric -/

/-- **Math.** do Carmo Ch. 8 §3, curvature of `Hⁿ` (constant `-1`), chart-frame
`(0,4)` value. In the abstract chart frame `∂ₐ = finBasisₐ` at `p ∈ Hⁿ`, the
pointwise curvature form of the Levi-Civita connection is
`⟨R(∂ᵢ,∂ⱼ)∂ₖ,∂ₗ⟩_g = −(GᵢₖGⱼₗ − GⱼₖGᵢₗ)`, `G` the hyperbolic chart Gram matrix —
the coordinate curvature `R_{ijkl}` of the conformal metric `gᵢⱼ = δᵢⱼ/xₑ²`. -/
theorem hyperbolic_curvatureFormAt_frame (e : Fin n) (p : ↥(upperHalfSpace e))
    (i j k l : Fin (Module.finrank ℝ E)) :
    (hyperbolicMetric e).leviCivitaConnection.curvatureFormAt (hyperbolicMetric e) p
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)
        ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l)
      = -((hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) k)
            * (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) l)
          - (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) k)
            * (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) l)) := by
  have hframe := leviCivita_curvatureFormAt_chartFrame (hyperbolicMetric e) p i j k l
  rw [hyperbolic_chartBasisVecFiber e p p i, hyperbolic_chartBasisVecFiber e p p j,
    hyperbolic_chartBasisVecFiber e p p k, hyperbolic_chartBasisVecFiber e p p l] at hframe
  rw [hframe]
  have hymem : extChartAt (𝓡 n) p p ∈ (extChartAt (𝓡 n) p).target := mem_extChartAt_target p
  have hunit := finBasisGramMatrix_det_isUnit (n := n) e p
  have htne : (extChartAt (𝓡 n) p p) e ≠ 0 := ne_of_gt (coord_pos e p)
  -- closed-form Christoffel symbol `Γᵏᵢⱼ = yₑ⁻¹·Kᵏᵢⱼ` at the point
  have hΓ : ∀ a b m, chartChristoffel (hyperbolicMetric e) p a b m (extChartAt (𝓡 n) p p)
      = ((extChartAt (𝓡 n) p p) e)⁻¹ * Kcoef (n := n) e a b m := by
    intro a b m
    rw [hyperbolic_chartChristoffel e p a b m hymem]
    simp only [Kcoef, finBasisCoord, Dvec]
    ring
  -- closed-form derivative `∂ₘ′Γᵏᵢⱼ = Kᵏᵢⱼ·(−cₘ′·yₑ⁻²)`
  have hdΓ : ∀ a b m m', partialDeriv m'
      (chartChristoffel (hyperbolicMetric e) p a b m) (extChartAt (𝓡 n) p p)
      = Kcoef (n := n) e a b m
          * (-(finBasisCoord (n := n) e m') * ((extChartAt (𝓡 n) p p) e ^ 2)⁻¹) := by
    intro a b m m'
    rw [hyperbolic_partialDeriv_chartChristoffel e p a b m m' hymem]
    simp only [Kcoef, finBasisCoord, Dvec]
  -- chart Gram at the point: `⟨∂ₘ,∂ₗ⟩_g = yₑ⁻²·Bₘₗ`
  have hGm : ∀ m, (hyperbolicMetric e).metricInner p
      (chartBasisVecFiber p m p) ((Module.finBasis ℝ E) l)
      = ((extChartAt (𝓡 n) p p) e ^ 2)⁻¹ * finBasisGram (n := n) m l := by
    intro m
    rw [hyperbolic_chartBasisVecFiber e p p m, hyperbolicMetric_apply]
    rfl
  have hGab : ∀ a b, (hyperbolicMetric e).metricInner p
      ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) b)
      = ((extChartAt (𝓡 n) p p) e ^ 2)⁻¹ * finBasisGram (n := n) a b := by
    intro a b
    rw [hyperbolicMetric_apply]
    rfl
  simp only [hdΓ, hΓ, hGm, hGab]
  set t := (extChartAt (𝓡 n) p p) e with htdef
  set u := (t ^ 2)⁻¹ with hudef
  have hu2 : t⁻¹ * t⁻¹ = u := by rw [hudef, pow_two, mul_inv_rev]
  have hfac : ∀ m, ∑ s, ((t⁻¹ * Kcoef (n := n) e i k s) * (t⁻¹ * Kcoef (n := n) e j s m)
        - (t⁻¹ * Kcoef (n := n) e j k s) * (t⁻¹ * Kcoef (n := n) e i s m))
      = u * ∑ s, (Kcoef (n := n) e i k s * Kcoef (n := n) e j s m
          - Kcoef (n := n) e j k s * Kcoef (n := n) e i s m) := by
    intro m
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [← hu2]; ring
  have key := const_curv_frame_algebra (finBasisCoord (n := n) e) (finBasisGram (n := n))
    (Dvec (n := n) e) (Kcoef (n := n) e) (fun a b m => rfl) (finBasisGram_symm (n := n))
    (Dvec_gram_contract e hunit) (Dvec_coord_contract e hunit) i j k l
  trans (u ^ 2 * ∑ m, (-finBasisCoord (n := n) e j * Kcoef (n := n) e i k m
        + finBasisCoord (n := n) e i * Kcoef (n := n) e j k m
        + ∑ s, (Kcoef (n := n) e i k s * Kcoef (n := n) e j s m
            - Kcoef (n := n) e j k s * Kcoef (n := n) e i s m)) * finBasisGram (n := n) m l)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [hfac m]; ring
  · rw [key]; ring

/-! ## `Hⁿ` has constant sectional curvature `-1` -/

/-- **Math.** do Carmo Ch. 8 §3: the pointwise curvature `(0,4)` form of `Hⁿ` is
`−1` times the standard curvature form: `⟨R(x,y)z,t⟩_g = −(⟨x,z⟩_g⟨y,t⟩_g −
⟨y,z⟩_g⟨x,t⟩_g)` on all of `T_pHⁿ` (not just the chart frame), by
`IsAlgCurvatureForm.ext_basis` on `finBasis` from the chart-frame value. -/
theorem hyperbolic_curvatureFormAt_eq (e : Fin n) (p : ↥(upperHalfSpace e))
    (x y z t : TangentSpace 𝓘(ℝ, E) p) :
    (hyperbolicMetric e).leviCivitaConnection.curvatureFormAt (hyperbolicMetric e) p x y z t
      = -((hyperbolicMetric e).metricInner p x z * (hyperbolicMetric e).metricInner p y t
          - (hyperbolicMetric e).metricInner p y z * (hyperbolicMetric e).metricInner p x t) := by
  letI : Bundle.RiemannianBundle (fun q : ↥(upperHalfSpace e) => TangentSpace 𝓘(ℝ, E) q) :=
    ⟨(hyperbolicMetric e).toRiemannianMetric⟩
  have hLC : (hyperbolicMetric e).leviCivitaConnection.IsLeviCivita (hyperbolicMetric e) :=
    (hyperbolicMetric e).leviCivitaConnection.isLeviCivita_of_koszulDual (hyperbolicMetric e)
      (fun X Y W r => (hyperbolicMetric e).koszulDualSection_dual X Y W r)
  have hinner : ∀ v w : TangentSpace 𝓘(ℝ, E) p,
      @inner ℝ (TangentSpace 𝓘(ℝ, E) p) _ v w = (hyperbolicMetric e).metricInner p v w :=
    fun _ _ => rfl
  have hB := (hyperbolicMetric e).leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt
    (hyperbolicMetric e) hLC p
  have hB' : IsAlgCurvatureForm
      (fun a b c d : TangentSpace 𝓘(ℝ, E) p => -1 * stdCurvForm a b c d) :=
    isAlgCurvatureForm_stdCurvForm.smul (-1)
  have hext := hB.ext_basis hB' (Module.finBasis ℝ E) ?_
  · rw [hext x y z t]
    simp only [stdCurvForm, hinner]
    ring
  · intro a b c d
    refine (hyperbolic_curvatureFormAt_frame e p a b c d).trans ?_
    show -((hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) c)
            * (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) b) ((Module.finBasis ℝ E) d)
          - (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) b) ((Module.finBasis ℝ E) c)
            * (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) d))
        = -1 * ((hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) c)
            * (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) b) ((Module.finBasis ℝ E) d)
          - (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) b) ((Module.finBasis ℝ E) c)
            * (hyperbolicMetric e).metricInner p ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) d))
    ring

/-- **Math.** do Carmo Ch. 8 §3, `prop:dc-ch8-3-const-curv` (field-level form):
the Levi-Civita connection of hyperbolic space `Hⁿ` has **constant curvature `−1`**
— `⟨R(X,Y)Z,W⟩ = −(⟨X,Z⟩⟨Y,W⟩ − ⟨Y,Z⟩⟨X,W⟩)` at every point and for all fields. -/
theorem hyperbolic_isConstantCurvature (e : Fin n) :
    (hyperbolicMetric e).leviCivitaConnection.IsConstantCurvature (hyperbolicMetric e) (-1) := by
  intro X Y Z W p
  have h1 : (hyperbolicMetric e).leviCivitaConnection.curvatureFormAt (hyperbolicMetric e) p
      (X p) (Y p) (Z p) (W p)
      = (hyperbolicMetric e).metricInner p
          ((hyperbolicMetric e).leviCivitaConnection.curvature X Y Z p) (W p) :=
    (hyperbolicMetric e).leviCivitaConnection.curvatureFormAt_eq (hyperbolicMetric e) p
      (X := X) (Y := Y) (Z := Z) (T := W) rfl rfl rfl rfl
  rw [← h1, hyperbolic_curvatureFormAt_eq e p]
  ring

/-- **Math.** do Carmo Ch. 8 §3, `prop:dc-ch8-3-const-curv`: for every point of
`Hⁿ` and every genuine `2`-plane `σ = span{x,y} ⊆ T_pHⁿ` (`x, y` linearly
independent), the **sectional curvature** `K(p,σ) = −1`. -/
theorem hyperbolicMetric_sectionalCurvature_eq_neg_one (e : Fin n) (p : ↥(upperHalfSpace e))
    (x y : TangentSpace 𝓘(ℝ, E) p) (hxy : LinearIndependent ℝ ![x, y]) :
    letI : Bundle.RiemannianBundle (fun q : ↥(upperHalfSpace e) => TangentSpace 𝓘(ℝ, E) q) :=
      ⟨(hyperbolicMetric e).toRiemannianMetric⟩
    sectionalCurvature
        ((hyperbolicMetric e).leviCivitaConnection.curvatureFormAt (hyperbolicMetric e) p) x y
      = -1 := by
  letI : Bundle.RiemannianBundle (fun q : ↥(upperHalfSpace e) => TangentSpace 𝓘(ℝ, E) q) :=
    ⟨(hyperbolicMetric e).toRiemannianMetric⟩
  have hwpos : 0 < wedgeSq x y := (wedgeSq_pos_iff_linearIndependent x y).mpr hxy
  have hwne : wedgeSq x y ≠ 0 := ne_of_gt hwpos
  have hsymm : (hyperbolicMetric e).metricInner p y x = (hyperbolicMetric e).metricInner p x y :=
    (hyperbolicMetric e).symm p y x
  rw [sectionalCurvature, hyperbolic_curvatureFormAt_eq e p x y x y]
  have hnum : (hyperbolicMetric e).metricInner p x x * (hyperbolicMetric e).metricInner p y y
      - (hyperbolicMetric e).metricInner p y x * (hyperbolicMetric e).metricInner p x y
      = wedgeSq x y := by rw [hsymm]; rfl
  rw [hnum, neg_div, div_self hwne]

end Riemannian.Hyperbolic
