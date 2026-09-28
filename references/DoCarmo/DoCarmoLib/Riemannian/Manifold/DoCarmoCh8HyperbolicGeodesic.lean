import DoCarmoLib.Riemannian.Manifold.DoCarmoCh8HyperbolicChristoffel
import DoCarmoLib.Riemannian.Geodesic.Equation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Geodesics of hyperbolic space `Hⁿ` (do Carmo Ch. 8 §3, Prop. 3.1)

Working from the closed-form chart Christoffel symbols of the hyperbolic metric
(`hyperbolic_chartChristoffel`), this file establishes the **basis-independent
`E`-valued Christoffel contraction**

`Γ(v, w)(y) = (yₑ)⁻¹ · ( -(vₑ)·w - (wₑ)·v + ⟪v,w⟫·1ₑ )`,

do Carmo's `Γᵏᵢⱼ = -δⱼₖfᵢ - δₖᵢfⱼ + δᵢⱼfₖ` contracted against `v, w` (`1ₑ` is the
distinguished unit vector `EuclideanSpace.single e 1`). From this clean form the
geodesic equation `u'' + Γ(u', u') = 0` of `Hⁿ` reads

`u'' + (uₑ)⁻¹·( -2 (u'ₑ)·u' + ⟪u',u'⟫·1ₑ ) = 0`,

and the two families of do Carmo Prop. 3.1 — the vertical lines and the
semicircles perpendicular to `∂Hⁿ = {xₑ = 0}` — satisfy it, hence are geodesics.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §3, Prop. 3.1.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix RealInnerProductSpace

namespace Riemannian.Hyperbolic

open Riemannian Riemannian.Geodesic

variable {n : ℕ} [NeZero n]

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Coordinate helpers relating the abstract basis to Euclidean coordinates -/

/-- **Math.** The `e`-th Euclidean coordinate of `v` is the abstract-basis-weighted
sum of the coordinates of the basis vectors: `vₑ = ∑ᵢ (repr v)ᵢ · (finBasisᵢ)ₑ`. -/
theorem coord_eq_sum_repr (e : Fin n) (v : E) :
    v e = ∑ i, (Module.finBasis ℝ E).repr v i * (((Module.finBasis ℝ E) i) e) := by
  have hsum : ∑ i, (Module.finBasis ℝ E).repr v i • (Module.finBasis ℝ E) i = v :=
    (Module.finBasis ℝ E).sum_repr v
  have hproj : (EuclideanSpace.proj (𝕜 := ℝ) e) v
      = ∑ i, (Module.finBasis ℝ E).repr v i * (((Module.finBasis ℝ E) i) e) := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
    rfl
  exact hproj

/-- **Math.** The Euclidean inner product expressed via the abstract-basis Gram
matrix: `⟪v,w⟫ = ∑ᵢⱼ Bᵢⱼ (repr v)ᵢ (repr w)ⱼ`. -/
theorem inner_eq_sum_gram (v w : E) :
    (⟪v, w⟫ : ℝ) = ∑ i, ∑ j, finBasisGram (n := n) i j
        * (Module.finBasis ℝ E).repr v i * (Module.finBasis ℝ E).repr w j := by
  have hv : ∑ i, (Module.finBasis ℝ E).repr v i • (Module.finBasis ℝ E) i = v :=
    (Module.finBasis ℝ E).sum_repr v
  have hw : ∑ j, (Module.finBasis ℝ E).repr w j • (Module.finBasis ℝ E) j = w :=
    (Module.finBasis ℝ E).sum_repr w
  conv_lhs => rw [← hv, ← hw]
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_smul_left, real_inner_smul_right, finBasisGram]
  ring

/-- **Math.** The `B⁻¹`-contraction of the coordinate vector `cₖ = (finBasisₖ)ₑ`
reconstructs the abstract-basis representation of the distinguished unit vector
`1ₑ = EuclideanSpace.single e 1`: `∑ₗ Bᵏˡ cₗ = (repr 1ₑ)ₖ`. -/
theorem invGram_coord_eq_repr_single (e : Fin n)
    (hunit : IsUnit (finBasisGramMatrix (n := n)).det) (k : Fin (Module.finrank ℝ E)) :
    ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * (((Module.finBasis ℝ E) l) e)
      = (Module.finBasis ℝ E).repr (EuclideanSpace.single e (1 : ℝ)) k := by
  classical
  set b := Module.finBasis ℝ E with hb
  set w : E := EuclideanSpace.single e (1 : ℝ) with hw
  have hcoord : ∀ x : E, @inner ℝ E _ x w = x e := by
    intro x
    have h1 : @inner ℝ E _ x w = (1 : ℝ) * (starRingEnd ℝ) (x e) := by
      rw [hw]; exact EuclideanSpace.inner_single_right e 1 x
    rw [h1]; simp
  have hrepr : ∑ i, (b.repr w i) • b i = w := b.sum_repr w
  -- `cₗ = (b l)ₑ = ∑ₘ B_{lm} (repr w)ₘ`
  have hcB : ∀ l, (b l) e = ∑ m, finBasisGram (n := n) l m * (b.repr w m) := by
    intro l
    rw [← hcoord (b l)]
    conv_lhs => rw [← hrepr]
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [real_inner_smul_right, finBasisGram, hb]; ring
  -- `∑ₗ Bᵏˡ B_{lm} = δᵏₘ`
  have hBinvB : ∀ m, ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * finBasisGram (n := n) l m
      = (if k = m then (1 : ℝ) else 0) := by
    intro m
    have hmul : ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * finBasisGram (n := n) l m
        = ((finBasisGramMatrix (n := n))⁻¹ * finBasisGramMatrix (n := n)) k m := by
      rw [Matrix.mul_apply]; rfl
    rw [hmul, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]
  calc ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * ((b l) e)
      = ∑ l, ∑ m, (finBasisGramMatrix (n := n))⁻¹ k l
            * finBasisGram (n := n) l m * (b.repr w m) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hcB l, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_); ring
    _ = ∑ m, ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l
            * finBasisGram (n := n) l m * (b.repr w m) := Finset.sum_comm
    _ = ∑ m, (∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * finBasisGram (n := n) l m)
            * (b.repr w m) := by
        refine Finset.sum_congr rfl (fun m _ => ?_); rw [← Finset.sum_mul]
    _ = ∑ m, (if k = m then (1 : ℝ) else 0) * (b.repr w m) := by
        refine Finset.sum_congr rfl (fun m _ => ?_); rw [hBinvB m]
    _ = b.repr w k := by simp [Finset.sum_ite_eq]

/-- **Math.** The distinguished unit vector `1ₑ` is recovered from the
inverse-Gram-contracted coordinate vector: `∑ₖ (∑ₗ Bᵏˡ cₗ)·finBasisₖ = 1ₑ`. -/
theorem sum_invGram_coord_smul_finBasis (e : Fin n)
    (hunit : IsUnit (finBasisGramMatrix (n := n)).det) :
    ∑ k, (∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * (((Module.finBasis ℝ E) l) e))
        • ((Module.finBasis ℝ E) k) = EuclideanSpace.single e (1 : ℝ) := by
  have hrepr : ∑ k, ((Module.finBasis ℝ E).repr (EuclideanSpace.single e (1 : ℝ)) k)
      • (Module.finBasis ℝ E) k = EuclideanSpace.single e (1 : ℝ) :=
    (Module.finBasis ℝ E).sum_repr _
  rw [← hrepr]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [invGram_coord_eq_repr_single e hunit k]

/-! ## The `E`-valued Christoffel contraction of the hyperbolic metric -/

/-- **Math.** do Carmo Ch. 8 §3: the **basis-independent `E`-valued Christoffel
contraction** of the hyperbolic metric. Contracting the closed-form chart
Christoffel symbols `Γᵏᵢⱼ = -δⱼₖfᵢ - δₖᵢfⱼ + δᵢⱼfₖ` (`fᵢ = (finBasisᵢ)ₑ/yₑ`)
against `v, w : E` collapses, via the inverse-Gram/coordinate identities, to

`Γ(v, w)(y) = (yₑ)⁻¹ · ( ⟪v,w⟫·1ₑ - (vₑ)·w - (wₑ)·v )`,

where `1ₑ = EuclideanSpace.single e 1`, `vₑ = v e`, and `⟪·,·⟫` is the ambient
Euclidean inner product. This is do Carmo's `∇_v w` in the trivial chart of the
open half-space, and it drives the geodesic equation of `Hⁿ`. -/
theorem hyperbolic_chartChristoffelContraction_eq (e : Fin n) (α : ↥(upperHalfSpace e))
    (v w : E) {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ, E) α).target) :
    chartChristoffelContraction (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α v w y
      = (y e)⁻¹ • ((⟪v, w⟫ : ℝ) • EuclideanSpace.single e (1 : ℝ)
          - (v e) • w - (w e) • v) := by
  classical
  have hunit := finBasisGramMatrix_det_isUnit (n := n) e α
  -- Abbreviation for the inverse-Gram-contracted coordinate vector `S̃ₖ = ∑ₗ Bᵏˡ cₗ`.
  set S : Fin (Module.finrank ℝ E) → ℝ :=
    fun k => ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * (((Module.finBasis ℝ E) l) e) with hS
  -- Per-`k` closed form of the inner double sum, the `k`-component of `Γ(v,w)(y)`.
  have hcoef : ∀ k, (∑ i, ∑ j, chartChristoffel (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α i j k y
        * chartCoord i v * chartCoord j w)
      = (y e)⁻¹ * ((⟪v, w⟫ : ℝ) * S k
          - (v e) * chartCoord k w - (w e) * chartCoord k v) := by
    intro k
    have hstep : ∀ i j, chartChristoffel (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α i j k y
        = (y e)⁻¹ * ( -(((Module.finBasis ℝ E) i) e) * (if k = j then (1:ℝ) else 0)
            - (((Module.finBasis ℝ E) j) e) * (if k = i then (1:ℝ) else 0)
            + S k * finBasisGram (n := n) i j) := by
      intro i j
      rw [hyperbolic_chartChristoffel (n := n) e α i j k hy, hS]
      ring
    calc ∑ i, ∑ j, chartChristoffel (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α i j k y
            * chartCoord i v * chartCoord j w
        = (y e)⁻¹ * ∑ i, ∑ j,
            ( -(((Module.finBasis ℝ E) i) e) * (if k = j then (1:ℝ) else 0)
              - (((Module.finBasis ℝ E) j) e) * (if k = i then (1:ℝ) else 0)
              + S k * finBasisGram (n := n) i j)
            * chartCoord i v * chartCoord j w := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hstep i j]; ring
      _ = (y e)⁻¹ * ((⟪v, w⟫ : ℝ) * S k
            - (v e) * chartCoord k w - (w e) * chartCoord k v) := by
          congr 1
          -- coordinate contraction of a `-(finBasisᵢ)ₑ` coefficient against `u`
          have hcoef_c : ∀ u : E, ∑ i, -(((Module.finBasis ℝ E) i) e) * chartCoord i u = -(u e) := by
            intro u
            have hrw : ∀ i, -(((Module.finBasis ℝ E) i) e) * chartCoord i u
                = (-1 : ℝ) * (chartCoord i u * (((Module.finBasis ℝ E) i) e)) := by
              intro i; ring
            rw [Finset.sum_congr rfl (fun i _ => hrw i), ← Finset.mul_sum]
            simp only [chartCoord_def]
            rw [← coord_eq_sum_repr e u]; ring
          -- the three do Carmo terms `-δⱼₖfᵢ · v^i w^j`, `-δₖᵢfⱼ · v^i w^j`, `δᵢⱼ… · v^i w^j`
          have hsum1 : ∑ i, ∑ j, (-(((Module.finBasis ℝ E) i) e) * (if k = j then (1:ℝ) else 0))
                * chartCoord i v * chartCoord j w
              = -((v e) * chartCoord k w) := by
            have step : ∀ i, ∑ j, (-(((Module.finBasis ℝ E) i) e) * (if k = j then (1:ℝ) else 0))
                  * chartCoord i v * chartCoord j w
                = (-(((Module.finBasis ℝ E) i) e) * chartCoord i v) * chartCoord k w := by
              intro i
              rw [Finset.sum_eq_single k
                  (fun j _ hjk => by rw [if_neg (fun h => hjk h.symm)]; ring)
                  (fun hk => absurd (Finset.mem_univ k) hk)]
              rw [if_pos rfl]; ring
            rw [Finset.sum_congr rfl (fun i _ => step i), ← Finset.sum_mul]
            rw [show (∑ i, -(((Module.finBasis ℝ E) i) e) * chartCoord i v)
                = -(v e) from hcoef_c v]
            ring
          have hsum2 : ∑ i, ∑ j, (-(((Module.finBasis ℝ E) j) e) * (if k = i then (1:ℝ) else 0))
                * chartCoord i v * chartCoord j w
              = -((w e) * chartCoord k v) := by
            have step : ∀ i, ∑ j, (-(((Module.finBasis ℝ E) j) e) * (if k = i then (1:ℝ) else 0))
                  * chartCoord i v * chartCoord j w
                = (if k = i then (1:ℝ) else 0) * chartCoord i v * -(w e) := by
              intro i
              have hfac : ∑ j, (-(((Module.finBasis ℝ E) j) e) * (if k = i then (1:ℝ) else 0))
                    * chartCoord i v * chartCoord j w
                  = (if k = i then (1:ℝ) else 0) * chartCoord i v
                      * ∑ j, (-(((Module.finBasis ℝ E) j) e) * chartCoord j w) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun j _ => ?_); ring
              rw [hfac, hcoef_c w]
            rw [Finset.sum_congr rfl (fun i _ => step i),
              Finset.sum_eq_single k
                (fun i _ hik => by rw [if_neg (fun h => hik h.symm)]; ring)
                (fun hk => absurd (Finset.mem_univ k) hk)]
            rw [if_pos rfl]; ring
          have hsum3 : ∑ i, ∑ j, (S k * finBasisGram (n := n) i j)
                * chartCoord i v * chartCoord j w
              = S k * (⟪v, w⟫ : ℝ) := by
            rw [inner_eq_sum_gram v w, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [chartCoord_def]; ring
          have expand : ∀ i j,
              ( -(((Module.finBasis ℝ E) i) e) * (if k = j then (1:ℝ) else 0)
                - (((Module.finBasis ℝ E) j) e) * (if k = i then (1:ℝ) else 0)
                + S k * finBasisGram (n := n) i j)
                * chartCoord i v * chartCoord j w
              = (-(((Module.finBasis ℝ E) i) e) * (if k = j then (1:ℝ) else 0))
                  * chartCoord i v * chartCoord j w
                + (-(((Module.finBasis ℝ E) j) e) * (if k = i then (1:ℝ) else 0))
                  * chartCoord i v * chartCoord j w
                + (S k * finBasisGram (n := n) i j)
                  * chartCoord i v * chartCoord j w := by
            intro i j; ring
          simp_rw [expand, Finset.sum_add_distrib, hsum1, hsum2, hsum3]
          ring
  -- assemble the vector: pull `(yₑ)⁻¹` out and recombine the three coordinate sums
  rw [chartChristoffelContraction_def,
    Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => by rw [hcoef k])]
  simp_rw [mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  have hA : ∑ k, ((⟪v, w⟫ : ℝ) * S k) • ((Module.finBasis ℝ E) k)
      = (⟪v, w⟫ : ℝ) • EuclideanSpace.single e (1 : ℝ) := by
    simp_rw [mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    simp only [hS]
    exact sum_invGram_coord_smul_finBasis e hunit
  have hB : ∑ k, ((v e) * chartCoord k w) • ((Module.finBasis ℝ E) k) = (v e) • w := by
    simp_rw [mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    simp only [chartCoord_def]
    exact (Module.finBasis ℝ E).sum_repr w
  have hC : ∑ k, ((w e) * chartCoord k v) • ((Module.finBasis ℝ E) k) = (w e) • v := by
    simp_rw [mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    simp only [chartCoord_def]
    exact (Module.finBasis ℝ E).sum_repr v
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hA, hB, hC]

/-! ## The geodesic equation of `Hⁿ` and its solutions -/

/-- **Math.** do Carmo Ch. 8 §3: the **geodesic equation of `Hⁿ`** in `E`-valued
form. A twice-differentiable curve `φ : ℝ → E` staying in the half-space
(`φ(s)ₑ > 0`) whose acceleration obeys

`φ''(t) + (φ(t)ₑ)⁻¹·( ⟪φ'(t),φ'(t)⟫·1ₑ - 2 (φ'(t)ₑ)·φ'(t) ) = 0`

lifts to a geodesic of the hyperbolic metric. This is `u'' + Γ(u',u') = 0` read
through the closed-form contraction `hyperbolic_chartChristoffelContraction_eq`;
the chart of the open half-space is the inclusion, so the moving-foot chart curve
`s ↦ φ_{γt}(γ s)` is literally `φ`. -/
theorem hyperbolic_isGeodesic_of {e : Fin n} {φ φ' φ'' : ℝ → E}
    (hpos : ∀ s, 0 < φ s e)
    (hd1 : ∀ s, HasDerivAt φ (φ' s) s)
    (hd2 : ∀ s, HasDerivAt φ' (φ'' s) s)
    (hgeo : ∀ t, φ'' t + (φ t e)⁻¹ • ((⟪φ' t, φ' t⟫ : ℝ) • EuclideanSpace.single e (1 : ℝ)
        - (φ' t e) • φ' t - (φ' t e) • φ' t) = 0) :
    IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e)
      (fun s => (⟨φ s, hpos s⟩ : ↥(upperHalfSpace e))) := by
  set γ : ℝ → ↥(upperHalfSpace e) := fun s => ⟨φ s, hpos s⟩ with hγ
  have hclc : ∀ t, chartLocalCurve (I := 𝓘(ℝ, E)) γ t = φ := by
    intro t; funext s
    rw [chartLocalCurve_def, extChartAt_opens_coe]
  intro t
  refine ⟨φ' t, φ'' t, ?_, ?_, ?_, ?_⟩
  · rw [hclc t]; exact hd1 t
  · rw [hclc t]
    exact Filter.Eventually.of_forall (fun s => by rw [(hd1 s).deriv]; exact hd1 s)
  · have hfun : (fun s => deriv (chartLocalCurve (I := 𝓘(ℝ, E)) γ t) s) = φ' := by
      funext s; rw [hclc t]; exact (hd1 s).deriv
    rw [hfun]; exact hd2 t
  · have hxeq : extChartAt 𝓘(ℝ, E) (γ t) (γ t) = φ t := rfl
    have hymem : φ t ∈ (extChartAt 𝓘(ℝ, E) (γ t)).target :=
      (extChartAt 𝓘(ℝ, E) (γ t)).map_source (mem_extChartAt_source (γ t))
    rw [hxeq, hyperbolic_chartChristoffelContraction_eq e (γ t) (φ' t) (φ' t) hymem]
    exact hgeo t

/-- **Math.** The vertical line `t ↦ c + (a·eᵗ)·1ₑ` (horizontal base `cₑ = 0`,
`a > 0`) stays in the half-space `Hⁿ`. -/
theorem vertical_mem (e : Fin n) (c : E) (hc : c e = 0) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    c + (a * Real.exp s) • EuclideanSpace.single e (1 : ℝ) ∈ upperHalfSpace e := by
  rw [mem_upperHalfSpace]
  have hpos : (0 : ℝ) < a * Real.exp s := by positivity
  simpa [hc] using hpos

/-- **Math.** do Carmo Ch. 8 §3, Prop. 3.1 (vertical geodesics). The **vertical
lines of `Hⁿ`**, perpendicular to the boundary hyperplane `∂Hⁿ = {xₑ = 0}`, are
geodesics: for a horizontal base point `c` (`cₑ = 0`) and `a > 0`, the affinely
parametrised vertical line `t ↦ c + (a·eᵗ)·1ₑ` is a geodesic of the hyperbolic
metric. (Its `e`-coordinate `a·eᵗ` solves do Carmo's `h''·h = (h')²`.) -/
theorem hyperbolic_vertical_isGeodesic (e : Fin n) (c : E) (hc : c e = 0)
    {a : ℝ} (ha : 0 < a) :
    IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e)
      (fun s => (⟨c + (a * Real.exp s) • EuclideanSpace.single e (1 : ℝ),
        vertical_mem e c hc ha s⟩ : ↥(upperHalfSpace e))) := by
  refine hyperbolic_isGeodesic_of (hpos := fun s => vertical_mem e c hc ha s)
    (φ := fun s => c + (a * Real.exp s) • EuclideanSpace.single e (1 : ℝ))
    (φ' := fun s => (a * Real.exp s) • EuclideanSpace.single e (1 : ℝ))
    (φ'' := fun s => (a * Real.exp s) • EuclideanSpace.single e (1 : ℝ))
    (fun s => (((Real.hasDerivAt_exp s).const_mul a).smul_const _).const_add c)
    (fun s => ((Real.hasDerivAt_exp s).const_mul a).smul_const _)
    ?_
  intro t
  dsimp only
  set b := a * Real.exp t with hb
  have hce : (c + b • EuclideanSpace.single e (1 : ℝ)) e = b := by simp [hc]
  have hse : (b • EuclideanSpace.single e (1 : ℝ)) e = b := by simp
  have hinner : (⟪b • EuclideanSpace.single e (1 : ℝ),
      b • EuclideanSpace.single e (1 : ℝ)⟫ : ℝ) = b * b := by
    rw [real_inner_smul_left, real_inner_smul_right]; simp
  rw [hce, hse, hinner]
  match_scalars <;> field_simp <;> ring

/-- **Math.** The semicircle `t ↦ m + (r·tanh t)·û + (r·sech t)·1ₑ` (center `m` on
`∂Hⁿ`, `û` horizontal) stays in the half-space `Hⁿ`. -/
theorem semicircle_mem (e : Fin n) (m u : E) (hm : m e = 0) (hu : u e = 0) {r : ℝ}
    (hr : 0 < r) (s : ℝ) :
    m + ((r * Real.sinh s / Real.cosh s) • u + (r / Real.cosh s) • EuclideanSpace.single e (1 : ℝ))
      ∈ upperHalfSpace e := by
  rw [mem_upperHalfSpace]
  have hpos : (0 : ℝ) < r / Real.cosh s := div_pos hr (Real.cosh_pos s)
  simpa [hm, hu] using hpos

/-- **Math.** do Carmo Ch. 8 §3, Prop. 3.1 (semicircle geodesics). The **semicircles
of `Hⁿ` perpendicular to `∂Hⁿ = {xₑ = 0}` with center on `∂Hⁿ`** are geodesics: for
a center `m` on the boundary (`mₑ = 0`), a unit horizontal vector `û` (`ûₑ = 0`,
`⟪û,û⟫ = 1`) and radius `r > 0`, the affinely parametrised semicircle
`t ↦ m + (r·tanh t)·û + (r·sech t)·1ₑ` (with `tanh t = sinh t/cosh t`,
`sech t = 1/cosh t`) is a geodesic of the hyperbolic metric. -/
theorem hyperbolic_semicircle_isGeodesic (e : Fin n) (m u : E) (hm : m e = 0) (hu : u e = 0)
    (hunorm : (⟪u, u⟫ : ℝ) = 1) {r : ℝ} (hr : 0 < r) :
    IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e)
      (fun s => (⟨m + ((r * Real.sinh s / Real.cosh s) • u
            + (r / Real.cosh s) • EuclideanSpace.single e (1 : ℝ)),
          semicircle_mem e m u hm hu hr s⟩ : ↥(upperHalfSpace e))) := by
  refine hyperbolic_isGeodesic_of (hpos := fun s => semicircle_mem e m u hm hu hr s)
    (φ := fun s => m + ((r * Real.sinh s / Real.cosh s) • u
        + (r / Real.cosh s) • EuclideanSpace.single e (1 : ℝ)))
    (φ' := fun s => (r / (Real.cosh s)^2) • u
        + (-(r * Real.sinh s) / (Real.cosh s)^2) • EuclideanSpace.single e (1 : ℝ))
    (φ'' := fun s => (-2 * r * Real.sinh s / (Real.cosh s)^3) • u
        + ((-r * (Real.cosh s)^2 + 2 * r * (Real.sinh s)^2) / (Real.cosh s)^3)
            • EuclideanSpace.single e (1 : ℝ))
    ?_ ?_ ?_
  · -- `HasDerivAt φ (φ' s) s`
    intro s
    have hc : Real.cosh s ≠ 0 := (Real.cosh_pos s).ne'
    have hA : HasDerivAt (fun t => r * Real.sinh t / Real.cosh t) (r / (Real.cosh s)^2) s := by
      have h := ((Real.hasDerivAt_sinh s).const_mul r).div (Real.hasDerivAt_cosh s) hc
      convert h using 1 <;> try rfl
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq s]
    have hB : HasDerivAt (fun t => r / Real.cosh t) (-(r * Real.sinh s) / (Real.cosh s)^2) s := by
      have h := (hasDerivAt_const s r).div (Real.hasDerivAt_cosh s) hc
      convert h using 1 <;> try rfl
      field_simp
      ring
    exact ((hA.smul_const u).add (hB.smul_const _)).const_add m
  · -- `HasDerivAt φ' (φ'' s) s`
    intro s
    have hc : Real.cosh s ≠ 0 := (Real.cosh_pos s).ne'
    have hA' : HasDerivAt (fun t => r / (Real.cosh t)^2)
        (-2 * r * Real.sinh s / (Real.cosh s)^3) s := by
      have h := (hasDerivAt_const s r).div ((Real.hasDerivAt_cosh s).pow 2) (pow_ne_zero 2 hc)
      convert h using 1 <;> try rfl
      simp only [Pi.pow_apply]
      field_simp
      ring
    have hB' : HasDerivAt (fun t => -(r * Real.sinh t) / (Real.cosh t)^2)
        ((-r * (Real.cosh s)^2 + 2 * r * (Real.sinh s)^2) / (Real.cosh s)^3) s := by
      have h := (((Real.hasDerivAt_sinh s).const_mul r).neg).div
        ((Real.hasDerivAt_cosh s).pow 2) (pow_ne_zero 2 hc)
      convert h using 1 <;> try rfl
      simp only [Pi.pow_apply, Pi.neg_apply]
      field_simp
      ring
    exact (hA'.smul_const u).add (hB'.smul_const _)
  · -- the geodesic ODE
    intro t
    dsimp only
    have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
    have hphie : (m + ((r * Real.sinh t / Real.cosh t) • u
        + (r / Real.cosh t) • EuclideanSpace.single e (1 : ℝ))) e = r / Real.cosh t := by
      simp [hm, hu]
    have hphi'e : ((r / (Real.cosh t)^2) • u
        + (-(r * Real.sinh t) / (Real.cosh t)^2) • EuclideanSpace.single e (1 : ℝ)) e
          = -(r * Real.sinh t) / (Real.cosh t)^2 := by
      simp [hu]
    have hnorm : (⟪(r / (Real.cosh t)^2) • u
          + (-(r * Real.sinh t) / (Real.cosh t)^2) • EuclideanSpace.single e (1 : ℝ),
          (r / (Real.cosh t)^2) • u
          + (-(r * Real.sinh t) / (Real.cosh t)^2) • EuclideanSpace.single e (1 : ℝ)⟫ : ℝ)
        = r^2 / (Real.cosh t)^2 := by
      have huw : (⟪u, EuclideanSpace.single e (1 : ℝ)⟫ : ℝ) = 0 := by
        have h : (⟪u, EuclideanSpace.single e (1 : ℝ)⟫ : ℝ) = 1 * (starRingEnd ℝ) (u e) :=
          EuclideanSpace.inner_single_right e (1 : ℝ) u
        rw [h, hu]; simp
      have hww : (⟪EuclideanSpace.single e (1 : ℝ), EuclideanSpace.single e (1 : ℝ)⟫ : ℝ) = 1 := by
        have h : (⟪EuclideanSpace.single e (1 : ℝ), EuclideanSpace.single e (1 : ℝ)⟫ : ℝ)
            = 1 * (starRingEnd ℝ) ((EuclideanSpace.single e (1 : ℝ)) e) :=
          EuclideanSpace.inner_single_right e (1 : ℝ) (EuclideanSpace.single e (1 : ℝ))
        rw [h]; simp
      have hwu : (⟪EuclideanSpace.single e (1 : ℝ), u⟫ : ℝ) = 0 := by
        rw [real_inner_comm]; exact huw
      have hkey : (r / (Real.cosh t)^2)^2 + (-(r * Real.sinh t) / (Real.cosh t)^2)^2
          = r^2 / (Real.cosh t)^2 := by
        rw [neg_div, neg_sq, div_pow, div_pow, mul_pow, ← add_div,
          div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (-(r^2 * (Real.cosh t)^2)) * Real.cosh_sq_sub_sinh_sq t
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hunorm, huw, hww, hwu]
      linear_combination hkey
    rw [hphie, hphi'e, hnorm]
    match_scalars <;> field_simp <;> ring

end Riemannian.Hyperbolic
