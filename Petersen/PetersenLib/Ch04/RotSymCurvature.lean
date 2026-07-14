import PetersenLib.Ch04.ComputationalSimplifications
import PetersenLib.Ch01.SnCsFunctions

/-!
# Petersen Ch. 4, §4.2.3 — Curvature of rotationally symmetric metrics

Petersen computes the curvature of the rotationally symmetric metric
`g = dr² + ρ²(r)·ds²_{n-1}` on `I × Sⁿ⁻¹` in an adapted orthonormal frame
`{∂r} ∪ {eᵢ}` (`eᵢ` tangent to the distance spheres): the fundamental
equations of the frame are the **radial Jacobi equation**
`R(X,∂r)∂r = -(ρ̈/ρ)·X` (blueprint node `prop:pet-ch4-rotsym-radial-jacobi`),
the **tangential (Gauss) equation** with sectional curvature `(1-ρ̇²)/ρ²`,
and the **mixed vanishing** `g(R(X,Y)Z, ∂r) = 0` for tangential `X,Y,Z`.
These are Chapter 3 manifold facts **not yet formalized**, so throughout this
file they enter as *hypotheses* (`hrad`, `htan`, `hmix`) on an abstract
algebraic curvature form `B` on a single tangent space, in the vendored
convention where `B x y x y` is the sectional-curvature numerator
(`sectionalCurvature B x y = B x y x y / wedgeSq x y`); in that convention
the radial Jacobi equation reads `B(eᵢ, e_{i₀}, eⱼ, e_{i₀}) = a·δᵢⱼ` with
`a := -ρ̈/ρ` and `e_{i₀}` playing the role of `∂r`.

Blueprint nodes covered (`\lean{}` anchors):

* `rotSymCurvatureOperator` (`thm:pet-ch4-rotsym-curvature-operator`):
  the three frame equations force the full Kronecker-diagonal form
  `B(eᵢ,eⱼ,e_k,e_l) = λᵢⱼ(δᵢₖδⱼₗ − δᵢₗδⱼₖ)` with `λᵢⱼ = a` for radial pairs
  and `λᵢⱼ = b := (1-ρ̇²)/ρ²` for tangential pairs — so the wedges of the
  adapted frame diagonalize the curvature operator — and consequently every
  sectional curvature lies in `[min a b, max a b]`
  (via Prop 4.1.1, `secBoundsFromDiagonalCurvatureOperator`).
* `rotSymRicciScalar`: the adapted frame diagonalizes the Ricci tensor, with
  `Ric(∂r,∂r) = (n-1)·a`, `Ric(eᵢ,eᵢ) = a + (n-2)·b`, and scalar curvature
  `2(n-1)·a + (n-1)(n-2)·b`.
* `rotSymDim2Curvature`: in dimension `2` the tangential equation is vacuous
  and the sectional curvature of the unique 2-plane is `a = -ρ̈/ρ`.
* `snkConstantCurvature`: for `ρ = sn_k` both eigenvalues equal `k`
  (`sn_k'' = -k·sn_k` and the Pythagorean identity `cs_k² + k·sn_k² = 1`),
  so the metric has constant curvature `k`.
* `ricciFlatRotSymIsFlat`: (pure ODE) in dimension `n ≥ 3`, Ricci-flatness
  (`ρ̈ = 0` and `(n-2)(1-ρ̇²)/ρ² - ρ̈/ρ = 0`) forces `ρ(r) = a ± r` — the
  metric is flat; `ricciFlatRotSymIsFlat_dim2` records the `n = 2` case,
  where `ρ̈ = 0` alone gives `ρ(r) = a + c·r`.

The core algebraic step is `rotSymDiagonalization`, a pure symmetry
case-bash reducing every component `B(eᵢ,eⱼ,e_k,e_l)` of the adapted frame
to the radial/tangential/mixed patterns.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.2.3, pp. 145–148.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace PetersenLib

open Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [DecidableEq ι]

/-! ## The diagonalization of the curvature operator -/

/-- **Math.** Petersen §4.2.3, core algebraic step of the curvature
computation for rotationally symmetric metrics: let `e i` be an adapted
frame with distinguished radial direction `e i₀ = ∂r`, and suppose the
algebraic curvature form `B` satisfies

* the **radial Jacobi equation** `B(eᵢ, e_{i₀}, eⱼ, e_{i₀}) = a·δᵢⱼ`
  (`hrad`; in Petersen's notation `R(X,∂r)∂r = a·X` with `a = -ρ̈/ρ`, written
  here in the convention where `B x y x y` is the sectional numerator),
* the **tangential Gauss equation**
  `B(eᵢ,eⱼ,e_k,e_l) = b·(δᵢₖδⱼₗ − δᵢₗδⱼₖ)` for tangential indices (`htan`,
  with `b = (1-ρ̇²)/ρ²`), and
* the **mixed vanishing** `B(eᵢ,eⱼ,e_k,e_{i₀}) = 0` for tangential indices
  (`hmix`),

then *all* components of `B` in the frame have the Kronecker-diagonal form
`B(eᵢ,eⱼ,e_k,e_l) = λᵢⱼ·(δᵢₖδⱼₗ − δᵢₗδⱼₖ)` with eigenvalue `λᵢⱼ = a` when
the pair `{i,j}` contains the radial index and `λᵢⱼ = b` otherwise: the
wedges `eᵢ ∧ eⱼ` diagonalize the curvature operator. The proof is a
systematic case analysis on which slots carry `i₀`, using the antisymmetries
and the pair-swap symmetry of `B` to reduce every component to one of the
three hypothesis patterns or to zero. These three equations are Chapter 3
manifold facts (blueprint node `prop:pet-ch4-rotsym-radial-jacobi` and the
Gauss equation), taken here as hypotheses on the abstract curvature form. -/
theorem rotSymDiagonalization {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (e : ι → V) (i₀ : ι) (a b : ℝ)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) = a * (if i = j then (1 : ℝ) else 0))
    (htan : ∀ i j k l, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → l ≠ i₀ →
      B (e i) (e j) (e k) (e l) = b *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ i j k, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → B (e i) (e j) (e k) (e i₀) = 0) :
    ∀ i j k l, B (e i) (e j) (e k) (e l) =
      (if i = i₀ ∨ j = i₀ then a else b) *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)) := by
  intro i j k l
  by_cases hi : i = i₀
  · by_cases hj : j = i₀
    · -- the first pair is (∂r, ∂r): everything vanishes
      rw [hi, hj, hB.self_left]; ring
    · by_cases hk : k = i₀
      · by_cases hl : l = i₀
        · -- the second pair is (∂r, ∂r)
          rw [hk, hl, hB.self_right]; ring
        · -- (i₀, j, i₀, l): radial, after moving `i₀` to the second slots
          rw [hi, hk, hB.antisymm₁₂, hB.antisymm₃₄, neg_neg, hrad j l hj hl]
          simp [hj, Ne.symm hl]
      · by_cases hl : l = i₀
        · -- (i₀, j, k, i₀): radial with one sign
          rw [hi, hl, hB.antisymm₁₂, hrad j k hj hk]
          simp [hj, Ne.symm hk]
        · -- (i₀, j, k, l): mixed, vanishes
          rw [hi, hB.pairSwap, hB.antisymm₃₄, hmix k l j hk hl hj]
          simp [Ne.symm hk, Ne.symm hl]
  · by_cases hj : j = i₀
    · by_cases hk : k = i₀
      · by_cases hl : l = i₀
        · rw [hk, hl, hB.self_right]; ring
        · -- (i, i₀, i₀, l): radial with one sign
          rw [hj, hk, hB.antisymm₃₄, hrad i l hi hl]
          simp [hi, Ne.symm hl]
      · by_cases hl : l = i₀
        · -- (i, i₀, k, i₀): the radial hypothesis itself
          rw [hj, hl, hrad i k hi hk]
          simp [hi, Ne.symm hk]
        · -- (i, i₀, k, l): mixed, vanishes
          rw [hj, hB.pairSwap, hmix k l i hk hl hi]
          simp [Ne.symm hk, Ne.symm hl]
    · by_cases hk : k = i₀
      · by_cases hl : l = i₀
        · rw [hk, hl, hB.self_right]; ring
        · -- (i, j, i₀, l): mixed, vanishes
          rw [hk, hB.antisymm₃₄, hmix i j l hi hj hl]
          simp [hi, hj]
      · by_cases hl : l = i₀
        · -- (i, j, k, i₀): the mixed hypothesis itself
          rw [hl, hmix i j k hi hj hk]
          simp [hi, hj]
        · -- all indices tangential: the Gauss equation
          rw [htan i j k l hi hj hk hl]
          simp [hi, hj]

/-- **Math.** Petersen §4.2.3: given the three frame equations of a
rotationally symmetric metric (radial eigenvalue `a`, tangential eigenvalue
`b`; see `rotSymDiagonalization`), every sectional curvature lies between
`min a b` and `max a b`. This is Petersen's Prop 4.1.1
(`secBoundsFromDiagonalCurvatureOperator`) applied to the Kronecker
diagonalization with eigenvalues `λᵢⱼ ∈ {a, b}`. -/
theorem rotSymSectionalBounds [Fintype ι] {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis ι ℝ V) (i₀ : ι) (a b : ℝ)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) = a * (if i = j then (1 : ℝ) else 0))
    (htan : ∀ i j k l, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → l ≠ i₀ →
      B (e i) (e j) (e k) (e l) = b *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ i j k, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → B (e i) (e j) (e k) (e i₀) = 0) :
    ∀ v w : V, ⟪v, v⟫ = 1 → ⟪w, w⟫ = 1 → ⟪v, w⟫ = 0 →
      sectionalCurvature B v w ∈ Set.Icc (min a b) (max a b) := by
  have hdiag := rotSymDiagonalization hB (⇑e) i₀ a b hrad htan hmix
  intro v w hv hw hvw
  refine secBoundsFromDiagonalCurvatureOperator hB e
    (lam := fun i j => if i = i₀ ∨ j = i₀ then a else b) hdiag ?_ ?_ hv hw hvw
  · intro i j _
    show min a b ≤ if i = i₀ ∨ j = i₀ then a else b
    split
    · exact min_le_left a b
    · exact min_le_right a b
  · intro i j _
    show (if i = i₀ ∨ j = i₀ then a else b) ≤ max a b
    split
    · exact le_max_left a b
    · exact le_max_right a b

/-! ## The curvature operator theorem (blueprint anchor) -/

set_option linter.unusedVariables false in
/-- **Math.** Petersen §4.2.3, **curvature of rotationally symmetric metrics**
(blueprint node `thm:pet-ch4-rotsym-curvature-operator`): for
`g = dr² + ρ²(r)·ds²_{n-1}`, in an adapted orthonormal frame with radial
direction `e i₀ = ∂r`, write `a := -ρ̈/ρ` for the radial and
`b := (1-ρ̇²)/ρ²` for the tangential sectional curvature at radius `r`
(`hρ : ρ r ≠ 0` makes these the genuine curvatures). Assuming the three
frame equations (`hrad`, `htan`, `hmix` — Chapter 3 manifold facts taken as
hypotheses on the abstract curvature form `B` at the given point, cf.
`prop:pet-ch4-rotsym-radial-jacobi` and the Gauss equation):

1. the wedges of the frame diagonalize the curvature operator, with the
   Kronecker-diagonal components
   `B(eᵢ,eⱼ,e_k,e_l) = λᵢⱼ(δᵢₖδⱼₗ − δᵢₗδⱼₖ)`, `λᵢⱼ = a` for radial and `b`
   for tangential pairs; and
2. every sectional curvature lies in `[min a b, max a b]`. -/
theorem rotSymCurvatureOperator [Fintype ι] {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis ι ℝ V) (i₀ : ι)
    (ρ : ℝ → ℝ) (r : ℝ) (hρ : ρ r ≠ 0)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) =
        (-(deriv (deriv ρ) r) / ρ r) * (if i = j then (1 : ℝ) else 0))
    (htan : ∀ i j k l, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → l ≠ i₀ →
      B (e i) (e j) (e k) (e l) = ((1 - deriv ρ r ^ 2) / ρ r ^ 2) *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ i j k, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → B (e i) (e j) (e k) (e i₀) = 0) :
    (∀ i j k l, B (e i) (e j) (e k) (e l) =
      (if i = i₀ ∨ j = i₀ then -(deriv (deriv ρ) r) / ρ r
        else (1 - deriv ρ r ^ 2) / ρ r ^ 2) *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))) ∧
    ∀ v w : V, ⟪v, v⟫ = 1 → ⟪w, w⟫ = 1 → ⟪v, w⟫ = 0 →
      sectionalCurvature B v w ∈ Set.Icc
        (min (-(deriv (deriv ρ) r) / ρ r) ((1 - deriv ρ r ^ 2) / ρ r ^ 2))
        (max (-(deriv (deriv ρ) r) / ρ r) ((1 - deriv ρ r ^ 2) / ρ r ^ 2)) :=
  ⟨rotSymDiagonalization hB (⇑e) i₀ _ _ hrad htan hmix,
    rotSymSectionalBounds hB e i₀ _ _ hrad htan hmix⟩

/-! ## Ricci and scalar curvature -/

/-- **Math.** Petersen §4.2.3, Ricci curvature of a rotationally symmetric
metric, abstract form: with radial eigenvalue `a` and tangential eigenvalue
`b` as in `rotSymDiagonalization`, and `n = card ι` the dimension, the
adapted frame diagonalizes the Ricci tensor with
`Ric(∂r,∂r) = (n-1)·a`, `Ric(eᵢ,eᵢ) = a + (n-2)·b` for tangential `i`, and
the scalar curvature is `2(n-1)·a + (n-1)(n-2)·b`. Each diagonal Ricci
entry is the trace `∑_k B(eᵢ,e_k,eᵢ,e_k)`, which the Kronecker form reduces
to a count of eigenvalues (`n-1` radial terms for `∂r`; one radial plus
`n-2` tangential terms for `eᵢ`); the off-diagonal entries vanish by
Petersen's Prop 4.1.3 (`ricciDiagonalFromTripleVanishing`). -/
theorem rotSymRicciDiagonal [Fintype ι] [FiniteDimensional ℝ V]
    {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis ι ℝ V) (i₀ : ι) (a b : ℝ)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) = a * (if i = j then (1 : ℝ) else 0))
    (htan : ∀ i j k l, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → l ≠ i₀ →
      B (e i) (e j) (e k) (e l) = b *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ i j k, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → B (e i) (e j) (e k) (e i₀) = 0) :
    ricciForm hB (e i₀) (e i₀) = ((Fintype.card ι : ℝ) - 1) * a ∧
    (∀ i, i ≠ i₀ → ricciForm hB (e i) (e i) = a + ((Fintype.card ι : ℝ) - 2) * b) ∧
    (∀ i j, i ≠ j → ricciForm hB (e i) (e j) = 0) ∧
    scalarCurvature hB = 2 * ((Fintype.card ι : ℝ) - 1) * a
      + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * b := by
  have hdiag := rotSymDiagonalization hB (⇑e) i₀ a b hrad htan hmix
  -- Ricci in the radial direction: `n - 1` radial eigenvalues.
  have h₁ : ricciForm hB (e i₀) (e i₀) = ((Fintype.card ι : ℝ) - 1) * a := by
    rw [ricciForm_eq_sum hB _ _ e]
    have hterm : ∀ i : ι, B (e i₀) (e i) (e i₀) (e i) =
        a - (if i = i₀ then a else 0) := by
      intro i
      rw [hdiag i₀ i i₀ i]
      by_cases hii : i = i₀
      · simp [hii]
      · simp [hii, Ne.symm hii]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq' Finset.univ i₀ fun _ => a, if_pos (Finset.mem_univ i₀)]
    ring
  -- Ricci in a tangential direction: one radial plus `n - 2` tangential.
  have h₂ : ∀ i, i ≠ i₀ →
      ricciForm hB (e i) (e i) = a + ((Fintype.card ι : ℝ) - 2) * b := by
    intro x hx
    rw [ricciForm_eq_sum hB _ _ e]
    have hterm : ∀ i : ι, B (e x) (e i) (e x) (e i) =
        b + (if i = x then -b else 0) + (if i = i₀ then a - b else 0) := by
      intro i
      rw [hdiag x i x i]
      by_cases h1 : i = x
      · simp [h1, hx]
      · by_cases h2 : i = i₀
        · simp [h2, Ne.symm hx]
        · simp [h1, h2, hx]
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq' Finset.univ x fun _ => -b, if_pos (Finset.mem_univ x),
      Finset.sum_ite_eq' Finset.univ i₀ fun _ => a - b, if_pos (Finset.mem_univ i₀)]
    ring
  -- The frame diagonalizes the Ricci tensor (Prop 4.1.3).
  have h₃ : ∀ i j, i ≠ j → ricciForm hB (e i) (e j) = 0 := by
    intro i j hij
    refine ricciDiagonalFromTripleVanishing hB e ?_ hij
    intro x y z hxy hyz hxz
    rw [hdiag x y z x]
    simp [hxz, Ne.symm hxy, hyz]
  refine ⟨h₁, h₂, h₃, ?_⟩
  -- Scalar curvature: sum of the Ricci diagonal.
  rw [scalarCurvature_eq_sum_ricci hB e]
  have hterm : ∀ j : ι, ricciForm hB (e j) (e j) =
      (a + ((Fintype.card ι : ℝ) - 2) * b)
        + (if j = i₀ then
            ((Fintype.card ι : ℝ) - 1) * a - (a + ((Fintype.card ι : ℝ) - 2) * b)
          else 0) := by
    intro j
    by_cases hj : j = i₀
    · rw [hj, h₁, if_pos rfl]; ring
    · rw [h₂ j hj, if_neg hj]; ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq' Finset.univ i₀
      fun _ => ((Fintype.card ι : ℝ) - 1) * a - (a + ((Fintype.card ι : ℝ) - 2) * b),
    if_pos (Finset.mem_univ i₀)]
  ring

set_option linter.unusedVariables false in
/-- **Math.** Petersen §4.2.3, **Ricci and scalar curvature of a rotationally
symmetric metric** `g = dr² + ρ²(r)·ds²_{n-1}` (blueprint anchor): with
`a = -ρ̈/ρ`, `b = (1-ρ̇²)/ρ²` and `n = card ι` the dimension, under the three
frame equations (hypotheses as in `rotSymCurvatureOperator`):

* `Ric(∂r, ∂r) = (n-1)·a = -(n-1)·ρ̈/ρ`;
* `Ric(eᵢ, eᵢ) = a + (n-2)·b = -ρ̈/ρ + (n-2)(1-ρ̇²)/ρ²` for tangential `eᵢ`;
* the adapted frame diagonalizes the Ricci tensor; and
* `scal = 2(n-1)·a + (n-1)(n-2)·b = -2(n-1)ρ̈/ρ + (n-1)(n-2)(1-ρ̇²)/ρ²`. -/
theorem rotSymRicciScalar [Fintype ι] [FiniteDimensional ℝ V]
    {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis ι ℝ V) (i₀ : ι)
    (ρ : ℝ → ℝ) (r : ℝ) (hρ : ρ r ≠ 0)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) =
        (-(deriv (deriv ρ) r) / ρ r) * (if i = j then (1 : ℝ) else 0))
    (htan : ∀ i j k l, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → l ≠ i₀ →
      B (e i) (e j) (e k) (e l) = ((1 - deriv ρ r ^ 2) / ρ r ^ 2) *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    (hmix : ∀ i j k, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → B (e i) (e j) (e k) (e i₀) = 0) :
    ricciForm hB (e i₀) (e i₀) =
      ((Fintype.card ι : ℝ) - 1) * (-(deriv (deriv ρ) r) / ρ r) ∧
    (∀ i, i ≠ i₀ → ricciForm hB (e i) (e i) = -(deriv (deriv ρ) r) / ρ r
      + ((Fintype.card ι : ℝ) - 2) * ((1 - deriv ρ r ^ 2) / ρ r ^ 2)) ∧
    (∀ i j, i ≠ j → ricciForm hB (e i) (e j) = 0) ∧
    scalarCurvature hB =
      2 * ((Fintype.card ι : ℝ) - 1) * (-(deriv (deriv ρ) r) / ρ r)
        + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) *
          ((1 - deriv ρ r ^ 2) / ρ r ^ 2) :=
  rotSymRicciDiagonal hB e i₀ _ _ hrad htan hmix

/-! ## Dimension 2: only the radial equation survives -/

/-- **Math.** Petersen §4.2.3, dimension-2 remark, abstract form: on a
surface `dr² + ρ²(r)·dθ²` there are no two distinct tangential indices, so
the tangential Gauss equation is vacuous; the radial Jacobi equation
(`hrad`) and the mixed vanishing (`hmix`) alone force the Kronecker form
with the single eigenvalue `a`, and the sectional curvature of every
2-plane equals `a`. -/
theorem rotSymDim2SectionalConst [Fintype ι] {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis ι ℝ V) (i₀ : ι)
    (hcard : Fintype.card ι = 2) (a : ℝ)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) = a * (if i = j then (1 : ℝ) else 0))
    (hmix : ∀ i j k, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → B (e i) (e j) (e k) (e i₀) = 0) :
    ∀ v w : V, ⟪v, v⟫ = 1 → ⟪w, w⟫ = 1 → ⟪v, w⟫ = 0 →
      sectionalCurvature B v w = a := by
  -- In a two-element index type, all non-radial indices coincide.
  have huniq : ∀ x y : ι, x ≠ i₀ → y ≠ i₀ → x = y := by
    intro x y hx hy
    by_contra hxy
    have h3 : ({x, y, i₀} : Finset ι).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hx]),
        Finset.card_insert_of_notMem (by simp [hy]), Finset.card_singleton]
    have hle : ({x, y, i₀} : Finset ι).card ≤ Fintype.card ι :=
      Finset.card_le_univ _
    rw [hcard, h3] at hle
    omega
  -- Hence the tangential Gauss equation holds vacuously, with eigenvalue `a`.
  have htan : ∀ i j k l, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → l ≠ i₀ →
      B (e i) (e j) (e k) (e l) = a *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)) := by
    intro i j k l hi hj hk hl
    rw [huniq i j hi hj, hB.self_left]
    ring
  intro v w hv hw hvw
  have hmem := rotSymSectionalBounds hB e i₀ a a hrad htan hmix v w hv hw hvw
  rw [min_self, max_self] at hmem
  exact le_antisymm hmem.2 hmem.1

set_option linter.unusedVariables false in
/-- **Math.** Petersen §4.2.3, the `n = 2` case (blueprint anchor): for a
rotationally symmetric surface `dr² + ρ²(r)·dθ²`, the radial Jacobi
equation and the mixed vanishing alone (the tangential Gauss equation is
vacuous in dimension 2) give that every sectional curvature — i.e. the
Gauss curvature — equals `-ρ̈/ρ`. -/
theorem rotSymDim2Curvature [Fintype ι] {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis ι ℝ V) (i₀ : ι)
    (hcard : Fintype.card ι = 2) (ρ : ℝ → ℝ) (r : ℝ) (hρ : ρ r ≠ 0)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) =
        (-(deriv (deriv ρ) r) / ρ r) * (if i = j then (1 : ℝ) else 0))
    (hmix : ∀ i j k, i ≠ i₀ → j ≠ i₀ → k ≠ i₀ → B (e i) (e j) (e k) (e i₀) = 0) :
    ∀ v w : V, ⟪v, v⟫ = 1 → ⟪w, w⟫ = 1 → ⟪v, w⟫ = 0 →
      sectionalCurvature B v w = -(deriv (deriv ρ) r) / ρ r :=
  rotSymDim2SectionalConst hB e i₀ hcard _ hrad hmix

/-! ## The constant-curvature models `ρ = sn_k` -/

/-- **Math.** Petersen §4.2.3 (blueprint anchor): for `ρ = sn_k` the
rotationally symmetric metric `dr² + sn_k²(r)·ds²_{n-1}` has constant
curvature `k`. Both curvature eigenvalues equal `k`:
`-s̈n_k/sn_k = k` since `s̈n_k = -k·sn_k` (the defining ODE), and
`(1 - ṡn_k²)/sn_k² = k` since `ṡn_k = cs_k` and `cs_k² + k·sn_k² = 1`
(the Pythagorean identity); hence, under the three frame equations at a
point with `sn_k(r) ≠ 0`, every sectional curvature equals `k`. -/
theorem snkConstantCurvature [Fintype ι] {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) (e : OrthonormalBasis ι ℝ V) (i₀ : ι)
    (k r : ℝ) (hsn : snFunction k r ≠ 0)
    (hrad : ∀ i j, i ≠ i₀ → j ≠ i₀ →
      B (e i) (e i₀) (e j) (e i₀) =
        (-(deriv (deriv (snFunction k)) r) / snFunction k r) *
          (if i = j then (1 : ℝ) else 0))
    (htan : ∀ i j k' l, i ≠ i₀ → j ≠ i₀ → k' ≠ i₀ → l ≠ i₀ →
      B (e i) (e j) (e k') (e l) =
        ((1 - deriv (snFunction k) r ^ 2) / snFunction k r ^ 2) *
        ((if i = k' then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k' then (1 : ℝ) else 0)))
    (hmix : ∀ i j k', i ≠ i₀ → j ≠ i₀ → k' ≠ i₀ → B (e i) (e j) (e k') (e i₀) = 0) :
    -(deriv (deriv (snFunction k)) r) / snFunction k r = k ∧
    (1 - deriv (snFunction k) r ^ 2) / snFunction k r ^ 2 = k ∧
    ∀ v w : V, ⟪v, v⟫ = 1 → ⟪w, w⟫ = 1 → ⟪v, w⟫ = 0 →
      sectionalCurvature B v w = k := by
  -- The radial eigenvalue: the defining ODE of `sn_k`.
  have ha : -(deriv (deriv (snFunction k)) r) / snFunction k r = k := by
    rw [snFunction_ode k r, neg_mul, neg_neg, mul_div_assoc, div_self hsn, mul_one]
  -- The tangential eigenvalue: the Pythagorean identity.
  have hb : (1 - deriv (snFunction k) r ^ 2) / snFunction k r ^ 2 = k := by
    rw [deriv_snFunction k r]
    have hpyth := csFunction_sq_add_mul_snFunction_sq k r
    have h1 : 1 - csFunction k r ^ 2 = k * snFunction k r ^ 2 := by linarith
    rw [h1, mul_div_assoc, div_self (pow_ne_zero 2 hsn), mul_one]
  refine ⟨ha, hb, ?_⟩
  rw [ha] at hrad
  rw [hb] at htan
  intro v w hv hw hvw
  have hmem := rotSymSectionalBounds hB e i₀ k k hrad htan hmix v w hv hw hvw
  rw [min_self, max_self] at hmem
  exact le_antisymm hmem.2 hmem.1

/-! ## Ricci-flat rotationally symmetric metrics are flat -/

/-- **Math.** Petersen §4.2.3 (blueprint anchor): a Ricci-flat rotationally
symmetric metric `dr² + ρ²(r)·ds²_{n-1}` of dimension `n ≥ 3` is flat: the
warping function is `ρ(r) = a + r` or `ρ(r) = a - r` for some constant `a`.
This is a pure ODE statement: vanishing of the radial Ricci curvature gives
`ρ̈ = 0` (`hric_rad`), so the tangential Ricci equation
`(n-2)(1-ρ̇²)/ρ² - ρ̈/ρ = 0` (`hric_tan`) forces `ρ̇² ≡ 1` (here `n ≥ 3` is
essential). The continuous function `ρ̇` takes values in `{±1}`, so by the
intermediate value theorem on the connected line it is constantly `1` or
constantly `-1`, and integrating (a function with vanishing derivative is
constant) yields `ρ(r) = ρ(0) ± r`. -/
theorem ricciFlatRotSymIsFlat (n : ℕ) (hn : 3 ≤ n) (ρ : ℝ → ℝ)
    (hsm : ContDiff ℝ 2 ρ) (hρ : ∀ r, 0 < ρ r)
    (hric_rad : ∀ r, deriv (deriv ρ) r = 0)
    (hric_tan : ∀ r,
      ((n : ℝ) - 2) * (1 - deriv ρ r ^ 2) / ρ r ^ 2 - deriv (deriv ρ) r / ρ r = 0) :
    ∃ a : ℝ, (∀ r, ρ r = a + r) ∨ (∀ r, ρ r = a - r) := by
  -- Step 1: the Ricci equations force `ρ̇² ≡ 1`.
  have hsq : ∀ r, deriv ρ r ^ 2 = 1 := by
    intro r
    have h := hric_tan r
    rw [hric_rad r, zero_div, sub_zero] at h
    have hpow : ρ r ^ 2 ≠ 0 := pow_ne_zero 2 (hρ r).ne'
    have hn2 : ((n : ℝ) - 2) ≠ 0 := by
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h2 : ((n : ℝ) - 2) * (1 - deriv ρ r ^ 2) = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hpow
    have h4 := (mul_eq_zero.mp h2).resolve_left hn2
    linarith
  have hcont : Continuous (deriv ρ) := hsm.continuous_deriv (by norm_num)
  have hdiff : Differentiable ℝ ρ := hsm.differentiable (by norm_num)
  have hval : ∀ r, deriv ρ r = 1 ∨ deriv ρ r = -1 := fun r => sq_eq_one_iff.mp (hsq r)
  -- Step 2: `ρ̇` is continuous with values in `{±1}`, hence of constant sign
  -- by the intermediate value theorem.
  have hsign : (∀ r, deriv ρ r = 1) ∨ ∀ r, deriv ρ r = -1 := by
    rcases hval 0 with h0 | h0
    · refine Or.inl fun r => (hval r).resolve_right fun h => ?_
      have hmem : (0 : ℝ) ∈ Set.Icc (deriv ρ r) (deriv ρ 0) := by
        rw [h, h0]
        exact ⟨by norm_num, by norm_num⟩
      obtain ⟨c, hc⟩ := intermediate_value_univ r 0 hcont hmem
      have h1 := hsq c
      rw [hc] at h1
      norm_num at h1
    · refine Or.inr fun r => (hval r).resolve_left fun h => ?_
      have hmem : (0 : ℝ) ∈ Set.Icc (deriv ρ 0) (deriv ρ r) := by
        rw [h, h0]
        exact ⟨by norm_num, by norm_num⟩
      obtain ⟨c, hc⟩ := intermediate_value_univ 0 r hcont hmem
      have h1 := hsq c
      rw [hc] at h1
      norm_num at h1
  -- Step 3: integrate `ρ̇ ≡ ±1`.
  rcases hsign with hone | hneg
  · refine ⟨ρ 0, Or.inl fun r => ?_⟩
    have hd0 : ∀ s, deriv (fun t => ρ t - t) s = 0 := by
      intro s
      have h2 : HasDerivAt (fun t : ℝ => ρ t - t) (deriv ρ s - 1) s := by
        simpa using (hdiff s).hasDerivAt.sub (hasDerivAt_id s)
      rw [h2.deriv, hone s, sub_self]
    have hdf : Differentiable ℝ fun t : ℝ => ρ t - t := hdiff.sub differentiable_id
    have hkey : ρ r - r = ρ 0 - 0 := is_const_of_deriv_eq_zero hdf hd0 r 0
    linarith
  · refine ⟨ρ 0, Or.inr fun r => ?_⟩
    have hd0 : ∀ s, deriv (fun t => ρ t + t) s = 0 := by
      intro s
      have h2 : HasDerivAt (fun t : ℝ => ρ t + t) (deriv ρ s + 1) s := by
        simpa using (hdiff s).hasDerivAt.add (hasDerivAt_id s)
      rw [h2.deriv, hneg s]
      norm_num
    have hdf : Differentiable ℝ fun t : ℝ => ρ t + t := hdiff.add differentiable_id
    have hkey : ρ r + r = ρ 0 + 0 := is_const_of_deriv_eq_zero hdf hd0 r 0
    linarith

/-- **Math.** Petersen §4.2.3, the `n = 2` companion of
`ricciFlatRotSymIsFlat`: in dimension 2 the tangential Ricci equation is
absent, and radial Ricci-flatness `ρ̈ ≡ 0` alone only forces the warping
function to be affine, `ρ(r) = a + c·r` (any cone is scalar/Ricci-flat in
dimension 2 away from the tip). `ρ̇` has vanishing derivative, hence is a
constant `c`, and `ρ - c·id` has vanishing derivative, hence is a
constant `a`. -/
theorem ricciFlatRotSymIsFlat_dim2 (ρ : ℝ → ℝ) (hsm : ContDiff ℝ 2 ρ)
    (hric_rad : ∀ r, deriv (deriv ρ) r = 0) :
    ∃ a c : ℝ, ∀ r, ρ r = a + c * r := by
  have hdiff : Differentiable ℝ ρ := hsm.differentiable (by norm_num)
  have hdiff' : Differentiable ℝ (deriv ρ) := by
    have h21 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [h21] at hsm
    exact (contDiff_succ_iff_deriv.mp hsm).2.2.differentiable (by norm_num)
  refine ⟨ρ 0, deriv ρ 0, fun r => ?_⟩
  have hconst : ∀ s, deriv ρ s = deriv ρ 0 := fun s =>
    is_const_of_deriv_eq_zero hdiff' hric_rad s 0
  have hd0 : ∀ s, deriv (fun t => ρ t - deriv ρ 0 * t) s = 0 := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => deriv ρ 0 * t) (deriv ρ 0) s := by
      simpa using (hasDerivAt_id s).const_mul (deriv ρ 0)
    have h2 : HasDerivAt (fun t : ℝ => ρ t - deriv ρ 0 * t)
        (deriv ρ s - deriv ρ 0) s := (hdiff s).hasDerivAt.sub h1
    rw [h2.deriv, hconst s, sub_self]
  have hdf : Differentiable ℝ fun t : ℝ => ρ t - deriv ρ 0 * t :=
    hdiff.sub (differentiable_id.const_mul _)
  have hkey : ρ r - deriv ρ 0 * r = ρ 0 - deriv ρ 0 * 0 :=
    is_const_of_deriv_eq_zero hdf hd0 r 0
  have h0 : deriv ρ 0 * 0 = 0 := mul_zero _
  linarith

end PetersenLib
