import PetersenLib.Ch03.RiemannConstantCurvature
import PetersenLib.Ch03.ScalarFormulas

/-!
# Petersen Ch. 3, §3.1.4 — Einstein 3-manifolds have constant curvature

In dimension `3` the Ricci curvature determines the sectional curvature
(Petersen §3.1.4, the corollary
`cor:pet-ch3-ricci-determines-sec-low-dim`): `(M,g)` is Einstein with
Einstein constant `k` iff it has constant curvature `k/2`.

For `⟸`, constant curvature `k/2` forces the Einstein condition with Einstein
constant `(n−1)·(k/2) = k` when `n = 3` (`constantCurvature_isEinstein`).

For `⟹`, fix `p ∈ M` and a `g`-orthonormal basis `e₁, e₂, e₃` of `T_pM`. The
trace formula `Ric(eₘ,eₘ) = ∑_{i≠m} sec(eₘ,eᵢ)` turns the diagonal Einstein
equations into the linear system
`sec(e₁,e₂) + sec(e₁,e₃) = sec(e₂,e₁) + sec(e₂,e₃) = sec(e₃,e₁) + sec(e₃,e₂) = k`,
whose unique solution is `sec(eᵢ,eⱼ) = k/2` for all `i ≠ j`; the off-diagonal
Einstein equations `Ric(eⱼ,eₗ) = 0` (for `j ≠ l`) kill the curvature
components `R⁴(eᵢ,eⱼ,eᵢ,eₗ)` with three distinct indices. Hence the
difference `D = R⁴ − (−k/2)·g(·∧·,·∧·)` — an algebraic curvature form —
vanishes on all basis 4-tuples, so `D ≡ 0`
(`IsAlgCurvatureForm.eq_zero_of_basis`), giving the diagonal identity
`R⁴(x,y,x,y) = −(k/2)·g(x∧y,x∧y)` for **all** pairs and thus `sec ≡ k/2`
(`sectionalCurvature_const_of_diag`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.4.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** The substantial half of Petersen §3.1.4's corollary in dimension
`3`: an **Einstein** 3-manifold with Einstein constant `k` has **constant
curvature** `k/2`. At each `p ∈ M` pick a `g`-orthonormal basis `e₁, e₂, e₃`
of `T_pM`. By the trace formula `Ric(eₘ,eₘ) = ∑_{i≠m} sec(eₘ,eᵢ)` the diagonal
Einstein equations form the linear system `sec(eᵢ,eⱼ) + sec(eᵢ,eₘ) = k` over
the three coordinate planes, forcing `sec(eᵢ,eⱼ) = k/2` for `i ≠ j`, and the
off-diagonal equations `Ric(eⱼ,eₗ) = 0` force `R⁴(eᵢ,eⱼ,eᵢ,eₗ) = 0` for
pairwise distinct `i,j,l`. Hence `R⁴ + (k/2)·g(·∧·,·∧·)` is an algebraic
curvature form vanishing on all basis 4-tuples, so it vanishes identically,
and the diagonal identity `R⁴(x,y,x,y) = −(k/2)·g(x∧y,x∧y)` yields
`sec ≡ k/2`. -/
theorem hasConstantCurvature_of_isEinstein_of_finrank_three
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) {k : ℝ}
    (hdim : Module.finrank ℝ E = 3) (hE : IsEinstein D k) :
    HasConstantCurvature D (k / 2) := by
  intro p v w hvw
  classical
  -- A `g`-orthonormal basis of the 3-dimensional tangent space, over `Fin 3`.
  have hfr : Module.finrank ℝ (TangentSpace I p) = 3 := by
    have h0 : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
    rw [h0, hdim]
  obtain ⟨c, hc⟩ : ∃ c : Module.Basis (Fin 3) ℝ (TangentSpace I p),
      ∀ i j, g.metricInner p (c i) (c j) = if i = j then 1 else 0 := by
    obtain ⟨b, hb⟩ := exists_metricOrthonormalBasis g p
    refine ⟨b.reindex (finCongr hfr), fun i j => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    by_cases hij : i = j
    · rw [hij, if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hij ((finCongr hfr).symm.injective h)), if_neg hij]
  -- The algebraic-curvature-form players.
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  have hG : ∀ a b : TangentSpace I p,
      g.metricBilin p a b = g.metricBilin p b a :=
    fun a b => g.metricInner_comm p a b
  have hB' : IsAlgCurvatureForm (fun x y z t : TangentSpace I p =>
      -(k / 2) * bivectorPairing (g.metricBilin p) x y z t) :=
    (isAlgCurvatureForm_bivectorPairing (g.metricBilin p) hG).smul (-(k / 2))
  have hD : IsAlgCurvatureForm (fun x y z t : TangentSpace I p =>
      curvatureTensorFourAt D p x y z t
        - -(k / 2) * bivectorPairing (g.metricBilin p) x y z t) :=
    hAlg.sub hB'
  -- Step 1: the diagonal Einstein equations give `sec(eᵢ,eⱼ) = k/2`.
  have hric_diag : ∀ m : Fin 3,
      RicciCurvature D.toAffineConnection p (c m) (c m) = k := by
    intro m
    rw [hE p (c m) (c m), hc m m, if_pos rfl, mul_one]
  have hthird : ∀ i j : Fin 3, i ≠ j → ∃ m : Fin 3, i ≠ m ∧ j ≠ m ∧
      (Finset.univ : Finset (Fin 3)).erase i = {j, m} ∧
      (Finset.univ : Finset (Fin 3)).erase j = {i, m} ∧
      (Finset.univ : Finset (Fin 3)).erase m = {i, j} := by decide
  have hsec : ∀ i j : Fin 3, i ≠ j →
      sectionalCurvature D p (c i) (c j) = k / 2 := by
    intro i j hij
    obtain ⟨m, him, hjm, hei, hej, hem⟩ := hthird i j hij
    have hsi := ricciCurvature_eq_sum_sectionalCurvature D p c hc i
    have hsj := ricciCurvature_eq_sum_sectionalCurvature D p c hc j
    have hsm := ricciCurvature_eq_sum_sectionalCurvature D p c hc m
    rw [hric_diag i, hei, Finset.sum_pair hjm] at hsi
    rw [hric_diag j, hej, Finset.sum_pair him] at hsj
    rw [hric_diag m, hem, Finset.sum_pair hij] at hsm
    have h1 := sectionalCurvature_comm D p (c i) (c j)
    have h2 := sectionalCurvature_comm D p (c i) (c m)
    have h3 := sectionalCurvature_comm D p (c j) (c m)
    linarith
  -- Step 2: `sec(eᵢ,eⱼ) = k/2` in `(0,4)`-tensor form on the diagonal pairs.
  have hdiagB : ∀ i j : Fin 3, i ≠ j →
      curvatureTensorFourAt D p (c i) (c j) (c i) (c j) = -(k / 2) := by
    intro i j hij
    have hs := hsec i j hij
    rw [sectionalCurvature_eq_curvatureTensorFourAt] at hs
    have hbip : bivectorInnerProduct g p (c i) (c j) (c i) (c j) = 1 := by
      simp only [bivectorInnerProduct, hc]
      simp [hij, Ne.symm hij]
    rw [hbip, div_one] at hs
    have h12 : curvatureTensorFourAt D p (c j) (c i) (c i) (c j)
        = -curvatureTensorFourAt D p (c i) (c j) (c i) (c j) :=
      hAlg.antisymm₁₂ (c j) (c i) (c i) (c j)
    linarith
  have hdiagP : ∀ i j : Fin 3, i ≠ j →
      bivectorPairing (g.metricBilin p) (c i) (c j) (c i) (c j) = 1 := by
    intro i j hij
    simp only [bivectorPairing, RiemannianMetric.metricBilin_apply, hc]
    simp [hij, Ne.symm hij]
  -- Step 3: the off-diagonal Einstein equations kill the three-distinct-index
  -- components.
  have huniv3 : ∀ a b d : Fin 3, a ≠ b → a ≠ d → b ≠ d →
      (Finset.univ : Finset (Fin 3)) = {a, b, d} := by decide
  have hoffB : ∀ a b d : Fin 3, a ≠ b → a ≠ d → b ≠ d →
      curvatureTensorFourAt D p (c a) (c b) (c a) (c d) = 0 := by
    intro a b d hab had hbd
    have hsum := ricciCurvature_eq_sum D p c hc (c b) (c d)
    rw [hE p (c b) (c d), hc b d, if_neg hbd, mul_zero,
      huniv3 a b d hab had hbd,
      Finset.sum_insert (by simp [hab, had]),
      Finset.sum_insert (by simp [hbd]),
      Finset.sum_singleton] at hsum
    have hzb : curvatureTensorFourAt D p (c b) (c b) (c d) (c b) = 0 :=
      hAlg.self_left (c b) (c d) (c b)
    have hzd : curvatureTensorFourAt D p (c d) (c b) (c d) (c d) = 0 :=
      hAlg.self_right (c d) (c b) (c d)
    have h34 : curvatureTensorFourAt D p (c a) (c b) (c a) (c d)
        = -curvatureTensorFourAt D p (c a) (c b) (c d) (c a) :=
      hAlg.antisymm₃₄ (c a) (c b) (c a) (c d)
    linarith
  have hoffP : ∀ a b d : Fin 3, a ≠ b → a ≠ d → b ≠ d →
      bivectorPairing (g.metricBilin p) (c a) (c b) (c a) (c d) = 0 := by
    intro a b d hab had hbd
    simp only [bivectorPairing, RiemannianMetric.metricBilin_apply, hc]
    simp [hbd, had, Ne.symm hab]
  -- Step 4: the difference form vanishes on the two normalized shapes.
  have hDdiag : ∀ i j : Fin 3, i ≠ j →
      curvatureTensorFourAt D p (c i) (c j) (c i) (c j)
        - -(k / 2) * bivectorPairing (g.metricBilin p) (c i) (c j) (c i) (c j)
        = 0 := by
    intro i j hij
    rw [hdiagB i j hij, hdiagP i j hij]
    ring
  have hDoff : ∀ a b d : Fin 3, a ≠ b → a ≠ d → b ≠ d →
      curvatureTensorFourAt D p (c a) (c b) (c a) (c d)
        - -(k / 2) * bivectorPairing (g.metricBilin p) (c a) (c b) (c a) (c d)
        = 0 := by
    intro a b d hab had hbd
    rw [hoffB a b d hab had hbd, hoffP a b d hab had hbd]
    ring
  -- Step 5: the difference form vanishes on all basis 4-tuples, by the
  -- curvature symmetries and 3-element index combinatorics.
  have hcomp : ∀ i j m l : Fin 3,
      curvatureTensorFourAt D p (c i) (c j) (c m) (c l)
        - -(k / 2) * bivectorPairing (g.metricBilin p) (c i) (c j) (c m) (c l)
        = 0 := by
    intro i j m l
    by_cases hij : i = j
    · rw [hij]
      exact hD.self_left (c j) (c m) (c l)
    by_cases hml : m = l
    · rw [hml]
      exact hD.self_right (c i) (c j) (c l)
    by_cases hmi : m = i
    · rw [hmi]
      by_cases hlj : l = j
      · rw [hlj]
        exact hDdiag i j hij
      · exact hDoff i j l hij (fun h => hml (hmi.trans h)) (Ne.symm hlj)
    by_cases hmj : m = j
    · rw [hmj]
      by_cases hli : l = i
      · rw [hli]
        have h1 : curvatureTensorFourAt D p (c i) (c j) (c j) (c i)
            - -(k / 2) * bivectorPairing (g.metricBilin p)
                (c i) (c j) (c j) (c i)
            = -(curvatureTensorFourAt D p (c i) (c j) (c i) (c j)
              - -(k / 2) * bivectorPairing (g.metricBilin p)
                  (c i) (c j) (c i) (c j)) :=
          hD.antisymm₃₄ (c i) (c j) (c j) (c i)
        rw [h1, hDdiag i j hij, neg_zero]
      · have h1 : curvatureTensorFourAt D p (c i) (c j) (c j) (c l)
            - -(k / 2) * bivectorPairing (g.metricBilin p)
                (c i) (c j) (c j) (c l)
            = -(curvatureTensorFourAt D p (c j) (c i) (c j) (c l)
              - -(k / 2) * bivectorPairing (g.metricBilin p)
                  (c j) (c i) (c j) (c l)) :=
          hD.antisymm₁₂ (c i) (c j) (c j) (c l)
        rw [h1, hDoff j i l (Ne.symm hij) (fun h => hml (hmj.trans h))
          (fun h => hli h.symm), neg_zero]
    by_cases hli : l = i
    · rw [hli]
      have h1 : curvatureTensorFourAt D p (c i) (c j) (c m) (c i)
          - -(k / 2) * bivectorPairing (g.metricBilin p)
              (c i) (c j) (c m) (c i)
          = -(curvatureTensorFourAt D p (c i) (c j) (c i) (c m)
            - -(k / 2) * bivectorPairing (g.metricBilin p)
                (c i) (c j) (c i) (c m)) :=
        hD.antisymm₃₄ (c i) (c j) (c m) (c i)
      rw [h1, hDoff i j m hij (fun h => hmi h.symm) (fun h => hmj h.symm),
        neg_zero]
    by_cases hlj : l = j
    · rw [hlj]
      have h1 : curvatureTensorFourAt D p (c i) (c j) (c m) (c j)
          - -(k / 2) * bivectorPairing (g.metricBilin p)
              (c i) (c j) (c m) (c j)
          = -(curvatureTensorFourAt D p (c i) (c j) (c j) (c m)
            - -(k / 2) * bivectorPairing (g.metricBilin p)
                (c i) (c j) (c j) (c m)) :=
        hD.antisymm₃₄ (c i) (c j) (c m) (c j)
      have h2 : curvatureTensorFourAt D p (c i) (c j) (c j) (c m)
          - -(k / 2) * bivectorPairing (g.metricBilin p)
              (c i) (c j) (c j) (c m)
          = -(curvatureTensorFourAt D p (c j) (c i) (c j) (c m)
            - -(k / 2) * bivectorPairing (g.metricBilin p)
                (c j) (c i) (c j) (c m)) :=
        hD.antisymm₁₂ (c i) (c j) (c j) (c m)
      have h3 := hDoff j i m (Ne.symm hij) (fun h => hmj h.symm)
        (fun h => hmi h.symm)
      linarith
    · -- four pairwise distinct indices are impossible in `Fin 3`
      exfalso
      have e1 : i.val ≠ j.val := fun h => hij (Fin.val_injective h)
      have e2 : m.val ≠ l.val := fun h => hml (Fin.val_injective h)
      have e3 : m.val ≠ i.val := fun h => hmi (Fin.val_injective h)
      have e4 : m.val ≠ j.val := fun h => hmj (Fin.val_injective h)
      have e5 : l.val ≠ i.val := fun h => hli (Fin.val_injective h)
      have e6 : l.val ≠ j.val := fun h => hlj (Fin.val_injective h)
      have b1 : i.val < 3 := i.isLt
      have b2 : j.val < 3 := j.isLt
      have b3 : m.val < 3 := m.isLt
      have b4 : l.val < 3 := l.isLt
      omega
  -- Step 6: hence the difference form vanishes identically, giving the
  -- diagonal identity for all pairs, and `sec ≡ k/2`.
  have hzero : ∀ x y z t : TangentSpace I p,
      curvatureTensorFourAt D p x y z t
        - -(k / 2) * bivectorPairing (g.metricBilin p) x y z t = 0 :=
    fun x y z t => hD.eq_zero_of_basis c hcomp x y z t
  have hdiagAll : ∀ x y : TangentSpace I p,
      curvatureTensorFourAt D p x y x y
        = -(k / 2) * bivectorInnerProduct g p x y x y := by
    intro x y
    have h := hzero x y x y
    rw [bivectorInnerProduct_eq_bivectorPairing]
    linarith
  exact sectionalCurvature_const_of_diag D p (k / 2) hdiagAll v w hvw

/-- **Math.** **In dimension 3 the Ricci curvature determines the sectional
curvature** (Petersen §3.1.4, corollary): a Riemannian 3-manifold is Einstein
with Einstein constant `k` iff it has constant curvature `k/2`. The forward
direction is `hasConstantCurvature_of_isEinstein_of_finrank_three`; the
converse is `constantCurvature_isEinstein` with `(n−1)·(k/2) = k` for
`n = 3`. -/
theorem einstein_iff_hasConstantCurvature_of_finrank_three
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) (k : ℝ)
    (hdim : Module.finrank ℝ E = 3) :
    IsEinstein D k ↔ HasConstantCurvature D (k / 2) := by
  constructor
  · exact hasConstantCurvature_of_isEinstein_of_finrank_three D hdim
  · intro h
    have h1 := constantCurvature_isEinstein D h
    have hck : ((Module.finrank ℝ E : ℝ) - 1) * (k / 2) = k := by
      rw [hdim]
      push_cast
      ring
    rwa [hck] at h1

end PetersenLib
