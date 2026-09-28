import Topping.ParabolicPDE.Vector

/-!
# Quasilinear jet evaluators

The DeTurck equation has coefficients depending on the value and first jet of
the unknown section.  This file isolates the elementary local Nemytskii
boundary for that situation.  The coefficient and lower-order maps are kept
as explicit hypotheses; no manifold chart or global section-space claim is
made here.
-/

namespace Topping

open scoped BigOperators

noncomputable section

variable {X ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace QuasilinearSecondOrderOperator

variable (P : QuasilinearSecondOrderOperator X ι V)

/-! ## Product-space evaluation -/

/-- Evaluation on separate value, first-jet, and second-jet slots. -/
def applyJetArgs (x : X) (value : V) (first : ι → V)
    (second : ι → ι → V) : V :=
  (∑ i, ∑ k, P.a x value first i k (second i k)) +
    P.lower x value first

@[simp] theorem applyJetArgs_eq_applyJet (x : X)
    (j : VectorSecondOrderJet ι V) :
    P.applyJet x j = P.applyJetArgs x j.value j.first j.second := rfl

omit [Fintype ι] in
private theorem continuous_pi_eval
    {Y : Type*} [TopologicalSpace Y]
    (i : ι) (k : ι) :
    Continuous (fun z : (ι → ι → Y) => z i k) := by
  exact (continuous_apply k).comp (continuous_apply i)

private theorem differentiable_pi_eval
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (i : ι) (k : ι) :
    Differentiable ℝ (fun z : (ι → ι → Y) => z i k) := by
  fun_prop

/-! ## Continuity -/

/-- Continuous coefficient and lower-order maps give a continuous
quasilinear jet evaluator at a fixed base point. -/
theorem continuous_applyJetArgs
    (x : X)
    (ha : ∀ i k, Continuous
      (fun z : V × (ι → V) => P.a x z.1 z.2 i k))
    (hlower : Continuous
      (fun z : V × (ι → V) => P.lower x z.1 z.2)) :
    Continuous (fun z : V × (ι → V) × (ι → ι → V) =>
      P.applyJetArgs x z.1 z.2.1 z.2.2) := by
  let D := V × (ι → V) × (ι → ι → V)
  have hvalue : Continuous (fun z : D => z.1) := continuous_fst
  have hfirst : Continuous (fun z : D => z.2.1) :=
    continuous_fst.comp continuous_snd
  have hsecond : Continuous (fun z : D => z.2.2) :=
    continuous_snd.comp continuous_snd
  have hbase : Continuous (fun z : D => (z.1, z.2.1)) :=
    hvalue.prodMk hfirst
  have ha' : ∀ i k, Continuous
      (fun z : D => P.a x z.1 z.2.1 i k (z.2.2 i k)) := by
    intro i k
    have hcoeff : Continuous
        (fun z : D => P.a x z.1 z.2.1 i k) :=
      (ha i k).comp hbase
    have hjet : Continuous (fun z : D => z.2.2 i k) :=
      (continuous_pi_eval i k).comp hsecond
    exact hcoeff.clm_apply hjet
  have hsumA : Continuous
      (fun z : D => ∑ i, ∑ k,
        P.a x z.1 z.2.1 i k (z.2.2 i k)) := by
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro k hk
    exact ha' i k
  have hLower : Continuous
      (fun z : D => P.lower x z.1 z.2.1) :=
    hlower.comp hbase
  change Continuous (fun z : D =>
    (∑ i, ∑ k, P.a x z.1 z.2.1 i k (z.2.2 i k)) +
      P.lower x z.1 z.2.1)
  exact hsumA.add hLower

/-! ## Differentiability -/

/-- Differentiable coefficient and lower-order maps give a differentiable
quasilinear jet evaluator at a fixed base point. -/
theorem differentiable_applyJetArgs
    (x : X)
    (ha : ∀ i k, Differentiable ℝ
      (fun z : V × (ι → V) => P.a x z.1 z.2 i k))
    (hlower : Differentiable ℝ
      (fun z : V × (ι → V) => P.lower x z.1 z.2)) :
    Differentiable ℝ (fun z : V × (ι → V) × (ι → ι → V) =>
      P.applyJetArgs x z.1 z.2.1 z.2.2) := by
  let D := V × (ι → V) × (ι → ι → V)
  have hvalue : Differentiable ℝ (fun z : D => z.1) := differentiable_fst
  have hfirst : Differentiable ℝ (fun z : D => z.2.1) :=
    differentiable_fst.comp differentiable_snd
  have hsecond : Differentiable ℝ (fun z : D => z.2.2) :=
    differentiable_snd.comp differentiable_snd
  have hbase : Differentiable ℝ (fun z : D => (z.1, z.2.1)) :=
    hvalue.prodMk hfirst
  have ha' : ∀ i k, Differentiable ℝ
      (fun z : D => P.a x z.1 z.2.1 i k (z.2.2 i k)) := by
    intro i k
    have hcoeff : Differentiable ℝ
        (fun z : D => P.a x z.1 z.2.1 i k) :=
      (ha i k).comp hbase
    have hjet : Differentiable ℝ (fun z : D => z.2.2 i k) := by
      fun_prop
    exact hcoeff.clm_apply hjet
  have hsumA : Differentiable ℝ
      (fun z : D => ∑ i, ∑ k,
        P.a x z.1 z.2.1 i k (z.2.2 i k)) := by
    apply Differentiable.fun_sum (u := Finset.univ)
    intro i hi
    apply Differentiable.fun_sum (u := Finset.univ)
    intro k hk
    exact ha' i k
  have hLower : Differentiable ℝ
      (fun z : D => P.lower x z.1 z.2.1) :=
    (hlower.comp hbase)
  change Differentiable ℝ (fun z : D =>
    (∑ i, ∑ k, P.a x z.1 z.2.1 i k (z.2.2 i k)) +
      P.lower x z.1 z.2.1)
  exact hsumA.add hLower

/-! ## The principal-symbol slice of the Frechet derivative -/

/-- The Frechet derivative of the local quasilinear jet evaluator in an
arbitrary pure second-jet direction.  The coefficient and lower-order
differentiability assumptions are kept explicit; this is the local analytic
producer used before a section-space construction.
-/
theorem fderiv_applyJetArgs_second
    (x : X)
    (ha : ∀ i k, Differentiable ℝ
      (fun z : V × (ι → V) => P.a x z.1 z.2 i k))
    (hlower : Differentiable ℝ
      (fun z : V × (ι → V) => P.lower x z.1 z.2))
    (w : X → V) (dw : X → ι → V)
    (secondData secondDir : ι → ι → V) :
    let D := V × (ι → V) × (ι → ι → V)
    let F : D → V := fun z =>
      P.applyJetArgs x z.1 z.2.1 z.2.2
    fderiv ℝ F (w x, dw x, secondData) (0, 0, secondDir) =
      ∑ i, ∑ k, P.a x (w x) (dw x) i k (secondDir i k) := by
  dsimp
  let D := V × (ι → V) × (ι → ι → V)
  let F : D → V := fun z =>
    P.applyJetArgs x z.1 z.2.1 z.2.2
  let z₀ : D := (w x, dw x, secondData)
  let h : D := (0, 0, secondDir)
  have hdiff : Differentiable ℝ F := by
    dsimp [F]
    exact P.differentiable_applyJetArgs x ha hlower
  have hfull : HasFDerivAt F (fderiv ℝ F z₀) z₀ :=
    (hdiff z₀).hasFDerivAt
  let line : ℝ → D := fun s => z₀ + s • h
  have hline : HasDerivAt line h 0 := by
    have hc := (hasDerivAt_const (𝕜 := ℝ) 0 z₀).add
      ((hasDerivAt_id 0).smul_const h)
    convert hc using 1 <;> ext s <;> simp [line, id]
  have hcomp : HasDerivAt (F ∘ line)
      ((fderiv ℝ F z₀) h) 0 := by
    simpa using hfull.comp_hasDerivAt_of_eq 0 hline (by simp [line])
  let q : ι → ι → V := secondDir
  have hterm : ∀ i k, HasDerivAt
      (fun s : ℝ => P.a x (w x) (dw x) i k
        (secondData i k + s • q i k))
      (P.a x (w x) (dw x) i k (q i k)) 0 := by
    intro i k
    have hs : HasDerivAt
        (fun s : ℝ => secondData i k + s • q i k) (q i k) 0 := by
      have hs' := (hasDerivAt_const (𝕜 := ℝ) 0 (secondData i k)).add
        ((hasDerivAt_id 0).smul_const (q i k))
      convert hs' using 1
      · funext s
        simp
      · simp
    simpa [Function.comp_def] using
      (P.a x (w x) (dw x) i k).hasFDerivAt.comp_hasDerivAt 0 hs
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ i, ∑ k,
        P.a x (w x) (dw x) i k (secondData i k + s • q i k))
      (∑ i, ∑ k, P.a x (w x) (dw x) i k (q i k)) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro k hk
    exact hterm i k
  have hline_eq (s : ℝ) :
      line s = (w x, dw x, fun i k => secondData i k + s • q i k) := by
    apply Prod.ext
    · dsimp [line, z₀, h]
      change w x + s • (0 : V) = w x
      simp
    · apply Prod.ext
      · dsimp [line, z₀, h]
        change dw x + s • (0 : ι → V) = dw x
        simp
      · funext i k
        dsimp [line, z₀, h, q]
        change secondData i k + s • (secondDir i k) =
          secondData i k + s • (secondDir i k)
        rfl
  have hexpl : HasDerivAt
      (fun s : ℝ => F (line s))
      (∑ i, ∑ k, P.a x (w x) (dw x) i k (q i k)) 0 := by
    have hadd := hsum.add_const (P.lower x (w x) (dw x))
    have hfun :
        (fun s : ℝ => F (line s)) =
          (fun s : ℝ => ∑ i, ∑ k,
            P.a x (w x) (dw x) i k (secondData i k + s • q i k) +
              P.lower x (w x) (dw x)) := by
      funext s
      rw [hline_eq s]
      simp only [F, applyJetArgs]
    rw [hfun]
    exact hadd
  have heq :
      (fderiv ℝ F z₀) h =
        ∑ i, ∑ k, P.a x (w x) (dw x) i k (q i k) :=
    hcomp.unique hexpl
  rw [heq]

/-- The rank-one second-jet specialization identifies the preceding
directional derivative with the quasilinear linearisation symbol. -/
theorem fderiv_applyJetArgs_rankOne_second
    (x : X)
    (ha : ∀ i k, Differentiable ℝ
      (fun z : V × (ι → V) => P.a x z.1 z.2 i k))
    (hlower : Differentiable ℝ
      (fun z : V × (ι → V) => P.lower x z.1 z.2))
    (w : X → V) (dw : X → ι → V)
    (secondData : ι → ι → V) (xi : ι → ℝ) (v : V) :
    let D := V × (ι → V) × (ι → ι → V)
    let F : D → V := fun z =>
      P.applyJetArgs x z.1 z.2.1 z.2.2
    fderiv ℝ F (w x, dw x, secondData)
        (0, 0, fun i k => (xi i * xi k) • v) =
      P.linearisationSymbol w dw x xi v := by
  have h := P.fderiv_applyJetArgs_second x ha hlower w dw secondData
    (fun i k => (xi i * xi k) • v)
  simpa [linearisationSymbol] using h

end QuasilinearSecondOrderOperator

end
end Topping
