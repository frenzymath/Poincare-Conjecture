import Mathlib

/-!
# Chapter 4: vector-bundle principal symbols

This file contains the algebraic, source-faithful core of Topping's vector
bundle discussion.  The base and covector types are deliberately abstract:
the geometric chart and cosphere-bundle producers can be supplied by a later
manifold PDE development without changing these definitions.
-/

namespace Topping

noncomputable section

open scoped RealInnerProductSpace

/-! ## Local coefficient data and the vector principal symbol -/

variable {X ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The coefficient data of a linear second-order system in a local frame.

The index type `ι` represents the spatial coordinate indices.  The values are
continuous linear maps on the fibre, so this definition keeps the
`a^(ij)_(ab)`, `b^i_(ab)`, and `c_(ab)` of (4.3.1) without choosing a basis of
the fibre. -/
structure VectorSecondOrderCoefficients (X ι V : Type*) [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  a : X → ι → ι → V →L[ℝ] V
  b : X → ι → V →L[ℝ] V
  c : X → V →L[ℝ] V

/-- A second-order jet in a local frame. -/
structure VectorSecondOrderJet (ι V : Type*) [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  value : V
  first : ι → V
  second : ι → ι → V

namespace VectorSecondOrderCoefficients

variable (A : VectorSecondOrderCoefficients X ι V)

/-- Evaluation of the local operator on a formal second-order jet. -/
def applyJet (x : X) (j : VectorSecondOrderJet ι V) : V :=
  (∑ i, ∑ k, A.a x i k (j.second i k))
    + (∑ i, A.b x i (j.first i)) + A.c x j.value

/-- The principal symbol, as a fibre endomorphism, obtained by retaining the
quadratic spatial derivatives. -/
def principalSymbol (x : X) (ξ : ι → ℝ) : V →L[ℝ] V :=
  ∑ i, ∑ k, (ξ i * ξ k) • A.a x i k

@[simp] theorem principalSymbol_apply (x : X) (xi : ι → ℝ) (v : V) :
    A.principalSymbol x xi v =
      ∑ i, ∑ k, (xi i * xi k) • A.a x i k v := by
  simp [principalSymbol]

/-- Formal jet of `e^(s phi) v` after the common exponential factor has been
removed.  `firstData` and `secondData` are the derivatives of the amplitude,
and `phiSecond` is the second derivative of the phase. -/
def exponentialJet (s : ℝ) (xi : ι → ℝ) (v : V)
    (firstData : ι → V) (secondData : ι → ι → V)
    (phiSecond : ι → ι → ℝ) : VectorSecondOrderJet ι V where
  value := v
  first := fun i => (s * xi i) • v + firstData i
  second := fun i k =>
    (s ^ 2 * xi i * xi k) • v +
      s • (xi i • firstData k + xi k • firstData i + phiSecond i k • v) +
      secondData i k

def exponentialLinearTerm (x : X) (xi : ι → ℝ) (v : V)
    (firstData : ι → V) (phiSecond : ι → ι → ℝ) : V :=
  (∑ i, ∑ k,
      A.a x i k
        (xi i • firstData k + xi k • firstData i + phiSecond i k • v)) +
    ∑ i, A.b x i (xi i • v)

def exponentialConstantTerm (x : X) (v : V)
    (firstData : ι → V) (secondData : ι → ι → V) : V :=
  (∑ i, ∑ k, A.a x i k (secondData i k)) +
    (∑ i, A.b x i (firstData i)) + A.c x v

/-- The exponential-conjugation expansion underlying Topping's formula
(4.3.3).  After the common exponential factor is removed, the quadratic term
is the principal symbol and all remaining terms have degree at most one in
the conjugation parameter. -/
theorem applyJet_exponentialJet_eq_quadratic_plus_lower
    (x : X) (s : ℝ) (xi : ι → ℝ) (v : V)
    (firstData : ι → V) (secondData : ι → ι → V)
    (phiSecond : ι → ι → ℝ) :
    A.applyJet x
        (exponentialJet s xi v firstData secondData phiSecond) =
      s ^ 2 • A.principalSymbol x xi v +
        s • A.exponentialLinearTerm x xi v firstData phiSecond +
        A.exponentialConstantTerm x v firstData secondData := by
  simp only [applyJet, exponentialJet, principalSymbol_apply,
    exponentialLinearTerm, exponentialConstantTerm, map_add, map_smul,
    Finset.sum_add_distrib, Finset.smul_sum, smul_add]
  simp only [smul_smul, mul_assoc]
  abel

/-- A vector-valued quadratic polynomial, normalized by `s⁻²`, converges
to its quadratic coefficient as `s → ∞`. -/
theorem tendsto_normalized_quadratic_vector_polynomial
    {q r t : V} :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 • (s ^ 2 • q + s • r + t))
      Filter.atTop (nhds q) := by
  have hinv : Filter.Tendsto (fun s : ℝ => s⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv2 : Filter.Tendsto (fun s : ℝ => s⁻¹ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa [pow_two] using hinv.mul hinv
  have hlin : Filter.Tendsto (fun s : ℝ => s⁻¹ • r)
      Filter.atTop (nhds 0) := by
    simpa using hinv.smul_const r
  have hquad : Filter.Tendsto (fun s : ℝ => s⁻¹ ^ 2 • t)
      Filter.atTop (nhds 0) := by
    simpa using hinv2.smul_const t
  have hconst : Filter.Tendsto (fun _ : ℝ => q)
      Filter.atTop (nhds q) :=
    tendsto_const_nhds
  have hsum :
      Filter.Tendsto (fun s : ℝ => q + s⁻¹ • r + s⁻¹ ^ 2 • t)
        Filter.atTop (nhds q) := by
    simpa using (hconst.add hlin).add hquad
  apply hsum.congr'
  filter_upwards [Filter.eventually_atTop.2
      ⟨(1 : ℝ), fun s hs => ne_of_gt (lt_of_lt_of_le zero_lt_one hs)⟩] with s hs
  have hquadCoeff : s⁻¹ ^ 2 * s ^ 2 = 1 := by
    field_simp [hs]
  have hlinearCoeff : s⁻¹ ^ 2 * s = s⁻¹ := by
    field_simp [hs]
  simp only [smul_add, smul_smul, hquadCoeff, hlinearCoeff, one_smul]

/-- The normalized exponential-conjugation expression converges to the vector
principal symbol.  This is the formal local-frame version of (4.3.3). -/
theorem exponentialJet_normalized_tendsto
    (x : X) (xi : ι → ℝ) (v : V)
    (firstData : ι → V) (secondData : ι → ι → V)
    (phiSecond : ι → ι → ℝ) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 • A.applyJet x
        (exponentialJet s xi v firstData secondData phiSecond))
      Filter.atTop (nhds (A.principalSymbol x xi v)) := by
  simpa only [applyJet_exponentialJet_eq_quadratic_plus_lower] using
    (tendsto_normalized_quadratic_vector_polynomial
      (q := A.principalSymbol x xi v)
      (r := A.exponentialLinearTerm x xi v firstData phiSecond)
      (t := A.exponentialConstantTerm x v firstData secondData))

/-- Topping's vector principal-symbol limit formula (4.3.3), in the formal
local-frame jet model. -/
theorem vectorPrincipalSymbol_limit
    (x : X) (xi : ι → ℝ) (v : V)
    (firstData : ι → V) (secondData : ι → ι → V)
    (phiSecond : ι → ι → ℝ) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 • A.applyJet x
        (exponentialJet s xi v firstData secondData phiSecond))
      Filter.atTop (nhds (A.principalSymbol x xi v)) :=
  A.exponentialJet_normalized_tendsto x xi v firstData secondData phiSecond

end VectorSecondOrderCoefficients

/-! ## Strict parabolicity -/

/-- The elementary properties required of a squared covector norm.

The zero value and degree-two homogeneity clauses rule out a merely positive
gauge.  The remaining positivity clauses are the fibrewise norm properties
needed by the strict-parabolicity inequality. -/
def IsSquaredCovectorNorm
    (q : X → (ι → ℝ) → ℝ) : Prop :=
  (∀ x, q x 0 = 0) ∧
    (∀ x xi, 0 ≤ q x xi) ∧
    (∀ x xi, xi ≠ 0 → 0 < q x xi) ∧
    (∀ x r xi, q x (r • xi) = r ^ 2 * q x xi)

/-- Topping's strong (strict) parabolicity inequality (4.3.4).

`q x ξ` is the squared covector norm.  Keeping it as an explicit function
allows this algebraic core to be reused with a Riemannian cotangent bundle;
`IsSquaredCovectorNorm q` records zero, positivity, and degree-two
homogeneity. -/
def StrictlyParabolic
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (q : X → (ι → ℝ) → ℝ) : Prop :=
  IsSquaredCovectorNorm q ∧
    ∃ lam : ℝ, 0 < lam ∧
      ∀ (x : X) (xi : ι → ℝ) (v : V),
        lam * q x xi * ‖v‖ ^ 2 ≤ inner ℝ (sigma x xi v) v

/-- A symbol is a positive multiple of the identity at each covector. -/
def IsPositiveMultipleOfIdentity
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) : Prop :=
  ∀ (x : X) (xi : ι → ℝ), xi ≠ 0 →
    ∃ mu : ℝ, 0 < mu ∧ sigma x xi = mu • ContinuousLinearMap.id ℝ V

/-- A positive-identity symbol together with the uniform lower bound needed to
turn pointwise positivity into (4.3.4).  On a closed manifold the lower bound
is normally obtained by minimizing on the unit cosphere; here it is kept as an
explicit, non-tautological compactness/continuity output. -/
def HasUniformPositiveMultiple
    (sigma : X → (ι → ℝ) → V →L[ℝ] V)
    (q : X → (ι → ℝ) → ℝ) : Prop :=
  ∃ mu : X → (ι → ℝ) → ℝ,
    (∀ x xi, sigma x xi = mu x xi • ContinuousLinearMap.id ℝ V) ∧
    (∀ x xi, xi ≠ 0 → 0 < mu x xi) ∧
    (∃ lam : ℝ, 0 < lam ∧ ∀ x xi, lam * q x xi ≤ mu x xi)

omit [Fintype ι] in
/-- A uniformly positive identity-multiple symbol satisfies the coercivity
inequality for any second fibre inner product carried by
`InnerProductSpace.Core`.  The same lower-bound constant works because both
sides acquire the new squared norm as a common nonnegative factor.  This is
metric independence for identity-multiple symbols, not for arbitrary symbols. -/
theorem HasUniformPositiveMultiple.coercive_inequality_for_core
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    {q : X → (ι → ℝ) → ℝ}
    (h : HasUniformPositiveMultiple sigma q)
    (newMetric : InnerProductSpace.Core ℝ V) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ (x : X) (xi : ι → ℝ) (v : V),
        lam * q x xi * newMetric.inner v v ≤
          newMetric.inner (sigma x xi v) v := by
  obtain ⟨mu, hsymbol, _hpos, lam, hlam, hlower⟩ := h
  refine ⟨lam, hlam, ?_⟩
  intro x xi v
  rw [hsymbol x xi]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  rw [show newMetric.inner (mu x xi • v) v =
      mu x xi * newMetric.inner v v by
    simpa using newMetric.smul_left v v (mu x xi)]
  exact mul_le_mul_of_nonneg_right (hlower x xi) (by
    simpa using newMetric.re_inner_nonneg v)

omit [Fintype ι] in
theorem StrictlyParabolic.of_hasUniformPositiveMultiple
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    {q : X → (ι → ℝ) → ℝ}
    (hq : IsSquaredCovectorNorm q)
    (h : HasUniformPositiveMultiple sigma q) :
    StrictlyParabolic sigma q := by
  obtain ⟨mu, hsymbol, _hpos, hlam⟩ := h
  obtain ⟨lam, hlam_pos, hlam_lower⟩ := hlam
  refine ⟨hq, ⟨lam, hlam_pos, ?_⟩⟩
  intro x xi v
  rw [hsymbol x xi]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  rw [real_inner_smul_self_left, pow_two]
  have hv : 0 ≤ ‖v‖ * ‖v‖ := mul_self_nonneg _
  exact mul_le_mul_of_nonneg_right (hlam_lower x xi) hv

omit [Fintype ι] in
/-- Coercivity transfers from the ambient fibre metric to a second genuine
inner product when explicit uniform comparison constants are available.

The second metric is carried by `InnerProductSpace.Core`, so it does not
compete with the ambient norm and inner-product instances.  Its squared norm
is written as `newMetric.inner v v`.  The three comparison hypotheses control
the covector square, the fibre-vector square, and the symbol pairing in the
directions used by the parabolicity inequality. -/
theorem StrictlyParabolic.coercive_inequality_of_core_comparison
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    {qOld qNew : X → (ι → ℝ) → ℝ}
    (hOld : StrictlyParabolic sigma qOld)
    (newMetric : InnerProductSpace.Core ℝ V)
    (hqNew : IsSquaredCovectorNorm qNew)
    {cV cDual cPair : ℝ}
    (hcV : 0 < cV) (hcDual : 0 < cDual) (hcPair : 0 < cPair)
    (hVector : ∀ v, newMetric.inner v v ≤ cV * ‖v‖ ^ 2)
    (hCovector : ∀ x xi, qNew x xi ≤ cDual * qOld x xi)
    (hPair : ∀ x xi v,
      cPair * inner ℝ (sigma x xi v) v ≤
        newMetric.inner (sigma x xi v) v) :
    ∃ lamNew : ℝ, 0 < lamNew ∧
      ∀ (x : X) (xi : ι → ℝ) (v : V),
        lamNew * qNew x xi * newMetric.inner v v ≤
          newMetric.inner (sigma x xi v) v := by
  obtain ⟨_hqOld, lam, hlam, hcoercive⟩ := hOld
  let lamNew := cPair * lam / (cDual * cV)
  have hlamNew : 0 < lamNew := by
    exact div_pos (mul_pos hcPair hlam) (mul_pos hcDual hcV)
  refine ⟨lamNew, hlamNew, ?_⟩
  intro x xi v
  have hqNew_nonneg : 0 ≤ qNew x xi := hqNew.2.1 x xi
  have hproduct :
      qNew x xi * newMetric.inner v v ≤
        (cDual * qOld x xi) * (cV * ‖v‖ ^ 2) := by
    have := mul_le_mul (hVector v) (hCovector x xi) hqNew_nonneg
      (mul_nonneg hcV.le (sq_nonneg ‖v‖))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hscaled := mul_le_mul_of_nonneg_left hproduct hlamNew.le
  have hcoeff :
      lamNew * ((cDual * qOld x xi) * (cV * ‖v‖ ^ 2)) =
        cPair * (lam * qOld x xi * ‖v‖ ^ 2) := by
    dsimp [lamNew]
    field_simp [hcDual.ne', hcV.ne']
  calc
    lamNew * qNew x xi * newMetric.inner v v =
        lamNew * (qNew x xi * newMetric.inner v v) := by ring
    _ ≤ lamNew * ((cDual * qOld x xi) * (cV * ‖v‖ ^ 2)) := hscaled
    _ = cPair * (lam * qOld x xi * ‖v‖ ^ 2) := hcoeff
    _ ≤ cPair * inner ℝ (sigma x xi v) v :=
      mul_le_mul_of_nonneg_left (hcoercive x xi v) hcPair.le
    _ ≤ newMetric.inner (sigma x xi v) v := hPair x xi v

/-- The model symbol of a connection Laplacian. -/
def connectionLaplacianSymbol
    (q : X → (ι → ℝ) → ℝ) : X → (ι → ℝ) → V →L[ℝ] V :=
  fun x ξ => q x ξ • ContinuousLinearMap.id ℝ V

omit [Fintype ι] in
@[simp] theorem connectionLaplacianSymbol_apply
    (q : X → (ι → ℝ) → ℝ) (x : X) (xi : ι → ℝ) (v : V) :
    connectionLaplacianSymbol q x xi v = q x xi • v := by
  simp [connectionLaplacianSymbol]

omit [Fintype ι] in
theorem connectionLaplacianSymbol_strictlyParabolic
    (q : X → (ι → ℝ) → ℝ)
    (hq : IsSquaredCovectorNorm q) :
    StrictlyParabolic (X := X) (ι := ι) (V := V)
      (connectionLaplacianSymbol q) q := by
  refine ⟨hq, ⟨1, by norm_num, ?_⟩⟩
  intro x xi v
  simp [connectionLaplacianSymbol]
  rw [real_inner_smul_self_left, pow_two]

/-! ## Quasilinear systems -/

/-- Coefficient data for the quasilinear equation (4.3.5).

The first two arguments after `x` stand for the value and first derivative of a
section.  The map `a` is the principal coefficient depending on those lower
jets; `lower` collects all terms of order at most one. -/
structure QuasilinearSecondOrderOperator (X ι V : Type*) [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  a : X → V → (ι → V) → ι → ι → V →L[ℝ] V
  lower : X → V → (ι → V) → V

namespace QuasilinearSecondOrderOperator

variable (P : QuasilinearSecondOrderOperator X ι V)

/-- Evaluation of the quasilinear operator (4.3.5) on a formal second-order
jet.  The principal coefficients are evaluated at the value and first-order
parts of the jet; `lower` contains no second-jet dependence. -/
def applyJet (x : X) (j : VectorSecondOrderJet ι V) : V :=
  (∑ i, ∑ k, P.a x j.value j.first i k (j.second i k)) +
    P.lower x j.value j.first

/-- The principal symbol of the linearisation at a fixed lower jet. -/
def linearisationSymbol (w : X → V) (dw : X → ι → V)
    (x : X) (ξ : ι → ℝ) : V →L[ℝ] V :=
  ∑ i, ∑ k, (ξ i * ξ k) • P.a x (w x) (dw x) i k

@[simp] theorem linearisationSymbol_apply
    (w : X → V) (dw : X → ι → V) (x : X) (xi : ι → ℝ) (v : V) :
    P.linearisationSymbol w dw x xi v =
      ∑ i, ∑ k, (xi i * xi k) • P.a x (w x) (dw x) i k v := by
  simp [linearisationSymbol]

/-- Varying only the second-order part of a formal jet in the rank-one
direction `(xi i * xi k) • v` changes the quasilinear operator by its existing
linearisation symbol.  This is an exact principal-coefficient identity, not a
claim about a Fréchet derivative on a section space. -/
theorem applyJet_add_rankOne_second
    (w : X → V) (dw : X → ι → V) (x : X)
    (secondData : ι → ι → V) (xi : ι → ℝ) (v : V) :
    P.applyJet x
        { value := w x
          first := dw x
          second := fun i k => secondData i k + (xi i * xi k) • v } =
      P.applyJet x
          { value := w x
            first := dw x
            second := secondData } +
        P.linearisationSymbol w dw x xi v := by
  simp only [applyJet, linearisationSymbol_apply, map_add, map_smul,
    Finset.sum_add_distrib]
  abel

/-- "Parabolic at `w`" in the sense of the source: the linearised symbol is
strictly parabolic. -/
def IsStrictlyParabolicAt (q : X → (ι → ℝ) → ℝ)
    (w : X → V) (dw : X → ι → V) : Prop :=
  StrictlyParabolic (P.linearisationSymbol w dw) q

end QuasilinearSecondOrderOperator

end

end Topping
