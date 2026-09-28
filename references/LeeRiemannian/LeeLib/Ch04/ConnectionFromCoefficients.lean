/-
Chapter 4, "Connections", §"Connections in the Tangent Bundle": **building a
connection from connection coefficients** (Lee's Lemma 4.10 and the exercise
`exer:complete-proof-lemma-4.10`).

Lee's Lemma 4.10 says a connection in `TM` is *determined by* its connection
coefficients relative to a smooth local frame, and conversely that *any* choice of
coefficient functions `Γ^k_{ij}` gives a connection.  The forward direction ("a
connection determines and is reconstructed from its coefficients", Lee's equation
(4.9)) is already available as
`covariantDeriv_eq_connectionCoeff_formula` in `ConnectionCoefficients.lean`.  This
file supplies the *converse construction*: from arbitrary `Γ : ι → ι → ι → M → ℝ`
we build an honest covariant derivative and check that its recovered connection
coefficients are exactly `Γ`.

Mathlib's `Bundle.CovariantDerivative` has **no** way to construct a covariant
derivative from scratch — every operation (`addOneForm`, `affine_combination`,
`difference`) needs a pre-existing one.  We supply the missing base construction on
a *single trivialization frame*: given a compatible trivialization `e` of `TM` and
a basis `b` of the model fibre `E`, the frame `∂_k = e.localFrame b k` and its
coordinate functionals `σ^k = e.localFrame_coeff I b k` let us *define*

  `∇σ x (X) = ∑_k ( X(σ^k) + ∑_i ∑_j σ^i(X)·σ^j(σ x)·Γ^k_{ij}(x) ) ∂_k x`

(Lee's coordinate formula (4.9), read as a *definition* — `connOfCoeffAux`).  We prove
this is a covariant derivative on `e.baseSet`
(`connOfCoeff_isCovariantDerivativeOn : IsCovariantDerivativeOn …`, discharging the
additivity and Leibniz axioms), and — when the trivialization is global,
`e.baseSet = univ`, i.e. the bundle is parallelizable in this chart — package it
as a bundled `CovariantDerivative` (`connOfCoeff`).  Finally
`connectionCoeff_connOfCoeff` recovers `Γ^k_{ij}` as the connection coefficients of
the built connection: the substantive existence-and-recovery half of Lee 4.10.

Because forward-differentiability of the coordinate functionals
(`mdifferentiableAt_localFrame_coeff`) is only available for a *trivialization*
frame, the construction is phrased with `e.localFrame b`, not an arbitrary
`IsLocalFrameOn`.  We do not attempt a type-level bijection between connections and
coefficient families (false, due to non-differentiable "junk" sections).
-/
import LeeLib.Ch04.ConnectionCoefficients
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace LeeLib.Ch04

open Bundle Module Filter
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]
  {e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)}
  [MemTrivializationAtlas e] {b : Basis ι ℝ E}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Auxiliary: `d% g x = 0` when `g` is *eventually constant* near `x`.  Used to kill
the derivative of the (locally constant) frame coordinates of a frame vector. -/
private lemma mvfderiv_eq_zero_of_eventuallyEq_const {g : M → ℝ} {x : M} {c : ℝ}
    (h : g =ᶠ[𝓝 x] fun _ => c) : d% g x = 0 := by
  simp only [mvfderiv]
  rw [h.mfderiv_eq, mfderiv_const]
  simp

/-- **The connection built from connection coefficients** (Lee's Lemma 4.10, the
construction), in a single trivialization frame `∂_k = e.localFrame b k`.

Given coefficient functions `Γ^k_{ij}`, this sends a section `σ` to the section of
`Hom(TM, TM)` given by Lee's formula (4.9):
`∇σ x (X) = ∑_k ( X(σ^k) + ∑_i ∑_j σ^i(X)·σ^j(σ x)·Γ^k_{ij}(x) ) ∂_k x`,
where `σ^k` are the coordinate functionals of the trivialization frame. -/
noncomputable def connOfCoeffAux
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (Γ : ι → ι → ι → M → ℝ) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x =>
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    ∑ k, ((d% (fun y => e.localFrame_coeff I b k y (σ y)) x)
          + ∑ i, (∑ j, e.localFrame_coeff I b j x (σ x) * Γ i j k x)
                  • (e.localFrame_coeff I b i x).toContinuousLinearMap).smulRight
        (e.localFrame b k x)

/-- Pointwise formula for `connOfCoeffAux` applied to a direction `X`: Lee's
coordinate expression (4.9). -/
theorem connOfCoeffAux_apply (Γ : ι → ι → ι → M → ℝ) (σ : Π x : M, TangentSpace I x)
    (x : M) (X : TangentSpace I x) :
    connOfCoeffAux e b Γ σ x X
      = ∑ k, ((d% (fun y => e.localFrame_coeff I b k y (σ y)) x) X
              + ∑ i, (∑ j, e.localFrame_coeff I b j x (σ x) * Γ i j k x)
                      * e.localFrame_coeff I b i x X) • e.localFrame b k x := by
  simp only [connOfCoeffAux, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, LinearMap.coe_toContinuousLinearMap']

omit [Fintype ι] in
/-- Differentiability of the frame coordinates of a section differentiable at `x`. -/
private lemma mdiffAt_coeff {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (k : ι) :
    MDiffAt (fun y => e.localFrame_coeff I b k y (σ y)) x := by
  simpa using mdifferentiableAt_localFrame_coeff b hx hσ k

/-- **`connOfCoeffAux` is a covariant derivative on the trivialization domain**
(Lee's Lemma 4.10): it satisfies additivity and the Leibniz rule.  This discharges
the two `IsCovariantDerivativeOn` axioms directly from Lee's coordinate formula. -/
theorem connOfCoeff_isCovariantDerivativeOn (Γ : ι → ι → ι → M → ℝ) :
    IsCovariantDerivativeOn E (connOfCoeffAux e b Γ) e.baseSet where
  add {σ σ' x} hσ hσ' hx := by
    ext X
    rw [ContinuousLinearMap.add_apply, connOfCoeffAux_apply, connOfCoeffAux_apply,
      connOfCoeffAux_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- The `k`-th coordinate coefficient splits additively.
    have hd : (d% (fun y => e.localFrame_coeff I b k y ((σ + σ') y)) x)
        = (d% (fun y => e.localFrame_coeff I b k y (σ y)) x)
          + (d% (fun y => e.localFrame_coeff I b k y (σ' y)) x) := by
      have hfun : (fun y => e.localFrame_coeff I b k y ((σ + σ') y))
          = (fun y => e.localFrame_coeff I b k y (σ y))
            + (fun y => e.localFrame_coeff I b k y (σ' y)) := by
        funext y; simp [map_add]
      rw [hfun, mvfderiv_add (mdiffAt_coeff hx hσ k) (mdiffAt_coeff hx hσ' k)]
    rw [hd, ContinuousLinearMap.add_apply, ← add_smul]
    congr 1
    simp only [Pi.add_apply, map_add]
    -- Distribute the Christoffel sum over the two sections.
    rw [add_add_add_comm]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← add_mul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  leibniz {σ g x} hσ hg hx := by
    ext X
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, connOfCoeffAux_apply, connOfCoeffAux_apply]
    -- Frame components scale by `g`: `(g • σ)^j(x) = g x · σ^j(x)`.
    have hgs : ∀ j, e.localFrame_coeff I b j x ((g • σ) x)
        = g x * e.localFrame_coeff I b j x (σ x) := fun j => by
      simp [map_smul, smul_eq_mul]
    -- Reconstruct `(d% g x) X • σ x` in the trivialization frame `∂_k = e.localFrame b k`.
    have hgterm : (d% g x) X • σ x
        = ∑ k, ((d% g x) X * e.localFrame_coeff I b k x (σ x)) • e.localFrame b k x := by
      conv_lhs => rw [e.eq_sum_localFrame_coeff_smul (I := I) (b := b) (s := σ) hx]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun k _ => smul_smul _ _ _)
    rw [hgterm, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- `(g • σ)^k = g · σ^k`, so its derivative obeys the scalar product rule (4.9).
    have hd : (d% (fun y => e.localFrame_coeff I b k y ((g • σ) y)) x)
        = g x • (d% (fun y => e.localFrame_coeff I b k y (σ y)) x)
          + (d% g x).smulRight (e.localFrame_coeff I b k x (σ x)) := by
      have hfun : (fun y => e.localFrame_coeff I b k y ((g • σ) y))
          = g * (fun y => e.localFrame_coeff I b k y (σ y)) := by
        funext y; simp [map_smul]
      rw [hfun, mvfderiv_mul hg (mdiffAt_coeff hx hσ k)]
      congr 1
      ext v
      simp [ContinuousLinearMap.smulRight_apply, mul_comm]
    -- The Christoffel term scales by `g x` since `(g • σ)^j(x) = g x · σ^j(x)`.
    have hchr : (∑ i, (∑ j, e.localFrame_coeff I b j x ((g • σ) x) * Γ i j k x)
                    * e.localFrame_coeff I b i x X)
        = g x * ∑ i, (∑ j, e.localFrame_coeff I b j x (σ x) * Γ i j k x)
                    * e.localFrame_coeff I b i x X := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hgs j, mul_assoc]
    -- Reduce to equality of the `∂_k x` coefficients, then match by ring arithmetic.
    rw [smul_smul, ← add_smul]
    congr 1
    rw [hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, hchr]
    simp only [smul_eq_mul]
    ring

/-- **Bundled connection from coefficients** on a *globally* trivialized bundle
(`e.baseSet = Set.univ`, i.e. `TM` is parallelizable in this chart): package
`connOfCoeffAux` as an honest `Connection I E (TangentSpace I)`, the covariant-derivative
axioms coming from `connOfCoeff_isCovariantDerivativeOn`. -/
noncomputable def connOfCoeff (b : Basis ι ℝ E) (Γ : ι → ι → ι → M → ℝ)
    (he : e.baseSet = Set.univ) :
    Connection I E (TangentSpace I : M → Type _) where
  toFun := connOfCoeffAux e b Γ
  isCovariantDerivativeOnUniv := he ▸ connOfCoeff_isCovariantDerivativeOn Γ

@[simp] lemma connOfCoeff_apply (b : Basis ι ℝ E) (Γ : ι → ι → ι → M → ℝ)
    (he : e.baseSet = Set.univ) (σ : Π x : M, TangentSpace I x) :
    connOfCoeff b Γ he σ = connOfCoeffAux e b Γ σ := rfl

/-- **Recovery of the coefficients** (the substantive half of Lee's Lemma 4.10):
relative to the trivialization frame `∂_k = e.localFrame b k`, the connection
coefficients of the built connection `connOfCoeff b Γ he` are exactly the given `Γ`.
Since the frame coordinates of a frame vector are locally constant (their derivative
vanishes) and Kronecker at `x`, Lee's formula (4.9) collapses to `∇_{∂_i} ∂_j = Γ^{·}_{ij} ∂_·`. -/
theorem connectionCoeff_connOfCoeff (b : Basis ι ℝ E) (Γ : ι → ι → ι → M → ℝ)
    (he : e.baseSet = Set.univ) (i j k : ι) (x : M) :
    connectionCoeff (connOfCoeff b Γ he) (e.isLocalFrameOn_localFrame_baseSet I 1 b) i j k x
      = Γ i j k x := by
  classical
  have hx : x ∈ e.baseSet := he ▸ Set.mem_univ x
  -- Kronecker delta: the `a`-coordinate of the `c`-th frame vector at `x`.
  have hkron : ∀ a c : ι,
      e.localFrame_coeff I b a x (e.localFrame b c x) = if c = a then (1 : ℝ) else 0 := by
    intro a c
    rw [e.localFrame_coeff_apply_of_mem_baseSet b hx (e.localFrame b c) a,
      e.localFrame_apply_of_mem_baseSet b hx, Module.Basis.repr_self_apply]
  -- The frame coordinates of a frame vector are locally constant, so their derivative vanishes.
  have hderiv : ∀ a c : ι, (d% (fun y => e.localFrame_coeff I b a y (e.localFrame b c y)) x) = 0 := by
    intro a c
    refine mvfderiv_eq_zero_of_eventuallyEq_const (c := if c = a then (1 : ℝ) else 0) ?_
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.localFrame_coeff_apply_of_mem_baseSet b hy (e.localFrame b c) a,
      e.localFrame_apply_of_mem_baseSet b hy, Module.Basis.repr_self_apply]
  -- `∇_{∂_i} ∂_j = ∑ k', Γ i j k' • ∂_{k'}` from Lee's formula (4.9).
  have hcov : covariantDeriv (connOfCoeff b Γ he) (e.localFrame b i) (e.localFrame b j) x
      = ∑ k', Γ i j k' x • e.localFrame b k' x := by
    rw [covariantDeriv_apply, connOfCoeff_apply, connOfCoeffAux_apply]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    congr 1
    rw [hderiv k' j, ContinuousLinearMap.zero_apply, zero_add]
    simp only [hkron, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- Read off the `k`-th coefficient; only the `k' = k` term of the reconstruction survives.
  rw [connectionCoeff, hcov,
    show (e.isLocalFrameOn_localFrame_baseSet I 1 b).coeff k = e.localFrame_coeff I b k from rfl,
    map_sum]
  simp only [map_smul, smul_eq_mul, hkron, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end LeeLib.Ch04
