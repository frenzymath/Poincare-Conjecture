import DoCarmoLib.Riemannian.Jacobi.ConjugateDifferential
import DoCarmoLib.Riemannian.Jacobi.JacobiVelocityPairing

/-!
# The vector space of Jacobi fields: dimension and conjugate points

do Carmo, *Riemannian Geometry*, Ch. 5, §3.  Along a geodesic `γ : [0, L] → M`,
the Jacobi fields form a `2n`-dimensional real vector space, faithfully
**parametrized by their initial data** `(J(0), DJ(0)) ∈ E × E`: existence
(`exists_isJacobiFieldAlongOn`) makes the parametrization surjective, uniqueness
(`IsJacobiFieldAlongOn.eqOn_of_initial`) makes it injective.  Under this
identification, evaluation of the Jacobi field at a fixed time `t₀ ∈ [0, L]` is a
**linear map** `evalJacobiAt t₀ : E × E →ₗ[ℝ] E`, `(J₀, DJ₀) ↦ J(t₀)`.

This file develops the resulting finite-dimensional linear algebra, closing the
`§3` dimension statements that do Carmo derives from it:

* `evalJacobiAt`, `evalJacobiAt_zero` — the evaluation map and `J(0) = J₀`.
* `jacobiEndpointOfVel` (`Θ`) — the linear map `DJ₀ ↦ J(L)` on the space of
  Jacobi fields with `J(0) = 0`, and `injective_jacobiEndpointOfVel_iff_not_conjugate`:
  `Θ` is injective iff `γ(L)` is **not** conjugate to `γ(0)` (do Carmo
  `prop:dc-ch5-3-5`, first assertion, endpoint-general form).
* `exists_unique_jacobi_of_endpoints` — do Carmo **Proposition 3.9**: if `γ(L)` is
  not conjugate to `γ(0)`, then for any `V₁ ∈ T_{γ(0)}M`, `V₂ ∈ T_{γ(L)}M` there is
  a unique Jacobi field with `J(0) = V₁`, `J(L) = V₂`.

The construction is the classical order-`2n` well-posedness of the Jacobi ODE,
here read off the manifold Jacobi-field predicate `IsJacobiFieldAlongOn` and its
existence/uniqueness/superposition API.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

variable {g : RiemannianMetric I M} {γ : ℝ → M} {L : ℝ}

/-! ### The chosen Jacobi field with prescribed initial data -/

/-- **Math.** The chosen Jacobi field `J` along `γ` on `[0, L]` with initial data
`(J(0), DJ(0)) = p`, extracted from `exists_isJacobiFieldAlongOn`. -/
def jacobiJ (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t) (p : E × E) : ℝ → E :=
  (exists_isJacobiFieldAlongOn hab hgeo hγc p.1 p.2).choose

/-- **Math.** The covariant derivative field of `jacobiJ`. -/
def jacobiDJ (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t) (p : E × E) : ℝ → E :=
  (exists_isJacobiFieldAlongOn hab hgeo hγc p.1 p.2).choose_spec.choose

variable (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
  (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)

theorem jacobiJ_spec (p : E × E) :
    IsJacobiFieldAlongOn (I := I) g γ (jacobiJ hab hgeo hγc p) (jacobiDJ hab hgeo hγc p) 0 L
      ∧ jacobiJ hab hgeo hγc p 0 = p.1 ∧ jacobiDJ hab hgeo hγc p 0 = p.2 :=
  (exists_isJacobiFieldAlongOn hab hgeo hγc p.1 p.2).choose_spec.choose_spec

theorem jacobiJ_isJacobiField (p : E × E) :
    IsJacobiFieldAlongOn (I := I) g γ (jacobiJ hab hgeo hγc p) (jacobiDJ hab hgeo hγc p) 0 L :=
  (jacobiJ_spec hab hgeo hγc p).1

@[simp] theorem jacobiJ_zero (p : E × E) : jacobiJ hab hgeo hγc p 0 = p.1 :=
  (jacobiJ_spec hab hgeo hγc p).2.1

@[simp] theorem jacobiDJ_zero (p : E × E) : jacobiDJ hab hgeo hγc p 0 = p.2 :=
  (jacobiJ_spec hab hgeo hγc p).2.2

/-- **Math.** **Uniqueness, packaged.** Any Jacobi field with the same initial data as `p`
agrees with the chosen one `jacobiJ p` on `[0, L]`. -/
theorem eqOn_jacobiJ {J DJ : ℝ → E} (p : E × E)
    (hJF : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 L)
    (h0 : J 0 = p.1) (h0' : DJ 0 = p.2) :
    ∀ t ∈ Icc (0 : ℝ) L, J t = jacobiJ hab hgeo hγc p t ∧ DJ t = jacobiDJ hab hgeo hγc p t := by
  refine IsJacobiFieldAlongOn.eqOn_of_initial hab hgeo hγc hJF (jacobiJ_isJacobiField hab hgeo hγc p)
    ?_ ?_
  · rw [h0, jacobiJ_zero]
  · rw [h0', jacobiDJ_zero]

/-! ### Evaluation at a fixed time is linear -/

/-- **Math.** **Evaluation of the Jacobi field at a fixed time `t₀ ∈ [0, L]`** as a linear
map `E × E →ₗ[ℝ] E`, sending the initial data `(J(0), DJ(0))` to `J(t₀)`.  It is
linear by uniqueness of Jacobi fields with given initial data (superposition:
`IsJacobiFieldAlongOn.add`, `.smul`). -/
def evalJacobiAt (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) L) : (E × E) →ₗ[ℝ] E where
  toFun p := jacobiJ hab hgeo hγc p t₀
  map_add' p q := by
    have hsum : IsJacobiFieldAlongOn (I := I) g γ
        (fun t => jacobiJ hab hgeo hγc p t + jacobiJ hab hgeo hγc q t)
        (fun t => jacobiDJ hab hgeo hγc p t + jacobiDJ hab hgeo hγc q t) 0 L :=
      (jacobiJ_isJacobiField hab hgeo hγc p).add hab hgeo hγc (jacobiJ_isJacobiField hab hgeo hγc q)
    have h := eqOn_jacobiJ hab hgeo hγc (p + q) hsum (by simp [Prod.fst_add]) (by simp [Prod.snd_add])
    exact ((h t₀ ht₀).1).symm
  map_smul' c p := by
    have hsm : IsJacobiFieldAlongOn (I := I) g γ
        (fun t => c • jacobiJ hab hgeo hγc p t) (fun t => c • jacobiDJ hab hgeo hγc p t) 0 L :=
      (jacobiJ_isJacobiField hab hgeo hγc p).smul c
    have h := eqOn_jacobiJ hab hgeo hγc (c • p) hsm (by simp [Prod.smul_fst]) (by simp [Prod.smul_snd])
    exact ((h t₀ ht₀).1).symm

@[simp] theorem evalJacobiAt_apply (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) L) (p : E × E) :
    evalJacobiAt hab hgeo hγc t₀ ht₀ p = jacobiJ hab hgeo hγc p t₀ := rfl

/-- **Math.** Evaluating at the left endpoint recovers the initial value `J(0) = J₀`. -/
@[simp] theorem evalJacobiAt_zero (p : E × E) :
    evalJacobiAt hab hgeo hγc 0 ⟨le_rfl, hab.le⟩ p = p.1 := by
  simp [evalJacobiAt_apply]

/-! ### The endpoint map on Jacobi fields vanishing at `0`, and conjugate points -/

/-- **Math.** **The endpoint map `Θ : DJ(0) ↦ J(L)`** on the `n`-dimensional space of Jacobi
fields with `J(0) = 0` (do Carmo `prop:dc-ch5-3-5`).  A Jacobi field with `J(0) = 0`
is determined by `DJ(0) = J'(0)`; `Θ` sends that initial velocity to the terminal
value `J(L)`. -/
def jacobiEndpointOfVel : E →ₗ[ℝ] E :=
  (evalJacobiAt hab hgeo hγc L (right_mem_Icc.2 hab.le)).comp (LinearMap.inr ℝ E E)

@[simp] theorem jacobiEndpointOfVel_apply (w : E) :
    jacobiEndpointOfVel hab hgeo hγc w = jacobiJ hab hgeo hγc (0, w) L := by
  simp [jacobiEndpointOfVel, evalJacobiAt_apply]

/-- **Math.** **do Carmo Ch. 5, Proposition 3.5 (first assertion, endpoint-general form).**
The endpoint map `Θ` is injective **iff** `γ(L)` is *not* conjugate to `γ(0)` along
`γ`.  A nonzero element of `ker Θ` is a nonzero Jacobi field with `J(0) = J(L) = 0`
(a conjugacy), and conversely. -/
theorem injective_jacobiEndpointOfVel_iff_not_conjugate :
    Function.Injective (jacobiEndpointOfVel hab hgeo hγc)
      ↔ ¬ IsConjugatePointAt (I := I) g γ L := by
  constructor
  · intro hinj hconj
    obtain ⟨J, DJ, hJF, ⟨t, ht, hJt⟩, hJ0, hJL⟩ := hconj
    have hDJ0 : DJ 0 ≠ 0 := by
      intro h0
      exact hJt ((hJF.eqOn_zero hab.le hgeo hγc hJ0 h0 t ht).1)
    have hkey : jacobiEndpointOfVel hab hgeo hγc (DJ 0) = 0 := by
      have heq := eqOn_jacobiJ hab hgeo hγc (0, DJ 0) hJF (by simpa using hJ0) (by simp)
      rw [jacobiEndpointOfVel_apply, ← (heq L (right_mem_Icc.2 hab.le)).1]
      exact hJL
    exact hDJ0 (hinj (hkey.trans (map_zero _).symm))
  · intro hnc
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra hwne
    apply hnc
    refine ⟨jacobiJ hab hgeo hγc (0, w), jacobiDJ hab hgeo hγc (0, w),
      jacobiJ_isJacobiField hab hgeo hγc (0, w), ?_, by simp, ?_⟩
    · by_contra hall
      push_neg at hall
      have hd := (jacobiJ_isJacobiField hab hgeo hγc (0, w)).deriv_eq_zero_of_forall_eq_zero hab hall
      rw [jacobiDJ_zero] at hd
      exact hwne hd
    · rwa [jacobiEndpointOfVel_apply] at hw

/-! ### Proposition 3.9 — prescribed endpoints -/

include hab hgeo hγc in
/-- **Math.** **do Carmo Ch. 5, Proposition 3.9.** If `γ(L)` is not conjugate to `γ(0)`,
then for any `V₁ ∈ T_{γ(0)}M` and `V₂ ∈ T_{γ(L)}M` there is a **unique** Jacobi
field `J` along `γ` with `J(0) = V₁` and `J(L) = V₂`.

Existence: the endpoint map `Θ` is injective, hence (finite dimension) surjective,
so we can solve `Θ w = V₂ − J_{(V₁,0)}(L)` and take the initial data `(V₁, w)`.
Uniqueness: a competing field has the same `J(0)`; subtracting gives a Jacobi field
with `J(0) = J(L) = 0`, i.e. an element of `ker Θ = 0`, hence equal initial velocity
and (uniqueness of initial-value problems) equal on `[0, L]`. -/
theorem exists_unique_jacobi_of_endpoints (hnc : ¬ IsConjugatePointAt (I := I) g γ L)
    (V₁ V₂ : E) :
    ∃ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ 0 L ∧ J 0 = V₁ ∧ J L = V₂ ∧
      ∀ J' DJ' : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J' DJ' 0 L → J' 0 = V₁ → J' L = V₂ →
        ∀ t ∈ Icc (0 : ℝ) L, J' t = J t ∧ DJ' t = DJ t := by
  have hinj : Function.Injective (jacobiEndpointOfVel hab hgeo hγc) :=
    (injective_jacobiEndpointOfVel_iff_not_conjugate hab hgeo hγc).2 hnc
  have hsurj : Function.Surjective (jacobiEndpointOfVel hab hgeo hγc) :=
    LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨w, hw⟩ := hsurj (V₂ - evalJacobiAt hab hgeo hγc L (right_mem_Icc.2 hab.le) (V₁, 0))
  refine ⟨jacobiJ hab hgeo hγc (V₁, w), jacobiDJ hab hgeo hγc (V₁, w),
    jacobiJ_isJacobiField hab hgeo hγc (V₁, w), by simp, ?_, ?_⟩
  · -- `J(L) = V₂`
    have hsplit : (V₁, w) = ((V₁, 0) : E × E) + (0, w) := by simp
    have hL : jacobiJ hab hgeo hγc (V₁, w) L
        = evalJacobiAt hab hgeo hγc L (right_mem_Icc.2 hab.le) (V₁, 0)
          + jacobiEndpointOfVel hab hgeo hγc w := by
      rw [← evalJacobiAt_apply hab hgeo hγc L (right_mem_Icc.2 hab.le) (V₁, w), hsplit, map_add]
      simp only [jacobiEndpointOfVel_apply, evalJacobiAt_apply]
    rw [hL, hw]; abel
  · -- uniqueness
    intro J' DJ' hJF' hJ0' hJL' t ht
    have hδJF : IsJacobiFieldAlongOn (I := I) g γ
        (fun τ => J' τ - jacobiJ hab hgeo hγc (V₁, w) τ)
        (fun τ => DJ' τ - jacobiDJ hab hgeo hγc (V₁, w) τ) 0 L :=
      hJF'.sub hab hgeo hγc (jacobiJ_isJacobiField hab hgeo hγc (V₁, w))
    have hJL0 : jacobiJ hab hgeo hγc (V₁, w) L = V₂ := by
      have hsplit : (V₁, w) = ((V₁, 0) : E × E) + (0, w) := by simp
      have hL : jacobiJ hab hgeo hγc (V₁, w) L
          = evalJacobiAt hab hgeo hγc L (right_mem_Icc.2 hab.le) (V₁, 0)
            + jacobiEndpointOfVel hab hgeo hγc w := by
        rw [← evalJacobiAt_apply hab hgeo hγc L (right_mem_Icc.2 hab.le) (V₁, w), hsplit, map_add]
        simp only [jacobiEndpointOfVel_apply, evalJacobiAt_apply]
      rw [hL, hw]; abel
    -- `Θ (DJ'(0) − DJ₀(0)) = 0`, hence (injectivity) equal initial velocity
    have hΘ : jacobiEndpointOfVel hab hgeo hγc (DJ' 0 - jacobiDJ hab hgeo hγc (V₁, w) 0) = 0 := by
      have heq := eqOn_jacobiJ hab hgeo hγc (0, DJ' 0 - jacobiDJ hab hgeo hγc (V₁, w) 0) hδJF
        (by simp [hJ0']) (by simp)
      rw [jacobiEndpointOfVel_apply, ← (heq L (right_mem_Icc.2 hab.le)).1]
      simp [hJL', hJL0]
    have hvel : DJ' 0 = jacobiDJ hab hgeo hγc (V₁, w) 0 :=
      sub_eq_zero.1 (hinj (hΘ.trans (map_zero _).symm))
    exact IsJacobiFieldAlongOn.eqOn_of_initial hab hgeo hγc hJF'
      (jacobiJ_isJacobiField hab hgeo hγc (V₁, w))
      (by rw [hJ0', jacobiJ_zero]) hvel t ht

/-! ### Multiplicity of a conjugate point (do Carmo `def:dc-ch5-3-1`, `rem:dc-ch5-3-2`) -/

/-- **Math.** **The multiplicity of the conjugate point `γ(L)`** (do Carmo `def:dc-ch5-3-1`):
the maximal number of linearly independent Jacobi fields with `J(0) = J(L) = 0`.
Under the parametrization of Jacobi fields with `J(0) = 0` by their initial
velocity `DJ(0) ∈ E`, these are exactly `ker Θ`, so the multiplicity is the
dimension of `ker Θ`. -/
def conjugateMultiplicity : ℕ :=
  Module.finrank ℝ (LinearMap.ker (jacobiEndpointOfVel hab hgeo hγc))

/-- **Math.** **`γ(L)` is conjugate to `γ(0)` iff the multiplicity is positive**: a nonzero
element of `ker Θ` is precisely a nontrivial Jacobi field vanishing at both ends. -/
theorem isConjugatePointAt_iff_conjugateMultiplicity_pos :
    IsConjugatePointAt (I := I) g γ L ↔ 0 < conjugateMultiplicity hab hgeo hγc := by
  rw [conjugateMultiplicity, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero,
    LinearMap.ker_eq_bot, injective_jacobiEndpointOfVel_iff_not_conjugate, not_not]

/-- **Math.** **The multiplicity never exceeds `n = dim M`** (the weak half of do Carmo
`rem:dc-ch5-3-2`; `ker Θ ⊆ E`).  The sharp bound `≤ n − 1` additionally uses that
`t γ'(t)` is a Jacobi field with `J(0) = 0` never vanishing on `(0, L]`
(do Carmo `rem:dc-ch5-2-2`), so `γ'(0) ∉ ker Θ`. -/
theorem conjugateMultiplicity_le_finrank :
    conjugateMultiplicity hab hgeo hγc ≤ Module.finrank ℝ E :=
  Submodule.finrank_le _

/-! ### Proposition 3.5, multiplicity clause: `mult = dim ker (d exp_p)` -/

/-- **Math.** **do Carmo Ch. 5, Proposition 3.5 (multiplicity clause, endpoint form).**
If `D : E →L[ℝ] E` is the differential of `exp_p` at `v` read in a chart `ζ` around
`exp_p(v) = γ(1)` — i.e. `D(DJ(0)) = ` chart reading of `J(1)` for every Jacobi
field along `γ` with `J(0) = 0` (`hjac`, the defining property of the exponential
differential, cf. `expDifferential_injective_iff_not_conjugate`) — then the
multiplicity of the conjugate point `γ(1)` equals the dimension of `ker D`.

The kernels coincide: for `Z ∈ E`, `D Z` is the chart reading of `J_{(0,Z)}(1)`, and
the tangent chart reading is injective, so `D Z = 0` iff `J_{(0,Z)}(1) = Θ Z = 0`.
Hence `ker D = ker Θ` and the multiplicity `dim ker Θ` equals `dim ker D`. -/
theorem conjugateMultiplicity_eq_finrank_ker_expDifferential
    {ζ : M} {D : E →L[ℝ] E}
    (hγgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) 1))
    (hγcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t)
    (hγ1 : γ 1 ∈ (chartAt H ζ).source)
    (hjac : ∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ 0 1 → J 0 = 0 →
      D (DJ 0) = chartVectorRep (I := I) γ ζ J 1) :
    Module.finrank ℝ (LinearMap.ker (D : E →ₗ[ℝ] E))
      = conjugateMultiplicity zero_lt_one hγgeo hγcont := by
  -- reading `J 1` off its (injective) chart reading
  have hread : ∀ J : ℝ → E, chartVectorRep (I := I) γ ζ J 1 = 0 ↔ J 1 = 0 := by
    intro J
    refine ⟨fun h => ?_, fun h => by simp [chartVectorRep, h]⟩
    exact tangentCoordChange_injective (I := I) (x := γ 1) (β := ζ) hγ1
      (by simpa [chartVectorRep] using h)
  -- `D Z` is the chart reading of `J_{(0,Z)}(1)`
  have hDZ : ∀ Z : E, D Z
      = chartVectorRep (I := I) γ ζ (jacobiJ zero_lt_one hγgeo hγcont (0, Z)) 1 := by
    intro Z
    have h := hjac (jacobiJ zero_lt_one hγgeo hγcont (0, Z))
      (jacobiDJ zero_lt_one hγgeo hγcont (0, Z))
      (jacobiJ_isJacobiField zero_lt_one hγgeo hγcont (0, Z)) (by simp)
    rw [jacobiDJ_zero] at h
    simpa using h
  -- the kernels coincide
  have hker : LinearMap.ker (D : E →ₗ[ℝ] E)
      = LinearMap.ker (jacobiEndpointOfVel zero_lt_one hγgeo hγcont) := by
    refine Submodule.ext fun Z => ?_
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, jacobiEndpointOfVel_apply]
    rw [hDZ Z, hread]
  rw [conjugateMultiplicity, hker]

end Riemannian.Jacobi

end
