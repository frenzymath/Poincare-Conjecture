import PetersenLib.Ch02.ChristoffelSymbols
import PetersenLib.Ch02.IndexNotation

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.24 (covariant-derivative components in coordinates)

Exercise 2.5.24 asks for the coordinate expression of the covariant derivative of
a tensor in terms of Christoffel symbols.  For a `(0,2)`-tensor `T` with
components `T_{kl} = T(∂_k, ∂_l)` the formula is
`(∇T)_{jkl} = ∂_j T_{kl} − Γ^m_{jk} T_{ml} − Γ^m_{jl} T_{km}`,
which we formalize as `exercise2_5_24` for the `(0,k)`-tensor operators of the
project (`TensorOperator I M 2`); here `∇_j` is the index-notation covariant
derivative `covariantDerivativeIndexNotation` in the direction of the `j`-th
frame field, and `Γ^m_{jk}` are the Christoffel symbols of the second kind.

The `(1,1)`-tensor variant `(∇T)^k_{ji} = ∂_j T^k_i − Γ^ℓ_{ji} T^k_ℓ + Γ^k_{jℓ} T^ℓ_i`
requires a representation of `(1,1)`-tensor fields, which the project does not
have (all of §2.1–2.4 is developed for `(0,k)`-tensors); it is not formalized
here — this follows the same partial-formalization convention as
`exercise2_5_12`.

The proof mirrors `hessian_coordinate_formula`: the Leibniz expansion of
`∇_{∂_j} T` (`covariantDerivativeIndexNotation_formula`), the Christoffel
expansion of `∇_{∂_j}∂_k` on the coordinate frame
(`leviCivita_covField_chartFrame_eq_christoffel_sum`), and tensoriality of `T`
(`isTensorOperator_slot_eq_zero_of_vanish` for pointwise dependence of a slot,
plus additivity/homogeneity to pull the Christoffel sum out of the slot).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, `rem:pet-ch2-ex-24`.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Eng.** A tensor slot depends only on the value of the field at the point:
if `V x = 0` then `T(…, V, …)(x) = 0`.  (Local copy of the standard tensoriality
consequence, cf. `isTensorOperator_slot_eq_zero_of_vanish`.) -/
private theorem slot_eq_zero_of_vanish {k : ℕ} {T : TensorOperator I M k}
    (hT : IsTensorOperator T) (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k) (x : M)
    (V : Π x : M, TangentSpace I x) (hV : V x = 0) :
    T (Function.update Y i V) x = 0 := by
  classical
  set c : M → ℝ := fun p => if p = x then 1 else 0 with hc_def
  have hgv : (fun p => c p • V p) = (fun p => (0 : TangentSpace I p)) := by
    funext p
    by_cases hp : p = x
    · subst hp; simp [hc_def, hV]
    · simp [hc_def, hp]
  have hkey := hT.smul_slot Y i c V x
  rw [hgv, hT.zero_slot Y i x] at hkey
  have hcx : c x = 1 := by simp [hc_def]
  rw [hcx, one_mul] at hkey
  exact hkey.symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Eng.** Linearity of a tensor operator in a slot against a finite linear
combination: `T(…, Σ_m c_m • V_m, …) = Σ_m c_m · T(…, V_m, …)`.  Built from the
`add_slot`/`smul_slot` clauses by induction on the index set. -/
theorem isTensorOperator_slot_sum_smul {k : ℕ} {T : TensorOperator I M k}
    (hT : IsTensorOperator T) (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k)
    {n : ℕ} (c : Fin n → ℝ) (V : Fin n → Π x : M, TangentSpace I x) (x : M) :
    T (Function.update Y i (fun p => ∑ m, c m • V m p)) x
      = ∑ m, c m * T (Function.update Y i (V m)) x := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simpa using hT.zero_slot Y i x
  | @insert a s ha ih =>
    have hsplit : (fun p => ∑ m ∈ insert a s, c m • V m p)
        = fun p => c a • V a p + (∑ m ∈ s, c m • V m p) := by
      funext p; rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    rw [hsplit, hT.add_slot, hT.const_smul_slot, ih]

/-- **Math.** **Exercise 2.5.24** (`(0,2)` part): the coordinate components of the
covariant derivative of a `(0,2)`-tensor `T` are
`(∇_j T)(∂_k, ∂_l) = ∂_j T_{kl} − Σ_m Γ^m_{jk} T_{ml} − Σ_m Γ^m_{jl} T_{km}`,
where `T_{kl} = T(∂_k, ∂_l)`, `∇_j` is the index-notation covariant derivative in
the `j`-th coordinate direction, and `Γ^m_{jk}` are the second-kind Christoffel
symbols.  The frame `Efr` is any smooth local frame agreeing with the coordinate
frame `chartBasisVecFiber p a` near `p` (e.g. `chartFrameExtension`), matching
the convention of `hessian_coordinate_formula`.  (The `(1,1)`-tensor variant is
not formalized — see the module docstring.) -/
theorem exercise2_5_24 (g : RiemannianMetric I M) {T : TensorOperator I M 2}
    (hT : IsTensorOperator T) (p : M) (j k l : Fin (Module.finrank ℝ E))
    (Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)
    (hEfr : ∀ a, IsSmoothVectorField (Efr a))
    (hEfrev : ∀ a, (Efr a) =ᶠ[nhds p] fun q => chartBasisVecFiber (I := I) p a q) :
    covariantDerivativeIndexNotation (g.leviCivita).toAffineConnection Efr j T
        ![Efr k, Efr l] p
      = directionalDerivative (Efr j) (T ![Efr k, Efr l]) p
        - (∑ m, christoffelSymbolsSecondKind g p j k m * T ![Efr m, Efr l] p)
        - (∑ m, christoffelSymbolsSecondKind g p j l m * T ![Efr k, Efr m] p) := by
  classical
  -- The covariant derivative of `∂_a` in the direction `∂_j`, rewritten against
  -- the frame `Efr` (which agrees with the coordinate frame at `p`).
  have hcovEfr : ∀ a : Fin (Module.finrank ℝ E),
      (g.leviCivita).covField (Efr j) (Efr a) p
        = (fun q => ∑ m, christoffelSymbolsSecondKind g p j a m • Efr m q) p := by
    intro a
    rw [leviCivita_covField_chartFrame_eq_christoffel_sum g p j a Efr hEfr hEfrev]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(hEfrev m).self_of_nhds]
  -- A tensor slot depends only on the value of the field at `p`, so replace the
  -- covariant-derivative field with its Christoffel expansion.
  have hslot : ∀ (a : Fin (Module.finrank ℝ E)) (i : Fin 2),
      T (Function.update ![Efr k, Efr l] i
          ((g.leviCivita).covField (Efr j) (Efr a))) p
        = T (Function.update ![Efr k, Efr l] i
            (fun q => ∑ m, christoffelSymbolsSecondKind g p j a m • Efr m q)) p := by
    intro a i
    have hvanish : (fun q => (g.leviCivita).covField (Efr j) (Efr a) q
        - (∑ m, christoffelSymbolsSecondKind g p j a m • Efr m q)) p = 0 := by
      show (g.leviCivita).covField (Efr j) (Efr a) p
        - (∑ m, christoffelSymbolsSecondKind g p j a m • Efr m p) = 0
      rw [hcovEfr a]; simp
    have hz := slot_eq_zero_of_vanish hT ![Efr k, Efr l] i p
      (fun q => (g.leviCivita).covField (Efr j) (Efr a) q
        - (∑ m, christoffelSymbolsSecondKind g p j a m • Efr m q)) hvanish
    rw [hT.sub_slot] at hz
    linarith [hz]
  -- Slot updates identify with the `T_{ml}` / `T_{km}` components.
  have hupd0 : ∀ m, Function.update (![Efr k, Efr l] : Fin 2 → Π x : M, TangentSpace I x) 0
      (Efr m) = ![Efr m, Efr l] := by
    intro m; funext i; fin_cases i <;> simp
  have hupd1 : ∀ m, Function.update (![Efr k, Efr l] : Fin 2 → Π x : M, TangentSpace I x) 1
      (Efr m) = ![Efr k, Efr m] := by
    intro m; funext i; fin_cases i <;> simp
  -- The Leibniz formula for the index-notation covariant derivative.
  rw [covariantDerivativeIndexNotation_formula, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hslot k 0, hslot l 1,
    isTensorOperator_slot_sum_smul hT _ 0, isTensorOperator_slot_sum_smul hT _ 1]
  rw [Finset.sum_congr rfl (fun m _ => by rw [hupd0 m] :
        ∀ m ∈ Finset.univ, christoffelSymbolsSecondKind g p j k m
          * T (Function.update ![Efr k, Efr l] 0 (Efr m)) p
          = christoffelSymbolsSecondKind g p j k m * T ![Efr m, Efr l] p),
    Finset.sum_congr rfl (fun m _ => by rw [hupd1 m] :
        ∀ m ∈ Finset.univ, christoffelSymbolsSecondKind g p j l m
          * T (Function.update ![Efr k, Efr l] 1 (Efr m)) p
          = christoffelSymbolsSecondKind g p j l m * T ![Efr k, Efr m] p)]
  ring

end PetersenLib

end
