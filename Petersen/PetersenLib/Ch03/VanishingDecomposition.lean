import PetersenLib.Ch02.CovariantDerivative
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Vanishing decomposition of a smooth vector field near a zero

A smooth vector field `Z` vanishing at a point `p` decomposes, near `p`, as a
finite sum `Σᵢ fᵢ • Vᵢ` with **globally** smooth scalars `fᵢ` vanishing at `p`
and **globally** smooth vector fields `Vᵢ` (`exists_decomposition_of_eq_zero`).

## Design notes

The proof reads the coordinates of `Z` in the trivialization at `p` (via the
chart-basis frame `Tensor.chartBasisVecFiber` of
`Vendored/OpenGA/TensorBundle/SmoothOrthoFrame/ChartBasis.lean`), which are
raw scalars `f₀ i` smooth only on the trivialization's base set and vanishing
at `p`. These are globalized in two independent ways:

* the chart-basis vectors `Tensor.chartBasisVecFiber p i` are extended to
  global smooth vector fields `V i` agreeing with the frame near `p`
  (`exists_smoothVectorField_eventuallyEq`, imitating
  `gradient_isSmoothVectorField` in `Ch02/CovariantDerivative.lean`);
* the raw scalars `f₀ i` are globalized by multiplying with a smooth bump
  function `χ` centred at `p` (`SmoothBumpFunction.contMDiff_smul`), giving
  `f i := χ • f₀ i`, globally smooth and vanishing at `p` since `f₀ i p = 0`.

Since `χ ≡ 1` near `p` and `V i` agrees with the chart-basis frame near `p`,
the global decomposition `Z q = Σᵢ f i q • V i q` holds in a neighborhood of
`p`, matching the local basis expansion of `Z` in the trivialization.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold Topology ContDiff Bundle

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A smooth vector field `Z` vanishing at `p` decomposes, near `p`, as
a finite sum `Σᵢ fᵢ • Vᵢ` with globally smooth scalars `fᵢ` vanishing at `p` and
globally smooth vector fields `Vᵢ`. -/
theorem exists_decomposition_of_eq_zero
    {Z : Π x : M, TangentSpace I x} (hZ : IsSmoothVectorField Z)
    {p : M} (hZp : Z p = 0) :
    ∃ (f : Fin (Module.finrank ℝ E) → M → ℝ)
      (V : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x),
      (∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i)) ∧ (∀ i, IsSmoothVectorField (V i))
      ∧ (∀ i, f i p = 0) ∧ (∀ᶠ q in 𝓝 p, Z q = ∑ i, f i q • V i q) := by
  classical
  let e := trivializationAt E (TangentSpace I) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hbaseopen : IsOpen e.baseSet := e.open_baseSet
  have hbase_eq : e.baseSet = (chartAt H p).source := TangentBundle.trivializationAt_baseSet p
  -- coefficient continuous linear functionals reading off the trivialization
  let c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)
  have hc_apply : ∀ (i : Fin (Module.finrank ℝ E)) (v : E), c i v = (Module.finBasis ℝ E).repr v i :=
    fun _ _ => rfl
  -- raw scalar coefficients of `Z` read through the trivialization at `p`
  let f₀ : Fin (Module.finrank ℝ E) → M → ℝ := fun i b => c i ((e ⟨b, Z b⟩).2)
  -- smoothness of `f₀ i` on the base set
  have hZsec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (TotalSpace.mk' E x (Z x))) e.baseSet := hZ.contMDiffOn
  have hZtriv : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun x => (e ⟨x, Z x⟩).2) e.baseSet :=
    (e.contMDiffOn_section_baseSet_iff (IB := I) (n := (∞ : ℕ∞ω)) (s := Z)).mp hZsec
  have hf₀_smoothOn : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (f₀ i) e.baseSet := fun i =>
    (c i).contMDiff.comp_contMDiffOn hZtriv
  -- `f₀ i` vanishes at `p`
  have hf₀p : ∀ i, f₀ i p = 0 := by
    intro i
    show c i ((e ⟨p, Z p⟩).2) = 0
    rw [hZp]
    have hzero : (e ⟨p, (0 : TangentSpace I p)⟩).2 = 0 := by
      have h0 : (e.continuousLinearEquivAt ℝ p hp) (0 : TangentSpace I p) = 0 :=
        (e.continuousLinearEquivAt ℝ p hp).map_zero
      exact h0
    rw [hzero, map_zero]
  -- basis expansion of `Z` on the base set
  have hZexpand : ∀ b, b ∈ e.baseSet →
      Z b = ∑ i, f₀ i b • Tensor.chartBasisVecFiber (I := I) p i b := by
    intro b hb
    apply (e.continuousLinearEquivAt ℝ b hb).injective
    have hlhs : (e.continuousLinearEquivAt ℝ b hb) (Z b) = (e ⟨b, Z b⟩).2 := rfl
    have hrhs : (e.continuousLinearEquivAt ℝ b hb)
        (∑ i, f₀ i b • Tensor.chartBasisVecFiber (I := I) p i b)
        = ∑ i, f₀ i b • (Module.finBasis ℝ E) i := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
      congr 1
      show (e ⟨b, Tensor.chartBasisVecFiber (I := I) p i b⟩).2 = (Module.finBasis ℝ E) i
      exact Tensor.trivializationAt_chartBasisVec_snd (I := I) p i hb
    rw [hlhs, hrhs]
    have hswap : ∑ i, f₀ i b • (Module.finBasis ℝ E) i
        = ∑ i, (Module.finBasis ℝ E).repr ((e ⟨b, Z b⟩).2) i • (Module.finBasis ℝ E) i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show f₀ i b = (Module.finBasis ℝ E).repr ((e ⟨b, Z b⟩).2) i from hc_apply i _]
    rw [hswap]
    exact ((Module.finBasis ℝ E).sum_repr ((e ⟨b, Z b⟩).2)).symm
  -- a bump function centred at `p`
  obtain ⟨χ⟩ : Nonempty (SmoothBumpFunction I p) := inferInstance
  -- globally smooth scalars
  let f : Fin (Module.finrank ℝ E) → M → ℝ := fun i b => χ b • f₀ i b
  have hf_smooth : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (f i) := by
    intro i
    have hg : ContMDiffOn I 𝓘(ℝ) ∞ (f₀ i) (chartAt H p).source := hbase_eq ▸ hf₀_smoothOn i
    exact χ.contMDiff_smul hg
  have hfp : ∀ i, f i p = 0 := by
    intro i
    show χ p • f₀ i p = 0
    rw [hf₀p i, smul_zero]
  -- globally smooth vector fields, agreeing near `p` with the chart-basis frame
  have hVex : ∀ i : Fin (Module.finrank ℝ E), ∃ V' : SmoothVectorField I M,
      ∀ᶠ y in 𝓝 p, V' y = Tensor.chartBasisVecFiber (I := I) p i y := by
    intro i
    exact exists_smoothVectorField_eventuallyEq (I := I)
      (σ := fun q => Tensor.chartBasisVecFiber (I := I) p i q)
      (s := e.baseSet) hbaseopen (Tensor.chartBasisVec_contMDiffOn (I := I) p i) hp
  choose Vsvf hVsvf using hVex
  refine ⟨f, fun i x => Vsvf i x, hf_smooth, fun i => ?_, hfp, ?_⟩
  · show IsSmoothVectorField (fun x => Vsvf i x)
    simpa using (Vsvf i).smooth
  · have hχ_one : χ =ᶠ[𝓝 p] (1 : M → ℝ) := χ.eventuallyEq_one
    have hVall : ∀ᶠ q in 𝓝 p, ∀ i, Vsvf i q = Tensor.chartBasisVecFiber (I := I) p i q :=
      Filter.eventually_all.mpr hVsvf
    filter_upwards [hbaseopen.mem_nhds hp, hχ_one, hVall] with q hq_mem hq_chi hq_V
    have hZq := hZexpand q hq_mem
    rw [hZq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show f₀ i q • Tensor.chartBasisVecFiber (I := I) p i q = f i q • Vsvf i q
    have hfq : f i q = f₀ i q := by
      show χ q • f₀ i q = f₀ i q
      rw [hq_chi, Pi.one_apply, one_smul]
    rw [hfq, hq_V i]

end PetersenLib
