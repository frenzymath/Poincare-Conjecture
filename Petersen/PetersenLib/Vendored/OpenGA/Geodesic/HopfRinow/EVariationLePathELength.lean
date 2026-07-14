/- Vendored from DoCarmo `OpenGALib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean`.
   Namespace `Riemannian` mapped to `PetersenLib`; engineering infrastructure only,
   not a blueprint node. -/
import Mathlib.Geometry.Manifold.Riemannian.Basic
import PetersenLib.Vendored.OpenGA.MetricGeometry.LengthSpace

/-!
# ① `dist = ⨅ pathLength` bridge — analytic core

The key lemma behind `Bridges/RiemannianToLength.lean`'s remaining `sorry`
(`⨅ γ, pathLength γ ≤ edist x y`): for a `C¹` path the metric `eVariationOn`
(OpenGA `pathLength`) is bounded by the tangent integral (`Manifold.pathELength`).

Proof map (do Carmo Ch. 7 §2 / Burago–Burago–Ivanov §2.7.1):
```
eVariationOn (↑γ) univ = ⨆_partitions  Σ edist (γ tᵢ₊₁) (γ tᵢ)
  ≤ ⨆_partitions Σ pathELength I γ.extend tᵢ tᵢ₊₁   -- edist = riemannianEDist ≤ pathELength
  = pathELength I γ.extend 0 1                        -- pathELength_add telescoping
```

Once proved, replace the bridge `sorry` with
`le_iInf₂ fun γ hγ ↦ iInf_le_of_le γ (pathLength_le_pathELength γ hγ)`
(after `rw [IsRiemannianManifold.out, riemannianEDist]`).
-/

open Bundle Set Topology
open scoped Manifold ContDiff

namespace OpenGA.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- **Math.** Per-segment bound: on a `C¹` path, the metric distance between two
parameter values is bounded by the tangent-integral length over that subinterval.
`edist (γ a) (γ b) = riemannianEDist ≤ pathELength I γ a b`. -/
theorem edist_le_pathELength_of_cmdiff {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ) (hab : a ≤ b) :
    edist (γ a) (γ b) ≤ Manifold.pathELength I γ a b := by
  rw [IsRiemannianManifold.out (I := I) (γ a) (γ b)]
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

/-- **Math.** **Key lemma (①).** For a `C¹` path `γ : ℝ → M` smooth on `[0,1]`, the
metric `eVariationOn` of `γ` over `[0,1]` is bounded by the tangent-integral length
`pathELength I γ 0 1`. This is the sole remaining content of the metric=length
bridge `Bridges/RiemannianToLength.lean`. -/
theorem eVariationOn_le_pathELength {γ : ℝ → M}
    (hγ : CMDiff[Icc 0 1] 1 γ) :
    eVariationOn γ (Icc 0 1) ≤ Manifold.pathELength I γ 0 1 := by
  -- eVariationOn = ⨆ over monotone partitions of `Σ edist (γ tᵢ₊₁) (γ tᵢ)`;
  -- each term ≤ pathELength over its segment (`edist_le_pathELength_of_cmdiff`);
  -- the telescoped sum collapses to `pathELength I γ 0 1` (`pathELength_add`).
  apply iSup_le
  rintro ⟨n, u, humono, us⟩
  -- each partition segment: edist ≤ pathELength over [u i, u (i+1)] ⊆ [0,1]
  have seg : ∀ i, edist (γ (u (i + 1))) (γ (u i)) ≤ Manifold.pathELength I γ (u i) (u (i + 1)) := by
    intro i
    rw [edist_comm]
    exact edist_le_pathELength_of_cmdiff
      (hγ.mono (Icc_subset_Icc (us i).1 (us (i + 1)).2)) (humono (Nat.le_succ i))
  -- telescoping: Σ_{i<m} pathELength (u i) (u (i+1)) = pathELength (u 0) (u m)
  have tele : ∀ m, ∑ i ∈ Finset.range m, Manifold.pathELength I γ (u i) (u (i + 1))
      = Manifold.pathELength I γ (u 0) (u m) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih,
        Manifold.pathELength_add (humono (Nat.zero_le k)) (humono (Nat.le_succ k))]
  calc ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
      ≤ ∑ i ∈ Finset.range n, Manifold.pathELength I γ (u i) (u (i + 1)) :=
        Finset.sum_le_sum fun i _ ↦ seg i
    _ = Manifold.pathELength I γ (u 0) (u n) := tele n
    _ ≤ Manifold.pathELength I γ 0 1 := Manifold.pathELength_mono (us 0).1 (us n).2

end OpenGA.HopfRinow
