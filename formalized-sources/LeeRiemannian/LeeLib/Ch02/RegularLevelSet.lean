/-
Chapter 2, "Riemannian Metrics", §"Raising and Lowering Indices": **Proposition
2.37** — a regular level set of `f ∈ C^∞(M)` is an embedded hypersurface, and
`grad f` is everywhere normal to it.

Lee states the proposition for `M_c = f⁻¹(c) ∩ ℛ`, where `ℛ` is the set of
regular points of `f`.  The two halves are proved separately here:

* the **hypersurface structure** is `LevelSetChartedSpace.lean`
  (`levelSetChartedSpace`, `isManifold_levelSet`, `contMDiff_levelSet_val`) —
  Lee's Corollary A.26 in codimension one, whose global assembly the pinned
  mathlib does not have in any form;
* the **normality of `grad f`** is this file, and is where the Riemannian
  metric finally enters.

## What "normal" means here

Lee's `grad f|_p ⊥ T_p M_c` is, after the identification `T_p M_c = ker df_p`
(`range_mfderiv_levelSet_val`), the statement that `⟨grad f|_p, w⟩ = 0` for
every `w` in the range of the inclusion differential.  That is
`innerAt_grad_eq_zero_of_mem_ker` transported along the identification, which
is `innerAt_grad_mfderiv_levelSet_val_eq_zero` below.

The converse — every `g`-orthogonal direction to `grad f|_p` *is* tangent to
`M_c` — also holds and is proved here
(`exists_mfderiv_levelSet_val_eq_of_innerAt_grad_eq_zero`), so together the two
say that `T_p M_c` is exactly the `g`-orthogonal complement of `grad f|_p`:
the normal bundle of a regular level set is spanned by the gradient.  This is
the form Lee actually uses when he computes with hypersurfaces.

## Scope: regular value versus regular part

Everything below is stated for a **regular value** — `hreg` says `df_x ≠ 0` at
every point of `f⁻¹(c)` — rather than for Lee's `M_c = f⁻¹(c) ∩ ℛ`, which keeps
only the regular part of a possibly-critical level set.  `regularSet` (Lee's
`ℛ`) is defined here and characterised as the non-vanishing locus of `grad f`,
but the reduction of the general statement to the regular-value one is **not**
carried out: it needs `ℛ` to be open, which is not proved here.  See the note
at the bottom of the file for what that proof requires.
-/
import LeeLib.Ch02.LevelSetChartedSpace
import LeeLib.Ch02.MusicalIsomorphism
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set Function
open scoped Manifold Topology ContDiff

noncomputable section

namespace LeeLib.Ch02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ### The gradient and the kernel of the differential -/

section GradKer

variable (g : RiemannianMetric I M) (f : M → ℝ) (p : M)

/-- **The gradient detects the kernel of the differential**: `w` is `g`-orthogonal
to `grad f|_p` if and only if `df_p w = 0`.

The forward direction is Lee's (2.14) read backwards; the converse is
`innerAt_grad_eq_zero_of_mem_ker`.  Both are immediate from
`⟨grad f|_p, w⟩ = df_p w`, once one notes that the identification of
`TangentSpace 𝓘(ℝ, ℝ) (f p)` with `ℝ` is an equivalence and so detects zero. -/
theorem innerAt_grad_eq_zero_iff (w : TangentSpace I p) :
    g.innerAt p (grad g f p) w = 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f p w = 0 := by
  refine ⟨fun h => ?_, innerAt_grad_eq_zero_of_mem_ker g f p w⟩
  rw [innerAt_grad] at h
  -- `extDerivFun f p w` is `fromTangentSpace (f p) (df_p w)`, and
  -- `fromTangentSpace` is a continuous linear equivalence, hence injective.
  have h' : (NormedSpace.fromTangentSpace (f p)).toContinuousLinearMap
      (mfderiv I 𝓘(ℝ, ℝ) f p w) = 0 := h
  have := (NormedSpace.fromTangentSpace (f p)).injective
    (a₁ := mfderiv I 𝓘(ℝ, ℝ) f p w) (a₂ := 0) (by simpa using h')
  exact this

end GradKer

/-! ### The regular-point set -/

section RegularSet

variable (I) in
/-- **The set of regular points of `f`** — Lee's `ℛ`: the points where the
differential does not vanish. -/
def regularSet (f : M → ℝ) : Set M := {x : M | mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0}

@[simp] theorem mem_regularSet_iff (f : M → ℝ) (x : M) :
    x ∈ regularSet I f ↔ mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := Iff.rfl

/-- The regular points of `f` are exactly the points where `grad f` does not
vanish — Lee's remark following the definition of the gradient. -/
theorem mem_regularSet_iff_grad_ne_zero (g : RiemannianMetric I M) (f : M → ℝ)
    (x : M) : x ∈ regularSet I f ↔ grad g f x ≠ 0 := by
  rw [mem_regularSet_iff, ne_eq, ne_eq, grad_eq_zero_iff]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · ext w
    simp only [ContinuousLinearMap.zero_apply]
    exact congrArg (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap
      (congrFun (congrArg DFunLike.coe h) w) |>.trans (by simp)
  · ext w
    have := congrFun (congrArg DFunLike.coe h) w
    simp only [ContinuousLinearMap.zero_apply] at this ⊢
    exact (NormedSpace.fromTangentSpace (f x)).injective (by simpa using this)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **The non-vanishing locus of the differential of a smooth map is open.**

`x ↦ df_x` is a family of maps between *varying* tangent spaces, so it has no
continuity statement to quote directly.  Reading it in tangent coordinates fixes
that: `inTangentCoordinates I I' id f (mfderiv f) x₀` is an honest map into the
fixed model space `E →L[ℝ] E'`, it is smooth at `x₀` by
`ContMDiffAt.mfderiv_const`, and on the base sets of the two trivializations it
is `df_x` conjugated by the trivialization equivalences — so it vanishes exactly
where `df_x` does.  Openness is then the openness of `{L | L ≠ 0}` pulled back
along a continuous map. -/
theorem isOpen_setOf_mfderiv_ne_zero
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {f : M → M'} (hf : ContMDiff I I' ∞ f) :
    IsOpen {x : M | mfderiv I I' f x ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I') (f x₀) with htT
  have hx₀s : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : f x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') (f x₀)
  set D := inTangentCoordinates I I' id f (fun x => mfderiv I I' f x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    ContMDiffAt.mfderiv_const (I := I) (I' := I') hf.contMDiffAt (by simp)
  -- In tangent coordinates the differential is conjugated by the two trivializations.
  have hDu : ∀ x, ∀ hx : x ∈ sT.baseSet, ∀ hfx : f x ∈ tT.baseSet, ∀ u : E,
      D x u = tT.continuousLinearEquivAt ℝ (f x) hfx
        (mfderiv I I' f x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
    intro x hx hfx u
    rw [hD]
    simp only [inTangentCoordinates, id_eq]
    rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
    rfl
  -- Hence it vanishes exactly where the differential does.
  have key : ∀ x, ∀ hx : x ∈ sT.baseSet, ∀ hfx : f x ∈ tT.baseSet,
      (D x = 0 ↔ mfderiv I I' f x = 0) := by
    intro x hx hfx
    constructor
    · intro h
      ext v
      have hu := hDu x hx hfx (sT.continuousLinearEquivAt ℝ x hx v)
      rw [h] at hu
      simp only [ContinuousLinearMap.zero_apply, ContinuousLinearEquiv.symm_apply_apply] at hu
      have := (tT.continuousLinearEquivAt ℝ (f x) hfx).map_eq_zero_iff.mp hu.symm
      simp [this]
    · intro h
      ext u
      rw [hDu x hx hfx u, h]
      simpa using (tT.continuousLinearEquivAt ℝ (f x) hfx).map_zero
  have hDx₀ : D x₀ ≠ 0 := fun h => hx₀ ((key x₀ hx₀s hfx₀).mp h)
  have hbase : {x : M | f x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hf.continuous.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hDsmooth.continuousAt (isOpen_ne.mem_nhds hDx₀),
    sT.open_baseSet.mem_nhds hx₀s, hbase] with x hx hxs hxf
  exact fun h0 => hx ((key x hxs hxf).mpr h0)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **The regular set is open** — the step Lee leaves implicit when he restricts a
possibly-critical level set to its regular part.  This is the case `M' = ℝ` of
`isOpen_setOf_mfderiv_ne_zero`. -/
theorem isOpen_regularSet {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    IsOpen (regularSet I f) :=
  isOpen_setOf_mfderiv_ne_zero hf

end RegularSet

/-! ### Proposition 2.37: `grad f` is normal to a regular level set -/

section Normal

variable {f : M → ℝ} (g : RiemannianMetric I M) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] (c : ℝ)

/-- **Proposition 2.37, second half — `grad f` is normal to the level set.**

For every tangent vector `w` of the hypersurface `f ⁻¹' {c}` at `x₀`, the
gradient of `f` is `g`-orthogonal to the corresponding tangent vector
`dι(w) ∈ T_{x₀} M` of the ambient manifold.

This is Lee's assertion that `grad f` is everywhere normal to `M_c`.  Its
content is the identification `T_p M_c = ker df_p` (`range_mfderiv_levelSet_val`
supplies the harder inclusion, though only the easy one is needed here) plus
the pointwise fact `⟨grad f|_p, ·⟩ = df_p`. -/
theorem innerAt_grad_mfderiv_levelSet_val_eq_zero
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) (w : EuclideanSpace ℝ (Fin n)) :
    letI := levelSetChartedSpace hf n c hreg
    g.innerAt ↑x₀ (grad g f ↑x₀)
        (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀ w) = 0 := by
  letI := levelSetChartedSpace hf n c hreg
  exact innerAt_grad_eq_zero_of_mem_ker g f ↑x₀ _
    (mfderivReal_mfderiv_levelSet_val hf n c hreg x₀ w)

/-- **The normal direction is exactly the gradient direction.**

Conversely to `innerAt_grad_mfderiv_levelSet_val_eq_zero`: every ambient
tangent vector at `x₀` that is `g`-orthogonal to `grad f|_{x₀}` *is* tangent to
the level set.  Together the two say that `T_{x₀} M_c` is precisely the
`g`-orthogonal complement of `grad f|_{x₀}` in `T_{x₀} M`, which is the
statement Lee's hypersurface computations use.

This direction is the one that needs the full strength of
`range_mfderiv_levelSet_val`: it is a dimension count, not a computation. -/
theorem exists_mfderiv_levelSet_val_eq_of_innerAt_grad_eq_zero
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (x₀ : (f ⁻¹' {c} : Set M)) (u : E)
    (hu : g.innerAt ↑x₀ (grad g f ↑x₀) u = 0) :
    letI := levelSetChartedSpace hf n c hreg
    ∃ w : EuclideanSpace ℝ (Fin n),
      (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) x₀ w : E) = u := by
  letI := levelSetChartedSpace hf n c hreg
  have hker : u ∈ levelHyperplane (I := I) f ↑x₀ :=
    (mem_levelHyperplane_iff (I := I) f ↑x₀ u).2
      ((innerAt_grad_eq_zero_iff g f ↑x₀ u).1 hu)
  rw [← range_mfderiv_levelSet_val hf n c hreg x₀] at hker
  -- `LinearMap.range` is `Set.range` on the nose, so membership destructures
  -- directly; `LinearMap.mem_range` cannot fire here because its
  -- `RingHomSurjective` instance argument is still a metavariable.
  obtain ⟨w, hw⟩ := hker
  exact ⟨w, hw⟩

end Normal

/-!
### Proposition 2.37 for a possibly-critical level set

Lee's `M_c = f⁻¹(c) ∩ ℛ` allows the level set to contain critical points, and
keeps only its regular part.  Everything above is stated for a *regular value*
(`hreg`: `df_x ≠ 0` at every point of `f⁻¹(c)`), which is the case Lee's own
proof reduces to and the case his applications use.

The reduction of the general statement to this one is carried out in
`RegularSetHypersurface.lean`, on top of the openness of `ℛ` proved here
(`isOpen_regularSet`): `ℛ` is an open submanifold of `M`, `M_c` is the level set
of `f|_ℛ` at `c`, and `c` is a regular value of that restriction *by
construction*, because restricting to an open set does not change the
differential.

Openness did not need the chart comparison an earlier note here called for:
rather than identify `df_x` with the derivative of a chart representative,
`isOpen_setOf_mfderiv_ne_zero` reads `x ↦ df_x` in *tangent* coordinates, where
mathlib's `ContMDiffAt.mfderiv_const` already supplies smoothness and the
trivialization equivalences make vanishing of the coordinate representation
equivalent to vanishing of `df_x`.

The remaining transfer needed `d(ℛ ↪ M) = id` for `ℛ` open in an *arbitrary*
manifold.  An earlier note here cited `OpenSubmanifold.lean` for that, but at the
time that file proved it only for an open subset of a normed space (the flat case
`W : Opens F` used by `PolarCoordinates.lean`); the general form has since been
added there (`mfderiv_opens_subtypeVal`, `mfderiv_opens_restrict`).
-/

end LeeLib.Ch02

end
