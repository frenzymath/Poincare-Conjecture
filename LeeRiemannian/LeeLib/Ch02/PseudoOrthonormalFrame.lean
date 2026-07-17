/-
Chapter 2, "Riemannian Metrics", §7 "Pseudo-Riemannian Metrics": existence of smooth
orthonormal frames.

Lee's Proposition 2.66: *let `(M,g)` be a pseudo-Riemannian manifold.  For each `p ∈ M`,
there exists a smooth orthonormal frame on a neighborhood of `p` in `M`.*

Lee leaves the proof as Exercise 2.67, with the intended argument being "apply the
Gram-Schmidt algorithm of Proposition 2.63 to a local frame, and note the formulas are
smooth".  That is exactly the argument of Lee's Proposition 2.8 in the Riemannian case
(`LeeLib.Ch02.OrthonormalFrame`), and this file is deliberately a transcription of it.
Two things are not transcribable, and they are the whole content:

* **There is no fibrewise Gram-Schmidt to call.**  In the Riemannian case mathlib's
  `RiemannianBundle` installs an `InnerProductSpace ℝ (V x)` on each fibre, so
  `gramSchmidtNormed ℝ` applies fibrewise and orthonormality is free.  An indefinite
  form induces no inner product, so the algorithm had to be written out as a formula
  first — that is `LeeLib.Ch02.PseudoGramSchmidt` — and this file makes it smooth.
* **Linear independence is not enough.**  In the Riemannian case any linearly
  independent family can be orthonormalized, so a plain local frame is a valid input
  and `IsLocalIndepOn` is the right hypothesis.  Here the Gram-Schmidt denominators
  `⟪u_j, u_j⟫` can vanish on a linearly independent family — a null vector is nonzero
  and orthogonal to itself — so the input must be a *nondegenerate* tuple at each
  point, Lee's hypothesis in Proposition 2.63.  `IsLocalNondegenerateOn` is that
  condition, and it is strictly stronger than `IsLocalIndepOn`.

The analytic step that replaces `ContMDiffWithinAt.inner_bundle` is
`ContMDiffPseudoMetric.contMDiffOn_pairing`, which says the `g`-pairing of two smooth
sections is a smooth function and holds without positivity.  The one place positivity
is genuinely missed is normalization: `√⟪u_j,u_j⟫` is replaced by `√|⟪u_j,u_j⟫|`, and
`|·|` is not differentiable at `0`.  `contDiffAt_inv_sqrt_abs` below is the small
lemma that handles it — away from `0` the absolute value is locally `±id`, so the
composite is smooth exactly where the denominators do not vanish, which is everywhere
the hypothesis holds.
-/
import LeeLib.AppendixA.LocalFrameCriterion
import LeeLib.Ch02.PseudoGramSchmidt
import LeeLib.Ch02.PseudoRiemannianMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

namespace LeeLib.Ch02

open Bundle Module Submodule
open scoped Manifold ContDiff

/-! ### `(√|·|)⁻¹` is smooth away from the origin -/

/-- **The normalizing scalar of the indefinite Gram-Schmidt is smooth away from `0`.**

`t ↦ (√|t|)⁻¹` is the scalar by which `gramSchmidtBilinNormed` rescales, and unlike the
positive-definite `t ↦ (√t)⁻¹` it involves an absolute value, which is not
differentiable at `0`.  It does not need to be: the Gram-Schmidt denominators are
nonvanishing under Lee's nondegeneracy hypothesis, and away from `0` the absolute value
agrees locally with `id` or with `-id`, both smooth. -/
theorem contDiffAt_inv_sqrt_abs {k : WithTop ℕ∞} {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ k (fun s : ℝ => (Real.sqrt |s|)⁻¹) t := by
  have habs : ContDiffAt ℝ k (fun s : ℝ => |s|) t := by
    rcases ht.lt_or_gt with h | h
    · refine ContDiffAt.congr_of_eventuallyEq (f := fun s : ℝ => -s) contDiffAt_id.neg ?_
      filter_upwards [Iio_mem_nhds h] with s hs
      exact abs_of_neg (Set.mem_Iio.mp hs)
    · refine ContDiffAt.congr_of_eventuallyEq (f := fun s : ℝ => s) contDiffAt_id ?_
      filter_upwards [Ioi_mem_nhds h] with s hs
      exact abs_of_pos (Set.mem_Ioi.mp hs)
  have hsqrt : ContDiffAt ℝ k (fun s : ℝ => Real.sqrt |s|) t :=
    (Real.contDiffAt_sqrt (x := |t|) (abs_ne_zero.mpr ht)).comp t habs
  exact hsqrt.inv (Real.sqrt_ne_zero'.mpr (abs_pos.mpr ht))

section BundleFrame

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} {m : ℕ} {X : Fin m → (x : B) → V x} {u : Set B}

variable (IB F n) in
/-- A family of sections that is `C^n` on `u` and forms a **nondegenerate tuple** in the
fibre at each point of `u` (Lee's hypothesis in Proposition 2.63).

This is the indefinite replacement for `LeeLib.Ch02.IsLocalIndepOn`.  The difference is
not bookkeeping: `IsNondegenerateTuple` requires every step `span (X_1|_x, …, X_k|_x)`
of the flag to be a nondegenerate subspace, which is strictly stronger than linear
independence and is exactly what keeps the Gram-Schmidt denominators away from `0`.
A linearly independent family of null vectors — impossible in the Riemannian case,
routine in a Lorentz metric — is not admissible input. -/
structure IsLocalNondegenerateOn (g : Bundle.ContMDiffPseudoMetric IB n F V)
    (X : Fin m → (x : B) → V x) (u : Set B) where
  nondegenerateTuple {x : B} (hx : x ∈ u) : IsNondegenerateTuple (g.bilin x) (fun i => X i x)
  contMDiffOn (i : Fin m) : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (X i)) u

variable (g : Bundle.ContMDiffPseudoMetric IB n F V)

/-- The **unnormalized fibrewise indefinite Gram-Schmidt** of a family of sections: at
each point `x`, `gramSchmidtBilin` applied in the fibre `V x` against the form `g_x`. -/
noncomputable def pseudoGramSchmidtFrameAux (X : Fin m → (x : B) → V x) (j : Fin m) (x : B) :
    V x :=
  gramSchmidtBilin (g.bilin x) (fun i => X i x) j

/-- The **fibrewise indefinite Gram-Schmidt orthonormalization** of a family of sections
— the family Lee's Proposition 2.66 produces.  It is orthonormal at every point of `u`
in Lee's `±1` sense (`pseudoGramSchmidtFrame_isOrthonormal`) and smooth on `u`
(`contMDiffOn_pseudoGramSchmidtFrame`). -/
noncomputable def pseudoGramSchmidtFrame (X : Fin m → (x : B) → V x) (j : Fin m) (x : B) : V x :=
  gramSchmidtBilinNormed (g.bilin x) (fun i => X i x) j

/-! ### The algebraic half

At each point of `u` the input is a nondegenerate tuple, so the pointwise theory of
`LeeLib.Ch02.PseudoGramSchmidt` applies verbatim in the fibre. -/

/-- The Gram-Schmidt denominators are nowhere zero on `u` — the indefinite case's
burden, and the fact that makes the quotients below smooth. -/
theorem pseudoGramSchmidtFrameAux_apply_self_ne_zero (hX : IsLocalNondegenerateOn IB F n g X u)
    {x : B} (hx : x ∈ u) (j : Fin m) :
    g.bilin x (pseudoGramSchmidtFrameAux g X j x) (pseudoGramSchmidtFrameAux g X j x) ≠ 0 :=
  gramSchmidtBilin_apply_self_ne_zero (g.bilin_isSymm x) (hX.nondegenerateTuple hx) j

/-- **Orthonormality** (Lee, Proposition 2.66): at each point of `u` the orthonormalized
family is orthonormal in the fibre — `⟪E_i, E_j⟫ = 0` for `i ≠ j` and `⟪E_i, E_i⟫ = ±1`. -/
theorem pseudoGramSchmidtFrame_isOrthonormal (hX : IsLocalNondegenerateOn IB F n g X u)
    {x : B} (hx : x ∈ u) :
    IsOrthonormal (g.bilin x) (fun j => pseudoGramSchmidtFrame g X j x) :=
  gramSchmidtBilin_isOrthonormal (g.bilin_isSymm x) (hX.nondegenerateTuple hx)

/-- **The initial span condition** (Lee, Proposition 2.63, carried to the frame):
`span (E_1|_x, …, E_k|_x) = span (X_1|_x, …, X_k|_x)` for every `k`. -/
theorem prefixSpan_pseudoGramSchmidtFrame (hX : IsLocalNondegenerateOn IB F n g X u)
    {x : B} (hx : x ∈ u) (k : ℕ) (hk : k ≤ m) :
    prefixSpan (fun j => pseudoGramSchmidtFrame g X j x) k = prefixSpan (fun i => X i x) k :=
  prefixSpan_gramSchmidtBilinNormed (g.bilin_isSymm x) (hX.nondegenerateTuple hx) k hk

/-- The orthonormalized family is linearly independent at each point of `u`. -/
theorem pseudoGramSchmidtFrame_linearIndependent (hX : IsLocalNondegenerateOn IB F n g X u)
    {x : B} (hx : x ∈ u) :
    LinearIndependent ℝ (fun j => pseudoGramSchmidtFrame g X j x) :=
  (pseudoGramSchmidtFrame_isOrthonormal g hX hx).linearIndependent

/-! ### The analytic half: smoothness of the Gram-Schmidt sections

The induction is along the recursion

  `u_j = X_j - ∑_{i < j} (⟪u_i, X_j⟫ / ⟪u_i, u_i⟫) • u_i`,

in which every ingredient is smooth: `X_j` by hypothesis, `u_i` for `i < j` by the
inductive hypothesis, the pairings by `contMDiffOn_pairing`, and the quotients because
the denominators are nonvanishing on `u`.  This is `contMDiffOn_gramSchmidtFrameAux` of
`LeeLib.Ch02.OrthonormalFrame` with `inner_bundle` swapped for `contMDiffOn_pairing`. -/

/-- **Smoothness of the unnormalized indefinite Gram-Schmidt sections.** -/
theorem contMDiffOn_pseudoGramSchmidtFrameAux (hX : IsLocalNondegenerateOn IB F n g X u)
    (j : Fin m) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (pseudoGramSchmidtFrameAux g X j)) u := by
  induction j using WellFoundedLT.induction with
  | _ j IH =>
    have hc : ∀ i ∈ Finset.Iio j, ContMDiffOn IB 𝓘(ℝ, ℝ) n
        (fun x => g.bilin x (pseudoGramSchmidtFrameAux g X i x) (X j x) /
          g.bilin x (pseudoGramSchmidtFrameAux g X i x)
            (pseudoGramSchmidtFrameAux g X i x)) u := by
      intro i hi
      have hui := IH i (Finset.mem_Iio.mp hi)
      exact ContMDiffOn.div₀
        (g.contMDiffOn_pairing contMDiffOn_id hui (hX.contMDiffOn j))
        (g.contMDiffOn_pairing contMDiffOn_id hui hui)
        fun x hx => pseudoGramSchmidtFrameAux_apply_self_ne_zero g hX hx i
    have hsum : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
        (T% (fun x => ∑ i ∈ Finset.Iio j,
          (g.bilin x (pseudoGramSchmidtFrameAux g X i x) (X j x) /
            g.bilin x (pseudoGramSchmidtFrameAux g X i x)
              (pseudoGramSchmidtFrameAux g X i x)) • pseudoGramSchmidtFrameAux g X i x)) u :=
      ContMDiffOn.sum_section fun i hi => (hc i hi).smul_section (IH i (Finset.mem_Iio.mp hi))
    refine ((hX.contMDiffOn j).sub_section hsum).congr fun x hx => ?_
    exact congrArg (TotalSpace.mk' F x) (gramSchmidtBilin_def (g.bilin x) (fun i => X i x) j)

/-- **Smoothness of the orthonormalized frame** — the analytic content of Lee's
Proposition 2.66.  Normalization divides by `√|⟪u_j,u_j⟫|`, which is smooth and nonzero
on `u` because `⟪u_j,u_j⟫` is smooth and *nonvanishing* there — note "nonvanishing",
not "positive": this is the one line where the Riemannian proof's `√` of a positive
quantity becomes `√` of an absolute value, handled by `contDiffAt_inv_sqrt_abs`. -/
theorem contMDiffOn_pseudoGramSchmidtFrame (hX : IsLocalNondegenerateOn IB F n g X u)
    (j : Fin m) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (pseudoGramSchmidtFrame g X j)) u := by
  have hu := contMDiffOn_pseudoGramSchmidtFrameAux g hX j
  have hq : ContMDiffOn IB 𝓘(ℝ, ℝ) n
      (fun x => g.bilin x (pseudoGramSchmidtFrameAux g X j x)
        (pseudoGramSchmidtFrameAux g X j x)) u :=
    g.contMDiffOn_pairing contMDiffOn_id hu hu
  have hnorm : ContMDiffOn IB 𝓘(ℝ, ℝ) n
      (fun x => (Real.sqrt |g.bilin x (pseudoGramSchmidtFrameAux g X j x)
        (pseudoGramSchmidtFrameAux g X j x)|)⁻¹) u := by
    intro x hx
    exact ContDiffAt.comp_contMDiffWithinAt (g := fun s : ℝ => (Real.sqrt |s|)⁻¹)
      (f := fun y => g.bilin y (pseudoGramSchmidtFrameAux g X j y)
        (pseudoGramSchmidtFrameAux g X j y))
      (contDiffAt_inv_sqrt_abs (pseudoGramSchmidtFrameAux_apply_self_ne_zero g hX hx j))
      (hq x hx)
  exact hnorm.smul_section hu

/-- **Lee's Proposition 2.66 for a general pseudo-Riemannian vector bundle**: the
fibrewise indefinite Gram-Schmidt of a smooth pointwise-nondegenerate family is again
one, and is orthonormal. -/
theorem isLocalNondegenerateOn_pseudoGramSchmidtFrame (hX : IsLocalNondegenerateOn IB F n g X u) :
    ∀ j, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (pseudoGramSchmidtFrame g X j)) u :=
  contMDiffOn_pseudoGramSchmidtFrame g hX

/-! ### Nondegeneracy of a family of sections is an open condition

Everything above is conditional on `IsLocalNondegenerateOn`, which is Lee's hypothesis but is
not something a caller holding only a pseudo-Riemannian manifold can produce: it asserts
nondegeneracy at *every* point of `u`, whereas a construction naturally delivers it at one
point.  This subsection closes that gap, and it is what makes Lee's Proposition 2.66 provable
rather than merely stateable.

The mechanism is `LeeLib.Ch02.isNondegenerateTuple_iff_forall_det_gramMatrix_ne_zero`: it
re-reads nondegeneracy of a tuple as the nonvanishing of finitely many determinants, each of
which is a polynomial in the pairings `⟪X_i, X_j⟫` and hence smooth by
`ContMDiffPseudoMetric.contMDiffOn_pairing`.  Nonvanishing at a point then survives on a
neighbourhood, which is all Lee's "the conditions are open" amounts to. -/

/-- **The leading Gram determinants of a smooth family are smooth.**

`Matrix.det` is a finite sum of finite products of entries, so this reduces to smoothness of
each pairing; no determinant-specific analysis is involved.  Note that mathlib's
`Continuous.matrix_det` is stated only for a *global* `Continuous` and has no `ContinuousOn`
or `ContMDiff` analogue, so the expansion is the route rather than a fallback. -/
theorem contMDiffOn_det_gramMatrix {k : ℕ} {Y : Fin k → (x : B) → V x}
    (hY : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (Y i)) u) :
    ContMDiffOn IB 𝓘(ℝ, ℝ) n (fun x => (gramMatrix (g.bilin x) (fun i => Y i x)).det) u := by
  simp_rw [Matrix.det_apply']
  intro x hx
  refine ContMDiffWithinAt.sum fun σ _ => contMDiffWithinAt_const.mul ?_
  exact ContMDiffWithinAt.prod fun i _ =>
    (g.contMDiffOn_pairing contMDiffOn_id (hY (σ i)) (hY i)) x hx

/-- **Nondegeneracy of a tuple of smooth sections is an open condition** (Lee, the lemma behind
Proposition 2.66): a family of sections that is smooth on an open `u` and nondegenerate *at one
point* `x₀ ∈ u` is nondegenerate on a whole neighbourhood of `x₀`.

This is the converse move to everything above: it *produces* an `IsLocalNondegenerateOn`, at
the cost of shrinking the domain, from data at a single point. -/
theorem exists_isLocalNondegenerateOn_nhds (hu : IsOpen u)
    (hX : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (X i)) u)
    {x₀ : B} (hx₀ : x₀ ∈ u) (h0 : IsNondegenerateTuple (g.bilin x₀) (fun i => X i x₀)) :
    ∃ w : Set B, IsOpen w ∧ x₀ ∈ w ∧ w ⊆ u ∧ IsLocalNondegenerateOn IB F n g X w := by
  rw [isNondegenerateTuple_iff_forall_det_gramMatrix_ne_zero] at h0
  -- each leading Gram determinant is nonzero on a neighbourhood of `x₀`; there are finitely
  -- many, so one neighbourhood serves them all
  have hev : ∀ k ∈ Set.Iic m, ∀ᶠ x in nhds x₀,
      ∀ hk : k ≤ m, (gramMatrix (g.bilin x) (fun i => X (Fin.castLE hk i) x)).det ≠ 0 := by
    intro k hk
    have hk' : k ≤ m := Set.mem_Iic.mp hk
    have hc : ContinuousAt
        (fun x => (gramMatrix (g.bilin x) (fun i => X (Fin.castLE hk' i) x)).det) x₀ :=
      (contMDiffOn_det_gramMatrix g fun i => hX _).continuousOn.continuousAt (hu.mem_nhds hx₀)
    filter_upwards [hc.eventually_ne (h0 k hk')] with x hx _ using hx
  have h := (Filter.eventually_all_finite (Set.finite_Iic m)).mpr hev
  obtain ⟨w, hwsub, hwopen, hx₀w⟩ := mem_nhds_iff.mp (Filter.inter_mem h (hu.mem_nhds hx₀))
  refine ⟨w, hwopen, hx₀w, fun x hx => (hwsub hx).2, ?_, fun i => (hX i).mono ?_⟩
  · intro x hx
    rw [isNondegenerateTuple_iff_forall_det_gramMatrix_ne_zero]
    exact fun k hk => (hwsub hx).1 k (Set.mem_Iic.mpr hk) hk
  · exact fun x hx => (hwsub hx).2

end BundleFrame

section TangentFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {m : ℕ}

/-- **Existence of orthonormal frames for pseudo-Riemannian manifolds**
(Lee, Proposition 2.66 / Exercise 2.67), in the form Lee's Proposition 2.63 gives it.

If `(X_i)` is a smooth family of vector fields on an open set `U` which is a
*nondegenerate tuple* at each point — Lee's hypothesis, and the indefinite replacement
for "a frame" — then there is a smooth family `(E_j)` on `U` which is orthonormal at
each point, `⟪E_i, E_j⟫_g = ±δ_ij`, and reproduces the same flag.

Orthonormality is stated through `g` itself (Lee's own phrasing) rather than through a
fibrewise structure, because in the indefinite case there is no fibrewise
`InnerProductSpace` to state it through — that absence is precisely why this
proposition needed new infrastructure rather than a call to mathlib. -/
theorem exists_pseudo_orthonormalFrame (g : PseudoRiemannianMetric I M)
    {X : Fin m → (x : M) → TangentSpace I x} {u : Set M}
    (hX : IsLocalNondegenerateOn I E ∞ g X u) :
    ∃ Y : Fin m → (x : M) → TangentSpace I x,
      (∀ j, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (Y j)) u) ∧
      (∀ x ∈ u, IsOrthonormal (g.bilin x) (fun j => Y j x)) ∧
      (∀ x ∈ u, ∀ k ≤ m, prefixSpan (fun j => Y j x) k = prefixSpan (fun i => X i x) k) :=
  ⟨pseudoGramSchmidtFrame g X,
    contMDiffOn_pseudoGramSchmidtFrame g hX,
    fun x hx => pseudoGramSchmidtFrame_isOrthonormal g hX hx,
    fun x hx k hk => prefixSpan_pseudoGramSchmidtFrame g hX hx k hk⟩

/-- **Every point of a pseudo-Riemannian manifold has a neighbourhood carrying a smooth
orthonormal frame** (Lee, Proposition 2.66 / Exercise 2.67).

This is Lee's proposition as stated: the only inputs are the metric and the point.  Compare
`exists_pseudo_orthonormalFrame`, which assumes a family that is already nondegenerate at every
point of the given set — Lee's Proposition 2.63 hypothesis, which no caller holding just
`(M, g, p)` can supply.

The three steps that produce that family are exactly where the indefinite case costs more than
the Riemannian one.  In `exists_orthonormalFrame_nhds` (Lee 2.8) *any* local frame may be fed
to Gram-Schmidt, so the trivialization frame induced by an arbitrary basis of `E` is taken and
the proof ends; here the input must be nondegenerate, so:

* a *nondegenerate* basis of `T_p M` is chosen (`exists_isNondegenerateTuple`, Lee 2.62 applied
  to the empty tuple) — an arbitrary basis will not do, since a basis of null vectors is
  perfectly possible in a Lorentz metric;
* it is spread to vector fields near `p` (`exists_contMDiffOn_section_eq_basis`), which needs
  the prescribed-value refinement of mathlib's `localFrame`;
* nondegeneracy is propagated from `p` to a neighbourhood (`exists_isLocalNondegenerateOn_nhds`),
  which is where the Gram determinant criterion earns its keep.

Only then is `exists_pseudo_orthonormalFrame` applicable. -/
theorem exists_pseudo_orthonormalFrame_nhds [FiniteDimensional ℝ E]
    (g : PseudoRiemannianMetric I M) (p : M) :
    ∃ (u : Set M) (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x),
      IsOpen u ∧ p ∈ u ∧ IsLocalFrameOn I E ∞ Y u ∧
      (∀ x ∈ u, IsOrthonormal (g.bilin x) (fun j => Y j x)) := by
  -- a nondegenerate basis of the scalar product space `(T_p M, g_p)`; the index type is
  -- `Fin (finrank ℝ E)` because `TangentSpace I p` is a type synonym for `E`
  obtain ⟨w, hw⟩ : ∃ w : Fin (finrank ℝ E) → TangentSpace I p,
      IsNondegenerateTuple (g.bilin p) w :=
    exists_isNondegenerateTuple (g.bilin_isSymm p) (g.bilin_nondegenerate p)
  have hspan : finrank ℝ (span ℝ (Set.range w)) = finrank ℝ (TangentSpace I p) := by
    rw [← prefixSpan_last w]
    exact (hw _ le_rfl).1
  have hli : LinearIndependent ℝ w :=
    linearIndependent_iff_card_eq_finrank_span.mpr (by simpa [Set.finrank] using hspan.symm)
  let wb : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I p) :=
    Basis.mk hli (Submodule.eq_top_of_finrank_eq hspan).ge
  -- spread it to vector fields near `p`
  obtain ⟨v, Y, hvopen, hpv, hYsmooth, hYeq⟩ :=
    LeeLib.AppendixA.exists_contMDiffOn_section_eq_basis (F := E)
      (V := (TangentSpace I : M → Type _)) I ∞ p wb
  have h0 : IsNondegenerateTuple (g.bilin p) (fun i => Y i p) := by
    have hYw : (fun i => Y i p) = w := by
      funext i
      rw [hYeq i]
      simp [wb, Basis.coe_mk]
    rw [hYw]
    exact hw
  -- nondegeneracy at `p` spreads to a neighbourhood, giving Lee's Proposition 2.63 hypothesis
  obtain ⟨u, huopen, hpu, -, hnd⟩ := exists_isLocalNondegenerateOn_nhds g hvopen hYsmooth hpv h0
  obtain ⟨Z, hZsmooth, hZon, -⟩ := exists_pseudo_orthonormalFrame g hnd
  -- an orthonormal tuple is linearly independent, and `finrank ℝ E` independent vectors span
  -- the `finrank ℝ E`-dimensional space `T_x M`: the frame conditions come for free
  exact ⟨u, Z, huopen, hpu,
    ⟨fun {x} hx => (hZon x hx).linearIndependent,
      fun {x} hx => ((hZon x hx).linearIndependent.span_eq_top_of_card_eq_finrank'
        (Fintype.card_fin _)).ge,
      hZsmooth⟩,
    hZon⟩

end TangentFrame

end LeeLib.Ch02
