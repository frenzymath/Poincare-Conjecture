import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Evans, Ch. 1 §1.5 & Appendix A — multiindex partial derivatives `Dᵅ`

Evans' Chapter 1 problems (Exercises 3 and 4) and all of Appendix A are phrased in
the **multiindex notation** for partial derivatives: for a multiindex
`α = (α₁, …, αₙ)` and a smooth `f : ℝⁿ → ℝ`,
`Dᵅ f = ∂^{α₁}_{x₁} ⋯ ∂^{αₙ}_{xₙ} f`.

Mathlib has no such coordinate multiindex operator — everything is phrased through
the coordinate-free iterated Fréchet derivative `iteratedFDeriv` (a symmetric
`k`-linear form). This file builds the missing infrastructure directly:

* `EvansLib.partialDeriv i f = ∂f/∂xᵢ`, the `i`-th partial derivative of
  `f : EuclideanSpace ℝ (Fin n) → ℝ`, defined as the directional derivative
  `x ↦ Df(x)(eᵢ)` along the `i`-th standard basis vector.
* Smoothness is preserved: `ContDiff.partialDeriv`, `ContDiff.partialDeriv_iterate`.
* **Clairaut / Schwarz symmetry in coordinate form**: partial derivatives of a
  smooth function commute, `partialDeriv_comm` and `partialDeriv_iterate_comm`.

These are the reusable building blocks for the multiindex Leibniz rule (Evans
Ch. 1, Exercise 3) and multiindex Taylor formula (Exercise 4).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19),
Appendix A.2–A.3 and §1.5.
-/

open scoped BigOperators ContDiff

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The **`i`-th partial derivative** `∂f/∂xᵢ` of a function
`f : ℝⁿ → ℝ` (with `ℝⁿ = EuclideanSpace ℝ (Fin n)`), defined as the directional
derivative of `f` along the `i`-th standard basis vector `eᵢ`:
`(partialDeriv i f)(x) = Df(x)(eᵢ)`. -/
def partialDeriv (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

lemma partialDeriv_apply (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    partialDeriv i f x = fderiv ℝ f x (EuclideanSpace.single i 1) := rfl

/-- Taking a partial derivative preserves smoothness. -/
theorem partialDeriv_contDiff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (partialDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Iterating a partial derivative preserves smoothness. -/
theorem partialDeriv_iterate_contDiff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) (m : ℕ) :
    ContDiff ℝ ∞ ((partialDeriv i)^[m] f) := by
  induction m generalizing f with
  | zero => simpa using hf
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (partialDeriv_contDiff hf i)

/-- **Clairaut's theorem in coordinate form.** For a smooth function the mixed
second partial derivatives agree: `∂ᵢ ∂ⱼ f = ∂ⱼ ∂ᵢ f`. -/
theorem partialDeriv_comm {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin n) : partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  funext x
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp; decide)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  unfold partialDeriv
  rw [fderiv_clm_apply (hdf.differentiable (by simp)).differentiableAt (differentiableAt_const _)]
  rw [fderiv_clm_apply (hdf.differentiable (by simp)).differentiableAt (differentiableAt_const _)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add]
  exact hsymm.eq _ _

/-- Iterated partial derivatives along different axes commute: `∂ᵢ (∂ⱼ)^m f =
(∂ⱼ)^m (∂ᵢ f)` for smooth `f`. -/
theorem partialDeriv_iterate_comm (i j : Fin n) (m : ℕ) :
    ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, ContDiff ℝ ∞ f →
      partialDeriv i ((partialDeriv j)^[m] f) = (partialDeriv j)^[m] (partialDeriv i f) := by
  induction m with
  | zero => intro f _; simp
  | succ k ih =>
    intro f hf
    simp only [Function.iterate_succ_apply']
    rw [partialDeriv_comm (partialDeriv_iterate_contDiff hf j k), ih hf]

/-! ## Reduction to one variable along a line -/

/-- The restriction of a differentiable `f : ℝⁿ → ℝ` to the line `s ↦ x + s • v`
has derivative the directional derivative `Df(x + t•v)(v)`. -/
lemma hasDerivAt_comp_line {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Differentiable ℝ f)
    (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline

/-- **Reduction to one variable.** The `m`-fold ordinary derivative of the line
restriction `t ↦ f(x + t • eᵢ)` equals the `m`-fold `i`-th partial derivative of
`f` evaluated along that line. This transports one-variable calculus (iterated
`deriv`) to the `i`-th coordinate direction of the multivariable calculus. -/
lemma iteratedDeriv_comp_line (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, ContDiff ℝ ∞ f →
      iteratedDeriv m (fun t : ℝ => f (x + t • EuclideanSpace.single i 1))
        = fun s : ℝ => (partialDeriv i)^[m] f (x + s • EuclideanSpace.single i 1) := by
  induction m with
  | zero => intro f _; funext s; simp
  | succ k ih =>
    intro f hf
    rw [iteratedDeriv_succ, ih hf]
    funext s
    have hsmooth : ContDiff ℝ ∞ ((partialDeriv i)^[k] f) := partialDeriv_iterate_contDiff hf i k
    rw [(hasDerivAt_comp_line (hsmooth.differentiable (by simp)) x
          (EuclideanSpace.single i 1) s).deriv, Function.iterate_succ_apply']
    rfl

/-! ## Single-axis iterated Leibniz rule -/

/-- **Single-axis iterated Leibniz rule.** For smooth `u, v : ℝⁿ → ℝ` the `m`-fold
`i`-th partial derivative of a product expands by the binomial formula
`∂ᵢ^m (u·v) = ∑_{j ≤ m} \binom{m}{j} (∂ᵢ^j u)(∂ᵢ^{m-j} v)`. This is the one-axis
special case of the multiindex Leibniz rule, obtained from the one-variable
`iteratedDeriv_mul` by restricting to the line through `x` in direction `eᵢ`. -/
theorem partialDeriv_iterate_mul {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (i : Fin n) (m : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (partialDeriv i)^[m] (fun y => u y * v y) x
      = ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * (partialDeriv i)^[j] u x * (partialDeriv i)^[m - j] v x := by
  have key : ∀ (r : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ ∞ w →
      (partialDeriv i)^[r] w x
        = iteratedDeriv r (fun t : ℝ => w (x + t • EuclideanSpace.single i 1)) 0 := by
    intro r w hw
    have h := congrFun (iteratedDeriv_comp_line i x r hw) 0
    simp only [zero_smul, add_zero] at h
    exact h.symm
  have haffine : ContDiff ℝ ∞ (fun t : ℝ => x + t • EuclideanSpace.single i 1) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hlu : ContDiffAt ℝ (m : WithTop ℕ∞)
      (fun t : ℝ => u (x + t • EuclideanSpace.single i 1)) 0 :=
    (hu.comp haffine).contDiffAt.of_le (by exact_mod_cast le_top)
  have hlv : ContDiffAt ℝ (m : WithTop ℕ∞)
      (fun t : ℝ => v (x + t • EuclideanSpace.single i 1)) 0 :=
    (hv.comp haffine).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [key m _ (hu.mul hv)]
  have hmul : (fun t : ℝ => (fun y => u y * v y) (x + t • EuclideanSpace.single i 1))
      = (fun t : ℝ => u (x + t • EuclideanSpace.single i 1))
          * (fun t : ℝ => v (x + t • EuclideanSpace.single i 1)) := by
    funext t; simp [Pi.mul_apply]
  rw [hmul, iteratedDeriv_mul hlu hlv]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [key j u hu, key (m - j) v hv]

/-! ## The multiindex derivative `Dᵅ` (Evans, Appendix A.3) -/

/-- The **multiindex partial derivative** `Dᵅf = ∂^{α₁}_{x₁} ⋯ ∂^{αₙ}_{xₙ} f` of
`f : ℝⁿ → ℝ`, for a multiindex `α : Fin n → ℕ`. It is defined by iterating each
coordinate partial `∂ᵢ` exactly `αᵢ` times (in a fixed axis order); for a smooth
function `partialDeriv_multiPartial_comm` shows the order is immaterial. -/
def multiPartial (α : Fin n → ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  (List.finRange n).foldr (fun i g => (partialDeriv i)^[α i] g) f

/-- Smoothness of a foldr of iterated partials over an arbitrary axis list. -/
private lemma contDiff_foldr (β : Fin n → ℕ) (L : List (Fin n)) :
    ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, ContDiff ℝ ∞ f →
      ContDiff ℝ ∞ (L.foldr (fun j g => (partialDeriv j)^[β j] g) f) := by
  induction L with
  | nil => intro f hf; simpa using hf
  | cons j l ih =>
    intro f hf; simp only [List.foldr_cons]
    exact partialDeriv_iterate_contDiff (ih hf) j (β j)

/-- `partialDeriv i` commutes with a foldr of iterated partials over any axis list. -/
private lemma partialDeriv_foldr_comm (i : Fin n) (β : Fin n → ℕ) (L : List (Fin n)) :
    ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, ContDiff ℝ ∞ f →
      partialDeriv i (L.foldr (fun j g => (partialDeriv j)^[β j] g) f)
        = L.foldr (fun j g => (partialDeriv j)^[β j] g) (partialDeriv i f) := by
  induction L with
  | nil => intro f _; simp
  | cons j l ih =>
    intro f hf; simp only [List.foldr_cons]
    rw [partialDeriv_iterate_comm i j (β j) (contDiff_foldr β l hf), ih hf]

/-- `Dᵅ` of a smooth function is smooth. -/
theorem multiPartial_contDiff {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (α : Fin n → ℕ) : ContDiff ℝ ∞ (multiPartial α f) :=
  contDiff_foldr α (List.finRange n) hf

/-- The empty multiindex gives the identity: `D⁰f = f`. -/
@[simp] theorem multiPartial_zero (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    multiPartial (0 : Fin n → ℕ) f = f := by
  unfold multiPartial
  have hbody : (fun (i : Fin n) (g : EuclideanSpace ℝ (Fin n) → ℝ) =>
      (partialDeriv i)^[(0 : Fin n → ℕ) i] g) = fun _ g => g := by
    funext i g; simp
  rw [hbody]
  induction (List.finRange n) with
  | nil => rfl
  | cons i l ih => exact ih

/-- **Clairaut's theorem for `Dᵅ`.** A single partial derivative commutes with the
multiindex derivative `Dᵅ` on smooth functions, so the fixed axis order used in
the definition of `multiPartial` does not affect the result. -/
theorem partialDeriv_multiPartial_comm {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) (α : Fin n → ℕ) :
    partialDeriv i (multiPartial α f) = multiPartial α (partialDeriv i f) :=
  partialDeriv_foldr_comm i α (List.finRange n) hf

/-! ## Linearity of the partial derivative (for the multiindex Leibniz rule)

The multiindex Leibniz rule is proved axis-by-axis: peeling one axis off the
`foldr` defining `multiPartial` and applying the single-axis rule
`partialDeriv_iterate_mul` to each summand of the inductive hypothesis. That last
step needs `(partialDeriv i)^[m]` to distribute over the finite sum and to pull
out the (constant) binomial coefficients, which the next few lemmas provide. -/

/-- A partial derivative pulls out a scalar: `∂ᵢ(c·f) = c·∂ᵢf`. -/
theorem partialDeriv_smul (i : Fin n) (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    partialDeriv i (c • f) = c • partialDeriv i f := by
  funext x
  simp only [partialDeriv, Pi.smul_apply, fderiv_const_smul_field,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- A partial derivative distributes over a finite sum of differentiable functions. -/
theorem partialDeriv_fun_sum (i : Fin n) {ι : Type*} (s : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hF : ∀ a ∈ s, Differentiable ℝ (F a)) :
    partialDeriv i (fun x => ∑ a ∈ s, F a x)
      = fun x => ∑ a ∈ s, partialDeriv i (F a) x := by
  funext x
  simp only [partialDeriv]
  rw [fderiv_fun_sum (fun a ha => (hF a ha x)), ContinuousLinearMap.sum_apply]

/-- Iterating: `(∂ᵢ)^[m](c•f) = c•(∂ᵢ)^[m]f`. -/
theorem partialDeriv_iterate_smul (i : Fin n) (m : ℕ) (c : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (partialDeriv i)^[m] (c • f) = c • (partialDeriv i)^[m] f := by
  induction m generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, partialDeriv_smul, ih, ← Function.iterate_succ_apply]

/-- Iterating: `(∂ᵢ)^[m](c·f) = c·(∂ᵢ)^[m]f` (multiplicative form). -/
theorem partialDeriv_iterate_const_mul (i : Fin n) (m : ℕ) (c : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (partialDeriv i)^[m] (fun x => c * f x) = fun x => c * (partialDeriv i)^[m] f x := by
  have h1 : (fun x => c * f x) = c • f := by funext x; simp [Pi.smul_apply, smul_eq_mul]
  rw [h1, partialDeriv_iterate_smul]
  funext x; simp [Pi.smul_apply, smul_eq_mul]

/-- Iterating: `(∂ᵢ)^[m]` distributes over a finite sum of smooth functions. -/
theorem partialDeriv_iterate_fun_sum (i : Fin n) (m : ℕ) {ι : Type*} (s : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hF : ∀ a ∈ s, ContDiff ℝ ∞ (F a)) :
    (partialDeriv i)^[m] (fun x => ∑ a ∈ s, F a x)
      = fun x => ∑ a ∈ s, (partialDeriv i)^[m] (F a) x := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      partialDeriv_fun_sum i s (fun a => (partialDeriv i)^[k] (F a))
        (fun a ha => (partialDeriv_iterate_contDiff (hF a ha) i k).differentiable (by simp))]
    funext x
    exact Finset.sum_congr rfl (fun a _ => by rw [Function.iterate_succ_apply'])

/-! ## Combinatorial bookkeeping for the multiindex Leibniz rule

The multiindex Leibniz rule is proved by induction on the list of axes `L` that
`multiPartial` folds over. At the intermediate stage only the axes already in `L`
carry a nonzero exponent in the running sum, so the summation multiindex `γ`
ranges over `∏_{k} {0,…,mask L α k}` where `mask L α` zeroes out the axes not yet
processed. Peeling the head axis `i` off `L` splits that product-of-ranges by the
`i`-th coordinate; `sum_piFinset_update_cons` records this bijection. -/

/-- `maskExp L α` agrees with `α` on the axes in `L` and is `0` elsewhere. It is
the exponent multiindex that bounds the summation index of the partially-unfolded
Leibniz sum after processing exactly the axes in `L`. -/
private def maskExp (L : List (Fin n)) (α : Fin n → ℕ) : Fin n → ℕ :=
  fun k => if k ∈ L then α k else 0

private lemma maskExp_cons (i : Fin n) (l : List (Fin n)) (α : Fin n → ℕ) :
    maskExp (i :: l) α = Function.update (maskExp l α) i (α i) := by
  funext k
  rw [Function.update_apply]
  by_cases hk : k = i
  · rw [if_pos hk, hk]; simp [maskExp]
  · rw [if_neg hk]; simp [maskExp, List.mem_cons, hk]

private lemma maskExp_finRange (α : Fin n → ℕ) : maskExp (List.finRange n) α = α := by
  funext k; simp [maskExp, List.mem_finRange]

private lemma maskExp_self_zero (i : Fin n) (l : List (Fin n)) (hi : i ∉ l) (α : Fin n → ℕ) :
    maskExp l α i = 0 := by simp [maskExp, hi]

/-- Two exponent multiindices that agree on all axes in `L` give the same iterated
partial-derivative fold. -/
private lemma foldr_partial_congr (L : List (Fin n)) (β γ : Fin n → ℕ)
    (h : ∀ k ∈ L, β k = γ k) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    L.foldr (fun k g => (partialDeriv k)^[β k] g) f
      = L.foldr (fun k g => (partialDeriv k)^[γ k] g) f := by
  induction L with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [h j (List.mem_cons_self ..), ih (fun k hk => h k (List.mem_cons_of_mem _ hk))]

/-- **Coordinate split of the summation index.** Summing over the product of ranges
bounded by `maskExp (i :: l) α` is the same as summing over the product bounded by
`maskExp l α` (which forces coordinate `i` to `0`) and then over `{0,…,α i}` at
coordinate `i`, reassembled with `Function.update`. -/
private lemma sum_piFinset_update_cons {M : Type*} [AddCommMonoid M]
    (i : Fin n) (l : List (Fin n)) (hi : i ∉ l) (α : Fin n → ℕ) (G : (Fin n → ℕ) → M) :
    ∑ γ ∈ Fintype.piFinset (fun k => Finset.range (maskExp (i :: l) α k + 1)), G γ
      = ∑ γ₀ ∈ Fintype.piFinset (fun k => Finset.range (maskExp l α k + 1)),
          ∑ j ∈ Finset.range (α i + 1), G (Function.update γ₀ i j) := by
  have key : ∑ γ ∈ Fintype.piFinset (fun k => Finset.range (maskExp (i :: l) α k + 1)), G γ
      = ∑ p ∈ (Fintype.piFinset (fun k => Finset.range (maskExp l α k + 1)) ×ˢ
                Finset.range (α i + 1)), G (Function.update p.1 i p.2) := by
    refine Finset.sum_nbij' (fun γ => (Function.update γ i 0, γ i))
      (fun p => Function.update p.1 i p.2) ?_ ?_ ?_ ?_ ?_
    · -- forward maps into the product
      intro γ hγ
      rw [Fintype.mem_piFinset] at hγ
      rw [Finset.mem_product]
      dsimp only
      refine ⟨?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro k
        rw [Function.update_apply]
        by_cases hk : k = i
        · rw [if_pos hk]; exact Finset.mem_range.2 (Nat.succ_pos _)
        · rw [if_neg hk]
          have h := hγ k
          rwa [maskExp_cons i l, Function.update_apply, if_neg hk] at h
      · have h := hγ i
        rwa [maskExp_cons i l, Function.update_apply, if_pos rfl] at h
    · -- backward maps into the source
      intro p hp
      rw [Finset.mem_product] at hp
      rw [Fintype.mem_piFinset]
      intro k
      dsimp only
      rw [maskExp_cons i l, Function.update_apply, Function.update_apply]
      by_cases hk : k = i
      · rw [if_pos hk, if_pos hk]; exact hp.2
      · rw [if_neg hk, if_neg hk]; exact (Fintype.mem_piFinset.1 hp.1) k
    · -- left inverse: j (i γ) = γ
      intro γ _
      funext k
      dsimp only
      by_cases hk : k = i
      · rw [hk]; simp
      · rw [Function.update_apply, if_neg hk, Function.update_apply, if_neg hk]
    · -- right inverse: i (j p) = p
      intro p hp
      rw [Finset.mem_product] at hp
      have hp1i : p.1 i = 0 := by
        have h := (Fintype.mem_piFinset.1 hp.1) i
        rw [Finset.mem_range, maskExp_self_zero i l hi] at h
        omega
      refine Prod.ext ?_ ?_
      · funext k
        dsimp only
        by_cases hk : k = i
        · rw [hk]; simp [hp1i]
        · rw [Function.update_apply, if_neg hk, Function.update_apply, if_neg hk]
      · dsimp only; simp
    · -- value equality: G γ = G (j (i γ))
      intro γ _
      dsimp only
      congr 1
      funext k
      by_cases hk : k = i
      · rw [hk]; simp
      · rw [Function.update_apply, if_neg hk, Function.update_apply, if_neg hk]
  rw [key]
  exact Finset.sum_product' _ _ (fun γ₀ j => G (Function.update γ₀ i j))

/-! ## The multiindex Leibniz rule (Evans, Ch. 1, Exercise 3) -/

/-- Applying `(∂ᵢ)^[m]` to a finite sum of products and expanding each by the
single-axis Leibniz rule. This is the analytic core of one inductive step of the
multiindex Leibniz rule. -/
private lemma partialDeriv_iterate_sum_mul (i : Fin n) (m : ℕ) {ι : Type*} (s : Finset ι)
    (C : ι → ℝ) (U V : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (hU : ∀ a ∈ s, ContDiff ℝ ∞ (U a)) (hV : ∀ a ∈ s, ContDiff ℝ ∞ (V a)) :
    (partialDeriv i)^[m] (fun x => ∑ a ∈ s, C a * U a x * V a x)
      = fun x => ∑ a ∈ s, ∑ j ∈ Finset.range (m + 1),
          C a * (m.choose j : ℝ) * (partialDeriv i)^[j] (U a) x
            * (partialDeriv i)^[m - j] (V a) x := by
  have hbody : (fun x => ∑ a ∈ s, C a * U a x * V a x)
      = fun x => ∑ a ∈ s, C a * (U a x * V a x) := by
    funext x; exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _
  rw [hbody, partialDeriv_iterate_fun_sum i m s (fun a => fun x => C a * (U a x * V a x))
      (fun a ha => contDiff_const.mul ((hU a ha).mul (hV a ha)))]
  funext x
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [partialDeriv_iterate_const_mul i m (C a) (fun y => U a y * V a y)]
  dsimp only
  rw [partialDeriv_iterate_mul (hU a ha) (hV a ha) i m x, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **Multiindex Leibniz rule, list form.** For a duplicate-free list `L` of axes,
the iterated partial-derivative fold of a product `u·v` expands into a sum, over
multiindices `γ` bounded coordinatewise on the axes in `L`, of the products
`(∂^γ u)(∂^{α-γ} v)` weighted by the binomial coefficients `∏ₖ C(αₖ, γₖ)`. -/
private lemma foldr_partial_mul_aux {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (α : Fin n → ℕ) :
    ∀ (L : List (Fin n)), L.Nodup →
      L.foldr (fun k g => (partialDeriv k)^[α k] g) (fun y => u y * v y)
        = fun x => ∑ γ ∈ Fintype.piFinset (fun k => Finset.range (maskExp L α k + 1)),
            (L.map (fun k => ((α k).choose (γ k) : ℝ))).prod *
              (L.foldr (fun k g => (partialDeriv k)^[γ k] g) u) x *
              (L.foldr (fun k g => (partialDeriv k)^[α k - γ k] g) v) x := by
  intro L
  induction L with
  | nil =>
    intro _
    funext x
    simp [maskExp]
  | cons i l ih =>
    intro hL
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hL
    rw [List.foldr_cons, ih hl,
      partialDeriv_iterate_sum_mul i (α i)
        (Fintype.piFinset (fun k => Finset.range (maskExp l α k + 1)))
        (fun γ₀ => (l.map (fun k => ((α k).choose (γ₀ k) : ℝ))).prod)
        (fun γ₀ => l.foldr (fun k g => (partialDeriv k)^[γ₀ k] g) u)
        (fun γ₀ => l.foldr (fun k g => (partialDeriv k)^[α k - γ₀ k] g) v)
        (fun γ₀ _ => contDiff_foldr γ₀ l hu)
        (fun γ₀ _ => contDiff_foldr (fun k => α k - γ₀ k) l hv)]
    funext x
    rw [sum_piFinset_update_cons i l hi α
      (fun γ => (((i :: l).map (fun k => ((α k).choose (γ k) : ℝ))).prod) *
        ((i :: l).foldr (fun k g => (partialDeriv k)^[γ k] g) u) x *
        ((i :: l).foldr (fun k g => (partialDeriv k)^[α k - γ k] g) v) x)]
    refine Finset.sum_congr rfl fun γ₀ _ => Finset.sum_congr rfl fun j _ => ?_
    have hagree : ∀ k ∈ l, Function.update γ₀ i j k = γ₀ k := by
      intro k hk
      rw [Function.update_apply, if_neg (by rintro rfl; exact hi hk)]
    have hmapc : l.map (fun k => ((α k).choose (Function.update γ₀ i j k) : ℝ))
        = l.map (fun k => ((α k).choose (γ₀ k) : ℝ)) :=
      List.map_congr_left (fun k hk => by rw [hagree k hk])
    have hc : ((i :: l).map (fun k => ((α k).choose (Function.update γ₀ i j k) : ℝ))).prod
        = ((α i).choose j : ℝ) * (l.map (fun k => ((α k).choose (γ₀ k) : ℝ))).prod := by
      rw [List.map_cons, List.prod_cons, Function.update_apply, if_pos rfl, hmapc]
    have hU : (i :: l).foldr (fun k g => (partialDeriv k)^[Function.update γ₀ i j k] g) u
        = (partialDeriv i)^[j] (l.foldr (fun k g => (partialDeriv k)^[γ₀ k] g) u) := by
      rw [List.foldr_cons, Function.update_apply, if_pos rfl,
        foldr_partial_congr l (Function.update γ₀ i j) γ₀ hagree u]
    have hV : (i :: l).foldr (fun k g => (partialDeriv k)^[α k - Function.update γ₀ i j k] g) v
        = (partialDeriv i)^[α i - j] (l.foldr (fun k g => (partialDeriv k)^[α k - γ₀ k] g) v) := by
      rw [List.foldr_cons, Function.update_apply, if_pos rfl,
        foldr_partial_congr l (fun k => α k - Function.update γ₀ i j k) (fun k => α k - γ₀ k)
          (fun k hk => by dsimp only; rw [hagree k hk]) v]
    rw [hc, hU, hV]
    ring

/-! ## Incrementing a multiindex by one axis (`∂ᵢ Dᵅ = D^{α+eᵢ}`)

The Taylor formula (Exercise 4) expands the directional derivative `Dᵥ = ∑ᵢ vᵢ∂ᵢ`
iterated `j` times. Each iteration applies one more coordinate partial `∂ᵢ` to a
`Dᵅ`, raising the exponent of axis `i` by one. `multiPartial_add_single` records
this: for smooth `f`, `∂ᵢ(Dᵅf) = D^{α+eᵢ}f`, where `eᵢ = Pi.single i 1`. -/

/-- Folding with exponents `α + eᵢ` over `f` (with `i` in the axis list `L`) equals
folding with exponents `α` over `∂ᵢf`: the extra `∂ᵢ` moves to the innermost
position. -/
private lemma foldr_partial_add_single (i : Fin n) (α : Fin n → ℕ) :
    ∀ (L : List (Fin n)), L.Nodup → i ∈ L →
      ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, ContDiff ℝ ∞ f →
        L.foldr (fun k g => (partialDeriv k)^[(α + (Pi.single i 1 : Fin n → ℕ)) k] g) f
          = L.foldr (fun k g => (partialDeriv k)^[α k] g) (partialDeriv i f) := by
  intro L
  induction L with
  | nil => intro _ hi; exact absurd hi (List.not_mem_nil)
  | cons j l ih =>
    intro hL hi f hf
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hL
    simp only [List.foldr_cons]
    by_cases hji : j = i
    · subst hji
      have hjl : j ∉ l := hj
      have hcong : l.foldr (fun k g => (partialDeriv k)^[(α + (Pi.single j 1 : Fin n → ℕ)) k] g) f
          = l.foldr (fun k g => (partialDeriv k)^[α k] g) f :=
        foldr_partial_congr l _ _
          (fun k hk => by
            have hkj : k ≠ j := fun h => hjl (h ▸ hk)
            simp [Pi.single_eq_of_ne hkj]) f
      have hcomm : l.foldr (fun k g => (partialDeriv k)^[α k] g) (partialDeriv j f)
          = partialDeriv j (l.foldr (fun k g => (partialDeriv k)^[α k] g) f) :=
        (partialDeriv_foldr_comm j α l hf).symm
      have hji1 : (α + (Pi.single j 1 : Fin n → ℕ)) j = α j + 1 := by
        simp [Pi.single_eq_same]
      rw [hji1, hcong, hcomm]
      exact Function.iterate_succ_apply _ _ _
    · have hil : i ∈ l := by cases hi with
        | head => exact absurd rfl hji
        | tail _ h => exact h
      have hαj : (α + (Pi.single i 1 : Fin n → ℕ)) j = α j := by
        simp [Pi.add_apply, Pi.single_eq_of_ne hji]
      rw [hαj, ih hl hil hf]

/-- **Incrementing a multiindex.** For smooth `f`, one more `i`-th partial applied
to `Dᵅf` raises the `i`-th exponent by one: `∂ᵢ(Dᵅf) = D^{α+eᵢ}f`, where
`eᵢ = Pi.single i 1`. -/
theorem multiPartial_add_single {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (α : Fin n → ℕ) :
    multiPartial (α + (Pi.single i 1 : Fin n → ℕ)) f = partialDeriv i (multiPartial α f) := by
  rw [partialDeriv_multiPartial_comm hf i α]
  exact foldr_partial_add_single i α (List.finRange n) (List.nodup_finRange n)
    (List.mem_finRange i) hf

/-- **Multiindex Leibniz rule** (Evans, *Partial Differential Equations*, Ch. 1,
Exercise 3). For smooth `u, v : ℝⁿ → ℝ` and a multiindex `α`,
`Dᵅ(uv) = ∑_{β ≤ α} \binom{α}{β} Dᵝu · D^{α-β}v`, where the sum ranges over all
multiindices `β` with `βₖ ≤ αₖ` for every coordinate `k` (encoded as
`β ∈ piFinset (range (αₖ+1))`), and `\binom{α}{β} = ∏ₖ \binom{αₖ}{βₖ}`. -/
theorem multiPartial_mul {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (α : Fin n → ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    multiPartial α (fun y => u y * v y) x
      = ∑ β ∈ Fintype.piFinset (fun k => Finset.range (α k + 1)),
          (∏ k, ((α k).choose (β k) : ℝ)) *
            multiPartial β u x * multiPartial (fun k => α k - β k) v x := by
  have h := congrFun (foldr_partial_mul_aux hu hv α (List.finRange n) (List.nodup_finRange n)) x
  rw [maskExp_finRange] at h
  simp only [multiPartial]
  rw [h]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← List.ofFn_eq_map, List.prod_ofFn]

end EvansLib
