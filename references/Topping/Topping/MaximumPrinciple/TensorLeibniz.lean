import Topping.MaximumPrinciple.CurvatureNorm
import Topping.MaximumPrinciple.TensorNormAlgebra
import Topping.Riemannian.CurvatureMultilinear
import Topping.Riemannian.SmoothTensor

/-!
# The Leibniz rule for the metric contraction of tensor fields

The Bochner-type identity `Δ|A|^2 = 2|∇A|^2 + 2⟨A,ΔA⟩` that Topping's
Proposition 3.2.10 needs rests on one identity applied twice:

`X⟨A,B⟩ = ⟨∇_XA,B⟩ + ⟨A,∇_XB⟩`.

This module proves it. The obstruction three previous sessions recorded (inbox
I-0494) was that `tensorInnerAt` and `normSqAt` are *defined* by contracting
against `stdOrthonormalBasis`, a per-point choice carrying no regularity, so the
left-hand side could not be differentiated at all. TOP.CH02's
`normSqAt_eq_sum_of_frame` removed that: the contraction may be computed in any
orthonormal basis, in particular in a *smooth* local frame.

Two steps, and the second is where the mathematics is.

* **Polarization** (`tensorInnerAt_eq_polarization`) reduces the pairing to three
  square norms, so frame independence for `normSqAt` gives it for
  `tensorInnerAt` with no new invariance argument.
* **The cross terms cancel by antisymmetry.** Differentiating the frame
  expansion `⟨A,B⟩ = Σ_v A(F_v)B(F_v)` termwise gives `X⟨A,B⟩`, and the Leibniz
  corrections in `∇_XA` and `∇_XB` contribute
  `Σ_i Σ_{j,m} ω_{jm}(T^i_{mj} + T^i_{jm})`, where `ω_{jm} = ⟨∇_XF_j,F_m⟩` and
  `T^i_{ab}` pairs `A` with `F_a` in slot `i` against `B` with `F_b` there.
  Metric compatibility makes `ω` antisymmetric (`⟨F_j,F_m⟩` is constant near
  `p`), the bracket is symmetric, so the whole correction vanishes.

The frame is *not* assumed normal at `p`. A normal frame would make each `ω`
vanish individually and is the textbook route; antisymmetry from metric
compatibility is weaker and suffices, so that is what is used here.

Two pointers, because this is not the first proof of this fact in the workspace
(inbox I-0511). `PetersenLib.exercise2_5_19` does construct a normal frame, and
`PetersenLib.tensorFieldMetricInner_leibniz_orthonormal` proves this same Leibniz
rule by the same involution. Neither is importable here — Topping's lakefile
requires only `DoCarmoLib` and `MorganTianLib` — and both are stated in Petersen's
`TensorOperator` vocabulary rather than `CovTensorField`, so this module is a
re-proof in the local vocabulary, not new mathematics. Read the Petersen file
before attempting the second differentiation; it is a worked template.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Polarization -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The pairing is the polarization of the square norm:
`2⟨A,B⟩ = |A+B|^2 - |A|^2 - |B|^2`. Both sides are sums over the same index set
of basis multi-indices, so this is the scalar identity `2ab = (a+b)²-a²-b²`
summed. It is what transports frame independence from `normSqAt` to
`tensorInnerAt` without a second invariance argument. -/
theorem two_mul_tensorInnerAt (g : RiemannianMetric I M) {k : ℕ}
    (A B : CovTensorField I M k) (p : M) :
    2 * tensorInnerAt g A B p =
      normSqAt g (fun Y q => A Y q + B Y q) p - normSqAt g A p - normSqAt g B p := by
  simp only [tensorInnerAt, normSqAt, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### Frame independence of the pairing -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Pointwise multilinearity is preserved by pointwise addition: both
`add` and `smul` are proved slotwise from the two summands', and tensoriality is
immediate. This is what lets polarization consume the frame theorem, whose
hypothesis is about `A + B` as well as about `A` and `B`. -/
theorem IsPointwiseMultilinear.add_field {k : ℕ}
    {A B : CovTensorField I M k} {p : M}
    (hA : IsPointwiseMultilinear A p) (hB : IsPointwiseMultilinear B p) :
    IsPointwiseMultilinear (fun Y q => A Y q + B Y q) p where
  tensorial := fun Y Z h => by
    show A Y p + B Y p = A Z p + B Z p
    rw [hA.tensorial Y Z h, hB.tensorial Y Z h]
  add := fun i v x y => by
    show pointwiseValue A p _ + pointwiseValue B p _ = _
    have h := hA.add i v x y
    have h' := hB.add i v x y
    show A _ p + B _ p = (A _ p + B _ p) + (A _ p + B _ p)
    simp only [pointwiseValue] at h h'
    rw [h, h']
    ring
  smul := fun i v c x => by
    have h := hA.smul i v c x
    have h' := hB.smul i v c x
    show A _ p + B _ p = c * (A _ p + B _ p)
    simp only [pointwiseValue] at h h'
    rw [h, h']
    ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** **The pairing does not depend on the orthonormal basis computing
it.** For pointwise multilinear `A` and `B` and any orthonormal basis `e` of
`T_pM`,
`⟨A,B⟩(p) = Σ_{i₁…i_k} A(e_{i₁},…)(p) · B(e_{i₁},…)(p)`.

Polarization plus `normSqAt_eq_sum_of_frame` on the three square norms; the
scalar identity `2ab = (a+b)²-a²-b²` runs backwards on the frame side. -/
theorem tensorInnerAt_eq_sum_of_frame (g : RiemannianMetric I M) {k : ℕ}
    {A B : CovTensorField I M k} {p : M}
    (hA : IsPointwiseMultilinear A p) (hB : IsPointwiseMultilinear B p)
    {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    tensorInnerAt g A B p
      = ∑ v : Fin k → ι,
          pointwiseValue A p (fun j => e (v j))
            * pointwiseValue B p (fun j => e (v j)) := by
  have h2 := two_mul_tensorInnerAt g A B p
  rw [normSqAt_eq_sum_of_frame g (hA.add_field hB) e,
    normSqAt_eq_sum_of_frame g hA e, normSqAt_eq_sum_of_frame g hB e] at h2
  have hpw : ∀ v : Fin k → ι,
      pointwiseValue (fun Y q => A Y q + B Y q) p (fun j => e (v j))
        = pointwiseValue A p (fun j => e (v j))
          + pointwiseValue B p (fun j => e (v j)) := fun v => rfl
  rw [Finset.sum_congr rfl (fun v _ => by rw [hpw v]),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib] at h2
  have hterm : ∑ v : Fin k → ι,
        ((pointwiseValue A p (fun j => e (v j))
              + pointwiseValue B p (fun j => e (v j))) ^ 2
            - pointwiseValue A p (fun j => e (v j)) ^ 2
            - pointwiseValue B p (fun j => e (v j)) ^ 2)
      = 2 * ∑ v : Fin k → ι,
          pointwiseValue A p (fun j => e (v j))
            * pointwiseValue B p (fun j => e (v j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hterm] at h2
  linarith

/-! ### The cancellation of the cross terms

This is the arithmetic the Leibniz rule turns on, isolated from the manifold. The
Leibniz corrections of `∇_XA` and `∇_XB` together contribute

`Σ_{j,m} ω_{jm} · (A_m B_j + A_j B_m)`,

with `ω_{jm} = ⟨∇_XF_j, F_m⟩`. The bracket is symmetric in `(j,m)` by
construction — it is the pairing of `A` and `B` with the two frame vectors
swapped and added — and `ω` is antisymmetric because the frame is orthonormal on
a neighbourhood. So the sum is its own negative. -/

/-- **Math.** **The cross terms cancel.** With `ω` antisymmetric, the total
Leibniz correction at slot `i`,

`Σ_v Σ_m ω_{v_i m} (a_{v[i→m]} b_v + a_v b_{v[i→m]})`,

vanishes for arbitrary component functions `a`, `b`.

The proof is an involution on the summation index: `(v,m) ↦ (v[i→m], v_i)` is its
own inverse, and it sends each summand to its negative — the bracket is symmetric
under it, `ω` flips sign. So the sum equals minus itself. Stated over abstract
`a`, `b` so that no property of the tensor fields is used beyond the antisymmetry
of `ω`; the geometry enters only through `hom`. -/
theorem sum_slot_swap_cancel {n k : ℕ} (i : Fin k) {om : Fin n → Fin n → ℝ}
    (hom : ∀ j m, om j m = -om m j) (a b : (Fin k → Fin n) → ℝ) :
    ∑ v : Fin k → Fin n, ∑ m : Fin n,
        om (v i) m * (a (Function.update v i m) * b v
          + a v * b (Function.update v i m)) = 0 := by
  classical
  set f : ((Fin k → Fin n) × Fin n) → ℝ := fun x =>
    om (x.1 i) x.2 * (a (Function.update x.1 i x.2) * b x.1
      + a x.1 * b (Function.update x.1 i x.2)) with hf
  -- the slot swap is an involution of the index set
  have hinv : Function.Involutive
      (fun x : (Fin k → Fin n) × Fin n => (Function.update x.1 i x.2, x.1 i)) := by
    intro x
    refine Prod.ext ?_ ?_
    · show Function.update (Function.update x.1 i x.2) i (x.1 i) = x.1
      rw [Function.update_idem, Function.update_eq_self]
    · show Function.update x.1 i x.2 i = x.2
      simp
  set e := hinv.toPerm _ with he
  -- each summand is sent to its negative
  have hneg : ∀ x, f (e x) = -f x := by
    intro x
    show om (Function.update x.1 i x.2 i) (x.1 i) *
        (a (Function.update (Function.update x.1 i x.2) i (x.1 i))
            * b (Function.update x.1 i x.2)
          + a (Function.update x.1 i x.2)
            * b (Function.update (Function.update x.1 i x.2) i (x.1 i)))
      = -f x
    rw [Function.update_idem, Function.update_eq_self, Function.update_self,
      hom x.2 (x.1 i), hf]
    ring
  have hsum : ∑ x, f (e x) = ∑ x, f x := Equiv.sum_comp e f
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hneg x),
    Finset.sum_neg_distrib] at hsum
  have hzero : ∑ x, f x = 0 := by linarith
  rw [← hzero, Fintype.sum_prod_type]

/-! ### Antisymmetry of the frame's connection coefficients -/

/-- **Math.** **The connection coefficients of an orthonormal frame are
antisymmetric.** If `F` is `g`-orthonormal on a neighbourhood of `p`, then
`⟨∇_XF_j, F_m⟩(p) = -⟨∇_XF_m, F_j⟩(p)`.

Metric compatibility gives
`X⟨F_j,F_m⟩ = ⟨∇_XF_j,F_m⟩ + ⟨F_j,∇_XF_m⟩`, and the left-hand side vanishes
because `⟨F_j,F_m⟩` is *locally constant* (`δ_{jm}` on the neighbourhood), so its
directional derivative at `p` is zero. This is the only place the orthonormality
of the frame is spent, and it is a weaker input than the normal frame the textbook
proof uses. -/
theorem metricInner_cov_frame_antisymm (g : RiemannianMetric I M)
    {n : ℕ} {F : Fin n → SmoothVectorField I M} {p : M}
    (hF : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0)
    (X : SmoothVectorField I M) (j m : Fin n) :
    g.metricInner p ((g.leviCivitaConnection.cov X (F j)) p) (F m p)
      = -g.metricInner p ((g.leviCivitaConnection.cov X (F m)) p) (F j p) := by
  have hcompat := (isLeviCivita_leviCivitaConnection g).2 X (F j) (F m) p
  -- the pairing is locally constant, so its directional derivative vanishes
  have hconst : X.dir (fun q => g.metricInner q (F j q) (F m q)) p = 0 :=
    MorganTianLib.dir_eventuallyEq_const X (hF j m)
  rw [hconst] at hcompat
  have hsymm : g.metricInner p (F j p) ((g.leviCivitaConnection.cov X (F m)) p)
      = g.metricInner p ((g.leviCivitaConnection.cov X (F m)) p) (F j p) :=
    g.metricInner_comm p _ _
  rw [hsymm] at hcompat
  linarith

/-! ### The Leibniz rule for the pairing, in frame components

With the two cores in place the rule is bookkeeping over the frame. Write
`A_v = A(F_{v_1},…,F_{v_k})` for the component functions of `A`. On the
neighbourhood where `F` is orthonormal, `⟨A,B⟩ = Σ_v A_v B_v`, so

`X⟨A,B⟩ = Σ_v (X(A_v) B_v + A_v X(B_v))`

by the product rule. Meanwhile `(∇_XA)(F_v) = X(A_v) - Σ_i A(…∇_XF_{v_i}…)`, and
the corrections are what `sum_antisymm_mul_symm_eq_zero` kills after expanding
`∇_XF_j` in the frame. The statement below is the *component* form, which is what
the Bochner assembly consumes; it is stated at a single slot count `k` and needs no
induction. -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **The product rule for the frame components of the pairing.** If
each component function `A_v`, `B_v` is differentiable at `p`, then
`X(Σ_v A_v B_v) = Σ_v (X(A_v)B_v + A_v X(B_v))` at `p`.

Pure calculus — the finite sum rule plus the product rule — but it is the step
that was impossible before the frame expansion existed: `⟨A,B⟩` as originally
defined is a contraction against a per-point basis, not a finite sum of
differentiable functions. -/
theorem dir_sum_mul_components {n k : ℕ} (F : Fin n → SmoothVectorField I M)
    {A B : CovTensorField I M k} (X : SmoothVectorField I M) (p : M)
    (hA : ∀ v : Fin k → Fin n,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (A (fun j => F (v j))))
    (hB : ∀ v : Fin k → Fin n,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (B (fun j => F (v j)))) :
    X.dir (fun q => ∑ v : Fin k → Fin n,
        A (fun j => F (v j)) q * B (fun j => F (v j)) q) p
      = ∑ v : Fin k → Fin n,
          (X.dir (A (fun j => F (v j))) p * B (fun j => F (v j)) p
            + A (fun j => F (v j)) p * X.dir (B (fun j => F (v j))) p) := by
  classical
  rw [MorganTianLib.dir_sum X
    (h := fun v : Fin k → Fin n =>
      fun q => A (fun j => F (v j)) q * B (fun j => F (v j)) q)
    (fun v _ => (hA v).mul (hB v)) p]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [X.dir_mul p ((hA v).mdifferentiableAt (by norm_num))
    ((hB v).mdifferentiableAt (by norm_num))]
  ring

/-! ### The Leibniz rule, in frame components

Everything is now in place. Fix a frame `F` orthonormal near `p` and write
`A_v = A(F_{v_1},…,F_{v_k})`. Then

* `X⟨A,B⟩ = Σ_v (X(A_v)B_v + A_v X(B_v))` — the product rule
  (`dir_sum_mul_components`), available because the pairing is a finite sum of
  smooth functions over the frame (`tensorInnerAt_eq_sum_of_frame`);
* `(∇_XA)_v = X(A_v) - Σ_i Σ_m ω_{v_i m} A_{v[i→m]}` — the Leibniz correction
  with its slot argument expanded (`pointwiseValue_expand_slot`);
* the corrections cancel in pairs (`sum_slot_swap_cancel`), because
  `ω` is antisymmetric (`metricInner_cov_frame_antisymm`).

The statement below packages exactly this: the *sum* of the two covariant
derivatives' frame pairings equals `X⟨A,B⟩`, which is the Leibniz rule with both
sides expressed in the frame. Deriving the basis-free form
`X⟨A,B⟩ = ⟨∇_XA,B⟩ + ⟨A,∇_XB⟩` from it additionally needs `∇_XA` to be pointwise
multilinear at `p` — true, and provable, but a separate obligation recorded on the
node rather than assumed here. -/

/-- **Math.** **The Leibniz rule for the metric pairing, in frame components.**
For a frame `F` that is `g`-orthonormal near `p`, and component functions of `A`
and `B` that are smooth,

`X(Σ_v A_v B_v) = Σ_v ((∇_XA)_v B_v + A_v (∇_XB)_v)`,

where `(∇_XA)_v` is written out as `X(A_v) - Σ_i A(…∇_XF_{v_i}…)`.

The two Leibniz corrections cancel: expanding each `∇_XF_{v_i}` over the frame
turns them into the antisymmetric-times-symmetric sum that
`sum_slot_swap_cancel` kills. -/
theorem dir_tensorInner_frame_leibniz (g : RiemannianMetric I M) {k : ℕ}
    {A B : CovTensorField I M k} {p : M}
    (hAm : IsPointwiseMultilinear A p)
    (hBm : IsPointwiseMultilinear B p)
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hF : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0)
    (X : SmoothVectorField I M)
    (hA : ∀ v : Fin k → Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (A (fun j => F (v j))))
    (hB : ∀ v : Fin k → Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (B (fun j => F (v j)))) :
    X.dir (fun q => ∑ v : Fin k → Fin (Module.finrank ℝ E),
        A (fun j => F (v j)) q * B (fun j => F (v j)) q) p
      = ∑ v : Fin k → Fin (Module.finrank ℝ E),
          (covDerivAlong g.leviCivitaConnection X A (fun j => F (v j)) p
              * B (fun j => F (v j)) p
            + A (fun j => F (v j)) p
              * covDerivAlong g.leviCivitaConnection X B (fun j => F (v j)) p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  -- the frame is orthonormal at `p` itself, hence a basis of `T_pM`
  have hp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0 :=
    fun i j => (hF i j).self_of_nhds
  set e := MorganTianLib.frameOrthonormalBasis (I := I) g hp with he
  have hev : ∀ m, e m = F m p := fun m =>
    MorganTianLib.frameOrthonormalBasis_apply (I := I) g hp m
  set a : (Fin k → Fin (Module.finrank ℝ E)) → ℝ :=
    fun v => A (fun j => F (v j)) p with ha
  set b : (Fin k → Fin (Module.finrank ℝ E)) → ℝ :=
    fun v => B (fun j => F (v j)) p with hb
  set om : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun j m => g.metricInner p (e m) ((g.leviCivitaConnection.cov X (F j)) p) with hom
  -- `ω` is antisymmetric: this is the geometric input
  have homanti : ∀ j m, om j m = -om m j := by
    intro j m
    have h := metricInner_cov_frame_antisymm g hF X j m
    rw [hom]
    simp only []
    rw [hev m, hev j, g.metricInner_comm p (F m p) _,
      g.metricInner_comm p (F j p) _, h]
  -- the Leibniz correction, with its slot argument expanded over the frame
  have hcorr : ∀ (C : CovTensorField I M k) (c : (Fin k → Fin (Module.finrank ℝ E)) → ℝ),
      IsPointwiseMultilinear C p →
      (c = fun v => C (fun j => F (v j)) p) →
      ∀ v, covDerivAlong g.leviCivitaConnection X C (fun j => F (v j)) p
        = X.dir (C (fun j => F (v j))) p
          - ∑ i, ∑ m, om (v i) m * c (Function.update v i m) := by
    intro C c hCm hc v
    rw [covDerivAlong_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    -- evaluate on fields via the pointwise value, then expand slot `i`
    have hval : C (Function.update (fun j => F (v j)) i
          (g.leviCivitaConnection.cov X (F (v i)))) p
        = pointwiseValue C p (Function.update (fun j => F (v j) p) i
            ((g.leviCivitaConnection.cov X (F (v i))) p)) := by
      have h := pointwiseValue_eq hCm.tensorial
        (Function.update (fun j => F (v j)) i
          (g.leviCivitaConnection.cov X (F (v i))))
      rw [← h]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [hval, pointwiseValue_expand_slot g hCm i _ _ e]
    refine Finset.sum_congr rfl fun m _ => ?_
    -- the coefficient is `ω`, and the expanded value is `c` at the updated index
    have hcval : pointwiseValue C p (Function.update (fun j => F (v j) p) i (e m))
        = c (Function.update v i m) := by
      have h := pointwiseValue_eq hCm.tensorial
        (fun j => F (Function.update v i m j))
      have harg : Function.update (fun j => F (v j) p) i (e m)
          = fun j => F (Function.update v i m j) p := by
        funext j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self, Function.update_self, hev m]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      rw [hc, harg, h]
    rw [hcval, hom]
  -- the product rule on the frame components
  rw [dir_sum_mul_components F X p hA hB]
  -- substitute both Leibniz corrections on the right-hand side
  have hsubst : ∑ v : Fin k → Fin (Module.finrank ℝ E),
        (covDerivAlong g.leviCivitaConnection X A (fun j => F (v j)) p
            * B (fun j => F (v j)) p
          + A (fun j => F (v j)) p
            * covDerivAlong g.leviCivitaConnection X B (fun j => F (v j)) p)
      = ∑ v : Fin k → Fin (Module.finrank ℝ E),
          ((X.dir (A (fun j => F (v j))) p
                - ∑ i, ∑ m, om (v i) m * a (Function.update v i m))
              * B (fun j => F (v j)) p
            + A (fun j => F (v j)) p
              * (X.dir (B (fun j => F (v j))) p
                - ∑ i, ∑ m, om (v i) m * b (Function.update v i m))) :=
    Finset.sum_congr rfl fun v _ => by
      rw [hcorr A a hAm ha v, hcorr B b hBm hb v]
  rw [hsubst]
  -- what is left is the sum of the cross terms, which cancels
  have hcancel : ∀ i : Fin k, ∑ v : Fin k → Fin (Module.finrank ℝ E), ∑ m,
      om (v i) m * (a (Function.update v i m) * b v
        + a v * b (Function.update v i m)) = 0 :=
    fun i => sum_slot_swap_cancel i homanti a b
  have hexpand : ∑ v : Fin k → Fin (Module.finrank ℝ E),
        ((X.dir (A (fun j => F (v j))) p
              - ∑ i, ∑ m, om (v i) m * a (Function.update v i m))
            * B (fun j => F (v j)) p
          + A (fun j => F (v j)) p
            * (X.dir (B (fun j => F (v j))) p
              - ∑ i, ∑ m, om (v i) m * b (Function.update v i m)))
      = ∑ v : Fin k → Fin (Module.finrank ℝ E),
          (X.dir (A (fun j => F (v j))) p * B (fun j => F (v j)) p
            + A (fun j => F (v j)) p * X.dir (B (fun j => F (v j))) p)
        - ∑ i : Fin k, ∑ v : Fin k → Fin (Module.finrank ℝ E), ∑ m,
            om (v i) m * (a (Function.update v i m) * b v
              + a v * b (Function.update v i m)) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin k))), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    -- per `v`: distribute, then match the two correction groups term by term
    have hgroup : (∑ i : Fin k, ∑ m, om (v i) m * a (Function.update v i m)) * b v
          + a v * ∑ i : Fin k, ∑ m, om (v i) m * b (Function.update v i m)
        = ∑ i : Fin k, ∑ m, om (v i) m * (a (Function.update v i m) * b v
            + a v * b (Function.update v i m)) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hav : A (fun j => F (v j)) p = a v := by rw [ha]
    have hbv : B (fun j => F (v j)) p = b v := by rw [hb]
    rw [hav, hbv, sub_mul, mul_sub, ← hgroup]
    ring
  rw [hexpand, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hcancel i)]
  simp

/-! ### The basis-free form

`dir_tensorInner_frame_leibniz` is the rule in frame components. Turning both sides
back into `tensorInnerAt` needs `tensorInnerAt_eq_sum_of_frame` three times — once
for `⟨A,B⟩` and once for each of `⟨∇_XA,B⟩`, `⟨A,∇_XB⟩` — and the latter two
require `∇_XA` and `∇_XB` to be **pointwise multilinear at `p`**.

The general statement below carries those two facts explicitly. For the curvature
tensor, `CurvatureMultilinear.lean` now supplies both the first and iterated
covariant-derivative witnesses, so the specialized consequences later in this file
are unconditional. -/

/-- **Math.** **The Leibniz rule for the metric pairing, basis-free:**
`X⟨A,B⟩ = ⟨∇_XA,B⟩ + ⟨A,∇_XB⟩` at `p`.

The frame-component form is `dir_tensorInner_frame_leibniz`; this converts both
sides using `tensorInnerAt_eq_sum_of_frame`. The two hypotheses `hdA`, `hdB` —
pointwise multilinearity of the covariant derivatives — are the price of that
conversion in this general lemma. Everything else is proved, including the
cancellation of the cross terms and `hpair`, which
`eventually_tensorInnerAt_eq_frame_sum` below discharges. -/
theorem dir_tensorInnerAt_leibniz (g : RiemannianMetric I M) {k : ℕ}
    {A B : CovTensorField I M k} {p : M} (X : SmoothVectorField I M)
    (hAm : IsPointwiseMultilinear A p)
    (hBm : IsPointwiseMultilinear B p)
    (hdA : IsPointwiseMultilinear (covDerivAlong g.leviCivitaConnection X A) p)
    (hdB : IsPointwiseMultilinear (covDerivAlong g.leviCivitaConnection X B) p)
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hF : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0)
    (hA : ∀ v : Fin k → Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (A (fun j => F (v j))))
    (hB : ∀ v : Fin k → Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (B (fun j => F (v j))))
    (hpair : ∀ᶠ q in 𝓝 p, tensorInnerAt g A B q
      = ∑ v : Fin k → Fin (Module.finrank ℝ E),
          A (fun j => F (v j)) q * B (fun j => F (v j)) q) :
    X.dir (fun q => tensorInnerAt g A B q) p
      = tensorInnerAt g (covDerivAlong g.leviCivitaConnection X A) B p
        + tensorInnerAt g A (covDerivAlong g.leviCivitaConnection X B) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hp : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0 :=
    fun i j => (hF i j).self_of_nhds
  set e := MorganTianLib.frameOrthonormalBasis (I := I) g hp with he
  have hev : ∀ m, (e m : TangentSpace I p) = F m p := fun m =>
    MorganTianLib.frameOrthonormalBasis_apply (I := I) g hp m
  -- the frame value of a tensor field is its pointwise value at the frame basis
  have hframe : ∀ (C : CovTensorField I M k), IsPointwiseTensorial C p →
      ∀ v : Fin k → Fin (Module.finrank ℝ E),
        pointwiseValue C p (fun j => e (v j)) = C (fun j => F (v j)) p := by
    intro C hC v
    have h := pointwiseValue_eq hC (fun j => F (v j))
    rw [← h]
    congr 1
    funext j
    rw [hev (v j)]
  -- the left-hand side is the frame sum, eventually, so its derivative is that sum's
  rw [MorganTianLib.dir_congr_nhds X hpair, dir_tensorInner_frame_leibniz g hAm hBm hF X hA hB]
  -- and the two right-hand pairings are frame sums at `p`
  rw [tensorInnerAt_eq_sum_of_frame g hdA hBm e,
    tensorInnerAt_eq_sum_of_frame g hAm hdB e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hframe _ hAm.tensorial v, hframe _ hBm.tensorial v,
    hframe _ hdA.tensorial v, hframe _ hdB.tensorial v]

/-! ### Discharging `hpair`

`dir_tensorInnerAt_leibniz` takes `hpair`: that `⟨A,B⟩` agrees with the frame sum
on a *neighbourhood* of `p`, not merely at `p`. That is a second antecedent, and
TOP.CH02's `exists_smooth_frame_normSqAt` does not supply it — that theorem is
about `normSqAt`, one field, and the eventual equality it produces is guarded by
`IsPointwiseMultilinear A q` at each nearby `q`.

It is dischargeable, and here it is discharged: run the same eventual argument
through `tensorInnerAt_eq_sum_of_frame` instead of the polarization. The frame is
orthonormal on a neighbourhood, so at each `q` there the frame *is* an orthonormal
basis and the pairing equals its frame sum. So `hpair` is not an open obligation —
it is a lemma, below. -/

omit [CompleteSpace E] in
/-- **Math.** **The pairing agrees with its frame sum near `p`.** Given a frame
orthonormal on a neighbourhood of `p` and fields pointwise multilinear at every
point, `⟨A,B⟩(q) = Σ_v A(F_v)(q)·B(F_v)(q)` for all `q` near `p`.

This is `tensorInnerAt_eq_sum_of_frame` applied at each nearby point, with the
frame's own orthonormality supplying the basis there. It is what discharges the
`hpair` hypothesis of `dir_tensorInnerAt_leibniz`, so that hypothesis is a
convenience rather than a gap. -/
theorem eventually_tensorInnerAt_eq_frame_sum (g : RiemannianMetric I M) {k : ℕ}
    {A B : CovTensorField I M k} {p : M}
    (hAm : ∀ q : M, IsPointwiseMultilinear A q)
    (hBm : ∀ q : M, IsPointwiseMultilinear B q)
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hF : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0) :
    ∀ᶠ q in 𝓝 p, tensorInnerAt g A B q
      = ∑ v : Fin k → Fin (Module.finrank ℝ E),
          A (fun j => F (v j)) q * B (fun j => F (v j)) q := by
  classical
  -- intersect the finitely many orthonormality neighbourhoods
  have hall : ∀ᶠ q in 𝓝 p, ∀ i j,
      g.metricInner q (F i q) (F j q) = if i = j then 1 else 0 :=
    (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun i =>
      (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun j => hF i j
  filter_upwards [hall] with q hq
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [tensorInnerAt_eq_sum_of_frame g (hAm q) (hBm q)
    (MorganTianLib.frameOrthonormalBasis (I := I) g hq)]
  refine Finset.sum_congr rfl fun v _ => ?_
  -- at `q` the frame vectors are the basis vectors, so the components agree
  have hframe : ∀ (C : CovTensorField I M k), IsPointwiseTensorial C q →
      pointwiseValue C q (fun j =>
          MorganTianLib.frameOrthonormalBasis (I := I) g hq (v j))
        = C (fun j => F (v j)) q := by
    intro C hC
    have h := pointwiseValue_eq hC (fun j => F (v j))
    rw [← h]
    congr 1
    funext j
    exact MorganTianLib.frameOrthonormalBasis_apply (I := I) g hq (v j)
  rw [hframe _ (hAm q).tensorial, hframe _ (hBm q).tensorial]

/-- **Math.** The metric contraction of two smooth covariant tensor fields is a
smooth scalar function.  A smooth local orthonormal frame turns the contraction
near each point into a finite sum of products of smooth component functions. -/
theorem tensorInnerAt_contMDiff (g : RiemannianMetric I M) {k : ℕ}
    {A B : CovTensorField I M k}
    (hAm : ∀ q : M, IsPointwiseMultilinear A q)
    (hBm : ∀ q : M, IsPointwiseMultilinear B q)
    (hA : HasSmoothComponents A) (hB : HasSmoothComponents B) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => tensorInnerAt g A B q) := by
  intro p
  obtain ⟨F, hF⟩ := MorganTianLib.exists_orthonormalFrame (I := I) g p
  have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun q => ∑ v : Fin k → Fin (Module.finrank ℝ E),
        A (fun j => F (v j)) q * B (fun j => F (v j)) q) :=
    MorganTianLib.contMDiff_fun_sum fun v _ => (hA _).mul (hB _)
  apply (hs p).congr_of_eventuallyEq
  filter_upwards [eventually_tensorInnerAt_eq_frame_sum g hAm hBm hF] with q hq
  exact hq

/-! ### The consequence Bochner consumes -/

/-- **Math.** **`X|A|^2 = 2⟨∇_XA, A⟩`.** The `A = B` case of the Leibniz rule,
with `⟨A,A⟩ = |A|^2` on the left and the two terms coinciding on the right by
symmetry of the pairing.

This is the first differentiation in the Bochner identity
`Δ|A|^2 = 2|∇A|^2 + 2⟨A,ΔA⟩`: applying it once gives the gradient of `|A|^2`, and
the second application (plus commuting the metric trace past `∇`) produces the
two terms of the identity. It inherits `dir_tensorInnerAt_leibniz`'s open
antecedent — pointwise multilinearity of `∇_XA` — and nothing else. -/
theorem dir_normSqAt_eq_two_mul_tensorInnerAt (g : RiemannianMetric I M) {k : ℕ}
    {A : CovTensorField I M k} {p : M} (X : SmoothVectorField I M)
    (hAm : ∀ q : M, IsPointwiseMultilinear A q)
    (hdA : IsPointwiseMultilinear (covDerivAlong g.leviCivitaConnection X A) p)
    {F : Fin (Module.finrank ℝ E) → SmoothVectorField I M}
    (hF : ∀ i j, ∀ᶠ q in 𝓝 p, g.metricInner q (F i q) (F j q)
      = if i = j then 1 else 0)
    (hA : ∀ v : Fin k → Fin (Module.finrank ℝ E),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (A (fun j => F (v j))))
    (hpair : ∀ᶠ q in 𝓝 p, tensorInnerAt g A A q
      = ∑ v : Fin k → Fin (Module.finrank ℝ E),
          A (fun j => F (v j)) q * A (fun j => F (v j)) q) :
    X.dir (fun q => normSqAt g A q) p
      = 2 * tensorInnerAt g (covDerivAlong g.leviCivitaConnection X A) A p := by
  have hself : (fun q => normSqAt g A q) = fun q => tensorInnerAt g A A q :=
    funext fun q => (tensorInnerAt_self g A q).symm
  rw [hself, dir_tensorInnerAt_leibniz g X (hAm p) (hAm p) hdA hdA hF hA hA hpair,
    tensorInnerAt_comm g A (covDerivAlong g.leviCivitaConnection X A) p]
  ring

/-! ### At the curvature tensor

The instance Proposition 3.2.10 needs. `\Rm` has all the general hypotheses
witnessed — `isPointwiseMultilinear_riemannTensorField` for multilinearity at every
point, `MorganTianLib.exists_orthonormalFrame` for the frame,
`curvatureForm_contMDiff` (via `HasSmoothComponents`) for the components, and the
curvature-specific covariant-derivative producer from `CurvatureMultilinear.lean`. -/

/-- **Math.** **`\Rm` has smooth components.** Evaluating the curvature `4`-tensor
field on smooth vector fields gives a smooth function: `\Rm(X,Y,Z,W)` *is* the
curvature form `⟨R(X,Y)Z, W⟩` pointwise, and that is smooth because the metric
pairing of smooth sections is (`MorganTianLib.curvatureForm_contMDiff`).

Without this the `hsm` hypothesis below would be another unwitnessed antecedent
rather than a discharged one, so it is proved rather than assumed. -/
theorem hasSmoothComponents_riemannTensorField (g : RiemannianMetric I M) :
    HasSmoothComponents (riemannTensorField g) := by
  intro Y
  have hfun : riemannTensorField g Y
      = g.leviCivitaConnection.curvatureForm g (Y 0) (Y 1) (Y 2) (Y 3) := by
    funext q
    exact riemannCurvatureAt_eq g q rfl rfl rfl rfl
  rw [hfun]
  exact MorganTianLib.curvatureForm_contMDiff g g.leviCivitaConnection
    (Y 0) (Y 1) (Y 2) (Y 3)

/-- **Math.** The squared norm of the curvature tensor of a fixed metric is
smooth in the base point. This is an unconditional producer: smooth curvature
components and pointwise multilinearity feed the smooth metric contraction. -/
theorem riemannNormAt_sq_contMDiff (g : RiemannianMetric I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => riemannNormAt g q ^ 2) := by
  have hbridge : riemannCovTensorField g = riemannTensorField g := rfl
  simpa only [riemannNormAt_sq, hbridge, tensorInnerAt_self] using
    (tensorInnerAt_contMDiff g
      (isPointwiseMultilinear_riemannTensorField g)
      (isPointwiseMultilinear_riemannTensorField g)
      (hasSmoothComponents_riemannTensorField g)
      (hasSmoothComponents_riemannTensorField g))

/-- **Math.** **`X|\Rm|^2 = 2⟨∇_X\Rm, \Rm⟩`.** The Leibniz rule at the curvature
tensor, with every tensoriality and smoothness hypothesis discharged.

`exists_orthonormalFrame` gives the frame, `eventually_tensorInnerAt_eq_frame_sum`
the frame-sum identity, `isPointwiseMultilinear_riemannTensorField` the
multilinearity of `\Rm`, `isPointwiseMultilinear_covDerivAlong_riemannTensorField`
the multilinearity of `∇_X\Rm`, and `hasSmoothComponents_riemannTensorField`
the smoothness. -/
theorem dir_riemannNormSq_eq_two_mul_tensorInnerAt (g : RiemannianMetric I M)
    (p : M) (X : SmoothVectorField I M) :
    X.dir (fun q => normSqAt g (riemannTensorField g) q) p
      = 2 * tensorInnerAt g
          (covDerivAlong g.leviCivitaConnection X (riemannTensorField g))
          (riemannTensorField g) p := by
  obtain ⟨F, hF⟩ := MorganTianLib.exists_orthonormalFrame (I := I) g p
  exact dir_normSqAt_eq_two_mul_tensorInnerAt g X
    (isPointwiseMultilinear_riemannTensorField g)
    (isPointwiseMultilinear_covDerivAlong_riemannTensorField g X p) hF
    (fun v => hasSmoothComponents_riemannTensorField g _)
    (eventually_tensorInnerAt_eq_frame_sum g
      (isPointwiseMultilinear_riemannTensorField g)
      (isPointwiseMultilinear_riemannTensorField g) hF)

/-- **Math.** The same statement in the notation Proposition 3.2.10 uses:
`X(|\Rm|^2) = 2⟨∇_X\Rm, \Rm⟩`, with the left side written through
`riemannNormAt`. `riemannCovTensorField` and `riemannTensorField` are the same
function (`riemannCovTensorField_eq_riemannTensorField`, an `rfl`), so this is a
restatement and not a second theorem — it exists so that
`CurvatureNormEvolution.lean` can consume the Leibniz rule without unfolding
`riemannNormAt` by hand. -/
theorem dir_riemannNormAt_sq (g : RiemannianMetric I M) (p : M)
    (X : SmoothVectorField I M) :
    X.dir (fun q => riemannNormAt g q ^ 2) p
      = 2 * tensorInnerAt g
          (covDerivAlong g.leviCivitaConnection X (riemannTensorField g))
          (riemannTensorField g) p := by
  have hfun : (fun q => riemannNormAt g q ^ 2)
      = fun q => normSqAt g (riemannTensorField g) q := by
    funext q
    -- `riemannCovTensorField` and `riemannTensorField` are the same function
    have hbridge : riemannCovTensorField g = riemannTensorField g := rfl
    rw [riemannNormAt, normAt_sq, hbridge]
  rw [hfun]
  exact dir_riemannNormSq_eq_two_mul_tensorInnerAt g p X

/-- **Math.** Differentiating the pairing `⟨∇_Y Rm, Rm⟩` gives the two
covariant-derivative terms.  All tensoriality and regularity antecedents are
witnessed by the curvature producers above. -/
theorem dir_covDerivAlong_riemannTensorInnerAt (g : RiemannianMetric I M)
    (p : M) (X Y : SmoothVectorField I M) :
    X.dir (fun q => tensorInnerAt g
        (covDerivAlong g.leviCivitaConnection Y (riemannTensorField g))
        (riemannTensorField g) q) p =
      tensorInnerAt g
          (covDerivAlong g.leviCivitaConnection X
            (covDerivAlong g.leviCivitaConnection Y (riemannTensorField g)))
          (riemannTensorField g) p
        + tensorInnerAt g
          (covDerivAlong g.leviCivitaConnection Y (riemannTensorField g))
          (covDerivAlong g.leviCivitaConnection X (riemannTensorField g)) p := by
  obtain ⟨F, hF⟩ := MorganTianLib.exists_orthonormalFrame (I := I) g p
  exact dir_tensorInnerAt_leibniz g X
    (isPointwiseMultilinear_covDerivAlong_riemannTensorField g Y p)
    (isPointwiseMultilinear_riemannTensorField g p)
    (isPointwiseMultilinear_covDerivAlong_covDerivAlong_riemannTensorField
      g Y X p)
    (isPointwiseMultilinear_covDerivAlong_riemannTensorField g X p) hF
    (fun _ => (hasSmoothComponents_riemannTensorField g).covDerivAlong
      g.leviCivitaConnection Y _)
    (fun _ => hasSmoothComponents_riemannTensorField g _)
    (eventually_tensorInnerAt_eq_frame_sum g
      (isPointwiseMultilinear_covDerivAlong_riemannTensorField g Y)
      (isPointwiseMultilinear_riemannTensorField g) hF)

/-- **Math.** The Hessian of `|Rm|²` in one direction is
`2|∇_X Rm|² + 2⟨∇²_{X,X}Rm,Rm⟩`.  This is the untraced Bochner
identity; tracing it produces the rough-Laplacian formula. -/
theorem hessian_riemannNormAt_sq (g : RiemannianMetric I M) (p : M)
    (X : SmoothVectorField I M) :
    MorganTianLib.hessian g.leviCivitaConnection
        (fun q => riemannNormAt g q ^ 2) X X p =
      2 * tensorInnerAt g
          (covDerivAlong g.leviCivitaConnection X (riemannTensorField g))
          (covDerivAlong g.leviCivitaConnection X (riemannTensorField g)) p
        + 2 * tensorInnerAt g
          (secondCovDerivAlong g.leviCivitaConnection X X (riemannTensorField g))
          (riemannTensorField g) p := by
  have hfirst : X.dir (fun q => riemannNormAt g q ^ 2) = fun q =>
      2 * tensorInnerAt g
        (covDerivAlong g.leviCivitaConnection X (riemannTensorField g))
        (riemannTensorField g) q := by
    funext q
    exact dir_riemannNormAt_sq g q X
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun q => tensorInnerAt g
        (covDerivAlong g.leviCivitaConnection X (riemannTensorField g))
        (riemannTensorField g) q) p :=
    ((tensorInnerAt_contMDiff g
      (isPointwiseMultilinear_covDerivAlong_riemannTensorField g X)
      (isPointwiseMultilinear_riemannTensorField g)
      ((hasSmoothComponents_riemannTensorField g).covDerivAlong
        g.leviCivitaConnection X)
      (hasSmoothComponents_riemannTensorField g)).mdifferentiable (by norm_num)) p
  rw [MorganTianLib.hessian, hfirst, X.dir_const_mul 2 p hmd,
    dir_covDerivAlong_riemannTensorInnerAt g p X X,
    dir_riemannNormAt_sq g p (g.leviCivitaConnection.cov X X)]
  simp only [secondCovDerivAlong, tensorInnerAt, sub_mul,
    Finset.sum_sub_distrib]
  ring

end Topping

end
