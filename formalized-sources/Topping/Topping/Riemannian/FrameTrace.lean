import MorganTianLib.Ch01.RicciFrameTrace
import MorganTianLib.Ch02.OrthoFrame
import Topping.Riemannian.TensorNorm

/-!
# Metric traces do not depend on the frame that computes them

`traceFirstTwo`, `trace₂` and `normSqAt` are all defined by feeding
`stdOrthonormalBasis ℝ (TangentSpace I p)` into the contracted slots. That is a
*per-point* choice, and it is the reason the resulting scalar functions cannot be
differentiated termwise: `p ↦ stdOrthonormalBasis ℝ (TangentSpace I p) i` is not
a vector field, so `q ↦ A(e_i(q),…)(q)` is not a composite of smooth maps.

This module removes the obstruction at the algebraic level, which is where it
actually lives. The contraction is basis-independent *provided the tensor is
pointwise multilinear* — that is exactly the hypothesis, and it is a genuine
hypothesis: `CovTensorField I M k = (Fin k → SmoothVectorField I M) → M → ℝ` is
an arbitrary map on tuples of fields, and nothing in the type forces the value at
`p` to depend linearly (or even only) on the values `Y i p`.

Two predicates carry the two things that are needed:

* `IsPointwiseTensorial A p` — `A Y p` depends only on the tangent vectors
  `Y i p`, so it *has* a pointwise value `pointwiseValue`;
* `IsPointwiseMultilinear A p` — that pointwise value is linear in each slot.

Under both, `traceFirstTwo`, `trace₂` and `normSqAt` agree with the value
computed in **any** orthonormal basis of `T_pM` (`traceFirstTwo_eq_sum_of_frame`,
`normSqAt_eq_sum_of_frame`). For a local *smooth* orthonormal frame — which
`MorganTianLib.exists_orthonormalFrame` produces — this turns the per-point sum
into a sum of smooth functions on a neighbourhood, which is what termwise
differentiation of `|A|²` and `ΔA` needs (memory item I-0494, asked for twice by
the maximum-principle lane in I-0482/I-0496).

The proofs go through DoCarmo's `Riemannian.bilinTrace` and Petersen's
`OrthonormalBasis.sum_apply_diagonal_invariant`: a diagonal sum over an
orthonormal basis of a *bilinear* form is a trace, hence basis-free. The work is
in packaging the relevant slot pair of `A` as an honest `V →ₗ[ℝ] V →ₗ[ℝ] ℝ`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Pointwise tensoriality -/

/-- **Math.** A covariant `k`-tensor field is *pointwise tensorial at `p`* when
its value at `p` depends only on the values of the arguments at `p`. This is what
"tensor" means and what the type `CovTensorField` does not enforce. -/
def IsPointwiseTensorial {k : ℕ} (A : CovTensorField I M k) (p : M) : Prop :=
  ∀ Y Z : Fin k → SmoothVectorField I M, (∀ i, Y i p = Z i p) → A Y p = A Z p

/-- **Math.** The pointwise value of a covariant `k`-tensor field at `p`, as a
function of `k` tangent vectors: evaluate on any extensions, `extendVector` being
the chosen ones. Under `IsPointwiseTensorial` this determines `A · p`
(`pointwiseValue_eq`). -/
def pointwiseValue {k : ℕ} (A : CovTensorField I M k) (p : M)
    (v : Fin k → TangentSpace I p) : ℝ :=
  A (fun i => MorganTianLib.extendVector p (v i)) p

omit [CompleteSpace E] in
/-- **Math.** For a pointwise tensorial field, evaluating on fields is the same
as evaluating the pointwise value on their values at `p`. -/
theorem pointwiseValue_eq {k : ℕ} {A : CovTensorField I M k} {p : M}
    (hA : IsPointwiseTensorial A p) (Y : Fin k → SmoothVectorField I M) :
    pointwiseValue A p (fun i => Y i p) = A Y p :=
  hA _ _ fun i => MorganTianLib.extendVector_apply p (Y i p)

/-- **Math.** A covariant `k`-tensor field is *pointwise multilinear at `p`* when
it is pointwise tensorial there and its pointwise value is additive and
homogeneous in every slot. This is the hypothesis under which metric
contractions of `A` are independent of the orthonormal basis used. -/
structure IsPointwiseMultilinear {k : ℕ} (A : CovTensorField I M k) (p : M) :
    Prop where
  /-- The value at `p` depends only on the arguments' values at `p`. -/
  tensorial : IsPointwiseTensorial A p
  /-- Additivity in each slot. -/
  add : ∀ (i : Fin k) (v : Fin k → TangentSpace I p) (x y : TangentSpace I p),
    pointwiseValue A p (Function.update v i (x + y))
      = pointwiseValue A p (Function.update v i x)
        + pointwiseValue A p (Function.update v i y)
  /-- Homogeneity in each slot. -/
  smul : ∀ (i : Fin k) (v : Fin k → TangentSpace I p) (c : ℝ)
    (x : TangentSpace I p),
    pointwiseValue A p (Function.update v i (c • x))
      = c * pointwiseValue A p (Function.update v i x)

/-! ### The contracted slot pair as a genuine bilinear form -/

section Bilin

variable {k : ℕ} {A : CovTensorField I M (k + 2)} {p : M}

omit [CompleteSpace E] in
/-- **Math.** The pointwise value of `A`, with the last `k` slots frozen, is a
genuine bilinear form in its first two slots — this is where
`IsPointwiseMultilinear` is spent, and it is what makes the diagonal sum over an
orthonormal basis a trace. -/
def pairBilin (hA : IsPointwiseMultilinear A p)
    (v : Fin k → TangentSpace I p) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x w => pointwiseValue A p (Fin.cons x (Fin.cons w v)))
    (fun x y w => by
      have h := hA.add 0
        (Fin.cons x (Fin.cons w v) : Fin (k + 2) → TangentSpace I p) x y
      rwa [Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero] at h)
    (fun c x w => by
      have h := hA.smul 0
        (Fin.cons x (Fin.cons w v) : Fin (k + 2) → TangentSpace I p) c x
      rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
      simpa using h)
    (fun x w₁ w₂ => by
      have h := hA.add 1
        (Fin.cons x (Fin.cons w₁ v) : Fin (k + 2) → TangentSpace I p) w₁ w₂
      rw [show (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ from rfl] at h
      simp only [← Fin.cons_update, Fin.update_cons_zero] at h
      exact h)
    (fun c x w => by
      have h := hA.smul 1
        (Fin.cons x (Fin.cons w v) : Fin (k + 2) → TangentSpace I p) c w
      rw [show (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ from rfl] at h
      simp only [← Fin.cons_update, Fin.update_cons_zero] at h
      simpa using h)

omit [CompleteSpace E] in
@[simp] private theorem pairBilin_apply (hA : IsPointwiseMultilinear A p)
    (v : Fin k → TangentSpace I p) (x w : TangentSpace I p) :
    pairBilin hA v x w = pointwiseValue A p (Fin.cons x (Fin.cons w v)) := rfl

end Bilin

/-! ### Frame independence of `tr₁₂` -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
/-- The diagonal sum of a bilinear form over an orthonormal basis is its trace,
hence the same for every orthonormal basis. Isolated over an abstract inner
product space so that the application below does not have to reconcile the
tangent space's two routes to a `NormedAddCommGroup` instance. -/
private theorem sum_diag_invariant {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis κ ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∑ i, B (b i) (b i) = ∑ i, B (b' i) (b' i) := by
  rw [← Riemannian.bilinTrace_eq_sum B b, Riemannian.bilinTrace_eq_sum B b']

omit [CompleteSpace E] in
/-- **Math.** **The metric trace does not depend on the orthonormal basis that
computes it.** For a pointwise multilinear `A` and any orthonormal basis `e` of
`T_pM`,
`(tr₁₂A)(Y₁,…,Y_k)(p) = Σᵢ A(eᵢ, eᵢ, Y₁(p),…,Y_k(p))`.

The right-hand side is the diagonal sum of the bilinear form `pairBilin`, hence
a trace (`Riemannian.bilinTrace`), hence basis-free. Multilinearity is genuinely
needed: for a merely pointwise tensorial `A` the two diagonal sums differ. -/
theorem traceFirstTwo_eq_sum_of_frame (g : RiemannianMetric I M) {k : ℕ}
    {A : CovTensorField I M (k + 2)} {p : M}
    (hA : IsPointwiseMultilinear A p)
    (Y : Fin k → SmoothVectorField I M) {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    traceFirstTwo g A Y p
      = ∑ i, pointwiseValue A p
          (Fin.cons (e i) (Fin.cons (e i) (fun j => Y j p))) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set v : Fin k → TangentSpace I p := fun j => Y j p with hv
  -- Both sides are the diagonal sum of `pairBilin hA v`, over two orthonormal
  -- bases; a diagonal sum of a bilinear form is a trace.
  have hstd : traceFirstTwo g A Y p
      = ∑ i, pairBilin hA v (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pairBilin_apply]
    refine hA.tensorial _ _ fun j => ?_
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro j; simp [hv]
  rw [hstd, sum_diag_invariant (stdOrthonormalBasis ℝ (TangentSpace I p)) e
    (pairBilin hA v)]
  exact Finset.sum_congr rfl fun i _ => pairBilin_apply hA v (e i) (e i)

/-! ### Expanding one slot over a frame -/

omit [CompleteSpace E] in
/-- **Math.** **Expanding a slot's argument over an orthonormal basis.** For a
pointwise multilinear `A` and an orthonormal basis `e` of `T_pM`,
`A(..., w, ...) = sum_m <e_m, w> A(..., e_m, ...)` in any single slot `i`.

This is `IsPointwiseMultilinear` doing the work it was defined for: the value is
linear in slot `i`, so substituting the orthonormal expansion of `w` and
distributing gives the sum. -/
theorem pointwiseValue_expand_slot (g : RiemannianMetric I M) {k : ℕ}
    {A : CovTensorField I M k} {p : M} (hA : IsPointwiseMultilinear A p)
    (i : Fin k) (v : Fin k → TangentSpace I p) (w : TangentSpace I p)
    {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    pointwiseValue A p (Function.update v i w)
      = ∑ m, g.metricInner p (e m) w *
          pointwiseValue A p (Function.update v i (e m)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hexp : w = ∑ m, (inner ℝ (e m) w) • (e m : TangentSpace I p) := by
    have hcoef : ∀ m, (inner ℝ (e m) w) • (e m : TangentSpace I p)
        = (e.repr w).ofLp m • e m := fun m => by rw [e.repr_apply_apply w m]
    rw [Finset.sum_congr rfl fun m _ => hcoef m]
    exact (e.sum_repr w).symm
  have hsum : ∀ (s : Finset _) (c : _ → ℝ),
      pointwiseValue A p (Function.update v i (∑ m ∈ s, c m • (e m : TangentSpace I p)))
        = ∑ m ∈ s, c m * pointwiseValue A p (Function.update v i (e m)) := by
    intro s c
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        have h0 : pointwiseValue A p (Function.update v i (0 : TangentSpace I p))
            = 0 := by
          have h := hA.smul i v 0 (0 : TangentSpace I p)
          rw [zero_smul] at h
          simpa using h
        exact h0
    | insert a t ha IH =>
        rw [Finset.sum_insert ha, hA.add i v _ _, IH, Finset.sum_insert ha,
          hA.smul i v (c a) (e a)]
  have hbridge : ∀ m, g.metricInner p (e m) w = inner ℝ (e m) w := fun m =>
    (MorganTianLib.inner_tangentSpace_eq_metricInner g p (e m) w).symm
  rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => by rw [hbridge m])]
  conv_lhs => rw [hexp]
  rw [hsum Finset.univ (fun m => inner ℝ (e m) w)]

/-! ### Frame independence of `|A|²`

The square norm is not a single trace: it is a `k`-fold sum of squares. The
invariance is proved slot by slot, each step being the Hilbert–Schmidt
invariance of a bilinear form in which the two arguments both feed **the same**
slot of `A` — so only linearity in that one slot is used, and the remaining
slots are frozen as parameters. This is the same argument
`MorganTianLib.hessianNormSqAt_eq_sum` makes for `k = 2`, run as an induction
over the slots. -/

/-- **Math.** The abstract slot-wise step: for a function `F` of `k+1` vectors that is
linear in its first argument, `Σ_{i,w} F(bᵢ, w)²` does not depend on the
orthonormal basis `b` used in that first argument.

`F` is packaged as a family of linear functionals indexed by the frozen tail,
which is all the step needs. -/
private theorem sum_sq_slot_invariant {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis κ ℝ V)
    {T : Type*} [Fintype T] (F : T → V →ₗ[ℝ] ℝ) :
    ∑ i, ∑ w : T, F w (b i) ^ 2 = ∑ i, ∑ w : T, F w (b' i) ^ 2 := by
  classical
  -- `Q x y = Σ_w F w x · F w y` is bilinear, and its diagonal is the inner sum.
  let Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => ∑ w : T, F w x * F w y)
      (fun x₁ x₂ y => by
        simp only [map_add]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring)
      (fun c x y => by
        simp only [map_smul, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring)
      (fun x y₁ y₂ => by
        simp only [map_add]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring)
      (fun c x y => by
        simp only [map_smul, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring)
  have hQ : ∀ x, Q x x = ∑ w : T, F w x ^ 2 := fun x =>
    Finset.sum_congr rfl fun w _ => (sq (F w x)).symm
  calc ∑ i, ∑ w : T, F w (b i) ^ 2
      = ∑ i, Q (b i) (b i) := Finset.sum_congr rfl fun i _ => (hQ (b i)).symm
    _ = ∑ i, Q (b' i) (b' i) := sum_diag_invariant b b' Q
    _ = ∑ i, ∑ w : T, F w (b' i) ^ 2 := Finset.sum_congr rfl fun i _ => hQ (b' i)

/-- **Math.** Slot-wise linearity of a `k`-argument function, the exact
hypothesis the induction below consumes. -/
private def IsMultilinearOn {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {k : ℕ} (F : (Fin k → V) → ℝ) : Prop :=
  (∀ (i : Fin k) (v : Fin k → V) (x y : V),
      F (Function.update v i (x + y))
        = F (Function.update v i x) + F (Function.update v i y))
    ∧ ∀ (i : Fin k) (v : Fin k → V) (c : ℝ) (x : V),
        F (Function.update v i (c • x)) = c * F (Function.update v i x)

/-- **Math.** Peeling the first slot of a sum over index tuples: a sum over
`Fin (k+1) → μ` is the double sum over the first index and the tail. -/
private theorem sum_tuple_peel {V : Type*} {μ : Type*} [Fintype μ] {k : ℕ}
    (F : (Fin (k + 1) → V) → ℝ) (c : μ → V) :
    ∑ v : Fin (k + 1) → μ, F (fun j => c (v j)) ^ 2
      = ∑ i : μ, ∑ w : Fin k → μ,
          F (Fin.cons (c i) (fun j => c (w j))) ^ 2 := by
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => μ)).symm _
    (fun q : μ × (Fin k → μ) =>
      F (Fin.cons (c q.1) (fun j => c (q.2 j))) ^ 2) (fun v => by
      simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk]
      have harg : (fun j => c (v j))
          = Fin.cons (c (v 0)) (fun j => c (Fin.tail v j)) := by
        funext j
        refine Fin.cases ?_ ?_ j <;> simp [Fin.tail]
      rw [harg]), Fintype.sum_prod_type]

/-- **Math.** **The sum of squares of the components is basis-independent.** For
a multilinear `F` of `k` vector arguments and two orthonormal bases `b, b'`,
`Σ_{v : Fin k → ι} F(b_{v₁},…,b_{v_k})² = Σ_{v : Fin k → κ} F(b'_{v₁},…)²`.

Induction on `k`, peeling the first slot: the tail sum is a family of functionals
linear in the first slot, so `sum_sq_slot_invariant` swaps the basis there, and
the induction hypothesis — applied to `F` with the first argument frozen at a
`b'` vector, which is still multilinear in the remaining slots — swaps it in the
tail. -/
private theorem sum_sq_multilinear_invariant {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis κ ℝ V) :
    ∀ {k : ℕ} (F : (Fin k → V) → ℝ), IsMultilinearOn F →
      ∑ v : Fin k → ι, F (fun j => b (v j)) ^ 2
        = ∑ v : Fin k → κ, F (fun j => b' (v j)) ^ 2 := by
  intro k
  induction k with
  | zero =>
      intro F _
      simp only [Finset.univ_unique, Finset.sum_singleton]
      congr 2
      exact funext fun j => j.elim0
  | succ k ih =>
      intro F hF
      -- Peel the first slot on both sides.
      rw [sum_tuple_peel F (fun i => b i), sum_tuple_peel F (fun i => b' i)]
      -- Step 1: swap the basis in the first slot, the tail sum being a family of
      -- functionals linear there.
      have hlin : ∀ w : Fin k → V, ∃ L : V →ₗ[ℝ] ℝ,
          ∀ x, L x = F (Fin.cons x w) := by
        intro w
        refine ⟨LinearMap.mk (AddHom.mk (fun x => F (Fin.cons x w)) ?_) ?_,
          fun _ => rfl⟩
        · intro x y
          have h := hF.1 0 (Fin.cons x w : Fin (k + 1) → V) x y
          rwa [Fin.update_cons_zero, Fin.update_cons_zero,
            Fin.update_cons_zero] at h
        · intro c x
          have h := hF.2 0 (Fin.cons x w : Fin (k + 1) → V) c x
          rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
          simpa using h
      choose L hL using hlin
      have step1 : ∑ i : ι, ∑ w : Fin k → ι,
            F (Fin.cons (b i) (fun j => b (w j))) ^ 2
          = ∑ i : κ, ∑ w : Fin k → ι,
            F (Fin.cons (b' i) (fun j => b (w j))) ^ 2 := by
        have h := sum_sq_slot_invariant b b'
          (T := (Fin k → ι)) (fun w => L (fun j => b (w j)))
        simpa only [hL] using h
      rw [step1]
      -- Step 2: for each fixed first vector, the tail is multilinear, so the
      -- induction hypothesis swaps the basis there.
      refine Finset.sum_congr rfl fun i _ => ?_
      refine ih (fun w => F (Fin.cons (b' i) w)) ⟨?_, ?_⟩
      · intro j v x y
        have h := hF.1 j.succ (Fin.cons (b' i) v : Fin (k + 1) → V) x y
        simp only [← Fin.cons_update] at h
        exact h
      · intro j v c x
        have h := hF.2 j.succ (Fin.cons (b' i) v : Fin (k + 1) → V) c x
        simp only [← Fin.cons_update] at h
        exact h

omit [CompleteSpace E] in
/-- **Math.** **`|A|²` does not depend on the orthonormal basis that computes
it.** For a pointwise multilinear covariant `k`-tensor field and any orthonormal
basis `e` of `T_pM`,
`|A|²(p) = Σ_{i₁…i_k} A(e_{i₁},…,e_{i_k})²`.

This is the theorem the maximum-principle lane asked for twice (I-0482, I-0496)
and the recorded blocker of the curvature Bochner identity (I-0494): `normSqAt`
is *defined* by `stdOrthonormalBasis`, a per-point choice, so `q ↦ |A|²(q)` was
not visibly a sum of smooth functions. Composed with
`MorganTianLib.exists_orthonormalFrame` — which gives *smooth* fields that are
orthonormal on a neighbourhood — this rewrites `|A|²` near `p` as a finite sum of
products of the smooth component functions `A(F_{i₁},…,F_{i_k})`, and termwise
differentiation becomes available. -/
theorem normSqAt_eq_sum_of_frame (g : RiemannianMetric I M) {k : ℕ}
    {A : CovTensorField I M k} {p : M} (hA : IsPointwiseMultilinear A p)
    {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    normSqAt g A p = ∑ v : Fin k → ι, pointwiseValue A p (fun j => e (v j)) ^ 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hmul : IsMultilinearOn (V := TangentSpace I p) (pointwiseValue A p) :=
    ⟨fun i v x y => hA.add i v x y, fun i v c x => hA.smul i v c x⟩
  exact sum_sq_multilinear_invariant (stdOrthonormalBasis ℝ (TangentSpace I p)) e
    (pointwiseValue A p) hmul

/-! ### `|A|²` and `tr₁₂A` over a smooth local frame

Frame independence is only useful once it is instantiated at a frame that is
*smooth in `p`*. `MorganTianLib.exists_orthonormalFrame` supplies exactly that:
global smooth fields `F₁,…,F_n` which are `g`-orthonormal at every point of some
neighbourhood of `p`. Combining the two gives the statements that unlock termwise
differentiation. -/

/-- **Math.** **`|A|²` is a finite sum of squares of smooth-frame components near
`p`.** There are global smooth vector fields `F₁,…,F_n` and a neighbourhood of
`p` on which
`|A|²(q) = Σ_{i₁…i_k} A(F_{i₁},…,F_{i_k})(q)²`,
provided `A` is pointwise multilinear at each point of that neighbourhood.

The right-hand side is now a *fixed finite sum of the fields' component
functions*, so its regularity is that of `A(F_{i₁},…,F_{i_k})` — no per-point
basis remains. This is the statement that turns `HasSmoothComponents A` into
smoothness of `|A|²`, which is what the curvature Bochner identity was blocked
on (I-0494). -/
theorem exists_smooth_frame_normSqAt (g : RiemannianMetric I M) [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    {k : ℕ} (A : CovTensorField I M k) (p : M) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      ∀ᶠ q in 𝓝 p, (IsPointwiseMultilinear A q →
        normSqAt g A q
          = ∑ v : Fin k → Fin (Module.finrank ℝ E),
              A (fun j => F (v j)) q ^ 2) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨F, hF⟩ := MorganTianLib.exists_orthonormalFrame (I := I) g p
  refine ⟨F, ?_⟩
  -- The orthonormality of the frame holds eventually for each pair `(i,j)`;
  -- intersect the finitely many neighbourhoods.
  have hall : ∀ᶠ q in 𝓝 p, ∀ i j,
      g.metricInner q (F i q) (F j q) = if i = j then 1 else 0 :=
    (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun i =>
      (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun j => hF i j
  filter_upwards [hall] with q hq hAq
  -- At `q` the frame is an orthonormal basis, so frame independence applies.
  rw [normSqAt_eq_sum_of_frame g hAq
    (MorganTianLib.frameOrthonormalBasis (I := I) g hq)]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  refine hAq.tensorial _ _ fun j => ?_
  rw [MorganTianLib.extendVector_apply]
  exact MorganTianLib.frameOrthonormalBasis_apply (I := I) g hq (v j)

end Topping

end
