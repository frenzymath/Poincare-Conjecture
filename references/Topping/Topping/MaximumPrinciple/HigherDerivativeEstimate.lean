import Topping.MaximumPrinciple.DerivativeEstimate

/-!
# The Bernstein--Bando--Shi cascade: Theorem 3.3.1 for every `k`

`Topping.MaximumPrinciple.DerivativeEstimate` proves the maximum-principle content
of Topping's Theorem 3.3.1 for `k = 1`: the combination `u = t w + α q` with
`w = |∇\Rm|^2`, `q = |\Rm|^2`, whose reaction bracket the choice `α = (1+c)/2`
kills. That argument does not iterate as stated, because for `k = 2` the term
`t^2|∇^2\Rm|^2` differentiates to `2t|∇^2\Rm|^2`, which no single `α` absorbs.

Topping's actual induction uses the *whole tower* at once:

`u = Σ_{j≤k} a_j t^j w_j`,   `w_j = |∇^j\Rm|^2`,

and the cancellation is telescoping rather than pointwise. Differentiating level
`j` produces `j a_j t^{j-1} w_j`; the favourable `-2 w_{j}` inside level `j-1`'s
evolution inequality contributes `-2 a_{j-1} t^{j-1} w_j`. So the coefficient of
`t^{j-1} w_j` is

`j a_j - 2 a_{j-1} + (reaction, controlled by κt ≤ 1)`,

and choosing `a_j` recursively downward makes every one of them nonpositive at
once. That simultaneous cancellation is what this module formalizes: the
maximum-principle *step* for arbitrary `k`. It is not the full theorem — the
induction that bounds each level's reaction using the previous levels is not
performed here (see the caveats below).

What is proved here, over abstract nonnegative `w : ℕ → M → ℝ → ℝ` (to be read as
`|∇^j\Rm|^2`):

* `shiCoeff` — the recursive coefficients, and `shiCoeff_telescope`, the identity
  `(j+1)a_{j+1} + (1+c)a_{j+1} ≤ 2a_j` that makes the tower cancel;
* `shi_cancel_sum_le` — the cancellation over the whole tower, leaving exactly the
  two terms the book leaves: level `0`'s reaction and the discarded top term;
* `shiCombination`, `shi_parabolic_inequality` — the combination `Σ_j a_j t^j w_j`
  and its parabolic inequality with constant reaction;
* `mul_pow_le_affineBarrier_of_shiTower` — the weak maximum principle applied to
  it, giving `t^k w_k ≤ a_0 m^2 + C t` on `[0,T]`, `T ≤ 1/m`;
* `sqrt_le_div_of_shiTower` — the division by `t^k` and the square root.

Two honest caveats, both about what is *not* claimed.

The geometric input is a hypothesis. `HasShiTowerOn` — the tower
`∂_t w_j ≤ Δ w_j - 2 w_{j+1} + κ·w_j + ρ` that Topping derives from the commutation
formulae — is proved nowhere in this project, so every result here is an
implication. Its `κ·w_j` term is not cosmetic: see that definition's docstring for
why the cross terms cannot be collected into `ρ`.

The constant is not asserted to have Topping's `C(n,k)M` shape. It comes out as
`√(a_0m^2 + (ρ·Σa_jT^j + a_0κm^2)T)`, carrying `T`, `κ` and `ρ`. Reducing that to
`CM` needs `κ ≲ m` and `ρ ≲ m^3` on Topping's interval, which is what the *induction
on `k`* supplies: at level `k` the lower levels are already bounded by the preceding
steps. That induction is not performed here. What is proved is one cascade step,
uniformly in `k` — which is the part the `k = 1` file could not express at all.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

/-! ### The coefficients of the tower -/

/-- **Math.** The coefficients `a_j` of Topping's telescoping combination, defined
by downward recursion from `a_k = 1`. The requirement is that level `j`'s
differentiated weight `j a_j` be dominated by twice level `j-1`'s coefficient, so
`a_{j-1} := (1 + c + j) * a_j / 2` is a safe choice: it leaves slack `1 + c` for
the reaction term as well.

Indexing runs downward from the top level `k`, so `shiCoeff c k j` is the
coefficient of `t^j w_j` and `shiCoeff c k k = 1`. -/
def shiAux (c : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | d + 1 => (1 + c + ((k - d : ℕ) : ℝ)) * shiAux c k d / 2

/-- **Math.** The coefficient of `t^j w_j` in the telescoping combination, obtained
by running `shiAux` over the gap `k - j` to the top level. -/
def shiCoeff (c : ℝ) (k j : ℕ) : ℝ := shiAux c k (k - j)

/-- **Math.** The top coefficient is `1`, which is what makes the conclusion about
`w_k` rather than a multiple of it. -/
theorem shiCoeff_top (c : ℝ) (k : ℕ) : shiCoeff c k k = 1 := by
  simp [shiCoeff, shiAux]

/-- **Math.** Above the top level the coefficients are `1` as well; only `j ≤ k`
is ever used, and this pins the recursion's base case. -/
theorem shiCoeff_of_le (c : ℝ) {k j : ℕ} (h : k ≤ j) : shiCoeff c k j = 1 := by
  rw [shiCoeff, Nat.sub_eq_zero_of_le h]
  rfl

/-- **Math.** Below the top level the recursion unfolds: the coefficient of level
`j` is built from that of level `j+1`. -/
theorem shiCoeff_succ (c : ℝ) {k j : ℕ} (h : j < k) :
    shiCoeff c k j = (1 + c + ((j + 1 : ℕ) : ℝ)) * shiCoeff c k (j + 1) / 2 := by
  have hgap : k - j = (k - (j + 1)) + 1 := by omega
  have hsub : k - (k - (j + 1)) = j + 1 := by omega
  rw [shiCoeff, hgap, shiAux, hsub, shiCoeff]

/-- **Math.** Every coefficient is positive: the recursion multiplies by a
positive factor when `c ≥ 0`. -/
theorem shiCoeff_pos {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : ∀ j, 0 < shiCoeff c k j := by
  intro j
  induction hd : k - j generalizing j with
  | zero =>
      rw [shiCoeff_of_le c (by omega)]
      exact one_pos
  | succ d ih =>
      have hjk : j < k := by omega
      rw [shiCoeff_succ c hjk]
      have := ih (j + 1) (by omega)
      positivity

/-- **Math.** **The telescoping inequality.** The differentiated weight of level
`j+1` is dominated by twice the coefficient of level `j`, with slack `1 + c` left
over for the reaction:

`(j+1) a_{j+1} + (1 + c) a_{j+1} ≤ 2 a_j`.

This single inequality is what makes the whole tower cancel simultaneously, and it
holds by construction of `shiCoeff` — with equality, in fact, which is why the
coefficients are not merely "large enough" but the natural choice. -/
theorem shiCoeff_telescope {c : ℝ} (hc : 0 ≤ c) {k j : ℕ} (h : j < k) :
    ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) + (1 + c) * shiCoeff c k (j + 1)
      ≤ 2 * shiCoeff c k j := by
  rw [shiCoeff_succ c h]
  have hpos := shiCoeff_pos hc k (j + 1)
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  ring_nf
  nlinarith [hpos]

/-! ### The combination and its parabolic inequality -/

section Estimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M]

/-- **Math.** Topping's telescoping combination `u = Σ_{j≤k} a_j t^j w_j`, to be
read at `w_j = |∇^j\Rm|^2`. The powers of `t` are what make the higher levels
vanish at `t = 0`, so the initial datum only sees level `0`. -/
def shiCombination (c : ℝ) (k : ℕ) (w : ℕ → M → ℝ → ℝ) (x : M) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), shiCoeff c k j * t ^ j * w j x t

set_option linter.unusedSectionVars false in
/-- **Math.** At `t = 0` only level `0` survives, so the initial bound on the
combination is `a_0 w_0(·,0)` — the reason the estimate needs no initial control on
the derivatives themselves. -/
theorem shiCombination_zero (c : ℝ) (k : ℕ) (w : ℕ → M → ℝ → ℝ) (x : M) :
    shiCombination c k w x 0 = shiCoeff c k 0 * w 0 x 0 := by
  rw [shiCombination, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · simp
  · intro j hj hj0
    have : (0 : ℝ) ^ j = 0 := zero_pow hj0
    rw [this]
    ring

/-- **Math.** The tower of evolution inequalities Topping derives from the
commutation formulae, in the form the cascade consumes:

`∂_t w_j ≤ Δ w_j - 2 w_{j+1} + κ · w_j + ρ`.

Three parts, each doing a specific job:

* `-2 w_{j+1}` is level `j`'s favourable term. It is what pays for the
  differentiated weight of level `j+1`, and it is the only reason the cascade
  closes rather than losing a power of `t` at every step.
* `κ · w_j` is the part of the reaction proportional to the level being estimated.
  It carries the `t` that `κT ≤ 1` spends, which is why it lands on the *same*
  monomial `t^{j-1}w_j` as the differentiated weight.
* `ρ` is what remains after that: a genuine constant.

The split matters, and getting it wrong is how a weakening hides here. The
commutation formulae produce cross terms
`Σ_{i+l=j}|∇^i\Rm||∇^l\Rm||∇^j\Rm|`, and **every one of them carries a factor
`|∇^j\Rm|`** — the level being estimated. So bounding the lower levels by induction
does *not* turn them into a constant; it turns them into `C·√(w_j)`, which is
absorbed into `κ·w_j` (together with the diagonal `c√q·w_j`), not into `ρ`. A tower
stated with a bare additive constant in place of `κ·w_j` would presuppose an a
priori bound on the top level, which is the conclusion — that would be assuming
what is to be proved. Hence `κ` is a separate parameter with its own smallness
hypothesis `κT ≤ 1`, and `ρ` collects only what is genuinely level-independent. -/
def HasShiTowerOn (g : ℝ → RiemannianMetric I M) (w : ℕ → M → ℝ → ℝ)
    (kappa rho : ℝ) (k : ℕ) (J : Set ℝ) : Prop :=
  ∀ j < k + 1, ∀ t ∈ J, ∀ x : M,
    derivWithin (fun s => w j x s) J t ≤
      metricLaplacianAt (g t) (fun y => w j y t) x
        - 2 * w (j + 1) x t
        + kappa * w j x t
        + rho

/-! ### The telescoping cancellation

This is the arithmetic heart of the cascade, isolated from the manifold so it can
be checked on its own. Write `b j = a_j t^j` for the weights. Differentiating the
combination gives, at each level `j`,

`j a_j t^{j-1} w_j + a_j t^j (∂_t w_j)`,

and substituting the tower bound for `∂_t w_j` produces three groups of terms:
the Laplacians (which reassemble into `Δu` by linearity), the favourable
`-2 a_j t^j w_{j+1}`, and the reactions `κ a_j t^j w_j + ρ a_j t^j`.

The claim is that everything except level `0`'s reaction and the `ρ` group is
nonpositive. For level `j+1 ≤ k` the coefficient of `t^j w_{j+1}` collects

`(j+1) a_{j+1}`  (differentiated weight, since `t^{j+1}` gives `(j+1)t^j`)
`-2 a_j`         (favourable term of level `j`)
`+ κ t · a_{j+1}` (level `j+1`'s own reaction, which carries one extra `t`),

and `κt ≤ κT ≤ 1` bounds the last by `(1+c) a_{j+1}` worth of slack. That is
exactly `shiCoeff_telescope`. -/

set_option linter.unusedSectionVars false in
/-- **Math.** The single-level cancellation, as pure arithmetic: with the reaction
factor `d ≤ 1 + c` and nonnegative `v`, the differentiated weight of level `j+1`
plus its reaction is dominated by the favourable term of level `j`.

`(j+1) a_{j+1} v + d a_{j+1} v ≤ 2 a_j v`

This is `shiCoeff_telescope` with the reaction slack spent. Callers instantiate `d`
at `κt`, so the hypothesis `d ≤ 1 + c` is discharged from `κT ≤ 1 ≤ 1 + c`. -/
theorem shi_level_cancel {c : ℝ} (hc : 0 ≤ c) {k j : ℕ} (h : j < k)
    {v d : ℝ} (hv : 0 ≤ v) (hd : d ≤ 1 + c) :
    ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) * v
        + d * shiCoeff c k (j + 1) * v
      ≤ 2 * shiCoeff c k j * v := by
  have hpos := shiCoeff_pos hc k (j + 1)
  have htel := shiCoeff_telescope hc h
  have hreact : d * shiCoeff c k (j + 1) ≤ (1 + c) * shiCoeff c k (j + 1) :=
    mul_le_mul_of_nonneg_right hd hpos.le
  nlinarith [hv, htel, hreact]

/-! ### Reassembling the tower

The bookkeeping is a single index shift. Level `j`'s favourable term is
`-2 a_j t^j w_{j+1}`, and level `j+1`'s differentiated weight is
`(j+1) a_{j+1} t^j w_{j+1}` — the *same* monomial `t^j w_{j+1}`. Summing over
`j < k` therefore pairs them off, and the two leftovers are level `0`'s weight
(nothing differentiates into it) and level `k`'s favourable term
`-2 a_k t^k w_{k+1}`, which is only ever discarded. -/

/-- **Math.** The total weight of the tower at time `T`, `Σ_{j≤k} a_j T^j`. The
off-diagonal constant `ρ` enters the combination once per level, so this is the
factor by which it is amplified: a `C(c,k,T)` and nothing else.

Evaluating at `T` rather than at `1` is not a convenience — `t^j ≤ T^j` for
`0 ≤ t ≤ T` needs no assumption, whereas `t^j ≤ 1` would need `T ≤ 1`, which
Topping's interval `[0,1/M]` does not give when `M < 1`. -/
def shiWeightAt (c : ℝ) (k : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), shiCoeff c k j * T ^ j

/-- **Math.** The total weight is positive for `T > 0`. -/
theorem shiWeightAt_pos {c : ℝ} (hc : 0 ≤ c) (k : ℕ) {T : ℝ} (hT : 0 < T) :
    0 < shiWeightAt c k T := by
  rw [shiWeightAt]
  refine Finset.sum_pos (fun j _ => ?_) ⟨0, Finset.mem_range.mpr (by omega)⟩
  have := shiCoeff_pos hc k j
  positivity

/-- **Math.** **The telescoping identity, as a finite-sum rearrangement.** Writing
`b j = a_j t^j`, the terms of the differentiated combination that involve the
levels `w_1,…,w_k` are

`Σ_{j≤k} j a_j t^{j-1} w_j`  (the differentiated weights)

and the favourable terms are `-2 Σ_{j≤k} a_j t^j w_{j+1}`. Shifting the second sum
by one index makes both range over `w_{j+1}` for `j < k`, plus the discarded top
term `-2a_k t^k w_{k+1}`.

Stated as: the differentiated weights of levels `1..k` equal the shifted sum. -/
theorem shi_weight_deriv_sum_eq (c : ℝ) (k : ℕ) (t : ℝ) (v : ℕ → ℝ) :
    ∑ j ∈ Finset.range (k + 1), (j : ℝ) * shiCoeff c k j * t ^ (j - 1) * v j
      = ∑ j ∈ Finset.range k,
          ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) * t ^ j * v (j + 1) := by
  rw [Finset.sum_range_succ' (fun j => (j : ℝ) * shiCoeff c k j * t ^ (j - 1) * v j) k]
  simp

/-- **Math.** Regression check on the index shift: at `k = 2` the rearrangement must
produce exactly the two monomials `a_1 w_1` and `2a_2 t w_2`, with the `j = 0` term
dropping. A `simp`-closed sum identity is easy to state degenerately, so this pins
which terms survive. -/
example (c : ℝ) (t : ℝ) (v : ℕ → ℝ) :
    ∑ j ∈ Finset.range (2 + 1), (j : ℝ) * shiCoeff c 2 j * t ^ (j - 1) * v j
      = shiCoeff c 2 1 * v 1 + 2 * shiCoeff c 2 2 * t * v 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num

/-! ### The combination obeys a parabolic inequality with constant reaction -/

set_option linter.unusedSectionVars false in
/-- **Math.** **The telescoping cancellation over the whole tower.** Every monomial
`t^j w_{j+1}` for `j < k` receives exactly three contributions — the differentiated
weight `(j+1)a_{j+1}t^j`, the diagonal reaction `c r a_{j+1} t^{j+1}`, and level
`j`'s favourable `-2a_j t^j` — and `shi_level_cancel` makes their sum nonpositive.

Two terms are left over, and they are the two the book leaves over as well:
level `0`'s diagonal reaction `a_0 c r w_0` (there is no lower level to pay for
it — this is the `cαm^3` of the `k = 1` case), and the top favourable term
`-2a_k t^k w_{k+1}`, which is nonpositive and simply discarded. -/
theorem shi_cancel_sum_le {c : ℝ} (hc : 0 ≤ c) (k : ℕ) {t kappa : ℝ}
    (ht : 0 ≤ t) (hk1 : t * kappa ≤ 1) {v : ℕ → ℝ}
    (hv : ∀ j, 0 ≤ v j) :
    ∑ j ∈ Finset.range (k + 1),
        ((j : ℝ) * shiCoeff c k j * t ^ (j - 1) * v j
          + shiCoeff c k j * t ^ j * (kappa * v j)
          - 2 * (shiCoeff c k j * t ^ j * v (j + 1)))
      ≤ shiCoeff c k 0 * (kappa * v 0) := by
  classical
  -- Reindex: the differentiated weights of levels `1..k` are the shifted sum.
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    shi_weight_deriv_sum_eq c k t v]
  -- Peel level `0`'s diagonal reaction off the middle group.
  rw [Finset.sum_range_succ' (fun j => shiCoeff c k j * t ^ j * (kappa * v j)) k]
  -- Peel the top favourable term off the last group.
  rw [Finset.sum_range_succ (fun j => 2 * (shiCoeff c k j * t ^ j * v (j + 1))) k]
  -- What remains is a term-by-term comparison over `Finset.range k`.
  have hterm : ∀ j ∈ Finset.range k,
      ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) * t ^ j * v (j + 1)
          + shiCoeff c k (j + 1) * t ^ (j + 1) * (kappa * v (j + 1))
        ≤ 2 * (shiCoeff c k j * t ^ j * v (j + 1)) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hpow : 0 ≤ t ^ j := pow_nonneg ht j
    -- `t ^ j * v (j+1) ≥ 0` is the `v` of `shi_level_cancel`; level `j+1`'s own
    -- reaction carries one extra `t`, so its factor is `t * κ ≤ 1 ≤ 1 + c`.
    have hvj : 0 ≤ v (j + 1) := hv (j + 1)
    have hd : t * kappa ≤ 1 + c := by linarith
    have hcancel := shi_level_cancel hc hjk (v := t ^ j * v (j + 1))
      (d := t * kappa) (by positivity) hd
    have hrw : shiCoeff c k (j + 1) * t ^ (j + 1) * (kappa * v (j + 1))
        = (t * kappa) * shiCoeff c k (j + 1) * (t ^ j * v (j + 1)) := by
      rw [pow_succ]; ring
    have hrw2 : ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) * t ^ j * v (j + 1)
        = ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) * (t ^ j * v (j + 1)) := by
      ring
    rw [hrw, hrw2]
    calc ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) * (t ^ j * v (j + 1))
          + (t * kappa) * shiCoeff c k (j + 1) * (t ^ j * v (j + 1))
        ≤ 2 * shiCoeff c k j * (t ^ j * v (j + 1)) := hcancel
      _ = 2 * (shiCoeff c k j * t ^ j * v (j + 1)) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  have htop : 0 ≤ 2 * (shiCoeff c k k * t ^ k * v (k + 1)) := by
    have hck := (shiCoeff_pos hc k k).le
    have hvk := hv (k + 1)
    have htk : (0:ℝ) ≤ t ^ k := pow_nonneg ht k
    positivity
  simp only [pow_zero, mul_one]
  linarith
/-- **Math.** **The cascade's cancellation, assembled.** Given

* the differentiated weights `Σ_j j a_j t^{j-1} w_j`,
* the tower's favourable terms `-2 Σ_j a_j t^j w_{j+1}`,
* the tower's level-proportional reactions `Σ_j κ a_j t^j w_j`,

the whole reaction of `u = Σ_j a_j t^j w_j` is at most
`ρ·shiWeightAt c k T + a_0 κ w_0`. Every monomial `t^j w_{j+1}` with `j < k` is
killed by `shi_level_cancel`, the top favourable term `-2a_k t^k w_{k+1}` is
discarded, and level `0`'s own reaction is what survives — nothing below it pays.

`hk1` is `tκ ≤ 1`, which on `[0,T]` follows from `Tκ ≤ 1`. -/
theorem shi_reaction_le {c rho : ℝ} (hc : 0 ≤ c) (k : ℕ) {t kappa T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) (hk1 : t * kappa ≤ 1) {v : ℕ → ℝ}
    (hv : ∀ j, 0 ≤ v j) (hrho : 0 ≤ rho) :
    ∑ j ∈ Finset.range (k + 1),
        ((j : ℝ) * shiCoeff c k j * t ^ (j - 1) * v j
          + shiCoeff c k j * t ^ j * (-2 * v (j + 1) + kappa * v j + rho))
      ≤ rho * shiWeightAt c k T + shiCoeff c k 0 * (kappa * v 0) := by
  classical
  -- Group the summand as (cancelling part) + (rho part).
  have hsplit : ∀ j ∈ Finset.range (k + 1),
      (j : ℝ) * shiCoeff c k j * t ^ (j - 1) * v j
        + shiCoeff c k j * t ^ j * (-2 * v (j + 1) + kappa * v j + rho)
      = ((j : ℝ) * shiCoeff c k j * t ^ (j - 1) * v j
          + shiCoeff c k j * t ^ j * (kappa * v j)
          - 2 * (shiCoeff c k j * t ^ j * v (j + 1)))
        + shiCoeff c k j * t ^ j * rho := by
    intro j _; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hrhogroup : ∑ j ∈ Finset.range (k + 1), shiCoeff c k j * t ^ j * rho
      ≤ rho * shiWeightAt c k T := by
    rw [shiWeightAt, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hcj := (shiCoeff_pos hc k j).le
    have hpow : t ^ j ≤ T ^ j := pow_le_pow_left₀ ht htT j
    have : shiCoeff c k j * t ^ j ≤ shiCoeff c k j * T ^ j :=
      mul_le_mul_of_nonneg_left hpow hcj
    calc shiCoeff c k j * t ^ j * rho
        ≤ shiCoeff c k j * T ^ j * rho := mul_le_mul_of_nonneg_right this hrho
      _ = rho * (shiCoeff c k j * T ^ j) := by ring
  have hcancel : ∑ j ∈ Finset.range (k + 1),
      ((j : ℝ) * shiCoeff c k j * t ^ (j - 1) * v j
        + shiCoeff c k j * t ^ j * (kappa * v j)
        - 2 * (shiCoeff c k j * t ^ j * v (j + 1)))
      ≤ shiCoeff c k 0 * (kappa * v 0) := shi_cancel_sum_le hc k ht hk1 hv
  linarith

/-! ### Dividing by `t^k`

The conclusion of the maximum principle bounds the whole combination; only the top
level is wanted. Since every summand is nonnegative, `a_k t^k w_k ≤ u`, and
`a_k = 1`. -/

set_option linter.unusedSectionVars false in
/-- **Math.** The top level is dominated by the combination, because every other
summand is nonnegative and the top coefficient is `1`. -/
theorem mul_pow_le_shiCombination {c : ℝ} (hc : 0 ≤ c) (k : ℕ)
    {w : ℕ → M → ℝ → ℝ} {x : M} {t : ℝ} (ht : 0 ≤ t)
    (hw : ∀ j, 0 ≤ w j x t) :
    t ^ k * w k x t ≤ shiCombination c k w x t := by
  classical
  rw [shiCombination]
  have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum
    (f := fun j => shiCoeff c k j * t ^ j * w j x t)
    (fun j _ => by
      have := (shiCoeff_pos hc k j).le
      have := hw j
      have : (0:ℝ) ≤ t ^ j := pow_nonneg ht j
      positivity) hmem
  rwa [shiCoeff_top, one_mul] at hle

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping's `k`-th derivative estimate, after division.** From
`t^k w_k ≤ B` with `w_k = |∇^k\Rm|^2` and `B` the barrier value,

`|∇^k\Rm| ≤ √B / t^{k/2}`,

which is the displayed form `C M / t^{k/2}` once `B` is the `C^2M^2` the maximum
principle produces. -/
theorem sqrt_le_div_of_mul_pow_le {k : ℕ} {W B t : ℝ} (ht : 0 < t) (hW : 0 ≤ W)
    (h : t ^ k * W ≤ B) :
    Real.sqrt W ≤ Real.sqrt B / Real.sqrt (t ^ k) := by
  have htk : (0 : ℝ) < t ^ k := pow_pos ht k
  rw [le_div_iff₀ (Real.sqrt_pos.mpr htk), ← Real.sqrt_mul hW]
  exact Real.sqrt_le_sqrt (by linarith [h])

/-! ### The parabolic inequality for the combination, on the manifold -/

set_option linter.unusedSectionVars false in
/-- **Math.** **The combination obeys a parabolic inequality with constant
reaction.** Differentiating `u = Σ_j a_j t^j w_j` in time, splitting `Δu` by
linearity (`metricLaplacianAt_finsetSum`), substituting the tower, and applying
`shi_reaction_le` gives

`∂_t u ≤ Δ u + (ρ · shiWeightAt c k T + a_0 κ w_0)`,

whose reaction is a constant once `w_0` is bounded. Everything specific to
the cascade has happened by this point; what follows is the affine maximum
principle already proved for `k = 1`. -/
theorem shi_parabolic_inequality
    {g : ℝ → RiemannianMetric I M} {w : ℕ → M → ℝ → ℝ}
    {c kappa rho T : ℝ} {k : ℕ} (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hwderiv : ∀ j x, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hwsmooth : ∀ j, ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun y => w j y t)
    (hkT : T * kappa ≤ 1) (hkappa : 0 ≤ kappa)
    (htower : HasShiTowerOn g w kappa rho k (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      derivWithin (fun s => shiCombination c k w x s) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => shiCombination c k w y t) x
          + (rho * shiWeightAt c k T
              + shiCoeff c k 0 * (kappa * w 0 x t)) := by
  classical
  intro t ht x
  -- 1. the time derivative of the combination, by the product rule at each level
  have hderiv : HasDerivWithinAt (fun s => shiCombination c k w x s)
      (∑ j ∈ Finset.range (k + 1),
        ((j : ℝ) * shiCoeff c k j * t ^ (j - 1) * w j x t
          + shiCoeff c k j * t ^ j * derivWithin (fun s => w j x s) (Icc 0 T) t))
      (Icc 0 T) t := by
    have hlev : ∀ j ∈ Finset.range (k + 1),
        HasDerivWithinAt (fun s : ℝ => shiCoeff c k j * s ^ j * w j x s)
          ((j : ℝ) * shiCoeff c k j * t ^ (j - 1) * w j x t
            + shiCoeff c k j * t ^ j * derivWithin (fun s => w j x s) (Icc 0 T) t)
          (Icc 0 T) t := by
      intro j _
      have hpow : HasDerivWithinAt (fun s : ℝ => shiCoeff c k j * s ^ j)
          (shiCoeff c k j * ((j : ℝ) * t ^ (j - 1))) (Icc 0 T) t :=
        ((hasDerivAt_pow j t).const_mul (shiCoeff c k j)).hasDerivWithinAt
      have hprod := hpow.mul (hwderiv j x t ht)
      have hshape : ((fun s : ℝ => shiCoeff c k j * s ^ j) * fun s => w j x s)
          = fun s : ℝ => shiCoeff c k j * s ^ j * w j x s := rfl
      rw [hshape] at hprod
      have hval : (j : ℝ) * shiCoeff c k j * t ^ (j - 1) * w j x t
            + shiCoeff c k j * t ^ j * derivWithin (fun s => w j x s) (Icc 0 T) t
          = shiCoeff c k j * ((j : ℝ) * t ^ (j - 1)) * w j x t
            + shiCoeff c k j * t ^ j * derivWithin (fun s => w j x s) (Icc 0 T) t := by
        ring
      rw [hval]
      exact hprod
    have hsum := HasDerivWithinAt.sum hlev
    have hfun : (fun s => shiCombination c k w x s)
        = ∑ j ∈ Finset.range (k + 1), fun s : ℝ => shiCoeff c k j * s ^ j * w j x s := by
      funext s
      rw [Finset.sum_apply]
      rfl
    rw [hfun]
    exact hsum
  rw [hderiv.derivWithin (uniqueDiffOn_Icc hT t ht), Finset.sum_add_distrib]
  -- 2. the Laplacian of the combination splits by linearity
  have hlap : metricLaplacianAt (g t) (fun y => shiCombination c k w y t) x
      = ∑ j ∈ Finset.range (k + 1),
          shiCoeff c k j * t ^ j * metricLaplacianAt (g t) (fun y => w j y t) x := by
    simp only [shiCombination]
    have hsm : ∀ j ∈ Finset.range (k + 1),
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => shiCoeff c k j * t ^ j * w j y t) :=
      fun j _ => contMDiff_const.mul (hwsmooth j t ht)
    rw [metricLaplacianAt_finsetSum (g t) (Finset.range (k + 1)) hsm x]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact metricLaplacianAt_const_mul (g t) (shiCoeff c k j * t ^ j)
      (hwsmooth j t ht) x
  rw [hlap]
  -- 3. substitute the tower level by level
  have hsub : ∀ j ∈ Finset.range (k + 1),
      (j : ℝ) * shiCoeff c k j * t ^ (j - 1) * w j x t
          + shiCoeff c k j * t ^ j * derivWithin (fun s => w j x s) (Icc 0 T) t
        ≤ shiCoeff c k j * t ^ j * metricLaplacianAt (g t) (fun y => w j y t) x
          + ((j : ℝ) * shiCoeff c k j * t ^ (j - 1) * w j x t
            + shiCoeff c k j * t ^ j
              * (-2 * w (j + 1) x t + kappa * w j x t + rho)) := by
    intro j hj
    have hjk : j < k + 1 := Finset.mem_range.mp hj
    have htow := htower j hjk t ht x
    have hweight : 0 ≤ shiCoeff c k j * t ^ j := by
      have := (shiCoeff_pos hc k j).le
      have : (0:ℝ) ≤ t ^ j := pow_nonneg ht.1 j
      positivity
    nlinarith [mul_le_mul_of_nonneg_left htow hweight]
  have hstep := Finset.sum_le_sum hsub
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hstep
  -- 4. the reaction collapses to the constant
  have htk : t * kappa ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right ht.2 hkappa) hkT
  have hreact := shi_reaction_le (c := c) (rho := rho) hc k
    (t := t) (kappa := kappa) (T := T) ht.1 ht.2 htk
    (v := fun j => w j x t) (fun j => hwnneg j x t) hrho
  linarith

/-! ### Topping, Theorem 3.3.1 for every `k` -/

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Theorem 3.3.1, maximum-principle content, for every `k`.**
On `[0,T]` with `T ≤ 1/m`, `q ≤ m^2` and `w_0 ≤ m^2`, the tower of evolution
inequalities gives

`t^k |∇^k\Rm|^2 ≤ a_0 m^2 + (ρ · shiWeightAt c k T + a_0 κ m^2) t`,

the affine barrier of the `k = 1` case with the cascade's constants. Every step is
proved: the telescoping cancellation, the parabolic inequality, and the affine
comparison via `le_affineBarrier_of_parabolic_inequality`, i.e. the weak maximum
principle.

`k = 1` recovers `mul_gradRiemannNormSq_le`'s conclusion up to the value of the
constants; the point of this statement is that `k` is arbitrary. -/
theorem mul_pow_le_affineBarrier_of_shiTower
    {g : ℝ → RiemannianMetric I M} {w : ℕ → M → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ} (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hkT : T * kappa ≤ 1) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x, ∀ t ∈ Icc 0 T, w 0 x t ≤ m ^ 2)
    (hwderiv : ∀ j x, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hwsmooth : ∀ j, ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun y => w j y t)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => shiCombination c k w z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (htower : HasShiTowerOn g w kappa rho k (Icc 0 T)) :
    ∀ x t, t ∈ Icc 0 T →
      t ^ k * w k x t ≤
        affineBarrier (shiCoeff c k 0 * m ^ 2)
          (rho * shiWeightAt c k T + shiCoeff c k 0 * (kappa * m ^ 2)) t := by
  classical
  -- the parabolic inequality, with the reaction bounded by the constant
  have hpde : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (fun s => shiCombination c k w x s) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => shiCombination c k w y t) x
          + (rho * shiWeightAt c k T + shiCoeff c k 0 * (kappa * m ^ 2)) := by
    intro t ht x
    have hstep := shi_parabolic_inequality hT hc hrho hwnneg hwderiv hwsmooth
      hkT hkappa htower t ht x
    have hlev : kappa * w 0 x t ≤ kappa * m ^ 2 :=
      mul_le_mul_of_nonneg_left (hw0 x t ht) hkappa
    have hcoeff := (shiCoeff_pos hc k 0).le
    have := mul_le_mul_of_nonneg_left hlev hcoeff
    linarith
  -- the initial datum: only level `0` survives at `t = 0`
  have hzero : ∀ x, shiCombination c k w x 0 ≤ shiCoeff c k 0 * m ^ 2 := by
    intro x
    rw [shiCombination_zero]
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    exact mul_le_mul_of_nonneg_left (hw0 x 0 h0) (shiCoeff_pos hc k 0).le
  have hmain := le_affineBarrier_of_parabolic_inequality (g := g)
    (u := fun x t => shiCombination c k w x t)
    (a := shiCoeff c k 0 * m ^ 2)
    (c := rho * shiWeightAt c k T + shiCoeff c k 0 * (kappa * m ^ 2))
    hT hu hpde hzero
  intro x t ht
  exact le_trans (mul_pow_le_shiCombination hc k ht.1 (fun j => hwnneg j x t))
    (hmain x t ht)

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Theorem 3.3.1 in its displayed form, for every `k`.**

`|∇^k\Rm| ≤ √B / t^{k/2}`   on `(0,T]`, `T ≤ 1/m`,

where `B = a_0 m^2 + (ρ·shiWeightAt c k T + a_0 κ m^2) T` is a constant built from
`c`, `k`, `κ`, `ρ`, `T` and `m` alone. This is the square root of the previous
estimate after dividing by `t^k`.

Two things to be honest about in comparing this to the book.

The constant is not asserted to be `C(n,k) m`: it is `√B`, which carries `T`, `κ`
and `ρ`. Recovering Topping's `CM` shape requires `κ ≲ m` and `ρ ≲ m^3` on
`[0,1/m]`, which is the *content* of the induction on `k` — each level's `κ` and `ρ`
are bounded using the previous levels' conclusions. That induction is not performed
here; what is proved is the single cascade step, uniformly in `k`.

The quantity bounded is `√(w_k)`, and `w_k = |∇^k\Rm|^2` only once the tower
hypothesis is discharged at the geometric quantities. `HasShiTowerOn` is not proved
anywhere in the project. -/
theorem sqrt_le_div_of_shiTower
    {g : ℝ → RiemannianMetric I M} {w : ℕ → M → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ} (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hm : 0 < m) (hkT : T * kappa ≤ 1) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x, ∀ t ∈ Icc 0 T, w 0 x t ≤ m ^ 2)
    (hwderiv : ∀ j x, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hwsmooth : ∀ j, ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun y => w j y t)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => shiCombination c k w z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (htower : HasShiTowerOn g w kappa rho k (Icc 0 T)) :
    ∀ x t, 0 < t → t ≤ T →
      Real.sqrt (w k x t) ≤
        Real.sqrt (affineBarrier (shiCoeff c k 0 * m ^ 2)
            (rho * shiWeightAt c k T + shiCoeff c k 0 * (kappa * m ^ 2)) T)
          / Real.sqrt (t ^ k) := by
  intro x t htpos htT
  have hmain := mul_pow_le_affineBarrier_of_shiTower hT hc hrho hkT hkappa
    hwnneg hw0 hwderiv hwsmooth hu htower x t ⟨htpos.le, htT⟩
  -- the affine barrier is monotone in `t`, so its value at `T` dominates
  have hmono : affineBarrier (shiCoeff c k 0 * m ^ 2)
        (rho * shiWeightAt c k T + shiCoeff c k 0 * (kappa * m ^ 2)) t
      ≤ affineBarrier (shiCoeff c k 0 * m ^ 2)
        (rho * shiWeightAt c k T + shiCoeff c k 0 * (kappa * m ^ 2)) T := by
    have hslope : 0 ≤ rho * shiWeightAt c k T
        + shiCoeff c k 0 * (kappa * m ^ 2) := by
      have h1 : 0 ≤ rho * shiWeightAt c k T := by
        have := (shiWeightAt_pos hc k hT).le
        positivity
      have h2 : 0 ≤ shiCoeff c k 0 * (kappa * m ^ 2) := by
        have := (shiCoeff_pos hc k 0).le
        positivity
      linarith
    simp only [affineBarrier]
    nlinarith [hslope, htT]
  exact sqrt_le_div_of_mul_pow_le htpos (hwnneg k x t) (by linarith)

/-! ### Consistency with the `k = 1` case

The docstrings above claim the cascade specializes to the already-proved `k = 1`
argument. That is a checkable claim, so it is checked: at `k = 1` the coefficients
must be `a_1 = 1` and `a_0 = (2 + c)/2`, and the conclusion must be about
`t^1 · w_1` — the `t·|∇\Rm|^2` of `mul_gradRiemannNormSq_le`.

The `k = 1` coefficient `a_0 = (2+c)/2` is slightly larger than that file's
`α = (1+c)/2`: the cascade leaves `(1+c)` of reaction slack at every level, where
the bespoke `k = 1` argument spends exactly `1 + ct|\Rm|`. Both are valid; the
cascade's is not tight, and this test records that rather than hiding it. -/

set_option linter.unusedSectionVars false in
/-- **Math.** At `k = 1` the top coefficient is `1`. -/
theorem shiCoeff_one_top (c : ℝ) : shiCoeff c 1 1 = 1 := shiCoeff_top c 1

/-- **Math.** At `k = 1` the bottom coefficient is `(2 + c)/2`, not the `(1 + c)/2`
of the bespoke `k = 1` argument: the cascade keeps `(1 + c)` of slack per level and
so is not tight. -/
theorem shiCoeff_one_bot (c : ℝ) : shiCoeff c 1 0 = (2 + c) / 2 := by
  rw [shiCoeff_succ c (by omega : 0 < 1), shiCoeff_one_top]
  push_cast
  ring

/-- **Math.** At `k = 1` the estimate really is about `t · w_1`, i.e. `t|∇\Rm|^2`. -/
example (w : ℕ → M → ℝ → ℝ) (x : M) (t : ℝ) :
    t ^ 1 * w 1 x t = t * w 1 x t := by rw [pow_one]

end Estimate

end Topping

end
