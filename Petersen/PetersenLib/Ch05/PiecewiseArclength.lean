import PetersenLib.Ch05.ArclengthReparametrization

/-!
# Petersen Ch. 5, §5.3 — piecewise arclength reparametrization

Petersen's Proposition on arclength reparametrization
(`prop:pet-ch5-arclength-reparametrization`), full piecewise case: a **regular
piecewise-`C^∞` curve** — one whose closed pieces agree with reference curves
that are `C^∞` on open windows with nonvanishing speed — admits a
reparametrization by arclength, piecewise smooth with unit speed away from
the (finitely many) break times.

* `IsPiecewiseRegularCurve` — the regularity class: a partition
  `a = u₀ ≤ ⋯ ≤ uₙ = b` together with, for each piece, a reference curve `σ`
  that is `C^∞` on an open window around the piece, agrees with `γ` on the
  closed piece, and has nonvanishing speed there.  (Petersen's "regular
  curve", p. 194: each smooth piece has never-vanishing velocity; the open
  window packages the one-sided smoothness of the closed piece.)
* `curveLength_congr_Icc` — the length only reads the curve on the interval.
* `isPiecewiseSmoothCurve_of_forall_contMDiffOn` — a partition of closed
  smooth pieces glues to a piecewise smooth curve (continuity included).
* `curveLength_eq_of_unitSpeed_offFinset` — a piecewise smooth curve with
  unit speed away from a finite set is parametrized by arclength.
* `piecewiseRegularCurve_arclengthReparametrization` — Petersen's
  proposition: the arclength function of a piecewise regular curve admits a
  piecewise smooth inverse `ψ`, and `γ ∘ ψ : [0, L(γ)] → M` runs from `γ a`
  to `γ b` with unit speed off the break set and `L(γ∘ψ)|_0^s = s`.  Proven
  by induction on the pieces: the smooth case
  (`regularCurve_arclengthReparametrization`) handles each piece, and the
  per-piece inverses glue along the accumulated lengths.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff Interval

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Length only reads the curve on the interval -/

/-- **Math.** The length functional only reads the curve on the interval: two
curves agreeing on `[a, b]` have equal lengths over any subinterval.  The
speeds agree at interior times (the squared speed only depends on the germ),
and the two endpoints form a null set. -/
theorem curveLength_congr_Icc (g : RiemannianMetric I M) {γ σ : ℝ → M} {a b : ℝ}
    (h : EqOn γ σ (Icc a b)) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    curveLength (I := I) g γ s t = curveLength (I := I) g σ s t := by
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : volume ({min s t, max s t} : Set ℝ) = 0 :=
    (Set.toFinite _).measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hxI
  rw [Set.uIoc, Set.mem_Ioc] at hxI
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  have hxIoo : x ∈ Ioo (min s t) (max s t) := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.2⟩
  have hxab : x ∈ Ioo a b := by
    constructor
    · exact lt_of_le_of_lt (le_min hs.1 ht.1) hxIoo.1
    · exact lt_of_lt_of_le hxIoo.2 (max_le hs.2 ht.2)
  have hgerm : γ =ᶠ[𝓝 x] σ := by
    filter_upwards [isOpen_Ioo.mem_nhds hxab] with y hy
    exact h ⟨hy.1.le, hy.2.le⟩
  rw [curveSpeedSq_congr_nhds (I := I) g hgerm]

/-! ## Assembling piecewise smooth curves from closed smooth pieces -/

/-- **Math.** A curve that is `C^∞` on each closed piece of a partition is
piecewise smooth on the whole interval: the continuity glue along adjacent
closed pieces is automatic. -/
theorem isPiecewiseSmoothCurve_of_forall_contMDiffOn {γ : ℝ → M} {n : ℕ}
    {u : Fin (n + 1) → ℝ} (hmono : Monotone u)
    (hsm : ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u i.castSucc) (u i.succ))) :
    IsPiecewiseSmoothCurve (I := I) γ (u 0) (u (Fin.last n)) := by
  have key : ∀ k : ℕ, ∀ hk : k < n + 1, ContinuousOn γ (Icc (u 0) (u ⟨k, hk⟩)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, Set.Icc_self]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact continuousWithinAt_singleton
    | succ k ih =>
      intro hk
      have hkn : k < n + 1 := by omega
      have hkn' : k < n := by omega
      have hcast : (⟨k, hkn⟩ : Fin (n + 1)) = (⟨k, hkn'⟩ : Fin n).castSucc := rfl
      have hsucc : (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkn'⟩ : Fin n).succ := rfl
      have h0k : u 0 ≤ u ⟨k, hkn⟩ := hmono (Fin.zero_le _)
      have hkk1 : u ⟨k, hkn⟩ ≤ u ⟨k + 1, hk⟩ := by
        rw [hcast, hsucc]
        exact hmono Fin.castSucc_lt_succ.le
      rw [← Set.Icc_union_Icc_eq_Icc h0k hkk1]
      refine (ih hkn).union_of_isClosed ?_ isClosed_Icc isClosed_Icc
      have := (hsm ⟨k, hkn'⟩).continuousOn
      rwa [← hcast, ← hsucc] at this
  have hlast := key n n.lt_succ_self
  exact ⟨hlast, n, u, hmono, rfl, rfl, hsm⟩

/-! ## Piecewise regular curves -/

/-- **Math.** Petersen Ch. 5, §5.3 (p. 194): a **regular piecewise-`C^∞`
curve** on `[a, b]`: a partition `a = u₀ ≤ ⋯ ≤ uₙ = b` such that on each
closed piece `[uᵢ, uᵢ₊₁]` the curve agrees with a reference curve `σ` that is
`C^∞` on an open window around the piece and has **nonvanishing speed** on
the piece.  (The open window packages the one-sided derivatives of the closed
piece; every smooth regular curve and every chart-line polygon is of this
form.) -/
def IsPiecewiseRegularCurve (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∃ (n : ℕ) (u : Fin (n + 1) → ℝ), Monotone u ∧ u 0 = a ∧ u (Fin.last n) = b ∧
    ∀ i : Fin n, ∃ (σ : ℝ → M) (J : Set ℝ), IsOpen J ∧
      Icc (u i.castSucc) (u i.succ) ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ J ∧ EqOn γ σ (Icc (u i.castSucc) (u i.succ)) ∧
      ∀ t ∈ Icc (u i.castSucc) (u i.succ), curveSpeedSq (I := I) g σ t ≠ 0

/-- **Math.** A piecewise regular curve is piecewise smooth: each closed piece
inherits the smoothness of its reference curve. -/
theorem IsPiecewiseRegularCurve.isPiecewiseSmoothCurve {g : RiemannianMetric I M}
    {γ : ℝ → M} {a b : ℝ} (hγ : IsPiecewiseRegularCurve (I := I) g γ a b) :
    IsPiecewiseSmoothCurve (I := I) γ a b := by
  obtain ⟨n, u, hmono, hu0, hun, hpieces⟩ := hγ
  subst hu0; subst hun
  refine isPiecewiseSmoothCurve_of_forall_contMDiffOn (I := I) hmono fun i => ?_
  obtain ⟨σ, J, hJo, hsub, hσ, heq, -⟩ := hpieces i
  exact ((hσ.mono hsub).congr fun t ht => heq ht)

/-- **Math.** A piecewise regular curve runs from left to right:
`a ≤ b`. -/
theorem IsPiecewiseRegularCurve.le {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseRegularCurve (I := I) g γ a b) : a ≤ b := by
  obtain ⟨n, u, hmono, hu0, hun, -⟩ := hγ
  rw [← hu0, ← hun]
  exact hmono (Fin.zero_le _)

/-! ## Constant-speed curves -/

/-- **Math.** Petersen Ch. 5, §5.3: a curve is **parametrized proportionally
to arc length** (has *constant speed*) on `[a, b]` if its speed equals a
constant `k ≥ 0` away from finitely many times (the break times of the
piecewise parametrization, where the two-sided velocity need not exist). -/
def IsConstantSpeedCurve (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∃ k : ℝ, 0 ≤ k ∧ ∃ T : Finset ℝ,
    ∀ t ∈ Icc a b \ (T : Set ℝ), curveSpeedSq (I := I) g γ t = k ^ 2

/-- **Math.** A curve with unit speed away from a finite exceptional set is
**parametrized by arclength**: `L(γ)|_0^s = s` for all `s ∈ [0, S]`.  The
speed integrand equals `1` almost everywhere on `[0, s]`. -/
theorem curveLength_eq_of_unitSpeed_offFinset (g : RiemannianMetric I M)
    {γ : ℝ → M} {S : ℝ} (T : Finset ℝ)
    (hunit : ∀ s ∈ Icc (0 : ℝ) S \ (T : Set ℝ), curveSpeedSq (I := I) g γ s = 1) :
    ∀ s ∈ Icc (0 : ℝ) S, curveLength (I := I) g γ 0 s = s := by
  intro s hs
  have hcongr : ∀ᵐ x ∂volume, x ∈ Ι (0 : ℝ) s →
      Real.sqrt (curveSpeedSq (I := I) g γ x) = 1 := by
    have hnull : volume (T : Set ℝ) = 0 := (T.finite_toSet).measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hxI
    rw [Set.uIoc_of_le hs.1, Set.mem_Ioc] at hxI
    have hxIcc : x ∈ Icc (0 : ℝ) S \ (T : Set ℝ) :=
      ⟨⟨hxI.1.le, hxI.2.trans hs.2⟩, hx⟩
    rw [hunit x hxIcc, Real.sqrt_one]
  calc curveLength (I := I) g γ 0 s
      = ∫ x in (0 : ℝ)..s, (1 : ℝ) := intervalIntegral.integral_congr_ae hcongr
    _ = s := by simp

/-! ## The piecewise arclength reparametrization -/

section Boundaryless

variable [I.Boundaryless]

/-- The inductive engine for
`piecewiseRegularCurve_arclengthReparametrization`: induction on the number
of pieces, gluing the inverse of the last (smooth, regular) piece onto the
inverse produced for the earlier pieces at the accumulated length `L₁`. -/
private theorem arclength_glue_aux (g : RiemannianMetric I M) (γ : ℝ → M) :
    ∀ (n : ℕ) (u : Fin (n + 1) → ℝ), Monotone u →
    (∀ i : Fin n, ∃ (σ : ℝ → M) (J : Set ℝ), IsOpen J ∧
      Icc (u i.castSucc) (u i.succ) ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ J ∧ EqOn γ σ (Icc (u i.castSucc) (u i.succ)) ∧
      ∀ t ∈ Icc (u i.castSucc) (u i.succ), curveSpeedSq (I := I) g σ t ≠ 0) →
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc (u 0) (u (Fin.last n)),
        ψ (curveLength (I := I) g γ (u 0) t) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ (u 0) (u (Fin.last n))),
        ψ s ∈ Icc (u 0) (u (Fin.last n))) ∧
      IsPiecewiseSmoothCurve (I := I) (γ ∘ ψ) 0
        (curveLength (I := I) g γ (u 0) (u (Fin.last n))) ∧
      (γ ∘ ψ) 0 = γ (u 0) ∧
      (γ ∘ ψ) (curveLength (I := I) g γ (u 0) (u (Fin.last n))) = γ (u (Fin.last n)) ∧
      ∃ T : Finset ℝ,
        ∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ (u 0) (u (Fin.last n))) \ (T : Set ℝ),
          curveSpeedSq (I := I) g (γ ∘ ψ) s = 1 := by
  intro n
  induction n with
  | zero =>
    intro u _ _
    have hlast : Fin.last 0 = (0 : Fin 1) := rfl
    rw [hlast, curveLength_self]
    refine ⟨fun _ => u 0, ?_, ?_, ?_, rfl, rfl, {0}, ?_⟩
    · intro t ht
      exact (le_antisymm ht.2 ht.1).symm ▸ rfl
    · intro s _
      exact ⟨le_rfl, le_rfl⟩
    · exact isPiecewiseSmoothCurve_const (I := I) (γ (u 0)) le_rfl
    · intro s hs
      exfalso
      have h0 : s = 0 := le_antisymm hs.1.2 hs.1.1
      exact hs.2 (by simp [h0])
  | succ n ih =>
    intro u hmono hpieces
    -- the split point `m` (second-to-last partition point) and endpoint `b`
    set m : ℝ := u (Fin.last n).castSucc with hm_def
    set b : ℝ := u (Fin.last (n + 1)) with hb_def
    have hmb : m ≤ b := by
      rw [hm_def, hb_def, ← Fin.succ_last]
      exact hmono Fin.castSucc_lt_succ.le
    have h0m : u 0 ≤ m := hmono (Fin.zero_le _)
    -- the restricted partition for the induction hypothesis
    set u' : Fin (n + 1) → ℝ := u ∘ Fin.castSucc with hu'_def
    have hmono' : Monotone u' := hmono.comp fun i j hij => Fin.castSucc_le_castSucc_iff.mpr hij
    have hu'0 : u' 0 = u 0 := by simp [hu'_def]
    have hu'last : u' (Fin.last n) = m := rfl
    have hpieces' : ∀ i : Fin n, ∃ (σ : ℝ → M) (J : Set ℝ), IsOpen J ∧
        Icc (u' i.castSucc) (u' i.succ) ⊆ J ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ J ∧ EqOn γ σ (Icc (u' i.castSucc) (u' i.succ)) ∧
        ∀ t ∈ Icc (u' i.castSucc) (u' i.succ), curveSpeedSq (I := I) g σ t ≠ 0 := by
      intro i
      have h1 : u' i.castSucc = u i.castSucc.castSucc := rfl
      have h2 : u' i.succ = u i.castSucc.succ := by
        show u i.succ.castSucc = u i.castSucc.succ
        rw [Fin.succ_castSucc]
      rw [h1, h2]
      exact hpieces i.castSucc
    obtain ⟨ψ₁, hψ₁left, hψ₁map, hψ₁pw, hψ₁0, hψ₁end, T₁, hψ₁unit⟩ :=
      ih u' hmono' hpieces'
    rw [hu'0, hu'last] at hψ₁left hψ₁map hψ₁pw hψ₁end hψ₁unit
    rw [hu'0] at hψ₁0
    -- the last piece: smooth reference curve `σ` on an open window
    obtain ⟨σ, J, hJo, hsub, hσ, heq, hreg⟩ := hpieces (Fin.last n)
    have hsub' : Icc m b ⊆ J := by
      rw [hm_def, hb_def, ← Fin.succ_last]; exact hsub
    have heq' : EqOn γ σ (Icc m b) := by
      rw [hm_def, hb_def, ← Fin.succ_last]; exact heq
    have hreg' : ∀ t ∈ Icc m b, curveSpeedSq (I := I) g σ t ≠ 0 := by
      rw [hm_def, hb_def, ← Fin.succ_last]; exact hreg
    obtain ⟨ψ₂, hψ₂left, hψ₂map, hψ₂smooth, hψ₂0, hψ₂end, hψ₂unit, hψ₂arc⟩ :=
      regularCurve_arclengthReparametrization (I := I) g hJo hσ hmb hsub' hreg'
    -- lengths: `L₁` on the earlier pieces, `ℓ` on the last piece
    set L₁ : ℝ := curveLength (I := I) g γ (u 0) m with hL₁_def
    set ℓ : ℝ := curveLength (I := I) g σ m b with hℓ_def
    have hlen_eq : ∀ t ∈ Icc m b,
        curveLength (I := I) g γ m t = curveLength (I := I) g σ m t := fun t ht =>
      curveLength_congr_Icc (I := I) g heq' (left_mem_Icc.mpr hmb) ht
    -- the whole curve is piecewise smooth, hence has integrable speed
    have hpsγ : IsPiecewiseSmoothCurve (I := I) γ (u 0) b := by
      refine isPiecewiseSmoothCurve_of_forall_contMDiffOn (I := I) hmono fun i => ?_
      obtain ⟨σi, Ji, hJio, hsubi, hσi, heqi, -⟩ := hpieces i
      exact ((hσi.mono hsubi).congr fun t ht => heqi ht)
    have hLsplit : curveLength (I := I) g γ (u 0) b = L₁ + ℓ := by
      rw [hL₁_def, hℓ_def, ← hlen_eq b (right_mem_Icc.mpr hmb)]
      exact hpsγ.curveLength_add (I := I) g h0m hmb
    set L : ℝ := curveLength (I := I) g γ (u 0) b with hL_def
    have hL₁nonneg : 0 ≤ L₁ := curveLength_nonneg (I := I) g γ h0m
    have hℓnonneg : 0 ≤ ℓ := by
      rw [hℓ_def, ← hlen_eq b (right_mem_Icc.mpr hmb)]
      exact curveLength_nonneg (I := I) g γ hmb
    -- positivity of partial lengths along the regular last piece
    have hφ₂int : ∀ t ∈ Icc m b, IntervalIntegrable
        (fun τ => Real.sqrt (curveSpeedSq (I := I) g σ τ)) volume m t := fun t ht =>
      ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g ht.1
        (hσ.mono ((Icc_subset_Icc le_rfl ht.2).trans hsub'))
    have hφ₂pos : ∀ t ∈ Ioc m b, 0 < curveLength (I := I) g σ m t := by
      intro t ht
      refine intervalIntegral.intervalIntegral_pos_of_pos_on
        (hφ₂int t ⟨ht.1.le, ht.2⟩) ?_ ht.1
      intro τ hτ
      have hτIcc : τ ∈ Icc m b := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
      exact Real.sqrt_pos.mpr (lt_of_le_of_ne (curveSpeedSq_nonneg (I := I) g σ τ)
        (Ne.symm (hreg' τ hτIcc)))
    have hφ₂le : ∀ t ∈ Icc m b, curveLength (I := I) g σ m t ≤ ℓ := by
      intro t ht
      have hadd : curveLength (I := I) g σ m b =
          curveLength (I := I) g σ m t + curveLength (I := I) g σ t b :=
        curveLength_additive (I := I) g σ (hφ₂int t ht)
          (ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g ht.2
            (hσ.mono ((Icc_subset_Icc ht.1 le_rfl).trans hsub')))
      have := curveLength_nonneg (I := I) g σ ht.2
      rw [hℓ_def, hadd]
      linarith
    -- the arclength function of `γ` on `[u 0, b]`
    have hInt := hpsγ.intervalIntegrable_sqrt_curveSpeedSq (I := I) g
    have hφadd : ∀ t ∈ Icc (u 0) b, curveLength (I := I) g γ (u 0) t
        = curveLength (I := I) g γ (u 0) (min t m) + curveLength (I := I) g γ (min t m) t := by
      intro t ht
      refine curveLength_additive (I := I) g γ (hInt.mono_set ?_) (hInt.mono_set ?_)
      · rw [uIcc_of_le (le_min_iff.mpr ⟨ht.1, h0m⟩), uIcc_of_le (h0m.trans hmb)]
        exact Icc_subset_Icc le_rfl ((min_le_right t m).trans hmb)
      · rw [uIcc_of_le (min_le_left t m), uIcc_of_le (h0m.trans hmb)]
        exact Icc_subset_Icc (le_min_iff.mpr ⟨ht.1, h0m⟩) ht.2
    have hφ_le_L₁ : ∀ t ∈ Icc (u 0) m, curveLength (I := I) g γ (u 0) t ≤ L₁ := by
      intro t ht
      have hadd : L₁ = curveLength (I := I) g γ (u 0) t + curveLength (I := I) g γ t m := by
        rw [hL₁_def]
        refine curveLength_additive (I := I) g γ (hInt.mono_set ?_) (hInt.mono_set ?_)
        · rw [uIcc_of_le ht.1, uIcc_of_le (h0m.trans hmb)]
          exact Icc_subset_Icc le_rfl (ht.2.trans hmb)
        · rw [uIcc_of_le ht.2, uIcc_of_le (h0m.trans hmb)]
          exact Icc_subset_Icc ht.1 hmb
      have : 0 ≤ curveLength (I := I) g γ t m := curveLength_nonneg (I := I) g γ ht.2
      linarith
    -- the glued inverse
    set ψ : ℝ → ℝ := fun s => if s ≤ L₁ then ψ₁ s else ψ₂ (s - L₁) with hψ_def
    -- membership of the shifted argument for branch-2 inputs
    have hbranch2 : ∀ s ∈ Icc (0 : ℝ) L, ¬s ≤ L₁ → s - L₁ ∈ Icc (0 : ℝ) ℓ := by
      intro s hs hns
      push_neg at hns
      constructor
      · linarith
      · have := hs.2
        rw [hLsplit] at this
        linarith
    refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- (1) left inverse
    · intro t ht
      rcases le_or_gt t m with htm | htm
      · have hφt : curveLength (I := I) g γ (u 0) t ≤ L₁ :=
          hφ_le_L₁ t ⟨ht.1, htm⟩
        rw [hψ_def]
        simp only [if_pos hφt]
        exact hψ₁left t ⟨ht.1, htm⟩
      · have hadd : curveLength (I := I) g γ (u 0) t
            = L₁ + curveLength (I := I) g γ m t := by
          have := hφadd t ht
          rwa [min_eq_right htm.le] at this
        have hpos : 0 < curveLength (I := I) g γ m t := by
          rw [hlen_eq t ⟨htm.le, ht.2⟩]
          exact hφ₂pos t ⟨htm, ht.2⟩
        rw [hψ_def]
        simp only [if_neg (by linarith : ¬curveLength (I := I) g γ (u 0) t ≤ L₁)]
        rw [hadd, add_sub_cancel_left, hlen_eq t ⟨htm.le, ht.2⟩]
        exact hψ₂left t ⟨htm.le, ht.2⟩
    -- (2) the inverse maps `[0, L]` into `[u 0, b]`
    · intro s hs
      by_cases hsL₁ : s ≤ L₁
      · have := hψ₁map s ⟨hs.1, hsL₁⟩
        rw [hψ_def]
        simp only [if_pos hsL₁]
        exact ⟨this.1, this.2.trans hmb⟩
      · have := hψ₂map (s - L₁) (hbranch2 s hs hsL₁)
        rw [hψ_def]
        simp only [if_neg hsL₁]
        exact ⟨h0m.trans this.1, this.2⟩
    -- (3) piecewise smoothness of the reparametrized curve
    · have hpart1 : IsPiecewiseSmoothCurve (I := I) (γ ∘ ψ) 0 L₁ := by
        refine hψ₁pw.congr fun s hs => ?_
        show γ (ψ s) = γ (ψ₁ s)
        rw [hψ_def]
        simp only [if_pos hs.2]
      have hpart2 : IsPiecewiseSmoothCurve (I := I) (γ ∘ ψ) L₁ L := by
        have hδsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => (σ ∘ ψ₂) (s - L₁)) (Icc L₁ L) := by
          have haff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s - L₁) (Icc L₁ L) :=
            ((contDiff_id.sub contDiff_const).contMDiff).contMDiffOn
          refine hψ₂smooth.comp haff ?_
          intro s hs
          rw [hLsplit] at hs
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        refine (ContMDiffOn.isPiecewiseSmoothCurve (I := I) ?_ hδsm).congr ?_
        · rw [hLsplit]; linarith
        · intro s hs
          show γ (ψ s) = (σ ∘ ψ₂) (s - L₁)
          rcases eq_or_lt_of_le hs.1 with hsL₁ | hsL₁
          · rw [hψ_def]
            simp only [if_pos hsL₁.symm.le]
            rw [← hsL₁, sub_self]
            calc γ (ψ₁ L₁) = γ m := hψ₁end
              _ = σ m := heq' (left_mem_Icc.mpr hmb)
              _ = (σ ∘ ψ₂) 0 := hψ₂0.symm
          · have hns : ¬s ≤ L₁ := not_le.mpr hsL₁
            rw [hψ_def]
            simp only [if_neg hns]
            show γ (ψ₂ (s - L₁)) = σ (ψ₂ (s - L₁))
            exact heq' (hψ₂map (s - L₁)
              (hbranch2 s ⟨hL₁nonneg.trans hs.1, hs.2⟩ hns))
      exact hpart1.trans hpart2
    -- (4) initial point
    · show γ (ψ 0) = γ (u 0)
      rw [hψ_def]
      simp only [if_pos hL₁nonneg]
      exact hψ₁0
    -- (5) terminal point
    · show γ (ψ L) = γ b
      rcases eq_or_lt_of_le hℓnonneg with hℓ0 | hℓpos
      · have hLL₁ : L = L₁ := by rw [hLsplit, ← hℓ0, add_zero]
        have hmb' : m = b := by
          by_contra hne
          have hmltb : m < b := lt_of_le_of_ne hmb hne
          have := hφ₂pos b ⟨hmltb, le_rfl⟩
          rw [← hℓ_def, ← hℓ0] at this
          exact lt_irrefl 0 this
        rw [hψ_def]
        simp only [hLL₁, if_pos le_rfl]
        calc γ (ψ₁ L₁) = γ m := hψ₁end
          _ = γ b := by rw [hmb']
      · have hns : ¬L ≤ L₁ := by rw [hLsplit]; linarith
        rw [hψ_def]
        simp only [if_neg hns]
        have hLsub : L - L₁ = ℓ := by rw [hLsplit]; ring
        rw [hLsub]
        calc γ (ψ₂ ℓ) = σ (ψ₂ ℓ) :=
              heq' (hψ₂map ℓ ⟨hℓnonneg, le_rfl⟩)
          _ = σ b := hψ₂end
          _ = γ b := (heq' (right_mem_Icc.mpr hmb)).symm
    -- (6) unit speed away from the break set
    · refine ⟨T₁ ∪ {L₁, L}, ?_⟩
      intro s hs
      obtain ⟨hsIcc, hsT⟩ := hs
      rw [Finset.coe_union, Set.mem_union, not_or] at hsT
      obtain ⟨hsT₁, hsbrk⟩ := hsT
      have hsL₁ : s ≠ L₁ := by
        intro h; exact hsbrk (by simp [h])
      have hsL : s ≠ L := by
        intro h; exact hsbrk (by simp [h])
      rcases lt_or_gt_of_ne hsL₁ with hlt | hgt
      · -- germ agreement with `γ ∘ ψ₁` below `L₁`
        have hgerm : (γ ∘ ψ) =ᶠ[𝓝 s] (γ ∘ ψ₁) := by
          filter_upwards [isOpen_Iio.mem_nhds (show s ∈ Iio L₁ from hlt)] with r hr
          show γ (ψ r) = γ (ψ₁ r)
          rw [hψ_def]
          simp only [if_pos (le_of_lt (Set.mem_Iio.mp hr))]
        rw [curveSpeedSq_congr_nhds (I := I) g hgerm]
        exact hψ₁unit s ⟨⟨hsIcc.1, hlt.le⟩, hsT₁⟩
      · -- germ agreement with the shifted last piece above `L₁`
        have hsltL : s < L := lt_of_le_of_ne hsIcc.2 hsL
        have hgerm : (γ ∘ ψ) =ᶠ[𝓝 s] (fun r => (σ ∘ ψ₂) (1 * r + -L₁)) := by
          filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Ioo L₁ L from ⟨hgt, hsltL⟩)]
            with r hr
          show γ (ψ r) = (σ ∘ ψ₂) (1 * r + -L₁)
          have hns : ¬r ≤ L₁ := not_le.mpr hr.1
          rw [hψ_def]
          simp only [if_neg hns]
          have hr' : r - L₁ ∈ Icc (0 : ℝ) ℓ :=
            hbranch2 r ⟨(le_trans hL₁nonneg hr.1.le), hr.2.le⟩ hns
          have : γ (ψ₂ (r - L₁)) = σ (ψ₂ (r - L₁)) := heq' (hψ₂map (r - L₁) hr')
          rw [this]
          have harg : 1 * r + -L₁ = r - L₁ := by ring
          rw [harg]
          rfl
        rw [curveSpeedSq_congr_nhds (I := I) g hgerm,
          curveSpeedSq_comp_mul_add (I := I) g (σ ∘ ψ₂) 1 (-L₁) s]
        have hmem : 1 * s + -L₁ ∈ Icc (0 : ℝ) ℓ := by
          have := hbranch2 s hsIcc (not_le.mpr hgt)
          simpa using this
        rw [hψ₂unit _ hmem]
        norm_num

/-- **Math.** Petersen Ch. 5, §5.3
(`prop:pet-ch5-arclength-reparametrization`): **arclength reparametrization
of regular curves**, piecewise case.  A regular piecewise-`C^∞` curve
`γ : [a, b] → M` (nonvanishing velocity on each piece) admits a
reparametrization by arclength: the arclength function `φ(t) = L(γ)|_a^t`
admits an inverse `ψ` mapping `[0, L(γ)]` into `[a, b]`, and the curve
`γ ∘ ψ : [0, L(γ)] → M` is piecewise smooth, runs from `γ a` to `γ b`, has
**unit speed** away from the finitely many break times, and is **parametrized
by arclength**: `L(γ ∘ ψ)|_0^s = s`.

Petersen p. 194: on each smooth piece `φ' = |γ̇| > 0`, so `φ` restricted to a
piece is invertible with smooth inverse
(`regularCurve_arclengthReparametrization`); the per-piece inverses glue
along the accumulated lengths since `φ` is continuous and strictly increasing
across pieces. -/
theorem piecewiseRegularCurve_arclengthReparametrization (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} (hγ : IsPiecewiseRegularCurve (I := I) g γ a b) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a b, ψ (curveLength (I := I) g γ a t) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b), ψ s ∈ Icc a b) ∧
      IsPiecewiseSmoothCurve (I := I) (γ ∘ ψ) 0 (curveLength (I := I) g γ a b) ∧
      (γ ∘ ψ) 0 = γ a ∧ (γ ∘ ψ) (curveLength (I := I) g γ a b) = γ b ∧
      (∃ T : Finset ℝ,
        ∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b) \ (T : Set ℝ),
          curveSpeedSq (I := I) g (γ ∘ ψ) s = 1) ∧
      ∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b),
        curveLength (I := I) g (γ ∘ ψ) 0 s = s := by
  obtain ⟨n, u, hmono, hu0, hun, hpieces⟩ := hγ
  subst hu0; subst hun
  obtain ⟨ψ, h1, h2, h3, h4, h5, T, h6⟩ := arclength_glue_aux (I := I) g γ n u hmono hpieces
  exact ⟨ψ, h1, h2, h3, h4, h5, ⟨T, h6⟩,
    curveLength_eq_of_unitSpeed_offFinset (I := I) g T h6⟩

end Boundaryless

end PetersenLib
