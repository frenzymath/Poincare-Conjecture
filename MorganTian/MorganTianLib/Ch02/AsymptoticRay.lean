import MorganTianLib.Ch02.GeodesicLimits
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Poincaré Ch. 2, §2.1 — Asymptotic rays and their Busemann values

Given a minimizing geodesic ray `lam` in a metric space `M` and a point `x ∈ M`, a
minimizing ray `μ` with `μ 0 = x` is **asymptotic to `lam`** if it is a limit — uniform on
compact subsets of `[0, ∞)` — of unit-speed minimizing segments from `x` to points
`lam (t n)` with `t n → ∞` (`IsAsymptoticRay`). We prove the three assertions of blueprint
`lem:asymptotic-ray`:

* `exists_isAsymptoticRay`: in a proper metric space with minimizing segments, every point
  `x` is the origin of at least one ray asymptotic to `lam` (limits of minimizing
  geodesics, applied to the segments from `x` to `lam n`);
* `IsAsymptoticRay.busemann_apply`: along any asymptotic ray the Busemann function of
  `lam` decreases at unit rate, `B_lam (μ s) = B_lam (μ 0) - s` for all `s ≥ 0`;
* `IsAsymptoticRay.busemann_le`: consequently `B_lam y ≤ B_lam (μ 0) - t + d(y, μ t)` for
  every `y ∈ M` and `t ≥ 0`.

## Design notes

* As everywhere in this chapter, rays and segments are total functions `ℝ → M` constrained
  only on their windows (`[0, ∞)` resp. `[0, d(x, lam (t n))]`); values outside are junk.
* The key computation behind `IsAsymptoticRay.busemann_apply` is the *exact* identity
  `B_{lam, t n}(σ n s) = B_{lam, t n}(μ 0) - s` for the approximating segments `σ n`
  whenever `s ≤ d(μ 0, lam (t n))`: the point `σ n s` lies on a minimizing segment from
  `μ 0` to `lam (t n)`, so its distance to `lam (t n)` is exactly `d(μ 0, lam (t n)) - s`.
  Letting `n → ∞` and using the antitonicity of `t ↦ B_{lam, t}` gives the inequality
  `B_lam (μ s) ≤ B_lam (μ 0) - s`; the reverse inequality is just the `1`-Lipschitz bound
  for `B_lam` along the unit-speed ray `μ`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.1
(blueprint `lem:asymptotic-ray`).
-/

open Filter Topology Metric Set

namespace MorganTianLib

variable {M : Type*} [MetricSpace M]

/-- `μ` is a **ray asymptotic to `lam`** (blueprint definition inside
`lem:asymptotic-ray`): `μ` is a unit-speed minimizing geodesic ray, and there are times
`t n → ∞` together with unit-speed minimizing segments `σ n` from `μ 0` to `lam (t n)`
(parameterized by arclength on `[0, d(μ 0, lam (t n))]`) converging to `μ` uniformly on
compact subsets of `[0, ∞)`. -/
def IsAsymptoticRay (lam μ : ℝ → M) : Prop :=
  IsGeodesicRay μ ∧
  ∃ (t : ℕ → ℝ) (σ : ℕ → ℝ → M),
    Filter.Tendsto t Filter.atTop Filter.atTop ∧
    (∀ n, σ n 0 = μ 0) ∧
    (∀ n, σ n (dist (μ 0) (lam (t n))) = lam (t n)) ∧
    (∀ n, IsMinGeodesicOn (σ n) (Set.Icc 0 (dist (μ 0) (lam (t n))))) ∧
    TendstoLocallyUniformlyOn σ μ Filter.atTop (Set.Ici 0)

/-- **Existence of asymptotic rays** (blueprint `lem:asymptotic-ray`, part 1): in a proper
metric space in which any two points are joined by a minimizing segment, every point `x` is
the origin of at least one ray asymptotic to a given minimizing geodesic ray `lam`. The ray
is produced by `exists_isMinGeodesicOn_tendstoLocallyUniformlyOn` from the minimizing
segments joining `x` to the points `lam n`, `n ∈ ℕ`, whose windows `[0, d(x, lam n)]`
exhaust `[0, ∞)` since `d(x, lam n) ≥ n - d(x, lam 0)`. -/
theorem exists_isAsymptoticRay [ProperSpace M] (hseg : HasMinSegments M)
    {lam : ℝ → M} (hlam : IsGeodesicRay lam) (x : M) :
    ∃ μ : ℝ → M, IsAsymptoticRay lam μ ∧ μ 0 = x := by
  classical
  -- minimizing segments from `x` to `lam n`
  choose σ hσ0 hσd hσgeo using fun n : ℕ => hseg x (lam n)
  -- the segment windows `[0, d(x, lam n)]` exhaust `[0, ∞)`
  have hexh : ∀ s ∈ Set.Ici (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      s ∈ Set.Icc 0 (dist x (lam n)) := by
    intro s hs
    filter_upwards [eventually_ge_atTop ⌈s + dist (lam 0) x⌉₊] with n hn
    refine Set.mem_Icc.mpr ⟨hs, ?_⟩
    have h0n : dist (lam 0) (lam (n : ℝ)) = (n : ℝ) := by
      have h := hlam le_rfl (Nat.cast_nonneg n)
      rwa [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)] at h
    have htri : dist (lam 0) (lam (n : ℝ)) ≤ dist (lam 0) x + dist x (lam (n : ℝ)) :=
      dist_triangle _ _ _
    rw [h0n] at htri
    have hceil : s + dist (lam 0) x ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    linarith
  have h0In : ∀ n : ℕ, (0 : ℝ) ∈ Set.Icc 0 (dist x (lam n)) :=
    fun _ => Set.mem_Icc.mpr ⟨le_refl 0, dist_nonneg⟩
  have hanch : ∀ n : ℕ, σ n 0 ∈ ({x} : Set M) := fun n => by
    rw [hσ0 n]; exact Set.mem_singleton x
  obtain ⟨γ, hγgeo, hγ0, φ, hφ, hφconv⟩ :=
    exists_isMinGeodesicOn_tendstoLocallyUniformlyOn isClosed_Ici Set.ordConnected_Ici
      Set.self_mem_Ici hσgeo (fun _ => Set.ordConnected_Icc) h0In hexh
      isCompact_singleton hanch
  have hγ0x : γ 0 = x := Set.mem_singleton_iff.mp hγ0
  refine ⟨γ, ⟨isGeodesicRay_iff_isMinGeodesicOn.mpr hγgeo,
    (fun m => ((φ m : ℕ) : ℝ)), (fun m => σ (φ m)), ?_, ?_, ?_, ?_, hφconv⟩, hγ0x⟩
  · exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  · intro m
    simp only [hγ0x]
    exact hσ0 (φ m)
  · intro m
    simp only [hγ0x]
    exact hσd (φ m)
  · intro m
    simp only [hγ0x]
    exact hσgeo (φ m)

/-- **Busemann values along an asymptotic ray** (blueprint `lem:asymptotic-ray`, part 2):
if `μ` is asymptotic to `lam` then `B_lam (μ s) = B_lam (μ 0) - s` for all `s ≥ 0`.

For the `≤` direction, the approximating segments give the exact identity
`B_{lam, t n}(σ n s) = B_{lam, t n}(μ 0) - s` once `s ≤ d(μ 0, lam (t n))`; combining it
with `σ n s → μ s`, the antitonicity of `t ↦ B_{lam, t}(μ 0)` and its convergence to
`B_lam (μ 0)` yields `B_lam (μ s) ≤ B_lam (μ 0) - s + ε` for every `ε > 0`. The `≥`
direction is the `1`-Lipschitz bound `B_lam (μ 0) - B_lam (μ s) ≤ d(μ 0, μ s) = s`. -/
theorem IsAsymptoticRay.busemann_apply {lam μ : ℝ → M} (hlam : IsGeodesicRay lam)
    (h : IsAsymptoticRay lam μ) {s : ℝ} (hs : 0 ≤ s) :
    busemann lam (μ s) = busemann lam (μ 0) - s := by
  obtain ⟨hμ, t, σ, htt, hσ0, hσd, hσgeo, hconv⟩ := h
  -- Step 1: the exact identity along the approximating segments
  have step1 : ∀ n, s ≤ dist (μ 0) (lam (t n)) →
      busemannAux lam (t n) (σ n s) = busemannAux lam (t n) (μ 0) - s := by
    intro n hsd
    have hkey : dist (σ n s) (lam (t n)) = dist (μ 0) (lam (t n)) - s := by
      have hmem_s : s ∈ Set.Icc 0 (dist (μ 0) (lam (t n))) := ⟨hs, hsd⟩
      have hmem_d : dist (μ 0) (lam (t n)) ∈ Set.Icc 0 (dist (μ 0) (lam (t n))) :=
        ⟨dist_nonneg, le_rfl⟩
      have h1 := hσgeo n hmem_s hmem_d
      rw [hσd n] at h1
      rw [h1, abs_of_nonpos (by linarith), neg_sub]
    show dist (lam (t n)) (σ n s) - t n = dist (lam (t n)) (μ 0) - t n - s
    rw [dist_comm (lam (t n)) (σ n s), hkey, dist_comm (lam (t n)) (μ 0)]
    ring
  -- Step 2: the inequality `≤`, up to an arbitrary `ε > 0`
  have hle : busemann lam (μ s) ≤ busemann lam (μ 0) - s := by
    apply le_of_forall_pos_le_add
    intro ε hε
    -- a time `T ≥ 0` where the Busemann approximant is `ε/2`-close to the infimum
    obtain ⟨T, hT0, hTclose⟩ : ∃ T : ℝ, 0 ≤ T ∧
        busemannAux lam T (μ 0) < busemann lam (μ 0) + ε / 2 := by
      have h1 : ∀ᶠ T in atTop, busemannAux lam T (μ 0) < busemann lam (μ 0) + ε / 2 :=
        (tendsto_busemannAux_atTop hlam (μ 0)).eventually_lt_const (by linarith)
      exact ((eventually_ge_atTop (0 : ℝ)).and h1).exists
    -- eventually `s` lies in the window `[0, d(μ 0, lam (t n))]`
    have hd : ∀ᶠ n in atTop, s ≤ dist (μ 0) (lam (t n)) := by
      filter_upwards [htt.eventually_ge_atTop (s + dist (lam 0) (μ 0)),
        htt.eventually_ge_atTop 0] with n h1 h2
      have h0n : dist (lam 0) (lam (t n)) = t n := by
        have h := hlam le_rfl h2
        rwa [zero_sub, abs_neg, abs_of_nonneg h2] at h
      have htri : dist (lam 0) (lam (t n)) ≤ dist (lam 0) (μ 0) + dist (μ 0) (lam (t n)) :=
        dist_triangle _ _ _
      rw [h0n] at htri
      linarith
    -- pointwise convergence `σ n s → μ s` at `s`
    have hσs : ∀ᶠ n in atTop, dist (σ n s) (μ s) < ε / 2 :=
      Metric.tendsto_nhds.mp (hconv.tendsto_at (Set.mem_Ici.mpr hs)) (ε / 2) (half_pos hε)
    -- choose one `n` far enough out
    obtain ⟨n, hsd, hTn, htn0, hns⟩ :=
      (hd.and ((htt.eventually_ge_atTop T).and ((htt.eventually_ge_atTop 0).and hσs))).exists
    -- chain the estimates
    have hlip : busemann lam (μ s) ≤ busemann lam (σ n s) + dist (μ s) (σ n s) := by
      have h1 := (lipschitzWith_busemann hlam).le_add_mul (μ s) (σ n s)
      rwa [NNReal.coe_one, one_mul] at h1
    have h2 : busemann lam (σ n s) ≤ busemannAux lam (t n) (σ n s) :=
      busemann_le_busemannAux hlam _ htn0
    have h3 : busemannAux lam (t n) (σ n s) = busemannAux lam (t n) (μ 0) - s :=
      step1 n hsd
    have h4 : busemannAux lam (t n) (μ 0) ≤ busemannAux lam T (μ 0) :=
      busemannAux_antitoneOn hlam (μ 0) (Set.mem_Ici.mpr hT0) (Set.mem_Ici.mpr htn0) hTn
    have h5 : dist (μ s) (σ n s) < ε / 2 := by rw [dist_comm]; exact hns
    linarith
  -- Step 3: the inequality `≥`, from the `1`-Lipschitz bound along the ray `μ`
  have hge : busemann lam (μ 0) - s ≤ busemann lam (μ s) := by
    have hd : dist (μ 0) (μ s) = s := by
      have h1 := hμ le_rfl hs
      rwa [zero_sub, abs_neg, abs_of_nonneg hs] at h1
    have h1 := (lipschitzWith_busemann hlam).le_add_mul (μ 0) (μ s)
    rw [NNReal.coe_one, one_mul, hd] at h1
    linarith
  exact le_antisymm hle hge

/-- **The Busemann upper bound from an asymptotic ray** (blueprint `lem:asymptotic-ray`,
part 3): `B_lam y ≤ B_lam (μ 0) - t + d(y, μ t)` for every `y` and `t ≥ 0`, combining
`IsAsymptoticRay.busemann_apply` with the `1`-Lipschitz bound for `B_lam`. -/
theorem IsAsymptoticRay.busemann_le {lam μ : ℝ → M} (hlam : IsGeodesicRay lam)
    (h : IsAsymptoticRay lam μ) (y : M) {t : ℝ} (ht : 0 ≤ t) :
    busemann lam y ≤ busemann lam (μ 0) - t + dist y (μ t) := by
  have h1 : busemann lam (μ t) = busemann lam (μ 0) - t := h.busemann_apply hlam ht
  have h2 := (lipschitzWith_busemann hlam).le_add_mul y (μ t)
  rw [NNReal.coe_one, one_mul, h1] at h2
  linarith

end MorganTianLib
