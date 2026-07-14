import PetersenLib.Ch05.Geodesics
import PetersenLib.Ch05.ChartTransition
import PetersenLib.Ch05.GeodesicSpeed
import PetersenLib.Ch05.TangentCompactness
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Petersen Ch. 5, §5.2 — extendability and geodesic completeness

Faithful statements of the compactness/extendability family of Petersen §5.2:

* `geodesic_uniformShortTimeExistence` (`lem:pet-ch5-uniform-time-existence`) —
  a single existence time `ε > 0` for all initial data in a compact subset of
  the tangent bundle.
* `maximalGeodesic_leavesCompactSet` (`prop:pet-ch5-leaves-compact-set`) — a
  geodesic on a maximal interval `(a, b)` with `b < ∞` eventually leaves every
  compact set.
* `compactManifold_geodesicallyComplete` (`cor:pet-ch5-compact-manifold-complete`,
  Petersen Cor. 5.2.5) — compact manifolds are geodesically complete.
* `geodesic_uniformExtensionOnCompactInterval` (`lem:pet-ch5-uniform-neighborhood`,
  Petersen Lemma 5.2.6) — all initial velocities near that of a geodesic defined
  over a compact time interval `[a, b]` yield geodesics on `[a, b]`.

The proofs are Petersen's compactness arguments over the local theory
(Thm. 5.2.2/5.2.3 + Lemma 5.2.4).  With the chart-transition law
(`PetersenLib/Ch05/ChartTransition.lean`), the compactness of bounded-velocity
sets in `TM` (`PetersenLib/Ch05/TangentCompactness.lean`) and the constant
speed of geodesics (`PetersenLib/Ch05/GeodesicSpeed.lean`) in place, the first
three statements are fully proven; the file also contains the
**maximal-geodesic machinery** (`geodesicMaximalDomain`,
`geodesicMaximalCurve`: the union of all admissible existence intervals,
coherent by Lemma 5.2.4), which proves Cor. 5.2.5 and will serve Hopf–Rinow
(§5.7).  Lemma 5.2.6 (`geodesic_uniformExtensionOnCompactInterval`), the
uniform extension over a compact time interval, is proven in
`PetersenLib/Ch05/GeodesicFlowBox.lean` via the local-flow continuity of
the flow-box argument.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** Petersen Ch. 5 (`lem:pet-ch5-uniform-time-existence`): **uniform
short-time existence over a compact set.**  If `K ⊆ TM` is compact, there is a
single `ε > 0` such that every initial datum `(q, v) ∈ K` is realised by a
geodesic defined on `(-ε, ε)`.

Proof: cover `K` by the finitely many `TM`-neighbourhoods produced by local
existence (Thm. 5.2.3) — each carrying the uniform time of its chart-local
Picard–Lindelöf flow — and take the minimum of the finitely many existence
times.  The produced chart-`p` geodesics are converted to intrinsic geodesics
with initial velocity read at their own foot by the chart-transition law. -/
theorem geodesic_uniformShortTimeExistence (g : RiemannianMetric I M)
    {K : Set (TangentBundle I M)} (hK : IsCompact K) :
    ∃ ε > 0, ∀ x ∈ K, ∃ γ : ℝ → M,
      IsGeodesicWithInitialOn g γ (Ioo (-ε) ε) 0 x.proj x.2 := by
  classical
  -- a uniform time on a `TM`-neighbourhood of every point
  have hpt : ∀ x₀ : TangentBundle I M, ∃ ε > 0, ∃ W ∈ 𝓝 x₀,
      ∀ x ∈ W, ∃ γ : ℝ → M,
        IsGeodesicWithInitialOn g γ (Ioo (-ε) ε) 0 x.proj x.2 := by
    intro x₀
    obtain ⟨p, v⟩ := x₀
    obtain ⟨ε₀, hε₀, V₁, hV₁, V₂, hV₂, c, L, hfam, -⟩ :=
      geodesic_local_existence_lipschitz (I := I) g p v
    have h0 : (0 : ℝ) ∈ Ioo (-ε₀) ε₀ := ⟨neg_lt_zero.mpr hε₀, hε₀⟩
    -- the chart-`p` fibre-coordinate map and its value/continuity at `⟨p, v⟩`
    have hφx₀ : (trivializationAt E (TangentSpace I) p ⟨p, v⟩).2 = (v : E) :=
      tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) p)
    have hx₀src : (⟨p, v⟩ : TangentBundle I M)
        ∈ (trivializationAt E (TangentSpace I) p).source := by
      rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H p
    have hφcont : ContinuousAt
        (fun y : TangentBundle I M => (trivializationAt E (TangentSpace I) p y).2)
        ⟨p, v⟩ :=
      continuous_snd.continuousAt.comp
        ((trivializationAt E (TangentSpace I) p).continuousOn.continuousAt
          ((trivializationAt E (TangentSpace I) p).open_source.mem_nhds hx₀src))
    -- the `TM`-neighbourhood of `⟨p, v⟩`
    have hW_nhds : (Bundle.TotalSpace.proj ⁻¹' (V₁ ∩ (chartAt H p).source)) ∩
        (fun y : TangentBundle I M => (trivializationAt E (TangentSpace I) p y).2) ⁻¹' V₂
        ∈ 𝓝 (⟨p, v⟩ : TangentBundle I M) := by
      refine Filter.inter_mem ?_
        (hφcont.preimage_mem_nhds (by rw [hφx₀]; exact hV₂))
      exact (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.preimage_mem_nhds
        (Filter.inter_mem hV₁ ((chartAt H p).open_source.mem_nhds (mem_chart_source H p)))
    refine ⟨ε₀, hε₀, _, hW_nhds, ?_⟩
    rintro ⟨q, w⟩ ⟨⟨hqV₁, hqsrc⟩, hwV₂⟩
    obtain ⟨hchart, hc0, hvel0⟩ := hfam q hqV₁
      ((trivializationAt E (TangentSpace I) p ⟨q, w⟩).2) hwV₂
    set γc : ℝ → M := c q ((trivializationAt E (TangentSpace I) p ⟨q, w⟩).2) with hγc_def
    have hcont : ContinuousOn γc (Ioo (-ε₀) ε₀) := hchart.continuousOn
    have hgeo : Geodesic.IsGeodesicOn (I := I) g γc (Ioo (-ε₀) ε₀) :=
      isGeodesicOn_of_isChartGeodesicOn g isOpen_Ioo hchart
    -- transfer the initial velocity from the chart at `p` to the chart at the foot
    have hqsrc_p : q ∈ (extChartAt I p).source := by
      rw [extChartAt_source I]; exact hqsrc
    have hqsrc_q : q ∈ (extChartAt I q).source := mem_extChartAt_source (I := I) q
    have hct0 : ContinuousAt γc 0 := hcont.continuousAt (isOpen_Ioo.mem_nhds h0)
    have hev : ∀ᶠ s in 𝓝 0,
        γc s ∈ (extChartAt I p).source ∩ (extChartAt I q).source := by
      refine hct0.eventually_mem ?_
      rw [hc0]
      exact Filter.inter_mem ((isOpen_extChartAt_source p).mem_nhds hqsrc_p)
        ((isOpen_extChartAt_source q).mem_nhds hqsrc_q)
    have hu1 : ∀ᶠ s in 𝓝 0, HasDerivAt (fun s' => extChartAt I p (γc s'))
        (deriv (fun s' => extChartAt I p (γc s')) s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
      exact hchart.2.1 s hs
    have heq : - Geodesic.chartChristoffelContraction (I := I) g p
        (deriv (fun s' => extChartAt I p (γc s')) 0)
        (deriv (fun s' => extChartAt I p (γc s')) 0) (extChartAt I p (γc 0))
        + Geodesic.chartChristoffelContraction (I := I) g p
          (deriv (fun s' => extChartAt I p (γc s')) 0)
          (deriv (fun s' => extChartAt I p (γc s')) 0) (extChartAt I p (γc 0)) = 0 :=
      neg_add_cancel _
    obtain ⟨hev', hvelq, -⟩ := chartReading_geodesicODE_transfer (I := I) g
      hev hu1 (hchart.2.2 0 h0) heq
    -- the transported velocity is the intrinsic fibre vector of `⟨q, w⟩`
    have hφ_eq : (trivializationAt E (TangentSpace I) p ⟨q, w⟩).2
        = tangentCoordChange I q p q w := rfl
    have hvel_val : deriv (fun s' => extChartAt I q (γc s')) 0 = (w : E) := by
      rw [hvelq, hvel0.deriv, hc0, hφ_eq,
        tangentCoordChange_comp (I := I) ⟨⟨hqsrc_q, hqsrc_p⟩, hqsrc_q⟩,
        tangentCoordChange_self (I := I) hqsrc_q]
    have hvel : HasDerivAt (fun s' => extChartAt I q (γc s')) (w : E) 0 := by
      rw [← hvel_val]
      exact hev'.self_of_nhds
    exact ⟨γc, hcont, hc0, hvel, hgeo⟩
  -- compactness: finitely many neighbourhoods and the minimum of their times
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, by simp⟩
  choose ε hε W hW hgood using hpt
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover W fun x _ => hW x
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨x₀, hx₀t, -⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact ⟨x₀, hx₀t⟩
  refine ⟨t.inf' htne ε, ?_, ?_⟩
  · obtain ⟨x₀, hx₀t, hinf⟩ := Finset.exists_mem_eq_inf' htne ε
    rw [hinf]
    exact hε x₀
  · intro x hx
    obtain ⟨x₀, hx₀t, hxW⟩ := Set.mem_iUnion₂.mp (hcover hx)
    obtain ⟨γ, hγ⟩ := hgood x₀ x hxW
    exact ⟨γ, hγ.mono (Set.Ioo_subset_Ioo
      (neg_le_neg (Finset.inf'_le ε hx₀t)) (Finset.inf'_le ε hx₀t))⟩

/-- **Math.** Petersen Ch. 5 (`prop:pet-ch5-leaves-compact-set`): **maximal
geodesics leave every compact set.**  Let `γ` be a continuous geodesic on
`(a, b)` (`a < b`, `b` finite) that is maximal in the sense that it does not
extend to a continuous geodesic on any strictly larger interval `(a, b')`,
`b' > b`.  Then for every compact `K ⊆ M` there is `t_K < b` beyond which `γ`
avoids `K`.  (Continuity and the Hausdorff hypothesis are implicit in
Petersen: geodesics are smooth curves on a Hausdorff manifold.)

Proof: otherwise `γ(t₁) ∈ K` for some `t₁` with `b - t₁ < ε/2`; constancy of
speed puts the velocity at `t₁` in the compact bounded-velocity set
`{x ∈ TM | x.proj ∈ K, g(ẋ, ẋ) ≤ c}` (`isCompact_tangentSublevel`), uniform
short-time existence (`geodesic_uniformShortTimeExistence`) realises it by a
geodesic `σ` on `(t₁ - ε, t₁ + ε)`, and global uniqueness (Lemma 5.2.4) glues
`σ` onto `γ`, extending it past `b` — contradicting maximality. -/
theorem maximalGeodesic_leavesCompactSet (g : RiemannianMetric I M) [T2Space M]
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn γ (Ioo a b))
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hmax : ∀ (γ' : ℝ → M) (b' : ℝ), b < b' → Set.EqOn γ γ' (Ioo a b) →
      ContinuousOn γ' (Ioo a b') → ¬ Geodesic.IsGeodesicOn (I := I) g γ' (Ioo a b'))
    {K : Set M} (hK : IsCompact K) :
    ∃ tK ∈ Ioo a b, ∀ t ∈ Ioo tK b, γ t ∉ K := by
  classical
  by_contra hcon
  push Not at hcon
  -- the constant squared speed of `γ`
  set t₀ : ℝ := (a + b) / 2 with ht₀_def
  have ht₀ : t₀ ∈ Ioo a b := ⟨by rw [ht₀_def]; linarith, by rw [ht₀_def]; linarith⟩
  set c : ℝ := curveSpeedSq (I := I) g γ t₀ with hc_def
  -- uniform short-time existence over the compact bounded-velocity set
  obtain ⟨ε, hε, huni⟩ := geodesic_uniformShortTimeExistence (I := I) g
    (isCompact_tangentSublevel (I := I) g hK c)
  -- a return time within `ε/2` of `b`
  set tK : ℝ := max t₀ (b - ε / 2) with htK_def
  have htK : tK ∈ Ioo a b := ⟨lt_of_lt_of_le ht₀.1 (le_max_left _ _),
    max_lt ht₀.2 (by linarith)⟩
  obtain ⟨t₁, ht₁mem, ht₁K⟩ := hcon tK htK
  have ht₁ : t₁ ∈ Ioo a b := ⟨lt_trans htK.1 ht₁mem.1, ht₁mem.2⟩
  have ht₁close : b - ε / 2 < t₁ := lt_of_le_of_lt (le_max_right t₀ (b - ε / 2)) ht₁mem.1
  -- the velocity of `γ` at `t₁` lies in the bounded-velocity set
  set v₁ : E := deriv (fun s => extChartAt I (γ t₁) (γ s)) t₁ with hv₁_def
  have hspeed : curveSpeedSq (I := I) g γ t₁ = c :=
    curveSpeedSq_eqOn_const (I := I) g isOpen_Ioo Set.ordConnected_Ioo hcont hγ ht₁ ht₀
  have hmem' : (⟨γ t₁, v₁⟩ : TangentBundle I M)
      ∈ {x : TangentBundle I M | x.proj ∈ K ∧ g.inner x.proj x.2 x.2 ≤ c} := by
    refine ⟨ht₁K, le_of_eq ?_⟩
    rw [← hspeed, hv₁_def]
    rfl
  obtain ⟨σ, hσ₀⟩ := huni _ hmem'
  have hσ : IsGeodesicWithInitialOn (I := I) g σ (Ioo (-ε) ε) 0 (γ t₁) v₁ := hσ₀
  -- shift `σ` to be based at time `t₁`
  have hσ' := hσ.shift t₁
  have hJeq : {s : ℝ | s - t₁ ∈ Ioo (-ε) ε} = Ioo (t₁ - ε) (t₁ + ε) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hJeq, zero_add] at hσ'
  set σ' : ℝ → M := fun s => σ (s - t₁) with hσ'_def
  obtain ⟨hσ'cont, hσ'val, hσ'vel, hσ'geo⟩ := hσ'
  have ht₁σ : t₁ ∈ Ioo (t₁ - ε) (t₁ + ε) := ⟨by linarith, by linarith⟩
  -- global uniqueness: `γ` and the shifted `σ` agree on the overlap
  have hvel : deriv (Geodesic.chartLocalCurve (I := I) γ t₁) t₁
      = deriv (fun s => extChartAt I (γ t₁) (σ' s)) t₁ := by
    rw [hσ'vel.deriv, hv₁_def]
    rfl
  have hveq : Set.EqOn γ σ' (Ioo a b ∩ Ioo (t₁ - ε) (t₁ + ε)) :=
    geodesic_global_uniqueness (I := I) g isOpen_Ioo Set.ordConnected_Ioo
      isOpen_Ioo Set.ordConnected_Ioo hcont hσ'cont hγ hσ'geo
      ⟨ht₁, ht₁σ⟩ hσ'val.symm hvel
  -- the glued extension past `b`
  set b' : ℝ := t₁ + ε with hb'_def
  have hbb' : b < b' := by rw [hb'_def]; linarith
  have hmaxab : max a (t₁ - ε) < b := max_lt hab (by linarith [ht₁.2])
  set γ' : ℝ → M := fun t => if t < b then γ t else σ' t with hγ'_def
  have hEqOn : Set.EqOn γ γ' (Ioo a b) := fun t ht => by
    rw [hγ'_def]
    simp only [if_pos ht.2]
  have hW : ∀ s ∈ Ioo (max a (t₁ - ε)) b', γ' s = σ' s := by
    intro s hs
    rw [hγ'_def]
    by_cases hsb : s < b
    · simp only [if_pos hsb]
      exact hveq ⟨⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hsb⟩,
        ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩⟩
    · simp only [if_neg hsb]
  have hγ'cont : ContinuousOn γ' (Ioo a b') := by
    intro t ht
    refine (ContinuousAt.continuousWithinAt ?_)
    by_cases htb : t < b
    · have htab : t ∈ Ioo a b := ⟨ht.1, htb⟩
      have heq : γ' =ᶠ[𝓝 t] γ :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htab) fun s hs => (hEqOn hs).symm
      exact (hcont.continuousAt (isOpen_Ioo.mem_nhds htab)).congr heq.symm
    · push Not at htb
      have htW : t ∈ Ioo (max a (t₁ - ε)) b' := ⟨lt_of_lt_of_le hmaxab htb, ht.2⟩
      have htσ : t ∈ Ioo (t₁ - ε) (t₁ + ε) :=
        ⟨lt_of_lt_of_le (by linarith [ht₁.2]) htb, ht.2⟩
      have heq : γ' =ᶠ[𝓝 t] σ' :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htW) hW
      exact (hσ'cont.continuousAt (isOpen_Ioo.mem_nhds htσ)).congr heq.symm
  have hγ'geo : Geodesic.IsGeodesicOn (I := I) g γ' (Ioo a b') := by
    intro t ht
    by_cases htb : t < b
    · have htab : t ∈ Ioo a b := ⟨ht.1, htb⟩
      exact hasGeodesicEquationAt_congr
        (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htab) hEqOn) (hγ t htab)
    · push Not at htb
      have htW : t ∈ Ioo (max a (t₁ - ε)) b' := ⟨lt_of_lt_of_le hmaxab htb, ht.2⟩
      have htσ : t ∈ Ioo (t₁ - ε) (t₁ + ε) :=
        ⟨lt_of_lt_of_le (by linarith [ht₁.2]) htb, ht.2⟩
      exact hasGeodesicEquationAt_congr
        (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htW) fun s hs => (hW s hs).symm)
        (hσ'geo t htσ)
  exact hmax γ' b' hbb' hEqOn hγ'cont hγ'geo

/-! ## The maximal geodesic through an initial datum

The union-of-intervals construction of the maximal geodesic: admissible
existence intervals patch coherently by global uniqueness (Lemma 5.2.4), so
their union carries a well-defined maximal geodesic.  This is the
"maximal interval of existence" of Petersen's proof of Cor. 5.2.5, and will
also serve Hopf–Rinow (§5.7). -/

/-- **Math.** The family of **admissible existence intervals** for the geodesic
initial-value problem `c(0) = p`, `ċ(0) = v`: open order-connected time sets
containing `0` on which some continuous geodesic realises the initial datum. -/
def geodesicExtensionFamily (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : Set (Set ℝ) :=
  {J | IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧
    ∃ γ : ℝ → M, IsGeodesicWithInitialOn g γ J 0 p v}

/-- **Math.** The **maximal existence domain** of the geodesic initial-value
problem: the union of all admissible existence intervals. -/
def geodesicMaximalDomain (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : Set ℝ :=
  ⋃₀ geodesicExtensionFamily g p v

theorem isOpen_geodesicMaximalDomain (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : IsOpen (geodesicMaximalDomain g p v) :=
  isOpen_sUnion fun _ hJ => hJ.1

/-- **Math.** The maximal existence domain is order-connected: all admissible
intervals contain `0`. -/
theorem ordConnected_geodesicMaximalDomain (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : (geodesicMaximalDomain g p v).OrdConnected := by
  constructor
  rintro x ⟨J₁, hJ₁, hxJ₁⟩ y ⟨J₂, hJ₂, hyJ₂⟩ z hz
  rcases le_total z 0 with h | h
  · exact ⟨J₁, hJ₁, hJ₁.2.1.out hxJ₁ hJ₁.2.2.1 ⟨hz.1, h⟩⟩
  · exact ⟨J₂, hJ₂, hJ₂.2.1.out hJ₂.2.2.1 hyJ₂ ⟨h, hz.2⟩⟩

/-- **Math.** Local existence (Thm. 5.2.3) seeds the maximal domain: `0` belongs
to it. -/
theorem zero_mem_geodesicMaximalDomain (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : (0 : ℝ) ∈ geodesicMaximalDomain g p v := by
  obtain ⟨ε, hε, huni⟩ := geodesic_uniformShortTimeExistence (I := I) g
    (isCompact_singleton (x := (⟨p, v⟩ : TangentBundle I M)))
  obtain ⟨γ, hγ₀⟩ := huni (⟨p, v⟩ : TangentBundle I M) rfl
  have hγ : IsGeodesicWithInitialOn (I := I) g γ (Ioo (-ε) ε) 0 p v := hγ₀
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  exact ⟨Ioo (-ε) ε, ⟨isOpen_Ioo, Set.ordConnected_Ioo, h0, γ, hγ⟩, h0⟩

/-- Every time in the maximal domain is witnessed by an admissible interval and
a geodesic through it. -/
theorem exists_geodesicWitness_of_mem_maximalDomain (g : RiemannianMetric I M)
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ geodesicMaximalDomain g p v) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicWithInitialOn g γ J 0 p v := by
  obtain ⟨J, ⟨hJo, hJc, h0J, γ, hγ⟩, htJ⟩ := ht
  exact ⟨γ, J, hJo, hJc, h0J, htJ, hγ⟩

open Classical in
/-- **Math.** The **maximal geodesic** through `(p, v)`: on the maximal domain it
follows a chosen admissible geodesic through each time (well defined by
Lemma 5.2.4); outside the domain it sits at `p`. -/
noncomputable def geodesicMaximalCurve (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : ℝ → M := fun t =>
  if ht : t ∈ geodesicMaximalDomain g p v then
    (exists_geodesicWitness_of_mem_maximalDomain g ht).choose t
  else p

/-- **Math.** **Coherence of admissible geodesics** (Lemma 5.2.4): two continuous
geodesics realising the same initial datum at `0` agree on the overlap of
their admissible intervals. -/
theorem geodesicWithInitialOn_eqOn (g : RiemannianMetric I M) [T2Space M]
    {p : M} {v : TangentSpace I p} {γ₁ γ₂ : ℝ → M} {J₁ J₂ : Set ℝ}
    (hJ₁o : IsOpen J₁) (hJ₁c : J₁.OrdConnected)
    (hJ₂o : IsOpen J₂) (hJ₂c : J₂.OrdConnected)
    (h₁ : IsGeodesicWithInitialOn (I := I) g γ₁ J₁ 0 p v)
    (h₂ : IsGeodesicWithInitialOn (I := I) g γ₂ J₂ 0 p v)
    (h0₁ : (0 : ℝ) ∈ J₁) (h0₂ : (0 : ℝ) ∈ J₂) :
    Set.EqOn γ₁ γ₂ (J₁ ∩ J₂) := by
  obtain ⟨hc₁, hval₁, hvel₁, hgeo₁⟩ := h₁
  obtain ⟨hc₂, hval₂, hvel₂, hgeo₂⟩ := h₂
  refine geodesic_global_uniqueness (I := I) g hJ₁o hJ₁c hJ₂o hJ₂c hc₁ hc₂
    hgeo₁ hgeo₂ ⟨h0₁, h0₂⟩ (by rw [hval₁, hval₂]) ?_
  show deriv (fun s => extChartAt I (γ₁ 0) (γ₁ s)) 0
      = deriv (fun s => extChartAt I (γ₁ 0) (γ₂ s)) 0
  rw [hval₁, hvel₁.deriv, hvel₂.deriv]

/-- **Math.** The maximal geodesic agrees with every admissible geodesic on its
interval. -/
theorem geodesicMaximalCurve_eqOn (g : RiemannianMetric I M) [T2Space M]
    {p : M} {v : TangentSpace I p} {γ : ℝ → M} {J : Set ℝ}
    (hJo : IsOpen J) (hJc : J.OrdConnected) (h0J : (0 : ℝ) ∈ J)
    (hγ : IsGeodesicWithInitialOn (I := I) g γ J 0 p v) :
    Set.EqOn (geodesicMaximalCurve g p v) γ J := by
  intro t htJ
  have htD : t ∈ geodesicMaximalDomain g p v := ⟨J, ⟨hJo, hJc, h0J, γ, hγ⟩, htJ⟩
  simp only [geodesicMaximalCurve, dif_pos htD]
  obtain ⟨J', hJ'o, hJ'c, h0', htJ', hγ'⟩ :=
    (exists_geodesicWitness_of_mem_maximalDomain g htD).choose_spec
  exact geodesicWithInitialOn_eqOn (I := I) g hJ'o hJ'c hJo hJc hγ' hγ h0' h0J
    ⟨htJ', htJ⟩

/-- **Math.** The maximal geodesic realises the initial datum on the whole
maximal domain: it is continuous there, starts at `(p, v)`, and satisfies the
geodesic equation.  (Locally it agrees with an admissible geodesic, and the
geodesic equation is local.) -/
theorem geodesicMaximalCurve_spec (g : RiemannianMetric I M) [T2Space M]
    (p : M) (v : TangentSpace I p) :
    IsGeodesicWithInitialOn (I := I) g (geodesicMaximalCurve g p v)
      (geodesicMaximalDomain g p v) 0 p v := by
  have hloc : ∀ t ∈ geodesicMaximalDomain g p v, ∃ (γ : ℝ → M) (J : Set ℝ),
      IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicWithInitialOn (I := I) g γ J 0 p v ∧
      Set.EqOn (geodesicMaximalCurve g p v) γ J := by
    intro t ht
    obtain ⟨γ, J, hJo, hJc, h0J, htJ, hγ⟩ :=
      exists_geodesicWitness_of_mem_maximalDomain g ht
    exact ⟨γ, J, hJo, h0J, htJ, hγ,
      geodesicMaximalCurve_eqOn (I := I) g hJo hJc h0J hγ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity on the domain
    intro t ht
    obtain ⟨γ, J, hJo, h0J, htJ, hγ, heq⟩ := hloc t ht
    refine ContinuousAt.continuousWithinAt ?_
    exact (hγ.1.continuousAt (hJo.mem_nhds htJ)).congr
      (Filter.eventuallyEq_of_mem (hJo.mem_nhds htJ) fun s hs => (heq hs).symm)
  · -- value at 0
    obtain ⟨γ, J, hJo, h0J, h0J', hγ, heq⟩ :=
      hloc 0 (zero_mem_geodesicMaximalDomain (I := I) g p v)
    rw [heq h0J']
    exact hγ.2.1
  · -- velocity at 0
    obtain ⟨γ, J, hJo, h0J, h0J', hγ, heq⟩ :=
      hloc 0 (zero_mem_geodesicMaximalDomain (I := I) g p v)
    refine hγ.2.2.1.congr_of_eventuallyEq ?_
    filter_upwards [hJo.mem_nhds h0J'] with s hs
    rw [heq hs]
  · -- the geodesic equation on the domain
    intro t ht
    obtain ⟨γ, J, hJo, h0J, htJ, hγ, heq⟩ := hloc t ht
    exact hasGeodesicEquationAt_congr
      (Filter.eventuallyEq_of_mem (hJo.mem_nhds htJ) fun s hs => (heq hs).symm)
      (hγ.2.2.2 t htJ)

/-- **Math.** On a compact manifold the maximal existence domain is **unbounded
above**: were `b = sup` finite, the maximal geodesic on `(0, b)` would satisfy
the maximality hypothesis of `maximalGeodesic_leavesCompactSet` (an extension
would glue with the maximal curve into a strictly larger admissible interval),
so it would have to leave the compact set `K = M` — absurd. -/
theorem not_bddAbove_geodesicMaximalDomain (g : RiemannianMetric I M)
    [T2Space M] [CompactSpace M] (p : M) (v : TangentSpace I p) :
    ¬ BddAbove (geodesicMaximalDomain g p v) := by
  intro hbdd
  set D : Set ℝ := geodesicMaximalDomain g p v with hD_def
  have hDopen : IsOpen D := isOpen_geodesicMaximalDomain (I := I) g p v
  have hDconn : D.OrdConnected := ordConnected_geodesicMaximalDomain (I := I) g p v
  have h0D : (0 : ℝ) ∈ D := zero_mem_geodesicMaximalDomain (I := I) g p v
  have hDne : D.Nonempty := ⟨0, h0D⟩
  set b : ℝ := sSup D with hb_def
  -- the supremum is positive and not attained
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hDopen 0 h0D
  have hb_pos : 0 < b := by
    have hmem : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
      linarith
    exact lt_of_lt_of_le (by linarith) (le_csSup hbdd (hball hmem))
  have hbD : b ∉ D := by
    intro hbD
    obtain ⟨δ', hδ', hball'⟩ := Metric.isOpen_iff.mp hDopen b hbD
    have hmem : b + δ' / 2 ∈ Metric.ball b δ' := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos (by linarith)]
      linarith
    have := le_csSup hbdd (hball' hmem)
    linarith
  have hDsubIio : D ⊆ Iio b := fun t htD =>
    lt_of_le_of_ne (le_csSup hbdd htD) fun h => hbD (by rw [hb_def, ← h]; exact htD)
  have hIooSub : Ioo 0 b ⊆ D := by
    intro t ht
    obtain ⟨s, hsD, hts⟩ := exists_lt_of_lt_csSup hDne ht.2
    exact hDconn.out h0D hsD ⟨le_of_lt ht.1, le_of_lt hts⟩
  have hspec := geodesicMaximalCurve_spec (I := I) g p v
  set γm : ℝ → M := geodesicMaximalCurve g p v with hγm_def
  -- the maximality hypothesis: any extension glues into a larger admissible set
  have hmaxhyp : ∀ (γ' : ℝ → M) (b' : ℝ), b < b' → Set.EqOn γm γ' (Ioo 0 b) →
      ContinuousOn γ' (Ioo 0 b') →
      ¬ Geodesic.IsGeodesicOn (I := I) g γ' (Ioo 0 b') := by
    intro γ' b' hbb' hEqOn hcont' hgeo'
    classical
    set γg : ℝ → M := fun t => if t < b then γm t else γ' t with hγg_def
    have hgm : ∀ s ∈ D, γg s = γm s := fun s hs => by
      rw [hγg_def]
      simp only [if_pos (Set.mem_Iio.mp (hDsubIio hs))]
    have hg' : ∀ s ∈ Ioo 0 b', γg s = γ' s := by
      intro s hs
      rw [hγg_def]
      by_cases hsb : s < b
      · simp only [if_pos hsb]
        exact hEqOn ⟨hs.1, hsb⟩
      · simp only [if_neg hsb]
    -- the enlarged admissible interval
    have hmem : (D ∪ Ioo 0 b') ∈ geodesicExtensionFamily (I := I) g p v := by
      have hb2D : b / 2 ∈ D := hIooSub ⟨by linarith, by linarith⟩
      have hb2I : b / 2 ∈ Ioo 0 b' := ⟨by linarith, by linarith⟩
      refine ⟨hDopen.union isOpen_Ioo, ?_, Or.inl h0D, γg, ?_, ?_, ?_, ?_⟩
      · -- order-connectedness: `b/2` is a common point
        constructor
        rintro x (hx | hx) y (hy | hy) z hz
        · exact Or.inl (hDconn.out hx hy hz)
        · rcases le_total z (b / 2) with h | h
          · exact Or.inl (hDconn.out hx hb2D ⟨hz.1, h⟩)
          · exact Or.inr (Set.ordConnected_Ioo.out hb2I hy ⟨h, hz.2⟩)
        · rcases le_total z (b / 2) with h | h
          · exact Or.inr (Set.ordConnected_Ioo.out hx hb2I ⟨hz.1, h⟩)
          · exact Or.inl (hDconn.out hb2D hy ⟨h, hz.2⟩)
        · exact Or.inr (Set.ordConnected_Ioo.out hx hy hz)
      · -- continuity of the glued curve
        intro t ht
        refine ContinuousAt.continuousWithinAt ?_
        by_cases htb : t < b
        · have htD : t ∈ D := by
            rcases ht with htD | htI
            · exact htD
            · exact hIooSub ⟨htI.1, htb⟩
          exact (hspec.1.continuousAt (hDopen.mem_nhds htD)).congr
            (Filter.eventuallyEq_of_mem (hDopen.mem_nhds htD)
              fun s hs => (hgm s hs).symm)
        · push Not at htb
          have htI : t ∈ Ioo 0 b' := by
            rcases ht with htD | htI
            · exact absurd (hDsubIio htD) (not_lt.mpr htb)
            · exact htI
          exact (hcont'.continuousAt (isOpen_Ioo.mem_nhds htI)).congr
            (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htI)
              fun s hs => (hg' s hs).symm)
      · -- value at 0
        rw [hgm 0 h0D]
        exact hspec.2.1
      · -- velocity at 0
        refine hspec.2.2.1.congr_of_eventuallyEq ?_
        filter_upwards [hDopen.mem_nhds h0D] with s hs
        rw [hgm s hs]
      · -- the geodesic equation on the union
        intro t ht
        by_cases htb : t < b
        · have htD : t ∈ D := by
            rcases ht with htD | htI
            · exact htD
            · exact hIooSub ⟨htI.1, htb⟩
          exact hasGeodesicEquationAt_congr
            (Filter.eventuallyEq_of_mem (hDopen.mem_nhds htD)
              fun s hs => (hgm s hs).symm) (hspec.2.2.2 t htD)
        · push Not at htb
          have htI : t ∈ Ioo 0 b' := by
            rcases ht with htD | htI
            · exact absurd (hDsubIio htD) (not_lt.mpr htb)
            · exact htI
          exact hasGeodesicEquationAt_congr
            (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htI)
              fun s hs => (hg' s hs).symm) (hgeo' t htI)
    -- the union is admissible, hence inside the domain: contradicts `sup D = b`
    have hin : (b + b') / 2 ∈ D := ⟨D ∪ Ioo 0 b', hmem,
      Or.inr ⟨by linarith, by linarith⟩⟩
    have hlt := hDsubIio hin
    rw [Set.mem_Iio] at hlt
    linarith
  -- the maximal geodesic on `(0, b)` leaves the compact set `M`: absurd
  obtain ⟨tK, htK, hleave⟩ := maximalGeodesic_leavesCompactSet (I := I) g hb_pos
    (hspec.1.mono hIooSub) (fun t ht => hspec.2.2.2 t (hIooSub ht)) hmaxhyp
    isCompact_univ
  exact hleave ((tK + b) / 2) ⟨by linarith [htK.2], by linarith [htK.2]⟩
    (mem_univ _)

/-- **Math.** **Time reversal** maps the maximal existence domain of `(p, v)`
into that of `(p, -v)` (homogeneity of geodesics with factor `-1`). -/
theorem neg_mem_geodesicMaximalDomain (g : RiemannianMetric I M)
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ geodesicMaximalDomain g p v) :
    -t ∈ geodesicMaximalDomain (I := I) g p (-v) := by
  obtain ⟨J, ⟨hJo, hJc, h0J, γ, hγ⟩, htJ⟩ := ht
  have hrev := geodesicHomogeneity (I := I) g (-1 : ℝ) hγ
  refine ⟨{s : ℝ | (-1 : ℝ) * s ∈ J}, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hJo.preimage (continuous_const.mul continuous_id)
  · constructor
    rintro x hx y hy z hz
    show (-1 : ℝ) * z ∈ J
    simp only [Set.mem_setOf_eq] at hx hy
    exact hJc.out hy hx ⟨by nlinarith [hz.2], by nlinarith [hz.1]⟩
  · show (-1 : ℝ) * 0 ∈ J
    simpa using h0J
  · exact ⟨fun s => γ ((-1 : ℝ) * s), by rw [← neg_one_smul ℝ v]; exact hrev⟩
  · show (-1 : ℝ) * (-t) ∈ J
    simpa using htJ

/-- **Math.** On a compact manifold the maximal existence domain is **unbounded
below** (time reversal of `not_bddAbove_geodesicMaximalDomain`). -/
theorem not_bddBelow_geodesicMaximalDomain (g : RiemannianMetric I M)
    [T2Space M] [CompactSpace M] (p : M) (v : TangentSpace I p) :
    ¬ BddBelow (geodesicMaximalDomain g p v) := by
  intro hbdd
  obtain ⟨m, hm⟩ := hbdd
  refine not_bddAbove_geodesicMaximalDomain (I := I) g p (-v) ⟨-m, ?_⟩
  rintro t ht
  have hneg := neg_mem_geodesicMaximalDomain (I := I) g ht
  rw [neg_neg] at hneg
  have := hm hneg
  linarith

/-- **Math.** Petersen Ch. 5, Corollary 5.2.5
(`cor:pet-ch5-compact-manifold-complete`): **compact manifolds are geodesically
complete** — every initial datum on a compact Riemannian manifold is realised
by a geodesic defined on all of `ℝ`.

Proof: the maximal existence domain is open, order-connected and unbounded in
both directions (`not_bddAbove_geodesicMaximalDomain` and its time reversal:
a finite endpoint would force the maximal geodesic to leave the compact set
`K = M`), hence is all of `ℝ`; the maximal geodesic realises the datum. -/
theorem compactManifold_geodesicallyComplete (g : RiemannianMetric I M)
    [CompactSpace M] [T2Space M] :
    IsGeodesicallyComplete (I := I) g := by
  intro p v
  have hunion : geodesicMaximalDomain (I := I) g p v = Set.univ := by
    have hup := not_bddAbove_geodesicMaximalDomain (I := I) g p v
    have hdown := not_bddBelow_geodesicMaximalDomain (I := I) g p v
    rw [not_bddAbove_iff] at hup
    rw [not_bddBelow_iff] at hdown
    ext t
    simp only [Set.mem_univ, iff_true]
    obtain ⟨x, hxD, hxt⟩ := hdown t
    obtain ⟨y, hyD, hty⟩ := hup t
    exact (ordConnected_geodesicMaximalDomain (I := I) g p v).out hxD hyD
      ⟨le_of_lt hxt, le_of_lt hty⟩
  have hspec := geodesicMaximalCurve_spec (I := I) g p v
  rw [hunion] at hspec
  exact ⟨geodesicMaximalCurve g p v, continuousOn_univ.mp hspec.1, hspec.2.1,
    hspec.2.2.1, fun t => hspec.2.2.2 t (Set.mem_univ t)⟩

end PetersenLib
