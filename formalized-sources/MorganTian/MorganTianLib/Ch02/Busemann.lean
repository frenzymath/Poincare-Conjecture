import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Order

/-!
# Poincaré Ch. 2, §2.1 — The Busemann function of a minimizing geodesic ray

For a minimizing geodesic ray `γ : ℝ → M` in a metric space `M`, the **Busemann
function** `B_γ(x) = lim_{t → ∞} (d(γ(t), x) - t)` (`busemann`), obtained as the limit
(equivalently, the infimum, by antitonicity) of the approximating functions
`B_{γ,t}(x) = d(γ(t), x) - t` (`busemannAux`). Each `B_{γ,t}` is `1`-Lipschitz and,
for fixed `x`, non-increasing and bounded below in `t`; hence the limit `B_γ` exists,
is itself `1`-Lipschitz, and satisfies `B_γ(γ(s)) = -s` for all `s ≥ 0`
(`lipschitzWith_busemann`, `busemann_apply_ray`).

## Design notes

* `IsGeodesicRay γ` only constrains `γ` on `[0, ∞)`; values at negative times are junk,
  matching the blueprint's convention that `γ : [0, ∞) → M`.
* `busemann` is defined as `⨅ t : Set.Ici (0 : ℝ), busemannAux γ t x` rather than as a
  primitive limit; `tendsto_busemannAux_atTop` records that this conditionally complete
  infimum is indeed the limit `t → ∞` claimed in the blueprint (monotone convergence).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.1
(blueprint `def:busemann-function`).
-/

open Filter Topology

namespace MorganTianLib

variable {M : Type*} [MetricSpace M]

/-- A **minimizing geodesic ray** in the metric sense: a curve `γ : ℝ → M` whose
restriction to `[0, ∞)` is a unit-speed isometric embedding, `dist (γ s) (γ t) = |s - t|`.
(Values of `γ` at negative times are irrelevant junk.) In a Riemannian manifold this is
exactly a unit-speed geodesic ray all of whose sub-arcs are length-minimizing. -/
def IsGeodesicRay (γ : ℝ → M) : Prop :=
  ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ ⦃t : ℝ⦄, 0 ≤ t → dist (γ s) (γ t) = |s - t|

/-- The approximating function `B_{γ,t}(x) = d(γ(t), x) - t` of the Busemann function. -/
def busemannAux (γ : ℝ → M) (t : ℝ) (x : M) : ℝ := dist (γ t) x - t

/-- The **Busemann function** of a minimizing geodesic ray, defined as the infimum
(equivalently, by antitonicity, the limit as `t → ∞`) of `d(γ(t), x) - t` over `t ≥ 0`. -/
noncomputable def busemann (γ : ℝ → M) (x : M) : ℝ :=
  ⨅ t : Set.Ici (0 : ℝ), busemannAux γ t x

/-- Each `B_{γ,t}` is `1`-Lipschitz in `x`, since `x ↦ d(γ(t), x)` is `1`-Lipschitz and
subtracting the constant `t` does not change Lipschitz behaviour. -/
theorem lipschitzWith_busemannAux (γ : ℝ → M) (t : ℝ) :
    LipschitzWith 1 (busemannAux γ t) :=
  LipschitzWith.mk_one fun x y => by
    have h : |dist x (γ t) - dist y (γ t)| ≤ dist x y := abs_dist_sub_le x y (γ t)
    show |dist (γ t) x - t - (dist (γ t) y - t)| ≤ dist x y
    rw [sub_sub_sub_cancel_right, dist_comm (γ t) x, dist_comm (γ t) y]
    exact h

/-- For fixed `x`, `t ↦ B_{γ,t}(x)` is non-increasing on `[0, ∞)`: if `0 ≤ s ≤ t` then
`d(γ(t), x) ≤ d(γ(t), γ(s)) + d(γ(s), x) = (t - s) + d(γ(s), x)`, i.e.
`B_{γ,t}(x) ≤ B_{γ,s}(x)`. -/
theorem busemannAux_antitoneOn {γ : ℝ → M} (hγ : IsGeodesicRay γ) (x : M) :
    AntitoneOn (fun t => busemannAux γ t x) (Set.Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have hdist : dist (γ t) (γ s) = t - s := by
    rw [hγ ht hs, abs_of_nonneg (by linarith)]
  have htri : dist (γ t) x ≤ dist (γ t) (γ s) + dist (γ s) x := dist_triangle _ _ _
  rw [hdist] at htri
  show busemannAux γ t x ≤ busemannAux γ s x
  show dist (γ t) x - t ≤ dist (γ s) x - s
  linarith

/-- `B_{γ,t}(x) ≥ -d(x, γ(0))` for all `t ≥ 0`: from `t = d(γ(0), γ(t)) ≤ d(γ(0), x) + d(x, γ(t))`. -/
theorem neg_dist_le_busemannAux {γ : ℝ → M} (hγ : IsGeodesicRay γ) (x : M) {t : ℝ} (ht : 0 ≤ t) :
    -dist x (γ 0) ≤ busemannAux γ t x := by
  have h0 : dist (γ 0) (γ t) = t := by
    have h := hγ le_rfl ht
    rwa [zero_sub, abs_neg, abs_of_nonneg ht] at h
  have htri : dist (γ 0) (γ t) ≤ dist (γ 0) x + dist x (γ t) := dist_triangle _ _ _
  rw [h0] at htri
  show -dist x (γ 0) ≤ dist (γ t) x - t
  rw [dist_comm (γ t) x, dist_comm x (γ 0)]
  linarith

/-- The range of `t ↦ B_{γ,t}(x)` over `t ≥ 0` is bounded below, by `-d(x, γ(0))`. -/
theorem busemannAux_bddBelow {γ : ℝ → M} (hγ : IsGeodesicRay γ) (x : M) :
    BddBelow (Set.range fun t : Set.Ici (0 : ℝ) => busemannAux γ (t : ℝ) x) :=
  ⟨-dist x (γ 0), by rintro _ ⟨t, rfl⟩; exact neg_dist_le_busemannAux hγ x t.2⟩

instance : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.self_mem_Ici⟩⟩

/-- `B_γ(x) ≤ B_{γ,t}(x)` for every `t ≥ 0`: the Busemann function is the infimum of the
approximating family. -/
theorem busemann_le_busemannAux {γ : ℝ → M} (hγ : IsGeodesicRay γ) (x : M) {t : ℝ} (ht : 0 ≤ t) :
    busemann γ x ≤ busemannAux γ t x :=
  ciInf_le (busemannAux_bddBelow hγ x) ⟨t, ht⟩

/-- `B_γ(x) ≥ -d(x, γ(0))`, inherited from the same bound on each `B_{γ,t}(x)`. -/
theorem neg_dist_le_busemann {γ : ℝ → M} (hγ : IsGeodesicRay γ) (x : M) :
    -dist x (γ 0) ≤ busemann γ x :=
  le_ciInf fun t => neg_dist_le_busemannAux hγ x t.2

/-- The defining property of the Busemann function: `B_{γ,t}(x) → B_γ(x)` as `t → ∞`.
Since `t ↦ B_{γ,t}(x)` is antitone and bounded below on `[0, ∞)`, this is monotone
convergence to the infimum. -/
theorem tendsto_busemannAux_atTop {γ : ℝ → M} (hγ : IsGeodesicRay γ) (x : M) :
    Tendsto (fun t => busemannAux γ t x) atTop (𝓝 (busemann γ x)) :=
  tendsto_comp_val_Ici_atTop.mp
    (tendsto_atTop_ciInf (Set.antitoneOn_iff_antitone.mp (busemannAux_antitoneOn hγ x))
      (busemannAux_bddBelow hγ x))

/-- The Busemann function `B_γ` is `1`-Lipschitz: for all `x, y` and `t ≥ 0`,
`B_γ(x) ≤ B_{γ,t}(x) ≤ B_{γ,t}(y) + d(x,y)`, so taking the infimum over `t` on the right
gives `B_γ(x) ≤ B_γ(y) + d(x,y)`; symmetrically for the other direction. -/
theorem lipschitzWith_busemann {γ : ℝ → M} (hγ : IsGeodesicRay γ) : LipschitzWith 1 (busemann γ) := by
  apply LipschitzWith.of_le_add
  intro x y
  have key : busemann γ x - dist x y ≤ busemann γ y := by
    apply le_ciInf
    rintro ⟨t, ht⟩
    have h1 : busemann γ x ≤ busemannAux γ t x := busemann_le_busemannAux hγ x ht
    have h2 : dist (γ t) x ≤ dist (γ t) y + dist x y := by
      calc dist (γ t) x ≤ dist (γ t) y + dist y x := dist_triangle _ _ _
        _ = dist (γ t) y + dist x y := by rw [dist_comm y x]
    show busemann γ x - dist x y ≤ busemannAux γ t y
    show busemann γ x - dist x y ≤ dist (γ t) y - t
    have h1' : busemann γ x ≤ dist (γ t) x - t := h1
    linarith
  linarith

/-- `B_γ(γ(s)) = -s` for `s ≥ 0`: the Busemann function measures (minus) arclength along
its own ray. The upper bound is `B_γ(γ(s)) ≤ B_{γ,s}(γ(s)) = d(γ(s),γ(s)) - s = -s`; the
lower bound follows since `B_{γ,t}(γ(s)) = |t - s| - t ≥ -s` for every `t ≥ 0`. -/
theorem busemann_apply_ray {γ : ℝ → M} (hγ : IsGeodesicRay γ) {s : ℝ} (hs : 0 ≤ s) :
    busemann γ (γ s) = -s := by
  apply le_antisymm
  · have heq : busemannAux γ s (γ s) = -s := by
      show dist (γ s) (γ s) - s = -s
      rw [dist_self]; ring
    have h := busemann_le_busemannAux hγ (γ s) hs
    rwa [heq] at h
  · apply le_ciInf
    rintro ⟨t, ht⟩
    show -s ≤ dist (γ t) (γ s) - t
    rw [hγ ht hs]
    rcases le_total t s with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith

end MorganTianLib
