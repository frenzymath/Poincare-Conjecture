import HatcherLib.Ch0.MappingCylinder
import HatcherLib.Ch0.HomotopyExtensionRel

/-!
# Chapter 0 — The pair `(M_f, X)` has the homotopy extension property

Hatcher's Corollary 0.21 needs the homotopy extension property of the pair
`(M_f, X)`, where `X` sits inside the mapping cylinder as the bottom `X × {0}`.
Hatcher obtains it from the mapping-cylinder neighborhood `X × [0, 1/2]`
(blueprint `ex:mapping-cylinder-neighborhood-hep`); here we prove it by a direct
formula.

The geometric picture: project the square `I × I` (cylinder coordinate `s`,
homotopy time `t`) radially from the external point `(1, 2)` onto the union of
the bottom edge `I × {0}` and the left edge `{0} × I`. The ray through `(s, t)`
exits through the left edge when `t ≥ 2s` (at height `(t - 2s)/(1 - s)`) and
through the bottom edge when `t ≤ 2s` (at abscissa `(2s - t)/(2 - t)`). Three
features make this the right projection:

* the bottom edge is fixed (`(s, 0) ↦ (s, 0)`), so the extension restricts to
  the given map at time `0`;
* the left edge is fixed (`(0, t) ↦ (0, t)`), so the extension restricts to the
  given homotopy on `X`;
* the whole right edge collapses to the corner (`(1, t) ↦ (1, 0)`), so the
  formula is constant along the seam `X × {1}` of the mapping cylinder and
  descends to the quotient `M_f` — this is where the collar `X × [0, 1/2]`
  is implicitly used: the region `t ≥ 2s` that reads the homotopy touches only
  `s ≤ 1/2`.

Main result:

* `HatcherLib.hasHEPMap_mcylInclX` — **`(M_f, X)` has the homotopy extension
  property** (map form, along the inclusion `i : X → M_f`).
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

/-! ## The radial projection of the square from `(1, 2)` -/

/-- The bottom-edge coordinate of the radial projection of the square from the
external point `(1, 2)`: `(s, t) ↦ (2s - t)/(2 - t)`, clipped to `I`. Meaningful
on the region `t ≤ 2s`, where the ray from `(1, 2)` through `(s, t)` exits the
square through the bottom edge at `((2s - t)/(2 - t), 0)`. -/
noncomputable def mcylHepDown : C(I × I, I) where
  toFun st := Set.projIcc 0 1 zero_le_one ((2 * (st.1 : ℝ) - (st.2 : ℝ)) / (2 - (st.2 : ℝ)))
  continuous_toFun := continuous_projIcc.comp <| Continuous.div (by fun_prop) (by fun_prop)
    fun st => ne_of_gt (by have := unitInterval.le_one st.2; linarith)

theorem mcylHepDown_coe {s t : I} (h : (t : ℝ) ≤ 2 * (s : ℝ)) :
    (mcylHepDown (s, t) : ℝ) = (2 * (s : ℝ) - (t : ℝ)) / (2 - (t : ℝ)) := by
  have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
  have hs1 : (s : ℝ) ≤ 1 := unitInterval.le_one s
  show (Set.projIcc (0 : ℝ) 1 zero_le_one _ : ℝ) = _
  rw [Set.projIcc_of_mem]
  rw [Set.mem_Icc]
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_le_one (by linarith)]; linarith

/-- The bottom edge is fixed: `(s, 0) ↦ s`. -/
theorem mcylHepDown_zero (s : I) : mcylHepDown (s, 0) = s := by
  apply Subtype.ext
  have c0 : ((0 : I) : ℝ) = 0 := rfl
  rw [mcylHepDown_coe (by rw [c0]; have := unitInterval.nonneg s; linarith), c0]
  ring

/-- The right edge collapses to the corner: `(1, t) ↦ 1`. This is what lets the
extension formula descend through the mapping-cylinder identification
`(x, 1) ∼ f x`. -/
theorem mcylHepDown_one (t : I) : mcylHepDown (1, t) = 1 := by
  apply Subtype.ext
  have c1 : ((1 : I) : ℝ) = 1 := rfl
  have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
  rw [mcylHepDown_coe (by rw [c1]; linarith), c1]
  rw [show 2 * (1 : ℝ) - (t : ℝ) = 2 - (t : ℝ) by ring]
  exact div_self (ne_of_gt (by linarith))

/-- On the seam `t = 2s` between the two regions, the bottom-edge coordinate is `0`. -/
theorem mcylHepDown_seam {s t : I} (h : (t : ℝ) = 2 * (s : ℝ)) : mcylHepDown (s, t) = 0 := by
  apply Subtype.ext
  show (Set.projIcc (0 : ℝ) 1 zero_le_one
    ((2 * (s : ℝ) - (t : ℝ)) / (2 - (t : ℝ))) : ℝ) = ((0 : I) : ℝ)
  rw [show 2 * (s : ℝ) - (t : ℝ) = 0 by linarith, zero_div, Set.projIcc_left]
  rfl

/-- The left-edge coordinate of the radial projection of the square from `(1, 2)`:
`(s, t) ↦ (t - 2s)/(1 - s)`, clipped to `I`. Meaningful on the region `t ≥ 2s`,
where the ray exits through the left edge at `(0, (t - 2s)/(1 - s))`; the
denominator is implemented as `max (1 - s) ((2 - t)/2)` — equal to `1 - s` on
that region — so that it stays bounded below by `1/2` on all of `I × I`. -/
noncomputable def mcylHepAcross : C(I × I, I) where
  toFun st := Set.projIcc 0 1 zero_le_one
    (((st.2 : ℝ) - 2 * (st.1 : ℝ)) / max (1 - (st.1 : ℝ)) ((2 - (st.2 : ℝ)) / 2))
  continuous_toFun := continuous_projIcc.comp <| Continuous.div (by fun_prop) (by fun_prop)
    fun st => ne_of_gt (lt_max_of_lt_right (by have := unitInterval.le_one st.2; linarith))

theorem mcylHepAcross_coe {s t : I} (h : 2 * (s : ℝ) ≤ (t : ℝ)) :
    (mcylHepAcross (s, t) : ℝ) = ((t : ℝ) - 2 * (s : ℝ)) / (1 - (s : ℝ)) := by
  have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := unitInterval.nonneg s
  have hs : (s : ℝ) ≤ 1 / 2 := by linarith
  have hmax : max (1 - (s : ℝ)) ((2 - (t : ℝ)) / 2) = 1 - (s : ℝ) :=
    max_eq_left (by linarith)
  show (Set.projIcc (0 : ℝ) 1 zero_le_one _ : ℝ) = _
  rw [hmax, Set.projIcc_of_mem]
  rw [Set.mem_Icc]
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_le_one (by linarith)]; linarith

/-- The left edge is fixed: `(0, t) ↦ t`. -/
theorem mcylHepAcross_zero (t : I) : mcylHepAcross (0, t) = t := by
  apply Subtype.ext
  have c0 : ((0 : I) : ℝ) = 0 := rfl
  rw [mcylHepAcross_coe (by rw [c0]; have := unitInterval.nonneg t; linarith), c0]
  ring

/-- On the seam `t = 2s`, the left-edge coordinate is `0`. -/
theorem mcylHepAcross_seam {s t : I} (h : (t : ℝ) = 2 * (s : ℝ)) : mcylHepAcross (s, t) = 0 := by
  apply Subtype.ext
  show (Set.projIcc (0 : ℝ) 1 zero_le_one
    (((t : ℝ) - 2 * (s : ℝ)) / max (1 - (s : ℝ)) ((2 - (t : ℝ)) / 2)) : ℝ) = ((0 : I) : ℝ)
  rw [show (t : ℝ) - 2 * (s : ℝ) = 0 by linarith, zero_div, Set.projIcc_left]
  rfl

/-! ## The homotopy extension property of `(M_f, X)` -/

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The pair `(M_f, X)` has the homotopy extension property** (Hatcher's input to
Corollary 0.21, an instance of the mapping-cylinder-neighborhood criterion of
blueprint `ex:mapping-cylinder-neighborhood-hep` with the collar `X × [0, 1/2]`).

Given `φ : M_f → Z` and a homotopy `h : X × I → Z` of `φ ∘ i`, the extension at
`([x, s], t)` reads `φ` at the radial projection of `(s, t)` from `(1, 2)` onto
the bottom edge when `t ≤ 2s`, and reads `h` at the left-edge projection when
`t ≥ 2s`; points of `Y` stay constant at `φ`. The right-edge collapse
`mcylHepDown_one` makes this well defined on the quotient. -/
theorem hasHEPMap_mcylInclX (f : C(X, Y)) : HasHEPMap (mcylInclX f) := by
  intro Z _ φ h hcompat
  classical
  -- The extension on the cylinder part `(X × I) × I`, glued along the seam `t = 2s`.
  let G : (X × I) × I → Z := fun q =>
    if (q.2 : ℝ) ≤ 2 * (q.1.2 : ℝ)
    then φ (mcylMk f (Sum.inl (q.1.1, mcylHepDown (q.1.2, q.2))))
    else h (q.1.1, mcylHepAcross (q.1.2, q.2))
  have hGdown : ∀ (x : X) (s t : I), (t : ℝ) ≤ 2 * (s : ℝ) →
      G ((x, s), t) = φ (mcylMk f (Sum.inl (x, mcylHepDown (s, t)))) :=
    fun _ _ _ hle => if_pos hle
  have hGacross : ∀ (x : X) (s t : I), ¬ (t : ℝ) ≤ 2 * (s : ℝ) →
      G ((x, s), t) = h (x, mcylHepAcross (s, t)) :=
    fun _ _ _ hgt => if_neg hgt
  have hG_cont : Continuous G := by
    refine Continuous.if_le ?_ ?_ (by fun_prop) (by fun_prop) ?_
    · exact (map_continuous φ).comp <| (map_continuous (mcylMk f)).comp <|
        continuous_inl.comp <| (continuous_fst.comp continuous_fst).prodMk <|
          (map_continuous mcylHepDown).comp <|
            (continuous_snd.comp continuous_fst).prodMk continuous_snd
    · exact (map_continuous h).comp <| (continuous_fst.comp continuous_fst).prodMk <|
        (map_continuous mcylHepAcross).comp <|
          (continuous_snd.comp continuous_fst).prodMk continuous_snd
    · intro q hq
      rw [mcylHepDown_seam hq, mcylHepAcross_seam hq]
      exact (hcompat q.1.1).symm
  -- The extension upstairs on `((X × I) ⊕ Y) × I`, packaged with `I` first for the
  -- quotient-lifting lemma.
  let Gtil : C(I × ((X × I) ⊕ Y), Z) :=
    ⟨fun p => p.2.elim (fun q => G (q, p.1)) fun y => φ (mcylMk f (Sum.inr y)), by
      have key : Continuous fun w : ((X × I) ⊕ Y) × I =>
          (w.1.elim (fun q => G (q, w.2)) fun y => φ (mcylMk f (Sum.inr y)) : Z) :=
        continuous_sumProd hG_cont
          (by exact ((map_continuous φ).comp <| (map_continuous (mcylMk f)).comp <|
            continuous_inr.comp continuous_fst :
              Continuous fun p : Y × I => φ (mcylMk f (Sum.inr p.1))))
      exact key.comp (by fun_prop : Continuous fun p : I × ((X × I) ⊕ Y) => (p.2, p.1))⟩
  have hGtil_inl : ∀ (t : I) (x : X) (s : I), Gtil (t, Sum.inl (x, s)) = G ((x, s), t) :=
    fun _ _ _ => rfl
  -- The formula is constant along the seam `(x, 1) ∼ f x`, so it descends to `M_f`.
  have hnorm : ∀ (t : I) (p : (X × I) ⊕ Y), Gtil (t, mcylNorm f p) = Gtil (t, p) := by
    intro t p
    cases p with
    | inr y => rfl
    | inl q =>
      obtain ⟨x, s⟩ := q
      by_cases hs : (s : ℝ) = 1
      · have h1 : s = 1 := Subtype.ext hs
        subst h1
        rw [mcylNorm_inl_top, hGtil_inl]
        have hle : (t : ℝ) ≤ 2 * ((1 : I) : ℝ) := by
          have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
          have c1 : ((1 : I) : ℝ) = 1 := rfl
          rw [c1]; linarith
        rw [hGdown x 1 t hle, mcylHepDown_one]
        exact congrArg φ (mcylMk_top f x).symm
      · rw [mcylNorm_inl_of_ne f x s hs]
  have hdesc : ∀ (t : I) (a b : (X × I) ⊕ Y), mcylNorm f a = mcylNorm f b →
      Gtil (t, a) = Gtil (t, b) := by
    intro t a b hab
    rw [← hnorm t a, ← hnorm t b, hab]
  -- The descended extension `F : M_f × I → Z`.
  let K : C(I × MappingCylinder f, Z) :=
    ⟨fun p => Quotient.liftOn p.2 (fun a => Gtil (p.1, a)) fun a b hab => hdesc p.1 a b hab, by
      apply (isQuotientMap_quotient_mk').continuous_lift_prod_right
      exact map_continuous Gtil⟩
  refine ⟨K.comp ⟨fun p => (p.2, p.1), by fun_prop⟩, ?_, ?_⟩
  · -- At time `0` the extension is `φ`: the bottom edge is fixed.
    intro m
    induction m using Quotient.ind with
    | _ p =>
      show Gtil (0, p) = φ (mcylMk f p)
      cases p with
      | inr y => rfl
      | inl q =>
        obtain ⟨x, s⟩ := q
        have hle : ((0 : I) : ℝ) ≤ 2 * (s : ℝ) := by
          have hs0 : (0 : ℝ) ≤ (s : ℝ) := unitInterval.nonneg s
          have c0 : ((0 : I) : ℝ) = 0 := rfl
          rw [c0]; linarith
        rw [hGtil_inl, hGdown x s 0 hle, mcylHepDown_zero]
  · -- Along `X` the extension is the prescribed homotopy: the left edge is fixed.
    intro x t
    show Gtil (t, Sum.inl (x, 0)) = h (x, t)
    rw [hGtil_inl]
    have c0 : ((0 : I) : ℝ) = 0 := rfl
    by_cases ht : (t : ℝ) ≤ 2 * ((0 : I) : ℝ)
    · have ht0 : t = 0 := by
        apply Subtype.ext
        rw [c0] at ht ⊢
        exact le_antisymm (by linarith) (unitInterval.nonneg t)
      subst ht0
      rw [hGdown x 0 0 ht, mcylHepDown_zero]
      exact (hcompat x).symm
    · rw [hGacross x 0 t ht, mcylHepAcross_zero]

end HatcherLib
