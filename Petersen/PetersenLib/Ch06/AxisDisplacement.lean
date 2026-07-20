import PetersenLib.Ch05.Geodesics
import PetersenLib.Ch05.MetricStructure

/-!
# Petersen Ch. 6, §6.2 — axes, periods, displacement functions (GTM 171, 3rd ed.)

Petersen's §6.2 (p. 263), `def:pet-ch6-axis-displacement`. For an isometry `F : M → M`:

* an **axis** for `F` is a geodesic `c : ℝ → M` such that `F ∘ c` is a reparametrization of
  `c`; since isometries carry geodesics to geodesics (and preserve the affine parameter up
  to sign), this forces `F (c t) = c (± t + a)` for some `a ∈ ℝ`;
* if the sign is `-`, then `c (a/2)` is fixed by `F` (`fixedPoint_of_reflectionAxis`);
* when `F (c t) = c (t + a)`, the number `a` is the **period** of `F` with respect to `c`
  — it depends on the parametrization of `c`;
* the **displacement function** of `F` is `δ_F(x) = |x F(x)|`.

These are the definitions that `lem:pet-ch6-axis-existence` (Lemma 6.2.7),
`lem:pet-ch6-deck-transformation-dilation` (Lemma 6.2.8) and ultimately
`thm:pet-ch6-preissmann` consume.

## TRAP (failure memory): `sInf` returns `0` on sets unbounded *below*, not just on `∅`

The obvious reading of "the period" as a `ℝ`-valued function is
`sInf {a | ∀ t, F (c t) = c (t + a)}`. **This is wrong, and wrong exactly where it matters.**
`Real.sInf` is junk-valued (`= 0`) on sets that are not bounded below
(`Real.sInf_of_not_bddBelow`), not merely on the empty set. If `c` is periodic with period
`P > 0` (the case in the deck-transformation / Preissmann setting, after projecting to a
closed geodesic), the set of translation numbers is `{a₀ + k P : k ∈ ℤ}`, which is unbounded
below — so that definition silently returns `0` for precisely the genuine translation axes
the notion exists to serve. A period of `0` says `F` fixes `c` pointwise; that is a false
statement about a nontrivial translation, not a harmless junk value, and Lemma 6.2.8's
"positive minimum" content would be destroyed by it.

The fix here is to take the infimum over **positive** periods:
`axisPeriod F c = sInf {a | 0 < a ∧ ∀ t, F (c t) = c (t + a)}`. That set is bounded below by
`0` by construction, so the infimum is meaningful, and on a periodic axis it selects the
smallest positive translation number — the period in the intended sense. This matches the
blueprint's use: Petersen's period is the *displacement* along the axis, which is positive
(Lemma 6.2.7 produces an axis of period `1` from a unit-speed segment realizing the positive
minimal displacement `δ_F(p)`).

Two residual honesty notes about `axisPeriod`, which is why the `Prop`-valued
`IsAxisPeriod` below is the *faithful* rendering of the blueprint and `axisPeriod` is a
*selection* from it:

* if `F` translates **backwards** along `c` (every period negative, e.g. `F` is the inverse
  translation and `c` is injective), the positive-period set is empty and `axisPeriod`
  returns `0`, which is junk. Consumers must supply a positive period; `axisPeriod_le`
  is the intended interface, and `IsAxisPeriod` is available for statements that should not
  depend on any selection at all.
* the blueprint itself does not claim `a` is unique — it explicitly says the period depends
  on the parametrization — so no `ℝ`-valued definition can be more than a choice. Prefer
  `IsAxisPeriod` in statements; use `axisPeriod` only where a numeral is genuinely wanted.
-/

open Set
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen §6.2 (p. 263), `def:pet-ch6-axis-displacement`: the **displacement
function** of a map `F : M → M` is `δ_F(x) = |x F(x)|`, the Riemannian distance from `x` to
its image.

No isometry hypothesis is imposed: `δ_F` makes sense for any `F`, and the isometry
assumption belongs to the theorems about it (Lemma 6.2.7 needs it, and asks moreover that
`δ_F` attain a *positive minimum*). The distance is Ch. 5's `riemannianDistance`, the
infimum of lengths of joining curves. -/
def displacementFunction (g : RiemannianMetric I M) (F : M → M) (x : M) : ℝ :=
  riemannianDistance (I := I) g x (F x)

/-- **Math.** Petersen §6.2 (p. 263), `def:pet-ch6-axis-displacement`: `c` is an **axis** for
`F` when `c` is a geodesic (on all of `ℝ`) whose image is preserved by `F` up to
reparametrization, i.e. `F (c t) = c (ε t + a)` with `ε = ±1`.

The `ε = ±1` shape is not an extra assumption but Petersen's derivation made explicit: an
isometry sends geodesics to geodesics *preserving the affine parameter*, so `F ∘ c` is a
geodesic with the same speed as `c` and the same image, hence differs from `c` by an
orientation-preserving or -reversing translation of the parameter. Encoding the conclusion
directly keeps the definition usable without first formalizing "reparametrization".

The two branches are genuinely different phenomena: `ε = 1` is a *translation* along `c`
(the Preissmann case, with `a` the period), while `ε = -1` is a *reflection* and forces a
fixed point at `c (a/2)` — see `fixedPoint_of_reflectionAxis`. -/
def IsAxis (g : RiemannianMetric I M) (F : M → M) (c : ℝ → M) : Prop :=
  IsGeodesic (I := I) g c ∧ ∃ ε a : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ t : ℝ, F (c t) = c (ε * t + a)

/-- **Math.** Petersen §6.2 (p. 263), `def:pet-ch6-axis-displacement`: `a` is a **period** of
`F` with respect to the geodesic `c` when `F (c t) = c (t + a)` for all `t`, i.e. `c` is a
translation axis (the `ε = 1` branch of `IsAxis`) with translation number `a`.

This `Prop` is the faithful rendering of the blueprint's sentence "when `F ∘ c(t) = c(t+a)`,
`a` is the period of `F` with respect to `c`". Petersen asserts no uniqueness — he notes the
period depends on the parametrization, and on a periodic `c` there are infinitely many valid
`a` differing by the period of `c`. Statements should therefore prefer `IsAxisPeriod` and
take `a` as data; `axisPeriod` below makes a canonical *choice* and carries the caveats. -/
def IsAxisPeriod (g : RiemannianMetric I M) (F : M → M) (c : ℝ → M) (a : ℝ) : Prop :=
  IsGeodesic (I := I) g c ∧ ∀ t : ℝ, F (c t) = c (t + a)

/-- **Math.** Petersen §6.2 (p. 263), `def:pet-ch6-axis-displacement`: the **period** of `F`
with respect to `c`, selected as the infimum of the *positive* periods.

The restriction to positive periods is mandatory. See the module docstring: over *all*
periods the infimum is junk (`= 0`) on any periodic axis, because `Real.sInf` collapses to
`0` on sets unbounded below — which would report "F fixes c pointwise" for exactly the
nontrivial translations of the Preissmann setting. Positive periods are bounded below by `0`
by construction, so this infimum is meaningful, and Petersen's periods are positive anyway
(they are displacements: Lemma 6.2.7 builds an axis of period `1` out of a unit-speed
segment realizing a positive minimal displacement).

`g` is not a parameter: the translation condition is purely about `F` and `c`, and the
geodesic hypothesis lives in `IsAxisPeriod`/`IsAxis`. Junk value `0` when there is no
positive period (e.g. `F` translates backwards along an injective `c`); use
`axisPeriod_le` and `IsAxisPeriod` rather than reading this number unconditionally. -/
def axisPeriod (F : M → M) (c : ℝ → M) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∀ t : ℝ, F (c t) = c (t + a)}

/-- **Math.** The selected period is never negative: the set it infimizes lies in `(0, ∞)`,
and on the degenerate case where that set is empty the `Real.sInf` junk value is `0`. -/
theorem axisPeriod_nonneg (F : M → M) (c : ℝ → M) : 0 ≤ axisPeriod F c :=
  Real.sInf_nonneg (fun _ hx => le_of_lt hx.1)

/-- **Math.** The intended interface to `axisPeriod`: any *positive* period dominates the
selected one. This is what makes `axisPeriod` usable without knowing the positive-period set
is nonempty at the call site — a consumer that exhibits one positive period `a` immediately
gets `axisPeriod F c ≤ a`. -/
theorem axisPeriod_le {F : M → M} {c : ℝ → M} {a : ℝ} (ha : 0 < a)
    (h : ∀ t : ℝ, F (c t) = c (t + a)) : axisPeriod F c ≤ a :=
  csInf_le ⟨0, fun _ hx => le_of_lt hx.1⟩ ⟨ha, h⟩

/-- **Math.** A translation axis is an axis: the `ε = 1` branch of `IsAxis`. This records
that `IsAxisPeriod` is a strengthening, not a variant. -/
theorem IsAxisPeriod.isAxis {g : RiemannianMetric I M} {F : M → M} {c : ℝ → M} {a : ℝ}
    (h : IsAxisPeriod (I := I) g F c a) : IsAxis (I := I) g F c :=
  ⟨h.1, 1, a, Or.inl rfl, fun t => by simpa using h.2 t⟩

/-- **Math.** Petersen §6.2 (p. 263), `def:pet-ch6-axis-displacement`: on the reflecting
branch of an axis — `F (c t) = c (-t + a)` — the midpoint `c (a/2)` is **fixed** by `F`.

This is the sentence "if the sign is `-`, `c(a/2)` is fixed by `F`", and it is the reason
Preissmann-type arguments may discard the `ε = -1` branch: a deck transformation acting
freely cannot have a fixed point, so its axes are translations. The proof is the
computation `-(a/2) + a = a/2`; no geodesic hypothesis is used. -/
theorem fixedPoint_of_reflectionAxis {F : M → M} {c : ℝ → M} {a : ℝ}
    (h : ∀ t : ℝ, F (c t) = c (-t + a)) : F (c (a / 2)) = c (a / 2) := by
  rw [h (a / 2)]
  congr 1
  ring

end PetersenLib
