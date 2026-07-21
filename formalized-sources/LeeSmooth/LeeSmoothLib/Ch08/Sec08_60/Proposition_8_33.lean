import LeeSmoothLib.Ch08.Sec08_60.Definition_8_60_extra_1
import LeeSmoothLib.Ch08.Sec08_59.Corollary_8_31
open scoped ContDiff Manifold
open VectorField

noncomputable section

section

universe uH uE uG

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : ModelWithCorners ℝ E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [LieGroup I ∞ G]

-- Domain sampling pass:
-- * primary domain: left-invariant vector fields on Lie groups and the manifold Lie bracket;
-- * source-facing owner: `IsLeftInvariant`;
-- * core/canonical bracket owner: `mlieBracket`, exposed via `⁅X, Y⁆`;
-- * dependency-facing bridge: `pushforward_mlieBracket` for diffeomorphism pushforwards of
--   smooth Lie brackets.
-- Source alignment note: Proposition 8.33 sits in Lee's real-manifold setting and depends on
-- Corollary 8.31, which in this chapter is formalized over `ℝ`; the smoothness of `X` and `Y`
-- therefore remains explicit in the statement instead of being removed via later Corollary 8.38.

/-- Proposition 8.33: Let `G` be a Lie group, and suppose `X` and `Y` are smooth left-invariant
vector fields on `G`. Then `[X, Y]` is also left-invariant. -/
theorem isLeftInvariant_mlieBracket
    {X Y : ∀ g : G, TangentSpace I g}
    (hX_smooth : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X))
    (hY_smooth : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% Y))
    (hX_left_invariant : IsLeftInvariant X)
    (hY_left_invariant : IsLeftInvariant Y) :
    IsLeftInvariant ⁅X, Y⁆ := by
  -- Route correction: use `f_related_mlieBracket` with the `mfderiv` characterization of
  -- left-invariance, instead of extracting pointwise differentiability from `ContMDiff`.
  refine (VectorField.isLeftInvariant_iff_mfderiv (I := I) (G := G) ⁅X, Y⁆).2 ?_
  intro g g'
  have hX_related : VectorField.f_related (fun x : G ↦ g * x) X X := by
    constructor
    · simpa using (contMDiff_mul_left (I := I) (a := g) :
        ContMDiff I I ∞ (fun x : G ↦ g * x))
    · -- Left-invariance says left translation pushes `X` forward to itself.
      intro p
      exact (VectorField.isLeftInvariant_iff_mfderiv (I := I) (G := G) X).1 hX_left_invariant g p
  have hY_related : VectorField.f_related (fun x : G ↦ g * x) Y Y := by
    constructor
    · simpa using (contMDiff_mul_left (I := I) (a := g) :
        ContMDiff I I ∞ (fun x : G ↦ g * x))
    · -- The same left-translation formula holds for `Y`.
      intro p
      exact (VectorField.isLeftInvariant_iff_mfderiv (I := I) (G := G) Y).1 hY_left_invariant g p
  have hBracket_related :
      VectorField.f_related (fun x : G ↦ g * x) ⁅X, Y⁆ ⁅X, Y⁆ :=
    f_related_mlieBracket hX_smooth hY_smooth hX_smooth hY_smooth hX_related hY_related
  -- Reading the relatedness formula at `g'` gives the required left-invariance identity.
  exact VectorField.f_related_apply hBracket_related g'

end
