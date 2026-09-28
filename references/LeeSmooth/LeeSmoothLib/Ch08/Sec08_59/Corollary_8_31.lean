import LeeSmoothLib.Ch08.Sec08_57.Proposition_8_19
import LeeSmoothLib.Ch08.Sec08_59.Proposition_8_30
open scoped ContDiff Manifold

noncomputable section

section

universe uE uE' uH uH' uM uN

-- Domain sampling pass:
-- * primary domain: smooth vector fields on manifolds under diffeomorphism pushforward;
-- * relevant owner-style declarations sampled upstream: `VectorField.mpullback`,
--   `VectorField.mpullback_mlieBracket`, and `ContMDiff.mpullback_vectorField`;
-- * bridge/view syntax sampled in the chapter: `F _* X`, expanding to `VectorField.mpullback`
--   along `F.symm`;
-- * derived local surface: this corollary is the pushforward-form restatement of Lie-bracket
--   naturality in the chapter's diffeomorphism-pushforward notation.
-- Primitive data is only the diffeomorphism `F` and the smooth vector fields `X₁`, `X₂`; the
-- pushforward itself is derived from the canonical pullback owner along `F.symm`.

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N]

/-- Corollary 8.31 (Pushforwards of Lie Brackets): if `F : M ≃ₘ⟮I, J⟯ N` is a diffeomorphism and
`X₁`, `X₂` are smooth vector fields on `M`, then the pushforward of their Lie bracket is the Lie
bracket of their pushforwards. -/
theorem pushforward_mlieBracket
    (F : M ≃ₘ⟮I, J⟯ N)
    {X₁ X₂ : ∀ p : M, TangentSpace I p}
    (hX₁ : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X₁))
    (hX₂ : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X₂)) :
    (F _* (⁅X₁, X₂⁆)) = ⁅F _* X₁, F _* X₂⁆ := by
  -- Route correction: use the chapter-level `f_related` naturality theorem and the uniqueness
  -- characterization of pushforward, rather than unfolding the generic pullback construction.
  have hFX₁ :
      ContMDiff J J.tangent (∞ : ℕ∞ω) (T% (((F _* X₁) : ∀ q : N, TangentSpace J q))) :=
    contMDiff_pushforward_of_diffeomorph F hX₁
  have hFX₂ :
      ContMDiff J J.tangent (∞ : ℕ∞ω) (T% (((F _* X₂) : ∀ q : N, TangentSpace J q))) :=
    contMDiff_pushforward_of_diffeomorph F hX₂
  have hrel₁ :
      VectorField.f_related F X₁ (((F _* X₁) : ∀ q : N, TangentSpace J q)) :=
    f_related_pushforward_of_diffeomorph F X₁
  have hrel₂ :
      VectorField.f_related F X₂ (((F _* X₂) : ∀ q : N, TangentSpace J q)) :=
    f_related_pushforward_of_diffeomorph F X₂
  -- Naturality promotes the two relatedness facts to the bracket level.
  have hBracket :
      VectorField.f_related F (⁅X₁, X₂⁆)
        (⁅((F _* X₁) : ∀ q : N, TangentSpace J q), ((F _* X₂) : ∀ q : N, TangentSpace J q)⁆) :=
    f_related_mlieBracket hX₁ hX₂ hFX₁ hFX₂ hrel₁ hrel₂
  -- The pushforward is the unique target vector field that is `F`-related to the source bracket.
  exact (eq_pushforward_of_f_related F hBracket).symm

end
