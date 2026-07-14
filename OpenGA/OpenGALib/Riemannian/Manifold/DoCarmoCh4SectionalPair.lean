import OpenGALib.Riemannian.Manifold.DoCarmoCh4Sectional

/-!
# do Carmo Chapter 4 §3 — sectional curvature is independent of the orthonormal pair

The (unnormalized) sectional-curvature numerator of an algebraic curvature form
takes the same value on any two orthonormal pairs spanning the same plane —
the well-definedness of the Gaussian curvature of a 2-plane. Reference: do Carmo,
*Riemannian Geometry*, Ch. 4 §3 (basis independence of sectional curvature), used by
Ch. 6 (Theorema Egregium).

* `linearIndependent_pair_of_orthonormal` — an orthonormal pair is linearly independent.
* `IsAlgCurvatureForm.apply_eq_of_orthonormal_of_mem_span` — if `u₁,u₂` and `v₁,v₂` are
  each orthonormal pairs with `v₁,v₂ ∈ span{u₁,u₂}`, then `B(v₁,v₂,v₁,v₂) = B(u₁,u₂,u₁,u₂)`.
  Proved via `sectionalCurvature_changeBasis`: the change-of-basis matrix `(a b; c d)`
  expressing `v₁,v₂` in terms of `u₁,u₂` satisfies `(ad-bc)² = 1` by the Lagrange identity,
  so both `|u₁∧u₂|²` and `|v₁∧v₂|²` equal `1` and the sectional-curvature identity reduces
  to the bare numerators.
* `IsAlgCurvatureForm.apply_eq_of_orthonormal_of_finrank_eq_two` — when `dim V = 2` the span
  hypotheses are automatic (any orthonormal pair spans), giving the well-definedness of the
  Gaussian curvature of a 2-dimensional tangent space.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4 §3.
-/

open scoped RealInnerProductSpace

namespace Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** An orthonormal pair `u₁, u₂` is linearly independent: pairing a vanishing
combination `s•u₁ + t•u₂ = 0` with `u₁` and with `u₂` kills each coefficient in turn. -/
theorem linearIndependent_pair_of_orthonormal {u₁ u₂ : V}
    (hu₁ : inner ℝ u₁ u₁ = (1:ℝ)) (hu₂ : inner ℝ u₂ u₂ = (1:ℝ))
    (hu₁₂ : inner ℝ u₁ u₂ = (0:ℝ)) : LinearIndependent ℝ ![u₁, u₂] := by
  have hu₂₁ : inner ℝ u₂ u₁ = (0:ℝ) := by rw [real_inner_comm]; exact hu₁₂
  rw [LinearIndependent.pair_iff]
  intro s t hst
  refine ⟨?_, ?_⟩
  · have h1 : inner ℝ (s • u₁ + t • u₂) u₁ = (0:ℝ) := by rw [hst]; exact inner_zero_left u₁
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hu₁, hu₂₁] at h1
    linarith
  · have h2 : inner ℝ (s • u₁ + t • u₂) u₂ = (0:ℝ) := by rw [hst]; exact inner_zero_left u₂
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hu₁₂, hu₂] at h2
    linarith

/-- **Math.** do Carmo Ch. 4 §3: the sectional-curvature numerator `B(x,y,x,y)` of an
algebraic curvature form is the same on any two orthonormal pairs spanning the same plane.
If `u₁,u₂` and `v₁,v₂` are both orthonormal and `v₁,v₂` lie in `span{u₁,u₂}`, write
`v₁ = a•u₁+b•u₂`, `v₂ = c•u₁+d•u₂`; orthonormality of `v₁,v₂` forces
`a²+b²=1`, `c²+d²=1`, `ac+bd=0`, and the Lagrange identity
`(ad-bc)² = (a²+b²)(c²+d²)-(ac+bd)²` gives `(ad-bc)²=1`, in particular `ad-bc ≠ 0` and
`u₁,u₂` linearly independent. `sectionalCurvature_changeBasis` then shows `K(v₁,v₂)=K(u₁,u₂)`,
and since both `|u₁∧u₂|²` and `|v₁∧v₂|²` equal `1` (orthonormality), the numerators agree. -/
theorem IsAlgCurvatureForm.apply_eq_of_orthonormal_of_mem_span
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    {u₁ u₂ v₁ v₂ : V}
    (hu₁ : inner ℝ u₁ u₁ = (1:ℝ)) (hu₂ : inner ℝ u₂ u₂ = (1:ℝ))
    (hu₁₂ : inner ℝ u₁ u₂ = (0:ℝ))
    (hv₁ : inner ℝ v₁ v₁ = (1:ℝ)) (hv₂ : inner ℝ v₂ v₂ = (1:ℝ))
    (hv₁₂ : inner ℝ v₁ v₂ = (0:ℝ))
    (hv₁span : v₁ ∈ Submodule.span ℝ {u₁, u₂})
    (hv₂span : v₂ ∈ Submodule.span ℝ {u₁, u₂}) :
    B v₁ v₂ v₁ v₂ = B u₁ u₂ u₁ u₂ := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv₁span
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hv₂span
  have hu₂₁ : inner ℝ u₂ u₁ = (0:ℝ) := by rw [real_inner_comm]; exact hu₁₂
  -- bilinear expansion of the inner product of two combinations of `u₁, u₂`
  have expand : ∀ p q r s : ℝ,
      inner ℝ (p • u₁ + q • u₂) (r • u₁ + s • u₂)
        = p * r * (inner ℝ u₁ u₁) + p * s * (inner ℝ u₁ u₂)
          + q * r * (inner ℝ u₂ u₁) + q * s * (inner ℝ u₂ u₂) := by
    intro p q r s
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    ring
  -- scalar identities coming from orthonormality of `v₁, v₂`
  have ha : a * a + b * b = 1 := by
    have h := hv₁
    rw [← hab, expand, hu₁, hu₂, hu₁₂, hu₂₁] at h
    linear_combination h
  have hc : c * c + d * d = 1 := by
    have h := hv₂
    rw [← hcd, expand, hu₁, hu₂, hu₁₂, hu₂₁] at h
    linear_combination h
  have hac : a * c + b * d = 0 := by
    have h := hv₁₂
    rw [← hab, ← hcd, expand, hu₁, hu₂, hu₁₂, hu₂₁] at h
    linear_combination h
  -- Lagrange identity: `(ad-bc)² = 1`, hence `ad - bc ≠ 0`
  have hdet2 : (a * d - b * c) ^ 2 = 1 := by
    have hlag : (a * d - b * c) ^ 2
        = (a * a + b * b) * (c * c + d * d) - (a * c + b * d) ^ 2 := by ring
    rw [hlag, ha, hc, hac]; ring
  have hdet : a * d - b * c ≠ 0 := by
    intro h0
    rw [h0] at hdet2
    norm_num at hdet2
  -- `u₁, u₂` are linearly independent
  have hLI : LinearIndependent ℝ ![u₁, u₂] :=
    linearIndependent_pair_of_orthonormal hu₁ hu₂ hu₁₂
  -- apply basis independence of the sectional curvature and unfold the (trivial) denominators
  have hSC := hB.sectionalCurvature_changeBasis hdet u₁ u₂ hLI
  rw [hab, hcd] at hSC
  have hwU : wedgeSq u₁ u₂ = 1 := by unfold wedgeSq; rw [hu₁, hu₂, hu₁₂]; ring
  have hwV : wedgeSq v₁ v₂ = 1 := by unfold wedgeSq; rw [hv₁, hv₂, hv₁₂]; ring
  unfold sectionalCurvature at hSC
  rw [hwU, hwV, div_one, div_one] at hSC
  exact hSC

/-- **Math.** do Carmo Ch. 4 §3, two-dimensional case (as used in Ch. 6, Theorema
Egregium): on a 2-dimensional inner product space every orthonormal pair spans, so the
sectional-curvature numerator `B(·,·,·,·)` of an algebraic curvature form takes the same
value on *any* two orthonormal pairs — the Gaussian curvature is well defined. The span
hypotheses of `apply_eq_of_orthonormal_of_mem_span` are discharged because a linearly
independent pair (`linearIndependent_pair_of_orthonormal`) of `2 = dim V` vectors spans. -/
theorem IsAlgCurvatureForm.apply_eq_of_orthonormal_of_finrank_eq_two
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (hdim : Module.finrank ℝ V = 2)
    {u₁ u₂ v₁ v₂ : V}
    (hu₁ : inner ℝ u₁ u₁ = (1:ℝ)) (hu₂ : inner ℝ u₂ u₂ = (1:ℝ))
    (hu₁₂ : inner ℝ u₁ u₂ = (0:ℝ))
    (hv₁ : inner ℝ v₁ v₁ = (1:ℝ)) (hv₂ : inner ℝ v₂ v₂ = (1:ℝ))
    (hv₁₂ : inner ℝ v₁ v₂ = (0:ℝ)) :
    B v₁ v₂ v₁ v₂ = B u₁ u₂ u₁ u₂ := by
  have hLI : LinearIndependent ℝ ![u₁, u₂] :=
    linearIndependent_pair_of_orthonormal hu₁ hu₂ hu₁₂
  have htop : Submodule.span ℝ ({u₁, u₂} : Set V) = ⊤ := by
    have h := hLI.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])
    rwa [Matrix.range_cons_cons_empty] at h
  have hv₁span : v₁ ∈ Submodule.span ℝ ({u₁, u₂} : Set V) := by
    rw [htop]; exact Submodule.mem_top
  have hv₂span : v₂ ∈ Submodule.span ℝ ({u₁, u₂} : Set V) := by
    rw [htop]; exact Submodule.mem_top
  exact hB.apply_eq_of_orthonormal_of_mem_span hu₁ hu₂ hu₁₂ hv₁ hv₂ hv₁₂ hv₁span hv₂span

end Riemannian
