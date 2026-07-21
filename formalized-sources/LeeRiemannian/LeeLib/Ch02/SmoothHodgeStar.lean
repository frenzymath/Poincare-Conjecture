/-
Chapter 2, "Riemannian Metrics", Problem 2-18(a): **the Hodge star as a bundle homomorphism**
`* : Λ^k T^*M → Λ^{n-k} T^*M` on an oriented Riemannian `n`-manifold.

Lee's Problem 2-18(a) asks for the unique smooth bundle homomorphism `*` satisfying

  `ω ∧ *η = ⟨ω, η⟩_g dV_g`                                                              (Lee 2-18a)

for all smooth `k`-forms `ω, η`, where `⟨·,·⟩_g` is the fibre metric on `k`-forms of Problem 2-16
(`LeeLib.Ch02.RiemannianMetric.innerFormsAt`) and `dV_g` is the Riemannian volume form
(`LeeLib.Ch02.RiemannianMetric.volumeForm`).

The **pointwise** theory of the Hodge star is already complete in `LeeLib.Ch02.HodgeStar`: for an
oriented orthonormal basis `e` and a splitting `k + l = n`, `hodgeStar e h` is the graded star, and
`wedge_hodgeStar`/`eq_hodgeStar_of_forall_wedge_eq` are its characterization and uniqueness.  This
file lifts that pointwise star to the **(g, o)-indexed family over `M`**:

* `RiemannianMetric.hodgeStarAt g o hpos h x` — the star at the point `x`, the pointwise star for
  the canonical positively oriented `g`-orthonormal basis of `T_x M`;
* `hodgeStarAt_wedge` — the characterizing identity (Lee 2-18a), stated against the manifold's own
  `innerFormsAt` and `volumeForm` (`dV_g` in the degree-`(k+l)` reindexing along `finCongr h`);
* `eq_hodgeStarAt_of_forall_wedge` — fibrewise uniqueness, holding among **all** fibrewise families
  satisfying the identity, smooth or not.  This is the uniqueness half of Lee 2-18a.

The remaining, genuinely analytic half — that `x ↦ *η_x` is a smooth section (so `*` is a *smooth*
bundle homomorphism, not merely a fibrewise-linear one) — is the intermediate-degree analogue of
`contMDiff_volumeForm` and is left to a follow-up: unlike the volume form (top degree, where `Λ^n`
is a line and the "top forms are a line" trick of `contMDiffAt_volumeForm` applies), it needs a
smooth intermediate-degree wedge-covector section.  The full route is recorded in the session
handoff.

A positive-dimensional manifold is assumed (`hpos : 0 < finrank ℝ E`): the canonical oriented basis
is produced by `OrthonormalBasis.adjustToOrientation`, which needs a nonempty index.  This matches
Lee's "oriented Riemannian `n`-manifold" with `n ≥ 1`.
-/
import LeeLib.Ch02.HodgeStar
import LeeLib.Ch02.FiberMetricForms
import LeeLib.Ch02.VolumeForm
import LeeLib.Ch02.SmoothCoframeWedge

namespace LeeLib.Ch02

open Bundle Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

/-! ### The oriented volume form as a coframe wedge (fibrewise) -/

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- **The oriented volume form is the wedge of a dual coframe** (fibrewise).  For a positively
oriented orthonormal basis `e`, the orientation's volume form `o.volumeFormL` equals the wedge
`e^1 ∧ ⋯ ∧ e^n` of the dual coframe `e^i = ⟨e_i, ·⟩`.  Both are top forms taking the value `1` on
`e`, and top-degree forms on an `n`-dimensional space are a line. -/
theorem volumeFormL_eq_wedgeCovectors_flatL (o : Orientation ℝ V (Fin n))
    (e : OrthonormalBasis (Fin n) ℝ V) (hor : e.toBasis.orientation = o) :
    o.volumeFormL = wedgeCovectors (fun i => flatL (e i)) := by
  refine (ContinuousAlternatingMap.ext_of_apply_basis_eq e.toBasis ?_).symm
  rw [OrthonormalBasis.coe_toBasis, wedgeCovectors_apply, volumeFormL_apply_eq_one o e hor]
  rw [show (Matrix.of fun i j => flatL (e i) (e j)) = (1 : Matrix (Fin n) (Fin n) ℝ) by
    ext i j; simp [flatL_apply, orthonormal_iff_ite.mp e.orthonormal, Matrix.one_apply]]
  exact Matrix.det_one

/-- **The volume form reindexed to degree `k + l`** is the wedge of the coframe reindexed along
`finCongr h`.  This is the shape in which `dV_g` appears in the Hodge characterization, where the
wedge `ω ∧ *η` lives in degree `k + l` while `dV_g` is a form of degree `n`.  The determinant is
unchanged because reindexing the rows and columns of a matrix by the same bijection preserves its
determinant. -/
theorem camDomDomCongr_volumeFormL (o : Orientation ℝ V (Fin n))
    (e : OrthonormalBasis (Fin n) ℝ V) (hor : e.toBasis.orientation = o) {k l : ℕ} (h : k + l = n) :
    camDomDomCongr (finCongr h).symm o.volumeFormL
      = wedgeCovectors (fun i : Fin (k + l) => flatL (e (finCongr h i))) := by
  rw [volumeFormL_eq_wedgeCovectors_flatL o e hor]
  ext v
  rw [camDomDomCongr_apply, wedgeCovectors_apply, wedgeCovectors_apply]
  have hmat : (Matrix.of fun i j : Fin (k + l) => flatL (e (finCongr h i)) (v j))
      = (Matrix.of fun a b => flatL (e a) (v ((finCongr h).symm b))).submatrix
          (finCongr h) (finCongr h) := by
    ext i j; simp [Matrix.submatrix_apply]
  rw [hmat, Matrix.det_submatrix_equiv_self]

end Pointwise

/-! ### The Hodge star at a point of an oriented Riemannian manifold -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k l : ℕ}

omit [FiniteDimensional ℝ E] in
/-- A finite sum of smooth `l`-form sections is a smooth `l`-form section. -/
theorem contMDiffAt_finsetSum_section {ι : Type*} (s : Finset ι)
    {W : ι → ∀ x : M, (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ} {x₀ : M}
    (hW : ∀ i ∈ s, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x (W i x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x (∑ i ∈ s, W i x)) x₀ := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact contMDiffAt_zeroSection ..
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hW a (Finset.mem_insert_self a s)).add_section
      (ih fun i hi => hW i (Finset.mem_insert_of_mem hi))

namespace RiemannianMetric

/-- **The Hodge star at `x`** (Lee, Problem 2-18(a)), `* : Λ^k(T_x^*M) → Λ^l(T_x^*M)` with
`k + l = n`.  It is the pointwise graded star `LeeLib.Ch02.hodgeStar` for the canonical positively
oriented `g`-orthonormal basis of `T_x M` — `stdOrthonormalBasis` adjusted to the orientation
`o x`.  By fibrewise uniqueness (`eq_hodgeStarAt_of_forall_wedge`) the value does not depend on this
choice; any positively oriented `g`-orthonormal basis gives the same map. -/
def hodgeStarAt (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E) (x : M)
    (η : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (finrank ℝ (TangentSpace I x))) := Fin.pos_iff_nonempty.mp hpos
  hodgeStar ((stdOrthonormalBasis ℝ (TangentSpace I x)).adjustToOrientation (o x)) h η

/-- **Additivity of the pointwise star.** -/
theorem hodgeStarAt_add (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E) (x : M)
    (η₁ η₂ : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.hodgeStarAt o hpos h x (η₁ + η₂)
      = g.hodgeStarAt o hpos h x η₁ + g.hodgeStarAt o hpos h x η₂ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (finrank ℝ (TangentSpace I x))) := Fin.pos_iff_nonempty.mp hpos
  exact hodgeStar_add _ h η₁ η₂

/-- **Homogeneity of the pointwise star.** -/
theorem hodgeStarAt_smul (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E) (x : M) (r : ℝ)
    (η : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    g.hodgeStarAt o hpos h x (r • η) = r • g.hodgeStarAt o hpos h x η := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (finrank ℝ (TangentSpace I x))) := Fin.pos_iff_nonempty.mp hpos
  exact hodgeStar_smul _ h r η

/-- **The Hodge star characterization (Lee 2-18a), fibrewise.**

`ω ∧ *η = ⟨ω, η⟩_g dV_g` at each point `x`, an equality of `(k+l)`-forms.  The volume form
`dV_g = g.volumeForm o x` is a form of degree `finrank ℝ E`; it is transported to the degree
`k + l` of the wedge `ω ∧ *η` along the canonical identification `finCongr h`.  Both `⟨·,·⟩_g` and
`dV_g` are the manifold's own fibre metric and volume form, so this is Lee's identity verbatim. -/
theorem hodgeStarAt_wedge (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E) (x : M)
    (w η : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) :
    wedge w (g.hodgeStarAt o hpos h x η)
      = g.innerFormsAt x w η •
          camDomDomCongr (finCongr h).symm (g.volumeForm o x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (finrank ℝ (TangentSpace I x))) := Fin.pos_iff_nonempty.mp hpos
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  set e := (stdOrthonormalBasis ℝ (TangentSpace I x)).adjustToOrientation (o x) with he
  have hor : e.toBasis.orientation = o x :=
    OrthonormalBasis.orientation_adjustToOrientation _ _
  have hinner : innerForms e w η = g.innerFormsAt x w η := by
    show innerForms e w η = innerForms (stdOrthonormalBasis ℝ (TangentSpace I x)) w η
    rw [innerForms_eq_innerForms e (stdOrthonormalBasis ℝ (TangentSpace I x))]
  show wedge w (hodgeStar e h η) = _
  rw [wedge_hodgeStar e h w η, hinner]
  congr 1
  exact (camDomDomCongr_volumeFormL (o x) e hor h).symm

/-- **Uniqueness in Lee 2-18a, fibrewise.**  Any `δ` satisfying the Hodge identity
`ω ∧ δ = ⟨ω, η⟩_g dV_g` for every `ω` at `x` equals `*η` at `x`.  Uniqueness needs no smoothness: it
is pinned down fibre by fibre, because the wedge `ω ∧ ·` is faithful in top degree. -/
theorem eq_hodgeStarAt_of_forall_wedge (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E) (x : M)
    (η : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) (δ : (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ)
    (hδ : ∀ w : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ,
      wedge w δ = g.innerFormsAt x w η •
        camDomDomCongr (finCongr h).symm (g.volumeForm o x)) :
    δ = g.hodgeStarAt o hpos h x η := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (finrank ℝ (TangentSpace I x))) := Fin.pos_iff_nonempty.mp hpos
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  set e := (stdOrthonormalBasis ℝ (TangentSpace I x)).adjustToOrientation (o x) with he
  have hor : e.toBasis.orientation = o x :=
    OrthonormalBasis.orientation_adjustToOrientation _ _
  show δ = hodgeStar e h η
  refine eq_hodgeStar_of_forall_wedge_eq e h η δ fun w => ?_
  rw [hδ w, show camDomDomCongr (finCongr h).symm (g.volumeForm o x)
        = wedgeCovectors (fun i : Fin (k + l) => flatL (e (finCongr h i)))
      from camDomDomCongr_volumeFormL (o x) e hor h]
  congr 1
  show g.innerFormsAt x w η = innerForms e w η
  show innerForms (stdOrthonormalBasis ℝ (TangentSpace I x)) w η = innerForms e w η
  rw [innerForms_eq_innerForms (stdOrthonormalBasis ℝ (TangentSpace I x)) e]

omit [FiniteDimensional ℝ E] in
/-- **The metric lowering of a smooth vector field is a smooth `1`-form field.**  For a smooth
vector field `Z`, the covector field `x ↦ g(Z(x), ·) = ♭Z(x)` is a smooth section of the
cotangent bundle.  This is `Z` fed to the metric read as a smooth section of the hom-bundle
`Hom(TM, T^*M)` (`g.contMDiff`, from `ContMDiffRiemannianMetric`), via `clm_bundle_apply`. -/
theorem contMDiffAt_inner_section (g : RiemannianMetric I M)
    {Z : ∀ x : M, TangentSpace I x} {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x (Z x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) →L[ℝ] ℝ) x (g.inner x (Z x))) x₀ :=
  (g.contMDiff.contMDiffAt).clm_bundle_apply hZ

/-- **The Hodge star of a smooth `k`-form is a smooth `(n-k)`-form, at a point** — the analytic
half of Lee's Problem 2-18(a).  This is the intermediate-degree analogue of `contMDiff_volumeForm`
and the reason `*` is a *smooth* bundle homomorphism.

The `stdOrthonormalBasis` used in the definition of `hodgeStarAt` is not smooth, so the proof first
switches, on a neighbourhood, to the smooth positively-oriented orthonormal frame `E` of
`exists_orientedOrthonormalFrame_nhds`: by fibrewise uniqueness (`eq_hodgeStarAt_of_forall_wedge`)
`*η` there equals `hodgeStar E`.  Its defining formula (the definition of `hodgeStarSum`) expands it
as `(l!)⁻¹ ∑_t d_t · (ε^{t_1} ∧ ⋯ ∧ ε^{t_l})`, a combination of the smooth coframe-wedge sections
`contMDiffAt_wedgeCovectors_section` (fed the smooth `1`-forms `♭E_i` of `contMDiffAt_inner_section`)
with the scalar coefficients `d_t = ⟨η, ε^t⟩`-style reference values `wedgeSum (η x) (ε^t) (E)`,
which are smooth `k`-forms applied to smooth vector fields (`contMDiffAt_apply_section`). -/
theorem contMDiffAt_hodgeStarAt (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (ho : IsSmoothOrientation o) (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E)
    {η : ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ} {x₀ : M}
    (hη : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (η x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x
          (g.hodgeStarAt o hpos h x (η x))) x₀ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  set ε : Fin k ⊕ Fin l ≃ Fin (finrank ℝ E) := finSumFinEquiv.trans (finCongr h) with hε
  obtain ⟨u, Z, hu, hx₀u, hZ, hon, hor⟩ := exists_orientedOrthonormalFrame_nhds g ho x₀
  have hZs : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x (Z i x)) x₀ :=
    fun i => hZ.contMDiffAt hu hx₀u i
  -- the coframe wedge section `W_t` and the scalar coefficient `d_t`
  set W : (Fin l → Fin (finrank ℝ E)) → ∀ x : M, (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ :=
    fun t x => wedgeCovectors (fun j => g.inner x (Z (t j) x)) with hW_def
  set d : (Fin l → Fin (finrank ℝ E)) → M → ℝ :=
    fun t x => wedgeSum (η x) (W t x) (fun y => Z (ε y) x) with hd_def
  have hW : ∀ t, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x (W t x)) x₀ :=
    fun t => contMDiffAt_wedgeCovectors_section
      (fun j => g.contMDiffAt_inner_section (hZs (t j)))
  have hd : ∀ t, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (d t) x₀ := by
    intro t
    have hform : d t = fun x =>
        (((Fintype.card (Fin k)).factorial * (Fintype.card (Fin l)).factorial : ℝ))⁻¹
          * ∑ σ : Equiv.Perm (Fin k ⊕ Fin l), ((Equiv.Perm.sign σ : ℤ) : ℝ)
              * ((η x) (fun i => Z (ε (σ (Sum.inl i))) x)
                  * (W t x) (fun j => Z (ε (σ (Sum.inr j))) x)) := by
      funext x; rw [hd_def]; exact wedgeSum_apply _ _ _
    rw [hform]
    refine contMDiffAt_const.mul (ContMDiffAt.sum fun σ _ => contMDiffAt_const.mul ?_)
    exact (contMDiffAt_apply_section hη (fun i => hZs (ε (σ (Sum.inl i))))).mul
      (contMDiffAt_apply_section (hW t) (fun j => hZs (ε (σ (Sum.inr j)))))
  -- the candidate section, manifestly smooth
  have hcand : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x
          ((l.factorial : ℝ)⁻¹ • ∑ t, d t x • W t x)) x₀ :=
    (contMDiffAt_finsetSum_section Finset.univ
      (fun t _ => (hd t).smul_section (hW t))).const_smul_section
  refine hcand.congr_of_eventuallyEq ?_
  filter_upwards [hu.mem_nhds hx₀u] with x hx
  -- `hodgeStarAt = (l!)⁻¹ • ∑_t d_t • W_t` at `x`, via the definition of `hodgeStarSum`
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (finrank ℝ (TangentSpace I x))) := Fin.pos_iff_nonempty.mp hpos
  have hon' := orthonormal_toBasisAt g hZ hon hx
  set Zb := (hZ.toBasisAt hx).toOrthonormalBasis hon' with hZb
  have hZbcoe : ∀ j, Zb j = Z j x := fun j => by
    rw [hZb, Basis.coe_toOrthonormalBasis, IsLocalFrameOn.toBasisAt_coe]
  have hflat : ∀ v : TangentSpace I x, flatL v = g.inner x v := fun v =>
    ContinuousLinearMap.ext fun w => by rw [flatL_apply]; rfl
  have hor' : Zb.toBasis.orientation = o x := by
    rw [hZb, Basis.toBasis_toOrthonormalBasis]; exact hor x hx
  have hWt : ∀ t : Fin l → Fin (finrank ℝ E),
      W t x = wedgeCovectors (fun j => flatL (Zb (t j))) := fun t => by
    rw [hW_def]; exact congrArg wedgeCovectors (funext fun j => by rw [hflat, hZbcoe])
  -- frame independence: the star for the smooth oriented ON frame is `hodgeStarAt`
  have hframe : hodgeStar Zb h (η x) = g.hodgeStarAt o hpos h x (η x) :=
    g.eq_hodgeStarAt_of_forall_wedge o hpos h x (η x) (hodgeStar Zb h (η x)) fun w => by
      rw [wedge_hodgeStar Zb h w (η x)]
      congr 1
      · show innerForms Zb w (η x) = g.innerFormsAt x w (η x)
        show innerForms Zb w (η x) = innerForms (stdOrthonormalBasis ℝ (TangentSpace I x)) w (η x)
        rw [innerForms_eq_innerForms Zb (stdOrthonormalBasis ℝ (TangentSpace I x))]
      · exact (camDomDomCongr_volumeFormL (o x) Zb hor' h).symm
  have hfib : g.hodgeStarAt o hpos h x (η x) = (l.factorial : ℝ)⁻¹ • ∑ t, d t x • W t x := by
    rw [← hframe]
    show ((Fintype.card (Fin l)).factorial : ℝ)⁻¹ •
        ∑ t : Fin l → Fin (finrank ℝ E),
          wedgeRef Zb ε (η x) (wedgeCovectors fun i => flatL (Zb (t i))) •
            wedgeCovectors (fun i => flatL (Zb (t i)))
        = (l.factorial : ℝ)⁻¹ • ∑ t, d t x • W t x
    rw [Fintype.card_fin]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    have hd_eq : d t x
        = wedgeSum (η x) (wedgeCovectors fun i => flatL (Zb (t i))) (fun y => Z (ε y) x) := by
      show wedgeSum (η x) (W t x) (fun y => Z (ε y) x) = _
      rw [hWt t]
    rw [hd_eq, hWt t, wedgeRef]
    congr 1
    exact congrArg (wedgeSum (η x) (wedgeCovectors fun i => flatL (Zb (t i))))
      (funext fun y => hZbcoe (ε y))
  exact congrArg (TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
    (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x) hfib

/-- **The Hodge star of a smooth `k`-form is a smooth `(n-k)`-form** (Lee, Problem 2-18(a)),
globally.  Together with `hodgeStarAt_wedge` (the characterization) and
`eq_hodgeStarAt_of_forall_wedge` (fibrewise uniqueness), this makes `*` the unique *smooth* bundle
homomorphism `Λ^k T^*M → Λ^{n-k} T^*M` satisfying `ω ∧ *η = ⟨ω, η⟩_g dV_g`. -/
theorem contMDiff_hodgeStarAt (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (ho : IsSmoothOrientation o) (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E)
    {η : ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ}
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (η x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x
          (g.hodgeStarAt o hpos h x (η x))) := fun x₀ =>
  g.contMDiffAt_hodgeStarAt o ho hpos h (hη x₀)

/-- **Lee, Problem 2-18(a).**  On an oriented Riemannian `n`-manifold there is a *unique smooth
bundle homomorphism* `* : Λ^k T^*M → Λ^{n-k} T^*M` (with `k + l = n`) satisfying Lee's identity

  `ω ∧ *η = ⟨ω, η⟩_g dV_g`.

Existence is `hodgeStarAt`, whose fibrewise linearity is `hodgeStarAt_add`/`hodgeStarAt_smul`;
that it is *smooth* — a bundle homomorphism, not a bare fibrewise-linear family — is
`contMDiff_hodgeStarAt`; the identity is `hodgeStarAt_wedge`; and uniqueness among *all* fibrewise
families satisfying the identity (smooth or not) is `eq_hodgeStarAt_of_forall_wedge`, which is what
this bundles.  The identity is stated with `dV_g` in the degree `k + l` of the wedge `ω ∧ *η`, via
the canonical reindexing `finCongr h`. -/
theorem riemannian_hodgeStar (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (ho : IsSmoothOrientation o) (hpos : 0 < finrank ℝ E) (h : k + l = finrank ℝ E) :
    ∃! S : (∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) →
        ∀ x : M, (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ,
      -- `S` maps each smooth `k`-form field to a *smooth* `(n-k)`-form field
      (∀ η : ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ,
        ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
            (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
              (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (η x)) →
          ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
            (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
              (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x (S η x))) ∧
      -- and satisfies Lee's identity `ω ∧ Sη = ⟨ω, η⟩_g dV_g` fibrewise
      (∀ (η : ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) (x : M)
          (w : (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ),
        wedge w (S η x) = g.innerFormsAt x w (η x) •
          camDomDomCongr (finCongr h).symm (g.volumeForm o x)) := by
  refine ⟨fun η x => g.hodgeStarAt o hpos h x (η x), ⟨fun η hη => g.contMDiff_hodgeStarAt o ho hpos h hη,
    fun η x w => g.hodgeStarAt_wedge o hpos h x w (η x)⟩, ?_⟩
  rintro S ⟨-, hchar⟩
  funext η x
  exact g.eq_hodgeStarAt_of_forall_wedge o hpos h x (η x) (S η x) fun w => hchar η x w

end RiemannianMetric

end

end LeeLib.Ch02
