/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Manifold/DoCarmoCh2.lean`; it is maintained
   here independently and is engineering support, not a blueprint node.
   `AffineConnection` is named `DCAffineConnection` here, to leave the
   `AffineConnection` anchor name free for Petersen's own blueprint. -/
import PetersenLib.Riemannian.Manifold.DoCarmoCh0
import PetersenLib.Foundations.RiemannianMetric
import PetersenLib.Riemannian.TensorBundle.MusicalIso
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# do Carmo Chapter 2 interface — affine connections

Thin, checked names for the abstract affine-connection primitives of do Carmo's
Chapter 2. Vector fields are the bundled `SmoothVectorField I M` (`= 𝒳(M)`) from
the Chapter 0 interface; the function ring `𝒟(M)` is the globally `C^∞` scalars
`f : M → ℝ`, acting on vector fields via `SmoothVectorField.smul`.

The abstract connection `∇` (do Carmo Def. 2.1) and the notion of a *symmetric*
connection (Def. 3.4) are genuinely new material: the library's metric layer
works `metric → Christoffel → geodesic` directly and never introduces the
operator `∇`. The coordinate Christoffel end (Def. 3.7) already exists as
`PetersenLib.chartChristoffel`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 2 §2–§3.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
/-- **Math.** Extensionality for smooth vector fields: two `SmoothVectorField`s
are equal as soon as their underlying tangent sections agree pointwise (the
smoothness witness is a proposition, hence irrelevant). -/
@[ext] theorem SmoothVectorField.ext {X Y : SmoothVectorField I M}
    (h : ∀ p, X p = Y p) : X = Y := by
  obtain ⟨fX, hX⟩ := X
  obtain ⟨fY, hY⟩ := Y
  have hfun : fX = fY := funext h
  subst hfun
  rfl

/-- **Math.** The directional derivative `X(f) : M → ℝ` of a scalar function
`f` along a smooth vector field `X`, i.e. `p ↦ df_p (X p)`. This is the
operator `X(·)` appearing in the Leibniz rule for an affine connection. -/
def SmoothVectorField.dir (X : SmoothVectorField I M) (f : M → ℝ) (p : M) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f p (X p)

/-- **Math.** The directional derivative `df_p(v)` of a scalar function `f` along a
*raw* tangent vector `v ∈ T_pM`, valued in `ℝ`. This is `SmoothVectorField.dir`
detached from the bundled smoothness witness; `X.dir f p = dirTangent f (X p)`. -/
def dirTangent (f : M → ℝ) {p : M} (v : TangentSpace I p) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f p v

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- **Math.** `dirTangent` is additive in the tangent vector. -/
theorem dirTangent_add (f : M → ℝ) {p : M} (v w : TangentSpace I p) :
    dirTangent f (v + w) = dirTangent f v + dirTangent f w :=
  map_add (mfderiv I 𝓘(ℝ, ℝ) f p) v w

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- **Math.** `dirTangent` is homogeneous in the tangent vector. -/
theorem dirTangent_smul (f : M → ℝ) {p : M} (c : ℝ) (v : TangentSpace I p) :
    dirTangent f (c • v) = c * dirTangent f v := by
  rw [dirTangent, dirTangent, map_smul]; rfl

open Bundle in
omit [CompleteSpace E] in
/-- **Math.** Tangent-vector extension: on a (finite-dimensional, σ-compact,
Hausdorff) smooth manifold, every tangent vector `v ∈ T_pM` is the value at `p`
of some *global* smooth vector field `Z ∈ 𝒳(M)`, i.e. `Z p = v`.

Construction (partition of unity): let `t x := {v}` at `x = p` and `t x := ⊤`
elsewhere; each `t x` is convex. Near `p` the constant section `x ↦ e.symm x c`
of the trivialization `e = trivializationAt` (with `c` the fibre coordinate of
`v`) is smooth and hits `v` at `p`; away from `p` the zero section works. Gluing
these local sections with `exists_contMDiffSection_forall_mem_convex_of_local`
yields a global smooth section `s` with `s p ∈ {v}`, i.e. `s p = v`. This is the
reusable infrastructure that upgrades the metric-tested Levi-Civita uniqueness to
full equality of connections (`DCAffineConnection.leviCivita_unique`). -/
theorem exists_smoothVectorField_eq [FiniteDimensional ℝ E] [SigmaCompactSpace M]
    [T2Space M] (p : M) (v : TangentSpace I p) :
    ∃ Z : SmoothVectorField I M, Z p = v := by
  classical
  set t : (x : M) → Set (TangentSpace I x) :=
    fun x => if x = p then {v} else Set.univ with ht
  have hconv : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases h : x = p
    · simp only [ht, if_pos h]; exact convex_singleton v
    · simp only [ht, if_neg h]; exact convex_univ
  have hlocal : ∀ x₀ : M, ∃ U ∈ nhds x₀, ∃ s_loc : (x : M) → TangentSpace I x,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, s_loc x⟩ : TangentBundle I M)) U ∧
        ∀ y ∈ U, s_loc y ∈ t y := by
    intro x₀
    by_cases hx : x₀ = p
    · subst hx
      set e := trivializationAt E (TangentSpace I) x₀ with he
      refine ⟨e.baseSet,
        e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀),
        fun x => e.symm x (e ⟨x₀, v⟩).2, ?_, ?_⟩
      · rw [Trivialization.contMDiffOn_section_baseSet_iff e]
        refine ContMDiffOn.congr (contMDiffOn_const (c := (e ⟨x₀, v⟩).2)) ?_
        intro x hx
        simp only [Trivialization.apply_mk_symm e hx]
      · intro y hy
        by_cases hyp : y = x₀
        · subst hyp
          simp only [ht, if_pos rfl, Set.mem_singleton_iff]
          exact Trivialization.symm_apply_apply_mk e hy v
        · simp only [ht, if_neg hyp]; exact Set.mem_univ _
    · refine ⟨{p}ᶜ, (isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hx),
        fun x => (0 : TangentSpace I x), ?_, ?_⟩
      · exact (contMDiff_zeroSection ℝ (TangentSpace I)).contMDiffOn
      · intro y hy
        have hyne : y ≠ p := by simpa using hy
        simp only [ht, if_neg hyne]; exact Set.mem_univ _
  obtain ⟨s, hs⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local I (n := (⊤ : ℕ∞))
      (TangentSpace I) t hconv hlocal
  have hsp : s p = v := by
    have := hs p; simpa only [ht, if_pos rfl, Set.mem_singleton_iff] using this
  exact ⟨⟨fun x => s x, s.contMDiff⟩, hsp⟩

/-- **Math.** do Carmo Ch. 2, Def. 2.1: an **affine connection** `∇` on the
manifold `M` is a map
`∇ : 𝒳(M) × 𝒳(M) → 𝒳(M)`, `(X, Y) ↦ ∇_X Y`, satisfying, for all
`X, Y, Z ∈ 𝒳(M)` and `f, g ∈ 𝒟(M)`:

* (i) `∇_{fX+gY} Z = f ∇_X Z + g ∇_Y Z` — `𝒟(M)`-linearity in the first slot,
  split here into additivity (`add_left`) and function-homogeneity (`smul_left`);
* (ii) `∇_X (Y + Z) = ∇_X Y + ∇_X Z` — additivity in the second slot;
* (iii) `∇_X (fY) = f ∇_X Y + X(f) Y` — the Leibniz rule, where `X(f)` is the
  directional derivative `p ↦ df_p (X p)` and the identity is stated pointwise.

Vector fields are bundled `SmoothVectorField I M`; the function action `f • X`
is `SmoothVectorField.smul f hf X` for a globally `C^∞` scalar `f`. -/
structure DCAffineConnection (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The underlying map `(X, Y) ↦ ∇_X Y`. -/
  cov : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M
  /-- (i-add) Additivity in the first argument. -/
  add_left : ∀ X Y Z : SmoothVectorField I M, cov (X + Y) Z = cov X Z + cov Y Z
  /-- (i-smul) `𝒟(M)`-homogeneity in the first argument. -/
  smul_left : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X Z : SmoothVectorField I M),
      cov (SmoothVectorField.smul f hf X) Z = SmoothVectorField.smul f hf (cov X Z)
  /-- (ii) Additivity in the second argument. -/
  add_right : ∀ X Y Z : SmoothVectorField I M, cov X (Y + Z) = cov X Y + cov X Z
  /-- (iii) The Leibniz rule, stated pointwise: `∇_X (fY) = f ∇_X Y + X(f) Y`. -/
  leibniz : ∀ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (X Y : SmoothVectorField I M) (p : M),
      (cov X (SmoothVectorField.smul f hf Y)) p
        = f p • (cov X Y) p + (SmoothVectorField.dir X f p) • (Y p)

namespace DCAffineConnection

/-- **Math.** do Carmo Ch. 2, Def. 3.4: an affine connection `∇` is
**symmetric** when
`∇_X Y − ∇_Y X = [X, Y]` for all `X, Y ∈ 𝒳(M)`,
where `[X, Y]` is the manifold Lie bracket (`DCLieBracket`). The identity is
stated pointwise on tangent vectors. -/
def IsSymmetric (nabla : DCAffineConnection I M) : Prop :=
  ∀ (X Y : SmoothVectorField I M) (p : M),
    (nabla.cov X Y) p - (nabla.cov Y X) p = DCLieBracket X Y p

/-- **Math.** do Carmo Ch. 2, Cor. 3.3 (eq. (4)): `∇` is **compatible with the
metric** `g` when
`X⟨Y, Z⟩ = ⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩` for all `X, Y, Z ∈ 𝒳(M)`,
stated pointwise, with `X⟨Y, Z⟩` the directional derivative of `p ↦ ⟨Y, Z⟩_p`
along `X` (`SmoothVectorField.dir`). This is do Carmo's characterization (4) of
compatibility; by Cor. 3.3 / Prop. 3.2 it is equivalent to the
parallel-transport definition (Def. 3.1) once the covariant derivative along a
curve is available. -/
def IsMetricCompatible (g : RiemannianMetric I M) (nabla : DCAffineConnection I M) :
    Prop :=
  ∀ (X Y Z : SmoothVectorField I M) (p : M),
    X.dir (fun q => g.metricInner q (Y q) (Z q)) p
      = g.metricInner p ((nabla.cov X Y) p) (Z p)
        + g.metricInner p (Y p) ((nabla.cov X Z) p)

/-- **Math.** do Carmo Ch. 2, Thm. 3.6: an affine connection is a
**Levi-Civita (Riemannian) connection** for the metric `g` when it is both
symmetric and compatible with `g`. The Levi-Civita theorem asserts that exactly
one such connection exists on any Riemannian manifold. -/
def IsLeviCivita (g : RiemannianMetric I M) (nabla : DCAffineConnection I M) : Prop :=
  nabla.IsSymmetric ∧ nabla.IsMetricCompatible g

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 2, Thm. 3.6, eq. (9) — the **Koszul formula**. For an
affine connection `∇` that is symmetric (Def. 3.4) and compatible with the metric
`g` in the sense of eq. (4) (`IsMetricCompatible`), the inner product
`⟨Z, ∇_Y X⟩` is completely determined by the metric and the Lie brackets:

`2⟨Z, ∇_Y X⟩ = X⟨Y,Z⟩ + Y⟨Z,X⟩ − Z⟨X,Y⟩ − ⟨[X,Z],Y⟩ − ⟨[Y,Z],X⟩ − ⟨[X,Y],Z⟩`,

where `X⟨Y,Z⟩` is the directional derivative of `p ↦ ⟨Y,Z⟩_p` along `X`
(`SmoothVectorField.dir`). This is the identity from which the uniqueness half of
the Levi-Civita theorem follows: the right-hand side does not mention `∇`. The
statement is pointwise at `p`. -/
theorem koszul_formula (g : RiemannianMetric I M) (nabla : DCAffineConnection I M)
    (hsym : nabla.IsSymmetric) (hcompat : nabla.IsMetricCompatible g)
    (X Y Z : SmoothVectorField I M) (p : M) :
    2 * g.metricInner p (Z p) ((nabla.cov Y X) p)
      = X.dir (fun q => g.metricInner q (Y q) (Z q)) p
        + Y.dir (fun q => g.metricInner q (Z q) (X q)) p
        - Z.dir (fun q => g.metricInner q (X q) (Y q)) p
        - g.metricInner p (DCLieBracket X Z p) (Y p)
        - g.metricInner p (DCLieBracket Y Z p) (X p)
        - g.metricInner p (DCLieBracket X Y p) (Z p) := by
  -- eq. (6), (7), (8): metric compatibility for the three cyclic orderings.
  have e6 := hcompat X Y Z p
  have e7 := hcompat Y Z X p
  have e8 := hcompat Z X Y p
  -- symmetry, rewritten as `[·,·] = ∇· − ∇·`.
  have s1 : DCLieBracket X Y p = (nabla.cov X Y) p - (nabla.cov Y X) p :=
    (hsym X Y p).symm
  have s2 : DCLieBracket X Z p = (nabla.cov X Z) p - (nabla.cov Z X) p :=
    (hsym X Z p).symm
  have s3 : DCLieBracket Y Z p = (nabla.cov Y Z) p - (nabla.cov Z Y) p :=
    (hsym Y Z p).symm
  -- expand the three bracket inner products via symmetry and bilinearity.
  have b1 : g.metricInner p (DCLieBracket X Y p) (Z p)
      = g.metricInner p ((nabla.cov X Y) p) (Z p)
        - g.metricInner p ((nabla.cov Y X) p) (Z p) := by
    rw [s1, g.metricInner_sub_left]
  have b2 : g.metricInner p (DCLieBracket X Z p) (Y p)
      = g.metricInner p ((nabla.cov X Z) p) (Y p)
        - g.metricInner p ((nabla.cov Z X) p) (Y p) := by
    rw [s2, g.metricInner_sub_left]
  have b3 : g.metricInner p (DCLieBracket Y Z p) (X p)
      = g.metricInner p ((nabla.cov Y Z) p) (X p)
        - g.metricInner p ((nabla.cov Z Y) p) (X p) := by
    rw [s3, g.metricInner_sub_left]
  -- symmetry of the metric to align the remaining inner products.
  have c1 := g.metricInner_comm p (Y p) ((nabla.cov X Z) p)
  have c2 := g.metricInner_comm p (X p) ((nabla.cov Z Y) p)
  have c3 := g.metricInner_comm p (Z p) ((nabla.cov Y X) p)
  linarith [e6, e7, e8, b1, b2, b3, c1, c2, c3]

omit [CompleteSpace E] in
/-- **Math.** Uniqueness half of the Levi-Civita theorem (do Carmo Ch. 2,
Thm. 3.6), in the form the metric can test directly: if `∇₁` and `∇₂` are both
symmetric and compatible with the metric `g`, then their covariant derivatives
have the *same* inner product against every smooth vector field `Z`,
`⟨Z, (∇₁)_Y X⟩ = ⟨Z, (∇₂)_Y X⟩`. Both sides equal the metric-only right-hand side
of the Koszul formula (`koszul_formula`), which does not mention the connection. -/
theorem leviCivita_cov_inner_unique (g : RiemannianMetric I M)
    (n₁ n₂ : DCAffineConnection I M)
    (h₁ : n₁.IsLeviCivita g) (h₂ : n₂.IsLeviCivita g)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.metricInner p (Z p) ((n₁.cov Y X) p)
      = g.metricInner p (Z p) ((n₂.cov Y X) p) := by
  have k1 := koszul_formula g n₁ h₁.1 h₁.2 X Y Z p
  have k2 := koszul_formula g n₂ h₂.1 h₂.2 X Y Z p
  linarith [k1, k2]

omit [CompleteSpace E] in
/-- **Math.** Extensionality for affine connections: two connections are equal as
soon as their covariant-derivative maps `(X, Y) ↦ ∇_X Y` agree; the four axiom
fields are propositions, hence irrelevant. -/
@[ext] theorem ext {n₁ n₂ : DCAffineConnection I M} (h : n₁.cov = n₂.cov) :
    n₁ = n₂ := by
  cases n₁; cases n₂; cases h; rfl

omit [CompleteSpace E] in
/-- **Math.** Uniqueness half of the Levi-Civita theorem (do Carmo Ch. 2,
Thm. 3.6): on a Riemannian manifold there is **at most one** connection that is
symmetric and compatible with the metric `g`. Concretely, any two Levi-Civita
connections `n₁`, `n₂` for `g` are equal, `n₁ = n₂`.

The proof upgrades the metric-tested identity `leviCivita_cov_inner_unique`
(`⟨Z, (∇₁)_Y X⟩ = ⟨Z, (∇₂)_Y X⟩` for every field `Z`) to full pointwise equality:
the tangent-vector-extension hypothesis `hext` says every tangent vector `w` at a
point `q` is realized as `Z q` for some global smooth field `Z`, so the two
covariant derivatives have the same inner product against *every* tangent vector
and non-degeneracy of `g` (`metricInner_eq_iff_eq`) forces them equal. -/
theorem leviCivita_unique (g : RiemannianMetric I M)
    (hext : ∀ (q : M) (w : TangentSpace I q),
      ∃ Z : SmoothVectorField I M, Z q = w)
    (n₁ n₂ : DCAffineConnection I M)
    (h₁ : n₁.IsLeviCivita g) (h₂ : n₂.IsLeviCivita g) :
    n₁ = n₂ := by
  refine DCAffineConnection.ext
    (funext fun Y => funext fun X => SmoothVectorField.ext fun p => ?_)
  refine (g.metricInner_eq_iff_eq p ((n₁.cov Y X) p) ((n₂.cov Y X) p)).mp ?_
  intro w
  obtain ⟨Z, hZ⟩ := hext p w
  have key := leviCivita_cov_inner_unique g n₁ n₂ h₁ h₂ X Y Z p
  rw [← hZ, g.metricInner_comm p _ (Z p), g.metricInner_comm p _ (Z p)]
  exact key

omit [CompleteSpace E] in
/-- **Math.** Uniqueness half of the Levi-Civita theorem (do Carmo Ch. 2,
Thm. 3.6), unconditional form: on a finite-dimensional, σ-compact, Hausdorff
Riemannian manifold there is at most one symmetric metric-compatible connection.
The tangent-vector-extension hypothesis of `leviCivita_unique` is discharged by
`exists_smoothVectorField_eq`. -/
theorem leviCivita_unique' [FiniteDimensional ℝ E] [SigmaCompactSpace M]
    [T2Space M] (g : RiemannianMetric I M) (n₁ n₂ : DCAffineConnection I M)
    (h₁ : n₁.IsLeviCivita g) (h₂ : n₂.IsLeviCivita g) :
    n₁ = n₂ :=
  leviCivita_unique g (fun q w => exists_smoothVectorField_eq q w) n₁ n₂ h₁ h₂

end DCAffineConnection

/-! ## Well-definedness of the Koszul construction

The uniqueness half of the Levi-Civita theorem is landed
(`DCAffineConnection.leviCivita_unique'`). The *existence* half constructs `∇` by
declaring, for each pair `(Y, X)`, the field `∇_Y X` to be the metric-dual of the
functional `Z ↦ ½·(Koszul RHS)`. For that recipe to define a genuine vector
field the functional must be `𝒟(M)`-linear in the test field `Z` — additive and
function-homogeneous — so that it is tensorial and Riesz-dualizes pointwise. The
lemmas below establish exactly that linearity (do Carmo's "it is easy to verify
that `∇` is well-defined"); the remaining analytic input for existence is the
*smoothness* of the resulting dual section. -/

omit [CompleteSpace E] in
/-- **Math.** Additivity of the directional derivative in the base field:
`(X + Y)(h) = X(h) + Y(h)`. -/
theorem SmoothVectorField.dir_add_field (X Y : SmoothVectorField I M) (h : M → ℝ)
    (p : M) : (X + Y).dir h p = X.dir h p + Y.dir h p := by
  simp only [SmoothVectorField.dir, SmoothVectorField.add_apply]
  exact map_add _ _ _

omit [CompleteSpace E] in
/-- **Math.** Homogeneity of the directional derivative in the base field:
`(fZ)(h) = f·Z(h)`, since `mfderiv` is `ℝ`-linear in the direction. -/
theorem SmoothVectorField.dir_smul_field {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (Z : SmoothVectorField I M) (h : M → ℝ) (p : M) :
    (SmoothVectorField.smul f hf Z).dir h p = f p * Z.dir h p := by
  simp only [SmoothVectorField.dir, SmoothVectorField.smul_apply, map_smul]
  rfl

omit [CompleteSpace E] in
/-- **Math.** Additivity of the directional derivative in the scalar argument:
`X(h₁ + h₂) = X(h₁) + X(h₂)` for `h₁, h₂` differentiable at `p`. -/
theorem SmoothVectorField.dir_add (X : SmoothVectorField I M) {h₁ h₂ : M → ℝ} (p : M)
    (h₁d : MDifferentiableAt I 𝓘(ℝ, ℝ) h₁ p)
    (h₂d : MDifferentiableAt I 𝓘(ℝ, ℝ) h₂ p) :
    X.dir (fun q => h₁ q + h₂ q) p = X.dir h₁ p + X.dir h₂ p := by
  simp only [SmoothVectorField.dir]
  rw [show (fun q => h₁ q + h₂ q) = h₁ + h₂ from rfl,
    (h₁d.hasMFDerivAt.add h₂d.hasMFDerivAt).mfderiv]
  rfl

omit [CompleteSpace E] in
/-- **Math.** Leibniz rule for the directional derivative:
`X(f·h) = f·X(h) + h·X(f)` for `f, h` differentiable at `p`. -/
theorem SmoothVectorField.dir_mul (X : SmoothVectorField I M) {f h : M → ℝ} (p : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h p) :
    X.dir (fun q => f q * h q) p = f p * X.dir h p + h p * X.dir f p := by
  simp only [SmoothVectorField.dir]
  rw [show (fun q => f q * h q) = f * h from rfl,
    (hf.hasMFDerivAt.mul hh.hasMFDerivAt).mfderiv]
  rfl

omit [CompleteSpace E] in
/-- **Math.** Differentiability of the pointwise metric pairing
`q ↦ ⟨Y(q), Z(q)⟩` of two smooth vector fields, at any point `p`. -/
theorem RiemannianMetric.metricInner_field_mdifferentiableAt
    (g : RiemannianMetric I M) (Y Z : SmoothVectorField I M) (p : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (Y q) (Z q)) p := by
  have h := g.metricInner_contMDiffWithinAt (s := Set.univ) (x := p) (n := (∞ : ℕ∞ω))
    (v := fun y => Y y) (w := fun y => Z y)
    ((Y.smooth p).contMDiffWithinAt) ((Z.smooth p).contMDiffWithinAt)
  rw [contMDiffWithinAt_univ] at h
  exact h.mdifferentiableAt (by simp)

/-- **Math.** Bracket Leibniz in the second slot, packaged for
`SmoothVectorField`: `[X, fZ] = X(f)·Z + f·[X, Z]`, pointwise at `p`. -/
theorem DCLieBracket_smul_right {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Z : SmoothVectorField I M) (p : M) :
    DCLieBracket X (SmoothVectorField.smul f hf Z) p
      = (X.dir f p) • Z p + f p • DCLieBracket X Z p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f p := hf.mdifferentiableAt (by simp)
  have hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z.toFun y⟩ : TangentBundle I M)) p := Z.smoothAt p
  show VectorField.mlieBracket I X.toFun (SmoothVectorField.smul f hf Z).toFun p = _
  have hrhs : (SmoothVectorField.smul f hf Z).toFun = f • Z.toFun := rfl
  rw [hrhs, VectorField.mlieBracket_smul_right hfd hZ]
  rfl

/-- **Math.** Additivity of the bracket in the second slot, packaged for
`SmoothVectorField`: `[X, Z₁ + Z₂] = [X, Z₁] + [X, Z₂]`, pointwise at `p`. -/
theorem DCLieBracket_add_right (X Z₁ Z₂ : SmoothVectorField I M) (p : M) :
    DCLieBracket X (Z₁ + Z₂) p = DCLieBracket X Z₁ p + DCLieBracket X Z₂ p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hZ₁ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z₁.toFun y⟩ : TangentBundle I M)) p := Z₁.smoothAt p
  have hZ₂ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z₂.toFun y⟩ : TangentBundle I M)) p := Z₂.smoothAt p
  show VectorField.mlieBracket I X.toFun (Z₁ + Z₂).toFun p = _
  have hrhs : (Z₁ + Z₂).toFun = Z₁.toFun + Z₂.toFun := rfl
  rw [hrhs, VectorField.mlieBracket_add_right hZ₁ hZ₂]

/-- **Math.** Additivity of the bracket in the **first** slot, packaged for
`SmoothVectorField`: `[X₁ + X₂, Z] = [X₁, Z] + [X₂, Z]`, pointwise at `p`. -/
theorem DCLieBracket_add_left (X₁ X₂ Z : SmoothVectorField I M) (p : M) :
    DCLieBracket (X₁ + X₂) Z p = DCLieBracket X₁ Z p + DCLieBracket X₂ Z p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hX₁ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X₁.toFun y⟩ : TangentBundle I M)) p := X₁.smoothAt p
  have hX₂ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X₂.toFun y⟩ : TangentBundle I M)) p := X₂.smoothAt p
  show VectorField.mlieBracket I (X₁ + X₂).toFun Z.toFun p = _
  have hlhs : (X₁ + X₂).toFun = X₁.toFun + X₂.toFun := rfl
  rw [hlhs, VectorField.mlieBracket_add_left hX₁ hX₂]

/-- **Math.** Bracket Leibniz in the **first** slot, packaged for
`SmoothVectorField`: `[fX, Z] = −Z(f)·X + f·[X, Z]`, pointwise at `p`. This is
the product rule `[f • V, W] = -(df W) • V + f • [V, W]` specialized to smooth
vector fields. -/
theorem DCLieBracket_smul_left {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Z : SmoothVectorField I M) (p : M) :
    DCLieBracket (SmoothVectorField.smul f hf X) Z p
      = -(Z.dir f p) • X p + f p • DCLieBracket X Z p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f p := hf.mdifferentiableAt (by simp)
  have hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p := X.smoothAt p
  show VectorField.mlieBracket I (SmoothVectorField.smul f hf X).toFun Z.toFun p = _
  have hlhs : (SmoothVectorField.smul f hf X).toFun = f • X.toFun := rfl
  rw [hlhs, VectorField.mlieBracket_smul_left hfd hX]
  rfl

/-- **Math.** The **Koszul functional** — the metric-only right-hand side of the
Koszul formula (do Carmo eq. (9)) as a functional of the test field `Z`:

`koszulRHS X Y Z = X⟨Y,Z⟩ + Y⟨Z,X⟩ − Z⟨X,Y⟩ − ⟨[X,Z],Y⟩ − ⟨[Y,Z],X⟩ − ⟨[X,Y],Z⟩`.

By `DCAffineConnection.koszul_formula` any Levi-Civita `∇` satisfies
`2⟨Z, ∇_Y X⟩ = koszulRHS X Y Z`, so existence amounts to Riesz-dualizing this
functional in `Z`. -/
noncomputable def RiemannianMetric.koszulRHS (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) : ℝ :=
  X.dir (fun q => g.metricInner q (Y q) (Z q)) p
    + Y.dir (fun q => g.metricInner q (Z q) (X q)) p
    - Z.dir (fun q => g.metricInner q (X q) (Y q)) p
    - g.metricInner p (DCLieBracket X Z p) (Y p)
    - g.metricInner p (DCLieBracket Y Z p) (X p)
    - g.metricInner p (DCLieBracket X Y p) (Z p)

/-- **Math.** The Koszul functional is **additive** in the test field `Z`:
`koszulRHS X Y (Z₁ + Z₂) = koszulRHS X Y Z₁ + koszulRHS X Y Z₂`. First half of
`𝒟(M)`-linearity — the additivity making the recipe `∇_Y X := (koszulRHS)^♯`
well-defined. -/
theorem RiemannianMetric.koszulRHS_add_right (g : RiemannianMetric I M)
    (X Y Z₁ Z₂ : SmoothVectorField I M) (p : M) :
    g.koszulRHS X Y (Z₁ + Z₂) p
      = g.koszulRHS X Y Z₁ p + g.koszulRHS X Y Z₂ p := by
  simp only [RiemannianMetric.koszulRHS,
    X.dir_add p (g.metricInner_field_mdifferentiableAt Y Z₁ p)
      (g.metricInner_field_mdifferentiableAt Y Z₂ p),
    Y.dir_add p (g.metricInner_field_mdifferentiableAt Z₁ X p)
      (g.metricInner_field_mdifferentiableAt Z₂ X p),
    SmoothVectorField.dir_add_field,
    DCLieBracket_add_right,
    SmoothVectorField.add_apply, g.metricInner_add_left, g.metricInner_add_right]
  ring

/-- **Math.** The Koszul functional is **function-homogeneous** in the test field
`Z`: `koszulRHS X Y (fZ) = f·koszulRHS X Y Z` for every smooth scalar `f`. This
is the crux of do Carmo's "`∇` is well-defined": the `X(f)`-type terms produced by
the Leibniz rule and the bracket Leibniz rule cancel against each other by
symmetry of the metric. Together with `koszulRHS_add_right` it exhibits
`Z ↦ koszulRHS X Y Z` as a `𝒟(M)`-linear (tensorial) functional, hence the Riesz
dual of the metric — the Levi-Civita covariant derivative `∇_Y X`. -/
theorem RiemannianMetric.koszulRHS_smul_right (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.koszulRHS X Y (SmoothVectorField.smul f hf Z) p
      = f p * g.koszulRHS X Y Z p := by
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f p := hf.mdifferentiableAt (by simp)
  simp only [RiemannianMetric.koszulRHS,
    X.dir_mul p hfd (g.metricInner_field_mdifferentiableAt Y Z p),
    Y.dir_mul p hfd (g.metricInner_field_mdifferentiableAt Z X p),
    SmoothVectorField.dir_smul_field,
    DCLieBracket_smul_right, SmoothVectorField.smul_apply,
    g.metricInner_add_left, g.metricInner_smul_left, g.metricInner_smul_right]
  -- the surviving `X(f)`-terms cancel by symmetry ⟨Y,Z⟩ = ⟨Z,Y⟩
  have hsymm : g.metricInner p (Y p) (Z p) = g.metricInner p (Z p) (Y p) :=
    g.metricInner_comm p (Y p) (Z p)
  rw [hsymm]
  ring

/-- **Math.** The Koszul functional is **additive in the first (differentiated)
field** `X`: `koszulRHS (X₁ + X₂) Y Z = koszulRHS X₁ Y Z + koszulRHS X₂ Y Z`.
Via `2⟨∇_Y X, Z⟩ = koszulRHS X Y Z` this is exactly additivity of the candidate
Levi-Civita connection in its differentiated argument (`DCAffineConnection.add_right`
for the Koszul-dual connection). -/
theorem RiemannianMetric.koszulRHS_add_left (g : RiemannianMetric I M)
    (X₁ X₂ Y Z : SmoothVectorField I M) (p : M) :
    g.koszulRHS (X₁ + X₂) Y Z p
      = g.koszulRHS X₁ Y Z p + g.koszulRHS X₂ Y Z p := by
  simp only [RiemannianMetric.koszulRHS,
    SmoothVectorField.dir_add_field,
    Y.dir_add p (g.metricInner_field_mdifferentiableAt Z X₁ p)
      (g.metricInner_field_mdifferentiableAt Z X₂ p),
    Z.dir_add p (g.metricInner_field_mdifferentiableAt X₁ Y p)
      (g.metricInner_field_mdifferentiableAt X₂ Y p),
    DCLieBracket_add_left,
    SmoothVectorField.add_apply, g.metricInner_add_left, g.metricInner_add_right]
  ring

/-- **Math.** The Koszul functional obeys a **Leibniz rule in the first
(differentiated) field** `X`:
`koszulRHS (fX) Y Z = f·koszulRHS X Y Z + 2·Y(f)·⟨X,Z⟩` for every smooth scalar
`f`. Via `2⟨∇_Y X, Z⟩ = koszulRHS X Y Z` the extra term `2·Y(f)·⟨X,Z⟩` is exactly
`2⟨Y(f)·X, Z⟩`, so this is the Leibniz rule `∇_Y (fX) = f∇_Y X + Y(f)X` for the
candidate Levi-Civita connection (`DCAffineConnection.leibniz` for the Koszul-dual
connection). -/
theorem RiemannianMetric.koszulRHS_leibniz_left (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.koszulRHS (SmoothVectorField.smul f hf X) Y Z p
      = f p * g.koszulRHS X Y Z p
        + 2 * (Y.dir f p) * g.metricInner p (X p) (Z p) := by
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f p := hf.mdifferentiableAt (by simp)
  simp only [RiemannianMetric.koszulRHS,
    SmoothVectorField.dir_smul_field,
    Y.dir_mul p hfd (g.metricInner_field_mdifferentiableAt Z X p),
    Z.dir_mul p hfd (g.metricInner_field_mdifferentiableAt X Y p),
    DCLieBracket_smul_left,
    SmoothVectorField.smul_apply,
    g.metricInner_add_left, g.metricInner_smul_left, g.metricInner_smul_right]
  rw [g.metricInner_comm p (Z p) (X p)]
  ring

/-- **Math.** The Koszul functional is **additive in the direction field** `Y`:
`koszulRHS X (Y₁ + Y₂) Z = koszulRHS X Y₁ Z + koszulRHS X Y₂ Z`. Via
`2⟨∇_Y X, Z⟩ = koszulRHS X Y Z` this is additivity of the candidate Levi-Civita
connection in its direction argument (`DCAffineConnection.add_left` for the
Koszul-dual connection). -/
theorem RiemannianMetric.koszulRHS_add_middle (g : RiemannianMetric I M)
    (X Y₁ Y₂ Z : SmoothVectorField I M) (p : M) :
    g.koszulRHS X (Y₁ + Y₂) Z p
      = g.koszulRHS X Y₁ Z p + g.koszulRHS X Y₂ Z p := by
  simp only [RiemannianMetric.koszulRHS,
    X.dir_add p (g.metricInner_field_mdifferentiableAt Y₁ Z p)
      (g.metricInner_field_mdifferentiableAt Y₂ Z p),
    SmoothVectorField.dir_add_field,
    Z.dir_add p (g.metricInner_field_mdifferentiableAt X Y₁ p)
      (g.metricInner_field_mdifferentiableAt X Y₂ p),
    DCLieBracket_add_left, DCLieBracket_add_right,
    SmoothVectorField.add_apply, g.metricInner_add_left, g.metricInner_add_right]
  ring

/-- **Math.** The Koszul functional is **function-homogeneous in the direction
field** `Y`: `koszulRHS X (fY) Z = f·koszulRHS X Y Z` for every smooth scalar `f`
(no Leibniz term — `Y` is the differentiating direction). Via
`2⟨∇_Y X, Z⟩ = koszulRHS X Y Z` this is `𝒟(M)`-homogeneity of the candidate
Levi-Civita connection in its direction argument (`DCAffineConnection.smul_left` for
the Koszul-dual connection); the `X(f)`- and `Z(f)`-type terms produced by the two
Leibniz rules cancel by symmetry of the metric. -/
theorem RiemannianMetric.koszulRHS_smul_middle (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.koszulRHS X (SmoothVectorField.smul f hf Y) Z p
      = f p * g.koszulRHS X Y Z p := by
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f p := hf.mdifferentiableAt (by simp)
  simp only [RiemannianMetric.koszulRHS,
    X.dir_mul p hfd (g.metricInner_field_mdifferentiableAt Y Z p),
    SmoothVectorField.dir_smul_field,
    Z.dir_mul p hfd (g.metricInner_field_mdifferentiableAt X Y p),
    DCLieBracket_smul_left, DCLieBracket_smul_right,
    SmoothVectorField.smul_apply,
    g.metricInner_add_left, g.metricInner_smul_left, g.metricInner_smul_right]
  rw [g.metricInner_comm p (Y p) (X p)]
  ring

/-! ## Locality of the Koszul functional in the test field

do Carmo's terse "it is easy to verify that `∇` is well-defined" hides a genuine
analytic fact: the Koszul functional `Z ↦ koszulRHS X Y Z p` — though built from
directional derivatives and Lie brackets that see `Z` on a whole neighbourhood of
`p` — depends on the test field `Z` **only through the single tangent vector**
`Z p`. This is the tensoriality (`𝒟(M)`-linearity) established above, upgraded from
germ-linearity to pointwise dependence. We obtain it for free from mathlib's
`TensorialAt` machinery, whose `pointwise`/`mkHom` lemmas run exactly the
chart-frame + bump-function argument. The resulting covector `koszulCovec X Y p`
is the Riesz-dualizable object from which the Levi-Civita connection is built. -/

/-- **Math.** The Koszul functional as an operator on **raw tangent sections**
`σ : Π q, T_qM` (not assumed globally smooth), matching
`RiemannianMetric.koszulRHS` on the underlying section of a `SmoothVectorField`
(`koszulRHSraw_toFun`). This unbundled form is what mathlib's `TensorialAt`
machinery consumes: the tensoriality of `σ ↦ koszulRHSraw X Y σ p` yields the
pointwise locality of the Koszul functional. -/
noncomputable def RiemannianMetric.koszulRHSraw (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (σ : Π q : M, TangentSpace I q) (p : M) : ℝ :=
  X.dir (fun q => g.metricInner q (Y q) (σ q)) p
    + Y.dir (fun q => g.metricInner q (σ q) (X q)) p
    - dirTangent (fun q => g.metricInner q (X q) (Y q)) (σ p)
    - g.metricInner p (VectorField.mlieBracket I X.toFun σ p) (Y p)
    - g.metricInner p (VectorField.mlieBracket I Y.toFun σ p) (X p)
    - g.metricInner p (VectorField.mlieBracket I X.toFun Y.toFun p) (σ p)

omit [CompleteSpace E] in
/-- **Math.** The raw Koszul functional agrees with `koszulRHS` on the underlying
section of a smooth vector field. -/
theorem RiemannianMetric.koszulRHSraw_toFun (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.koszulRHSraw X Y Z.toFun p = g.koszulRHS X Y Z p := rfl

omit [CompleteSpace E] in
/-- **Math.** Differentiability of the pointwise metric pairing `q ↦ ⟨v(q), w(q)⟩`
of two merely `C¹` tangent sections, at `p`. Wraps mathlib's
`MDifferentiableAt.inner_bundle` for the Riemannian tangent bundle carrying `g`. -/
theorem RiemannianMetric.metricInner_raw_mdifferentiableAt
    (g : RiemannianMetric I M) {v w : Π q : M, TangentSpace I q} {p : M}
    (hv : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) p)
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) p) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (v q) (w q)) p := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact MDifferentiableAt.inner_bundle (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _)) (b := fun y => y)
    (v := v) (w := w) (IM := I) hv hw

/-- **Math.** Bracket Leibniz in the second slot for a **raw** section:
`[X, f·σ] = X(f)·σ + f·[X, σ]` pointwise at `p`, for `f` and `σ` differentiable
at `p`. Raw-section analogue of `DCLieBracket_smul_right`. -/
theorem mlieBracket_field_smul_right_raw {f : M → ℝ} {p : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p) (X : SmoothVectorField I M)
    {σ : Π q : M, TangentSpace I q}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TangentBundle I M)) p) :
    VectorField.mlieBracket I X.toFun (f • σ) p
      = (X.dir f p) • σ p + f p • VectorField.mlieBracket I X.toFun σ p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  rw [VectorField.mlieBracket_smul_right hf hσ]
  rfl

/-- **Math.** Additivity of the raw Koszul functional in the test section:
`koszulRHSraw X Y (σ + σ') p = koszulRHSraw X Y σ p + koszulRHSraw X Y σ' p` for
`σ, σ'` differentiable at `p`. -/
theorem RiemannianMetric.koszulRHSraw_add (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) {σ σ' : Π q : M, TangentSpace I q} {p : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TangentBundle I M)) p)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ' y⟩ : TangentBundle I M)) p) :
    g.koszulRHSraw X Y (σ + σ') p
      = g.koszulRHSraw X Y σ p + g.koszulRHSraw X Y σ' p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hYσ := g.metricInner_raw_mdifferentiableAt (v := fun q => Y q) (Y.smoothAt p) hσ
  have hYσ' := g.metricInner_raw_mdifferentiableAt (v := fun q => Y q) (Y.smoothAt p) hσ'
  have hσX := g.metricInner_raw_mdifferentiableAt (w := fun q => X q) hσ (X.smoothAt p)
  have hσ'X := g.metricInner_raw_mdifferentiableAt (w := fun q => X q) hσ' (X.smoothAt p)
  simp only [RiemannianMetric.koszulRHSraw, Pi.add_apply,
    g.metricInner_add_right, g.metricInner_add_left,
    X.dir_add p hYσ hYσ', Y.dir_add p hσX hσ'X,
    VectorField.mlieBracket_add_right hσ hσ', dirTangent_add]
  ring

/-- **Math.** Homogeneity of the raw Koszul functional in the test section:
`koszulRHSraw X Y (f·σ) p = f(p)·koszulRHSraw X Y σ p` for `f, σ` differentiable
at `p`. The `X(f)`-type cross terms cancel by symmetry of the metric — the same
cancellation as in `koszulRHS_smul_right`. -/
theorem RiemannianMetric.koszulRHSraw_smul (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) {f : M → ℝ} {σ : Π q : M, TangentSpace I q} {p : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TangentBundle I M)) p) :
    g.koszulRHSraw X Y (f • σ) p = f p * g.koszulRHSraw X Y σ p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hYσ := g.metricInner_raw_mdifferentiableAt (v := fun q => Y q) (Y.smoothAt p) hσ
  have hσX := g.metricInner_raw_mdifferentiableAt (w := fun q => X q) hσ (X.smoothAt p)
  simp only [RiemannianMetric.koszulRHSraw, Pi.smul_apply',
    g.metricInner_smul_right, g.metricInner_smul_left,
    X.dir_mul p hf hYσ, Y.dir_mul p hf hσX,
    mlieBracket_field_smul_right_raw hf X hσ,
    mlieBracket_field_smul_right_raw hf Y hσ,
    g.metricInner_add_left, dirTangent_smul]
  have hsymm : g.metricInner p (Y p) (σ p) = g.metricInner p (σ p) (Y p) :=
    g.metricInner_comm p (Y p) (σ p)
  rw [hsymm]
  ring

/-- **Math.** **Tensoriality of the Koszul functional in the test field.** The
operator `σ ↦ koszulRHSraw X Y σ p` on tangent sections is additive and
`𝒟(M)`-homogeneous at `p`, i.e. `TensorialAt`. This is the hypothesis mathlib's
`TensorialAt.mkHom` consumes to produce the Koszul covector. -/
theorem RiemannianMetric.koszulRHSraw_tensorialAt (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (p : M) :
    TensorialAt I E (fun σ => g.koszulRHSraw X Y σ p) p where
  smul hf hσ := g.koszulRHSraw_smul X Y hf hσ
  add hσ hσ' := g.koszulRHSraw_add X Y hσ hσ'

/-- **Math.** The **Koszul covector** at `p`: the continuous linear functional
`T_pM → ℝ` realizing the tensorial Koszul functional, i.e.
`koszulCovec X Y p (Z p) = koszulRHS X Y Z p` for every smooth field `Z`
(`koszulCovec_apply`). Its metric-Riesz dual (halved) is the Levi-Civita
covariant derivative `∇_Y X` at `p`. -/
noncomputable def RiemannianMetric.koszulCovec [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (X Y : SmoothVectorField I M) (p : M) :
    TangentSpace I p →L[ℝ] ℝ :=
  TensorialAt.mkHom (fun σ => g.koszulRHSraw X Y σ p) p
    (g.koszulRHSraw_tensorialAt X Y p)

/-- **Math.** Defining property of the Koszul covector: it evaluates on `Z p` to
the Koszul functional `koszulRHS X Y Z p`. In particular the right-hand side
depends on `Z` only through `Z p`. -/
theorem RiemannianMetric.koszulCovec_apply [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (X Y Z : SmoothVectorField I M) (p : M) :
    g.koszulCovec X Y p (Z p) = g.koszulRHS X Y Z p := by
  rw [RiemannianMetric.koszulCovec,
    TensorialAt.mkHom_apply (g.koszulRHSraw_tensorialAt X Y p) (Z.smoothAt p)]
  exact g.koszulRHSraw_toFun X Y Z p

/-- **Math.** **Locality of the Koszul functional.** `koszulRHS X Y Z p` depends
on the test field `Z` only through the tangent vector `Z p`: two fields agreeing
at `p` give the same value. This is do Carmo's well-definedness of `∇`, discharged
by the tensoriality of the Koszul functional. -/
theorem RiemannianMetric.koszulRHS_local [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (X Y Z₁ Z₂ : SmoothVectorField I M) (p : M)
    (h : Z₁ p = Z₂ p) :
    g.koszulRHS X Y Z₁ p = g.koszulRHS X Y Z₂ p := by
  rw [← g.koszulCovec_apply X Y Z₁ p, ← g.koszulCovec_apply X Y Z₂ p, h]

/-- **Math.** The **Koszul-dual section** `p ↦ ♯_g(½ · koszulCovec X Y p)`: the
pointwise metric-Riesz dual of the halved Koszul covector. This is the candidate
value of the Levi-Civita covariant derivative `(∇_Y X) p`. Its only missing
property for assembling the Levi-Civita connection is *smoothness* as a section of
the tangent bundle (supplied by `metricRiesz_section_contMDiffAt`); the defining
Koszul relation it satisfies is purely algebraic (`koszulDualSection_dual`). -/
noncomputable def RiemannianMetric.koszulDualSection [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (X Y : SmoothVectorField I M) (p : M) :
    TangentSpace I p :=
  g.metricRiesz p ((1 / 2 : ℝ) • g.koszulCovec X Y p)

/-- **Math.** do Carmo Ch. 2, Thm. 3.6 (existence, Koszul dual relation). The
Koszul-dual section satisfies `2⟨(∇_Y X) p, Z p⟩ = koszulRHS X Y Z p` for every
test field `Z`, pointwise and with no smoothness assumption. This is exactly the
hypothesis `hdual` consumed by `DCAffineConnection.isLeviCivita_of_koszulDual`;
combined with smoothness of `koszulDualSection` it discharges the full existence
half of the Levi-Civita theorem. -/
theorem RiemannianMetric.koszulDualSection_dual [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (X Y Z : SmoothVectorField I M) (p : M) :
    2 * g.metricInner p (g.koszulDualSection X Y p) (Z p)
      = g.koszulRHS X Y Z p := by
  rw [RiemannianMetric.koszulDualSection,
    g.metricRiesz_inner p ((1 / 2 : ℝ) • g.koszulCovec X Y p) (Z p),
    ContinuousLinearMap.smul_apply, g.koszulCovec_apply X Y Z p, smul_eq_mul]
  ring

/-! ## The existence half of the Levi-Civita theorem — algebraic verification

Let `cov : 𝒳(M) × 𝒳(M) → 𝒳(M)` be a candidate connection whose covariant
derivative is the metric-Riesz dual of the Koszul functional, i.e.

`2⟨(cov Y X), Z⟩ = koszulRHS X Y Z`   (`hdual`).

Given the tensorial linearity of `koszulRHS` in `Z` (`koszulRHS_add_right`,
`koszulRHS_smul_right`) the pointwise Riesz dual `metricRiesz` yields such a
`cov`; the *smoothness* of that dual section is the remaining analytic input for
the full existence statement. Independently of smoothness, the two algebraic
identities below — do Carmo's "it is easy to verify that `∇` … satisfies the
desired conditions" — show that any such `cov` is symmetric and compatible with
the metric. They rest on two purely algebraic identities for `koszulRHS`. -/

omit [CompleteSpace E] in
/-- **Math.** Antisymmetrized Koszul identity: swapping the two connection slots
of `koszulRHS` recovers twice the bracket pairing,
`koszulRHS Y X Z − koszulRHS X Y Z = 2⟨[X,Y], Z⟩`. All directional-derivative
terms cancel by symmetry of the metric, and the bracket terms combine via the
antisymmetry `[Y,X] = −[X,Y]`. This is the algebraic core of the symmetry of the
Koszul-dual connection. -/
theorem RiemannianMetric.koszulRHS_antisymm_diff (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.koszulRHS Y X Z p - g.koszulRHS X Y Z p
      = 2 * g.metricInner p (DCLieBracket X Y p) (Z p) := by
  have hA : Y.dir (fun q => g.metricInner q (X q) (Z q)) p
      = Y.dir (fun q => g.metricInner q (Z q) (X q)) p :=
    congrArg (Y.dir · p) (funext fun q => g.metricInner_comm q (X q) (Z q))
  have hB : X.dir (fun q => g.metricInner q (Z q) (Y q)) p
      = X.dir (fun q => g.metricInner q (Y q) (Z q)) p :=
    congrArg (X.dir · p) (funext fun q => g.metricInner_comm q (Z q) (Y q))
  have hC : Z.dir (fun q => g.metricInner q (Y q) (X q)) p
      = Z.dir (fun q => g.metricInner q (X q) (Y q)) p :=
    congrArg (Z.dir · p) (funext fun q => g.metricInner_comm q (Y q) (X q))
  have hbr : g.metricInner p (DCLieBracket Y X p) (Z p)
      = -g.metricInner p (DCLieBracket X Y p) (Z p) := by
    rw [DCLieBracket_antisymm Y X p, g.metricInner_neg_left]
  simp only [RiemannianMetric.koszulRHS]
  linarith [hA, hB, hC, hbr]

omit [CompleteSpace E] in
/-- **Math.** Symmetrized Koszul identity: adding the two orderings that share
the same base field `X` recovers twice the derivative of the metric pairing,
`koszulRHS Y X Z + koszulRHS Z X Y = 2·X⟨Y,Z⟩`. The bracket terms cancel in pairs
by antisymmetry of the Lie bracket and the remaining derivative terms combine by
symmetry of the metric. This is the algebraic core of metric-compatibility of the
Koszul-dual connection. -/
theorem RiemannianMetric.koszulRHS_compat_sum (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.koszulRHS Y X Z p + g.koszulRHS Z X Y p
      = 2 * X.dir (fun q => g.metricInner q (Y q) (Z q)) p := by
  have hY : Y.dir (fun q => g.metricInner q (X q) (Z q)) p
      = Y.dir (fun q => g.metricInner q (Z q) (X q)) p :=
    congrArg (Y.dir · p) (funext fun q => g.metricInner_comm q (X q) (Z q))
  have hX : X.dir (fun q => g.metricInner q (Z q) (Y q)) p
      = X.dir (fun q => g.metricInner q (Y q) (Z q)) p :=
    congrArg (X.dir · p) (funext fun q => g.metricInner_comm q (Z q) (Y q))
  have hZ : Z.dir (fun q => g.metricInner q (Y q) (X q)) p
      = Z.dir (fun q => g.metricInner q (X q) (Y q)) p :=
    congrArg (Z.dir · p) (funext fun q => g.metricInner_comm q (Y q) (X q))
  have hbr1 : g.metricInner p (DCLieBracket Z Y p) (X p)
      = -g.metricInner p (DCLieBracket Y Z p) (X p) := by
    rw [DCLieBracket_antisymm Z Y p, g.metricInner_neg_left]
  have hbr2 : g.metricInner p (DCLieBracket Z X p) (Y p)
      = -g.metricInner p (DCLieBracket X Z p) (Y p) := by
    rw [DCLieBracket_antisymm Z X p, g.metricInner_neg_left]
  have hbr3 : g.metricInner p (DCLieBracket Y X p) (Z p)
      = -g.metricInner p (DCLieBracket X Y p) (Z p) := by
    rw [DCLieBracket_antisymm Y X p, g.metricInner_neg_left]
  simp only [RiemannianMetric.koszulRHS]
  linarith [hY, hX, hZ, hbr1, hbr2, hbr3]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 2, Thm. 3.6 (existence, metric-compatibility part).
Any candidate connection `cov` whose covariant derivative is the metric-Riesz
dual of the Koszul functional — `2⟨(cov Y X), Z⟩ = koszulRHS X Y Z` for every
test field `Z` (`hdual`) — is **compatible with the metric** in the sense of
eq. (4): `X⟨Y,Z⟩ = ⟨cov X Y, Z⟩ + ⟨Y, cov X Z⟩`. This is a pointwise identity,
needing no non-degeneracy: it follows directly from `hdual` (in the two orderings
sharing base field `X`) and the symmetrized Koszul identity
(`koszulRHS_compat_sum`). -/
theorem koszulDual_isMetricCompatible (g : RiemannianMetric I M)
    (cov : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M)
    (hdual : ∀ (X Y Z : SmoothVectorField I M) (p : M),
      2 * g.metricInner p ((cov Y X) p) (Z p) = g.koszulRHS X Y Z p)
    (X Y Z : SmoothVectorField I M) (p : M) :
    X.dir (fun q => g.metricInner q (Y q) (Z q)) p
      = g.metricInner p ((cov X Y) p) (Z p)
        + g.metricInner p (Y p) ((cov X Z) p) := by
  have h1 := hdual Y X Z p
  have h2 := hdual Z X Y p
  have hk := g.koszulRHS_compat_sum X Y Z p
  have hsym : g.metricInner p (Y p) ((cov X Z) p)
      = g.metricInner p ((cov X Z) p) (Y p) :=
    g.metricInner_comm p (Y p) ((cov X Z) p)
  rw [hsym]
  linarith [h1, h2, hk]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 2, Thm. 3.6 (existence, symmetry part). On a
finite-dimensional, σ-compact, Hausdorff Riemannian manifold, any candidate
connection `cov` whose covariant derivative is the metric-Riesz dual of the
Koszul functional (`hdual`) is **symmetric**: `cov X Y − cov Y X = [X,Y]`
pointwise. Testing against every tangent vector `w = Z p` (realized by
`exists_smoothVectorField_eq`), `hdual` in the two swapped orderings together
with the antisymmetrized Koszul identity (`koszulRHS_antisymm_diff`) equate the
inner products, and non-degeneracy of the metric (`metricInner_eq_iff_eq`) yields
the identity. -/
theorem koszulDual_isSymmetric [FiniteDimensional ℝ E] [SigmaCompactSpace M]
    [T2Space M] (g : RiemannianMetric I M)
    (cov : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M)
    (hdual : ∀ (X Y Z : SmoothVectorField I M) (p : M),
      2 * g.metricInner p ((cov Y X) p) (Z p) = g.koszulRHS X Y Z p)
    (X Y : SmoothVectorField I M) (p : M) :
    (cov X Y) p - (cov Y X) p = DCLieBracket X Y p := by
  refine (g.metricInner_eq_iff_eq p ((cov X Y) p - (cov Y X) p)
    (DCLieBracket X Y p)).mp ?_
  intro w
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq p w
  rw [← hZ, g.metricInner_sub_left]
  have h1 := hdual Y X Z p
  have h2 := hdual X Y Z p
  have hk := g.koszulRHS_antisymm_diff X Y Z p
  linarith [h1, h2, hk]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 2, Thm. 3.6 (existence, verification of the conditions).
On a finite-dimensional, σ-compact, Hausdorff Riemannian manifold, an affine
connection `∇` whose covariant derivative is the metric-Riesz dual of the Koszul
functional — `2⟨∇_Y X, Z⟩ = koszulRHS X Y Z` for every test field `Z`
(`hdual`) — is a **Levi-Civita connection** for `g`: it is both symmetric
(`koszulDual_isSymmetric`) and compatible with the metric
(`koszulDual_isMetricCompatible`).

Together with the uniqueness half `DCAffineConnection.leviCivita_unique'`, this
reduces the full Levi-Civita theorem (`thm:dc-ch2-3-6`) to the single remaining
analytic input: constructing *some* affine connection satisfying `hdual`, i.e.
exhibiting the pointwise metric-Riesz dual of the (tensorial) Koszul functional as
a *smooth* vector field. do Carmo dismisses this verification as "easy"; the
algebraic content is exactly this lemma. -/
theorem DCAffineConnection.isLeviCivita_of_koszulDual [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (nabla : DCAffineConnection I M)
    (hdual : ∀ (X Y Z : SmoothVectorField I M) (p : M),
      2 * g.metricInner p ((nabla.cov Y X) p) (Z p) = g.koszulRHS X Y Z p) :
    nabla.IsLeviCivita g :=
  ⟨fun X Y p => koszulDual_isSymmetric g nabla.cov hdual X Y p,
   fun X Y Z p => koszulDual_isMetricCompatible g nabla.cov hdual X Y Z p⟩

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 2, Thm. 3.6 — the Levi-Civita theorem, reduced to its
single analytic input. On a finite-dimensional, σ-compact, Hausdorff Riemannian
manifold, *if* some affine connection is the metric-Riesz dual of the Koszul
functional (`hexists` — the smoothness of that dual section is the one fact do
Carmo leaves to "it is easy to verify"), then there is a **unique** affine
connection that is both symmetric and compatible with the metric.

Existence of the Levi-Civita connection is the witness supplied by `hexists`
together with the verification `DCAffineConnection.isLeviCivita_of_koszulDual`;
uniqueness is `DCAffineConnection.leviCivita_unique'`. Thus the entire theorem is
reduced to constructing one smooth Koszul-dual connection. -/
theorem DCAffineConnection.exists_unique_isLeviCivita_of_koszulDual
    [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M)
    (hexists : ∃ nabla : DCAffineConnection I M,
      ∀ (X Y Z : SmoothVectorField I M) (p : M),
        2 * g.metricInner p ((nabla.cov Y X) p) (Z p) = g.koszulRHS X Y Z p) :
    ∃! nabla : DCAffineConnection I M, nabla.IsLeviCivita g := by
  obtain ⟨nabla, hdual⟩ := hexists
  have hLC := nabla.isLeviCivita_of_koszulDual g hdual
  exact ⟨nabla, hLC, fun n' hn' => leviCivita_unique' g n' nabla hn' hLC⟩

/-! ## Smoothness of the Koszul-dual section — the analytic input

The algebraic verification above reduces the full Levi-Civita theorem
(`thm:dc-ch2-3-6`) to constructing *one* smooth affine connection satisfying
`hdual`. The candidate is the metric-Riesz dual of the (tensorial) Koszul
covector, `koszulDualSection X Y`. What remains — do Carmo's "it is easy to
verify" — is that this pointwise section is **smooth**, so that `∇_Y X` is a
genuine `SmoothVectorField`. This section supplies that analytic input. -/

omit [CompleteSpace E] in
/-- **Math.** The directional derivative `X(F) : p ↦ dF_p(X_p)` of a smooth
scalar function `F` along a smooth vector field `X` is itself smooth. Indeed
`X(F) p` is the fibre component of the tangent map `Tf` of `F` evaluated on the
smooth tangent-bundle section `p ↦ (p, X_p)`; smoothness follows from
`ContMDiff.contMDiff_tangentMap` (the tangent map of a `C^∞` map is `C^∞`) and the
smoothness of the fibre projection of the model-space tangent bundle. -/
theorem SmoothVectorField.dir_contMDiff (X : SmoothVectorField I M) {F : M → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (X.dir F) := by
  have hcomp : X.dir F
      = (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2)
          ∘ (tangentMap I 𝓘(ℝ, ℝ) F)
          ∘ (fun p => (⟨p, X.toFun p⟩ : TangentBundle I M)) := by
    funext p
    simp only [Function.comp_apply, tangentMap, SmoothVectorField.dir]
  rw [hcomp]
  have h1 : ContMDiff I I.tangent ∞
      (fun p => (⟨p, X.toFun p⟩ : TangentBundle I M)) := X.smooth
  have h2 : ContMDiff I.tangent (𝓘(ℝ, ℝ)).tangent ∞ (tangentMap I 𝓘(ℝ, ℝ) F) :=
    hF.contMDiff_tangentMap (by simp)
  have h3 : ContMDiff (𝓘(ℝ, ℝ)).tangent 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2) :=
    contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)
  exact h3.comp (h2.comp h1)

omit [CompleteSpace E] in
/-- **Math.** The metric pairing `q ↦ ⟨Y(q), Z(q)⟩` of two smooth vector fields
is a smooth scalar function on `M`. `ContMDiff` upgrade of
`metricInner_field_mdifferentiableAt`. -/
theorem RiemannianMetric.metricInner_field_contMDiff (g : RiemannianMetric I M)
    (Y Z : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => g.metricInner q (Y q) (Z q)) := by
  intro p
  have h := g.metricInner_contMDiffWithinAt (s := Set.univ) (x := p) (n := (∞ : ℕ∞ω))
    (v := fun y => Y y) (w := fun y => Z y)
    ((Y.smooth p).contMDiffWithinAt) ((Z.smooth p).contMDiffWithinAt)
  rw [contMDiffWithinAt_univ] at h
  exact h

/-- **Math.** The Lie-bracket section `p ↦ [X, Y]_p` of two smooth vector fields
is `C^∞` as a section of the tangent bundle. `ContMDiff` companion of
`DCLieBracket_smoothAt` (which records only `C¹`). -/
theorem DCLieBracket_contMDiffAt (X Y : SmoothVectorField I M) (p : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, DCLieBracket X Y y⟩ : TangentBundle I M)) p := by
  haveI : IsManifold I ((⊤ : ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p := X.smooth p
  have hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) p := Y.smooth p
  have hbr : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, VectorField.mlieBracket I X.toFun Y.toFun y⟩ : TangentBundle I M)) p :=
    hX.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hY (by simp)
  exact hbr

/-- **Math.** The Koszul bracket term `p ↦ ⟨[X, Z]_p, W_p⟩` is a smooth scalar
function: the metric pairing of the `C^∞` bracket section with a smooth field. -/
theorem RiemannianMetric.metricInner_bracket_contMDiff (g : RiemannianMetric I M)
    (X Z W : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => g.metricInner q (DCLieBracket X Z q) (W q)) := by
  intro p
  have h := g.metricInner_contMDiffWithinAt (s := Set.univ) (x := p) (n := (∞ : ℕ∞ω))
    (v := fun y => DCLieBracket X Z y) (w := fun y => W y)
    ((DCLieBracket_contMDiffAt X Z p).contMDiffWithinAt) ((W.smooth p).contMDiffWithinAt)
  rw [contMDiffWithinAt_univ] at h
  exact h

/-- **Math.** The Koszul functional `p ↦ koszulRHS X Y Z p` is a smooth scalar
function of the base point, for smooth `X, Y, Z`. Its three directional-derivative
terms are smooth by `SmoothVectorField.dir_contMDiff`, its three bracket-pairing
terms by `metricInner_bracket_contMDiff`. This is the base-point smoothness that,
via Riesz duality, upgrades `koszulDualSection` to a `SmoothVectorField`. -/
theorem RiemannianMetric.koszulRHS_contMDiff (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (g.koszulRHS X Y Z) := by
  have hf1 := X.dir_contMDiff (g.metricInner_field_contMDiff Y Z)
  have hf2 := Y.dir_contMDiff (g.metricInner_field_contMDiff Z X)
  have hf3 := Z.dir_contMDiff (g.metricInner_field_contMDiff X Y)
  have hg1 := g.metricInner_bracket_contMDiff X Z Y
  have hg2 := g.metricInner_bracket_contMDiff Y Z X
  have hg3 := g.metricInner_bracket_contMDiff X Y Z
  exact ((((hf1.add hf2).sub hf3).sub hg1).sub hg2).sub hg3

open Bundle in
omit [CompleteSpace E] in
/-- **Math.** Local-to-global extension of a smooth tangent section. If `σ` is a
tangent section that is `C^∞` on an open set `s`, then near any point `x ∈ s` it
is the restriction of a *global* smooth vector field `Z ∈ 𝒳(M)`, i.e.
`Z =ᶠ[𝓝 x] σ`. Construction: by regularity of the (finite-dimensional, Hausdorff)
manifold pick an open `V ∋ x` with `closure V ⊆ s`; glue the constraint
`Z y ∈ {σ y}` on `V` with `Z y ∈ ⊤` elsewhere via
`exists_contMDiffSection_forall_mem_convex_of_local`, taking `σ` itself as the
local section near `closure V ⊆ s` and the zero section away from `closure V`.
This upgrades the tangent-vector extension `exists_smoothVectorField_eq` (agreement
at a single point) to agreement on a whole neighbourhood, the form needed to feed a
locally-defined chart frame into the globally-smooth Koszul functional. -/
theorem exists_smoothVectorField_eventuallyEq [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] {σ : Π q : M, TangentSpace I q} {s : Set M}
    (hs : IsOpen s)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, σ q⟩ : TangentBundle I M)) s)
    {x : M} (hx : x ∈ s) :
    ∃ Z : SmoothVectorField I M, ∀ᶠ y in nhds x, Z y = σ y := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K, hK_nhds, hK_closed, hK_sub⟩ :=
    exists_mem_nhds_isClosed_subset (hs.mem_nhds hx)
  set V : Set M := interior K with hV
  have hxV : x ∈ V := mem_interior_iff_mem_nhds.mpr hK_nhds
  have hV_open : IsOpen V := isOpen_interior
  have hclV_sub : closure V ⊆ s :=
    (hK_closed.closure_subset_iff.mpr interior_subset).trans hK_sub
  set t : (q : M) → Set (TangentSpace I q) :=
    fun q => if q ∈ V then {σ q} else Set.univ with ht
  have hconv : ∀ q, Convex ℝ (t q) := by
    intro q
    by_cases h : q ∈ V
    · simp only [ht, if_pos h]; exact convex_singleton (σ q)
    · simp only [ht, if_neg h]; exact convex_univ
  have hlocal : ∀ x₀ : M, ∃ U ∈ nhds x₀, ∃ s_loc : (q : M) → TangentSpace I q,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (⟨q, s_loc q⟩ : TangentBundle I M)) U ∧
        ∀ y ∈ U, s_loc y ∈ t y := by
    intro x₀
    by_cases hx0 : x₀ ∈ closure V
    · refine ⟨s, hs.mem_nhds (hclV_sub hx0), σ, hσ, ?_⟩
      intro y _
      by_cases hyV : y ∈ V
      · simp only [ht, if_pos hyV, Set.mem_singleton_iff]
      · simp only [ht, if_neg hyV]; exact Set.mem_univ _
    · refine ⟨(closure V)ᶜ, (isClosed_closure.isOpen_compl).mem_nhds hx0,
        fun q => (0 : TangentSpace I q), ?_, ?_⟩
      · exact (contMDiff_zeroSection ℝ (TangentSpace I)).contMDiffOn
      · intro y hy
        have hyV : y ∉ V := fun h => hy (subset_closure h)
        simp only [ht, if_neg hyV]; exact Set.mem_univ _
  obtain ⟨sglob, hsglob⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local I (n := (⊤ : ℕ∞))
      (TangentSpace I) t hconv hlocal
  refine ⟨⟨fun q => sglob q, sglob.contMDiff⟩, ?_⟩
  filter_upwards [hV_open.mem_nhds hxV] with y hy
  have hy' := hsglob y
  simp only [ht, if_pos hy, Set.mem_singleton_iff] at hy'
  exact hy'

/-- **Math.** do Carmo Ch. 2, Thm. 3.6 (existence, smoothness). The Koszul-dual
section `p ↦ ♯_g(½ · koszulCovec X Y p)` is a **smooth** vector field. This is the
one analytic input do Carmo leaves to "it is easy to verify". Working in the chart
frame at `p` via `metricRiesz_section_contMDiffAt_of_within`, the obligation
reduces per frame-index `j` to smoothness of
`y ↦ (koszulCovec X Y y)(chartBasisVecFiber p j y)`; extending the local chart
frame to a global smooth field `Z` (`exists_smoothVectorField_eventuallyEq`) and
using `koszulCovec_apply` identifies this with the globally smooth Koszul functional
`koszulRHS X Y Z` near `p` (`koszulRHS_contMDiff`). -/
theorem RiemannianMetric.koszulDualSection_contMDiffAt
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (p : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, g.koszulDualSection X Y y⟩ : TangentBundle I M)) p := by
  have hx : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  refine Tensor.metricRiesz_section_contMDiffAt_of_within g (α := p) hx
    (Φ := fun y => (1 / 2 : ℝ) • g.koszulCovec X Y y) ?_
  intro j
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => Tensor.chartBasisVecFiber (I := I) p j q)
    (s := (trivializationAt E (TangentSpace I) p).baseSet) hbaseopen
    (Tensor.chartBasisVec_contMDiffOn (I := I) p j) hx
  have hsmooth : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (g.koszulRHS X Y Z)
      (trivializationAt E (TangentSpace I) p).baseSet p :=
    (g.koszulRHS_contMDiff X Y Z p).contMDiffWithinAt
  have heq : (fun y => g.koszulCovec X Y y (Tensor.chartBasisVecFiber (I := I) p j y))
      =ᶠ[nhds p] (fun y => g.koszulRHS X Y Z y) := by
    filter_upwards [hZ] with y hy
    rw [← hy]; exact g.koszulCovec_apply X Y Z y
  have hcrux : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun y => g.koszulCovec X Y y (Tensor.chartBasisVecFiber (I := I) p j y))
      (trivializationAt E (TangentSpace I) p).baseSet p :=
    hsmooth.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact (contMDiffWithinAt_const).mul hcrux

/-- **Math.** The Levi-Civita covariant derivative `(∇_A B)` bundled as a genuine
`SmoothVectorField`: the smooth Koszul-dual section `p ↦ ♯_g(½ · koszulCovec B A p)`
(smoothness by `koszulDualSection_contMDiffAt`). The slot order matches the pairing
`koszulDualSection_dual`, so `∇_A B` is `koszulDualSection B A`. -/
noncomputable def RiemannianMetric.leviCivitaCovField [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (A B : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun p => g.koszulDualSection B A p
  smooth := fun p => g.koszulDualSection_contMDiffAt B A p

@[simp] theorem RiemannianMetric.leviCivitaCovField_apply [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    (A B : SmoothVectorField I M) (p : M) :
    g.leviCivitaCovField A B p = g.koszulDualSection B A p := rfl

/-- **Math.** do Carmo Ch. 2, Thm. 3.6 — the **Levi-Civita connection** of a
Riemannian metric on a finite-dimensional, σ-compact, Hausdorff manifold,
constructed as the metric-Riesz dual of the Koszul functional:
`(∇_A B) := ♯_g(½ · koszulCovec B A)`. The four affine-connection axioms are the
`𝒟(M)`-linearity identities of `koszulRHS` transported through the pointwise
non-degeneracy of the metric (`metricInner_eq_iff_eq`, tested against every tangent
vector realized by `exists_smoothVectorField_eq`) and the Koszul-dual relation
`koszulDualSection_dual`. -/
noncomputable def RiemannianMetric.leviCivitaConnection [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M) :
    DCAffineConnection I M where
  cov := fun A B => g.leviCivitaCovField A B
  add_left := by
    intro X Y Z
    refine SmoothVectorField.ext (fun p => ?_)
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p (g.koszulDualSection Z (X + Y) p) (W p)
      = g.metricInner p ((g.leviCivitaCovField X Z + g.leviCivitaCovField Y Z) p) (W p)
    rw [SmoothVectorField.add_apply, g.metricInner_add_left]
    have hL := g.koszulDualSection_dual Z (X + Y) W p
    have hX := g.koszulDualSection_dual Z X W p
    have hY := g.koszulDualSection_dual Z Y W p
    have hk := g.koszulRHS_add_middle Z X Y W p
    show g.metricInner p (g.koszulDualSection Z (X + Y) p) (W p)
      = g.metricInner p (g.koszulDualSection Z X p) (W p)
        + g.metricInner p (g.koszulDualSection Z Y p) (W p)
    linarith [hL, hX, hY, hk]
  smul_left := by
    intro f hf X Z
    refine SmoothVectorField.ext (fun p => ?_)
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p (g.koszulDualSection Z (SmoothVectorField.smul f hf X) p) (W p)
      = g.metricInner p ((SmoothVectorField.smul f hf (g.leviCivitaCovField X Z)) p) (W p)
    rw [SmoothVectorField.smul_apply, g.metricInner_smul_left]
    have hL := g.koszulDualSection_dual Z (SmoothVectorField.smul f hf X) W p
    have hX := g.koszulDualSection_dual Z X W p
    have hk := g.koszulRHS_smul_middle hf Z X W p
    show g.metricInner p (g.koszulDualSection Z (SmoothVectorField.smul f hf X) p) (W p)
      = f p * g.metricInner p (g.koszulDualSection Z X p) (W p)
    linear_combination (1 / 2 : ℝ) * hL + (1 / 2 : ℝ) * hk - (f p / 2) * hX
  add_right := by
    intro X Y Z
    refine SmoothVectorField.ext (fun p => ?_)
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p (g.koszulDualSection (Y + Z) X p) (W p)
      = g.metricInner p ((g.leviCivitaCovField X Y + g.leviCivitaCovField X Z) p) (W p)
    rw [SmoothVectorField.add_apply, g.metricInner_add_left]
    have hL := g.koszulDualSection_dual (Y + Z) X W p
    have hY := g.koszulDualSection_dual Y X W p
    have hZ := g.koszulDualSection_dual Z X W p
    have hk := g.koszulRHS_add_left Y Z X W p
    show g.metricInner p (g.koszulDualSection (Y + Z) X p) (W p)
      = g.metricInner p (g.koszulDualSection Y X p) (W p)
        + g.metricInner p (g.koszulDualSection Z X p) (W p)
    linarith [hL, hY, hZ, hk]
  leibniz := by
    intro f hf X Y p
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p (g.koszulDualSection (SmoothVectorField.smul f hf Y) X p) (W p)
      = g.metricInner p (f p • g.leviCivitaCovField X Y p
          + (SmoothVectorField.dir X f p) • Y p) (W p)
    rw [g.metricInner_add_left, g.metricInner_smul_left, g.metricInner_smul_left]
    have hL := g.koszulDualSection_dual (SmoothVectorField.smul f hf Y) X W p
    have hXY := g.koszulDualSection_dual Y X W p
    have hk := g.koszulRHS_leibniz_left hf Y X W p
    show g.metricInner p (g.koszulDualSection (SmoothVectorField.smul f hf Y) X p) (W p)
      = f p * g.metricInner p (g.koszulDualSection Y X p) (W p)
        + SmoothVectorField.dir X f p * g.metricInner p (Y p) (W p)
    linear_combination (1 / 2 : ℝ) * hL + (1 / 2 : ℝ) * hk - (f p / 2) * hXY

/-- **Math.** do Carmo Ch. 2, Thm. 3.6 — the **Levi-Civita theorem**,
unconditional. On a finite-dimensional, σ-compact, Hausdorff Riemannian manifold
there is a **unique** affine connection that is symmetric and compatible with the
metric. Existence is the smooth Koszul-dual connection `leviCivitaConnection`
(it satisfies the Koszul-dual relation `koszulDualSection_dual`); uniqueness is
`DCAffineConnection.leviCivita_unique'`. This closes the last analytic input
(`hexists`) of `exists_unique_isLeviCivita_of_koszulDual`. -/
theorem RiemannianMetric.exists_unique_isLeviCivita [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M) :
    ∃! nabla : DCAffineConnection I M, nabla.IsLeviCivita g :=
  DCAffineConnection.exists_unique_isLeviCivita_of_koszulDual g
    ⟨g.leviCivitaConnection, fun X Y Z p => g.koszulDualSection_dual X Y Z p⟩

end PetersenLib
