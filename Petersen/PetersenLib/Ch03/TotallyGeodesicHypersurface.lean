import PetersenLib.Ch03.SchurLemma
import PetersenLib.Ch03.GaussCodazzi
import PetersenLib.Ch03.RiemannConstantCurvature
import PetersenLib.Ch02.MetricOperator
import PetersenLib.Ch02.ExercisesProductRule

/-!
# Petersen Ch. 3, §3.4 — Exercise 3.4.13(2): the totally-geodesic-hypersurface
property forces constant curvature

A hypersurface is **totally geodesic** if its second fundamental form vanishes.
Petersen's Exercise 3.4.13 asks: (1) the space forms `S^n_k` have the property
that every tangent vector is normal to a totally geodesic hypersurface; (2) a
Riemannian `n`-manifold with `n > 2` and this property has constant curvature.

Part (1) needs explicit space-form models (round spheres, hyperbolic space) that
do not exist in `PetersenLib`, so only **part (2)** is formalized here, as
`exercise3_4_13`.

The property is encoded, at each unit vector `v ∈ T_pM`, by the level-set data
of the totally geodesic hypersurface through `p` normal to `v`: a smooth defining
function `f` with unit normal `N = c·∇f` (`c²|∇f|² ≡ 1`) with `N(p) = v` on an
open `U ∋ p`, whose second fundamental form vanishes on every pair of level-set
tangent fields over `U`.

## Proof (following the exercise's hint)

Fix `p` and a unit `n ∈ T_pM`. For level-set tangent fields `A, B, Z` (i.e.
`df ≡ 0` on `U`), the Peterson–Codazzi–Mainardi equation
(`normalCurvatureEquation`) reads `g(R(A,B)Z, N) = −(∇_AΠ)(B,Z) + (∇_BΠ)(A,Z)`,
and every term of `∇Π` vanishes because `Π ≡ 0` on `U` (the hypersurface is
totally geodesic). Hence `g(R(a,b)z, n) = 0` for all `a, b, z ⊥ n`; by
`antisymm₃₄` this gives `g(R(a,b)n, t) = 0` for all `t`, so `R(a,b)n = 0`
whenever `a, b ⊥ n` — exactly the exercise's `R(X,Y)Z = 0` on pairwise
orthogonal triples. Feeding this (in a `g`-orthonormal basis, via
`isAlgCurvatureForm_curvatureTensorFourAt`) into the algebraic argument of
Exercise 3.4.10 gives, at every point, the diagonal identity
`R(x,y,x,y) = k·|x∧y|²`; `sectionalCurvature_const_of_diag` turns this into
pointwise-constant sectional curvature, and `schurLemma` (with `n ≥ 3` and `M`
connected) promotes it to a single global constant.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.4, Exercise 3.4.13.
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-! ## A smooth global field tangent to a level set through a prescribed value -/

/-- **Eng.** Given a unit normal field `N` (with `|N| ≡ 1` on `U`) and a tangent
vector `a ⊥ N(p)` at `p`, there is a smooth global vector field `A` with
`A(p) = a` that is `g`-orthogonal to `N` on all of `U` (i.e. tangent to the
level sets): project the bump extension of `a` off `N`. -/
private theorem exists_levelSet_tangent_field
    {N : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    {U : Set M} (hunit : ∀ q ∈ U, g.metricInner q (N q) (N q) = 1)
    {p : M} (a : TangentSpace I p) (ha : g.metricInner p a (N p) = 0) :
    ∃ A : Π x : M, TangentSpace I x, IsSmoothVectorField A ∧ A p = a ∧
      ∀ q ∈ U, g.metricInner q (A q) (N q) = 0 := by
  classical
  set Ā : Π x : M, TangentSpace I x := ⇑(extendTangentVector p a) with hĀdef
  have hĀ : IsSmoothVectorField Ā := (extendTangentVector p a).smooth
  set coeff : M → ℝ := fun q => g.metricInner q (Ā q) (N q) with hcoeffdef
  have hcoeff : ContMDiff I 𝓘(ℝ) ∞ coeff := by
    have h := (metricOperator_isTensorOperator g).smooth_eval ![Ā, N] (by
      intro i; fin_cases i
      · simpa using hĀ
      · simpa using hN)
    have e : metricOperator g ![Ā, N] = coeff := by
      funext q; simp [metricOperator, hcoeffdef]
    rwa [e] at h
  refine ⟨fun q => Ā q - coeff q • N q, ?_, ?_, ?_⟩
  · have hsm := ((⟨Ā, hĀ⟩ : SmoothVectorField I M)
      - SmoothVectorField.smul coeff hcoeff ⟨N, hN⟩).smooth
    simpa [SmoothVectorField.smul] using hsm
  · have hcp : coeff p = 0 := by
      simp only [hcoeffdef, hĀdef, extendTangentVector_apply]; exact ha
    show Ā p - coeff p • N p = a
    rw [hcp, zero_smul, sub_zero, hĀdef, extendTangentVector_apply]
  · intro q hq
    show g.metricInner q (Ā q - coeff q • N q) (N q) = 0
    rw [g.metricInner_sub_left, g.metricInner_smul_left, hunit q hq, mul_one]
    simp only [hcoeffdef, sub_self]

/-! ## The pointwise vanishing of `R(a,b)n` for `a, b ⊥ n` -/

/-- **Math.** If every unit `v ∈ T_pM` is normal to a totally geodesic
hypersurface (encoded by the level-set data of `hP`), then for the unit vector
`n` and any `a, b` `g`-orthogonal to `n`, the curvature vanishes:
`R(a,b)n = 0`. This is the differential-geometric core of the exercise,
combining the Codazzi equation `normalCurvatureEquation` (all terms killed by
`Π ≡ 0`) with the antisymmetry of the `(0,4)`-tensor. -/
private theorem curvatureAt_normal_eq_zero
    (D : RiemannianConnection I g)
    (hP : ∀ p : M, ∀ v : TangentSpace I p, g.metricInner p v v = 1 →
      ∃ (f : M → ℝ) (c : M → ℝ) (U : Set M),
        ContMDiff I 𝓘(ℝ) ∞ f ∧ ContMDiff I 𝓘(ℝ) ∞ c ∧
          IsSmoothVectorField (gradient g f) ∧ IsOpen U ∧ p ∈ U ∧
          (∀ q ∈ U, c q * c q
            * g.metricInner q (gradient g f q) (gradient g f q) = 1) ∧
          c p • gradient g f p = v ∧
          (∀ X Y : Π x : M, TangentSpace I x, IsSmoothVectorField X →
            IsSmoothVectorField Y →
            (∀ q ∈ U, mfderiv I 𝓘(ℝ) f q (X q) = 0) →
            (∀ q ∈ U, mfderiv I 𝓘(ℝ) f q (Y q) = 0) →
            ∀ q ∈ U, secondFundamentalForm D.toAffineConnection g
                (fun r => c r • gradient g f r) X Y q = 0))
    (p : M) (n a b : TangentSpace I p) (hn1 : g.metricInner p n n = 1)
    (ha : g.metricInner p a n = 0) (hb : g.metricInner p b n = 0) :
    curvatureTensorAt D.toAffineConnection p a b n = 0 := by
  classical
  obtain ⟨fl, c, U, hf, hc, hgrad, hUopen, hpU, hnorm, hNv, hPi0⟩ := hP p n hn1
  set N : Π x : M, TangentSpace I x := fun q => c q • gradient g fl q with hNdef
  have hN : IsSmoothVectorField N := isSmoothVectorField_smul hc hgrad
  have hNp : N p = n := hNv
  have hunit : ∀ q ∈ U, g.metricInner q (N q) (N q) = 1 := by
    intro q hq
    show g.metricInner q (c q • gradient g fl q) (c q • gradient g fl q) = 1
    rw [g.metricInner_smul_left, g.metricInner_smul_right, ← mul_assoc]
    exact hnorm q hq
  have hc_ne : ∀ q ∈ U, c q ≠ 0 := by
    intro q hq h0
    have h1 := hnorm q hq
    rw [h0] at h1; simp at h1
  have htan_of_g : ∀ (W : Π x : M, TangentSpace I x),
      (∀ q ∈ U, g.metricInner q (W q) (N q) = 0) →
      ∀ q ∈ U, mfderiv I 𝓘(ℝ) fl q (W q) = 0 := by
    intro W hW q hq
    have hkeyeq : g.metricInner q (W q) (N q)
        = c q * g.metricInner q (gradient g fl q) (W q) := by
      show g.metricInner q (W q) (c q • gradient g fl q) = _
      rw [g.metricInner_smul_right, g.metricInner_comm q (W q) (gradient g fl q)]
    have h1 : c q * g.metricInner q (gradient g fl q) (W q) = 0 := by
      rw [← hkeyeq]; exact hW q hq
    have h0 : g.metricInner q (gradient g fl q) (W q) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (hc_ne q hq)
      · exact h
    rw [← metricInner_gradient g fl q (W q)]; exact h0
  have htanCov : ∀ (dir Y : Π x : M, TangentSpace I x) (q : M), q ∈ U →
      g.metricInner q (tangentialCovField D.toAffineConnection g N dir Y q) (N q)
        = 0 := by
    intro dir Y q hq
    rw [tangentialCovField_apply, tangentialCov_apply, g.metricInner_sub_left,
      g.metricInner_smul_left, hunit q hq, mul_one, sub_self]
  -- the covariant derivative of `Π` vanishes at `p` on level-set tangent fields
  have hsFCD : ∀ (dir Y Z : Π x : M, TangentSpace I x),
      IsSmoothVectorField dir → IsSmoothVectorField Y → IsSmoothVectorField Z →
      (∀ q ∈ U, mfderiv I 𝓘(ℝ) fl q (Y q) = 0) →
      (∀ q ∈ U, mfderiv I 𝓘(ℝ) fl q (Z q) = 0) →
      secondFundamentalFormCovariantDerivative D.toAffineConnection g N dir Y Z p
        = 0 := by
    intro dir Y Z hdir hY hZ hYdf hZdf
    have ht1 : directionalDerivative dir
        (fun q => secondFundamentalForm D.toAffineConnection g N Y Z q) p = 0 := by
      have hloc : (fun q => secondFundamentalForm D.toAffineConnection g N Y Z q)
          =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [hUopen.mem_nhds hpU] with q hq
        exact hPi0 Y Z hY hZ hYdf hZdf q hq
      rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]; rfl
    have hcovY : IsSmoothVectorField
        (tangentialCovField D.toAffineConnection g N dir Y) :=
      isSmoothVectorField_tangentialCovField D.toAffineConnection hN hdir hY
    have hcovZ : IsSmoothVectorField
        (tangentialCovField D.toAffineConnection g N dir Z) :=
      isSmoothVectorField_tangentialCovField D.toAffineConnection hN hdir hZ
    have ht2 : secondFundamentalForm D.toAffineConnection g N
        (tangentialCovField D.toAffineConnection g N dir Y) Z p = 0 :=
      hPi0 _ Z hcovY hZ (htan_of_g _ (fun q hq => htanCov dir Y q hq)) hZdf p hpU
    have ht3 : secondFundamentalForm D.toAffineConnection g N Y
        (tangentialCovField D.toAffineConnection g N dir Z) p = 0 :=
      hPi0 Y _ hY hcovZ hYdf (htan_of_g _ (fun q hq => htanCov dir Z q hq)) p hpU
    rw [secondFundamentalFormCovariantDerivative, ht1, ht2, ht3]; ring
  -- build the two fixed tangent fields `A ↦ a`, `B_f ↦ b`
  obtain ⟨A, hA, hAp, hAtan⟩ :=
    exists_levelSet_tangent_field hN hunit a (by rw [hNp]; exact ha)
  obtain ⟨B_f, hB_f, hBp, hBtan⟩ :=
    exists_levelSet_tangent_field hN hunit b (by rw [hNp]; exact hb)
  have hAdf : ∀ q ∈ U, mfderiv I 𝓘(ℝ) fl q (A q) = 0 := htan_of_g A hAtan
  have hBdf : ∀ q ∈ U, mfderiv I 𝓘(ℝ) fl q (B_f q) = 0 := htan_of_g B_f hBtan
  -- for each level-set tangent value `z ⊥ n`, `g(R(a,b)z, n) = 0`
  have hstep : ∀ (z : TangentSpace I p), g.metricInner p z n = 0 →
      curvatureTensorFourAt D p a b z n = 0 := by
    intro z hz
    obtain ⟨Z, hZ, hZp, hZtan⟩ :=
      exists_levelSet_tangent_field hN hunit z (by rw [hNp]; exact hz)
    have hZdf : ∀ q ∈ U, mfderiv I 𝓘(ℝ) fl q (Z q) = 0 := htan_of_g Z hZtan
    have hbr : g.metricInner p (N p) (lieDerivativeVectorField I A B_f p) = 0 := by
      have hbrdd := bracket_tangent_levelSet hf hA hB_f hUopen
        (fun q hq => hAdf q hq) (fun q hq => hBdf q hq) hpU
      show g.metricInner p (c p • gradient g fl p)
          (lieDerivativeVectorField I A B_f p) = 0
      rw [g.metricInner_smul_left, metricInner_gradient,
        ← directionalDerivative_apply, hbrdd, mul_zero]
    have key := normalCurvatureEquation D hUopen hN hA hB_f hZ hunit hZtan hpU hbr
    rw [hsFCD A B_f Z hA hB_f hZ hBdf hZdf,
      hsFCD B_f A Z hB_f hA hZ hAdf hZdf] at key
    have hz0 : curvatureTensorFour D A B_f Z N p = 0 := by rw [key]; ring
    have e := curvatureTensorFourAt_apply (D := D) (W := N) hA hB_f hZ p
    rw [hAp, hBp, hZp, hNp] at e
    rw [e, hz0]
  -- promote to `R(a,b)n = 0`
  have hB := isAlgCurvatureForm_curvatureTensorFourAt D p
  have hall : ∀ t : TangentSpace I p, curvatureTensorFourAt D p a b n t = 0 := by
    intro t
    have hsr : curvatureTensorFourAt D p a b n n = 0 := hB.self_right a b n
    set t0 := t - g.metricInner p t n • n with ht0
    have ht0n : g.metricInner p t0 n = 0 := by
      rw [ht0, g.metricInner_sub_left, g.metricInner_smul_left, hn1, mul_one,
        sub_self]
    have hexp : curvatureTensorFourAt D p a b t n
        = curvatureTensorFourAt D p a b t0 n
          + g.metricInner p t n * curvatureTensorFourAt D p a b n n := by
      conv_lhs => rw [show t = t0 + g.metricInner p t n • n by rw [ht0]; abel]
      rw [hB.add_three, hB.smul_three]
    have htn : curvatureTensorFourAt D p a b t n = 0 := by
      rw [hexp, hstep t0 ht0n, hsr]; ring
    rw [hB.antisymm₃₄ a b n t, htn, neg_zero]
  refine (g.metricInner_eq_iff_eq p _ 0).mp (fun Z => ?_)
  rw [g.metricInner_zero_left]
  exact hall Z

/-! ## Pointwise constant curvature from orthogonal vanishing -/

/-- **Math.** The algebraic core of Exercise 3.4.10, run in a `g`-orthonormal
basis: if `R(a,b)z = 0` for all `a, b` `g`-orthogonal to `z`, then at `p` the
`(0,4)`-curvature form is a scalar multiple of the bivector inner product,
`R(x,y,x,y) = k·|x∧y|²`. -/
private theorem exists_diag_const_of_orthogonal_vanishing
    (D : RiemannianConnection I g) (p : M) (hn : 3 ≤ Module.finrank ℝ E)
    (hkey : ∀ z a b : TangentSpace I p, g.metricInner p a z = 0 →
      g.metricInner p b z = 0 → curvatureTensorAt D.toAffineConnection p a b z = 0) :
    ∃ k : ℝ, ∀ x y : TangentSpace I p,
      curvatureTensorFourAt D p x y x y = k * bivectorInnerProduct g p x y x y := by
  classical
  have hB := isAlgCurvatureForm_curvatureTensorFourAt D p
  have hBvanish : ∀ v w z : TangentSpace I p, g.metricInner p v z = 0 →
      g.metricInner p w z = 0 → ∀ t, curvatureTensorFourAt D p v w z t = 0 := by
    intro v w z hv hw t
    show g.metricInner p (curvatureTensorAt D.toAffineConnection p v w z) t = 0
    rw [hkey z v w hv hw, g.metricInner_zero_left]
  obtain ⟨b, hOB⟩ := exists_metricOrthonormalBasis g p
  have hn2 : 2 ≤ Module.finrank ℝ (TangentSpace I p) := by
    have he : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
    omega
  generalize hn'def : Module.finrank ℝ (TangentSpace I p) = n' at b hOB hn2
  set G := g.metricBilin p with hGdef
  have hGsymm : ∀ x y : TangentSpace I p, G x y = G y x := by
    intro x y
    rw [hGdef, RiemannianMetric.metricBilin_apply,
      RiemannianMetric.metricBilin_apply]
    exact g.metricInner_comm p x y
  have hGval : ∀ i j : Fin n', G (b i) (b j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hGdef, RiemannianMetric.metricBilin_apply]; exact hOB i j
  have H1 : ∀ i j k l : Fin n', i ≠ k → j ≠ k →
      curvatureTensorFourAt D p (b i) (b j) (b k) (b l) = 0 := by
    intro i j k l hik hjk
    refine hBvanish (b i) (b j) (b k) ?_ ?_ (b l)
    · rw [hOB]; simp [hik]
    · rw [hOB]; simp [hjk]
  have connect : ∀ v a c : Fin n', a ≠ v → c ≠ v → a ≠ c →
      curvatureTensorFourAt D p (b v) (b a) (b v) (b a)
        = curvatureTensorFourAt D p (b v) (b c) (b v) (b c) := by
    intro v a c hav hcv hac
    have hva : g.metricInner p (b v) (b a) = 0 := by rw [hOB]; simp [Ne.symm hav]
    have hvc : g.metricInner p (b v) (b c) = 0 := by rw [hOB]; simp [Ne.symm hcv]
    have hac' : g.metricInner p (b a) (b c) = 0 := by rw [hOB]; simp [hac]
    have hz2 : g.metricInner p (b v) (b a - b c) = 0 := by
      rw [g.metricInner_sub_right, hva, hvc, sub_zero]
    have hz3 : g.metricInner p (b a + b c) (b a - b c) = 0 := by
      rw [g.metricInner_add_left, g.metricInner_sub_right, g.metricInner_sub_right,
        hac', hOB a a, hOB c a, hOB c c, if_pos rfl, if_pos rfl,
        if_neg (Ne.symm hac)]
      ring
    have h0 := hBvanish (b v) (b a + b c) (b a - b c) hz2 hz3 (b v)
    have hsub : b a - b c = b a + (-1 : ℝ) • b c := by rw [neg_one_smul]; abel
    have hexpand : curvatureTensorFourAt D p (b v) (b a + b c) (b a - b c) (b v)
        = curvatureTensorFourAt D p (b v) (b a) (b a) (b v)
          - curvatureTensorFourAt D p (b v) (b a) (b c) (b v)
          + curvatureTensorFourAt D p (b v) (b c) (b a) (b v)
          - curvatureTensorFourAt D p (b v) (b c) (b c) (b v) := by
      rw [hsub, hB.add_two, hB.add_three, hB.add_three, hB.smul_three,
        hB.smul_three]
      ring
    rw [hexpand] at h0
    have hcr1 : curvatureTensorFourAt D p (b v) (b a) (b c) (b v) = 0 :=
      H1 v a c v (Ne.symm hcv) hac
    have hcr2 : curvatureTensorFourAt D p (b v) (b c) (b a) (b v) = 0 :=
      H1 v c a v (Ne.symm hav) (Ne.symm hac)
    have hdg : curvatureTensorFourAt D p (b v) (b a) (b a) (b v)
        = curvatureTensorFourAt D p (b v) (b c) (b c) (b v) := by
      linarith [h0, hcr1, hcr2]
    have hsa := hB.antisymm₃₄ (b v) (b a) (b v) (b a)
    have hsc := hB.antisymm₃₄ (b v) (b c) (b v) (b c)
    linarith [hdg, hsa, hsc]
  have swapS : ∀ i j : Fin n', curvatureTensorFourAt D p (b i) (b j) (b i) (b j)
      = curvatureTensorFourAt D p (b j) (b i) (b j) (b i) := by
    intro i j
    have h1 := hB.antisymm₁₂ (b i) (b j) (b i) (b j)
    have h2 := hB.antisymm₃₄ (b j) (b i) (b i) (b j)
    linarith
  have hi0 : (0 : ℕ) < n' := by omega
  have hi1 : (1 : ℕ) < n' := by omega
  set i0 : Fin n' := ⟨0, hi0⟩ with hi0def
  set i1 : Fin n' := ⟨1, hi1⟩ with hi1def
  have hi01 : i0 ≠ i1 := by intro h; simp [hi0def, hi1def, Fin.ext_iff] at h
  set k' : ℝ := curvatureTensorFourAt D p (b i0) (b i1) (b i0) (b i1) with hk'def
  have Sconst : ∀ i j : Fin n', i ≠ j →
      curvatureTensorFourAt D p (b i) (b j) (b i) (b j) = k' := by
    intro i j hij
    rw [hk'def]
    rcases eq_or_ne i i0 with hi | hi
    · subst hi
      rcases eq_or_ne j i1 with hj | hj
      · subst hj; rfl
      · exact connect i0 j i1 hij.symm hi01.symm hj
    · rcases eq_or_ne i i1 with hi' | hi'
      · subst hi'
        rcases eq_or_ne j i0 with hj | hj
        · subst hj; exact (swapS i0 i1).symm
        · exact (connect i1 j i0 hij.symm hi01 hj).trans (swapS i1 i0)
      · rcases eq_or_ne j i0 with hj | hj
        · subst hj
          rw [swapS i i0, connect i0 i i1 hi hi01.symm hi']
        · rcases eq_or_ne j i1 with hj' | hj'
          · subst hj'
            rw [swapS i i1, connect i1 i i0 hi' hi01 hi]
            exact (swapS i0 i1).symm
          · rw [connect i j i0 hij.symm hi.symm hj, swapS i i0,
              connect i0 i i1 hi hi01.symm hi']
  have hbiv : ∀ i j k l : Fin n', bivectorPairing G (b i) (b j) (b k) (b l)
      = (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0) := by
    intro i j k l; simp only [bivectorPairing, hGval]
  have quad : ∀ i j k l : Fin n',
      curvatureTensorFourAt D p (b i) (b j) (b k) (b l)
        = k' * bivectorPairing G (b i) (b j) (b k) (b l) := by
    intro i j k l
    rw [hbiv]
    by_cases hij : i = j
    · subst hij; rw [hB.self_left]; ring
    by_cases hkl : k = l
    · subst hkl; rw [hB.self_right]; ring
    by_cases hik : i = k
    · subst hik
      have hil : i ≠ l := hkl
      by_cases hjl : j = l
      · subst hjl
        rw [Sconst i j hij, if_pos rfl, if_pos rfl, if_neg hij,
          if_neg (Ne.symm hij)]
        ring
      · have hval : curvatureTensorFourAt D p (b i) (b j) (b i) (b l) = 0 := by
          rw [hB.antisymm₃₄ (b i) (b j) (b i) (b l), H1 i j l i hil hjl, neg_zero]
        rw [hval, if_pos rfl, if_neg hjl, if_neg hil, if_neg (Ne.symm hij)]
        ring
    · by_cases hjk : j = k
      · subst hjk
        have hjl : j ≠ l := hkl
        by_cases hli : l = i
        · have hval : curvatureTensorFourAt D p (b i) (b j) (b j) (b i) = -k' := by
            rw [hB.antisymm₃₄ (b i) (b j) (b j) (b i), Sconst i j hij]
          rw [hli, hval, if_neg hij, if_neg (Ne.symm hij), if_pos rfl, if_pos rfl]
          ring
        · have hval : curvatureTensorFourAt D p (b i) (b j) (b j) (b l) = 0 := by
            rw [hB.antisymm₃₄ (b i) (b j) (b j) (b l),
              H1 i j l j (Ne.symm hli) hjl, neg_zero]
          rw [hval, if_neg hij, if_neg hjl, if_neg (Ne.symm hli), if_pos rfl]
          ring
      · have hval : curvatureTensorFourAt D p (b i) (b j) (b k) (b l) = 0 :=
          H1 i j k l hik hjk
        rw [hval, if_neg hik, if_neg hjk]; ring
  have hfull := hB.ext_basis ((isAlgCurvatureForm_bivectorPairing G hGsymm).smul k')
    b quad
  refine ⟨k', fun x y => ?_⟩
  rw [hfull x y x y, ← bivectorInnerProduct_eq_bivectorPairing]

/-! ## Exercise 3.4.13(2) -/

/-- **Math.** Petersen §3.4, Exercise 3.4.13(2): a Riemannian `n`-manifold with
`n > 2` in which every unit tangent vector is normal to a **totally geodesic**
hypersurface has **constant curvature**.

The property is encoded, at each unit `v ∈ T_pM`, by the level-set data of the
hypersurface: a smooth defining function `f` and normalizing factor `c` with
unit normal `N = c·∇f` (`c²|∇f|² ≡ 1`) satisfying `N(p) = v` on an open `U ∋ p`,
whose second fundamental form `Π` vanishes on every pair of level-set tangent
fields (`df ≡ 0` on `U`) — totally geodesic.

Part (1) of the exercise (the space forms `S^n_k` have this property) needs
explicit space-form models absent from `PetersenLib` and is out of scope. -/
theorem exercise3_4_13 [PreconnectedSpace M] (D : RiemannianConnection I g)
    (hn : 3 ≤ Module.finrank ℝ E)
    (hP : ∀ p : M, ∀ v : TangentSpace I p, g.metricInner p v v = 1 →
      ∃ (f : M → ℝ) (c : M → ℝ) (U : Set M),
        ContMDiff I 𝓘(ℝ) ∞ f ∧ ContMDiff I 𝓘(ℝ) ∞ c ∧
          IsSmoothVectorField (gradient g f) ∧ IsOpen U ∧ p ∈ U ∧
          (∀ q ∈ U, c q * c q
            * g.metricInner q (gradient g f q) (gradient g f q) = 1) ∧
          c p • gradient g f p = v ∧
          (∀ X Y : Π x : M, TangentSpace I x, IsSmoothVectorField X →
            IsSmoothVectorField Y →
            (∀ q ∈ U, mfderiv I 𝓘(ℝ) f q (X q) = 0) →
            (∀ q ∈ U, mfderiv I 𝓘(ℝ) f q (Y q) = 0) →
            ∀ q ∈ U, secondFundamentalForm D.toAffineConnection g
                (fun r => c r • gradient g f r) X Y q = 0)) :
    ∃ k : ℝ, HasConstantCurvature D k := by
  classical
  -- `R(a,b)z = 0` on `g`-orthogonal triples, at every point
  have hkey : ∀ (p : M) (z a b : TangentSpace I p), g.metricInner p a z = 0 →
      g.metricInner p b z = 0 →
      curvatureTensorAt D.toAffineConnection p a b z = 0 := by
    intro p z a b ha hb
    rcases eq_or_ne z 0 with hz | hz
    · subst hz
      have := curvatureTensorAt_smul_field D.toAffineConnection p (0 : ℝ) a b 0
      simpa using this
    · have hzz := g.metricInner_self_pos p z hz
      set s := Real.sqrt (g.metricInner p z z) with hsdef
      have hs_pos : 0 < s := Real.sqrt_pos.mpr hzz
      have hs2 : s * s = g.metricInner p z z := Real.mul_self_sqrt (le_of_lt hzz)
      set nrm := s⁻¹ • z with hnrmdef
      have hn1 : g.metricInner p nrm nrm = 1 := by
        rw [hnrmdef, g.metricInner_smul_left, g.metricInner_smul_right, ← hs2]
        field_simp
      have han : g.metricInner p a nrm = 0 := by
        rw [hnrmdef, g.metricInner_smul_right, ha, mul_zero]
      have hbn : g.metricInner p b nrm = 0 := by
        rw [hnrmdef, g.metricInner_smul_right, hb, mul_zero]
      have hzn : z = s • nrm := by
        rw [hnrmdef, smul_smul, mul_inv_cancel₀ hs_pos.ne', one_smul]
      have hv := curvatureAt_normal_eq_zero D hP p nrm a b hn1 han hbn
      rw [hzn, curvatureTensorAt_smul_field, hv, smul_zero]
  -- pointwise constant curvature, choosing the constant `f p`
  have hdiag : ∀ p : M, ∃ k : ℝ, ∀ x y : TangentSpace I p,
      curvatureTensorFourAt D p x y x y = k * bivectorInnerProduct g p x y x y :=
    fun p => exists_diag_const_of_orthogonal_vanishing D p hn (hkey p)
  set fconst : M → ℝ := fun p => -(hdiag p).choose with hfconstdef
  have hsec : ∀ (p : M) (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
      sectionalCurvature D p v w = fconst p := by
    intro p v w hvw
    refine sectionalCurvature_const_of_diag D p (fconst p) (fun x y => ?_) v w hvw
    have hch := (hdiag p).choose_spec x y
    rw [hch, hfconstdef]; ring
  obtain ⟨_, hcc⟩ := (schurLemma D hn (f := fconst)).1 hsec
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, fun p _ _ _ => (IsEmpty.false p).elim⟩
  · obtain ⟨x0⟩ := hM
    exact ⟨fconst x0, hcc x0⟩

end PetersenLib
