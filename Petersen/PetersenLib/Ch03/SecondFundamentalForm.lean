import PetersenLib.Ch03.RadialCurvature

/-!
# Petersen Ch. 3, §3.2.1–§3.2.2 — The second fundamental form and
Proposition 3.2.1

The **second fundamental form** `Π(X,Y) = g(∇_X N, Y)` of a hypersurface with
unit normal field `N` (`secondFundamentalForm`), with the two facts making it
a well-defined symmetric `(0,2)`-tensor on the tangent distribution:
`∇_X N ⊥ N` (`secondFundamentalForm_normal_orthogonal`) and symmetry on fields
tangent to the hypersurface (`secondFundamentalForm_symm`); the tangency of
Lie brackets of level-set-tangent fields (`bracket_tangent_levelSet`), which
supplies the symmetry hypothesis when the hypersurface is a level set;
**Proposition 3.2.1** (`normal_hessian_relation`): `N = ∇f/|∇f|` is a unit
normal to a regular level set of `f`, `Π = Hess f/|∇f|` on tangent vectors,
and `Hess f(∇f, X) = ½ D_X|∇f|²`; and **Lemma 3.2.8**
(`distanceFunction_iff_riemannianSubmersion`): a smooth function is a distance
function iff it is a pointwise Riemannian submersion.

## Design notes

* There is no Riemannian-submanifold layer at this point of the project, so a
  hypersurface enters through its **unit normal field**: an ambient smooth
  field `N` with `g(N,N) ≡ 1` on an open set `U`, fields *tangent to the
  hypersurface* being fields `X` with `g(X,N) ≡ 0` on `U`. All statements are
  pointwise at `p ∈ U`.
* In `normal_hessian_relation` the normalized gradient `N = ∇f/|∇f|` is
  encoded without square roots or partial smoothness: the data is a globally
  smooth `c : M → ℝ` with `c² · |∇f|² ≡ 1` on `U` (so `c = ±1/|∇f|` there),
  and `N := c • ∇f`. This keeps the Leibniz rule for `∇(c•∇f)` global while
  the conclusions remain the literal statements of Prop. 3.2.1.
* `distanceFunction_iff_riemannianSubmersion` states the Riemannian-submersion
  condition for `r : U → ℝ` pointwise: `dr_q ≠ 0` and `dr_q` is
  norm-preserving on the `g`-orthogonal complement of its kernel,
  `(dr_q(v))² = g(v,v)` for `v ⊥ ker dr_q`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2.1, §3.2.2.
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The second fundamental form -/

/-- **Math.** The **second fundamental form** (Petersen §3.2.1,
`def:pet-ch3-second-fundamental-form`): for a hypersurface with unit normal
field `N`, the `(0,2)`-tensor `Π(X,Y) = g(∇_X N, Y)` on fields tangent to the
hypersurface. `secondFundamentalForm_normal_orthogonal` and
`secondFundamentalForm_symm` record that `∇_X N` is automatically tangent and
that `Π` is symmetric on tangent fields. -/
def secondFundamentalForm (D : AffineConnection I M) (g : RiemannianMetric I M)
    (N X Y : Π x : M, TangentSpace I x) (p : M) : ℝ :=
  g.metricInner p (D.cov p (X p) N) (Y p)

@[simp]
theorem secondFundamentalForm_apply (D : AffineConnection I M)
    (g : RiemannianMetric I M) (N X Y : Π x : M, TangentSpace I x) (p : M) :
    secondFundamentalForm D g N X Y p
      = g.metricInner p (D.cov p (X p) N) (Y p) := rfl

section NormalOrthogonal

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Math.** `g(∇_X N, N) = ½ D_X|N|² = 0` for a unit field `N` (Petersen
§3.2.1): the covariant derivative of a unit normal is automatically tangent
to the hypersurface, so `Π(X, ·)` is well defined on tangent vectors. -/
theorem secondFundamentalForm_normal_orthogonal {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U)
    {N : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    (hunit : ∀ q ∈ U, g.metricInner q (N q) (N q) = 1)
    (X : Π x : M, TangentSpace I x) {p : M} (hp : p ∈ U) :
    secondFundamentalForm D.toAffineConnection g N X N p = 0 := by
  rw [secondFundamentalForm_apply]
  -- metric compatibility along `X p`
  have hcompat := D.metric_compat hN hN p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- `|N|² ≡ 1` near `p`
  have hloc : (fun q => g.metricInner q (N q) (N q)) =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hunit q hq
  have hdd : directionalDerivative X
      (fun q => g.metricInner q (N q) (N q)) p = 0 := by
    rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]
    rfl
  rw [hdd] at hcompat
  have hcomm : g.metricInner p (N p) (D.cov p (X p) N)
      = g.metricInner p (D.cov p (X p) N) (N p) := g.metricInner_comm ..
  linarith [hcompat, hcomm]

end NormalOrthogonal

section BracketTangent

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- **Math.** Lie brackets of fields tangent to a level set stay tangent
(Petersen §3.2.1, used for the symmetry of `Π`): if `D_X f = D_Y f = 0` on the
open set `U`, then `D_{[X,Y]}f = 0` at points of `U` — by the commutator
identity `D_{[X,Y]}f = D_X(D_Y f) − D_Y(D_X f)`. -/
theorem bracket_tangent_levelSet {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    {U : Set M} (hU : IsOpen U)
    (hXtan : ∀ q ∈ U, directionalDerivative X f q = 0)
    (hYtan : ∀ q ∈ U, directionalDerivative Y f q = 0)
    {p : M} (hp : p ∈ U) :
    directionalDerivative (lieDerivativeVectorField I X Y) f p = 0 := by
  have hbr := lieDerivative_vectorField_eq_bracket hX hY hf p
  -- both iterated derivatives vanish at `p`, since the inner ones vanish on `U`
  have hXzero : directionalDerivative X (directionalDerivative Y f) p = 0 := by
    have hloc : directionalDerivative Y f =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hYtan q hq
    rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]
    rfl
  have hYzero : directionalDerivative Y (directionalDerivative X f) p = 0 := by
    have hloc : directionalDerivative X f =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hXtan q hq
    rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]
    rfl
  rw [hbr, hXzero, hYzero, sub_zero]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E] in
/-- **Math.** Symmetry of the second fundamental form (Petersen §3.2.1, proof
content of `def:pet-ch3-second-fundamental-form`): for fields `X, Y` tangent
to the hypersurface (`g(X,N) = g(Y,N) ≡ 0` on `U`) whose bracket is tangent at
`p`, `Π(X,Y) = Π(Y,X)` — via
`g(∇_X N, Y) = D_X g(N,Y) − g(N, ∇_X Y) = −g(N, ∇_X Y)` and torsion-freeness. -/
theorem secondFundamentalForm_symm {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {U : Set M} (hU : IsOpen U)
    {N X Y : Π x : M, TangentSpace I x} (hN : IsSmoothVectorField N)
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hXtan : ∀ q ∈ U, g.metricInner q (X q) (N q) = 0)
    (hYtan : ∀ q ∈ U, g.metricInner q (Y q) (N q) = 0)
    {p : M} (hp : p ∈ U)
    (hbr : g.metricInner p (N p) (lieDerivativeVectorField I X Y p) = 0) :
    secondFundamentalForm D.toAffineConnection g N X Y p
      = secondFundamentalForm D.toAffineConnection g N Y X p := by
  -- `Π(X,Y) = −g(N, ∇_X Y)`, differentiating `g(N,Y) ≡ 0` along `X`
  have key : ∀ (Z W : Π x : M, TangentSpace I x), IsSmoothVectorField Z →
      IsSmoothVectorField W → (∀ q ∈ U, g.metricInner q (W q) (N q) = 0) →
      secondFundamentalForm D.toAffineConnection g N Z W p
        = -g.metricInner p (N p) (D.cov p (Z p) W) := by
    intro Z W hZ hW hWtan
    have hcompat := D.metric_compat hN hW p (Z p)
    rw [dirTangent_eq_directionalDerivative] at hcompat
    have hloc : (fun q => g.metricInner q (N q) (W q)) =ᶠ[𝓝 p]
        fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      rw [g.metricInner_comm]
      exact hWtan q hq
    have hdd : directionalDerivative Z
        (fun q => g.metricInner q (N q) (W q)) p = 0 := by
      rw [directionalDerivative_apply, hloc.mfderiv_eq, mfderiv_const]
      rfl
    rw [hdd] at hcompat
    have hcomm : g.metricInner p (D.cov p (Z p) N) (W p)
        = g.metricInner p (W p) (D.cov p (Z p) N) := g.metricInner_comm ..
    rw [secondFundamentalForm_apply]
    linarith [hcompat, hcomm]
  rw [key X Y hX hY hYtan, key Y X hY hX hXtan]
  -- torsion-freeness: `∇_X Y − ∇_Y X = [X,Y]`, which is tangent at `p`
  have htf := D.torsion_free hX hY p
  have hsub : g.metricInner p (N p) (D.cov p (X p) Y)
      - g.metricInner p (N p) (D.cov p (Y p) X)
      = g.metricInner p (N p) (lieDerivativeVectorField I X Y p) := by
    rw [← g.metricInner_sub_right, htf]
  rw [hbr] at hsub
  linarith [hsub]

end BracketTangent

/-! ## Proposition 3.2.1 -/

section NormalHessian

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Proposition 3.2.1** (Petersen,
`prop:pet-ch3-normal-hessian-relation`): let `H ⊂ f⁻¹(a)` consist of regular
points of `f`, with unit normal `N = ∇f/|∇f|` — encoded as `N = c • ∇f` for a
smooth `c` with `c²|∇f|² ≡ 1` on `U`. Then, at `p ∈ U`:

1. `N` is a unit normal: `g(N,N) = 1`, and `g(N,v) = 0` for every `v` tangent
   to the level set (`df(v) = 0`);
2. `Π(X,Y) = c · Hess f(X,Y) = Hess f(X,Y)/|∇f|` for `Y` tangent to the
   level set;
3. `Hess f(∇f, X) = ½ D_X|∇f|²` for all `X` (no tangency required).

The `1/|∇f|` factor of (2) enters only through `c(p)`: the derivative of `c`
pairs against `g(∇f, Y) = 0`. -/
theorem normal_hessian_relation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgradf : IsSmoothVectorField (gradient g f))
    {c : M → ℝ} (hc : ContMDiff I 𝓘(ℝ) ∞ c) {U : Set M}
    (hnorm : ∀ q ∈ U,
      c q * c q * g.metricInner q (gradient g f q) (gradient g f q) = 1)
    {p : M} (hp : p ∈ U) :
    (g.metricInner p ((fun q => c q • gradient g f q) p)
        ((fun q => c q • gradient g f q) p) = 1
      ∧ ∀ v : TangentSpace I p, mfderiv I 𝓘(ℝ) f p v = 0 →
          g.metricInner p ((fun q => c q • gradient g f q) p) v = 0)
    ∧ (∀ X Y : Π x : M, TangentSpace I x, IsSmoothVectorField X →
        IsSmoothVectorField Y → g.metricInner p (gradient g f p) (Y p) = 0 →
        secondFundamentalForm D.toAffineConnection g
            (fun q => c q • gradient g f q) X Y p
          = c p * hessianLieDerivative g f ![X, Y] p)
    ∧ (∀ X : Π x : M, TangentSpace I x, IsSmoothVectorField X →
        hessianLieDerivative g f ![gradient g f, X] p
          = (1 / 2 : ℝ) * directionalDerivative X
              (fun q => g.metricInner q (gradient g f q) (gradient g f q)) p) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- (1a): unit length
    rw [g.metricInner_smul_left, g.metricInner_smul_right, ← mul_assoc]
    exact hnorm p hp
  · -- (1b): normal to the level set
    intro v hv
    rw [g.metricInner_smul_left, metricInner_gradient, hv]
    simp
    exact Or.inr rfl
  · -- (2): `Π = c · Hess f` on tangent vectors
    intro X Y hX hY hYtan
    rw [secondFundamentalForm_apply,
      D.toAffineConnection.leibniz p (X p) hc hgradf, g.metricInner_add_left,
      g.metricInner_smul_left, g.metricInner_smul_left, hYtan, mul_zero, zero_add,
      hessianLieDerivative_eq_metricInner_cov D hf hX hY hgradf p]
  · -- (3): `Hess f(∇f, X) = ½ D_X|∇f|²`
    intro X hX
    rw [hessianLieDerivative_symm D hf hgradf hX hgradf p,
      hessianLieDerivative_eq_metricInner_cov D hf hX hgradf hgradf p]
    have hcompat := D.metric_compat hgradf hgradf p (X p)
    rw [dirTangent_eq_directionalDerivative] at hcompat
    have hcomm : g.metricInner p (gradient g f p) (D.cov p (X p) (gradient g f))
        = g.metricInner p (D.cov p (X p) (gradient g f)) (gradient g f p) :=
      g.metricInner_comm ..
    rw [hcomm] at hcompat
    linarith [hcompat]

end NormalHessian

/-! ## Lemma 3.2.8 — distance functions are Riemannian submersions -/

section Submersion

variable [FiniteDimensional ℝ E]

/-- **Math.** **Lemma 3.2.8** (Petersen,
`lem:pet-ch3-distance-function-submersion`): `r : U → ℝ` is a distance
function iff it is a **Riemannian submersion**: at each `q ∈ U`, the
differential `dr_q` is nonzero and norm-preserving on the `g`-orthogonal
complement of its kernel, `(dr_q(v))² = g(v,v)` whenever `v ⊥ ker dr_q`.
The complement of the kernel is spanned by `∇r`, and `dr_q` scales it by
`|∇r|²`, so the submersion condition is exactly `|∇r| ≡ 1`. -/
theorem distanceFunction_iff_riemannianSubmersion {g : RiemannianMetric I M}
    {U : Set M} {r : M → ℝ} :
    IsDistanceFunction g U r ↔
      ContMDiffOn I 𝓘(ℝ) ∞ r U ∧ ∀ q ∈ U, gradient g r q ≠ 0 ∧
        ∀ v : TangentSpace I q,
          (∀ w : TangentSpace I q, dirTangent r w = 0 → g.metricInner q v w = 0) →
          dirTangent r v ^ 2 = g.metricInner q v v := by
  have hdr : ∀ (q : M) (u : TangentSpace I q),
      dirTangent r u = g.metricInner q (gradient g r q) u :=
    fun q u => (metricInner_gradient g r q u).symm
  constructor
  · rintro ⟨hsmooth, heik⟩
    refine ⟨hsmooth, fun q hq => ⟨?_, ?_⟩⟩
    · -- `g(∇r,∇r) = 1` forces `∇r ≠ 0`
      intro h0
      have h1 := heik q hq
      rw [h0, g.metricInner_zero_left] at h1
      exact zero_ne_one h1
    · intro v hv
      -- `w₀ := |∇r|²·v − dr(v)·∇r` lies in `ker dr_q`, so `v ⊥ w₀`
      have hkerw : dirTangent r
          (g.metricInner q (gradient g r q) (gradient g r q) • v
            - g.metricInner q (gradient g r q) v • gradient g r q) = 0 := by
        rw [hdr, g.metricInner_sub_right, g.metricInner_smul_right,
          g.metricInner_smul_right]
        ring
      have horth := hv _ hkerw
      rw [g.metricInner_sub_right, g.metricInner_smul_right,
        g.metricInner_smul_right, heik q hq] at horth
      -- assemble: `dr(v)² = g(∇r,v)·g(v,∇r) = g(v,v)`
      have hcommGv : g.metricInner q v (gradient g r q)
          = g.metricInner q (gradient g r q) v := g.metricInner_comm ..
      rw [hcommGv] at horth
      rw [hdr q v]
      linear_combination -horth
  · rintro ⟨hsmooth, hsub⟩
    refine ⟨hsmooth, fun q hq => ?_⟩
    obtain ⟨hne, hiso⟩ := hsub q hq
    -- `∇r ⊥ ker dr_q`, so the isometry condition applies to it
    have hGperp : ∀ w : TangentSpace I q,
        dirTangent r w = 0 → g.metricInner q (gradient g r q) w = 0 := by
      intro w hw
      rw [← hdr q w]
      exact hw
    have hGG := hiso (gradient g r q) hGperp
    rw [hdr] at hGG
    -- positive-definiteness: `g(∇r,∇r) ≠ 0`
    have hGne : g.metricInner q (gradient g r q) (gradient g r q) ≠ 0 :=
      (g.metricInner_self_pos q (gradient g r q) hne).ne'
    -- `g(∇r,∇r)² = g(∇r,∇r)` with `g(∇r,∇r) ≠ 0` gives the eikonal equation
    exact mul_left_cancel₀ hGne (by linear_combination hGG)

end Submersion

end PetersenLib
