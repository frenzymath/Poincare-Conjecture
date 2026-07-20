import PetersenLib.Ch02.Connections
import PetersenLib.Riemannian.Connection.ChristoffelBridge
import PetersenLib.Riemannian.Connection.ChartFrameBridge

/-!
# Petersen Ch. 6, §6.1 — the chart ↔ Koszul connection bridge

`PetersenLib` carries two *a priori* unrelated covariant derivatives:

* the **abstract Koszul side** (Ch. 2): `AffineConnection` / `RiemannianConnection`,
  with `RiemannianMetric.leviCivita` built from the Koszul expression, and Ch. 3's
  `curvatureTensor` / `sectionalCurvature` defined on top of it;
* the **chart-Christoffel side** (Ch. 5 and the project's own geodesic stack),
  with `chartChristoffel`, `Geodesic.chartChristoffelContraction`,
  `covariantDerivCoord`, `IsGeodesic` and `expMap`.

Everything in Ch. 6 that mixes curvature with geodesics (Lemma 6.1.2, the Jacobi
equation with the *real* curvature tensor `R`, and hence §6.4's Rauch comparison)
needs these two to be identified. This file supplies that identification.

The route is a **uniqueness argument**, and it deliberately reuses the vendored
`christoffel_bridge_vector` (do Carmo's formula (10)) rather than redoing its
Koszul algebra:

* `AffineConnection.toDC` — repackages a Ch. 2 `AffineConnection` (whose `cov`
  eats a raw tangent vector and an arbitrary section) as a vendored
  `DCAffineConnection` (whose `cov` eats and returns bundled
  `SmoothVectorField`s). The two structures axiomatise the same object with
  different plumbing; `smooth_cov` is exactly what makes the repackaging
  type-check.
* `RiemannianConnection.toDC_isLeviCivita` — a Ch. 2 `RiemannianConnection` is
  Levi-Civita in the vendored sense: `torsion_free` *is* `IsSymmetric` and
  `metric_compat` *is* `IsMetricCompatible`, once `dirTangent`/`SmoothVectorField.dir`
  and `lieDerivativeVectorField`/`DCLieBracket` are seen to be definitionally the
  same operators.
* `leviCivita_chartFrame_christoffel` — **the bridge, pointwise**: for a frame of
  smooth fields realising the chart basis near `p`, Ch. 2's Levi-Civita connection
  satisfies `∇_{X_i} X_j = ∑_m Γ^m_{ij}(φ(p)) X_m` at `p`, with `Γ` the *chart*
  Christoffel symbols of `g`.
* `exists_chartFrame_leviCivita_christoffel_nhds` — **the bridge, on a
  neighbourhood**: the frame and the Christoffel formula are available on a whole
  open set around `p`, which is the form the curvature computation needs (it must
  differentiate `∇_{X_i} X_j`, so a pointwise identity is not enough).

Blueprint: `lem:chart-connection-bridge` (feeds `lem:third-partial-curvature`,
Petersen Lemma 6.1.2).

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), §6.1; the
coordinate identity is do Carmo, *Riemannian Geometry*, Ch. 2, eq. (10).
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Repackaging a Ch. 2 connection as a vendored `DCAffineConnection` -/

/-- **Math.** Petersen §2.2 (p. 24) vs. do Carmo Ch. 2 §2: the two book
presentations of an affine connection describe the same object. A Ch. 2
`AffineConnection`, whose `cov p v X` takes a raw tangent vector `v ∈ T_pM` and an
arbitrary section `X`, induces a vendored `DCAffineConnection`, whose
`cov X Y` takes and returns bundled smooth vector fields, by
`(∇_X Y)(p) := cov p (X p) Y`. Smoothness of the result is the Ch. 2 axiom
`smooth_cov`. -/
def AffineConnection.toDC (D : AffineConnection I M) : DCAffineConnection I M where
  cov X Y := ⟨fun p => D.cov p (X p) Y, D.smooth_cov X.smooth Y.smooth⟩
  add_left X Y Z := by
    ext p
    exact D.add_direction p (X p) (Y p) Z
  smul_left f hf X Z := by
    ext p
    exact D.smul_direction p (f p) (X p) Z
  add_right X Y Z := by
    ext p
    exact D.add_field p (X p) Y.smooth Z.smooth
  leibniz f hf X Y p := by
    show D.cov p (X p) (fun q => f q • Y q) = _
    rw [D.leibniz p (X p) hf Y.smooth]
    exact add_comm _ _

@[simp]
theorem AffineConnection.toDC_cov_apply (D : AffineConnection I M)
    (X Y : SmoothVectorField I M) (p : M) :
    (D.toDC.cov X Y) p = D.cov p (X p) Y := rfl

/-- **Math.** Petersen's torsion-freeness (Ch. 2 `RiemannianConnection.torsion_free`)
is do Carmo's symmetry (`DCAffineConnection.IsSymmetric`): both say
`∇_X Y − ∇_Y X = [X, Y]`, and `lieDerivativeVectorField` and `DCLieBracket` are
both `VectorField.mlieBracket`. -/
theorem RiemannianConnection.toDC_isSymmetric {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) : D.toAffineConnection.toDC.IsSymmetric := by
  intro X Y p
  exact D.torsion_free X.smooth Y.smooth p

/-- **Math.** Petersen's metric property (Ch. 2 `RiemannianConnection.metric_compat`)
is do Carmo's metric compatibility (`DCAffineConnection.IsMetricCompatible`): both
say `X⟨Y, Z⟩ = ⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩`, and `SmoothVectorField.dir` and
`dirTangent` are both `mfderiv`. -/
theorem RiemannianConnection.toDC_isMetricCompatible {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) :
    D.toAffineConnection.toDC.IsMetricCompatible g := by
  intro X Y Z p
  exact D.metric_compat Y.smooth Z.smooth p (X p)

/-- **Math.** Petersen §2.2 = do Carmo Ch. 2 Thm. 3.6: a Ch. 2
`RiemannianConnection` is a Levi-Civita connection in the vendored sense. This is
the adapter that lets the vendored chart-Christoffel bridge be applied to Ch. 2's
`leviCivita`. -/
theorem RiemannianConnection.toDC_isLeviCivita {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) : D.toAffineConnection.toDC.IsLeviCivita g :=
  ⟨D.toDC_isSymmetric, D.toDC_isMetricCompatible⟩

/-! ### Germ locality of a Ch. 2 connection in the differentiated slot

Lemma 6.1.2 must *use* the bridge below with a frame that only agrees with the
chart frame **near** `p`, so it needs to know that `∇_v Y` depends on `Y` through
its germ at `p` alone. Ch. 2 states no such lemma, so it is proved here from the
Leibniz axiom and a smooth bump function. -/

variable [T2Space M] [I.Boundaryless]

/-- **Math.** A smooth field `X` vanishing near `p` can be written `X = f · X` for
a globally smooth scalar `f` with `f(p) = 0` — take `f = 1 − χ` for a smooth bump
`χ` at `p` whose closed support lies inside the set where `X` vanishes. This is the
shape the `𝒟(M)`-homogeneity of a connection can annihilate. -/
theorem exists_smul_eq_self_of_eventuallyEq_zero {X : Π x : M, TangentSpace I x}
    {p : M} (hX : ∀ᶠ q in 𝓝 p, X q = 0) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ f p = 0 ∧ ∀ q, f q • X q = X q := by
  obtain ⟨U, hU_nhds, hU⟩ := hX.exists_mem
  obtain ⟨χ, -, hχU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp hU_nhds
  refine ⟨fun q => 1 - χ q, contMDiff_const.sub χ.contMDiff, by
    show 1 - χ p = 0
    rw [χ.eq_one, sub_self], fun q => ?_⟩
  show (1 - χ q) • X q = X q
  by_cases hq : χ q = 0
  · rw [hq, sub_zero, one_smul]
  · have hqU : q ∈ U := hχU (subset_closure (by simpa using hq))
    rw [hU q hqU, smul_zero]

/-- **Math.** Petersen §2.2 — `∇_v X = 0` when the smooth field `X` vanishes on a
neighbourhood of `p`. Write `X = f · X` with `f(p) = 0`
(`exists_smul_eq_self_of_eventuallyEq_zero`); the Leibniz rule then gives
`∇_v X = df(v)·X|_p + f(p)·∇_v X = df(v)·0 + 0·∇_v X = 0`. -/
theorem AffineConnection.cov_eq_zero_of_eventuallyEq_zero_right
    (D : AffineConnection I M) (p : M) (v : TangentSpace I p)
    {X : Π x : M, TangentSpace I x} (hXs : IsSmoothVectorField X)
    (hX : ∀ᶠ q in 𝓝 p, X q = 0) : D.cov p v X = 0 := by
  obtain ⟨f, hf, hfp, hfX⟩ := exists_smul_eq_self_of_eventuallyEq_zero hX
  have h := D.leibniz p v hf hXs
  rw [show (fun q => f q • X q) = X from funext hfX, hX.self_of_nhds, smul_zero,
    hfp, zero_smul, zero_add] at h
  exact h

/-- **Math.** Petersen §2.2 — **germ locality of `∇` in the differentiated slot**:
if `X = Y` on a neighbourhood of `p` then `(∇_v X)(p) = (∇_v Y)(p)`. Apply
`cov_eq_zero_of_eventuallyEq_zero_right` to `X − Y` and split with `add_field`.
This is what licenses computing `∇` against a frame that realises the chart frame
only locally. -/
theorem AffineConnection.cov_congr_right (D : AffineConnection I M) (p : M)
    (v : TangentSpace I p) {X Y : SmoothVectorField I M}
    (h : (X : Π x : M, TangentSpace I x) =ᶠ[𝓝 p] (Y : Π x : M, TangentSpace I x)) :
    D.cov p v X = D.cov p v Y := by
  have hτ : ∀ᶠ q in 𝓝 p, (X - Y : SmoothVectorField I M) q = 0 := by
    filter_upwards [h] with q hq
    rw [SmoothVectorField.sub_apply, hq, sub_self]
  have h0 := D.cov_eq_zero_of_eventuallyEq_zero_right p v (X - Y).smooth hτ
  have hsplit := D.add_field p v (X - Y).smooth Y.smooth
  rw [show (fun q => (X - Y : SmoothVectorField I M) q + Y q)
      = (X : Π x : M, TangentSpace I x) from
    funext fun q => by rw [SmoothVectorField.sub_apply, sub_add_cancel], h0,
    zero_add] at hsplit
  exact hsplit

/-! ### The bridge, pointwise -/

variable [SigmaCompactSpace M]

/-- **Math.** Petersen §6.1 / do Carmo Ch. 2 eq. (10) — **the chart-Christoffel
bridge, pointwise**. Let `Z` be a family of *globally smooth* vector fields which
agrees with the chart frame `∂/∂x_a` of the chart at `α` on a neighbourhood of
`q`. Then any Ch. 2 `RiemannianConnection` `D` for `g` — in particular
`g.leviCivita` — reproduces the *chart* Christoffel symbols of `g`:

`(∇_{Z_i} Z_j)(q) = ∑_m Γ^m_{ij}(φ(q)) · Z_m(q)`.

The germ hypothesis `hgerm` is what discharges the two analytic inputs of the
vendored `christoffel_bridge_vector`: the frame brackets vanish
(`mlieBracket_chartBasisVecFiber_eq_zero`) and the directional derivatives of the
Gram entries are partial derivatives of the chart Gram matrix
(`mfderiv_chartGramMatrix_eq_partialDeriv`); both are germ-local, so they transfer
from the chart frame to `Z`. -/
theorem riemannianConnection_chartFrame_christoffel {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (α : M)
    (Z : Fin (Module.finrank ℝ E) → SmoothVectorField I M) {q : M}
    (hq_source : q ∈ (chartAt H α).source)
    (hq_base : q ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hgerm : ∀ a, (fun r => Z a r) =ᶠ[𝓝 q] fun r => chartBasisVecFiber (I := I) α a r)
    (i j : Fin (Module.finrank ℝ E)) :
    D.cov q (Z i q) (Z j)
      = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α q) • Z m q := by
  classical
  have hval : ∀ a, Z a q = chartBasisVecFiber (I := I) α a q :=
    fun a => (hgerm a).self_of_nhds
  have hpe : (extChartAt I α).symm (extChartAt I α q) = q :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  -- the frame brackets vanish at `q`, germ-locally from the chart frame
  have hbr : ∀ a b, DCLieBracket (Z a) (Z b) q = 0 := by
    intro a b
    show VectorField.mlieBracket I (Z a).toFun (Z b).toFun q = 0
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hgerm a) (hgerm b)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α a b hq_source
  -- directional derivatives of the Gram entries are partial derivatives
  have hdir : ∀ r a b, (Z r).dir (fun q' => g.metricInner q' (Z a q') (Z b q')) q
      = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) (extChartAt I α q) := by
    intro r a b
    have hfeq : (fun q' => g.metricInner q' (Z a q') (Z b q'))
        =ᶠ[𝓝 q] fun q' => chartGramMatrix (I := I) g α q' a b := by
      filter_upwards [hgerm a, hgerm b] with r' hra hrb
      rw [hra, hrb]
      exact (chartGramMatrix_apply (I := I) g α r' a b).symm
    show mfderiv I 𝓘(ℝ, ℝ) (fun q' => g.metricInner q' (Z a q') (Z b q')) q (Z r q) = _
    rw [hfeq.mfderiv_eq, hval r]
    exact mfderiv_chartGramMatrix_eq_partialDeriv (I := I) g α a b r hq_source
  exact christoffel_bridge_vector (I := I) g D.toAffineConnection.toDC
    D.toDC_isLeviCivita α q Z hbr hdir hq_base hpe hval i j

/-- **Math.** Petersen §6.1 — **the chart-Christoffel bridge for the Levi-Civita
connection**, pointwise. The specialisation of
`riemannianConnection_chartFrame_christoffel` to `g.leviCivita`, i.e. to the
connection Ch. 3's `curvatureTensor` and `sectionalCurvature` are built from.
This is the identity that lets a curvature computation be carried out in a chart. -/
theorem leviCivita_chartFrame_christoffel (g : RiemannianMetric I M) (α : M)
    (Z : Fin (Module.finrank ℝ E) → SmoothVectorField I M) {q : M}
    (hq_source : q ∈ (chartAt H α).source)
    (hq_base : q ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hgerm : ∀ a, (fun r => Z a r) =ᶠ[𝓝 q] fun r => chartBasisVecFiber (I := I) α a r)
    (i j : Fin (Module.finrank ℝ E)) :
    (g.leviCivita).cov q (Z i q) (Z j)
      = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α q) • Z m q :=
  riemannianConnection_chartFrame_christoffel g.leviCivita α Z hq_source hq_base hgerm i j

/-! ### The bridge, on a neighbourhood -/

/-- **Math.** Petersen §6.1 — **the chart-Christoffel bridge on a neighbourhood**.
For any `p` in the chart at `α` there exist globally smooth fields `Z_a` and an
open `U ∋ p` inside the chart source on which the `Z_a` realise the chart frame
`∂/∂x_a` *and* Ch. 2's Levi-Civita connection is given by the chart Christoffel
symbols:

`(∇_{Z_i} Z_j)(q) = ∑_m Γ^m_{ij}(φ(q)) · Z_m(q)` for all `q ∈ U`.

The neighbourhood — as opposed to pointwise — form is what Lemma 6.1.2 needs: the
curvature tensor differentiates `∇_{Z_i} Z_j`, so the identity must hold on an
open set, not just at `p`. The fields are produced by bump-function extension of
the chart frame (`exists_smoothVectorField_eventuallyEq`, whence
`[SigmaCompactSpace M]` and `[T2Space M]`). -/
theorem exists_chartFrame_leviCivita_christoffel_nhds (g : RiemannianMetric I M)
    {α p : M} (hp : p ∈ (chartAt H α).source) :
    ∃ (Z : Fin (Module.finrank ℝ E) → SmoothVectorField I M) (U : Set M),
      IsOpen U ∧ p ∈ U ∧ U ⊆ (chartAt H α).source ∧
      (∀ a, ∀ q ∈ U, Z a q = chartBasisVecFiber (I := I) α a q) ∧
      (∀ i j, ∀ q ∈ U, (g.leviCivita).cov q (Z i q) (Z j)
        = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α q) • Z m q) := by
  classical
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hbase : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := hp
  -- bump-extend each chart frame vector to a global smooth field
  choose Z hZ using fun a : Fin (Module.finrank ℝ E) =>
    exists_smoothVectorField_eventuallyEq (I := I)
      (σ := fun q => chartBasisVecFiber (I := I) α a q)
      (s := (trivializationAt E (TangentSpace I) α).baseSet) hbaseopen
      (Tensor.chartBasisVec_contMDiffOn (I := I) α a) hbase
  -- a common open neighbourhood on which every frame agreement holds
  have hOa : ∀ a, ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ q ∈ O, Z a q = chartBasisVecFiber (I := I) α a q := by
    intro a
    obtain ⟨sa, hsa, hsub⟩ := (hZ a).exists_mem
    obtain ⟨O, hOsub, hOopen, hpO⟩ := mem_nhds_iff.mp hsa
    exact ⟨O, hOopen, hpO, fun q hq => hsub q (hOsub hq)⟩
  choose O hOopen hpO hOagree using hOa
  refine ⟨Z, (⋂ a, O a) ∩ ((chartAt H α).source ∩
      (trivializationAt E (TangentSpace I) α).baseSet),
    ((isOpen_iInter_of_finite hOopen).inter
      ((chartAt H α).open_source.inter hbaseopen)),
    ⟨mem_iInter.mpr hpO, hp, hbase⟩,
    fun q hq => hq.2.1, fun a q hq => hOagree a q (mem_iInter.mp hq.1 a), ?_⟩
  intro i j q hq
  refine leviCivita_chartFrame_christoffel g α Z hq.2.1 hq.2.2 (fun a => ?_) i j
  exact eventually_of_mem ((hOopen a).mem_nhds (mem_iInter.mp hq.1 a))
    (fun r hr => hOagree a r hr)

end PetersenLib

end
