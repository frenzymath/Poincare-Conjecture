import PetersenLib.Ch03.GaussCodazzi
import PetersenLib.Ch03.CurvatureSymmetries
import PetersenLib.Ch03.Bivector

/-!
# Petersen Ch. 3, §3.4 — Exercise 3.4.4

**Exercise 3.4.4** (`exercise3_4_4`, Petersen `rem:pet-ch3-ex-4`): for a
distance function `r = f` on an open set `U`, the tangential, mixed and normal
curvature equations can be rewritten with the shape operator
`S(X) = ∇_X∇r = hessianOperator` and the bivector map `x ∧ y`:

1. the **tangential (Gauss) equation** in vector form,
   `(R(X,Y)Z)^⊤ = R_H(X,Y)Z + (S(X) ∧ S(Y))(Z)`;
2. the **mixed equation**,
   `g(R(X,Y)Z, ∂_r) = −g((∇_XS)(Y), Z) + g((∇_YS)(X), Z)`;
3. the **normal equation**,
   `R(X,Y)∂_r = (d^∇S)(X,Y) = (∇_XS)(Y) − (∇_YS)(X)`.

## Design notes

* Here the unit normal of the level sets of `r` is the radial field
  `N = ∂_r = ∇r`, which is a genuine unit field because `|∇r|² ≡ 1` on `U`
  (`IsDistanceFunction`). The shape operator `S = ∇∂_r = Hess r` is then
  exactly `hessianOperator D g r`, and the second fundamental form `Π` is
  `Π(A,B) = g(S(A),B)`.
* Part 3 is the Ricci identity `R(X,Y)Z = ∇²_{X,Y}Z − ∇²_{Y,X}Z`
  (`curvatureTensor_eq_ricci_identity`) specialised to `Z = ∇r`, together with
  `(∇_XS)(Y) = ∇²_{X,Y}∇r`
  (`hessianOperatorCovariantDerivative_eq_secondCovariantDerivative`).
* Part 2 is part 3 paired against `∂_r` after skew-symmetry of `R(X,Y,·,·)`
  (`curvatureTensorFour_antisymm_right`): `g(R(X,Y)Z, ∂_r) = −g(R(X,Y)∂_r, Z)`.
* Part 1 upgrades the scalar Gauss equation `tangentialCurvatureEquation`
  (Theorem 3.2.4, valid against every `W ⊥ N` at `p`) to a vector identity by
  nondegeneracy of `g` (`metricInner_eq_iff_eq`) and the orthogonal splitting
  `w = (w − g(w,N)N) + g(w,N)N` of `T_pM`; the two sides pair identically
  against `N` (both vanish, using `S(X), S(Y) ⊥ N` and `∇^H ⊥ N`) and against
  every `w ⊥ N`.

**Sign note.** The blueprint writes part 1 with a minus,
`(R(X,Y)Z)^⊤ = R_H(X,Y)Z − (S(X)∧S(Y))(Z)`. With the library's proven
`tangentialCurvatureEquation` and the Petersen §3.1.2 wedge convention encoded
in `bivectorSkewMap` (`(x∧y)(v) = g(x,v)y − g(y,v)x`), the provable identity has
a **plus**: `g((S(X)∧S(Y))(Z), W) = Π(X,Z)Π(Y,W) − Π(X,W)Π(Y,Z)`, exactly the
cross-term of the Gauss equation with the opposite sign of the blueprint's
convention. We therefore state part 1 with `+`, which is the mathematically
correct form given the surrounding library. (Equivalently
`R_H − (S(Y)∧S(X))(Z)`, since `S(Y)∧S(X) = −(S(X)∧S(Y))`.)

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2, Exercise 3.4.4
(pp. 121–122).
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Exercise 3.4.4** (Petersen, `rem:pet-ch3-ex-4`): for a distance
function `r` on the open set `U`, with shape operator `S(X) = ∇_X∇r`
(`hessianOperator`) and `(∇_XS)(Y)` (`hessianOperatorCovariantDerivative`), the
tangential/mixed/normal curvature equations of §3.2 take the form

1. `(R(X,Y)Z)^⊤ = R_H(X,Y)Z + (S(X)∧S(Y))(Z)` (tangential Gauss equation, in
   vector form; see the sign note in the file header);
2. `g(R(X,Y)Z, ∂_r) = −g((∇_XS)(Y), Z) + g((∇_YS)(X), Z)` (mixed equation);
3. `R(X,Y)∂_r = (∇_XS)(Y) − (∇_YS)(X)` (normal equation, `R(X,Y)N = d^∇S`).

Part 3 is the Ricci identity at `Z = ∇r`; part 2 is part 3 paired against `∂_r`
via skew-symmetry of `R(X,Y,·,·)`; part 1 upgrades the scalar Gauss equation
(Theorem 3.2.4) to a vector identity by nondegeneracy of `g`. -/
theorem exercise3_4_4 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    (hgradr : IsSmoothVectorField (gradient g r))
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z)
    (hZtan : ∀ q ∈ U, g.metricInner q (Z q) (gradient g r q) = 0)
    {p : M} (hp : p ∈ U)
    (_hbr : g.metricInner p (gradient g r p)
      (lieDerivativeVectorField I X Y p) = 0) :
    (curvatureTensor D.toAffineConnection X Y Z p
        - g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p)
            (gradient g r p) • gradient g r p
      = tangentialCurvatureTensor D.toAffineConnection g (gradient g r) X Y Z p
        + bivectorSkewMap g p
            (hessianOperator D.toAffineConnection g r p (X p))
            (hessianOperator D.toAffineConnection g r p (Y p)) (Z p))
    ∧ (curvatureTensorFour D X Y Z (gradient g r) p
      = -g.metricInner p
            (hessianOperatorCovariantDerivative D.toAffineConnection g r X Y p)
            (Z p)
        + g.metricInner p
            (hessianOperatorCovariantDerivative D.toAffineConnection g r Y X p)
            (Z p))
    ∧ (curvatureTensor D.toAffineConnection X Y (gradient g r) p
      = hessianOperatorCovariantDerivative D.toAffineConnection g r X Y p
        - hessianOperatorCovariantDerivative D.toAffineConnection g r Y X p) := by
  -- Part 3: the Ricci identity at `Z = ∇r`.
  have hpart3 : curvatureTensor D.toAffineConnection X Y (gradient g r) p
      = hessianOperatorCovariantDerivative D.toAffineConnection g r X Y p
        - hessianOperatorCovariantDerivative D.toAffineConnection g r Y X p := by
    rw [curvatureTensor_eq_ricci_identity D hX hY (gradient g r) p]
    simp only [hessianOperatorCovariantDerivative_eq_secondCovariantDerivative]
  -- Part 2: pair part 3 against `∂_r` via skew-symmetry of `R(X,Y,·,·)`.
  have hpart2 : curvatureTensorFour D X Y Z (gradient g r) p
      = -g.metricInner p
            (hessianOperatorCovariantDerivative D.toAffineConnection g r X Y p)
            (Z p)
        + g.metricInner p
            (hessianOperatorCovariantDerivative D.toAffineConnection g r Y X p)
            (Z p) := by
    rw [curvatureTensorFour_antisymm_right D hX hY hZ hgradr p,
      curvatureTensorFour_apply, hpart3, g.metricInner_sub_left]
    ring
  -- Part 1: upgrade the scalar Gauss equation (Thm 3.2.4) to a vector identity.
  have hunitp : g.metricInner p (gradient g r p) (gradient g r p) = 1 := hr.2 p hp
  have hunit : ∀ q ∈ U,
      g.metricInner q (gradient g r q) (gradient g r q) = 1 := hr.2
  have hSXN : g.metricInner p (D.cov p (X p) (gradient g r)) (gradient g r p) = 0 :=
    secondFundamentalForm_normal_orthogonal D hU hgradr hunit X hp
  have hSYN : g.metricInner p (D.cov p (Y p) (gradient g r)) (gradient g r p) = 0 :=
    secondFundamentalForm_normal_orthogonal D hU hgradr hunit Y hp
  have hpart1 : curvatureTensor D.toAffineConnection X Y Z p
        - g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p)
            (gradient g r p) • gradient g r p
      = tangentialCurvatureTensor D.toAffineConnection g (gradient g r) X Y Z p
        + bivectorSkewMap g p
            (hessianOperator D.toAffineConnection g r p (X p))
            (hessianOperator D.toAffineConnection g r p (Y p)) (Z p) := by
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    -- pairing against any `u ⊥ ∂_r`: the scalar Gauss equation
    have hkey : ∀ u : TangentSpace I p,
        g.metricInner p u (gradient g r p) = 0 →
        g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p
            - g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p)
                (gradient g r p) • gradient g r p) u
          = g.metricInner p
              (tangentialCurvatureTensor D.toAffineConnection g (gradient g r)
                  X Y Z p
                + bivectorSkewMap g p
                    (hessianOperator D.toAffineConnection g r p (X p))
                    (hessianOperator D.toAffineConnection g r p (Y p)) (Z p)) u := by
      intro u hu
      set W : Π x : M, TangentSpace I x := ⇑(extendTangentVector p u) with hWdef
      have hWp : W p = u := extendTangentVector_apply p u
      have hWN : g.metricInner p (W p) (gradient g r p) = 0 := by rw [hWp]; exact hu
      have huN : g.metricInner p (gradient g r p) u = 0 := by
        rw [g.metricInner_comm]; exact hu
      have hgauss := tangentialCurvatureEquation D hU hgradr hX hY hZ hZtan hp hWN
      rw [curvatureTensorFour_apply] at hgauss
      simp only [secondFundamentalForm_apply] at hgauss
      rw [hWp] at hgauss
      simp only [hessianOperator_apply]
      rw [g.metricInner_sub_left, g.metricInner_smul_left, huN, mul_zero, sub_zero,
        g.metricInner_add_left, bivectorSkewMap_metricInner, bivectorInnerProduct,
        hgauss]
      ring
    -- pairing against `∂_r`: both sides vanish
    have hLN : g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p
          - g.metricInner p (curvatureTensor D.toAffineConnection X Y Z p)
              (gradient g r p) • gradient g r p) (gradient g r p) = 0 := by
      rw [g.metricInner_sub_left, g.metricInner_smul_left, hunitp, mul_one, sub_self]
    have htanperp : g.metricInner p
        (tangentialCurvatureTensor D.toAffineConnection g (gradient g r) X Y Z p)
        (gradient g r p) = 0 := by
      rw [tangentialCurvatureTensor_apply, g.metricInner_sub_left,
        g.metricInner_sub_left]
      have h : ∀ (v : TangentSpace I p) (Z' : Π x : M, TangentSpace I x),
          g.metricInner p
            (tangentialCov D.toAffineConnection g (gradient g r) p v Z')
            (gradient g r p) = 0 := by
        intro v Z'
        rw [tangentialCov_apply, g.metricInner_sub_left, g.metricInner_smul_left,
          hunitp, mul_one, sub_self]
      rw [h, h, h, sub_zero, sub_zero]
    have hBN : g.metricInner p
        (bivectorSkewMap g p (hessianOperator D.toAffineConnection g r p (X p))
          (hessianOperator D.toAffineConnection g r p (Y p)) (Z p))
        (gradient g r p) = 0 := by
      rw [bivectorSkewMap_metricInner, bivectorInnerProduct]
      simp only [hessianOperator_apply]
      rw [hSXN, hSYN]; ring
    have hRHSN : g.metricInner p
        (tangentialCurvatureTensor D.toAffineConnection g (gradient g r) X Y Z p
          + bivectorSkewMap g p
              (hessianOperator D.toAffineConnection g r p (X p))
              (hessianOperator D.toAffineConnection g r p (Y p)) (Z p))
        (gradient g r p) = 0 := by
      rw [g.metricInner_add_left, htanperp, hBN, add_zero]
    -- combine along `w = (w − g(w,N)N) + g(w,N)N`
    have hsplit : w = (w - g.metricInner p w (gradient g r p) • gradient g r p)
        + g.metricInner p w (gradient g r p) • gradient g r p := by abel
    have huperp : g.metricInner p
        (w - g.metricInner p w (gradient g r p) • gradient g r p)
        (gradient g r p) = 0 := by
      rw [g.metricInner_sub_left, g.metricInner_smul_left, hunitp, mul_one, sub_self]
    rw [hsplit, g.metricInner_add_right, g.metricInner_add_right, hkey _ huperp,
      g.metricInner_smul_right, g.metricInner_smul_right, hLN, hRHSN]
  exact ⟨hpart1, hpart2, hpart3⟩

end PetersenLib
