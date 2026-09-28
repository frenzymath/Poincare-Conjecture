import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4

/-!
# Poincaré Ch. 1, §1.2 — The Riemann curvature tensor

Formalizes Morgan–Tian's Riemann curvature tensor (blueprint
`def:riemann-curvature-tensor`) and its first-order symmetries and first
Bianchi identity (blueprint `claim:curvature-symmetries-bianchi`).

**Sign conventions.** Morgan–Tian's curvature operator is
`R_MT(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`,
which is exactly *minus* DoCarmoLib's do-Carmo-convention curvature operator
`Riemannian.AffineConnection.curvature`,
`R_dC(X,Y)Z = ∇_Y ∇_X Z − ∇_X ∇_Y Z + ∇_{[X,Y]} Z`.
We package the Morgan–Tian `(1,3)`-tensor as `riemannCurvature` and bridge it
to `R_dC` via `riemannCurvature_apply_eq_neg`.

Morgan–Tian's `(0,4)`-tensor is `R_MT(X,Y,Z,W) = g(R_MT(X,Y)W, Z)` (note the
transposition of the last two slots), packaged here as `curvatureForm`, as
opposed to DoCarmoLib's `Riemannian.AffineConnection.curvatureForm X Y Z T p
:= g(R_dC(X,Y)Z, T)`. The curvature-operator sign flip and the
metric-inner-product argument-order flip exactly cancel, so the two
`(0,4)`-tensors literally agree (`curvatureForm_eq`); the four first-order
symmetries for a Levi-Civita connection (antisymmetry in each pair,
pair-swap, first Bianchi identity — `claim:curvature-symmetries-bianchi`) are
transported through this bridge from DoCarmoLib's Ch. 4 results. The
**second** Bianchi identity from `claim:curvature-symmetries-bianchi` is
formalized elsewhere.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2
(blueprint `def:riemann-curvature-tensor`, `claim:curvature-symmetries-bianchi`).
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Morgan–Tian's Riemann curvature `(1,3)`-tensor of an affine
connection `∇`,
`R(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`.
This is the *Morgan–Tian* sign convention: it is the negative of DoCarmoLib's
do-Carmo-convention `Riemannian.AffineConnection.curvature`
(see `riemannCurvature_apply_eq_neg`).

Blueprint: `def:riemann-curvature-tensor`. -/
def riemannCurvature (nabla : Riemannian.AffineConnection I M)
    (X Y Z : Riemannian.SmoothVectorField I M) : Riemannian.SmoothVectorField I M :=
  nabla.cov X (nabla.cov Y Z) - nabla.cov Y (nabla.cov X Z)
    - nabla.cov (Riemannian.bracketField X Y) Z

/-- **Math.** Pointwise, Morgan–Tian's curvature operator is minus DoCarmoLib's
do-Carmo-convention curvature operator: `R_MT(X,Y)Z(p) = −R_dC(X,Y)Z(p)`.
Immediate from unfolding both operators: `R_dC(X,Y)Z = ∇_Y∇_XZ − ∇_X∇_YZ +
∇_{[X,Y]}Z` is term-by-term the negative of
`R_MT(X,Y)Z = ∇_X∇_YZ − ∇_Y∇_XZ − ∇_{[X,Y]}Z`.

Blueprint: `def:riemann-curvature-tensor`. -/
theorem riemannCurvature_apply_eq_neg (nabla : Riemannian.AffineConnection I M)
    (X Y Z : Riemannian.SmoothVectorField I M) (p : M) :
    (riemannCurvature nabla X Y Z) p = -(nabla.curvature X Y Z) p := by
  simp only [riemannCurvature, Riemannian.SmoothVectorField.sub_apply, nabla.curvature_apply]
  abel

variable [I.Boundaryless]

/-- **Math.** Morgan–Tian's Riemann curvature `(0,4)`-tensor,
`R(X,Y,Z,W) = g(R(X,Y)W, Z)` — note the transposition: the `(1,3)`-tensor is
applied to `W` and the result is paired against `Z` in the metric.

Blueprint: `def:riemann-curvature-tensor`. -/
def curvatureForm (g : Riemannian.RiemannianMetric I M) (nabla : Riemannian.AffineConnection I M)
    (X Y Z W : Riemannian.SmoothVectorField I M) (p : M) : ℝ :=
  g.metricInner p ((riemannCurvature nabla X Y W) p) (Z p)

/-- **Math.** Morgan–Tian's `(0,4)` curvature tensor literally agrees with
DoCarmoLib's do-Carmo-convention `Riemannian.AffineConnection.curvatureForm`
for a metric-compatible connection: the sign flip of
`riemannCurvature_apply_eq_neg` and the transposition of the last two
metric-inner-product slots (do Carmo's `g(R_dC(X,Y)Z,W)` vs. Morgan–Tian's
`g(R_MT(X,Y)W,Z)`) cancel. Concretely,
`curvatureForm g nabla X Y Z W p`
`= g(riemannCurvature nabla X Y W (p), Z(p))`
`= g(−R_dC(X,Y)W(p), Z(p))`                          (`riemannCurvature_apply_eq_neg`)
`= −g(R_dC(X,Y)W(p), Z(p))`                          (bilinearity of `g`)
`= −(−g(R_dC(X,Y)Z(p), W(p)))`                        (`curvature_inner_antisymm_right`)
`= g(R_dC(X,Y)Z(p), W(p)) = nabla.curvatureForm g X Y Z W p`.

Blueprint: `def:riemann-curvature-tensor`. -/
theorem curvatureForm_eq (g : Riemannian.RiemannianMetric I M)
    (nabla : Riemannian.AffineConnection I M) (hcompat : nabla.IsMetricCompatible g)
    (X Y Z W : Riemannian.SmoothVectorField I M) (p : M) :
    curvatureForm g nabla X Y Z W p = nabla.curvatureForm g X Y Z W p := by
  show g.metricInner p ((riemannCurvature nabla X Y W) p) (Z p)
      = g.metricInner p ((nabla.curvature X Y Z) p) (W p)
  rw [riemannCurvature_apply_eq_neg, Riemannian.RiemannianMetric.metricInner_neg_left,
    nabla.curvature_inner_antisymm_right g hcompat X Y W Z p, neg_neg]

/-- **Math.** Antisymmetry of the Riemann curvature `(0,4)`-tensor in its
**first pair** of arguments, `R(X,Y,Z,W) = −R(Y,X,Z,W)`, for a Levi-Civita
connection. Transported from `Riemannian.AffineConnection.curvatureForm_antisymm_left`
through `curvatureForm_eq`.

Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureForm_antisymm_left (g : Riemannian.RiemannianMetric I M)
    (nabla : Riemannian.AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y Z W : Riemannian.SmoothVectorField I M) (p : M) :
    curvatureForm g nabla X Y Z W p = -(curvatureForm g nabla Y X Z W p) := by
  rw [curvatureForm_eq g nabla hLC.2 X Y Z W p, curvatureForm_eq g nabla hLC.2 Y X Z W p]
  exact nabla.curvatureForm_antisymm_left g X Y Z W p

/-- **Math.** Antisymmetry of the Riemann curvature `(0,4)`-tensor in its
**second pair** of arguments, `R(X,Y,Z,W) = −R(X,Y,W,Z)`, for a Levi-Civita
connection. Transported from `Riemannian.AffineConnection.curvatureForm_antisymm_right`
through `curvatureForm_eq`.

Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureForm_antisymm_right (g : Riemannian.RiemannianMetric I M)
    (nabla : Riemannian.AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y Z W : Riemannian.SmoothVectorField I M) (p : M) :
    curvatureForm g nabla X Y Z W p = -(curvatureForm g nabla X Y W Z p) := by
  rw [curvatureForm_eq g nabla hLC.2 X Y Z W p, curvatureForm_eq g nabla hLC.2 X Y W Z p]
  exact nabla.curvatureForm_antisymm_right g hLC.2 X Y Z W p

/-- **Math.** Pair-swap symmetry of the Riemann curvature `(0,4)`-tensor,
`R(X,Y,Z,W) = R(Z,W,X,Y)`: the pair `(X,Y)` swaps with the pair `(Z,W)`, for
a Levi-Civita connection. Transported from
`Riemannian.AffineConnection.curvatureForm_pairSwap` through `curvatureForm_eq`.

Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureForm_pairSwap (g : Riemannian.RiemannianMetric I M)
    (nabla : Riemannian.AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y Z W : Riemannian.SmoothVectorField I M) (p : M) :
    curvatureForm g nabla X Y Z W p = curvatureForm g nabla Z W X Y p := by
  rw [curvatureForm_eq g nabla hLC.2 X Y Z W p, curvatureForm_eq g nabla hLC.2 Z W X Y p]
  exact nabla.curvatureForm_pairSwap g hLC.1 hLC.2 X Y Z W p

/-- **Math.** The **first Bianchi identity** for the Riemann curvature
`(0,4)`-tensor, in the form quoted by Morgan–Tian, Eq. (`firstBianchi`):
`R(X,Y,Z,W) + R(Y,W,Z,X) + R(W,X,Z,Y) = 0`, i.e. the cyclic sum over `X, Y,
W` (the entries in the first, second and fourth slots) vanishes while `Z`
(the third slot) stays fixed, for a Levi-Civita connection. Derived from
DoCarmoLib's `Riemannian.AffineConnection.curvatureForm_bianchi` (cyclic in the
first three slots, fixed fourth slot) after using `curvatureForm_antisymm_right`
to move the fixed slot from the fourth to the third position in each term.

Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureForm_firstBianchi (g : Riemannian.RiemannianMetric I M)
    (nabla : Riemannian.AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y Z W : Riemannian.SmoothVectorField I M) (p : M) :
    curvatureForm g nabla X Y Z W p + curvatureForm g nabla Y W Z X p
      + curvatureForm g nabla W X Z Y p = 0 := by
  obtain ⟨hsym, hcompat⟩ := hLC
  rw [curvatureForm_eq g nabla hcompat X Y Z W p, curvatureForm_eq g nabla hcompat Y W Z X p,
    curvatureForm_eq g nabla hcompat W X Z Y p]
  have a1 := nabla.curvatureForm_antisymm_right g hcompat X Y Z W p
  have a2 := nabla.curvatureForm_antisymm_right g hcompat Y W Z X p
  have a3 := nabla.curvatureForm_antisymm_right g hcompat W X Z Y p
  have b := nabla.curvatureForm_bianchi g hsym X Y W Z p
  linarith [a1, a2, a3, b]

/-- **Math.** Bundled statement of the first-order symmetries and first
Bianchi identity of the Riemann curvature `(0,4)`-tensor for a Levi-Civita
connection: antisymmetry in the first pair, antisymmetry in the second pair,
pair-swap, and the first Bianchi identity. This is the single anchor
declaration for blueprint `claim:curvature-symmetries-bianchi` (the
**second** Bianchi identity from the same claim is formalized in a separate
file). -/
theorem curvatureForm_symmetries (g : Riemannian.RiemannianMetric I M)
    (nabla : Riemannian.AffineConnection I M) (hLC : nabla.IsLeviCivita g) :
    (∀ (X Y Z W : Riemannian.SmoothVectorField I M) (p : M),
        curvatureForm g nabla X Y Z W p = -(curvatureForm g nabla Y X Z W p)) ∧
      (∀ (X Y Z W : Riemannian.SmoothVectorField I M) (p : M),
        curvatureForm g nabla X Y Z W p = -(curvatureForm g nabla X Y W Z p)) ∧
      (∀ (X Y Z W : Riemannian.SmoothVectorField I M) (p : M),
        curvatureForm g nabla X Y Z W p = curvatureForm g nabla Z W X Y p) ∧
      (∀ (X Y Z W : Riemannian.SmoothVectorField I M) (p : M),
        curvatureForm g nabla X Y Z W p + curvatureForm g nabla Y W Z X p
          + curvatureForm g nabla W X Z Y p = 0) :=
  ⟨curvatureForm_antisymm_left g nabla hLC, curvatureForm_antisymm_right g nabla hLC,
    curvatureForm_pairSwap g nabla hLC, curvatureForm_firstBianchi g nabla hLC⟩

end MorganTianLib
