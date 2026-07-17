import PoincareLib.Ch01.CurvatureTensor
import PoincareLib.Ch01.SecondBianchi
import PoincareLib.Ch01.PointwiseCurvature
import PoincareLib.Ch01.SectionalCurvature
import PoincareLib.Ch01.Einstein

/-!
# Morgan–Tian Ch. 1, §"Curvature of a Riemannian manifold" — manifold-level assembly

This file assembles the algebraic fiber-level results of
`PoincareLib.Ch01.SectionalCurvature` and `PoincareLib.Ch01.Einstein` with the
pointwise curvature bridge of `PoincareLib.Ch01.PointwiseCurvature` into the
manifold-level statements of Morgan–Tian Ch. 1:

* `curvatureForm_secondBianchi` — the second Bianchi identity for
  Morgan–Tian's `(0,4)` curvature tensor (`PoincareLib.curvatureForm`),
  transported from `PoincareLib.secondBianchi` through the sign-convention
  bridge `curvatureForm_eq` (blueprint `claim:curvature-symmetries-bianchi`);
* `scalarCurvatureAt` — the scalar curvature `R = tr_g Ric` at a point
  (blueprint `def:ricci-curvature`);
* `IsEinstein` — the Einstein condition `Ric(g) = λ g` (blueprint
  `def:einstein-manifold`);
* `HasConstantSectionalCurvature` and
  `hasConstantSectionalCurvature_iff_curvatureFormAt_eq` — a manifold has
  constant sectional curvature `λ` iff
  `R(X,Y,Z,W) = λ(⟨X,Z⟩⟨Y,W⟩ − ⟨X,W⟩⟨Y,Z⟩)` (blueprint
  `lem:constant-curvature-tensor`);
* `IsEinstein.sectionalCurvature_const` — in dimensions 2 and 3, an Einstein
  manifold with Einstein constant `λ` has constant sectional curvature
  `λ/(n−1)` (blueprint `ex:einstein-dimension-2-3`, the
  constant-sectional-curvature half; the space-form half needs
  `thm:uniformization` and is not formalized here).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The second Bianchi identity in Morgan–Tian's convention -/

section SecondBianchiMT

variable [I.Boundaryless]

/-- **Math.** The **second Bianchi identity** for Morgan–Tian's `(0,4)`
curvature tensor of a Levi-Civita connection:
`R_{ijkl,h} + R_{ijlh,k} + R_{ijhk,l} = 0`, i.e. the cyclic sum of the
covariant differential `∇R` over its third, fourth and fifth (differentiation)
slots vanishes. Transported from `PoincareLib.secondBianchi` (stated for the
do Carmo-convention `Riemannian.AffineConnection.curvatureForm`) through the
sign-convention bridge `curvatureForm_eq`, which identifies the two `(0,4)`
tensors slot for slot. Blueprint: `claim:curvature-symmetries-bianchi`. -/
theorem curvatureForm_secondBianchi (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y Z W U : SmoothVectorField I M) (p : M) :
    covariantDifferential4 nabla (curvatureForm g nabla) X Y Z W U p
      + covariantDifferential4 nabla (curvatureForm g nabla) X Y W U Z p
      + covariantDifferential4 nabla (curvatureForm g nabla) X Y U Z W p = 0 := by
  have hT : curvatureForm g nabla = nabla.curvatureForm g := by
    funext X' Y' Z' W' p'
    exact curvatureForm_eq g nabla hLC.2 X' Y' Z' W' p'
  rw [hT]
  exact secondBianchi g nabla hLC X Y Z W U p

end SecondBianchiMT

/-! ### Scalar curvature, the Einstein condition, and constant curvature -/

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

section PointwiseAssembly

variable [I.Boundaryless]

/-- **Math.** The **scalar curvature** at `p ∈ M`: the metric trace of the
Ricci tensor, `R = tr_g Ric = Σᵢ Ric(eᵢ, eᵢ)` for an orthonormal basis `{eᵢ}`
of `(T_pM, g_p)` (`Riemannian.scalarCurvature` applied to the pointwise
curvature form). Blueprint: `def:ricci-curvature`. -/
def scalarCurvatureAt (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  scalarCurvature (isAlgCurvatureForm_curvatureFormAt g nabla hLC p)

/-- **Math.** The **Einstein condition** with Einstein constant `λ`: the
Riemannian manifold `(M, g)` is Einstein if `Ric(g) = λ g`, i.e. at every point
`p` and for all tangent vectors `v, w ∈ T_pM` one has
`Ric_p(v, w) = λ g_p(v, w)`. Blueprint: `def:einstein-manifold`. -/
def IsEinstein (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (lam : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p),
    ricciAt g nabla hLC p v w = lam * g.metricInner p v w

end PointwiseAssembly

/-- **Math.** `(M, g)` **has constant sectional curvature** `λ`: at every point
`p` and for every pair `v, w ∈ T_pM`,
`R(v,w,v,w) = λ (g(v,v) g(w,w) − g(v,w)²)`; for `v, w` spanning a `2`-plane
`P` this says exactly `K(P) = λ` (divide by the Gram determinant
`|v ∧ w|² > 0`), and for dependent pairs both sides vanish.
Blueprint: `lem:constant-curvature-tensor`. -/
def HasConstantSectionalCurvature (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (lam : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p),
    curvatureFormAt g nabla p v w v w
      = lam * (g.metricInner p v v * g.metricInner p w w
          - g.metricInner p v w * g.metricInner p v w)

section ConstantCurvature

variable [I.Boundaryless]

/-- **Math.** A Riemannian manifold has constant sectional curvature `λ` if
and only if its curvature tensor is
`R(X,Y,Z,W) = λ (⟨X,Z⟩⟨Y,W⟩ − ⟨X,W⟩⟨Y,Z⟩)`, pointwise. This is the
manifold-level form of `lem:constant-curvature-tensor`, obtained by applying
the fiberwise polarization argument
(`hasConstantCurvature_iff_eq_smul_stdCurvForm`) on each tangent space.
Blueprint: `lem:constant-curvature-tensor`. -/
theorem hasConstantSectionalCurvature_iff_curvatureFormAt_eq
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (lam : ℝ) :
    HasConstantSectionalCurvature g nabla lam ↔
      ∀ (p : M) (v w z t : TangentSpace I p),
        curvatureFormAt g nabla p v w z t
          = lam * (g.metricInner p v z * g.metricInner p w t
              - g.metricInner p w z * g.metricInner p v t) := by
  constructor
  · intro hconst p v w z t
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hiff := hasConstantCurvature_iff_eq_smul_stdCurvForm
      (isAlgCurvatureForm_curvatureFormAt g nabla hLC p) lam
    have hdiag : HasConstantCurvature (curvatureFormAt g nabla p) lam := by
      intro x y
      exact hconst p x y
    have heq := hiff.mp hdiag
    exact congrFun (congrFun (congrFun (congrFun heq v) w) z) t
  · intro heq p v w
    have h := heq p v w v w
    rw [RiemannianMetric.metricInner_comm g p w v] at h
    exact h

end ConstantCurvature

section EinsteinDim23

variable [I.Boundaryless]

/-- **Math.** **Einstein manifolds in dimensions 2 and 3 have constant
sectional curvature `λ/(n−1)`**: if `(M, g)` is Einstein with Einstein
constant `λ` and `n = dim M ∈ {2, 3}`, then for every point `p` and every
orthonormal pair `v, w ∈ T_pM` (spanning an arbitrary `2`-plane `P`),
`K(P) = R(v,w,v,w) = λ/(n−1)`. This is the constant-sectional-curvature half
of `ex:einstein-dimension-2-3`; the space-form conclusion for complete `(M,g)`
additionally requires the uniformization theorem (`thm:uniformization`) and is
not formalized here. Blueprint: `ex:einstein-dimension-2-3`. -/
theorem IsEinstein.sectionalCurvature_const {g : RiemannianMetric I M}
    {nabla : AffineConnection I M} {hLC : nabla.IsLeviCivita g} {lam : ℝ}
    (hE : IsEinstein g nabla hLC lam)
    (hdim : Module.finrank ℝ E = 2 ∨ Module.finrank ℝ E = 3)
    (p : M) (v w : TangentSpace I p)
    (hv : g.metricInner p v v = 1) (hw : g.metricInner p w w = 1)
    (hvw : g.metricInner p v w = 0) :
    curvatureFormAt g nabla p v w v w = lam / (Module.finrank ℝ E - 1) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB := isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  have hfin : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
  have hE' : IsEinsteinForm hB lam := fun v' w' => hE p v' w'
  have hdim' : Module.finrank ℝ (TangentSpace I p) = 2
      ∨ Module.finrank ℝ (TangentSpace I p) = 3 := by
    rw [hfin]; exact hdim
  have h := IsEinsteinForm.sectional_const hB lam hE' hdim' v w hv hw hvw
  rw [hfin] at h
  exact h

end EinsteinDim23

end PoincareLib
