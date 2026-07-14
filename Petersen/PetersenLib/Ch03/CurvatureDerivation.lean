import PetersenLib.Ch03.CurvatureTensor

/-!
# Petersen Ch. 3, §3.1.1 — The Ricci identity as a derivation

`R_{X,Y}` acts trivially on functions (`curvatureTensor_derivation`): because
the Hessian of a function is symmetric, the second covariant derivative
`∇²_{X,Y} f` of a function — viewed as a `(0,0)`-tensor — is symmetric in
`X, Y`, so in the Ricci identity `∇²_{X,Y} − ∇²_{Y,X} = R_{X,Y}` the curvature
operator kills `C^∞(M)`.

On `(0,1)`-tensors the commutator of second covariant derivatives acts as
(minus) the algebraic action of `R(X,Y)` on the argument
(`secondCovariantDerivative_comm_apply_oneForm`):
`(∇²_{X,Y}T − ∇²_{Y,X}T)(Z) = −T(R(X,Y)Z)`, and on `(0,2)`-tensors as the
two-slot derivation (`secondCovariantDerivative_comm_apply_twoTensor`):
`(∇²_{X,Y}T − ∇²_{Y,X}T)(Z, W) = −T(R(X,Y)Z, W) − T(Z, R(X,Y)W)`. These are
the `k = 1, 2` instances of the derivation formula
`(R_{X,Y}T)(X₁, …, X_k) = −T(R(X,Y)X₁, …, X_k) − ⋯ − T(X₁, …, R(X,Y)X_k)`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.1.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## `R_{X,Y}` acts trivially on functions -/

section Functions

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **The Ricci identity as a derivation, degree `0`** (Petersen
§3.1.1): because the Hessian of a function is symmetric, `R_{X,Y}` acts
trivially on functions — the second covariant derivative of `f ∈ C^∞(M)`,
viewed as a `(0,0)`-tensor, satisfies `∇²_{X,Y} f = ∇²_{Y,X} f`, i.e.
`R_{X,Y} f = ∇²_{X,Y} f − ∇²_{Y,X} f = 0`. Both sides are the covariant
Hessian `(∇ df)`, symmetric by torsion-freeness. -/
theorem curvatureTensor_derivation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (v : Fin 0 → Π x : M, TangentSpace I x) (p : M) :
    secondCovariantDerivative D.toAffineConnection X Y (fun _ => f) v p
      = secondCovariantDerivative D.toAffineConnection Y X (fun _ => f) v p := by
  rw [hessian_eq_secondCovariantDerivative D.toAffineConnection X Y f v p,
    hessian_eq_secondCovariantDerivative D.toAffineConnection Y X f v p]
  exact covariantDerivative_differential_symm D hf hX hY p

end Functions

/-! ## The derivation formula on `(0,1)`-tensors -/

section OneForms

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **The Ricci identity as a derivation, degree `1`** (Petersen
§3.1.1): for a smooth `(0,1)`-tensor `T`, the commutator of second covariant
derivatives acts through (minus) the curvature operator on the argument:
`(∇²_{X,Y}T − ∇²_{Y,X}T)(Z) = −T(R(X,Y)Z)` — the `k = 1` instance of
`(R_{X,Y}T)(X₁, …, X_k) = −T(R(X,Y)X₁, …, X_k) − ⋯ − T(X₁, …, R(X,Y)X_k)`.

The proof expands both second covariant derivatives into directional
derivatives of the scalars `T(Z)`, `T(∇Z)`; the genuinely second-order terms
cancel by the commutator identity `D_{[X,Y]} = [D_X, D_Y]` combined with
torsion-freeness, and the surviving slot terms assemble into `−T(R(X,Y)Z)`. -/
theorem secondCovariantDerivative_comm_apply_oneForm {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {T : TensorOperator I M 1}
    (hT : IsTensorOperator T) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    secondCovariantDerivative D.toAffineConnection X Y T ![Z] p
      - secondCovariantDerivative D.toAffineConnection Y X T ![Z] p
      = -(T ![curvatureTensor D.toAffineConnection X Y Z] p) := by
  -- updating the single slot of a 1-tuple
  have hupd : ∀ (W V : Π x : M, TangentSpace I x),
      Function.update (![W] : Fin 1 → Π x : M, TangentSpace I x) 0 V = ![V] := by
    intro W V
    funext j
    fin_cases j
    simp
  -- the single slot of `![V]` is smooth for smooth `V`
  have hslot : ∀ {V : Π x : M, TangentSpace I x}, IsSmoothVectorField V →
      ∀ i : Fin 1,
        IsSmoothVectorField ((![V] : Fin 1 → Π x : M, TangentSpace I x) i) := by
    intro V hV i
    fin_cases i
    simpa using hV
  -- normal form of the covariant derivative of a `(0,1)`-tensor
  have hcdt : ∀ (U V : Π x : M, TangentSpace I x) (S : TensorOperator I M 1) (q : M),
      covariantDerivativeTensor D.toAffineConnection U S ![V] q
        = directionalDerivative U (S ![V]) q
          - S ![D.toAffineConnection.covField U V] q := by
    intro U V S q
    rw [covariantDerivativeTensor_formula, Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero]
    rw [hupd]
  -- smoothness bookkeeping
  have hTZ : ContMDiff I 𝓘(ℝ) ∞ (T ![Z]) := hT.smooth_eval ![Z] (hslot hZ)
  have hcovYZ : IsSmoothVectorField (D.toAffineConnection.covField Y Z) :=
    D.smooth_cov hY hZ
  have hcovXZ : IsSmoothVectorField (D.toAffineConnection.covField X Z) :=
    D.smooth_cov hX hZ
  have hTYZ : ContMDiff I 𝓘(ℝ) ∞ (T ![D.toAffineConnection.covField Y Z]) :=
    hT.smooth_eval _ (hslot hcovYZ)
  have hTXZ : ContMDiff I 𝓘(ℝ) ∞ (T ![D.toAffineConnection.covField X Z]) :=
    hT.smooth_eval _ (hslot hcovXZ)
  have hDYTZ : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative Y (T ![Z])) :=
    hY.directionalDerivative_contMDiff hTZ
  have hDXTZ : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative X (T ![Z])) :=
    hX.directionalDerivative_contMDiff hTZ
  -- splitting a directional derivative across a pointwise difference
  have hDDsub : ∀ {u v : M → ℝ}, ContMDiff I 𝓘(ℝ) ∞ u → ContMDiff I 𝓘(ℝ) ∞ v →
      ∀ W : Π x : M, TangentSpace I x,
      directionalDerivative W (fun r => u r - v r) p
        = directionalDerivative W u p - directionalDerivative W v p := by
    intro u v hu hv W
    have h1 : (fun r => u r - v r) = u - v := rfl
    rw [h1, directionalDerivative_sub ((hu p).mdifferentiableAt (by decide))
      ((hv p).mdifferentiableAt (by decide)) W]
  -- the first-derivative term of the outer covariant derivative, expanded
  have houterY : directionalDerivative X
      (covariantDerivativeTensor D.toAffineConnection Y T ![Z]) p
      = directionalDerivative X (directionalDerivative Y (T ![Z])) p
        - directionalDerivative X (T ![D.toAffineConnection.covField Y Z]) p := by
    have hfun : covariantDerivativeTensor D.toAffineConnection Y T ![Z]
        = fun q => directionalDerivative Y (T ![Z]) q
          - T ![D.toAffineConnection.covField Y Z] q := by
      funext q
      exact hcdt Y Z T q
    rw [hfun, hDDsub hDYTZ hTYZ X]
  have houterX : directionalDerivative Y
      (covariantDerivativeTensor D.toAffineConnection X T ![Z]) p
      = directionalDerivative Y (directionalDerivative X (T ![Z])) p
        - directionalDerivative Y (T ![D.toAffineConnection.covField X Z]) p := by
    have hfun : covariantDerivativeTensor D.toAffineConnection X T ![Z]
        = fun q => directionalDerivative X (T ![Z]) q
          - T ![D.toAffineConnection.covField X Z] q := by
      funext q
      exact hcdt X Z T q
    rw [hfun, hDDsub hDXTZ hTXZ Y]
  -- expansion of ∇²_{X,Y} T (Z) at p
  have E1 : secondCovariantDerivative D.toAffineConnection X Y T ![Z] p
      = directionalDerivative X (directionalDerivative Y (T ![Z])) p
        - directionalDerivative X (T ![D.toAffineConnection.covField Y Z]) p
        - directionalDerivative Y (T ![D.toAffineConnection.covField X Z]) p
        + T ![D.toAffineConnection.covField Y (D.toAffineConnection.covField X Z)] p
        - directionalDerivative (D.toAffineConnection.covField X Y) (T ![Z]) p
        + T ![D.toAffineConnection.covField (D.toAffineConnection.covField X Y) Z] p := by
    simp only [secondCovariantDerivative, Pi.sub_apply]
    rw [hcdt X Z (covariantDerivativeTensor D.toAffineConnection Y T) p, houterY,
      hcdt Y (D.toAffineConnection.covField X Z) T p,
      hcdt (D.toAffineConnection.covField X Y) Z T p]
    ring
  -- expansion of ∇²_{Y,X} T (Z) at p
  have E2 : secondCovariantDerivative D.toAffineConnection Y X T ![Z] p
      = directionalDerivative Y (directionalDerivative X (T ![Z])) p
        - directionalDerivative Y (T ![D.toAffineConnection.covField X Z]) p
        - directionalDerivative X (T ![D.toAffineConnection.covField Y Z]) p
        + T ![D.toAffineConnection.covField X (D.toAffineConnection.covField Y Z)] p
        - directionalDerivative (D.toAffineConnection.covField Y X) (T ![Z]) p
        + T ![D.toAffineConnection.covField (D.toAffineConnection.covField Y X) Z] p := by
    simp only [secondCovariantDerivative, Pi.sub_apply]
    rw [hcdt Y Z (covariantDerivativeTensor D.toAffineConnection X T) p, houterX,
      hcdt X (D.toAffineConnection.covField Y Z) T p,
      hcdt (D.toAffineConnection.covField Y X) Z T p]
    ring
  -- the second-order terms commute up to `D_{[X,Y]}` (Prop. 2.1.1)
  have hcomm := lieDerivative_vectorField_eq_bracket hX hY hTZ p
  -- torsion-freeness in the differentiated direction
  have hsub : directionalDerivative (D.toAffineConnection.covField X Y) (T ![Z]) p
      - directionalDerivative (D.toAffineConnection.covField Y X) (T ![Z]) p
      = directionalDerivative (lieDerivativeVectorField I X Y) (T ![Z]) p := by
    have hmap := (mfderiv I 𝓘(ℝ) (T ![Z]) p).map_sub (D.cov p (X p) Y) (D.cov p (Y p) X)
    have h1 : directionalDerivative (D.toAffineConnection.covField X Y) (T ![Z]) p
        - directionalDerivative (D.toAffineConnection.covField Y X) (T ![Z]) p
        = (mfderiv I 𝓘(ℝ) (T ![Z]) p (D.cov p (X p) Y - D.cov p (Y p) X) : ℝ) :=
      hmap.symm
    rw [h1, D.torsion_free hX hY p]
    rfl
  -- `T` splits across pointwise differences in its slot
  have hTsub : ∀ (V W : Π x : M, TangentSpace I x),
      T ![fun q => V q - W q] p = T ![V] p - T ![W] p := by
    intro V W
    have h := hT.sub_slot ![Z] 0 V W p
    rwa [hupd, hupd, hupd] at h
  -- the curvature field, rewritten through torsion-freeness
  have hfield : curvatureTensor D.toAffineConnection X Y Z
      = fun q =>
        (D.toAffineConnection.covField X (D.toAffineConnection.covField Y Z) q
          - D.toAffineConnection.covField Y (D.toAffineConnection.covField X Z) q)
        - (D.toAffineConnection.covField (D.toAffineConnection.covField X Y) Z q
          - D.toAffineConnection.covField (D.toAffineConnection.covField Y X) Z q) := by
    funext q
    rw [curvatureTensor_apply]
    have hdir : D.cov q (lieDerivativeVectorField I X Y q) Z
        = D.cov q (D.toAffineConnection.covField X Y q) Z
          - D.cov q (D.toAffineConnection.covField Y X q) Z := by
      rw [← D.toAffineConnection.cov_sub_direction]
      exact congrArg (fun v => D.cov q v Z) (D.torsion_free hX hY q).symm
    rw [hdir]
    rfl
  -- `T` applied to the curvature field, split into four slot terms
  have hcurv : T ![curvatureTensor D.toAffineConnection X Y Z] p
      = T ![D.toAffineConnection.covField X (D.toAffineConnection.covField Y Z)] p
        - T ![D.toAffineConnection.covField Y (D.toAffineConnection.covField X Z)] p
        - (T ![D.toAffineConnection.covField (D.toAffineConnection.covField X Y) Z] p
          - T ![D.toAffineConnection.covField (D.toAffineConnection.covField Y X) Z] p) := by
    rw [hfield, hTsub, hTsub, hTsub]
  rw [E1, E2, hcurv]
  linarith [hcomm, hsub]

end OneForms

/-! ## The derivation formula on `(0,2)`-tensors -/

section TwoTensors

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **The Ricci identity as a derivation, degree `2`** (Petersen
§3.1.1): for a smooth `(0,2)`-tensor `T`, the commutator of second covariant
derivatives acts through (minus) the curvature operator on each slot,
`(∇²_{X,Y}T − ∇²_{Y,X}T)(Z, W) = −T(R(X,Y)Z, W) − T(Z, R(X,Y)W)` — the
`k = 2` instance of the derivation formula. The proof is the same expansion as
in degree `1`, slot by slot; the new mixed terms `T(∇Z, ∇W)` produced by the
two iterated Leibniz expansions are symmetric in `X, Y` and cancel in the
commutator. -/
theorem secondCovariantDerivative_comm_apply_twoTensor {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {T : TensorOperator I M 2}
    (hT : IsTensorOperator T) {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hW : IsSmoothVectorField W) (p : M) :
    secondCovariantDerivative D.toAffineConnection X Y T ![Z, W] p
      - secondCovariantDerivative D.toAffineConnection Y X T ![Z, W] p
      = -(T ![curvatureTensor D.toAffineConnection X Y Z, W] p)
        - T ![Z, curvatureTensor D.toAffineConnection X Y W] p := by
  -- updating the slots of a 2-tuple
  have hupd0 : ∀ (A B V : Π x : M, TangentSpace I x),
      Function.update (![A, B] : Fin 2 → Π x : M, TangentSpace I x) 0 V
        = ![V, B] := by
    intro A B V
    funext j
    fin_cases j
    · simp
    · simp
  have hupd1 : ∀ (A B V : Π x : M, TangentSpace I x),
      Function.update (![A, B] : Fin 2 → Π x : M, TangentSpace I x) 1 V
        = ![A, V] := by
    intro A B V
    funext j
    fin_cases j
    · simp
    · simp
  -- the slots of `![A, B]` are smooth for smooth `A, B`
  have hslot2 : ∀ {A B : Π x : M, TangentSpace I x}, IsSmoothVectorField A →
      IsSmoothVectorField B → ∀ i : Fin 2,
        IsSmoothVectorField ((![A, B] : Fin 2 → Π x : M, TangentSpace I x) i) := by
    intro A B hA hB i
    fin_cases i
    · simpa using hA
    · simpa using hB
  -- normal form of the covariant derivative of a `(0,2)`-tensor
  have hcdt2 : ∀ (U A B : Π x : M, TangentSpace I x) (S : TensorOperator I M 2)
      (q : M),
      covariantDerivativeTensor D.toAffineConnection U S ![A, B] q
        = directionalDerivative U (S ![A, B]) q
          - S ![D.toAffineConnection.covField U A, B] q
          - S ![A, D.toAffineConnection.covField U B] q := by
    intro U A B S q
    rw [covariantDerivativeTensor_formula, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hupd0, hupd1]
    ring
  -- smoothness bookkeeping
  have hTZW : ContMDiff I 𝓘(ℝ) ∞ (T ![Z, W]) := hT.smooth_eval ![Z, W] (hslot2 hZ hW)
  have hcovYZ : IsSmoothVectorField (D.toAffineConnection.covField Y Z) :=
    D.smooth_cov hY hZ
  have hcovXZ : IsSmoothVectorField (D.toAffineConnection.covField X Z) :=
    D.smooth_cov hX hZ
  have hcovYW : IsSmoothVectorField (D.toAffineConnection.covField Y W) :=
    D.smooth_cov hY hW
  have hcovXW : IsSmoothVectorField (D.toAffineConnection.covField X W) :=
    D.smooth_cov hX hW
  have hTYZW : ContMDiff I 𝓘(ℝ) ∞ (T ![D.toAffineConnection.covField Y Z, W]) :=
    hT.smooth_eval _ (hslot2 hcovYZ hW)
  have hTXZW : ContMDiff I 𝓘(ℝ) ∞ (T ![D.toAffineConnection.covField X Z, W]) :=
    hT.smooth_eval _ (hslot2 hcovXZ hW)
  have hTZYW : ContMDiff I 𝓘(ℝ) ∞ (T ![Z, D.toAffineConnection.covField Y W]) :=
    hT.smooth_eval _ (hslot2 hZ hcovYW)
  have hTZXW : ContMDiff I 𝓘(ℝ) ∞ (T ![Z, D.toAffineConnection.covField X W]) :=
    hT.smooth_eval _ (hslot2 hZ hcovXW)
  have hDYTZW : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative Y (T ![Z, W])) :=
    hY.directionalDerivative_contMDiff hTZW
  have hDXTZW : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative X (T ![Z, W])) :=
    hX.directionalDerivative_contMDiff hTZW
  -- splitting a directional derivative across a three-term pointwise difference
  have hDDsub3 : ∀ {u v w : M → ℝ}, ContMDiff I 𝓘(ℝ) ∞ u → ContMDiff I 𝓘(ℝ) ∞ v →
      ContMDiff I 𝓘(ℝ) ∞ w → ∀ U : Π x : M, TangentSpace I x,
      directionalDerivative U (fun r => u r - v r - w r) p
        = directionalDerivative U u p - directionalDerivative U v p
          - directionalDerivative U w p := by
    intro u v w hu hv hw U
    have h1 : (fun r => u r - v r - w r) = (u - v) - w := rfl
    have huv : MDifferentiableAt I 𝓘(ℝ) (u - v) p :=
      ((hu p).mdifferentiableAt (by decide)).sub ((hv p).mdifferentiableAt (by decide))
    rw [h1, directionalDerivative_sub huv ((hw p).mdifferentiableAt (by decide)) U,
      directionalDerivative_sub ((hu p).mdifferentiableAt (by decide))
        ((hv p).mdifferentiableAt (by decide)) U]
  -- the first-derivative terms of the outer covariant derivatives, expanded
  have houterY2 : directionalDerivative X
      (covariantDerivativeTensor D.toAffineConnection Y T ![Z, W]) p
      = directionalDerivative X (directionalDerivative Y (T ![Z, W])) p
        - directionalDerivative X (T ![D.toAffineConnection.covField Y Z, W]) p
        - directionalDerivative X (T ![Z, D.toAffineConnection.covField Y W]) p := by
    have hfun : covariantDerivativeTensor D.toAffineConnection Y T ![Z, W]
        = fun q => directionalDerivative Y (T ![Z, W]) q
          - T ![D.toAffineConnection.covField Y Z, W] q
          - T ![Z, D.toAffineConnection.covField Y W] q := by
      funext q
      exact hcdt2 Y Z W T q
    rw [hfun, hDDsub3 hDYTZW hTYZW hTZYW X]
  have houterX2 : directionalDerivative Y
      (covariantDerivativeTensor D.toAffineConnection X T ![Z, W]) p
      = directionalDerivative Y (directionalDerivative X (T ![Z, W])) p
        - directionalDerivative Y (T ![D.toAffineConnection.covField X Z, W]) p
        - directionalDerivative Y (T ![Z, D.toAffineConnection.covField X W]) p := by
    have hfun : covariantDerivativeTensor D.toAffineConnection X T ![Z, W]
        = fun q => directionalDerivative X (T ![Z, W]) q
          - T ![D.toAffineConnection.covField X Z, W] q
          - T ![Z, D.toAffineConnection.covField X W] q := by
      funext q
      exact hcdt2 X Z W T q
    rw [hfun, hDDsub3 hDXTZW hTXZW hTZXW Y]
  -- expansion of ∇²_{X,Y} T (Z, W) at p
  have E1 : secondCovariantDerivative D.toAffineConnection X Y T ![Z, W] p
      = directionalDerivative X (directionalDerivative Y (T ![Z, W])) p
        - directionalDerivative X (T ![D.toAffineConnection.covField Y Z, W]) p
        - directionalDerivative X (T ![Z, D.toAffineConnection.covField Y W]) p
        - directionalDerivative Y (T ![D.toAffineConnection.covField X Z, W]) p
        + T ![D.toAffineConnection.covField Y (D.toAffineConnection.covField X Z), W] p
        + T ![D.toAffineConnection.covField X Z, D.toAffineConnection.covField Y W] p
        - directionalDerivative Y (T ![Z, D.toAffineConnection.covField X W]) p
        + T ![D.toAffineConnection.covField Y Z, D.toAffineConnection.covField X W] p
        + T ![Z, D.toAffineConnection.covField Y (D.toAffineConnection.covField X W)] p
        - directionalDerivative (D.toAffineConnection.covField X Y) (T ![Z, W]) p
        + T ![D.toAffineConnection.covField (D.toAffineConnection.covField X Y) Z, W] p
        + T ![Z, D.toAffineConnection.covField (D.toAffineConnection.covField X Y) W] p := by
    simp only [secondCovariantDerivative, Pi.sub_apply]
    rw [hcdt2 X Z W (covariantDerivativeTensor D.toAffineConnection Y T) p, houterY2,
      hcdt2 Y (D.toAffineConnection.covField X Z) W T p,
      hcdt2 Y Z (D.toAffineConnection.covField X W) T p,
      hcdt2 (D.toAffineConnection.covField X Y) Z W T p]
    ring
  -- expansion of ∇²_{Y,X} T (Z, W) at p
  have E2 : secondCovariantDerivative D.toAffineConnection Y X T ![Z, W] p
      = directionalDerivative Y (directionalDerivative X (T ![Z, W])) p
        - directionalDerivative Y (T ![D.toAffineConnection.covField X Z, W]) p
        - directionalDerivative Y (T ![Z, D.toAffineConnection.covField X W]) p
        - directionalDerivative X (T ![D.toAffineConnection.covField Y Z, W]) p
        + T ![D.toAffineConnection.covField X (D.toAffineConnection.covField Y Z), W] p
        + T ![D.toAffineConnection.covField Y Z, D.toAffineConnection.covField X W] p
        - directionalDerivative X (T ![Z, D.toAffineConnection.covField Y W]) p
        + T ![D.toAffineConnection.covField X Z, D.toAffineConnection.covField Y W] p
        + T ![Z, D.toAffineConnection.covField X (D.toAffineConnection.covField Y W)] p
        - directionalDerivative (D.toAffineConnection.covField Y X) (T ![Z, W]) p
        + T ![D.toAffineConnection.covField (D.toAffineConnection.covField Y X) Z, W] p
        + T ![Z, D.toAffineConnection.covField (D.toAffineConnection.covField Y X) W] p := by
    simp only [secondCovariantDerivative, Pi.sub_apply]
    rw [hcdt2 Y Z W (covariantDerivativeTensor D.toAffineConnection X T) p, houterX2,
      hcdt2 X (D.toAffineConnection.covField Y Z) W T p,
      hcdt2 X Z (D.toAffineConnection.covField Y W) T p,
      hcdt2 (D.toAffineConnection.covField Y X) Z W T p]
    ring
  -- the second-order terms commute up to `D_{[X,Y]}` (Prop. 2.1.1)
  have hcomm := lieDerivative_vectorField_eq_bracket hX hY hTZW p
  -- torsion-freeness in the differentiated direction
  have hsub : directionalDerivative (D.toAffineConnection.covField X Y) (T ![Z, W]) p
      - directionalDerivative (D.toAffineConnection.covField Y X) (T ![Z, W]) p
      = directionalDerivative (lieDerivativeVectorField I X Y) (T ![Z, W]) p := by
    have hmap := (mfderiv I 𝓘(ℝ) (T ![Z, W]) p).map_sub (D.cov p (X p) Y)
      (D.cov p (Y p) X)
    have h1 : directionalDerivative (D.toAffineConnection.covField X Y) (T ![Z, W]) p
        - directionalDerivative (D.toAffineConnection.covField Y X) (T ![Z, W]) p
        = (mfderiv I 𝓘(ℝ) (T ![Z, W]) p (D.cov p (X p) Y - D.cov p (Y p) X) : ℝ) :=
      hmap.symm
    rw [h1, D.torsion_free hX hY p]
    rfl
  -- `T` splits across pointwise differences in each slot
  have hTsub0 : ∀ (V V' B : Π x : M, TangentSpace I x),
      T ![fun q => V q - V' q, B] p = T ![V, B] p - T ![V', B] p := by
    intro V V' B
    have h := hT.sub_slot ![Z, B] 0 V V' p
    rwa [hupd0, hupd0, hupd0] at h
  have hTsub1 : ∀ (A V V' : Π x : M, TangentSpace I x),
      T ![A, fun q => V q - V' q] p = T ![A, V] p - T ![A, V'] p := by
    intro A V V'
    have h := hT.sub_slot ![A, W] 1 V V' p
    rwa [hupd1, hupd1, hupd1] at h
  -- the curvature field, rewritten through torsion-freeness
  have hfield : ∀ (V : Π x : M, TangentSpace I x),
      curvatureTensor D.toAffineConnection X Y V
        = fun q =>
          (D.toAffineConnection.covField X (D.toAffineConnection.covField Y V) q
            - D.toAffineConnection.covField Y (D.toAffineConnection.covField X V) q)
          - (D.toAffineConnection.covField (D.toAffineConnection.covField X Y) V q
            - D.toAffineConnection.covField (D.toAffineConnection.covField Y X) V q) := by
    intro V
    funext q
    rw [curvatureTensor_apply]
    have hdir : D.cov q (lieDerivativeVectorField I X Y q) V
        = D.cov q (D.toAffineConnection.covField X Y q) V
          - D.cov q (D.toAffineConnection.covField Y X q) V := by
      rw [← D.toAffineConnection.cov_sub_direction]
      exact congrArg (fun v => D.cov q v V) (D.torsion_free hX hY q).symm
    rw [hdir]
    rfl
  -- `T` applied to the curvature field in each slot, split into four terms
  have hcurvZ : T ![curvatureTensor D.toAffineConnection X Y Z, W] p
      = T ![D.toAffineConnection.covField X (D.toAffineConnection.covField Y Z), W] p
        - T ![D.toAffineConnection.covField Y (D.toAffineConnection.covField X Z), W] p
        - (T ![D.toAffineConnection.covField (D.toAffineConnection.covField X Y) Z, W] p
          - T ![D.toAffineConnection.covField (D.toAffineConnection.covField Y X) Z, W] p) := by
    rw [hfield Z, hTsub0, hTsub0, hTsub0]
  have hcurvW : T ![Z, curvatureTensor D.toAffineConnection X Y W] p
      = T ![Z, D.toAffineConnection.covField X (D.toAffineConnection.covField Y W)] p
        - T ![Z, D.toAffineConnection.covField Y (D.toAffineConnection.covField X W)] p
        - (T ![Z, D.toAffineConnection.covField (D.toAffineConnection.covField X Y) W] p
          - T ![Z, D.toAffineConnection.covField (D.toAffineConnection.covField Y X) W] p) := by
    rw [hfield W, hTsub1, hTsub1, hTsub1]
  rw [E1, E2, hcurvZ, hcurvW]
  linarith [hcomm, hsub]

end TwoTensors

end PetersenLib
