import Mathlib
import LeeSmoothLib.Ch01.Sec01.Example_1_5
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Projectivization
open scoped LinearAlgebra.Projectivization

/-- Helper for Exercise 1.6: the ambient Euclidean space whose projectivization is `ℝPⁿ`. -/
private abbrev realProjectiveAmbient (n : ℕ) :=
  EuclideanSpace ℝ (Fin (n + 1))

/-- Helper for Exercise 1.6: the unit sphere in the ambient Euclidean space. -/
private abbrev realProjectiveSphere (n : ℕ) :=
  Metric.sphere (0 : realProjectiveAmbient n) 1

/-- Helper for Exercise 1.6: the sign group `{±1}` acting on the unit sphere. -/
private abbrev realProjectiveSignGroup :=
  Metric.sphere (0 : ℝ) 1

/-- Helper for Exercise 1.6: the antipodal quotient of the unit sphere. -/
private abbrev realProjectiveSphereQuotient (n : ℕ) :=
  Quotient (MulAction.orbitRel realProjectiveSignGroup (realProjectiveSphere n))

/-- Helper for Exercise 1.6: the quotient map from the sphere to its antipodal quotient. -/
private def realProjectiveSphereQuotientMk (n : ℕ) :
    realProjectiveSphere n → realProjectiveSphereQuotient n :=
  @Quotient.mk' _ (MulAction.orbitRel realProjectiveSignGroup (realProjectiveSphere n))

/-- Helper for Exercise 1.6: normalize a nonzero vector to a unit vector on the same line. -/
private def realProjectiveNormalizedSphereVector (n : ℕ) :
    { v : realProjectiveAmbient n // v ≠ 0 } → realProjectiveAmbient n :=
  fun v ↦ ‖(v : realProjectiveAmbient n)‖⁻¹ • (v : realProjectiveAmbient n)

/-- Helper for Exercise 1.6: the normalized representative lies on the unit sphere. -/
private theorem realProjectiveNormalizedSphereVector_mem_sphere (n : ℕ)
    (v : { w : realProjectiveAmbient n // w ≠ 0 }) :
    realProjectiveNormalizedSphereVector n v ∈ realProjectiveSphere n := by
  -- The normalization rescales `v` to have norm `1`.
  have hv_norm_ne : ‖(v : realProjectiveAmbient n)‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
  simp [realProjectiveNormalizedSphereVector, realProjectiveSphere, norm_smul, hv_norm_ne]

/-- Helper for Exercise 1.6: choose the normalized sphere point representing a projective class. -/
private def realProjectiveNormalizedSpherePoint (n : ℕ) :
    { v : realProjectiveAmbient n // v ≠ 0 } → realProjectiveSphere n :=
  fun v ↦
    ⟨realProjectiveNormalizedSphereVector n v, realProjectiveNormalizedSphereVector_mem_sphere n v⟩

/-- Helper for Exercise 1.6: the normalization map on nonzero representatives is continuous. -/
private theorem realProjectiveNormalizedSpherePoint_continuous (n : ℕ) :
    Continuous (realProjectiveNormalizedSpherePoint n) := by
  -- The scaling factor `‖v‖⁻¹` varies continuously away from the zero vector.
  have hscale : Continuous fun v : { w : realProjectiveAmbient n // w ≠ 0 } ↦
      ‖(v : realProjectiveAmbient n)‖⁻¹ := by
    refine Continuous.inv₀ ?_ ?_
    · exact continuous_norm.comp continuous_subtype_val
    · intro v
      exact norm_ne_zero_iff.mpr v.2
  -- Multiplying by this continuous scale gives the normalized vector field.
  refine Continuous.subtype_mk ?_ (fun v ↦ realProjectiveNormalizedSphereVector_mem_sphere n v)
  simpa [realProjectiveNormalizedSpherePoint, realProjectiveNormalizedSphereVector] using
    hscale.smul continuous_subtype_val

/-- Helper for Exercise 1.6: projectively equivalent nonzero vectors determine the same antipodal
class after normalization. -/
private theorem real_projective_normalized_orbit_eq (n : ℕ)
    (a b : { v : realProjectiveAmbient n // v ≠ 0 }) (t : ℝ)
    (h : a = t • (b : realProjectiveAmbient n)) :
    realProjectiveSphereQuotientMk n (realProjectiveNormalizedSpherePoint n a) =
      realProjectiveSphereQuotientMk n (realProjectiveNormalizedSpherePoint n b) := by
  -- Route correction: descend normalization to the antipodal quotient first, then compare
  -- projective classes through that quotient instead of trying to prove Hausdorffness directly.
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  dsimp at h ⊢
  have ht : t ≠ 0 := by
    intro ht
    apply ha
    rw [h, ht, zero_smul]
  have hz : ‖t / ‖t‖‖ = 1 := by
    calc
      ‖t / ‖t‖‖ = ‖t‖ / ‖‖t‖‖ := by rw [norm_div]
      _ = ‖t‖ / ‖t‖ := by rw [Real.norm_of_nonneg (norm_nonneg t)]
      _ = 1 := div_self (norm_ne_zero_iff.mpr ht)
  let z : realProjectiveSignGroup := ⟨t / ‖t‖, by
    simpa [realProjectiveSignGroup, mem_sphere_zero_iff_norm] using hz⟩
  apply Quotient.sound
  change realProjectiveNormalizedSpherePoint n ⟨a, ha⟩ ∈
    MulAction.orbit realProjectiveSignGroup (realProjectiveNormalizedSpherePoint n ⟨b, hb⟩)
  refine ⟨z, ?_⟩
  apply Subtype.ext
  have hb_norm_ne : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hscalar :
      (((z : realProjectiveSignGroup) : ℝ) * ‖b‖⁻¹) = t * ‖t • b‖⁻¹ := by
    rw [show (((z : realProjectiveSignGroup) : ℝ)) = t / ‖t‖ by rfl, norm_smul]
    field_simp [norm_ne_zero_iff.mpr ht, hb_norm_ne]
  have hleft :
      ↑(z • realProjectiveNormalizedSpherePoint n ⟨b, hb⟩) =
        (((z : realProjectiveSignGroup) : ℝ) • (‖b‖⁻¹ • b)) := rfl
  calc
    ↑(z • realProjectiveNormalizedSpherePoint n ⟨b, hb⟩)
        = (((z : realProjectiveSignGroup) : ℝ) • (‖b‖⁻¹ • b)) := hleft
    _ = ((((z : realProjectiveSignGroup) : ℝ) * ‖b‖⁻¹) • b) := by rw [smul_smul]
    _ = (t * ‖t • b‖⁻¹) • b := congrArg (fun c : ℝ ↦ c • b) hscalar
    _ = ↑(realProjectiveNormalizedSpherePoint n ⟨a, ha⟩) := by
      simp [realProjectiveNormalizedSpherePoint, realProjectiveNormalizedSphereVector, h,
        smul_smul, mul_comm]

/-- Helper for Exercise 1.6: normalization descends to a continuous map from projective space to
the antipodal sphere quotient. -/
private def realProjectiveToSphereQuotient (n : ℕ) :
    RealProjectiveSpace n → realProjectiveSphereQuotient n :=
  Projectivization.lift
    (fun v ↦ realProjectiveSphereQuotientMk n (realProjectiveNormalizedSpherePoint n v))
    (real_projective_normalized_orbit_eq n)

/-- Helper for Exercise 1.6: the descended normalization map is continuous by the quotient
criterion on nonzero representatives. -/
private theorem realProjectiveToSphereQuotient_continuous (n : ℕ) :
    Continuous (realProjectiveToSphereQuotient n) := by
  let q : { v : realProjectiveAmbient n // v ≠ 0 } → RealProjectiveSpace n :=
    @Quotient.mk' _ (projectivizationSetoid ℝ (realProjectiveAmbient n))
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hmk : Continuous (realProjectiveSphereQuotientMk n) := by
    simpa [realProjectiveSphereQuotientMk] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' (realProjectiveSphere n)
          (MulAction.orbitRel realProjectiveSignGroup (realProjectiveSphere n))))
  -- The formula is explicit on nonzero representatives, so continuity is checked upstairs.
  refine hq.continuous_iff.mpr ?_
  simpa [q, realProjectiveToSphereQuotient, Function.comp] using
    hmk.comp (realProjectiveNormalizedSpherePoint_continuous n)

/-- Helper for Exercise 1.6: a point on the unit sphere is nonzero in the ambient vector space. -/
private theorem realProjectiveSpherePoint_ne_zero (n : ℕ) (x : realProjectiveSphere n) :
    (x : realProjectiveAmbient n) ≠ 0 :=
  Metric.ne_of_mem_sphere x.2 one_ne_zero

/-- Helper for Exercise 1.6: projectivizing a sphere point depends only on its antipodal orbit. -/
private theorem sphereQuotientToRealProjectiveSpace_wellDefined (n : ℕ)
    {a b : realProjectiveSphere n}
    (h : MulAction.orbitRel realProjectiveSignGroup (realProjectiveSphere n) a b) :
    mk ℝ (a : realProjectiveAmbient n) (realProjectiveSpherePoint_ne_zero n a) =
      mk ℝ (b : realProjectiveAmbient n) (realProjectiveSpherePoint_ne_zero n b) := by
  -- A sign scalar is a real scalar, so it preserves the represented projective line.
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  rcases h with ⟨z, hz⟩
  apply (mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨(z : ℝ), ?_⟩
  simpa using congrArg (fun x : realProjectiveSphere n => (x : realProjectiveAmbient n)) hz

/-- Helper for Exercise 1.6: forgetting the chosen unit representative defines a map from the
antipodal sphere quotient to projective space. -/
private def sphereQuotientToRealProjectiveSpace (n : ℕ) :
    realProjectiveSphereQuotient n → RealProjectiveSpace n :=
  Quotient.lift
    (fun x : realProjectiveSphere n ↦
      mk ℝ (x : realProjectiveAmbient n) (realProjectiveSpherePoint_ne_zero n x))
    (fun _ _ h ↦ sphereQuotientToRealProjectiveSpace_wellDefined n h)

/-- Helper for Exercise 1.6: the map from the antipodal sphere quotient back to projective space
is continuous by the quotient criterion on the sphere. -/
private theorem sphereQuotientToRealProjectiveSpace_continuous (n : ℕ) :
    Continuous (sphereQuotientToRealProjectiveSpace n) := by
  let q : realProjectiveSphere n → realProjectiveSphereQuotient n :=
    realProjectiveSphereQuotientMk n
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hmk :
      Continuous (@Quotient.mk' { v : realProjectiveAmbient n // v ≠ 0 }
        (projectivizationSetoid ℝ (realProjectiveAmbient n))) := continuous_quotient_mk'
  have hrep : Continuous fun x : realProjectiveSphere n ↦
      (⟨(x : realProjectiveAmbient n), realProjectiveSpherePoint_ne_zero n x⟩ :
        { v : realProjectiveAmbient n // v ≠ 0 }) := by
    exact
      Continuous.subtype_mk continuous_subtype_val
        (fun x ↦ realProjectiveSpherePoint_ne_zero n x)
  -- The formula is explicit on the sphere, so continuity is checked upstairs.
  refine hq.continuous_iff.mpr ?_
  simpa [q, sphereQuotientToRealProjectiveSpace, Function.comp, Projectivization.mk'_eq_mk] using
    hmk.comp hrep

/-- Helper for Exercise 1.6: a unit sphere point is fixed by the normalization procedure. -/
private theorem realProjectiveNormalizedSpherePoint_of_sphere (n : ℕ) (x : realProjectiveSphere n) :
    realProjectiveNormalizedSpherePoint n
      ⟨(x : realProjectiveAmbient n), realProjectiveSpherePoint_ne_zero n x⟩ = x := by
  -- On the unit sphere the norm is `1`, so normalization does nothing.
  apply Subtype.ext
  have hx_norm : ‖(x : realProjectiveAmbient n)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  simp [realProjectiveNormalizedSpherePoint, realProjectiveNormalizedSphereVector, hx_norm]

/-- Helper for Exercise 1.6: normalization and projectivization are inverse maps between `ℝPⁿ`
and the antipodal quotient of the unit sphere. -/
private theorem real_projective_sphere_quotient_inverse (n : ℕ) :
    Function.LeftInverse (sphereQuotientToRealProjectiveSpace n)
      (realProjectiveToSphereQuotient n) ∧
    Function.RightInverse (sphereQuotientToRealProjectiveSpace n)
      (realProjectiveToSphereQuotient n) := by
  constructor
  · intro x
    -- Normalizing a nonzero representative keeps the same projective line.
    refine Projectivization.ind (K := ℝ) (V := realProjectiveAmbient n) ?_ x
    intro v hv
    change
      mk ℝ (realProjectiveNormalizedSphereVector n ⟨v, hv⟩)
        (realProjectiveSpherePoint_ne_zero n (realProjectiveNormalizedSpherePoint n ⟨v, hv⟩)) =
        mk ℝ v hv
    apply (mk_eq_mk_iff' ℝ _ _ _ hv).2
    refine ⟨‖v‖⁻¹, ?_⟩
    simp [realProjectiveNormalizedSphereVector]
  · intro q
    -- A sphere representative stays fixed after projectivizing and re-normalizing.
    refine Quotient.inductionOn q ?_
    intro x
    simpa [sphereQuotientToRealProjectiveSpace, realProjectiveToSphereQuotient] using
      congrArg (realProjectiveSphereQuotientMk n)
        (realProjectiveNormalizedSpherePoint_of_sphere n x)

/-- Helper for Exercise 1.6: the sign action on the unit sphere is proper because the smul-pair
map has compact source and Hausdorff target. -/
private instance realProjectiveSphereProperSMul (n : ℕ) :
    ProperSMul realProjectiveSignGroup (realProjectiveSphere n) where
  isProperMap_smul_pair := by
    -- The source is compact, so any continuous map into the Hausdorff target is proper.
    have hcont : Continuous fun gx : realProjectiveSignGroup × realProjectiveSphere n ↦
        ((gx.1 • gx.2, gx.2) : realProjectiveSphere n × realProjectiveSphere n) := by
      fun_prop
    exact hcont.isProperMap

/-- Helper for Exercise 1.6: `ℝPⁿ` is homeomorphic to the antipodal quotient of the unit sphere. -/
private def realProjectiveSpaceSphereQuotientHomeomorph (n : ℕ) :
    RealProjectiveSpace n ≃ₜ realProjectiveSphereQuotient n :=
  { toEquiv :=
      { toFun := realProjectiveToSphereQuotient n
        invFun := sphereQuotientToRealProjectiveSpace n
        left_inv := (real_projective_sphere_quotient_inverse n).1
        right_inv := (real_projective_sphere_quotient_inverse n).2 }
    continuous_toFun := realProjectiveToSphereQuotient_continuous n
    continuous_invFun := sphereQuotientToRealProjectiveSpace_continuous n }

-- Proof sketch: identify `ℝPⁿ` with a quotient of the unit sphere by the antipodal action, then
-- use that the sphere is Hausdorff and the antipodal action is proper/discontinuous so the
-- quotient is Hausdorff.
/-- Exercise 1.6 (1): real projective space `ℝPⁿ` is Hausdorff. -/
theorem realProjectiveSpace_t2Space (n : ℕ) : T2Space (RealProjectiveSpace n) := by
  -- Transport Hausdorffness across the sphere-quotient homeomorphism.
  exact (realProjectiveSpaceSphereQuotientHomeomorph n).symm.t2Space

-- Proof sketch: realize `ℝPⁿ` as an open quotient of a second-countable space, for instance the
-- sphere or the nonzero vectors in `ℝ^(n+1)`, and apply the standard quotient theorem for
-- second-countability.
/-- Exercise 1.6 (2): real projective space `ℝPⁿ` is second-countable. -/
theorem realProjectiveSpace_secondCountableTopology (n : ℕ) :
    SecondCountableTopology (RealProjectiveSpace n) := by
  -- The antipodal sphere quotient is second-countable, and the homeomorphism transports that
  -- structure back to `ℝPⁿ`.
  let hq : SecondCountableTopology (realProjectiveSphereQuotient n) := by
    simpa [realProjectiveSphereQuotient] using
      (ContinuousConstSMul.secondCountableTopology
        (Γ := realProjectiveSignGroup) (T := realProjectiveSphere n))
  let _ : SecondCountableTopology (realProjectiveSphereQuotient n) := hq
  exact (realProjectiveSpaceSphereQuotientHomeomorph n).secondCountableTopology

-- Proof sketch: apply the standard affine chart existence theorem from Example 1.5.
/-- Exercise 1.6 (3): every point of `ℝPⁿ` lies in the source of a standard affine chart,
equivalently in a chart whose coordinate map is a homeomorphism with `ℝⁿ`. -/
theorem realProjectiveSpace_has_euclidean_chart (n : ℕ) (x : RealProjectiveSpace n) :
    ∃ i : Fin (n + 1), x ∈ realProjectiveChartDomain n i := by
  -- Example 1.5 already constructs a standard affine chart through every projective point.
  simpa using real_projective_space_has_standard_chart n x

-- Proof sketch: this is exactly the openness statement for the standard affine chart domains from
-- Example 1.5.
/-- Exercise 1.6 (4): each standard affine chart domain in `ℝPⁿ` is open. Together with
Exercise 1.6 (1), Exercise 1.6 (2), and Exercise 1.6 (3), this yields that `ℝPⁿ` is a
topological `n`-manifold. -/
theorem realProjectiveSpace_chartDomain_isOpen (n : ℕ) (i : Fin (n + 1)) :
    IsOpen (realProjectiveChartDomain n i) := by
  -- Example 1.5 proves the standard affine chart domains are open.
  simpa using realProjectiveChartDomain_isOpen n i
