import HatcherLib.Ch1.VanKampen
import HatcherLib.Ch1.HomotopyApplications
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Order.IntermediateValue

/-!
# Chapter 1: the fundamental group of a higher-dimensional sphere

The standard sphere is covered by the complements of two antipodal points.
Stereographic projection identifies each member with Euclidean space and
their intersection with punctured Euclidean space.  For spheres of dimension
at least two the latter is path connected, so the loop-decomposition theorem
shows that every loop is nullhomotopic.
-/

namespace HatcherLib

open Metric Set

noncomputable section

universe u v

/-! ## A simply-connected-cover criterion -/

/-- A loop contained in a simply connected subset is nullhomotopic in the
ambient space. -/
theorem loop_nullhomotopic_of_isSimplyConnected
    {X : Type u} [TopologicalSpace X] {A : Set X} {x : X}
    (hx : x ∈ A) (hA : IsSimplyConnected A)
    (γ : Loop x) (hγ : PathIn A γ) :
    γ.Homotopic (Path.refl x) := by
  let xA : A := ⟨x, hx⟩
  let γA : Path xA xA := {
    toFun := fun t => ⟨γ t, hγ ⟨t, rfl⟩⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := Subtype.ext γ.source
    target' := Subtype.ext γ.target }
  letI : SimplyConnectedSpace A := hA.simplyConnectedSpace
  have hsub : γA.Homotopic (Path.refl xA) :=
    SimplyConnectedSpace.paths_homotopic γA (Path.refl xA)
  have hamb := hsub.map ⟨Subtype.val, continuous_subtype_val⟩
  have hγA : γA.map continuous_subtype_val = γ := by
    apply Path.ext
    rfl
  have hrefl : (Path.refl xA).map continuous_subtype_val = Path.refl x := by
    apply Path.ext
    rfl
  rw [← hγA, ← hrefl]
  exact hamb

/-- A finite product of loops, each lying in one member of a simply connected
cover, is nullhomotopic. -/
theorem coveredLoopProduct_nullhomotopic
    {X : Type u} [TopologicalSpace X] {x : X} {ι : Type v}
    (carrier : ι → Set X) (hx : ∀ i, x ∈ carrier i)
    (hsc : ∀ i, IsSimplyConnected (carrier i))
    (loops : List (CoveredLoop x))
    (hloops : ∀ p ∈ loops, ∃ i, PathIn (carrier i) p.path) :
    (coveredLoopProduct x loops).Homotopic (Path.refl x) := by
  induction loops with
  | nil => exact Path.Homotopic.refl (Path.refl x)
  | cons p ps ih =>
      obtain ⟨i, hi⟩ := hloops p (by simp)
      have hp : p.path.Homotopic (Path.refl x) :=
        loop_nullhomotopic_of_isSimplyConnected (hx i) (hsc i) p.path hi
      have hps : ∀ q ∈ ps, ∃ i, PathIn (carrier i) q.path := by
        intro q hq
        exact hloops q (by simp [hq])
      exact (Path.Homotopic.hcomp hp (ih hps)).trans
        (Path.Homotopic.refl_trans (Path.refl x))

/-- A path-connected space covered as in the loop-decomposition theorem by
simply connected members is simply connected. -/
theorem simplyConnectedSpace_of_pathConnectedOpenCover
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (hsc : ∀ i, IsSimplyConnected (cover.carrier i)) :
    SimplyConnectedSpace X := by
  have hbase (γ : Loop x₀) : γ.Homotopic (Path.refl x₀) := by
    obtain ⟨loops, hγ, hloops⟩ :=
      loop_decomposition_of_pathConnectedOpenCover cover γ
    exact hγ.trans
      (coveredLoopProduct_nullhomotopic cover.carrier cover.base_mem hsc loops hloops)
  have hsub : Subsingleton (FundamentalGroup X x₀) := by
    constructor
    intro a b
    change FundamentalGroup.toPath a = FundamentalGroup.toPath b
    obtain ⟨γ, hγ⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath a)
    obtain ⟨δ, hδ⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath b)
    rw [← hγ, ← hδ]
    exact Path.Homotopic.Quotient.eq.mpr ((hbase γ).trans (hbase δ).symm)
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x γ
  let p : Path x x₀ := PathConnectedSpace.somePath x x₀
  let e : FundamentalGroup X x ≃* FundamentalGroup X x₀ :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
  have heq : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = e 1 :=
    hsub.elim _ _
  have hγeq : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = 1 :=
    e.injective heq
  apply Path.Homotopic.Quotient.eq.mp
  change FundamentalGroup.toPath
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
    FundamentalGroup.toPath 1
  exact congrArg FundamentalGroup.toPath hγeq

/-! ## Stereographic charts -/

/-- Deleting one point from the standard `n`-sphere leaves a space
homeomorphic to `n`-dimensional Euclidean space. -/
theorem sphereComplementHomeomorphEuclidean {n : ℕ}
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty ((({x}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) ≃ₜ
      EuclideanSpace ℝ (Fin n)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 1))
  refine ⟨(Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    (((stereographic' n x).toHomeomorphSourceTarget.trans
      (Homeomorph.setCongr (stereographic'_target (n := n) x))).trans
      (Homeomorph.Set.univ _))⟩

/-- Deleting two antipodal points from the standard `(n+1)`-sphere leaves
punctured `(n+1)`-dimensional Euclidean space. -/
theorem sphereComplementTwoPointsHomeomorphPuncturedEuclidean {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    Nonempty ((({v, -v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  letI : Fact
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) :=
    Fact.mk (by rw [finrank_euclideanSpace_fin])
  let e : OpenPartialHomeomorph
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (EuclideanSpace ℝ (Fin (n + 1))) :=
    stereographic' (n + 1) (-v)
  have hv_source : v ∈ e.source := by
    simp [e, stereographic'_source, ne_neg_of_mem_unit_sphere ℝ v]
  have hv_zero : e v = 0 := by
    dsimp [e, stereographic']
    exact
      (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1)
          (ne_zero_of_mem_unit_sphere (-v))).repr.map_eq_zero_iff.mpr
        (stereographic_neg_apply v)
  have hs : ({v, -v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) ⊆ e.source := by
    intro x hx
    simp [e, stereographic'_source] at hx ⊢
    exact hx.2
  have himage :
      e '' ({v, -v}ᶜ : Set
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) =
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx_source : x ∈ e.source := hs hx
      simp at hx ⊢
      intro hy
      have hxeq : x = v := e.injOn hx_source hv_source (by simp [hv_zero, hy])
      exact hx.1 hxeq
    · intro hy
      have hy_ne_zero : y ≠ 0 := hy
      have hy_target : y ∈ e.target := by simp [e, stereographic'_target]
      refine ⟨e.symm y, ?_, e.right_inv hy_target⟩
      have hy_source : e.symm y ∈ e.source := e.map_target hy_target
      have hy_not_neg : e.symm y ≠ -v := by
        simpa [e, stereographic'_source] using hy_source
      have hy_not_v : e.symm y ≠ v := by
        intro hEq
        have : y = 0 := by rw [← e.right_inv hy_target, hEq, hv_zero]
        exact hy_ne_zero this
      simp [hy_not_v, hy_not_neg]
  exact ⟨e.homeomorphOfImageSubsetSource hs himage⟩

/-! ## The standard sphere -/

/-- A pole in the standard sphere of dimension `k + 2`. -/
def standardSpherePole (k : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- A basepoint distinct from both chosen poles. -/
def standardSphereBasepoint (k : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
  ⟨EuclideanSpace.single 1 1, by simp⟩

private theorem standardSphereBasepoint_ne_pole (k : ℕ) :
    standardSphereBasepoint k ≠ standardSpherePole k := by
  intro h
  have h0 := congrArg
    (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 =>
      (x : EuclideanSpace ℝ (Fin (k + 3))) 0) h
  simp [standardSphereBasepoint, standardSpherePole] at h0

private theorem standardSphereBasepoint_ne_neg_pole (k : ℕ) :
    standardSphereBasepoint k ≠ -standardSpherePole k := by
  intro h
  have h0 := congrArg
    (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 =>
      (x : EuclideanSpace ℝ (Fin (k + 3))) 0) h
  simp [standardSphereBasepoint, standardSpherePole] at h0

private theorem standardSpherePole_ne_neg (k : ℕ) :
    standardSpherePole k ≠ -standardSpherePole k :=
  ne_neg_of_mem_unit_sphere ℝ (standardSpherePole k)

private theorem standardSphereComplement_isPathConnected
    (k : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :
    IsPathConnected ({v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) := by
  obtain ⟨e⟩ := sphereComplementHomeomorphEuclidean (n := k + 2) v
  letI : PathConnectedSpace
      ({v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

private theorem standardSphereComplement_isSimplyConnected
    (k : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :
    IsSimplyConnected ({v}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) := by
  obtain ⟨e⟩ := sphereComplementHomeomorphEuclidean (n := k + 2) v
  exact e.toHomotopyEquiv.simplyConnectedSpace

private theorem standardSphereTwoPointComplement_isPathConnected (k : ℕ) :
    IsPathConnected ({standardSpherePole k, -standardSpherePole k}ᶜ : Set
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) := by
  obtain ⟨e⟩ := sphereComplementTwoPointsHomeomorphPuncturedEuclidean
    (n := k + 1) (standardSpherePole k)
  have hrank :
      1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (k + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < k + 2 by omega)
  have hpunc : IsPathConnected
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 2)))) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  letI : PathConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 2)))) :=
    isPathConnected_iff_pathConnectedSpace.mp hpunc
  letI : PathConnectedSpace
      ({standardSpherePole k, -standardSpherePole k}ᶜ : Set
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

/-- The cover of a standard sphere by the complements of two antipodal
points, based at a third coordinate unit vector. -/
def standardSpherePathConnectedOpenCover (k : ℕ) :
    PathConnectedOpenCover (standardSphereBasepoint k) Bool where
  carrier
    | false => {standardSpherePole k}ᶜ
    | true => {-standardSpherePole k}ᶜ
  isOpen i := by
    cases i <;> exact isOpen_compl_singleton
  cover := by
    intro x _
    by_cases hx : x = standardSpherePole k
    · refine Set.mem_iUnion.2 ⟨true, ?_⟩
      subst x
      exact standardSpherePole_ne_neg k
    · refine Set.mem_iUnion.2 ⟨false, ?_⟩
      exact hx
  base_mem i := by
    cases i
    · exact standardSphereBasepoint_ne_pole k
    · exact standardSphereBasepoint_ne_neg_pole k
  pathConnected i := by
    cases i
    · exact standardSphereComplement_isPathConnected k (standardSpherePole k)
    · exact standardSphereComplement_isPathConnected k (-standardSpherePole k)
  interPathConnected i j := by
    cases i <;> cases j
    · simpa [inter_self] using
        standardSphereComplement_isPathConnected k (standardSpherePole k)
    · rw [show {standardSpherePole k}ᶜ ∩ {-standardSpherePole k}ᶜ =
          {standardSpherePole k, -standardSpherePole k}ᶜ by
        ext x
        simp]
      exact standardSphereTwoPointComplement_isPathConnected k
    · rw [show {-standardSpherePole k}ᶜ ∩ {standardSpherePole k}ᶜ =
          {standardSpherePole k, -standardSpherePole k}ᶜ by
        ext x
        simp [and_comm]]
      exact standardSphereTwoPointComplement_isPathConnected k
    · simpa [inter_self] using
        standardSphereComplement_isPathConnected k (-standardSpherePole k)

private theorem standardSphereCover_isSimplyConnected (k : ℕ) :
    ∀ i, IsSimplyConnected ((standardSpherePathConnectedOpenCover k).carrier i) := by
  intro i
  cases i
  · exact standardSphereComplement_isSimplyConnected k (standardSpherePole k)
  · exact standardSphereComplement_isSimplyConnected k (-standardSpherePole k)

/-- The standard sphere of dimension `k + 2` is simply connected. -/
theorem standardSphereSimplyConnected (k : ℕ) :
    SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) := by
  have hpc : IsPathConnected
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) := by
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (k + 3))) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (show 1 < k + 3 by omega)
    exact isPathConnected_sphere hrank 0 zero_le_one
  letI : PathConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hpc
  exact simplyConnectedSpace_of_pathConnectedOpenCover
    (standardSpherePathConnectedOpenCover k)
    (standardSphereCover_isSimplyConnected k)

/-- The standard `n`-sphere is simply connected when `n ≥ 2`. -/
theorem sphereSimplyConnected_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hdim : 2 + k + 1 = k + 3 := by omega
  rw [hdim]
  exact standardSphereSimplyConnected k

/-- Equivalently, the fundamental group of the standard `n`-sphere is
trivial for `n ≥ 2`. -/
theorem sphere_piOne_subsingleton_of_two_le {n : ℕ} (hn : 2 ≤ n)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Subsingleton (PiOne x) := by
  letI : SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    sphereSimplyConnected_of_two_le hn
  constructor
  intro a b
  apply MulOpposite.unop_injective
  change FundamentalGroup.toPath (MulOpposite.unop a) =
    FundamentalGroup.toPath (MulOpposite.unop b)
  exact Subsingleton.elim _ _

/-! ## Euclidean spaces of different dimensions -/

/-- A homeomorphism that fixes zero identifies the complements of zero. -/
theorem homeomorph_image_compl_singleton_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Zero X] [Zero Y] (e : X ≃ₜ Y) (h₀ : e 0 = 0) :
    e '' ({0}ᶜ : Set X) = ({0}ᶜ : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro hy
    apply hx
    apply e.injective
    simpa [h₀] using hy
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro hx₀
    simp only [Set.mem_singleton_iff] at hx₀
    apply hy
    rw [← e.apply_symm_apply y, hx₀, h₀]
    simp

/-- Punctured Euclidean `(k + 3)`-space has trivial fundamental group. -/
theorem puncturedEuclidean_piOne_subsingleton (k : ℕ)
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 3))))) :
    Subsingleton (PiOne x) := by
  let e := homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (k + 3)))
  let y := e x
  have hs : Subsingleton (PiOne y.1) := by
    simpa only [show k + 2 + 1 = k + 3 by omega] using
      sphere_piOne_subsingleton_of_two_le (n := k + 2) (by omega) y.1
  letI : Subsingleton (PiOne y.1) := hs
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by simp⟩
  letI : Subsingleton (PiOne y.2) :=
    contractible_piOne_subsingleton y.2
  have hprod : Subsingleton (PiOne (y.1, y.2)) := by
    constructor
    intro a b
    apply (piOneProdMulEquiv y.1 y.2).symm.injective
    exact Subsingleton.elim _ _
  have he : PiOne x ≃* PiOne (e x) :=
    homotopyEquivPiOneMulEquiv e.toHomotopyEquiv x
  constructor
  intro a b
  apply he.injective
  exact hprod.elim _ _

/-- The fundamental group of the punctured complex plane is nontrivial. -/
theorem puncturedComplex_piOne_nontrivial :
    ∃ x : ({0}ᶜ : Set ℂ), Nontrivial (PiOne x) := by
  let e := homeomorphUnitSphereProd ℂ
  let s : Circle := 1
  let r : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let x : ({0}ᶜ : Set ℂ) := e.symm (s, r)
  have hx : e x = (s, r) := e.apply_symm_apply (s, r)
  refine ⟨x, ?_⟩
  let he₀ : PiOne x ≃* PiOne (e x) :=
    homotopyEquivPiOneMulEquiv e.toHomotopyEquiv x
  let he : PiOne x ≃* PiOne (s, r) :=
    he₀.trans (MulEquiv.cast (M := fun z => PiOne z) hx)
  let a₀ : PiOne s :=
    MulOpposite.op
      (geometricCircleFundamentalGroupMulEquiv.symm
        (Multiplicative.ofAdd (0 : ℤ)))
  let b₀ : PiOne s :=
    MulOpposite.op
      (geometricCircleFundamentalGroupMulEquiv.symm
        (Multiplicative.ofAdd (1 : ℤ)))
  let u : PiOne r := 1
  let a : PiOne x := he.symm (piOneProdMulEquiv s r (a₀, u))
  let b : PiOne x := he.symm (piOneProdMulEquiv s r (b₀, u))
  refine ⟨⟨a, b, ?_⟩⟩
  intro hab
  have hp := congrArg he hab
  have hp₀ :
      piOneProdMulEquiv s r (a₀, u) = piOneProdMulEquiv s r (b₀, u) := by
    simpa only [a, b, MulEquiv.apply_symm_apply] using hp
  have hp' := (piOneProdMulEquiv s r).injective hp₀
  have hcircle := congrArg
    (fun q : PiOne s =>
      geometricCircleFundamentalGroupMulEquiv (MulOpposite.unop q))
    (congrArg Prod.fst hp')
  have hm :
      Multiplicative.ofAdd (0 : ℤ) = Multiplicative.ofAdd (1 : ℤ) := by
    simpa only [s, a₀, b₀, MulOpposite.unop_op, MulEquiv.apply_symm_apply] using hcircle
  have hz : (0 : ℤ) = 1 :=
    congrArg (fun z : Multiplicative ℤ => z.toAdd) hm
  exact zero_ne_one hz

private theorem real_compl_zero_not_preconnected :
    ¬ IsPreconnected ({0}ᶜ : Set ℝ) := by
  intro h
  have hIV := h.intermediate_value
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (by simp) (by simp) continuousOn_id
  have hzero := hIV (show (0 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)
  rcases hzero with ⟨x, hx, hxeq⟩
  apply hx
  simp only [Set.mem_singleton_iff]
  simpa using hxeq

/-- The standard real two-space, represented as a Euclidean space, is
homeomorphic to the complex plane. -/
def euclideanTwoHomeomorphComplex : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
    (Homeomorph.finTwoArrow (X := ℝ))).trans
      Complex.equivRealProdCLM.toHomeomorph.symm

private theorem complex_not_homeomorphic_euclideanOne
    (e : ℂ ≃ₜ EuclideanSpace ℝ (Fin 1)) : False := by
  let e' := e.trans (Homeomorph.addLeft (-e 0))
  have he'₀ : e' 0 = 0 := by simp [e']
  have himage := homeomorph_image_compl_singleton_zero e' he'₀
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  have hC : IsConnected ({0}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank hrank 0
  have hEimg : IsConnected (e' '' ({0}ᶜ : Set ℂ)) :=
    (e'.isConnected_image).2 hC
  have hE : IsConnected ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) := by
    rw [← himage]
    exact hEimg
  let u : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
    (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans
      (Homeomorph.piUnique (fun _ : Fin 1 => ℝ))
  have hu₀ : u 0 = 0 := by simp [u]
  have huimage := homeomorph_image_compl_singleton_zero u hu₀
  have hRimg : IsConnected
      (u '' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1)))) :=
    (u.isConnected_image).2 hE
  have hR : IsConnected ({0}ᶜ : Set ℝ) := by
    rw [← huimage]
    exact hRimg
  exact real_compl_zero_not_preconnected hR.isPreconnected

private theorem complex_not_homeomorphic_euclideanSuccThree (k : ℕ)
    (e : ℂ ≃ₜ EuclideanSpace ℝ (Fin (k + 3))) : False := by
  let e' := e.trans (Homeomorph.addLeft (-e 0))
  have he'₀ : e' 0 = 0 := by simp [e']
  have himage := homeomorph_image_compl_singleton_zero e' he'₀
  let hp : ({0}ᶜ : Set ℂ) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 3)))) :=
    (e'.image ({0}ᶜ : Set ℂ)).trans (Homeomorph.setCongr himage)
  obtain ⟨x, hnontriv⟩ := puncturedComplex_piOne_nontrivial
  let y := hp x
  have hpi : PiOne x ≃* PiOne y :=
    homotopyEquivPiOneMulEquiv hp.toHomotopyEquiv x
  have hsub : Subsingleton (PiOne x) := by
    constructor
    intro a b
    apply hpi.injective
    exact (puncturedEuclidean_piOne_subsingleton k (hp x)).elim _ _
  letI : Nontrivial (PiOne x) := hnontriv
  exact not_subsingleton (PiOne x) hsub

/-- `ℝ²` is not homeomorphic to `ℝⁿ` when `n ≠ 2`.  Dimensions at least
three are distinguished by the fundamental groups of their punctured spaces;
dimension one is distinguished by connectedness after deleting a point. -/
theorem euclideanTwo_not_homeomorphic_euclidean {n : ℕ} (hn : n ≠ 2) :
    ¬ Nonempty
      (EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  rintro ⟨e⟩
  let ec : ℂ ≃ₜ EuclideanSpace ℝ (Fin n) :=
    euclideanTwoHomeomorphComplex.symm.trans e
  rcases n with _ | n
  · have htarget : ec (0 : ℂ) = ec (1 : ℂ) := Subsingleton.elim _ _
    exact zero_ne_one (ec.injective htarget)
  rcases n with _ | n
  · exact complex_not_homeomorphic_euclideanOne ec
  rcases n with _ | k
  · exact hn rfl
  · exact complex_not_homeomorphic_euclideanSuccThree k ec

end
end HatcherLib
