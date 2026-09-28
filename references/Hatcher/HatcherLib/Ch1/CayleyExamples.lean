import HatcherLib.Ch1.AlgebraicConstructions
import HatcherLib.Ch1.Cayley

/-!
# Chapter 1: concrete Cayley graphs

The first Cayley-complex example in Hatcher is a free group: there are no
relator cells, and its universal cover is the Cayley graph.  This module
records the algebraic and combinatorial part of that example.
-/

namespace HatcherLib

universe u

/-- The canonical generators of a free group represent every group element
as a word in generators and inverses. -/
theorem freeGroup_cayleyGenerates (S : Type u) :
    CayleyGenerates (FreeGroup.of : S → FreeGroup S) := by
  rw [cayleyGenerates_iff_closure_range_eq_top]
  exact FreeGroup.closure_range_of S

/-- The Cayley graph of a free group on `S` is connected. -/
theorem freeGroup_cayleySimpleGraph_connected (S : Type u) :
    (CayleySimpleGraph (FreeGroup.of : S → FreeGroup S)).Connected :=
  cayleySimpleGraph_connected _ (freeGroup_cayleyGenerates S)

/-! ## The torus presentation -/

/-- The multiplicative form of `ℤ × ℤ`. -/
abbrev TorusCayleyGroup := Multiplicative (ℤ × ℤ)

/-- The two standard generators of `ℤ × ℤ`. -/
def torusCayleyGenerator : Bool → TorusCayleyGroup
  | false => Multiplicative.ofAdd (1, 0)
  | true => Multiplicative.ofAdd (0, 1)

/-- The commutator attaching word `xyx⁻¹y⁻¹`. -/
def torusCayleyRelator : List (CayleyLetter Bool) :=
  [(false, true), (true, true), (false, false), (true, false)]

theorem torusCayleyRelator_value :
    cayleyWordValue torusCayleyGenerator torusCayleyRelator = 1 := by
  norm_num [cayleyWordValue, cayleyLetterValue, torusCayleyRelator,
    torusCayleyGenerator]

/-- The standard horizontal and vertical translations generate `ℤ × ℤ`. -/
theorem torusCayleyGenerates : CayleyGenerates torusCayleyGenerator := by
  rw [cayleyGenerates_iff_closure_range_eq_top]
  apply top_unique
  rintro ⟨m, n⟩ _
  have hx : torusCayleyGenerator false ∈
      Subgroup.closure (Set.range torusCayleyGenerator) :=
    Subgroup.subset_closure ⟨false, rfl⟩
  have hy : torusCayleyGenerator true ∈
      Subgroup.closure (Set.range torusCayleyGenerator) :=
    Subgroup.subset_closure ⟨true, rfl⟩
  have hprod := Subgroup.mul_mem _
    (Subgroup.zpow_mem _ hx m) (Subgroup.zpow_mem _ hy n)
  have heq : torusCayleyGenerator false ^ m *
      torusCayleyGenerator true ^ n =
        (Multiplicative.ofAdd (m, n) : TorusCayleyGroup) := by
    change m • (1, 0) + n • (0, 1) = (m, n)
    ext <;> simp
  change (Multiplicative.ofAdd (m, n) : TorusCayleyGroup) ∈ _
  rw [← heq]
  exact hprod

/-- The combinatorial Cayley complex for the presentation
`ℤ × ℤ = ⟨x,y | xyx⁻¹y⁻¹⟩`. -/
def torusCayleyComplex : CayleyComplex TorusCayleyGroup Bool where
  generator := torusCayleyGenerator
  relators := {torusCayleyRelator}
  relator_is_identity := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    exact torusCayleyRelator_value

theorem torusCayleySimpleGraph_connected :
    (CayleySimpleGraph torusCayleyGenerator).Connected :=
  cayleySimpleGraph_connected _ torusCayleyGenerates

/-! ## Cyclic groups -/

/-- The cyclic group of order `n`, written multiplicatively.  For `n = 0`
this is the infinite cyclic group. -/
abbrev CyclicCayleyGroup (n : ℕ) := Multiplicative (ZMod n)

/-- The canonical generator of a cyclic group. -/
def cyclicCayleyGenerator (n : ℕ) : PUnit → CyclicCayleyGroup n :=
  fun _ => Multiplicative.ofAdd 1

/-- The relation `xⁿ`. -/
def cyclicCayleyRelator (n : ℕ) : List (CayleyLetter PUnit) :=
  List.replicate n (PUnit.unit, true)

theorem cyclicCayleyRelator_value (n : ℕ) :
    cayleyWordValue (cyclicCayleyGenerator n) (cyclicCayleyRelator n) = 1 := by
  simp only [cayleyWordValue, cyclicCayleyRelator, List.map_replicate,
    cayleyLetterValue, cyclicCayleyGenerator, List.prod_replicate]
  change n • (1 : ZMod n) = 0
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]

/-- The canonical generator generates `ZMod n` for every modulus. -/
theorem cyclicCayleyGenerates (n : ℕ) :
    CayleyGenerates (cyclicCayleyGenerator n) := by
  rw [cayleyGenerates_iff_closure_range_eq_top]
  apply top_unique
  intro g _
  let a : ZMod n := Multiplicative.toAdd g
  let k : ℤ := ZMod.cast a
  have hx : cyclicCayleyGenerator n PUnit.unit ∈
      Subgroup.closure (Set.range (cyclicCayleyGenerator n)) :=
    Subgroup.subset_closure ⟨PUnit.unit, rfl⟩
  have hpow := Subgroup.zpow_mem _ hx k
  have heq : cyclicCayleyGenerator n PUnit.unit ^ k = g := by
    change k • (1 : ZMod n) = a
    dsimp [k]
    rw [zsmul_eq_mul, mul_one, ZMod.intCast_zmod_cast]
  rw [← heq]
  exact hpow

/-- The combinatorial Cayley complex for `⟨x | xⁿ⟩`. -/
def cyclicCayleyComplex (n : ℕ) : CayleyComplex (CyclicCayleyGroup n) PUnit where
  generator := cyclicCayleyGenerator n
  relators := {cyclicCayleyRelator n}
  relator_is_identity := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    exact cyclicCayleyRelator_value n

theorem cyclicCayleySimpleGraph_connected (n : ℕ) :
    (CayleySimpleGraph (cyclicCayleyGenerator n)).Connected :=
  cayleySimpleGraph_connected _ (cyclicCayleyGenerates n)

/-! ## The infinite dihedral group -/

/-- The two order-two factors in the infinite dihedral free product. -/
abbrev DihedralFactor (_ : Bool) := Multiplicative (ZMod 2)

/-- The infinite dihedral group `ℤ₂ * ℤ₂`. -/
abbrev InfiniteDihedralGroup := FreeProduct DihedralFactor

/-- The canonical generators of the two factors. -/
def infiniteDihedralGenerator (i : Bool) : InfiniteDihedralGroup :=
  freeProductInclusion DihedralFactor i (Multiplicative.ofAdd 1)

/-- The two relations `a²` and `b²`, indexed by their generator. -/
def infiniteDihedralRelator (i : Bool) : List (CayleyLetter Bool) :=
  [(i, true), (i, true)]

theorem infiniteDihedralRelator_value (i : Bool) :
    cayleyWordValue infiniteDihedralGenerator (infiniteDihedralRelator i) = 1 := by
  change infiniteDihedralGenerator i * infiniteDihedralGenerator i = 1
  unfold infiniteDihedralGenerator
  rw [← map_mul]
  have htwo :
      (Multiplicative.ofAdd 1 : DihedralFactor i) *
        Multiplicative.ofAdd 1 = 1 := by
    change (1 + 1 : ZMod 2) = 0
    decide
  rw [htwo, map_one]

theorem multiplicativeZModTwo_eq_one_or_generator
    (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  change Multiplicative.toAdd x = 0 ∨ Multiplicative.toAdd x = 1
  generalize Multiplicative.toAdd x = b
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The two factor generators generate their free product. -/
theorem infiniteDihedralCayleyGenerates :
    CayleyGenerates infiniteDihedralGenerator := by
  rw [cayleyGenerates_iff_closure_range_eq_top]
  apply top_unique
  intro g hg
  clear hg
  induction g using Monoid.CoprodI.induction_on with
  | one => exact Subgroup.one_mem _
  | of i x =>
      rcases multiplicativeZModTwo_eq_one_or_generator x with rfl | rfl
      · simp
      · exact Subgroup.subset_closure ⟨i, rfl⟩
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

/-- The combinatorial Cayley complex for `ℤ₂ * ℤ₂`. -/
def infiniteDihedralCayleyComplex : CayleyComplex InfiniteDihedralGroup Bool where
  generator := infiniteDihedralGenerator
  relators := Set.range infiniteDihedralRelator
  relator_is_identity := by
    intro r hr
    obtain ⟨i, rfl⟩ := hr
    exact infiniteDihedralRelator_value i

theorem infiniteDihedralCayleySimpleGraph_connected :
    (CayleySimpleGraph infiniteDihedralGenerator).Connected :=
  cayleySimpleGraph_connected _ infiniteDihedralCayleyGenerates

end HatcherLib
