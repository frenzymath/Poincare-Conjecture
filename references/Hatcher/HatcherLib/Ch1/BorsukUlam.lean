import HatcherLib.Ch1.Sphere

/-!
# The two-dimensional Borsuk-Ulam theorem

A fixed-point-free antipodal difference would normalize to an odd map from
the standard two-sphere to the circle.  A path from a point to its antipode,
followed by its antipodal translate, is nullhomotopic on the two-sphere.  Its
image under an odd map is not nullhomotopic on the circle: lifting the first
half through `Circle.exp` shows that the second half adds the same nontrivial
displacement once more.
-/

namespace HatcherLib

noncomputable section

open scoped ContinuousMap unitInterval

/-- The standard unit two-sphere in real three-space. -/
abbrev StandardSphereTwo :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The Euclidean plane, used as the target of Borsuk-Ulam maps. -/
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-! ## The antipodal loop on the circle -/

/-- If `alpha` runs from `a` to `-a` and `beta` is its pointwise antipodal
translate, then `alpha.trans beta` is not nullhomotopic in the circle. -/
theorem circleAntipodalPathLoop_not_nullhomotopic
    {a : Circle} (alpha : Path a (-a)) (beta : Path (-a) a)
    (hbeta : forall t, beta t = -alpha t) :
    ¬ (alpha.trans beta).Homotopic (Path.refl a) := by
  let cov : IsCoveringMap (Circle.exp : Real -> Circle) :=
    Circle.isCoveringMap_exp
  obtain ⟨r, hr⟩ := Circle.exp_surjective a
  let A : C(unitInterval, Real) :=
    cov.liftPath (alpha : C(unitInterval, Circle)) r
      (by simpa using alpha.source.trans hr.symm)
  have hA0 : A 0 = r :=
    cov.liftPath_zero alpha r (by simpa using alpha.source.trans hr.symm)
  have hAlifts : (fun t => Circle.exp (A t)) = alpha :=
    cov.liftPath_lifts alpha r (by simpa using alpha.source.trans hr.symm)
  have hA1exp : Circle.exp (A 1) = -a := by
    simpa using congrFun hAlifts 1
  let B : C(unitInterval, Real) :=
    ⟨fun t => A t + (A 1 - r), A.continuous.add continuous_const⟩
  have hBlifts : (fun t => Circle.exp (B t)) = beta := by
    funext t
    rw [show B t = A t + (A 1 - r) by rfl, Circle.exp_add,
      Circle.exp_sub, hA1exp, hr]
    rw [hbeta]
    apply Circle.ext
    simp [← congrFun hAlifts t]
  have hB0 : B 0 = A 1 := by simp [B, hA0]
  have hB :
      B = cov.liftPath (beta : C(unitInterval, Circle))
        (A 1) (by simpa using beta.source.trans hA1exp.symm) := by
    apply (cov.eq_liftPath_iff' (Γ := B)
      (by simpa using beta.source.trans hA1exp.symm)).mpr
    exact ⟨hBlifts, hB0⟩
  let Cbeta : C(unitInterval, Real) :=
    cov.liftPath (beta : C(unitInterval, Circle))
      (A 1) (by simpa using beta.source.trans hA1exp.symm)
  let Apath : Path r (A 1) := ⟨A, hA0, rfl⟩
  let Bpath : Path (A 1) (Cbeta 1) :=
    ⟨Cbeta, cov.liftPath_zero _ _ _, rfl⟩
  have htrans :
      cov.liftPath (alpha.trans beta : C(unitInterval, Circle))
        r (by simpa using alpha.source.trans hr.symm) =
          (Apath.trans Bpath : C(unitInterval, Real)) := by
    simpa [A, Apath, Cbeta, Bpath] using
      (cov.liftPath_trans (e := r) (by simpa using hr.symm) alpha beta)
  have hfullEnd :
      cov.liftPath (alpha.trans beta : C(unitInterval, Circle))
          r (by simpa using alpha.source.trans hr.symm) 1 =
        A 1 + (A 1 - r) := by
    calc
      _ = (Apath.trans Bpath) 1 := DFunLike.congr_fun htrans 1
      _ = Cbeta 1 := Path.target (Apath.trans Bpath)
      _ = B 1 := DFunLike.congr_fun hB.symm 1
      _ = A 1 + (A 1 - r) := rfl
  intro hnull
  have hend := cov.liftPath_apply_one_eq_of_homotopicRel hnull
    r (by simpa using alpha.source.trans hr.symm)
      (by simpa using (Path.refl a).source.trans hr.symm)
  have hreflLift :
      ContinuousMap.const unitInterval r =
        cov.liftPath (Path.refl a : C(unitInterval, Circle))
          r (by simpa using (Path.refl a).source.trans hr.symm) := by
    apply (cov.eq_liftPath_iff'
      (Γ := ContinuousMap.const unitInterval r)
      (by simpa using (Path.refl a).source.trans hr.symm)).mpr
    constructor
    · funext t
      simpa [Path.refl] using hr
    · rfl
  have hfullR :
      cov.liftPath (alpha.trans beta : C(unitInterval, Circle))
        r (by simpa using alpha.source.trans hr.symm) 1 = r := by
    calc
      _ = cov.liftPath (Path.refl a : C(unitInterval, Circle))
          r (by simpa using (Path.refl a).source.trans hr.symm) 1 := by
            change cov.liftPath (alpha.trans beta).toContinuousMap r _ 1 =
              cov.liftPath (Path.refl a).toContinuousMap r _ 1
            exact hend
      _ = r := by rw [← hreflLift]; rfl
  have heq : A 1 + (A 1 - r) = r := hfullEnd.symm.trans hfullR
  have hAr : A 1 = r := by linarith
  apply Circle.neg_ne_self a
  rw [← hA1exp, hAr, hr]

private def sphereAntipodalSecondPath {x : StandardSphereTwo}
    (p : Path x (-x)) : Path (-x) x :=
  (p.map continuous_neg).cast (by simp) (by simp)

private theorem sphereAntipodalSecondPath_apply {x : StandardSphereTwo}
    (p : Path x (-x)) (t : unitInterval) :
    sphereAntipodalSecondPath p t = -p t := by
  rfl

/-- There is no continuous odd map from the standard two-sphere to the
circle. -/
theorem no_continuous_odd_map_standardSphereTwo_circle
    (q : C(StandardSphereTwo, Circle))
    (hodd : forall x, q (-x) = -q x) : False := by
  letI : SimplyConnectedSpace StandardSphereTwo :=
    standardSphereSimplyConnected 0
  let x0 : StandardSphereTwo := standardSphereBasepoint 0
  let p : Path x0 (-x0) := PathConnectedSpace.somePath x0 (-x0)
  let np : Path (-x0) x0 := sphereAntipodalSecondPath p
  let a : Circle := q x0
  let alpha : Path a (-a) :=
    (p.map q.continuous).cast rfl (hodd x0).symm
  let beta : Path (-a) a :=
    (np.map q.continuous).cast (hodd x0).symm rfl
  have hbetaOdd : forall t, beta t = -alpha t := by
    intro t
    change q (sphereAntipodalSecondPath p t) = -q (p t)
    rw [sphereAntipodalSecondPath_apply, hodd]
  have hdom : (p.trans np).Homotopic (Path.refl x0) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmap := hdom.map q
  have halpha (t : unitInterval) : alpha t = q (p t) := rfl
  have hbeta (t : unitInterval) : beta t = q (np t) := rfl
  have hleft : (p.trans np).map q.continuous = alpha.trans beta := by
    apply Path.ext
    funext t
    simp only [Path.map_coe, Function.comp_apply, Path.trans_apply]
    split_ifs
    · exact (halpha _).symm
    · exact (hbeta _).symm
  have hright : (Path.refl x0).map q.continuous = Path.refl a := by
    apply Path.ext
    rfl
  rw [hleft, hright] at hmap
  exact circleAntipodalPathLoop_not_nullhomotopic
    alpha beta hbetaOdd hmap

/-! ## The normalized antipodal difference -/

private theorem euclideanTwoHomeomorphComplex_zero :
    euclideanTwoHomeomorphComplex (0 : EuclideanPlane) = 0 := by
  simp [euclideanTwoHomeomorphComplex]

private theorem euclideanTwoHomeomorphComplex_neg (v : EuclideanPlane) :
    euclideanTwoHomeomorphComplex (-v) =
      -euclideanTwoHomeomorphComplex v := by
  simp [euclideanTwoHomeomorphComplex]
  rw [← map_neg]
  rfl

private noncomputable def normalizedAntipodalDifference
    (f : C(StandardSphereTwo, EuclideanPlane))
    (hno : forall x, f x ≠ f (-x)) : C(StandardSphereTwo, Circle) where
  toFun x :=
    let z := euclideanTwoHomeomorphComplex (f x - f (-x))
    ⟨z / ‖z‖, by
      change z / (‖z‖ : Complex) ∈ Metric.sphere (0 : Complex) 1
      rw [mem_sphere_zero_iff_norm, norm_div]
      have hz : z ≠ 0 := by
        intro hz
        apply hno x
        apply sub_eq_zero.mp
        apply euclideanTwoHomeomorphComplex.injective
        rw [euclideanTwoHomeomorphComplex_zero]
        exact hz
      simp [norm_ne_zero_iff.mpr hz]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    let z : StandardSphereTwo -> Complex :=
      fun x => euclideanTwoHomeomorphComplex (f x - f (-x))
    have hz : Continuous z := by
      unfold z
      fun_prop
    apply Continuous.div
    · exact hz
    · exact Complex.continuous_ofReal.comp hz.norm
    · intro x
      apply Complex.ofReal_ne_zero.mpr
      apply norm_ne_zero_iff.mpr
      intro hzero
      apply hno x
      apply sub_eq_zero.mp
      apply euclideanTwoHomeomorphComplex.injective
      rw [euclideanTwoHomeomorphComplex_zero]
      exact hzero

private theorem normalizedAntipodalDifference_neg
    (f : C(StandardSphereTwo, EuclideanPlane))
    (hno : forall x, f x ≠ f (-x)) (x : StandardSphereTwo) :
    normalizedAntipodalDifference f hno (-x) =
      -normalizedAntipodalDifference f hno x := by
  apply Circle.ext
  change euclideanTwoHomeomorphComplex (f (-x) - f (-(-x))) /
      (‖euclideanTwoHomeomorphComplex (f (-x) - f (-(-x)))‖ : Complex) =
    -(euclideanTwoHomeomorphComplex (f x - f (-x)) /
      (‖euclideanTwoHomeomorphComplex (f x - f (-x))‖ : Complex))
  rw [show f (-x) - f (-(-x)) = -(f x - f (-x)) by simp]
  rw [euclideanTwoHomeomorphComplex_neg, norm_neg]
  ring

/-! ## Borsuk-Ulam -/

/-- The two-dimensional Borsuk-Ulam theorem: every continuous map from the
standard two-sphere to the plane identifies a pair of antipodal points. -/
theorem borsukUlam_two (f : C(StandardSphereTwo, EuclideanPlane)) :
    exists x, f x = f (-x) := by
  by_contra hn
  have hno : forall x, f x ≠ f (-x) := by
    intro x hx
    exact hn ⟨x, hx⟩
  exact no_continuous_odd_map_standardSphereTwo_circle
    (normalizedAntipodalDifference f hno)
    (normalizedAntipodalDifference_neg f hno)

/-- Unbundled continuous-map form of the two-dimensional Borsuk-Ulam
theorem. -/
theorem borsukUlam_two_of_continuous
    (f : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ->
      EuclideanSpace Real (Fin 2)) (hf : Continuous f) :
    exists x, f x = f (-x) :=
  borsukUlam_two ⟨f, hf⟩

/-! ## A closed-cover consequence -/

private noncomputable def closedSetInfDistPair
    (A B : Set StandardSphereTwo) : C(StandardSphereTwo, EuclideanPlane) where
  toFun x :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i => if i = 0 then Metric.infDist x A else Metric.infDist x B)
  continuous_toFun := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using Metric.continuous_infDist_pt A
    · simpa using Metric.continuous_infDist_pt B

private theorem closedSetInfDistPair_fst
    (A B : Set StandardSphereTwo) (x y : StandardSphereTwo)
    (h : closedSetInfDistPair A B x = closedSetInfDistPair A B y) :
    Metric.infDist x A = Metric.infDist y A := by
  have hc := congrArg
    (fun v : EuclideanPlane => (EuclideanSpace.equiv (Fin 2) ℝ v) 0) h
  simpa [closedSetInfDistPair] using hc

private theorem closedSetInfDistPair_snd
    (A B : Set StandardSphereTwo) (x y : StandardSphereTwo)
    (h : closedSetInfDistPair A B x = closedSetInfDistPair A B y) :
    Metric.infDist x B = Metric.infDist y B := by
  have hc := congrArg
    (fun v : EuclideanPlane => (EuclideanSpace.equiv (Fin 2) ℝ v) 1) h
  simpa [closedSetInfDistPair] using hc

/-- If three closed subsets cover the standard two-sphere, one of them
contains a pair of antipodal points. -/
theorem sphere_three_closed_sets_antipodal
    (A B C : Set StandardSphereTwo)
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (hcover : A ∪ B ∪ C = Set.univ) :
    ∃ x : StandardSphereTwo,
      (x ∈ A ∧ -x ∈ A) ∨
      (x ∈ B ∧ -x ∈ B) ∨
      (x ∈ C ∧ -x ∈ C) := by
  have _ := hC
  obtain ⟨x, hxpair⟩ := borsukUlam_two (closedSetInfDistPair A B)
  have hdistA : Metric.infDist x A = Metric.infDist (-x) A :=
    closedSetInfDistPair_fst A B x (-x) hxpair
  have hdistB : Metric.infDist x B = Metric.infDist (-x) B :=
    closedSetInfDistPair_snd A B x (-x) hxpair
  have hxcover : x ∈ A ∪ B ∪ C := by
    rw [hcover]
    trivial
  by_cases hxA : x ∈ A
  · have hzero : Metric.infDist (-x) A = 0 := by
      rw [← hdistA]
      exact Metric.infDist_zero_of_mem hxA
    have hnegA : -x ∈ A :=
      (hA.mem_iff_infDist_zero ⟨x, hxA⟩).2 hzero
    exact ⟨x, Or.inl ⟨hxA, hnegA⟩⟩
  · by_cases hxB : x ∈ B
    · have hzero : Metric.infDist (-x) B = 0 := by
        rw [← hdistB]
        exact Metric.infDist_zero_of_mem hxB
      have hnegB : -x ∈ B :=
        (hB.mem_iff_infDist_zero ⟨x, hxB⟩).2 hzero
      exact ⟨x, Or.inr (Or.inl ⟨hxB, hnegB⟩)⟩
    · have hxC : x ∈ C := by
        rcases hxcover with hxAB | hxC
        · rcases hxAB with hxA' | hxB'
          · exact (hxA hxA').elim
          · exact (hxB hxB').elim
        · exact hxC
      have hnotA : -x ∉ A := by
        intro hnegA
        have hzeroNeg := Metric.infDist_zero_of_mem hnegA
        have hzeroX : Metric.infDist x A = 0 := hdistA.trans hzeroNeg
        exact hxA ((hA.mem_iff_infDist_zero ⟨-x, hnegA⟩).2 hzeroX)
      have hnotB : -x ∉ B := by
        intro hnegB
        have hzeroNeg := Metric.infDist_zero_of_mem hnegB
        have hzeroX : Metric.infDist x B = 0 := hdistB.trans hzeroNeg
        exact hxB ((hB.mem_iff_infDist_zero ⟨-x, hnegB⟩).2 hzeroX)
      have hnegcover : -x ∈ A ∪ B ∪ C := by
        rw [hcover]
        trivial
      rcases hnegcover with hnegAB | hnegC
      · rcases hnegAB with hnegA | hnegB
        · exact (hnotA hnegA).elim
        · exact (hnotB hnegB).elim
      · exact ⟨x, Or.inr (Or.inr ⟨hxC, hnegC⟩)⟩

end

end HatcherLib
