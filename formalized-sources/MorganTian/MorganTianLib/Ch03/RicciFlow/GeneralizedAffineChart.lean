import MorganTianLib.Ch03.RicciFlow.AffineTimeDiffeomorph
import MorganTianLib.Ch03.RicciFlow.GeneralizedSpaceTime

/-!
# Morgan--Tian Ch. 3 - affine transport of adapted local charts

The positive affine time change acts on the source of an adapted product
chart by the inverse product diffeomorph.  This file records the resulting
partial chart and its domain, target, center, and time-coordinate laws.  The
time-vector differential is proved here; packaging the transported chart into
a full `GeneralizedSpaceTime`/`GeneralizedRicciFlow` remains subsequent.
-/

open scoped ContDiff Manifold Topology
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

private abbrev SpatialModel (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- **Math.** Pull an adapted local chart back along the positive affine time
coordinate change `s = Q t + a`. -/
def affineTimeChangeChart
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : PartialEquiv
      (SpatialModel n × ℝ) N :=
  (affineTimeProductDiffeomorph (E := SpatialModel n) Q a hQ.ne').symm.toEquiv
    |>.transPartialEquiv c.equiv

/-- **Math.** The pulled-back chart has the spatial source unchanged and the
time source transported by the positive affine order isomorphism. -/
theorem affineTimeChangeChart_source
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (affineTimeChangeChart n c Q hQ a).source =
      c.spatialSource ×ˢ
        ((fun t : ℝ => Q * t + a) '' c.timeSource) := by
  let A := affineTimeProductDiffeomorph (E := SpatialModel n) Q a hQ.ne'
  rw [affineTimeChangeChart, Equiv.transPartialEquiv_source]
  change A.symm.toEquiv ⁻¹' c.equiv.source = _
  rw [c.source_eq]
  ext z
  rcases z with ⟨u, s⟩
  constructor
  · intro hz
    have hzA : A.toEquiv (A.symm.toEquiv (u, s)) = (u, s) :=
      A.toEquiv.apply_symm_apply (u, s)
    let t := (A.symm.toEquiv (u, s)).2
    have hcoord : A.symm.toEquiv (u, s) = (u, t) := by
      apply Prod.ext
      · have hfst := congrArg Prod.fst hzA
        change (A.symm.toEquiv (u, s)).1 = u at hfst
        exact hfst
      · rfl
    have ht : t ∈ c.timeSource := by
      exact hz.2
    refine ⟨hz.1, ⟨t, ht, ?_⟩⟩
    have hsnd := congrArg Prod.snd hzA
    rw [hcoord] at hsnd
    have hforward : A.toEquiv (u, t) = (u, Q * t + a) := by
      simpa [A] using
        (affineTimeProductDiffeomorph_apply (E := SpatialModel n)
          Q a hQ.ne' u t)
    rw [hforward] at hsnd
    exact hsnd
  · rintro ⟨hu, t, ht, hst⟩
    have hA : A.toEquiv (u, t) = (u, s) := by
      simpa [A, affineTimeProductDiffeomorph_apply] using
        congrArg (fun v => (u, v)) hst
    have hcoord : A.symm.toEquiv (u, s) = (u, t) := by
      apply A.toEquiv.injective
      calc
        A.toEquiv (A.symm.toEquiv (u, s)) = (u, s) :=
          A.toEquiv.apply_symm_apply _
        _ = A.toEquiv (u, t) := hA.symm
    change A.symm.toEquiv (u, s) ∈ c.spatialSource ×ˢ c.timeSource
    rw [hcoord]
    exact ⟨hu, ht⟩

/-- **Math.** The pulled-back chart map remains smooth on its transported
source. -/
theorem affineTimeChangeChart_contMDiffOn
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    ContMDiffOn
      ((modelWithCornersSelf ℝ (SpatialModel n)).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersEuclideanHalfSpace n.succ) ∞
      (affineTimeChangeChart n c Q hQ a)
      (affineTimeChangeChart n c Q hQ a).source := by
  let A := affineTimeProductDiffeomorph (E := SpatialModel n) Q a hQ.ne'
  rw [affineTimeChangeChart, Equiv.transPartialEquiv_source]
  apply c.to_contMDiffOn.comp A.symm.contMDiff.contMDiffOn
  intro z hz
  exact hz

/-- **Math.** The transported source retains the unique-differential property
needed for the adapted chart. -/
theorem affineTimeChangeChart_source_uniqueMDiffOn
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    UniqueMDiffOn
      ((modelWithCornersSelf ℝ (SpatialModel n)).prod
        (modelWithCornersSelf ℝ ℝ))
      (affineTimeChangeChart n c Q hQ a).source := by
  let A := affineTimeProductDiffeomorph (E := SpatialModel n) Q a hQ.ne'
  rw [affineTimeChangeChart, Equiv.transPartialEquiv_source]
  exact (A.symm.uniqueMDiffOn_preimage (by norm_num)).mpr
    c.source_uniqueMDiffOn

/-- **Math.** The inverse pulled-back chart is smooth on the unchanged target.
 -/
theorem affineTimeChangeChart_inv_contMDiffOn
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    ContMDiffOn
      (modelWithCornersEuclideanHalfSpace n.succ)
      ((modelWithCornersSelf ℝ (SpatialModel n)).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      (affineTimeChangeChart n c Q hQ a).symm
      (affineTimeChangeChart n c Q hQ a).target := by
  let A := affineTimeProductDiffeomorph (E := SpatialModel n) Q a hQ.ne'
  have hcomp :
      ContMDiffOn
        (modelWithCornersEuclideanHalfSpace n.succ)
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ)) ∞
        (A.toEquiv ∘ c.equiv.symm) c.equiv.target := by
    have hA : ContMDiffOn
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ)) ∞ A.toEquiv Set.univ :=
      A.contMDiff.contMDiffOn
    exact hA.comp c.inv_contMDiffOn (by simp)
  have htarget :
      (affineTimeChangeChart n c Q hQ a).target = c.equiv.target := by
    rw [affineTimeChangeChart, Equiv.transPartialEquiv_target]
  rw [htarget]
  apply hcomp.congr
  intro y hy
  have hcy : c.equiv.symm y ∈ c.equiv.source :=
    c.equiv.map_target hy
  have hcand : A.toEquiv (c.equiv.symm y) ∈
      (affineTimeChangeChart n c Q hQ a).source := by
    change A.toEquiv (c.equiv.symm y) ∈
      A.symm.toEquiv ⁻¹' c.equiv.source
    simpa using hcy
  have heval :
      (affineTimeChangeChart n c Q hQ a)
          (A.toEquiv (c.equiv.symm y)) = y := by
    simp [affineTimeChangeChart, A, hy]
  have hleft := (affineTimeChangeChart n c Q hQ a).left_inv hcand
  calc
    (affineTimeChangeChart n c Q hQ a).symm y =
        (affineTimeChangeChart n c Q hQ a).symm
          ((affineTimeChangeChart n c Q hQ a)
            (A.toEquiv (c.equiv.symm y))) := by rw [heval]
    _ = A.toEquiv (c.equiv.symm y) := hleft

/-- **Math.** Affine pullback preserves the chart target. -/
theorem affineTimeChangeChart_target
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (affineTimeChangeChart n c Q hQ a).target = c.equiv.target := by
  rw [affineTimeChangeChart, Equiv.transPartialEquiv_target]

/-- **Math.** The center remains in the pulled-back chart target. -/
theorem affineTimeChangeChart_center_mem
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    x ∈ (affineTimeChangeChart n c Q hQ a).target := by
  rw [affineTimeChangeChart_target]
  exact c.center_mem

/-- **Math.** In the pulled-back chart, the original time function is the
inverse affine coordinate: `Q * time + a = s`. -/
theorem affineTimeChangeChart_time_coordinate
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    {z : SpatialModel n × ℝ}
    (hz : z ∈ (affineTimeChangeChart n c Q hQ a).source) :
    Q * S.time ((affineTimeChangeChart n c Q hQ a) z) + a = z.2 := by
  let A := affineTimeProductDiffeomorph (E := SpatialModel n) Q a hQ.ne'
  have hz' : A.symm.toEquiv z ∈ c.equiv.source := by
    change z ∈ A.symm.toEquiv ⁻¹' c.equiv.source at hz
    exact hz
  have htime := c.time_eq (A.symm.toEquiv z) hz'
  have hzA : A.toEquiv (A.symm.toEquiv z) = z :=
    A.toEquiv.apply_symm_apply z
  change Q * S.time (c.equiv (A.symm.toEquiv z)) + a = z.2
  rw [htime]
  have hsnd := congrArg Prod.snd hzA
  have hforward_snd :
      (A.toEquiv (A.symm.toEquiv z)).2 =
        Q * (A.symm.toEquiv z).2 + a := by
    simpa [A] using congrArg Prod.snd
      (affineTimeProductDiffeomorph_apply (E := SpatialModel n)
        Q a hQ.ne' (A.symm.toEquiv z).1 (A.symm.toEquiv z).2)
  rw [hforward_snd] at hsnd
  exact hsnd

/-! The preceding coordinate identity has a differential counterpart.  It is
used to transport the adapted time-vector clause through the affine pullback.
-/

/-- **Math.** The affine pullback of an adapted chart sends the positive unit
time direction to the rescaled time vector. -/
theorem affineTimeChangeChart_timeVector_eq
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    {z : SpatialModel n × ℝ}
    (hz : z ∈ (affineTimeChangeChart n c Q hQ a).source) :
    mfderivWithin
      ((modelWithCornersSelf ℝ (SpatialModel n)).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersEuclideanHalfSpace n.succ)
      (affineTimeChangeChart n c Q hQ a)
      (affineTimeChangeChart n c Q hQ a).source z (0, 1) =
      Q⁻¹ • S.timeVector ((affineTimeChangeChart n c Q hQ a) z) := by
  let A := affineTimeProductDiffeomorph (E := SpatialModel n) Q a hQ.ne'
  let fA : SpatialModel n × ℝ → SpatialModel n × ℝ := A.symm.toEquiv
  have hy : fA z ∈ c.equiv.source := by
    change z ∈ fA ⁻¹' c.equiv.source at hz
    exact hz
  have huniq :=
    (affineTimeChangeChart_source_uniqueMDiffOn n c Q hQ a) z hz
  have hAmd :
      MDifferentiableAt
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        fA z :=
    A.symm.contMDiff.mdifferentiableAt (by norm_num)
  have hAwithin :
      mfderivWithin
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        fA
        (affineTimeChangeChart n c Q hQ a).source z =
      mfderiv
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        fA z := by
    exact mfderivWithin_eq_mfderiv huniq hAmd
  have hscalar :
      mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ)
          ((affineTimeDiffeomorph Q a hQ.ne').symm : ℝ → ℝ) z.2 =
        ContinuousLinearMap.toSpanSingleton ℝ (1 / Q) := by
    have hfun :
        ((affineTimeDiffeomorph Q a hQ.ne').symm : ℝ → ℝ) =
          (fun s : ℝ => (s - a) / Q) := by
      funext s
      have hinv :=
        (affineTimeDiffeomorph Q a hQ.ne').apply_symm_apply s
      rw [affineTimeDiffeomorph_apply] at hinv
      apply (eq_div_iff hQ.ne').2
      nlinarith [hinv]
    rw [hfun, mfderiv_eq_fderiv]
    have hderiv :
        HasDerivAt (fun s : ℝ => (s - a) / Q) (1 / Q) z.2 := by
      simpa using (hasDerivAt_id z.2).sub_const a |>.div_const Q
    exact hderiv.hasFDerivAt.fderiv
  have hAglobal :
      mfderiv
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ (SpatialModel n)).prod
          (modelWithCornersSelf ℝ ℝ))
        fA z =
      (ContinuousLinearMap.id ℝ
          (TangentSpace (𝓘(ℝ, SpatialModel n)) z.1)).prodMap
        (ContinuousLinearMap.toSpanSingleton ℝ (1 / Q)) := by
    change mfderiv
      ((modelWithCornersSelf ℝ (SpatialModel n)).prod
        (modelWithCornersSelf ℝ ℝ))
      ((modelWithCornersSelf ℝ (SpatialModel n)).prod
        (modelWithCornersSelf ℝ ℝ))
      (Prod.map id ((affineTimeDiffeomorph Q a hQ.ne').symm)) z = _
    rw [mfderiv_prodMap]
    · nth_rewrite 1 [mfderiv_id]
      nth_rewrite 1 [hscalar]
      rfl
    · exact mdifferentiableAt_id
    · exact (affineTimeDiffeomorph Q a hQ.ne').symm.contMDiff.mdifferentiableAt
        (by norm_num)
  have hAaction :
      (mfderivWithin
          ((modelWithCornersSelf ℝ (SpatialModel n)).prod
            (modelWithCornersSelf ℝ ℝ))
          ((modelWithCornersSelf ℝ (SpatialModel n)).prod
            (modelWithCornersSelf ℝ ℝ))
          fA
          (affineTimeChangeChart n c Q hQ a).source z) (0, 1) =
        (0, Q⁻¹) := by
    rw [hAwithin, hAglobal]
    have h_eval :
        ((ContinuousLinearMap.id ℝ
            (TangentSpace (𝓘(ℝ, SpatialModel n)) z.1)).prodMap
          (ContinuousLinearMap.toSpanSingleton ℝ (1 / Q))) (0, 1) =
          (0, Q⁻¹) := by
      rw [ContinuousLinearMap.prodMap, ContinuousLinearMap.prod_apply]
      simp [ContinuousLinearMap.comp_apply, one_div]
    exact h_eval
  have hcomp :=
    mfderivWithin_comp (x := z) (f := fA) (g := c.equiv)
      (s := (affineTimeChangeChart n c Q hQ a).source)
      (u := c.equiv.source)
      ((c.to_contMDiffOn (fA z) hy).mdifferentiableWithinAt (by norm_num))
      (A.symm.contMDiff.mdifferentiableWithinAt (by norm_num))
      (by
        intro q hq
        change fA q ∈ c.equiv.source
        exact hq)
      huniq
  have hcomp_eval := congrArg (fun L => L (0, 1)) hcomp
  have hcomp_eval' :
      mfderivWithin
          ((modelWithCornersSelf ℝ (SpatialModel n)).prod
            (modelWithCornersSelf ℝ ℝ))
          (modelWithCornersEuclideanHalfSpace n.succ)
          (c.equiv ∘ fA)
          (affineTimeChangeChart n c Q hQ a).source z (0, 1) =
        (mfderivWithin
            ((modelWithCornersSelf ℝ (SpatialModel n)).prod
              (modelWithCornersSelf ℝ ℝ))
            (modelWithCornersEuclideanHalfSpace n.succ)
            c.equiv c.equiv.source (fA z)).comp
          (mfderivWithin
            ((modelWithCornersSelf ℝ (SpatialModel n)).prod
              (modelWithCornersSelf ℝ ℝ))
            ((modelWithCornersSelf ℝ (SpatialModel n)).prod
              (modelWithCornersSelf ℝ ℝ))
            fA (affineTimeChangeChart n c Q hQ a).source z) (0, 1) := by
    simpa only [ContinuousLinearMap.comp_apply] using! hcomp_eval
  change mfderivWithin
      ((modelWithCornersSelf ℝ (SpatialModel n)).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersEuclideanHalfSpace n.succ)
      (c.equiv ∘ fA)
      (affineTimeChangeChart n c Q hQ a).source z (0, 1) =
      Q⁻¹ • S.timeVector (c.equiv (fA z))
  rw [hcomp_eval', ContinuousLinearMap.comp_apply, hAaction]
  have hlinear :
      (mfderivWithin
          ((modelWithCornersSelf ℝ (SpatialModel n)).prod
            (modelWithCornersSelf ℝ ℝ))
          (modelWithCornersEuclideanHalfSpace n.succ)
          c.equiv c.equiv.source (fA z)
          (show TangentSpace
              ((modelWithCornersSelf ℝ (SpatialModel n)).prod
                (modelWithCornersSelf ℝ ℝ)) (fA z) from (0, Q⁻¹))) =
        Q⁻¹ •
          (mfderivWithin
            ((modelWithCornersSelf ℝ (SpatialModel n)).prod
              (modelWithCornersSelf ℝ ℝ))
            (modelWithCornersEuclideanHalfSpace n.succ)
            c.equiv c.equiv.source (fA z)
            (show TangentSpace
                ((modelWithCornersSelf ℝ (SpatialModel n)).prod
                  (modelWithCornersSelf ℝ ℝ)) (fA z) from (0, 1))) := by
    have hmap :=
      ContinuousLinearMap.map_smul
          (mfderivWithin
          ((modelWithCornersSelf ℝ (SpatialModel n)).prod
            (modelWithCornersSelf ℝ ℝ))
          (modelWithCornersEuclideanHalfSpace n.succ)
          c.equiv c.equiv.source (fA z)) (Q⁻¹ : ℝ)
        (show TangentSpace
            ((modelWithCornersSelf ℝ (SpatialModel n)).prod
              (modelWithCornersSelf ℝ ℝ)) (fA z) from (0, 1))
    have hv :
        (Q⁻¹ : ℝ) •
            (show TangentSpace
                ((modelWithCornersSelf ℝ (SpatialModel n)).prod
                  (modelWithCornersSelf ℝ ℝ)) (fA z) from (0, 1)) =
          (show TangentSpace
              ((modelWithCornersSelf ℝ (SpatialModel n)).prod
                (modelWithCornersSelf ℝ ℝ)) (fA z) from (0, Q⁻¹)) := by
      change (Q⁻¹ : ℝ) • ((0, 1) : SpatialModel n × ℝ) = (0, Q⁻¹)
      simp [smul_eq_mul]
    rw [← hv]
    exact hmap
  rw [hlinear, c.timeVector_eq (fA z) hy]

end MorganTianLib
