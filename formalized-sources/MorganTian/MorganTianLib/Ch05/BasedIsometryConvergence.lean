import MorganTianLib.Ch05.UnboundedAssembly

/-!
# Morgan--Tian Chapter 5: convergence adapters from based isometries

These elementary adapters package the exact zero-distance argument needed when
a compact-limit construction has already produced a basepoint-preserving
isometry.  The bounded statement supplies the uniform diameter witness, and the
unbounded statement applies it radius by radius to the canonical ball models.
No compactness or smoothness is inferred by these bridges.
-/

open Set Filter Topology
open scoped Topology

namespace MorganTianLib

universe u

/-! ## Bounded models -/

/-- **Math.** A sequence of finite-diameter based metric spaces which is
pointwise based-isometric to a fixed target converges to that target in the
bounded pointed Gromov--Hausdorff interface. -/
theorem pointedGHConverges_of_basedIsometry_sequence
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (e : ∀ k, (X k).carrier ≃ᵢ Y.carrier)
    (hbase : ∀ k, e k (X k).base = Y.base) :
    PointedGHConverges X Y := by
  obtain ⟨C, hC⟩ := Y.finite_diameter
  refine ⟨⟨C, ?_⟩, ?_⟩
  · intro k p q
    rw [← (e k).dist_eq p q]
    exact hC (e k p) (e k q)
  · have hzero : ∀ k, pointedGHDistance (X k) Y = 0 := by
      intro k
      exact pointedGHDistance_eq_zero_of_basedIsometry
        (X k) Y (e k) (hbase k)
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    simpa [hzero] using hconst

/-! ## Unbounded models -/

/-- **Math.** The restriction of a based isometry to equal-radius open balls is
again a based isometry.  Keeping this as a local construction makes the
radius-wise unbounded adapter below independent of any choice of ambient
realization. -/
private noncomputable def ballModelBasedIsometry
    {X Y : BasedMetricSpaceBundle.{u}}
    (e : X.carrier ≃ᵢ Y.carrier)
    (hbase : e X.base = Y.base)
    (r : ℝ) (hr : 0 < r) :
    (ballModel X r hr).carrier ≃ᵢ (ballModel Y r hr).carrier := by
  let f : (ballModel X r hr).carrier → (ballModel Y r hr).carrier :=
    fun p => ⟨e p.1, by
      change dist (e p.1) Y.base < r
      rw [← hbase, e.dist_eq]
      exact p.2⟩
  let g : (ballModel Y r hr).carrier → (ballModel X r hr).carrier :=
    fun q => ⟨e.symm q.1, by
      change dist (e.symm q.1) X.base < r
      calc
        dist (e.symm q.1) X.base =
            dist (e.symm q.1) (e.symm (e X.base)) := by
              rw [e.symm_apply_apply]
        _ = dist q.1 (e X.base) := (e.symm.dist_eq _ _)
        _ = dist q.1 Y.base := by rw [hbase]
        _ < r := q.2⟩
  have hfg : Function.LeftInverse g f := by
    intro p
    apply Subtype.ext
    simp [f, g]
  have hgf : Function.RightInverse g f := by
    intro q
    apply Subtype.ext
    simp [f, g]
  let E : (ballModel X r hr).carrier ≃ (ballModel Y r hr).carrier :=
    Equiv.ofBijective f ⟨(Function.LeftInverse.injective hfg),
      (Function.RightInverse.surjective hgf)⟩
  exact
    { toEquiv := E
      isometry_toFun := Isometry.of_dist_eq (by
        intro p q
        change dist (e p.1) (e q.1) = dist p.1 q.1
        exact e.dist_eq p.1 q.1) }

/-- **Math.** A sequence of based metric-space bundles that is pointwise
based-isometric to a fixed target satisfies the unbounded pointed
Gromov--Hausdorff convergence predicate.  The witnesses use the constant
zero radius perturbation, while each bounded ball is identified by the
restricted isometry. -/
theorem pointedGHConvergesUnbounded_of_basedIsometry_sequence
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u})
    (e : ∀ k, (X k).carrier ≃ᵢ Y.carrier)
    (hbase : ∀ k, e k (X k).base = Y.base) :
    PointedGHConvergesUnbounded X Y := by
  intro r hr
  let δ : ℕ → ℝ := fun _ => 0
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hpos : ∀ k, 0 < r + δ k := by
    intro k
    simpa [δ] using hr
  refine ⟨δ, hδ, hpos, ?_⟩
  have hconv :
      PointedGHConverges
        (fun k => ballModel (X k) r hr)
        (ballModel Y r hr) := by
    apply pointedGHConverges_of_basedIsometry_sequence
      (fun k => ballModel (X k) r hr)
      (ballModel Y r hr)
      (fun k => ballModelBasedIsometry (e k) (hbase k) r hr)
      (fun k => by
        apply Subtype.ext
        change e k (X k).base = Y.base
        exact hbase k)
  simpa [δ] using hconv

end MorganTianLib

#print axioms MorganTianLib.pointedGHConverges_of_basedIsometry_sequence
#print axioms MorganTianLib.pointedGHConvergesUnbounded_of_basedIsometry_sequence
