import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace PetersenLib.ChartMul

open scoped Topology

/-- Differentiating a post-composition of the (fixed-second-slot) derivative slice.
For a fixed continuous linear map `T`, the derivative at `c` of
`a ↦ T (fderiv F (a, c))` in direction `u` is `T (S (inl u))`, where
`S = fderiv (fderiv F) (c,c)`. -/
private lemma slice_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E × E → E) (c : E) (S : (E × E) →L[ℝ] (E × E) →L[ℝ] E)
    (hf2 : HasFDerivAt (fderiv ℝ F) S (c, c))
    (T : ((E × E) →L[ℝ] E) →L[ℝ] G) (u : E) :
    fderiv ℝ (fun a => T (fderiv ℝ F (a, c))) c u
      = T (S (ContinuousLinearMap.inl ℝ E E u)) := by
  have hbase : HasFDerivAt (fun a : E => (a, c)) (ContinuousLinearMap.inl ℝ E E) c := by
    simpa using (hasFDerivAt_id c).prodMk (hasFDerivAt_const c c)
  have hcomp : HasFDerivAt (fun a => fderiv ℝ F (a, c))
      (S.comp (ContinuousLinearMap.inl ℝ E E)) c := by
    exact HasFDerivAt.comp c hf2 hbase
  have hT : HasFDerivAt (fun a => T (fderiv ℝ F (a, c)))
      (T.comp (S.comp (ContinuousLinearMap.inl ℝ E E))) c := by
    exact HasFDerivAt.comp c T.hasFDerivAt hcomp
  rw [hT.fderiv]
  simp [ContinuousLinearMap.comp_apply]

theorem adChart_eq_bracketChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : E → E → E) (ν : E → E) (c : E) (X U : E)
    (hμ : ContDiffAt ℝ 2 (fun p : E × E => μ p.1 p.2) (c, c))
    (hν : ContDiffAt ℝ 2 ν c)
    (hR : ∀ᶠ a in 𝓝 c, μ a c = a)
    (hL : ∀ᶠ b in 𝓝 c, μ c b = b)
    (hνc : ν c = c)
    (hinv : ∀ᶠ α in 𝓝 c, μ α (ν α) = c) :
    fderiv ℝ (fun α => fderiv ℝ (fun a => μ (μ α a) (ν α)) c X) c U
      = fderiv ℝ (fun a => fderiv ℝ (fun b => μ a b) c X) c U
        - fderiv ℝ (fun a => fderiv ℝ (fun b => μ a b) c U) c X := by
  set F : E × E → E := fun p => μ p.1 p.2 with hFdef
  set S : (E × E) →L[ℝ] (E × E) →L[ℝ] E := fderiv ℝ (fderiv ℝ F) (c, c) with hSdef
  -- Derivatives of the coordinate inclusions.
  have hInl : ∀ (q p : E), HasFDerivAt (fun z : E => (z, q)) (ContinuousLinearMap.inl ℝ E E) p :=
    fun q p => by simpa using (hasFDerivAt_id p).prodMk (hasFDerivAt_const q p)
  have hInr : ∀ (q p : E), HasFDerivAt (fun z : E => (q, z)) (ContinuousLinearMap.inr ℝ E E) p :=
    fun q p => by simpa using (hasFDerivAt_const q p).prodMk (hasFDerivAt_id p)
  -- First- and second-order regularity of `F`.
  have hFd : DifferentiableAt ℝ F (c, c) := hμ.differentiableAt (by norm_num)
  have hf2 : HasFDerivAt (fderiv ℝ F) S (c, c) :=
    ((hμ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hslice : HasFDerivAt (fun a : E => fderiv ℝ F (a, c))
      (S.comp (ContinuousLinearMap.inl ℝ E E)) c := HasFDerivAt.comp c hf2 (hInl c c)
  have hsym : ∀ v w : E × E, S v w = S w v :=
    fun v w => (hμ.isSymmSndFDerivAt (by norm_num [minSmoothness])).eq v w
  have hnear : ∀ᶠ p in 𝓝 (c, c), DifferentiableAt ℝ F p :=
    (hμ.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))
  -- Pullbacks of the neighbourhood differentiability of `F`.
  have hnearR : ∀ᶠ a in 𝓝 c, DifferentiableAt ℝ F (a, c) :=
    ((hInl c c).continuousAt).eventually hnear
  have htendφ : Filter.Tendsto (fun α : E => (α, ν α)) (𝓝 c) (𝓝 (c, c)) := by
    have h : Filter.Tendsto (fun α : E => (α, ν α)) (𝓝 c) (𝓝 (c, ν c)) :=
      continuousAt_id.prodMk hν.continuousAt
    rwa [hνc] at h
  have hnearφ : ∀ᶠ α in 𝓝 c, DifferentiableAt ℝ F (α, ν α) := htendφ.eventually hnear
  -- The two "slice = identity" facts, from the right/left unit laws.
  have hslR : fderiv ℝ (fun z : E => μ z c) c = ContinuousLinearMap.id ℝ E := by
    have h : (fun z : E => μ z c) =ᶠ[𝓝 c] id := by filter_upwards [hR] with a ha using ha
    rw [h.fderiv_eq]; exact fderiv_id
  have hslL : fderiv ℝ (fun b : E => μ c b) c = ContinuousLinearMap.id ℝ E := by
    have h : (fun b : E => μ c b) =ᶠ[𝓝 c] id := by filter_upwards [hL] with b hb using hb
    rw [h.fderiv_eq]; exact fderiv_id
  -- The two first-order partial derivatives of `F` at `(c,c)` are the identity.
  have hP1 : ∀ u : E, fderiv ℝ F (c, c) (ContinuousLinearMap.inl ℝ E E u) = u := by
    intro u
    have hHF : HasFDerivAt (fun z : E => μ z c)
        ((fderiv ℝ F (c, c)).comp (ContinuousLinearMap.inl ℝ E E)) c :=
      HasFDerivAt.comp (f := fun z : E => (z, c)) c hFd.hasFDerivAt (hInl c c)
    have e : fderiv ℝ (fun z : E => μ z c) c
        = (fderiv ℝ F (c, c)).comp (ContinuousLinearMap.inl ℝ E E) := hHF.fderiv
    rw [hslR] at e
    have := congrArg (fun L : E →L[ℝ] E => L u) e.symm
    simpa [ContinuousLinearMap.comp_apply] using this
  have hP2 : ∀ w : E, fderiv ℝ F (c, c) (ContinuousLinearMap.inr ℝ E E w) = w := by
    intro w
    have hHF : HasFDerivAt (fun b : E => μ c b)
        ((fderiv ℝ F (c, c)).comp (ContinuousLinearMap.inr ℝ E E)) c :=
      HasFDerivAt.comp c hFd.hasFDerivAt (hInr c c)
    have e : fderiv ℝ (fun b : E => μ c b) c
        = (fderiv ℝ F (c, c)).comp (ContinuousLinearMap.inr ℝ E E) := hHF.fderiv
    rw [hslL] at e
    have := congrArg (fun L : E →L[ℝ] E => L w) e.symm
    simpa [ContinuousLinearMap.comp_apply] using this
  -- Differential of the inverse map: `Dν(c) = -id`.
  have hDν : ∀ u : E, fderiv ℝ ν c u = -u := by
    have hconst : fderiv ℝ (fun α : E => μ α (ν α)) c = 0 := by
      have h : (fun α : E => μ α (ν α)) =ᶠ[𝓝 c] (fun _ => c) := by
        filter_upwards [hinv] with a ha using ha
      rw [h.fderiv_eq]; simp
    have hφ : HasFDerivAt (fun α : E => (α, ν α))
        ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ν c)) c :=
      (hasFDerivAt_id c).prodMk (hν.differentiableAt (by norm_num)).hasFDerivAt
    have hFdφ : HasFDerivAt F (fderiv ℝ F (c, c)) (c, ν c) := by rw [hνc]; exact hFd.hasFDerivAt
    have hHF : HasFDerivAt (fun α : E => μ α (ν α))
        ((fderiv ℝ F (c, c)).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ν c))) c :=
      HasFDerivAt.comp (f := fun α : E => (α, ν α)) c hFdφ hφ
    have hchain : fderiv ℝ (fun α : E => μ α (ν α)) c
        = (fderiv ℝ F (c, c)).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ν c)) :=
      hHF.fderiv
    intro u
    have hzero : (fderiv ℝ F (c, c)) (u, fderiv ℝ ν c u) = 0 := by
      have h0 : (fderiv ℝ F (c, c)).comp
          ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ν c)) = 0 := by rw [← hchain, hconst]
      have := congrArg (fun L : E →L[ℝ] E => L u) h0
      simpa [ContinuousLinearMap.comp_apply] using this
    have hsplit : (fderiv ℝ F (c, c)) (u, fderiv ℝ ν c u) = u + fderiv ℝ ν c u := by
      have hpair : ((u : E), fderiv ℝ ν c u)
          = ContinuousLinearMap.inl ℝ E E u
            + ContinuousLinearMap.inr ℝ E E (fderiv ℝ ν c u) := by simp
      rw [hpair, map_add, hP1, hP2]
    rw [hsplit] at hzero
    exact (neg_eq_of_add_eq_zero_right hzero).symm
  -- The `P`-bridge (as a `HasFDerivAt`): differentiating the right-invariant field.
  have hPBhas : ∀ Z : E, HasFDerivAt (fun α => fderiv ℝ (fun b => μ α b) c Z)
      ((ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inr ℝ E E Z)).comp
        (S.comp (ContinuousLinearMap.inl ℝ E E))) c := by
    intro Z
    have heq : (fun α : E => (ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inr ℝ E E Z))
          (fderiv ℝ F (α, c)))
        =ᶠ[𝓝 c] (fun α => fderiv ℝ (fun b => μ α b) c Z) := by
      filter_upwards [hnearR] with a ha
      have hHF : HasFDerivAt (fun b : E => μ a b)
          ((fderiv ℝ F (a, c)).comp (ContinuousLinearMap.inr ℝ E E)) c :=
        HasFDerivAt.comp c ha.hasFDerivAt (hInr a c)
      have hd : fderiv ℝ (fun b : E => μ a b) c
          = (fderiv ℝ F (a, c)).comp (ContinuousLinearMap.inr ℝ E E) := hHF.fderiv
      show (ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inr ℝ E E Z)) (fderiv ℝ F (a, c))
          = fderiv ℝ (fun b => μ a b) c Z
      rw [hd, ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply]
    have hbase : HasFDerivAt (fun α : E =>
        (ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inr ℝ E E Z)) (fderiv ℝ F (α, c)))
        ((ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inr ℝ E E Z)).comp
          (S.comp (ContinuousLinearMap.inl ℝ E E))) c :=
      HasFDerivAt.comp c (ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inr ℝ E E Z)).hasFDerivAt
        hslice
    exact hbase.congr_of_eventuallyEq heq.symm
  -- Vanishing of the `(inl, inl)` second derivative (from the right unit law).
  have hPP : ∀ u x : E,
      S (ContinuousLinearMap.inl ℝ E E u) (ContinuousLinearMap.inl ℝ E E x) = 0 := by
    intro u x
    have hev : (fun a : E => (ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inl ℝ E E x))
          (fderiv ℝ F (a, c)))
        =ᶠ[𝓝 c] (fun _ => x) := by
      filter_upwards [hnearR, hR.eventually_nhds] with a ha hnb
      have hHF : HasFDerivAt (fun z : E => μ z c)
          ((fderiv ℝ F (a, c)).comp (ContinuousLinearMap.inl ℝ E E)) a :=
        HasFDerivAt.comp (f := fun z : E => (z, c)) a ha.hasFDerivAt (hInl c a)
      have hd : fderiv ℝ (fun z : E => μ z c) a
          = (fderiv ℝ F (a, c)).comp (ContinuousLinearMap.inl ℝ E E) := hHF.fderiv
      have hid : fderiv ℝ (fun z : E => μ z c) a = ContinuousLinearMap.id ℝ E := by
        have h : (fun z : E => μ z c) =ᶠ[𝓝 a] id := by filter_upwards [hnb] with z hz using hz
        rw [h.fderiv_eq]; exact fderiv_id
      rw [hd] at hid
      show (ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inl ℝ E E x)) (fderiv ℝ F (a, c)) = x
      rw [ContinuousLinearMap.apply_apply, ← ContinuousLinearMap.comp_apply, hid,
        ContinuousLinearMap.id_apply]
    have hsl := slice_first F c S hf2
      (ContinuousLinearMap.apply ℝ E (ContinuousLinearMap.inl ℝ E E x)) u
    rw [hev.fderiv_eq] at hsl
    simpa [ContinuousLinearMap.apply_apply] using hsl.symm
  -- The post-composition operator `Ψ : L ↦ L ∘ inl`.
  set Ψ : ((E × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E × E) E).flip (ContinuousLinearMap.inl ℝ E E) with hΨdef
  have hΨ : ∀ g : (E × E) →L[ℝ] E, Ψ g = g.comp (ContinuousLinearMap.inl ℝ E E) := by
    intro g; simp [hΨdef, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  -- The `Q`-field `α ↦ D₁(α, ν α)` is differentiable, with computable derivative.
  have hφ : HasFDerivAt (fun α : E => (α, ν α))
      ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ν c)) c :=
    (hasFDerivAt_id c).prodMk (hν.differentiableAt (by norm_num)).hasFDerivAt
  have hQhas : HasFDerivAt (fun α => fderiv ℝ (fun z => μ z (ν α)) α)
      ((Ψ.comp S).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ν c))) c := by
    have hW : HasFDerivAt (fun p : E × E => Ψ (fderiv ℝ F p)) (Ψ.comp S) (c, ν c) := by
      rw [hνc]; exact HasFDerivAt.comp (c, c) Ψ.hasFDerivAt hf2
    have hcomp : HasFDerivAt (fun α : E => Ψ (fderiv ℝ F (α, ν α)))
        ((Ψ.comp S).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ν c))) c :=
      HasFDerivAt.comp (f := fun α : E => (α, ν α)) c hW hφ
    have heqQ : (fun α : E => Ψ (fderiv ℝ F (α, ν α)))
        =ᶠ[𝓝 c] (fun α => fderiv ℝ (fun z => μ z (ν α)) α) := by
      filter_upwards [hnearφ] with a ha
      have hHF : HasFDerivAt (fun z : E => μ z (ν a))
          ((fderiv ℝ F (a, ν a)).comp (ContinuousLinearMap.inl ℝ E E)) a :=
        HasFDerivAt.comp (f := fun z : E => (z, ν a)) a ha.hasFDerivAt (hInl (ν a) a)
      have hd : fderiv ℝ (fun z : E => μ z (ν a)) a
          = (fderiv ℝ F (a, ν a)).comp (ContinuousLinearMap.inl ℝ E E) := hHF.fderiv
      rw [hd, hΨ]
    exact hcomp.congr_of_eventuallyEq heqQ.symm
  -- Values at the base point.
  have hQcid : fderiv ℝ (fun z => μ z (ν c)) c = ContinuousLinearMap.id ℝ E := by
    rw [hνc]; exact hslR
  have hRcX : fderiv ℝ (fun b => μ c b) c X = X := by
    rw [hslL, ContinuousLinearMap.id_apply]
  -- Rewrite the right-hand side of the goal.
  have hrhs1 : fderiv ℝ (fun a => fderiv ℝ (fun b => μ a b) c X) c U
      = S (ContinuousLinearMap.inl ℝ E E U) (ContinuousLinearMap.inr ℝ E E X) := by
    rw [(hPBhas X).fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have hrhs2 : fderiv ℝ (fun a => fderiv ℝ (fun b => μ a b) c U) c X
      = S (ContinuousLinearMap.inl ℝ E E X) (ContinuousLinearMap.inr ℝ E E U) := by
    rw [(hPBhas U).fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  -- The left-hand side, expanded via the chain rule.
  have hA : (fun α => fderiv ℝ (fun a => μ (μ α a) (ν α)) c X)
      =ᶠ[𝓝 c] (fun α => (fderiv ℝ (fun z => μ z (ν α)) α)
        (fderiv ℝ (fun b => μ α b) c X)) := by
    filter_upwards [hnearR, hnearφ, hR] with α hα1 hα2 hα3
    have hgd : HasFDerivAt (fun a => μ α a)
        ((fderiv ℝ F (α, c)).comp (ContinuousLinearMap.inr ℝ E E)) c :=
      HasFDerivAt.comp c hα1.hasFDerivAt (hInr α c)
    have hg : HasFDerivAt (fun a => μ α a) (fderiv ℝ (fun a => μ α a) c) c :=
      hgd.differentiableAt.hasFDerivAt
    have hkd : HasFDerivAt (fun z => μ z (ν α))
        ((fderiv ℝ F (α, ν α)).comp (ContinuousLinearMap.inl ℝ E E)) α :=
      HasFDerivAt.comp (f := fun z : E => (z, ν α)) α hα2.hasFDerivAt (hInl (ν α) α)
    have hk : HasFDerivAt (fun z => μ z (ν α)) (fderiv ℝ (fun z => μ z (ν α)) α) α :=
      hkd.differentiableAt.hasFDerivAt
    have hkc : HasFDerivAt (fun z => μ z (ν α)) (fderiv ℝ (fun z => μ z (ν α)) α) (μ α c) := by
      rw [hα3]; exact hk
    have hHF : HasFDerivAt (fun a => μ (μ α a) (ν α))
        ((fderiv ℝ (fun z => μ z (ν α)) α).comp (fderiv ℝ (fun a => μ α a) c)) c :=
      HasFDerivAt.comp c hkc hg
    have hAα : fderiv ℝ (fun a => μ (μ α a) (ν α)) c
        = (fderiv ℝ (fun z => μ z (ν α)) α).comp (fderiv ℝ (fun a => μ α a) c) :=
      hHF.fderiv
    show fderiv ℝ (fun a => μ (μ α a) (ν α)) c X
        = (fderiv ℝ (fun z => μ z (ν α)) α) (fderiv ℝ (fun b => μ α b) c X)
    rw [hAα, ContinuousLinearMap.comp_apply]
  -- The key symmetry/antisymmetry consequence.
  have hkey : S (((U : E), -U) : E × E) (ContinuousLinearMap.inl ℝ E E X)
      = - S (ContinuousLinearMap.inl ℝ E E X) (ContinuousLinearMap.inr ℝ E E U) := by
    have hp : (((U : E), -U) : E × E)
        = ContinuousLinearMap.inl ℝ E E U - ContinuousLinearMap.inr ℝ E E U := by simp
    rw [hp, map_sub, ContinuousLinearMap.sub_apply, hPP U X,
      hsym (ContinuousLinearMap.inr ℝ E E U) (ContinuousLinearMap.inl ℝ E E X)]
    abel
  -- Assemble.
  rw [hrhs1, hrhs2, hA.fderiv_eq, (hQhas.clm_apply (hPBhas X)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply, hΨ,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, hQcid, hRcX, hDν]
  rw [hkey]
  abel
