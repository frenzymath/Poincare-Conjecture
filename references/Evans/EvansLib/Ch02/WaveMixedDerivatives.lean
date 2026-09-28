import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Commuting iterated derivatives of smooth space-time slices

This file packages the finite-smooth Schwarz argument needed for Evans's
odd-dimensional wave transform.  Unlike the analytic permutation theorem for
`iteratedFDeriv`, the result below assumes only `C^∞` smoothness.
-/

open scoped ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

private def waveMixedDirDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E) (f : E → F) : E → F :=
  fun x => fderiv ℝ f x v

private def waveMixedDirIter {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E) : ℕ → (E → F) → E → F
  | 0, f => f
  | m + 1, f => waveMixedDirDeriv v (waveMixedDirIter v m f)

private lemma waveMixed_fderiv_fderiv_apply' {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hfd : DifferentiableAt ℝ (fderiv ℝ f) x) (w v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v =
      fderiv ℝ (fderiv ℝ f) x v w := by
  rw [fderiv_clm_apply hfd (differentiableAt_const w)]
  simp

private lemma waveMixedDirDeriv_contDiff_infty {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (waveMixedDirDeriv v f) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private lemma waveMixedDirIter_contDiff_infty {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (v : E) (m : ℕ) :
    ContDiff ℝ ∞ (waveMixedDirIter v m f) := by
  induction m with
  | zero => exact hf
  | succ m ih => exact waveMixedDirDeriv_contDiff_infty ih v

private lemma waveMixedDirDeriv_contDiff_of_order {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {q : ℕ} (hf : ContDiff ℝ (q + 1 : ℕ) f) (v : E) :
    ContDiff ℝ q (waveMixedDirDeriv v f) := by
  exact (hf.fderiv_right (m := q) (by norm_num)).clm_apply contDiff_const

/-- Taking `a` fixed directional derivatives consumes exactly `a` of the
available finite differentiability order. -/
private lemma waveMixedDirIter_contDiff_of_order {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {a q : ℕ} (hf : ContDiff ℝ (a + q : ℕ) f) (v : E) :
    ContDiff ℝ q (waveMixedDirIter v a f) := by
  induction a generalizing q with
  | zero => simpa [waveMixedDirIter] using hf
  | succ a ih =>
      rw [waveMixedDirIter]
      apply waveMixedDirDeriv_contDiff_of_order
      apply ih (q := q + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf

private lemma waveMixedDirDeriv_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (v w : E) :
    waveMixedDirDeriv v (waveMixedDirDeriv w f) = waveMixedDirDeriv w (waveMixedDirDeriv v f) := by
  funext x
  have htwo : (2 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) htwo).differentiable (by norm_num) x
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact htwo)
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f y v) x w
  rw [waveMixed_fderiv_fderiv_apply' hfd w v, waveMixed_fderiv_fderiv_apply' hfd v w]
  exact hsymm v w

private lemma waveMixedDirDeriv_comm_of_order {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ 2 f) (v w : E) :
    waveMixedDirDeriv v (waveMixedDirDeriv w f) =
      waveMixedDirDeriv w (waveMixedDirDeriv v f) := by
  funext x
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by norm_num)
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f y v) x w
  rw [waveMixed_fderiv_fderiv_apply' hfd w v,
    waveMixed_fderiv_fderiv_apply' hfd v w]
  exact hsymm v w

private lemma waveMixedDirDeriv_waveMixedDirIter_comm_of_order {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {a : ℕ} (hf : ContDiff ℝ (a + 1 : ℕ) f) (v w : E) :
    waveMixedDirDeriv v (waveMixedDirIter w a f) =
      waveMixedDirIter w a (waveMixedDirDeriv v f) := by
  induction a generalizing f with
  | zero => rfl
  | succ a ih =>
      rw [waveMixedDirIter, waveMixedDirIter]
      have hinner : ContDiff ℝ 2 (waveMixedDirIter w a f) := by
        apply waveMixedDirIter_contDiff_of_order (a := a) (q := 2) _ w
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
      rw [waveMixedDirDeriv_comm_of_order hinner]
      rw [ih (hf.of_le (by exact_mod_cast
        (show a + 1 ≤ a + 1 + 1 by omega)))]

private lemma waveMixedDirIter_comm_of_order {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {a b : ℕ} (hf : ContDiff ℝ (a + b : ℕ) f) (v w : E) :
    waveMixedDirIter v a (waveMixedDirIter w b f) =
      waveMixedDirIter w b (waveMixedDirIter v a f) := by
  induction a generalizing f with
  | zero => rfl
  | succ a ih =>
      rw [waveMixedDirIter, waveMixedDirIter]
      have hf' : ContDiff ℝ (a + b : ℕ) f :=
        hf.of_le (by exact_mod_cast (show a + b ≤ a + 1 + b by omega))
      rw [ih hf']
      have hinner : ContDiff ℝ (b + 1 : ℕ) (waveMixedDirIter v a f) := by
        apply waveMixedDirIter_contDiff_of_order (a := a) (q := b + 1) _ v
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
      rw [waveMixedDirDeriv_waveMixedDirIter_comm_of_order hinner]

private lemma waveMixedDirIter_two_eq_iteratedFDeriv_of_order
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 2 f) (v x : E) :
    waveMixedDirIter v 2 f x = iteratedFDeriv ℝ 2 f x ![v, v] := by
  change fderiv ℝ (fun y => fderiv ℝ f y v) x v = _
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [waveMixed_fderiv_fderiv_apply' hfd v v]
  simp [iteratedFDeriv_two_apply]

private lemma waveMixedDirIter_prod_fst_two_eq_iteratedFDeriv_of_order
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ 2 f)
    (v x : E) (t : ℝ) :
    waveMixedDirIter (v, (0 : ℝ)) 2 f (x, t) =
      iteratedFDeriv ℝ 2 (fun y => f (y, t)) x ![v, v] := by
  let a : E × ℝ := (0, t)
  let L : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  have hslice : iteratedFDeriv ℝ 2 (fun y => f (y, t)) x =
      (iteratedFDeriv ℝ 2 f (x, t)).compContinuousLinearMap
        (fun _ : Fin 2 => L) := by
    have hfun : (fun y => f (y, t)) = (fun z => f (a + z)) ∘ L := by
      funext y
      simp [a, L]
    have htrans : ContDiff ℝ 2 (fun z => f (a + z)) :=
      hf.comp (contDiff_const.add contDiff_id)
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L htrans x
      (by norm_num)]
    rw [iteratedFDeriv_comp_add_left]
    simp [a, L]
  rw [waveMixedDirIter_two_eq_iteratedFDeriv_of_order hf (v, (0 : ℝ)) (x, t)]
  have happ := congrArg
    (fun T => T ![v, v]) hslice
  have harr : (fun i : Fin 2 => (![v, v] i, (0 : ℝ))) =
      ![(v, (0 : ℝ)), (v, (0 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at happ
  change (iteratedFDeriv ℝ 2 (fun y => f (y, t)) x) ![v, v] =
    (iteratedFDeriv ℝ 2 f (x, t))
      (fun i => (![v, v] i, (0 : ℝ))) at happ
  rw [harr] at happ
  exact happ.symm

private lemma waveMixedDirDeriv_waveMixedDirIter_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (v w : E) (m : ℕ) :
    waveMixedDirDeriv v (waveMixedDirIter w m f) = waveMixedDirIter w m (waveMixedDirDeriv v f) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
      rw [waveMixedDirIter, waveMixedDirIter]
      rw [waveMixedDirDeriv_comm (waveMixedDirIter_contDiff_infty hf w m)]
      rw [ih hf]

private lemma waveMixedDirIter_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (v w : E) (a b : ℕ) :
    waveMixedDirIter v a (waveMixedDirIter w b f) = waveMixedDirIter w b (waveMixedDirIter v a f) := by
  induction a generalizing f with
  | zero => rfl
  | succ a ih =>
      rw [waveMixedDirIter, waveMixedDirIter]
      rw [ih hf]
      rw [waveMixedDirDeriv_waveMixedDirIter_comm (waveMixedDirIter_contDiff_infty hf v a)]

private lemma waveMixedDirDeriv_fst_eq_deriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {r t : ℝ} (hf : DifferentiableAt ℝ f (r, t)) :
    waveMixedDirDeriv ((1 : ℝ), (0 : ℝ)) f (r, t) =
      deriv (fun s => f (s, t)) r := by
  symm
  have hcurve : HasDerivAt (fun s : ℝ => (s, t)) (1, 0) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r t)
  exact (hf.hasFDerivAt.comp_hasDerivAt r hcurve).deriv

private lemma waveMixedDirDeriv_snd_eq_deriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {r t : ℝ} (hf : DifferentiableAt ℝ f (r, t)) :
    waveMixedDirDeriv ((0 : ℝ), (1 : ℝ)) f (r, t) =
      deriv (fun s => f (r, s)) t := by
  symm
  have hcurve : HasDerivAt (fun s : ℝ => (r, s)) (0, 1) t :=
    (hasDerivAt_const t r).prodMk (hasDerivAt_id t)
  exact (hf.hasFDerivAt.comp_hasDerivAt t hcurve).deriv

private lemma waveMixedDirIter_fst_eq_iteratedDeriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (r t : ℝ) :
    waveMixedDirIter ((1 : ℝ), (0 : ℝ)) m f (r, t) =
      iteratedDeriv m (fun s => f (s, t)) r := by
  induction m generalizing r t with
  | zero => rfl
  | succ m ih =>
      rw [waveMixedDirIter]
      rw [waveMixedDirDeriv_fst_eq_deriv
        ((waveMixedDirIter_contDiff_infty hf ((1 : ℝ), (0 : ℝ)) m).differentiable
          (by simp) (r, t))]
      rw [iteratedDeriv_succ]
      congr 1
      funext s
      exact ih s t

/-- Finite-order form of the identification between repeated differentiation
in the first coordinate and an ordinary iterated derivative of the slice. -/
private lemma waveMixedDirIter_fst_eq_iteratedDeriv_of_order {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {m : ℕ} (hf : ContDiff ℝ m f) (r t : ℝ) :
    waveMixedDirIter ((1 : ℝ), (0 : ℝ)) m f (r, t) =
      iteratedDeriv m (fun s => f (s, t)) r := by
  induction m generalizing r t with
  | zero => rfl
  | succ m ih =>
      rw [waveMixedDirIter]
      have hiter : ContDiff ℝ 1
          (waveMixedDirIter ((1 : ℝ), (0 : ℝ)) m f) := by
        apply waveMixedDirIter_contDiff_of_order (a := m) (q := 1) _
          ((1 : ℝ), (0 : ℝ))
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf
      rw [waveMixedDirDeriv_fst_eq_deriv
        (hiter.differentiable (by norm_num) (r, t))]
      rw [iteratedDeriv_succ]
      congr 1
      funext s
      exact ih (hf.of_le (by exact_mod_cast
        (show m ≤ m + 1 by omega))) s t

/-- Finite-order form of the identification between repeated differentiation
in the second coordinate and an ordinary iterated derivative of the slice. -/
private lemma waveMixedDirIter_snd_eq_iteratedDeriv_of_order {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {m : ℕ} (hf : ContDiff ℝ m f) (r t : ℝ) :
    waveMixedDirIter ((0 : ℝ), (1 : ℝ)) m f (r, t) =
      iteratedDeriv m (fun s => f (r, s)) t := by
  induction m generalizing r t with
  | zero => rfl
  | succ m ih =>
      rw [waveMixedDirIter]
      have hiter : ContDiff ℝ 1
          (waveMixedDirIter ((0 : ℝ), (1 : ℝ)) m f) := by
        apply waveMixedDirIter_contDiff_of_order (a := m) (q := 1) _
          ((0 : ℝ), (1 : ℝ))
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf
      rw [waveMixedDirDeriv_snd_eq_deriv
        (hiter.differentiable (by norm_num) (r, t))]
      rw [iteratedDeriv_succ]
      congr 1
      funext s
      exact ih (hf.of_le (by exact_mod_cast
        (show m ≤ m + 1 by omega))) r s

private lemma waveMixedDirIter_snd_eq_iteratedDeriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (r t : ℝ) :
    waveMixedDirIter ((0 : ℝ), (1 : ℝ)) m f (r, t) =
      iteratedDeriv m (fun s => f (r, s)) t := by
  induction m generalizing r t with
  | zero => rfl
  | succ m ih =>
      rw [waveMixedDirIter]
      rw [waveMixedDirDeriv_snd_eq_deriv
        ((waveMixedDirIter_contDiff_infty hf ((0 : ℝ), (1 : ℝ)) m).differentiable
          (by simp) (r, t))]
      rw [iteratedDeriv_succ]
      congr 1
      funext s
      exact ih r s

/-- Taking a fixed-order derivative in the first coordinate of a jointly smooth
function leaves a smooth function of the second coordinate. -/
theorem contDiff_iteratedDeriv_fst_slice {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (fun t => iteratedDeriv m (fun s => f (s, t)) r) := by
  have hdir := waveMixedDirIter_contDiff_infty hf ((1 : ℝ), (0 : ℝ)) m
  have heq : (fun t => iteratedDeriv m (fun s => f (s, t)) r) =
      fun t => waveMixedDirIter ((1 : ℝ), (0 : ℝ)) m f (r, t) := by
    funext t
    exact (waveMixedDirIter_fst_eq_iteratedDeriv hf m r t).symm
  rw [heq]
  exact hdir.comp (contDiff_const.prodMk contDiff_id)

/-- Taking `m` derivatives in the first coordinate of a `C^(m+q)` function
leaves a `C^q` function of the second coordinate. -/
theorem contDiff_iteratedDeriv_fst_slice_of_order {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {m q : ℕ} (hf : ContDiff ℝ (m + q : ℕ) f)
    (r : ℝ) :
    ContDiff ℝ q (fun t => iteratedDeriv m (fun s => f (s, t)) r) := by
  have hdir : ContDiff ℝ q
      (waveMixedDirIter ((1 : ℝ), (0 : ℝ)) m f) := by
    exact waveMixedDirIter_contDiff_of_order hf ((1 : ℝ), (0 : ℝ))
  have heq : (fun t => iteratedDeriv m (fun s => f (s, t)) r) =
      fun t => waveMixedDirIter ((1 : ℝ), (0 : ℝ)) m f (r, t) := by
    funext t
    exact (waveMixedDirIter_fst_eq_iteratedDeriv_of_order
      (hf.of_le (by exact_mod_cast (show m ≤ m + q by omega))) r t).symm
  rw [heq]
  exact hdir.comp (contDiff_const.prodMk contDiff_id)

/-- Taking a fixed-order time derivative of a jointly smooth function leaves a
smooth function of the spatial slice variable. -/
theorem contDiff_iteratedDeriv_snd_slice {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (fun s => iteratedDeriv m (fun tau => f (s, tau)) t) := by
  have hdir := waveMixedDirIter_contDiff_infty hf ((0 : ℝ), (1 : ℝ)) m
  have heq : (fun s => iteratedDeriv m (fun tau => f (s, tau)) t) =
      fun s => waveMixedDirIter ((0 : ℝ), (1 : ℝ)) m f (s, t) := by
    funext s
    exact (waveMixedDirIter_snd_eq_iteratedDeriv hf m s t).symm
  rw [heq]
  exact hdir.comp (contDiff_id.prodMk contDiff_const)

/-- Taking `m` derivatives in the second coordinate of a `C^(q+m)` function
leaves a `C^q` function of the first coordinate. -/
theorem contDiff_iteratedDeriv_snd_slice_of_order {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {m q : ℕ} (hf : ContDiff ℝ (q + m : ℕ) f)
    (t : ℝ) :
    ContDiff ℝ q (fun s => iteratedDeriv m (fun tau => f (s, tau)) t) := by
  have hdir : ContDiff ℝ q
      (waveMixedDirIter ((0 : ℝ), (1 : ℝ)) m f) := by
    apply waveMixedDirIter_contDiff_of_order (a := m) (q := q) _
      ((0 : ℝ), (1 : ℝ))
    simpa [Nat.add_comm] using hf
  have heq : (fun s => iteratedDeriv m (fun tau => f (s, tau)) t) =
      fun s => waveMixedDirIter ((0 : ℝ), (1 : ℝ)) m f (s, t) := by
    funext s
    exact (waveMixedDirIter_snd_eq_iteratedDeriv_of_order
      (hf.of_le (by exact_mod_cast (show m ≤ q + m by omega))) s t).symm
  rw [heq]
  exact hdir.comp (contDiff_id.prodMk contDiff_const)

/-- The first ordinary derivative of a time slice is the first Fréchet
derivative evaluated in the time direction. -/
theorem iteratedDeriv_snd_one_eq_iteratedFDeriv_of_order {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ 1 f) (r t : ℝ) :
    iteratedDeriv 1 (fun tau => f (r, tau)) t =
      iteratedFDeriv ℝ 1 f (r, t) ![((0 : ℝ), (1 : ℝ))] := by
  rw [iteratedDeriv_one]
  rw [← waveMixedDirDeriv_snd_eq_deriv
    (hf.differentiable (by norm_num) (r, t))]
  simp [waveMixedDirDeriv, iteratedFDeriv_one_apply]

/-- Smooth specialization of
`iteratedDeriv_snd_one_eq_iteratedFDeriv_of_order`. -/
theorem iteratedDeriv_snd_one_eq_iteratedFDeriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (r t : ℝ) :
    iteratedDeriv 1 (fun tau => f (r, tau)) t =
      iteratedFDeriv ℝ 1 f (r, t) ![((0 : ℝ), (1 : ℝ))] := by
  rw [iteratedDeriv_one]
  rw [← waveMixedDirDeriv_snd_eq_deriv (hf.differentiable (by simp) (r, t))]
  simp [waveMixedDirDeriv, iteratedFDeriv_one_apply]

/-- The second ordinary derivative of a time slice is the second Fréchet
derivative evaluated twice in the time direction. -/
theorem iteratedDeriv_snd_two_eq_iteratedFDeriv_of_order {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ 2 f) (r t : ℝ) :
    iteratedDeriv 2 (fun tau => f (r, tau)) t =
      iteratedFDeriv ℝ 2 f (r, t)
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] := by
  rw [← waveMixedDirIter_snd_eq_iteratedDeriv_of_order hf r t]
  change fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) (r, t) (0, 1) = _
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (r, t) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (r, t)
  rw [waveMixed_fderiv_fderiv_apply' hfd (0, 1) (0, 1)]
  simp [iteratedFDeriv_two_apply]

/-- Smooth specialization of
`iteratedDeriv_snd_two_eq_iteratedFDeriv_of_order`. -/
theorem iteratedDeriv_snd_two_eq_iteratedFDeriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (r t : ℝ) :
    iteratedDeriv 2 (fun tau => f (r, tau)) t =
      iteratedFDeriv ℝ 2 f (r, t)
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] := by
  rw [← waveMixedDirIter_snd_eq_iteratedDeriv hf 2 r t]
  change fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) (r, t) (0, 1) = _
  have htwo : (2 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (r, t) :=
    (hf.fderiv_right (m := 1) htwo).differentiable (by norm_num) (r, t)
  rw [waveMixed_fderiv_fderiv_apply' hfd (0, 1) (0, 1)]
  simp [iteratedFDeriv_two_apply]

/-- Iterated derivatives along the two coordinate slices of a smooth function
commute.  This is the finite-smooth version of the mixed-derivative permutation
needed for Evans's radial wave transform. -/
theorem iteratedDeriv_slices_comm {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ ∞ f) (a b : ℕ) (r t : ℝ) :
    iteratedDeriv a (fun tau => iteratedDeriv b (fun s => f (s, tau)) r) t =
      iteratedDeriv b (fun s => iteratedDeriv a (fun tau => f (s, tau)) t) r := by
  have hleft : (fun tau => iteratedDeriv b (fun s => f (s, tau)) r) =
      fun tau => waveMixedDirIter ((1 : ℝ), (0 : ℝ)) b f (r, tau) := by
    funext tau
    exact (waveMixedDirIter_fst_eq_iteratedDeriv hf b r tau).symm
  have hright : (fun s => iteratedDeriv a (fun tau => f (s, tau)) t) =
      fun s => waveMixedDirIter ((0 : ℝ), (1 : ℝ)) a f (s, t) := by
    funext s
    exact (waveMixedDirIter_snd_eq_iteratedDeriv hf a s t).symm
  rw [hleft, hright]
  rw [← waveMixedDirIter_snd_eq_iteratedDeriv
    (waveMixedDirIter_contDiff_infty hf ((1 : ℝ), (0 : ℝ)) b) a r t]
  rw [← waveMixedDirIter_fst_eq_iteratedDeriv
    (waveMixedDirIter_contDiff_infty hf ((0 : ℝ), (1 : ℝ)) a) b r t]
  exact congrFun
    (waveMixedDirIter_comm hf ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) a b) (r, t)

/-- Iterated derivatives along the two coordinate slices commute as soon as
the sum of their orders is available. -/
theorem iteratedDeriv_slices_comm_of_order {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {a b : ℕ} (hf : ContDiff ℝ (a + b : ℕ) f)
    (r t : ℝ) :
    iteratedDeriv a (fun tau => iteratedDeriv b (fun s => f (s, tau)) r) t =
      iteratedDeriv b (fun s => iteratedDeriv a (fun tau => f (s, tau)) t) r := by
  have hleft : (fun tau => iteratedDeriv b (fun s => f (s, tau)) r) =
      fun tau => waveMixedDirIter ((1 : ℝ), (0 : ℝ)) b f (r, tau) := by
    funext tau
    exact (waveMixedDirIter_fst_eq_iteratedDeriv_of_order
      (hf.of_le (by exact_mod_cast (show b ≤ a + b by omega))) r tau).symm
  have hright : (fun s => iteratedDeriv a (fun tau => f (s, tau)) t) =
      fun s => waveMixedDirIter ((0 : ℝ), (1 : ℝ)) a f (s, t) := by
    funext s
    exact (waveMixedDirIter_snd_eq_iteratedDeriv_of_order
      (hf.of_le (by exact_mod_cast (show a ≤ a + b by omega))) s t).symm
  have hleftReg : ContDiff ℝ a
      (waveMixedDirIter ((1 : ℝ), (0 : ℝ)) b f) := by
    apply waveMixedDirIter_contDiff_of_order (a := b) (q := a) _
      ((1 : ℝ), (0 : ℝ))
    simpa [Nat.add_comm] using hf
  have hrightReg : ContDiff ℝ b
      (waveMixedDirIter ((0 : ℝ), (1 : ℝ)) a f) := by
    apply waveMixedDirIter_contDiff_of_order (a := a) (q := b) _
      ((0 : ℝ), (1 : ℝ))
    exact hf
  rw [hleft, hright]
  rw [← waveMixedDirIter_snd_eq_iteratedDeriv_of_order hleftReg r t]
  rw [← waveMixedDirIter_fst_eq_iteratedDeriv_of_order hrightReg r t]
  exact congrFun
    (waveMixedDirIter_comm_of_order hf
      ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))) (r, t)

/-! ## Center-radius mixed derivatives -/

private lemma waveMixedDirDeriv_prod_snd_eq_deriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {x : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x, t)) :
    waveMixedDirDeriv ((0 : E), (1 : ℝ)) f (x, t) =
      deriv (fun s => f (x, s)) t := by
  symm
  have hcurve : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact (hf.hasFDerivAt.comp_hasDerivAt t hcurve).deriv

private lemma waveMixedDirIter_prod_snd_eq_iteratedDeriv_of_order
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {a : ℕ} (hf : ContDiff ℝ a f)
    (x : E) (t : ℝ) :
    waveMixedDirIter ((0 : E), (1 : ℝ)) a f (x, t) =
      iteratedDeriv a (fun s => f (x, s)) t := by
  induction a generalizing x t with
  | zero => rfl
  | succ a ih =>
      rw [waveMixedDirIter]
      have hiter : ContDiff ℝ 1
          (waveMixedDirIter ((0 : E), (1 : ℝ)) a f) := by
        apply waveMixedDirIter_contDiff_of_order (a := a) (q := 1) _
          ((0 : E), (1 : ℝ))
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf
      rw [waveMixedDirDeriv_prod_snd_eq_deriv
        (hiter.differentiable (by norm_num) (x, t))]
      rw [iteratedDeriv_succ]
      congr 1
      funext s
      exact ih (hf.of_le (by exact_mod_cast
        (show a ≤ a + 1 by omega))) x s

private lemma waveMixedDirIter_prod_snd_eq_iteratedDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (x : E) (t : ℝ) :
    waveMixedDirIter ((0 : E), (1 : ℝ)) m f (x, t) =
      iteratedDeriv m (fun s => f (x, s)) t := by
  induction m generalizing x t with
  | zero => rfl
  | succ m ih =>
      rw [waveMixedDirIter]
      rw [waveMixedDirDeriv_prod_snd_eq_deriv
        ((waveMixedDirIter_contDiff_infty hf ((0 : E), (1 : ℝ)) m).differentiable
          (by simp) (x, t))]
      rw [iteratedDeriv_succ]
      congr 1
      funext s
      exact ih x s

private lemma waveMixedDirIter_two_eq_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (v x : E) :
    waveMixedDirIter v 2 f x = iteratedFDeriv ℝ 2 f x ![v, v] := by
  change fderiv ℝ (fun y => fderiv ℝ f y v) x v = _
  have htwo : (2 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) htwo).differentiable (by norm_num) x
  rw [waveMixed_fderiv_fderiv_apply' hfd v v]
  simp [iteratedFDeriv_two_apply]

private lemma waveMixedDirIter_prod_fst_two_eq_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (v x : E) (t : ℝ) :
    waveMixedDirIter (v, (0 : ℝ)) 2 f (x, t) =
      iteratedFDeriv ℝ 2 (fun y => f (y, t)) x ![v, v] := by
  let a : E × ℝ := (0, t)
  let L : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  have hslice : iteratedFDeriv ℝ 2 (fun y => f (y, t)) x =
      (iteratedFDeriv ℝ 2 f (x, t)).compContinuousLinearMap
        (fun _ : Fin 2 => L) := by
    have hfun : (fun y => f (y, t)) = (fun z => f (a + z)) ∘ L := by
      funext y
      simp [a, L]
    have htrans : ContDiff ℝ ∞ (fun z => f (a + z)) :=
      hf.comp (contDiff_const.add contDiff_id)
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L htrans x
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))]
    rw [iteratedFDeriv_comp_add_left]
    simp [a, L]
  rw [waveMixedDirIter_two_eq_iteratedFDeriv hf (v, (0 : ℝ)) (x, t)]
  have happ := congrArg
    (fun T => T ![v, v]) hslice
  have harr : (fun i : Fin 2 => (![v, v] i, (0 : ℝ))) =
      ![(v, (0 : ℝ)), (v, (0 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at happ
  change (iteratedFDeriv ℝ 2 (fun y => f (y, t)) x) ![v, v] =
    (iteratedFDeriv ℝ 2 f (x, t))
      (fun i => (![v, v] i, (0 : ℝ))) at happ
  rw [harr] at happ
  exact happ.symm

/-- Taking any fixed radial derivative of a jointly smooth center-radius
function and evaluating it at the running radius remains jointly smooth. -/
theorem contDiff_iteratedDeriv_centerRadius {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ =>
      iteratedDeriv m (fun s => f (p.1, s)) p.2) := by
  have hdir := waveMixedDirIter_contDiff_infty hf ((0 : E), (1 : ℝ)) m
  have heq : (fun p : E × ℝ =>
      iteratedDeriv m (fun s => f (p.1, s)) p.2) =
      waveMixedDirIter ((0 : E), (1 : ℝ)) m f := by
    funext p
    exact (waveMixedDirIter_prod_snd_eq_iteratedDeriv
      hf m p.1 p.2).symm
  rw [heq]
  exact hdir

/-- Taking any fixed radial derivative of a jointly smooth center-radius
function leaves a smooth function of the center. -/
theorem contDiff_iteratedDeriv_center_slice {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => iteratedDeriv m (fun s => f (x, s)) t) := by
  have hdir := waveMixedDirIter_contDiff_infty hf ((0 : E), (1 : ℝ)) m
  have heq : (fun x => iteratedDeriv m (fun s => f (x, s)) t) =
      fun x => waveMixedDirIter ((0 : E), (1 : ℝ)) m f (x, t) := by
    funext x
    exact (waveMixedDirIter_prod_snd_eq_iteratedDeriv hf m x t).symm
  rw [heq]
  exact hdir.comp (contDiff_id.prodMk contDiff_const)

/-- For a finite-order center-radius function, every available radial
derivative commutes with the Laplacian in the center variable. -/
theorem iteratedDeriv_laplacian_center_slice_comm_of_order {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hf : ContDiff ℝ (m + 2 : ℕ) f)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    iteratedDeriv m (fun s => Δ (fun y => f (y, s)) x) t =
      Δ (fun y => iteratedDeriv m (fun s => f (y, s)) t) x := by
  let er : EuclideanSpace ℝ (Fin n) × ℝ := (0, 1)
  let ex : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) →
      EuclideanSpace ℝ (Fin n) × ℝ := fun i =>
    ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i, 0)
  have hf2 : ContDiff ℝ 2 f := by
    exact hf.of_le (by exact_mod_cast (show 2 ≤ m + 2 by omega))
  have hspace : ContDiff ℝ 2
      (waveMixedDirIter er m f) := by
    apply waveMixedDirIter_contDiff_of_order (a := m) (q := 2) _ er
    exact hf
  have hlap : (fun s => Δ (fun y => f (y, s)) x) =
      fun s => ∑ i, iteratedFDeriv ℝ 2 (fun y => f (y, s)) x
        ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
          (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i] := by
    funext s
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [hlap]
  rw [iteratedDeriv_fun_sum]
  · rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    apply Finset.sum_congr rfl
    intro i hi
    have hterm : ContDiff ℝ m
        (waveMixedDirIter (ex i) 2 f) := by
      apply waveMixedDirIter_contDiff_of_order (a := 2) (q := m) _ (ex i)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf
    have hleft : (fun s => iteratedFDeriv ℝ 2 (fun y => f (y, s)) x
          ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
            (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]) =
      fun s => waveMixedDirIter (ex i) 2 f (x, s) := by
      funext s
      exact (waveMixedDirIter_prod_fst_two_eq_iteratedFDeriv_of_order hf2
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i) x s).symm
    rw [hleft]
    rw [← waveMixedDirIter_prod_snd_eq_iteratedDeriv_of_order hterm x t]
    rw [waveMixedDirIter_comm_of_order hf er (ex i)]
    rw [waveMixedDirIter_prod_fst_two_eq_iteratedFDeriv_of_order hspace
      ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i) x t]
    have hfun : (fun y => waveMixedDirIter er m f (y, t)) =
        fun y => iteratedDeriv m (fun s => f (y, s)) t := by
      funext y
      exact waveMixedDirIter_prod_snd_eq_iteratedDeriv_of_order
        (hf.of_le (by exact_mod_cast (show m ≤ m + 2 by omega))) y t
    rw [hfun]
  · intro i hi
    have hterm : ContDiff ℝ m
        (waveMixedDirIter (ex i) 2 f) := by
      apply waveMixedDirIter_contDiff_of_order (a := 2) (q := m) _ (ex i)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf
    have heq : (fun s => iteratedFDeriv ℝ 2 (fun y => f (y, s)) x
          ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
            (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]) =
      fun s => waveMixedDirIter (ex i) 2 f (x, s) := by
      funext s
      exact (waveMixedDirIter_prod_fst_two_eq_iteratedFDeriv_of_order hf2
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i) x s).symm
    rw [heq]
    exact (hterm.comp (contDiff_const.prodMk contDiff_id)).contDiffAt

/-- Smooth specialization of the finite center-radius commutation theorem. -/
theorem iteratedDeriv_laplacian_center_slice_comm {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    iteratedDeriv m (fun s => Δ (fun y => f (y, s)) x) t =
      Δ (fun y => iteratedDeriv m (fun s => f (y, s)) t) x :=
  iteratedDeriv_laplacian_center_slice_comm_of_order
    (hf.of_le (WithTop.coe_le_coe.mpr
      (show (m + 2 : ℕ∞) ≤ ⊤ from le_top))) x t

end EvansLib
