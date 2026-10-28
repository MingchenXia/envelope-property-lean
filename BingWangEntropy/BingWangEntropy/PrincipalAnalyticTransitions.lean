import BingWangEntropy.AlgebraicAnalyticTransitions
import BingWangEntropy.AffineComplexLocalization

/-!
# Genuine principal-localization analytic coordinates

Actual localization points form the actual nonvanishing open locus. The
localization universal property and genuine denominator powers make every
localized element analytic in standard-smooth chart coordinates.
-/

open Algebra Topology

set_option backward.isDefEq.respectTransparency false

namespace BingWangEntropy

noncomputable section

variable {A S : Type*} [CommRing A] [Algebra ℂ A] [CommRing S]
  [Algebra ℂ S] [Algebra A S] [IsScalarTower ℂ A S]

/-- Actual localization points map to the genuine nonvanishing open subset. -/
def localizationComplexPointOpenChart (S : Type*) [CommRing S] [Algebra ℂ S]
    [Algebra A S] [IsScalarTower ℂ A S] (r : A) [IsLocalization.Away r S]
    (p : ComplexAlgebraPoint A) (hp : p r ≠ 0) :
    OpenPartialHomeomorph (ComplexAlgebraPoint S) (ComplexAlgebraPoint A) :=
  let U : TopologicalSpace.Opens (ComplexAlgebraPoint A) :=
    ⟨complexPrincipalOpen r, complexPrincipalOpen_isOpen r⟩
  let hU : Nonempty U := ⟨⟨p, hp⟩⟩
  (localizationComplexPointHomeomorph S r).toOpenPartialHomeomorph.trans
    (U.openPartialHomeomorphSubtypeCoe hU)

@[simp]
theorem localizationComplexPointOpenChart_source (r : A) [IsLocalization.Away r S]
    (p : ComplexAlgebraPoint A) (hp : p r ≠ 0) :
    (localizationComplexPointOpenChart S r p hp).source = Set.univ := by
  simp [localizationComplexPointOpenChart]

@[simp]
theorem localizationComplexPointOpenChart_target (r : A) [IsLocalization.Away r S]
    (p : ComplexAlgebraPoint A) (hp : p r ≠ 0) :
    (localizationComplexPointOpenChart S r p hp).target = complexPrincipalOpen r := by
  simp [localizationComplexPointOpenChart]

/-- The actual forward map is the genuine algebra-point restriction. -/
@[simp]
theorem localizationComplexPointOpenChart_apply (r : A) [IsLocalization.Away r S]
    (p : ComplexAlgebraPoint A) (hp : p r ≠ 0) (q : ComplexAlgebraPoint S) :
    localizationComplexPointOpenChart S r p hp q = q.comp (Algebra.algHom ℂ A S) := rfl

/-- On the genuine nonvanishing locus the inverse is the native localization extension. -/
theorem localizationComplexPointOpenChart_symm_apply (r : A) [IsLocalization.Away r S]
    (p : ComplexAlgebraPoint A) (hp : p r ≠ 0) (q : ComplexAlgebraPoint A) (hq : q r ≠ 0) :
    (localizationComplexPointOpenChart S r p hp).symm q =
      localizationComplexPoint_extend S r ⟨q, hq⟩ := by
  let U : TopologicalSpace.Opens (ComplexAlgebraPoint A) :=
    ⟨complexPrincipalOpen r, complexPrincipalOpen_isOpen r⟩
  let hU : Nonempty U := ⟨⟨p, hp⟩⟩
  change (localizationComplexPointHomeomorph S r).symm
    ((U.openPartialHomeomorphSubtypeCoe hU).symm q) = _
  have he : (U.openPartialHomeomorphSubtypeCoe hU).symm q = ⟨q, hq⟩ := by
    apply Subtype.ext
    apply (U.openPartialHomeomorphSubtypeCoe hU).right_inv
    simpa [U, complexPrincipalOpen] using hq
  rw [he]
  rfl

/-- Every actual localization fraction has its literal denominator evaluation. -/
theorem localizationComplexPointOpenChart_symm_eval_fraction (r : A)
    [IsLocalization.Away r S] (p : ComplexAlgebraPoint A) (hp : p r ≠ 0)
    (q : ComplexAlgebraPoint A) (hq : q r ≠ 0) (s : S) (n : ℕ) (a : A)
    (hs : s * algebraMap A S r ^ n = algebraMap A S a) :
    (localizationComplexPointOpenChart S r p hp).symm q s = q a / q r ^ n := by
  rw [localizationComplexPointOpenChart_symm_apply]
  exact localizationComplexPoint_eval_fraction S r ⟨q, hq⟩ s n a hs

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

/-- Actual free coordinates whose actual inverse point lies in the genuine principal open. -/
def submersivePrincipalAnalyticDomain (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (r : A) : Set (Fin P.dimension → ℂ) :=
  (submersiveAnalyticComplexPointChart P p).target ∩
    (submersiveAnalyticComplexPointChart P p).symm ⁻¹' complexPrincipalOpen r

/-- The actual local chart inverse followed by the actual localization extension. -/
def submersivePrincipalAnalyticPoint (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (r : A) [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) :
    (Fin P.dimension → ℂ) → ComplexAlgebraPoint S :=
  fun t => (localizationComplexPointOpenChart S r w hw).symm
    ((submersiveAnalyticComplexPointChart P p).symm t)

/-- The true principal point inverse is continuous at each actual parameter-domain point. -/
theorem submersivePrincipalAnalyticPoint_continuousAt (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (r : A) [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0)
    {t : Fin P.dimension → ℂ} (ht : t ∈ submersivePrincipalAnalyticDomain P p r) :
    ContinuousAt (submersivePrincipalAnalyticPoint (S := S) P p r w hw) t := by
  have hm : (submersiveAnalyticComplexPointChart P p).symm t ∈
      (localizationComplexPointOpenChart S r w hw).target := by
    rw [localizationComplexPointOpenChart_target]
    exact ht.2
  exact ((localizationComplexPointOpenChart S r w hw).continuousAt_symm hm).comp
    ((submersiveAnalyticComplexPointChart P p).continuousAt_symm ht.1)

/-- The actual denominator remains nonzero on a true neighborhood of each principal parameter. -/
theorem submersivePrincipalAnalyticDomain_eventually_nonzero
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) (r : A)
    {t : Fin P.dimension → ℂ} (ht : t ∈ submersivePrincipalAnalyticDomain P p r) :
    ∀ᶠ s in 𝓝 t, (submersiveAnalyticComplexPointChart P p).symm s r ≠ 0 := by
  have hnonzero : (submersiveAnalyticComplexPointChart P p).symm t r ≠ 0 := ht.2
  have hU : IsOpen {z : ℂ | z ≠ 0} := isClosed_singleton.isOpen_compl
  exact Filter.Tendsto.eventually (p := fun z : ℂ => z ≠ 0)
    (submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd P p r t ht.1).continuousAt
    (hU.mem_nhds hnonzero)

/-- The actual localization parameter domain is genuinely open. -/
theorem submersivePrincipalAnalyticDomain_isOpen (P : SubmersivePresentation ℂ A I J)
    (p : ComplexAlgebraPoint A) (r : A) : IsOpen (submersivePrincipalAnalyticDomain P p r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  exact Filter.inter_mem
    ((submersiveAnalyticComplexPointChart P p).open_target.mem_nhds ht.1)
    (submersivePrincipalAnalyticDomain_eventually_nonzero P p r ht)

/-- Genuine numerator/denominator formulas prove every localized element analytic on the actual domain. -/
theorem submersivePrincipalAnalyticPoint_eval_analyticOnNhd
    (P : SubmersivePresentation ℂ A I J) (p : ComplexAlgebraPoint A) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) (s : S) :
    AnalyticOnNhd ℂ (fun t => submersivePrincipalAnalyticPoint P p r w hw t s)
      (submersivePrincipalAnalyticDomain P p r) := by
  intro t ht
  obtain ⟨n, a, hs⟩ := IsLocalization.Away.surj r s
  have hn := submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd P p a t ht.1
  have hd := submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd P p r t ht.1
  apply (hn.div (hd.pow n) (pow_ne_zero n ht.2)).congr
  filter_upwards [submersivePrincipalAnalyticDomain_eventually_nonzero P p r ht] with u hu
  exact (localizationComplexPointOpenChart_symm_eval_fraction r w hw
    ((submersiveAnalyticComplexPointChart P p).symm u) hu s n a hs).symm

variable {B I' J' : Type*} [CommRing B] [Algebra ℂ B]
  [Fintype I'] [Fintype J'] [DecidableEq J']

/-- The genuine overlap with another affine chart after actual principal localization. -/
def submersivePrincipalTransitionDomain (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] S)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) : Set (Fin P.dimension → ℂ) :=
  submersivePrincipalAnalyticDomain P p r ∩
    (fun t => (submersivePrincipalAnalyticPoint P p r w hw t).comp g) ⁻¹'
      (submersiveAnalyticComplexPointChart Q q).source

/-- Literal coordinate expression of the actual localization-chart morphism. -/
def submersivePrincipalTransition (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] S)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) :
    (Fin P.dimension → ℂ) → (Fin Q.dimension → ℂ) :=
  fun t => submersiveAnalyticComplexPointChart Q q
    ((submersivePrincipalAnalyticPoint P p r w hw t).comp g)

/-- Actual localization-point continuity supplies a genuine neighborhood in the other chart. -/
theorem submersivePrincipalTransition_eventually_source
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] S) (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) {t : Fin P.dimension → ℂ}
    (ht : t ∈ submersivePrincipalTransitionDomain P Q g p q r w hw) :
    ∀ᶠ u in 𝓝 t, (submersivePrincipalAnalyticPoint P p r w hw u).comp g ∈
      (submersiveAnalyticComplexPointChart Q q).source :=
  Filter.Tendsto.eventually
    ((complexPoint_pullback_continuous g).continuousAt.comp
      (submersivePrincipalAnalyticPoint_continuousAt P p r w hw ht.1))
    ((submersiveAnalyticComplexPointChart Q q).open_source.mem_nhds ht.2)

/-- The actual principal overlap parameter domain is open. -/
theorem submersivePrincipalTransitionDomain_isOpen
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] S) (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) :
    IsOpen (submersivePrincipalTransitionDomain P Q g p q r w hw) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  exact Filter.inter_mem ((submersivePrincipalAnalyticDomain_isOpen P p r).mem_nhds ht.1)
    (submersivePrincipalTransition_eventually_source P Q g p q r w hw ht)

/-- Genuine principal-chart transition components evaluate actual localized free generators. -/
theorem submersivePrincipalTransition_apply (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] S)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) {t : Fin P.dimension → ℂ}
    (ht : t ∈ submersivePrincipalTransitionDomain P Q g p q r w hw) (i : Fin Q.dimension) :
    submersivePrincipalTransition P Q g p q r w hw t i =
      submersivePrincipalAnalyticPoint P p r w hw t
        (g (Q.val ((submersiveFreeIndexEquiv Q).symm i))) :=
  submersiveAnalyticComplexPointChart_apply Q q _ ht.2 i

/-- Every actual principal-overlap transition is analytic throughout its genuine open domain. -/
theorem submersivePrincipalTransition_analyticOnNhd
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] S) (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) :
    AnalyticOnNhd ℂ (submersivePrincipalTransition P Q g p q r w hw)
      (submersivePrincipalTransitionDomain P Q g p q r w hw) := by
  intro t ht
  apply AnalyticAt.pi
  intro i
  have h := submersivePrincipalAnalyticPoint_eval_analyticOnNhd P p r w hw
    (g (Q.val ((submersiveFreeIndexEquiv Q).symm i))) t ht.1
  apply h.congr
  filter_upwards [submersivePrincipalTransition_eventually_source P Q g p q r w hw ht] with u hu
  exact (submersiveAnalyticComplexPointChart_apply Q q _ hu i).symm

/-- All differentiability orders hold on the true principal overlap. -/
theorem submersivePrincipalTransition_contDiffOn
    (P : SubmersivePresentation ℂ A I J) (Q : SubmersivePresentation ℂ B I' J')
    (g : B →ₐ[ℂ] S) (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (r : A)
    [IsLocalization.Away r S] (w : ComplexAlgebraPoint A) (hw : w r ≠ 0) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n (submersivePrincipalTransition P Q g p q r w hw)
      (submersivePrincipalTransitionDomain P Q g p q r w hw) :=
  (submersivePrincipalTransition_analyticOnNhd P Q g p q r w hw).contDiffOn
    (submersivePrincipalTransitionDomain_isOpen P Q g p q r w hw).uniqueDiffOn

end

end BingWangEntropy
