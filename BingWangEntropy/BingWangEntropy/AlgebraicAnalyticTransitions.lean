import BingWangEntropy.StandardSmoothComplexCharts

/-!
# Analytic coordinate expressions of genuine algebra morphisms

The source and target are actual standard-smooth presentation charts. On their
genuine overlap, each transition component evaluates the pullback of a literal
free generator. The inverse chart makes every such algebra element analytic.
-/

open Algebra
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace BingWangEntropy

noncomputable section

variable {A B I J I' J' : Type*} [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B] [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype I'] [Fintype J'] [DecidableEq J']

/-- The actual chart overlap for the genuine algebra-point pullback. -/
def submersiveAnalyticTransitionDomain (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    Set (Fin P.dimension → ℂ) :=
  (submersiveAnalyticComplexPointChart P p).target ∩
    (fun t => ((submersiveAnalyticComplexPointChart P p).symm t).comp g) ⁻¹'
      (submersiveAnalyticComplexPointChart Q q).source

/-- Literal coordinate expression of the actual algebra morphism. -/
def submersiveAnalyticTransition (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    (Fin P.dimension → ℂ) → (Fin Q.dimension → ℂ) :=
  fun t => submersiveAnalyticComplexPointChart Q q
    (((submersiveAnalyticComplexPointChart P p).symm t).comp g)

/-- Every genuine transition component evaluates the pulled-back actual free generator. -/
theorem submersiveAnalyticTransition_apply (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B)
    {t : Fin P.dimension → ℂ} (ht : t ∈ submersiveAnalyticTransitionDomain P Q g p q)
    (i : Fin Q.dimension) :
    submersiveAnalyticTransition P Q g p q t i =
      (submersiveAnalyticComplexPointChart P p).symm t
        (g (Q.val ((submersiveFreeIndexEquiv Q).symm i))) :=
  submersiveAnalyticComplexPointChart_apply Q q _ ht.2 i

/-- The actual inverse chart and genuine point pullback are continuous at each actual target point. -/
theorem submersiveAnalyticPullback_continuousAt (P : SubmersivePresentation ℂ A I J)
    (g : B →ₐ[ℂ] A) (p : ComplexAlgebraPoint A) {t : Fin P.dimension → ℂ}
    (ht : t ∈ (submersiveAnalyticComplexPointChart P p).target) :
    ContinuousAt (fun s => ((submersiveAnalyticComplexPointChart P p).symm s).comp g) t :=
  (complexPoint_pullback_continuous g).continuousAt.comp
    ((submersiveAnalyticComplexPointChart P p).continuousAt_symm ht)

/-- Native openness and actual continuity produce the true local target-chart overlap. -/
theorem submersiveAnalyticTransition_eventually_source (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B)
    {t : Fin P.dimension → ℂ} (ht : t ∈ submersiveAnalyticTransitionDomain P Q g p q) :
    ∀ᶠ s in 𝓝 t, ((submersiveAnalyticComplexPointChart P p).symm s).comp g ∈
      (submersiveAnalyticComplexPointChart Q q).source :=
  Filter.Tendsto.eventually (submersiveAnalyticPullback_continuousAt P g p ht.1)
    ((submersiveAnalyticComplexPointChart Q q).open_source.mem_nhds ht.2)

/-- The actual source-target overlap is open in the genuine free-coordinate model. -/
theorem submersiveAnalyticTransitionDomain_isOpen (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    IsOpen (submersiveAnalyticTransitionDomain P Q g p q) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  exact Filter.inter_mem
    ((submersiveAnalyticComplexPointChart P p).open_target.mem_nhds ht.1)
    (submersiveAnalyticTransition_eventually_source P Q g p q ht)

/-- Actual algebra morphisms have analytic coordinates everywhere on the genuine chart overlap. -/
theorem submersiveAnalyticTransition_analyticOnNhd (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    AnalyticOnNhd ℂ (submersiveAnalyticTransition P Q g p q)
      (submersiveAnalyticTransitionDomain P Q g p q) := by
  intro t ht
  apply AnalyticAt.pi
  intro i
  have ha := submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd P p
    (g (Q.val ((submersiveFreeIndexEquiv Q).symm i))) t ht.1
  apply ha.congr
  filter_upwards [submersiveAnalyticTransition_eventually_source P Q g p q ht] with s hs
  exact (submersiveAnalyticComplexPointChart_apply Q q _ hs i).symm

/-- Every differentiability order follows for actual coordinate pullbacks on their true open domain. -/
theorem submersiveAnalyticTransition_contDiffOn (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (g : B →ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n (submersiveAnalyticTransition P Q g p q)
      (submersiveAnalyticTransitionDomain P Q g p q) :=
  (submersiveAnalyticTransition_analyticOnNhd P Q g p q).contDiffOn
    (submersiveAnalyticTransitionDomain_isOpen P Q g p q).uniqueDiffOn

/-- An actual algebra isomorphism gives the native transition open partial homeomorphism. -/
def submersiveAnalyticTransitionChart (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (e : B ≃ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    OpenPartialHomeomorph (Fin P.dimension → ℂ) (Fin Q.dimension → ℂ) :=
  (submersiveAnalyticComplexPointChart P p).symm.trans
    ((complexPointAlgEquivHomeomorph e.symm).toOpenPartialHomeomorph.trans
      (submersiveAnalyticComplexPointChart Q q))

@[simp]
theorem submersiveAnalyticTransitionChart_apply (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (e : B ≃ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) (t : Fin P.dimension → ℂ) :
    submersiveAnalyticTransitionChart P Q e p q t =
      submersiveAnalyticTransition P Q e.toAlgHom p q t := rfl

@[simp]
theorem submersiveAnalyticTransitionChart_source (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (e : B ≃ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    (submersiveAnalyticTransitionChart P Q e p q).source =
      submersiveAnalyticTransitionDomain P Q e.toAlgHom p q := by
  simp [submersiveAnalyticTransitionChart, submersiveAnalyticTransitionDomain,
    complexPointAlgEquivHomeomorph]
  rfl

/-- The actual native transition has analytic forward coordinates throughout its genuine source. -/
theorem submersiveAnalyticTransitionChart_analyticOnNhd (P : SubmersivePresentation ℂ A I J)
    (Q : SubmersivePresentation ℂ B I' J') (e : B ≃ₐ[ℂ] A)
    (p : ComplexAlgebraPoint A) (q : ComplexAlgebraPoint B) :
    AnalyticOnNhd ℂ (submersiveAnalyticTransitionChart P Q e p q)
      (submersiveAnalyticTransitionChart P Q e p q).source := by
  rw [submersiveAnalyticTransitionChart_source]
  change AnalyticOnNhd ℂ (submersiveAnalyticTransition P Q e.toAlgHom p q)
    (submersiveAnalyticTransitionDomain P Q e.toAlgHom p q)
  exact submersiveAnalyticTransition_analyticOnNhd P Q e.toAlgHom p q

end

end BingWangEntropy
