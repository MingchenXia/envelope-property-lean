/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupChartHomSurjective
import EnvelopeProperty.ReesPresentation

/-!
# The actual original affine-base Rees polynomial substitution

This is a polynomial-map producer for comparison of the original bigraded
blowup with the genuine affine-base Rees scheme. It retains the actual base
quotient and original centre family. No native comparison is assumed.
-/

open MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))

omit B in
/-- The actual map keeps the second polynomial variables and evaluates
first variables at the original affine quotient coordinate ratios. -/
def fcAffineReesPolynomial : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k]
    MvPolynomial (Fin (M' + 1)) (ProjBerk.QuotChartAlg V.ideal (X i) 1) :=
  aeval (Sum.elim (fun j => C (ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j))) X)

omit B in
@[simp]
theorem fcAffineReesPolynomial_X_inl (j : Fin (M + 1)) :
    fcAffineReesPolynomial (V := V) (M' := M') i (X (Sum.inl j)) =
      C (ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) := by
  simp [fcAffineReesPolynomial]

omit B in
@[simp]
theorem fcAffineReesPolynomial_X_inr (m : Fin (M' + 1)) :
    fcAffineReesPolynomial (V := V) i (X (Sum.inr m)) = X m := by
  simp [fcAffineReesPolynomial]

omit B in
/-- The whole actual first-polynomial evaluation is retained as a coefficient. -/
theorem fcAffineReesPolynomial_rename_inl (F : MvPolynomial (Fin (M + 1)) k) :
    fcAffineReesPolynomial (V := V) (M' := M') i (rename Sum.inl F) =
      C ((aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [rename_C]
    change (fcAffineReesPolynomial (V := V) (M' := M') i) (algebraMap k _ c) =
      C ((aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) (algebraMap k _ c))
    rw [AlgHom.commutes, AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply k (ProjBerk.QuotChartAlg V.ideal (X i) 1) _ c
  | add F G hF hG =>
    rw [map_add (rename Sum.inl), map_add (fcAffineReesPolynomial (V := V) (M' := M') i),
      hF, hG, map_add (aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j))]
    exact C_add.symm
  | mul_X F j hF =>
    rw [map_mul (rename Sum.inl), rename_X,
      map_mul (fcAffineReesPolynomial (V := V) (M' := M') i), hF,
      fcAffineReesPolynomial_X_inl,
      map_mul (aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)), aeval_X]
    exact C_mul.symm

omit B in
/-- The genuine affine-base substitution is surjective onto every polynomial
with coefficients in the whole original affine quotient chart. -/
theorem fcAffineReesPolynomial_surjective :
    Function.Surjective (fcAffineReesPolynomial (V := V) (M' := M') i) := by
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨F, hF⟩ := fc_baseChart_aeval_surjective (V := V) i a
    exact ⟨rename Sum.inl F, by rw [fcAffineReesPolynomial_rename_inl, hF]⟩
  | add Q R hQ hR =>
    obtain ⟨P, hP⟩ := hQ
    obtain ⟨S, hS⟩ := hR
    exact ⟨P + S, by rw [map_add, hP, hS]⟩
  | mul_X Q m hQ =>
    obtain ⟨P, hP⟩ := hQ
    exact ⟨P * X (Sum.inr m), by rw [map_mul, hP, fcAffineReesPolynomial_X_inr]⟩

/-- Evaluation of the actual affine Rees polynomial at the actual centre
family is the original homogeneous substitution evaluated in the base chart. -/
theorem fc_aeval_affineReesPolynomial
    (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    (aeval (B.centerGen i)) (fcAffineReesPolynomial (V := V) i F) =
      (aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) (B.subst F) := by
  have he : ((aeval (B.centerGen i)).restrictScalars k).comp
      (fcAffineReesPolynomial (V := V) i) =
      (aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)).comp B.subst := by
    ext (j | m)
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        fcAffineReesPolynomial_X_inl, aeval_C, subst_X_inl, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        fcAffineReesPolynomial_X_inr, aeval_X, subst_X_inr, aeval_quotChartMk_X_G]
  exact AlgHom.congr_fun he F

omit B in
/-- The second component of the genuine bidegree becomes the genuine
homogeneous degree over the entire affine coefficient ring. -/
theorem fcAffineReesPolynomial_isHomogeneous {a b : ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    (fcAffineReesPolynomial (V := V) i F).IsHomogeneous b := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero =>
    simp only [map_zero]
    exact (homogeneousSubmodule _ _ b).zero_mem
  | add P Q hP hQ ihP ihQ => simpa only [map_add] using ihP.add ihQ
  | monomial α c hr =>
    rw [fcAffineReesPolynomial, aeval_monomial]
    let f : Fin (M + 1) ⊕ Fin (M' + 1) →
        MvPolynomial (Fin (M' + 1)) (ProjBerk.QuotChartAlg V.ideal (X i) 1) :=
      Sum.elim (fun j => C (ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j))) X
    have hf (v) : (f v).IsHomogeneous (biWeight M M' v).2 := by
      rcases v with j | m
      · exact isHomogeneous_C _ _
      · exact isHomogeneous_X _ _
    have hd : (∑ v ∈ α.support, (biWeight M M' v).2 * α v) = b := by
      have h := congrArg Prod.snd hr
      simpa [Finsupp.weight_apply, Finsupp.sum, Prod.snd_sum, mul_comm] using h
    have hp := IsHomogeneous.prod α.support (fun v => f v ^ α v)
      (fun v => (biWeight M M' v).2 * α v) (fun v _ => (hf v).pow (α v))
    have hc : algebraMap k (MvPolynomial (Fin (M' + 1))
        (ProjBerk.QuotChartAlg V.ideal (X i) 1)) c =
        C (algebraMap k (ProjBerk.QuotChartAlg V.ideal (X i) 1) c) :=
      IsScalarTower.algebraMap_apply k (ProjBerk.QuotChartAlg V.ideal (X i) 1) _ c
    rw [hc]
    simpa only [Finsupp.prod, hd, f] using
      hp.C_mul (algebraMap k (ProjBerk.QuotChartAlg V.ideal (X i) 1) c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire actual Rees presentation of a bihomogeneous source form
is the original substituted affine coefficient times the exact second power. -/
theorem fc_presentation_affineReesPolynomial {a b : ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    ReesPresentation.presentation (B.centerGen i) (fcAffineReesPolynomial (V := V) i F) =
      Polynomial.C ((aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) (B.subst F)) *
        Polynomial.X ^ b := by
  have hh := fcAffineReesPolynomial_isHomogeneous (V := V) i hF
  have he := ReesPresentation.presentation_of_isHomogeneous (B.centerGen i) hh
  exact he.trans (by rw [B.fc_aeval_affineReesPolynomial])

/-- The whole original blowup ideal, including nonhomogeneous elements,
maps into the genuine original Rees presentation kernel. -/
theorem fcAffineReesPolynomial_mem_kernel {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F ∈ B.ideal) :
    fcAffineReesPolynomial (V := V) i F ∈ ReesPresentation.kernel (B.centerGen i) := by
  change ReesPresentation.presentation (B.centerGen i)
    (fcAffineReesPolynomial (V := V) i F) = 0
  rw [← sum_weightSupport (w := biWeight M M') F, map_sum, map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hp := weightedHomogeneousComponent_isWeightedHomogeneous (w := biWeight M M') p F
  have hI := (B.mem_ideal_iff_of_isWeightedHomogeneous hp).1
    (B.weightedHomogeneousComponent_mem_ideal hF p)
  rw [B.fc_presentation_affineReesPolynomial i hp,
    aeval_quotChartMk_X i (B.isHomogeneous_subst hp)]
  have hz : ProjBerk.quotChartMk V.ideal (X i) 1 (p.1 + p.2 * B.d)
      (B.subst (weightedHomogeneousComponent (biWeight M M') p F)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (ProjBerk.chartMk_mem_chartIdeal
      (by simpa only [mul_one] using B.isHomogeneous_subst hp) hI)
  rw [hz, Polynomial.C_0, zero_mul]

/-- On original bihomogeneous forms, the genuine Rees kernel is exactly the
original blowup ideal. The domain hypothesis is derived from a nonzero base
coordinate when this is applied to a fibre. -/
theorem fcAffineReesPolynomial_mem_kernel_iff
    [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)] {a b : ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    fcAffineReesPolynomial (V := V) i F ∈ ReesPresentation.kernel (B.centerGen i) ↔
      F ∈ B.ideal := by
  refine ⟨fun hz => ?_, B.fcAffineReesPolynomial_mem_kernel i⟩
  change ReesPresentation.presentation (B.centerGen i)
    (fcAffineReesPolynomial (V := V) i F) = 0 at hz
  rw [B.fc_presentation_affineReesPolynomial i hF] at hz
  have he := congrArg (fun P => Polynomial.coeff P b) hz
  have hc : (aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) (B.subst F) = 0 := by
    simpa only [Polynomial.coeff_C_mul_X_pow, if_pos rfl, ite_true, Polynomial.coeff_zero] using he
  rw [aeval_quotChartMk_X i (B.isHomogeneous_subst hF)] at hc
  exact (B.mem_ideal_iff_of_isWeightedHomogeneous hF).2
    ((ProjBerk.quotChartMk_eq_zero_iff (X_notMem_ideal_of_isDomain (V := V) i)
      (by simpa only [mul_one] using B.isHomogeneous_subst hF)).1 hc)

end EnvelopeProperty.ProjSubvariety.BlowupCenter
