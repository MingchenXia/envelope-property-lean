/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupAffineReesPolynomial

/-!
# Constructed bihomogeneous lifts of actual affine-base homogeneous polynomials

Whole affine coefficient elements have homogeneous numerator representatives.
Aligning their first degrees with the selected unit coordinate constructs a
bihomogeneous preimage of every actual homogeneous Rees polynomial. This is
needed to recover whole native projective seminorms from the old point model.
-/

open MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (i : Fin (M + 1))

/-- Every actual affine quotient element has an actual homogeneous numerator
preimage, with no domain or extra representative hypothesis. -/
theorem fc_baseChart_homogeneous_preimage (a : ProjBerk.QuotChartAlg V.ideal (X i) 1) :
    ∃ (n : ℕ) (F : MvPolynomial (Fin (M + 1)) k), F.IsHomogeneous n ∧
      (aeval fun j => ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) F = a := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨n, F, hF, rfl⟩ := ProjBerk.exists_eq_chartMk (isHomogeneous_X k i) c
  refine ⟨n, F, by simpa only [mul_one] using hF, ?_⟩
  exact aeval_quotChartMk_X i (by simpa only [mul_one] using hF)

/-- The whole second-polynomial substitution retains every coefficient via
the actual original coefficient map. -/
theorem fcAffineReesPolynomial_rename_inr (Q : MvPolynomial (Fin (M' + 1)) k) :
    fcAffineReesPolynomial (V := V) i (rename Sum.inr Q) =
      MvPolynomial.map (algebraMap k (ProjBerk.QuotChartAlg V.ideal (X i) 1)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    rw [rename_C, map_C]
    change (fcAffineReesPolynomial (V := V) i) (algebraMap k _ c) = _
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply k (ProjBerk.QuotChartAlg V.ideal (X i) 1) _ c
  | add Q R hQ hR => simp only [map_add, hQ, hR]
  | mul_X Q m hQ => simp only [map_mul, rename_X, hQ, fcAffineReesPolynomial_X_inr, map_X]

/-- Every homogeneous polynomial over the entire original affine quotient
chart has one genuinely constructed bihomogeneous original preimage. -/
theorem fcAffineReesPolynomial_homogeneous_preimage {b : ℕ}
    {Q : MvPolynomial (Fin (M' + 1)) (ProjBerk.QuotChartAlg V.ideal (X i) 1)}
    (hQ : Q.IsHomogeneous b) :
    ∃ (a : ℕ) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k),
      F.IsWeightedHomogeneous (biWeight M M') (a, b) ∧
        fcAffineReesPolynomial (V := V) i F = Q := by
  induction hQ using IsWeightedHomogeneous.induction_on with
  | zero =>
    exact ⟨0, 0, isWeightedHomogeneous_zero k _ _, map_zero _⟩
  | add Q R hQ hR ihQ ihR =>
    obtain ⟨a, F, hF, eF⟩ := ihQ
    obtain ⟨c, G, hG, eG⟩ := ihR
    have hF' : (F * X (Sum.inl i) ^ c).IsWeightedHomogeneous (biWeight M M') (a + c, b) := by
      convert hF.mul ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inl i)).pow c) using 1
      simp [biWeight, Prod.add_def]
    have hG' : (G * X (Sum.inl i) ^ a).IsWeightedHomogeneous (biWeight M M') (a + c, b) := by
      convert hG.mul ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inl i)).pow a) using 1
      simp [biWeight, Prod.add_def, add_comm]
    refine ⟨a + c, F * X (Sum.inl i) ^ c + G * X (Sum.inl i) ^ a, hF'.add hG', ?_⟩
    simp only [map_add, map_mul, map_pow, fcAffineReesPolynomial_X_inl,
      quotChartMk_X_self, C_1, one_pow, mul_one, eF, eG]
  | monomial α c hr =>
    obtain ⟨a, F, hF, eF⟩ := fc_baseChart_homogeneous_preimage i c
    have hY : (monomial α (1 : k)).IsHomogeneous b :=
      isWeightedHomogeneous_monomial 1 α (1 : k) hr
    have hH := (isWeightedHomogeneous_rename_inl (M' := M') hF).mul
      (isWeightedHomogeneous_rename_inr (M := M) hY)
    refine ⟨a, rename Sum.inl F * rename Sum.inr (monomial α (1 : k)), ?_, ?_⟩
    · simpa only [Prod.add_def, add_zero, zero_add] using hH
    · simp only [map_mul, fcAffineReesPolynomial_rename_inl, eF,
        fcAffineReesPolynomial_rename_inr, map_monomial, map_one, C_mul_monomial, mul_one]

end EnvelopeProperty.ProjSubvariety.BlowupCenter
