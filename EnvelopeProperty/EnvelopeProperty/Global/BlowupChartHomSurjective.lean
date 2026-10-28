/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BlowupChart

/-!
# Actual algebra generators of the original projective blowup chart

The original chart homomorphism is surjective on the entire paper chart
ring. This follows from homogeneous representatives in the base quotient
chart and the actual finite set of centre ratios. No inverse chart point
or comparison theorem is assumed.
-/

open MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))
    [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

omit B [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)] in
/-- Every element of the actual base quotient chart is a polynomial in the
original affine coordinate ratios. -/
theorem fc_baseChart_aeval_surjective :
    Function.Surjective (aeval (R := k) fun j : Fin (M + 1) =>
      ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j)) := by
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨N, F, hF, rfl⟩ := ProjBerk.exists_eq_chartMk (isHomogeneous_X k i) b
  refine ⟨F, ?_⟩
  exact aeval_quotChartMk_X i (by simpa only [mul_one] using hF)

/-- The actual dehomogenization map is onto the whole original blowup
chart ring, including every sum and product of its centre fractions. -/
theorem fc_chartHom_surjective (g : ProjBerk.QuotChartAlg V.ideal (X i) 1) :
    Function.Surjective (B.chartHom i g) := by
  classical
  have hbase (a : ProjBerk.QuotChartAlg V.ideal (X i) 1) :
      EnvelopeProperty.chartMap k (B.centerSet i) g a ∈ (B.chartHom i g).range := by
    obtain ⟨F, hF⟩ := fc_baseChart_aeval_surjective (V := V) i a
    refine ⟨rename Sum.inl F, ?_⟩
    change B.chartHom i g (rename Sum.inl F) = EnvelopeProperty.chartMap k (B.centerSet i) g a
    simp only [chartHom, dehomHom_rename_inl, hF]
  have hfrac (h : B.centerSet i) :
      chartFrac (B.centerSet i) g h.2 ∈ (B.chartHom i g).range := by
    obtain ⟨m, hm⟩ := (B.mem_centerSet_iff i).1 h.2
    refine ⟨X (Sum.inr m), ?_⟩
    change B.chartHom i g (X (Sum.inr m)) = chartFrac (B.centerSet i) g h.2
    rw [B.chartHom_X_inr]
    apply Subtype.ext
    simp only [coe_chartFrac, hm]
  have hgen := EnvelopeProperty.adjoin_chartMap_union_chartFrac
    (k := k) (B.centerSet i) g (S := Set.univ) (by simp)
  have hle :
      Algebra.adjoin k (EnvelopeProperty.chartMap k (B.centerSet i) g '' Set.univ ∪
        Set.range fun h : B.centerSet i => chartFrac (B.centerSet i) g h.2) ≤
        (B.chartHom i g).range := Algebra.adjoin_le (by
    rintro z (⟨a, _, rfl⟩ | ⟨h, rfl⟩)
    · exact hbase a
    · exact hfrac h)
  rw [hgen] at hle
  exact (AlgHom.range_eq_top _).1 (top_unique hle)

/-- The two genuine unit coordinates let every chart element be represented
by one bihomogeneous form, retaining its entire original value. -/
theorem fc_chartHom_homogeneous_preimage
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g)
    (z : blowupChart (B.centerSet i) g) :
    ∃ (p : ℕ × ℕ) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k),
      F.IsWeightedHomogeneous (biWeight M M') p ∧ B.chartHom i g F = z := by
  obtain ⟨F, rfl⟩ := B.fc_chartHom_surjective i g z
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    exact ⟨Finsupp.weight (biWeight M M') α, monomial α c,
      isWeightedHomogeneous_monomial _ _ _ rfl, rfl⟩
  | add F G ihF ihG =>
    obtain ⟨p, F', hF, eF⟩ := ihF
    obtain ⟨q, G', hG, eG⟩ := ihG
    have hF' : (F' * X (Sum.inl i) ^ q.1 * X (Sum.inr l) ^ q.2).IsWeightedHomogeneous
        (biWeight M M') (p + q) := by
      convert (hF.mul ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inl i)).pow q.1)).mul
        ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inr l)).pow q.2) using 1
      cases p
      cases q
      simp [biWeight, Prod.add_def]
    have hG' : (G' * X (Sum.inl i) ^ p.1 * X (Sum.inr l) ^ p.2).IsWeightedHomogeneous
        (biWeight M M') (p + q) := by
      convert (hG.mul ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inl i)).pow p.1)).mul
        ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inr l)).pow p.2) using 1
      cases p
      cases q
      simp [biWeight, Prod.add_def, add_comm]
    refine ⟨p + q,
      F' * X (Sum.inl i) ^ q.1 * X (Sum.inr l) ^ q.2 +
        G' * X (Sum.inl i) ^ p.1 * X (Sum.inr l) ^ p.2,
      hF'.add hG', ?_⟩
    simp only [map_add, map_mul, map_pow, B.chartHom_X_inl_self,
      B.chartHom_X_inr_of_centerGen_eq hg0 hl, one_pow, mul_one, eF, eG]

end EnvelopeProperty.ProjSubvariety.BlowupCenter
