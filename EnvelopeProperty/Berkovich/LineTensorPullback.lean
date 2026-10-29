/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.SurjectiveBaseChange
import EnvelopeProperty.Berkovich.NormalizedLineProduct

/-!
# Literal tensor pullback of the actual principal-open affine line

The original transverse equation ideal, without its radical, defines the actual
unreduced preimage. Its true descended line action and literal tensor algebra
are identified on every original element. The whole normalized component map
factors through this actual quotient. Finite/free/etale and natural-valued
finrank transport use genuine base change. Generic normalization and original
degree comparisons remain separate further producers.
-/

open scoped TensorProduct Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.AffineLine
variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B)
include hb

/-- Every original line equation vanishes in the original whole preimage quotient. -/
theorem originalLine_ker_le :
    RingHom.ker (principalLineHom a b g).toRingHom ≤
      RingHom.ker ((Ideal.Quotient.mkₐ F (linePreimageIdeal a b j g φ)).comp φ).toRingHom := by
  rw [ker_principalLineHom a b j g hb]
  change (lineIdeal a b j).map (algebraMap _ (Localization.Away g)) ≤
    RingHom.ker ((Ideal.Quotient.mk (linePreimageIdeal a b j g φ)).comp φ.toRingHom)
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← Ideal.map_le_iff_le_comap, Ideal.map_map]

/-- The actual line coefficient map into the entire original unreduced pullback quotient. -/
def originalLineHom : OpenLineRing (subst a b g) →ₐ[F] B ⧸ linePreimageIdeal a b j g φ :=
  AlgHom.liftOfSurjective (principalLineHom a b g)
    (principalLineHom_surjective a b g (by intro hz; exact hb (congrFun hz j)))
    ((Ideal.Quotient.mkₐ F (linePreimageIdeal a b j g φ)).comp φ)
    (originalLine_ker_le a b j g hb φ)

/-- The complete original line/ambient quotient triangle commutes. -/
theorem originalLineHom_comp :
    (originalLineHom a b j g hb φ).comp (principalLineHom a b g) =
      (Ideal.Quotient.mkₐ F (linePreimageIdeal a b j g φ)).comp φ :=
  AlgHom.liftOfSurjective_comp _ _ _ _

/-- Every original localized ambient element retains its actual original quotient class. -/
theorem originalLineHom_principalLineHom (r : Localization.Away g) :
    originalLineHom a b j g hb φ (principalLineHom a b g r) =
      Ideal.Quotient.mk (linePreimageIdeal a b j g φ) (φ r) :=
  congrArg (fun f : Localization.Away g →ₐ[F] B ⧸ linePreimageIdeal a b j g φ => f r)
    (originalLineHom_comp a b j g hb φ)

/-- The full original line-preimage ideal is the true extended localized kernel, without a radical. -/
theorem linePreimageIdeal_eq_surjectiveBaseChange :
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := φ.toRingHom.toAlgebra
    SurjectiveBaseChange.ideal (Localization.Away g) (OpenLineRing (subst a b g)) B =
      linePreimageIdeal a b j g φ := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  change (RingHom.ker (principalLineHom a b g).toRingHom).map φ.toRingHom = _
  rw [ker_principalLineHom a b j g hb, Ideal.map_map]

/-- The literal scalar tensor pullback is the entire original unreduced line quotient. -/
def lineTensorPullbackEquiv :
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := φ.toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    OpenLineRing (subst a b g) ⊗[Localization.Away g] B ≃ₐ[OpenLineRing (subst a b g)]
      B ⧸ linePreimageIdeal a b j g φ := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let hs := principalLineHom_surjective a b g (by intro hz; exact hb (congrFun hz j))
  let e := (SurjectiveBaseChange.quotientRingEquiv (Localization.Away g)
      (OpenLineRing (subst a b g)) B hs).symm.trans
    (Ideal.quotientEquivAlgOfEq F (linePreimageIdeal_eq_surjectiveBaseChange a b j g hb φ)).toRingEquiv
  have he (z : B) : e (1 ⊗ₜ[Localization.Away g] z) =
      Ideal.Quotient.mk (linePreimageIdeal a b j g φ) z := by
    change Ideal.quotientEquivAlgOfEq F (linePreimageIdeal_eq_surjectiveBaseChange a b j g hb φ)
      ((SurjectiveBaseChange.quotientRingEquiv (Localization.Away g)
        (OpenLineRing (subst a b g)) B hs).symm (1 ⊗ₜ[Localization.Away g] z)) = _
    rw [← SurjectiveBaseChange.quotientRingEquiv_mk (Localization.Away g)
      (OpenLineRing (subst a b g)) B hs z, RingEquiv.symm_apply_apply]
    rfl
  refine { e with commutes' := fun c => ?_ }
  obtain ⟨r, rfl⟩ := hs c
  change e (algebraMap _ _ (principalLineHom a b g r)) =
    originalLineHom a b j g hb φ (principalLineHom a b g r)
  rw [originalLineHom_principalLineHom]
  have ht : algebraMap (OpenLineRing (subst a b g))
      (OpenLineRing (subst a b g) ⊗[Localization.Away g] B) (principalLineHom a b g r) =
      1 ⊗ₜ[Localization.Away g] φ r :=
    Algebra.TensorProduct.tmul_one_eq_one_tmul r
  rw [ht, he]

/-- The literal tensor comparison retains every original element of the unreduced preimage. -/
@[simp] theorem lineTensorPullbackEquiv_one_tmul (z : B) :
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := φ.toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    lineTensorPullbackEquiv a b j g hb φ (1 ⊗ₜ[Localization.Away g] z) =
      Ideal.Quotient.mk (linePreimageIdeal a b j g φ) z := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let hs := principalLineHom_surjective a b g (by intro hz; exact hb (congrFun hz j))
  change Ideal.quotientEquivAlgOfEq F (linePreimageIdeal_eq_surjectiveBaseChange a b j g hb φ)
    ((SurjectiveBaseChange.quotientRingEquiv (Localization.Away g)
      (OpenLineRing (subst a b g)) B hs).symm (1 ⊗ₜ[Localization.Away g] z)) = _
  rw [← SurjectiveBaseChange.quotientRingEquiv_mk (Localization.Away g)
    (OpenLineRing (subst a b g)) B hs z, RingEquiv.symm_apply_apply]
  rfl

/-- Both whole original-element directions of the actual tensor comparison are explicit. -/
@[simp] theorem lineTensorPullbackEquiv_symm_mk (z : B) :
    letI := (principalLineHom a b g).toRingHom.toAlgebra
    letI := φ.toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    (lineTensorPullbackEquiv a b j g hb φ).symm
      (Ideal.Quotient.mk (linePreimageIdeal a b j g φ) z) = 1 ⊗ₜ[Localization.Away g] z := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  apply (lineTensorPullbackEquiv a b j g hb φ).injective
  rw [AlgEquiv.apply_symm_apply, lineTensorPullbackEquiv_one_tmul]

/-- The whole normalized-product coefficient map factors through the entire original unreduced pullback. -/
theorem normalizedLineProductHom_eq_originalNormalization_comp :
    (normalizedLineProductHom a b j g hb φ).toRingHom =
      (ReducedComponents.originalNormalizationMap (linePreimageIdeal a b j g φ)).comp
        (originalLineHom a b j g hb φ).toRingHom := by
  apply RingHom.ext
  intro c
  obtain ⟨r, rfl⟩ := principalLineHom_surjective a b g (by intro hz; exact hb (congrFun hz j)) c
  rw [RingHom.comp_apply]
  change normalizedLineProductHom a b j g hb φ (principalLineHom a b g r) =
    ReducedComponents.originalNormalizationMap _ (originalLineHom a b j g hb φ (principalLineHom a b g r))
  rw [originalLineHom_principalLineHom, normalizedLineProductHom_principalLineHom]
  rfl

/-- Actual original module finiteness passes to the whole unreduced line pullback. -/
theorem originalLineHom_finite (hφ : φ.toRingHom.Finite) :
    (originalLineHom a b j g hb φ).toRingHom.Finite := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  have : Module.Finite (Localization.Away g) B := hφ
  exact Module.Finite.equiv (lineTensorPullbackEquiv a b j g hb φ).toLinearEquiv

/-- Actual original free modules, with their true coefficient action, remain free on the unreduced line pullback. -/
theorem originalLineHom_free
    (hfree : letI := φ.toRingHom.toAlgebra; Module.Free (Localization.Away g) B) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    Module.Free (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ) := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  have : Module.Free (Localization.Away g) B := hfree
  exact Module.Free.of_equiv (lineTensorPullbackEquiv a b j g hb φ).toLinearEquiv

/-- Actual original étaleness passes to the literal whole line pullback. -/
theorem originalLineHom_etale
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale (Localization.Away g) B) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    Algebra.Etale (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ) := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  have : Algebra.Etale (Localization.Away g) B := het
  exact Algebra.Etale.of_equiv (lineTensorPullbackEquiv a b j g hb φ)

/-- Actual natural-valued `Module.finrank` is retained by the unreduced free line pullback; the infinite-rank convention is zero. -/
theorem originalLineHom_finrank (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hfree : letI := φ.toRingHom.toAlgebra; Module.Free (Localization.Away g) B) :
    letI := φ.toRingHom.toAlgebra
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    Module.finrank (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ) =
      Module.finrank (Localization.Away g) B := by
  let := (principalLineHom a b g).toRingHom.toAlgebra
  let := φ.toRingHom.toAlgebra
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers g) (Localization.Away g)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hg))
  have : IsDomain (OpenLineRing (subst a b g)) := openLineRing_isDomain _ hline
  have : Module.Free (Localization.Away g) B := hfree
  change Module.finrank (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ) = _
  rw [← (lineTensorPullbackEquiv a b j g hb φ).toLinearEquiv.finrank_eq,
    Module.finrank_baseChange]

/-- Genuine original étaleness, not a reducedness witness, makes the entire nonempty open-line pullback reduced. -/
theorem originalLineQuotient_isReduced_of_etale (hline : subst a b g ≠ 0)
    (het : letI := φ.toRingHom.toAlgebra; Algebra.Etale (Localization.Away g) B) :
    IsReduced (B ⧸ linePreimageIdeal a b j g φ) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  have : IsDomain (OpenLineRing (subst a b g)) := openLineRing_isDomain _ hline
  have : Algebra.Etale (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ) :=
    originalLineHom_etale a b j g hb φ het
  exact isReduced_of_etale_of_domain (OpenLineRing (subst a b g)) _

end EnvelopeProperty.AffineLine
