/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.LineTensorPullback
import EnvelopeProperty.GenericNormalizationProduct
import EnvelopeProperty.QuotientNormalizationProduct
import EnvelopeProperty.ScalarTensorExt

/-!
# The actual original line quotient and the whole generic normalization map

Every component of the literal original line quotient inherits the genuine
injective line action. Its true normalization-product comparison preserves that
whole action and every original function. Genuine generic reducedness, or actual
etaleness on a nonzero line open, then makes the CANONICAL original normalization
map generically bijective. The actual finite free normalized line rank equals
the ORIGINAL generic line degree. Ambient original-degree comparison and an
isomorphism on a nonzero line open remain separate producers.
-/

open scoped TensorProduct Polynomial
noncomputable section
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u
namespace EnvelopeProperty.AffineLine
open ReducedComponents
variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B)

/-- The original quotient component comparison preserves every coefficient of the actual descended line action. -/
theorem lineQuotientComponentEquiv_commutes
    (p : Index (linePreimageIdeal a b j g φ))
    (c : OpenLineRing (subst a b g)) :
    quotientComponentEquiv (linePreimageIdeal a b j g φ) p
      (Ideal.Quotient.mk (quotientIndexEquiv (linePreimageIdeal a b j g φ) p).1
        (originalLineHom a b j g hb φ c)) =
      componentLineHom a b j g hb φ p.1 p.2 c := by
  obtain ⟨r, rfl⟩ := principalLineHom_surjective a b g
    (by intro hz; exact hb (congrFun hz j)) c
  rw [originalLineHom_principalLineHom, quotientComponentEquiv_mk_mk,
    componentLineHom_principalLineHom]

/-- Every genuine minimal component of the original unreduced line quotient dominates the actual line. -/
theorem originalLineQuotient_components_injective [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    ∀ q : Index (⊥ : Ideal (B ⧸ linePreimageIdeal a b j g φ)),
      Function.Injective (algebraMap (OpenLineRing (subst a b g)) (Component ⊥ q)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  intro q
  obtain ⟨p, rfl⟩ := (quotientIndexEquiv (linePreimageIdeal a b j g φ)).surjective q
  intro c d he
  apply componentLineHom_injective a b j g hb φ p.1 p.2 hg hline hφ hiφ
  have he' := congrArg (quotientComponentEquiv (linePreimageIdeal a b j g φ) p) he
  change quotientComponentEquiv (linePreimageIdeal a b j g φ) p
      (Ideal.Quotient.mk (quotientIndexEquiv (linePreimageIdeal a b j g φ) p).1
        (originalLineHom a b j g hb φ c)) =
    quotientComponentEquiv (linePreimageIdeal a b j g φ) p
      (Ideal.Quotient.mk (quotientIndexEquiv (linePreimageIdeal a b j g φ) p).1
        (originalLineHom a b j g hb φ d)) at he'
  simpa only [lineQuotientComponentEquiv_commutes] using he'

/-- The original unreduced quotient acts on the actual normalized product compatibly with the entire descended line action. -/
theorem normalizedLineProduct_quotient_tower :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    letI := normalizationProductQuotientAlgebra (linePreimageIdeal a b j g φ)
    IsScalarTower (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ)
      (NormalizationProduct (linePreimageIdeal a b j g φ)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  let := normalizationProductQuotientAlgebra (linePreimageIdeal a b j g φ)
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (congrArg (fun f => f c)
    (normalizedLineProductHom_eq_originalNormalization_comp a b j g hb φ)).symm

/-- The genuine quotient normalization comparison preserves the actual whole line coefficient action. -/
def lineNormalizationProductQuotientEquiv :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    NormalizationProduct (⊥ : Ideal (B ⧸ linePreimageIdeal a b j g φ)) ≃ₐ[OpenLineRing (subst a b g)]
      NormalizationProduct (linePreimageIdeal a b j g φ) := by
  letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  letI := normalizationProductQuotientAlgebra (linePreimageIdeal a b j g φ)
  haveI := normalizedLineProduct_quotient_tower a b j g hb φ
  exact (normalizationProductQuotientEquivOverQuotient (linePreimageIdeal a b j g φ)).restrictScalars _

/-- This actual line comparison agrees with the original normalization map on every whole unreduced quotient element. -/
theorem lineNormalizationProductQuotientEquiv_quotient
    (q : B ⧸ linePreimageIdeal a b j g φ) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    lineNormalizationProductQuotientEquiv a b j g hb φ (normalizationMap ⊥ q) =
      originalNormalizationMap (linePreimageIdeal a b j g φ) q :=
  normalizationProductQuotientEquiv_quotient (linePreimageIdeal a b j g φ) q

/-- The original normalization homomorphism is genuinely an algebra map for the actual line action. -/
def originalLineNormalizationAlgHom :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    (B ⧸ linePreimageIdeal a b j g φ) →ₐ[OpenLineRing (subst a b g)]
      NormalizationProduct (linePreimageIdeal a b j g φ) :=
  letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  { originalNormalizationMap (linePreimageIdeal a b j g φ) with
    commutes' := fun c => (congrArg (fun f => f c)
      (normalizedLineProductHom_eq_originalNormalization_comp a b j g hb φ)).symm }

/-- The actual ORIGINAL line quotient and its actual normalized component product have genuinely identical generic algebras. -/
def originalLineGenericNormalizationEquiv [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (hred : letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
      IsReduced (FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
        (B ⧸ linePreimageIdeal a b j g φ))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
        (B ⧸ linePreimageIdeal a b j g φ) ≃ₐ[FractionRing (OpenLineRing (subst a b g))]
      FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
        NormalizationProduct (linePreimageIdeal a b j g φ) := by
  letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  letI := openLineRing_isDomain _ hline
  haveI : Module.Finite (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ) :=
    originalLineHom_finite a b j g hb φ hφ
  haveI := hred
  exact (genericNormalizationProductEquiv
    (originalLineQuotient_components_injective a b j g hb φ hg hline hφ hiφ)).trans
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : FractionRing (OpenLineRing (subst a b g)) ≃ₐ[FractionRing (OpenLineRing (subst a b g))]
        FractionRing (OpenLineRing (subst a b g)))
      (lineNormalizationProductQuotientEquiv a b j g hb φ))

/-- The genuine generic comparison retains EVERY whole original unreduced quotient function. -/
theorem originalLineGenericNormalizationEquiv_one_tmul [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (hred : letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
      IsReduced (FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
        (B ⧸ linePreimageIdeal a b j g φ)))
    (q : B ⧸ linePreimageIdeal a b j g φ) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    originalLineGenericNormalizationEquiv a b j g hb φ hg hline hφ hiφ hred (1 ⊗ₜ[_] q) =
      1 ⊗ₜ[_] originalNormalizationMap (linePreimageIdeal a b j g φ) q := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  let := openLineRing_isDomain _ hline
  have : Module.Finite (OpenLineRing (subst a b g)) (B ⧸ linePreimageIdeal a b j g φ) :=
    originalLineHom_finite a b j g hb φ hφ
  have := hred
  change Algebra.TensorProduct.congr
    (AlgEquiv.refl : FractionRing (OpenLineRing (subst a b g)) ≃ₐ[FractionRing (OpenLineRing (subst a b g))]
      FractionRing (OpenLineRing (subst a b g)))
    (lineNormalizationProductQuotientEquiv a b j g hb φ)
      (genericNormalizationProductEquiv
        (originalLineQuotient_components_injective a b j g hb φ hg hline hφ hiφ) (1 ⊗ₜ[_] q)) = _
  rw [genericNormalizationProductEquiv_one_tmul]
  change 1 ⊗ₜ[_] lineNormalizationProductQuotientEquiv a b j g hb φ (normalizationMap ⊥ q) = _
  rw [lineNormalizationProductQuotientEquiv_quotient]

/-- The constructed generic comparison is the CANONICAL base change of the entire original normalization map. -/
theorem originalLineGenericNormalizationEquiv_toAlgHom [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (hred : letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
      IsReduced (FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
        (B ⧸ linePreimageIdeal a b j g φ))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    (originalLineGenericNormalizationEquiv a b j g hb φ hg hline hφ hiφ hred).toAlgHom =
      Algebra.TensorProduct.map (AlgHom.id (FractionRing (OpenLineRing (subst a b g)))
        (FractionRing (OpenLineRing (subst a b g))))
        (originalLineNormalizationAlgHom a b j g hb φ) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  let := openLineRing_isDomain _ hline
  apply tensorAlgHom_ext_of_one_tmul
  intro q
  have hf : Algebra.TensorProduct.map
      (AlgHom.id (FractionRing (OpenLineRing (subst a b g))) (FractionRing (OpenLineRing (subst a b g))))
      (originalLineNormalizationAlgHom a b j g hb φ) (1 ⊗ₜ[_] q) =
      1 ⊗ₜ[_] originalNormalizationMap (linePreimageIdeal a b j g φ) q := by
    simp only [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  exact (originalLineGenericNormalizationEquiv_one_tmul a b j g hb φ hg hline hφ hiφ hred q).trans hf.symm

/-- The actual normalized line product's free rank is the ORIGINAL whole unreduced generic line degree. -/
theorem normalizedLineProduct_finrank_eq_original_generic [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (hred : letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
      IsReduced (FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
        (B ⧸ linePreimageIdeal a b j g φ))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    Module.finrank (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) =
      Module.finrank (FractionRing (OpenLineRing (subst a b g)))
        (FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
          (B ⧸ linePreimageIdeal a b j g φ)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  let := openLineRing_isDomain _ hline
  have : Module.Finite (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_finite a b j g hb φ hφ
  have : Module.Free (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_free a b j g hb φ hg hline hφ hiφ
  rw [← Module.finrank_baseChange (R := FractionRing (OpenLineRing (subst a b g))),
    (originalLineGenericNormalizationEquiv a b j g hb φ hg hline hφ hiφ hred).toLinearEquiv.finrank_eq]

/-- Genuine etaleness on an actual nonzero line open derives the canonical ORIGINAL normalization map's generic bijectivity. -/
theorem originalLineNormalization_generic_bijective_of_principal_etale
    [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (c : OpenLineRing (subst a b g)) (hc : c ≠ 0)
    (het : letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
      Algebra.Etale (Localization.Away c)
        (Localization.Away c ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id (FractionRing (OpenLineRing (subst a b g)))
        (FractionRing (OpenLineRing (subst a b g))))
        (originalLineNormalizationAlgHom a b j g hb φ)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  let := openLineRing_isDomain _ hline
  have := het
  have hred := generic_isReduced_of_principal_etale
    (R := B ⧸ linePreimageIdeal a b j g φ) c hc
  rw [← originalLineGenericNormalizationEquiv_toAlgHom a b j g hb φ hg hline hφ hiφ hred]
  exact (originalLineGenericNormalizationEquiv a b j g hb φ hg hline hφ hiφ hred).bijective

/-- The actual finite-free normalized line rank equals the ORIGINAL generic line degree from genuine etaleness on a nonzero line open. -/
theorem normalizedLineProduct_finrank_eq_original_generic_of_principal_etale
    [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (c : OpenLineRing (subst a b g)) (hc : c ≠ 0)
    (het : letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
      Algebra.Etale (Localization.Away c)
        (Localization.Away c ⊗[OpenLineRing (subst a b g)] (B ⧸ linePreimageIdeal a b j g φ))) :
    letI := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    Module.finrank (OpenLineRing (subst a b g)) (NormalizationProduct (linePreimageIdeal a b j g φ)) =
      Module.finrank (FractionRing (OpenLineRing (subst a b g)))
        (FractionRing (OpenLineRing (subst a b g)) ⊗[OpenLineRing (subst a b g)]
          (B ⧸ linePreimageIdeal a b j g φ)) := by
  let := (originalLineHom a b j g hb φ).toRingHom.toAlgebra
  let := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  let := openLineRing_isDomain _ hline
  have := het
  exact normalizedLineProduct_finrank_eq_original_generic a b j g hb φ hg hline hφ hiφ
    (generic_isReduced_of_principal_etale (R := B ⧸ linePreimageIdeal a b j g φ) c hc)

end EnvelopeProperty.AffineLine
