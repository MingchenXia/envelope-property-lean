import EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreOpens

/-! # The SAME entire residue tensor sections retain actual original scheme reduction and restrictions -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreReduction
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u

private theorem restrict_top {X Z : Scheme.{u}} (g : X ⟶ Z) (U : Z.Opens) :
    (g ∣_ U).appTop ≫ (g ⁻¹ᵁ U).topIso.hom =
      U.topIso.hom ≫ g.appLE U (g ⁻¹ᵁ U) le_rfl := by
  have e0 : g ⁻¹ᵁ U ≤ g ⁻¹ᵁ (U.ι ''ᵁ ⊤) := by rw [Scheme.Opens.ι_image_top]
  have h1 : (g ∣_ U).appTop = g.appLE (U.ι ''ᵁ ⊤) ((g ⁻¹ᵁ U).ι ''ᵁ ⊤) _ :=
    (Scheme.Hom.appLE_eq_app _).symm.trans (morphismRestrict_appLE g U ⊤ ⊤ le_rfl)
  rw [h1]
  change g.appLE (U.ι ''ᵁ ⊤) ((g ⁻¹ᵁ U).ι ''ᵁ ⊤) _ ≫
      X.presheaf.map (eqToHom (g ⁻¹ᵁ U).ι_image_top.symm).op =
    Z.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ g.appLE U (g ⁻¹ᵁ U) le_rfl
  rw [Scheme.Hom.appLE_map', Scheme.Hom.map_appLE]

private theorem nativeReductionNaturality {X Z : Scheme.{u}} (j : X ⟶ Z)
    {U V : Z.Opens} (i : U ⟶ V) (i₀ : j ⁻¹ᵁ U ⟶ j ⁻¹ᵁ V) (a : Γ(Z,V)) :
    j.appLE U (j ⁻¹ᵁ U) le_rfl (Z.presheaf.map i.op a) =
      X.presheaf.map i₀.op (j.appLE V (j ⁻¹ᵁ V) le_rfl a) := by
  have hm := ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE j (U := U) (U' := V) (V := j ⁻¹ᵁ U) le_rfl i.op) a
  have hr := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_map j (U := V) (V := j ⁻¹ᵁ V) (V' := j ⁻¹ᵁ U) le_rfl i₀.op) a
  exact hm.trans hr.symm

private theorem nativeTensorNaturality {R K A A' C D : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing A'] [CommRing C] [CommRing D]
    [Algebra R K] [Algebra R A] [Algebra R A'] [Algebra K C] [Algebra K D]
    (β : A →ₐ[R] A') (eA : K ⊗[R] A →ₐ[K] C) (eB : K ⊗[R] A' →ₐ[K] D)
    (r : C →ₐ[K] D) (he : ∀ a, eB ((1 : K) ⊗ₜ[R] β a) = r (eA ((1 : K) ⊗ₜ[R] a)))
    (b : K ⊗[R] A) :
    eB (Algebra.TensorProduct.map (AlgHom.id R K) β b) = r (eA b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add b c hb hc => rw [map_add, map_add, map_add, map_add, hb, hc]
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hA : c ⊗ₜ[R] a = c • ((1 : K) ⊗ₜ[R] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hB : c ⊗ₜ[R] β a = c • ((1 : K) ⊗ₜ[R] β a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hA, hB, map_smul, map_smul, map_smul, he]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
attribute [local instance] WittTwoResidue.reductionAlgebra
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
variable {U : Y.Opens} (hU : IsAffineOpen U)

/-- The SAME actual open-spectrum isomorphism preserves the original lifted-open projection. -/
theorem residueOpenIso_snd :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (WittTwoSpecialFibreOpens.residueOpenIso p k f hU).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Y,U) →ₐ[WittTwo.Ring p k]
        WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)).toRingHom) =
    (pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f ∣_ U) ≫ hU.isoSpec.hom := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  rw [WittTwoSpecialFibreOpens.residueOpenIso, Iso.trans_hom, Category.assoc,
    WittTwoAffineResidueGeometry.residueAffineIso_snd, ← Category.assoc,
    WittTwoSpecialFibreOpens.openFibreIso_snd]
  rfl

/-- EVERY original coefficient-one residue tensor has its literal ACTUAL scheme section reduction. -/
theorem residueOpenSections_tmul_one (a : Γ(Y,U)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    WittTwoSpecialFibreOpens.residueOpenSections p k f hU ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) =
    (pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f).appLE
      U (WittTwoSpecialFibreOpens.residueOpen p k f U) le_rfl a := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let B := WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)
  let e := WittTwoSpecialFibreOpens.residueOpenIso p k f hU
  let j := pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
  let V := WittTwoSpecialFibreOpens.residueOpen p k f U
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Y,U) →ₐ[WittTwo.Ring p k] B).toRingHom)) a
  have he : (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Y,U) →ₐ[WittTwo.Ring p k] B).toRingHom)).appTop ≫ e.hom.appTop =
      hU.isoSpec.hom.appTop ≫ (j ∣_ U).appTop :=
    congrArg (fun z => z.appTop) (residueOpenIso_snd p k f hU)
  have hv := ConcreteCategory.congr_hom he ((Scheme.ΓSpecIso Γ(Y,U)).inv a)
  have hi : hU.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(Y,U)).inv a) = U.topIso.inv a := by
    rw [IsAffineOpen.isoSpec_hom_appTop]
    exact congrArg (fun z => U.topIso.inv z) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(Y,U)) a)
  have ht := ConcreteCategory.congr_hom (restrict_top j U) (U.topIso.inv a)
  rw [WittTwoSpecialFibreOpens.residueOpenSections_value]
  exact (congrArg (fun z => V.topIso.hom (e.hom.appTop z)) hn).trans
    ((congrArg (fun z => V.topIso.hom z) (hv.trans (congrArg (fun z => (j ∣_ U).appTop z) hi))).trans
      (ht.trans (congrArg (fun z => j.appLE U V le_rfl z) (Iso.inv_hom_id_apply U.topIso a))))

/-- The original actual inclusion of the SAME global special-fibre inverse-image opens. -/
def residueInclusion {U V : Y.Opens} (i : U ⟶ V) :
    WittTwoSpecialFibreOpens.residueOpen p k f U ⟶ WittTwoSpecialFibreOpens.residueOpen p k f V :=
  homOfLE (fun _ hx => i.le hx)

/-- EVERY original whole residue tensor retains actual original scheme restriction. -/
theorem residueOpenSections_restrict {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : U ⟶ V) (b : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
      WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,V)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    WittTwoSpecialFibreOpens.residueOpenSections p k f hU
      (WittTwoAlgebraDivisionNaturality.residueMap p k
        (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i) b) =
    (WittTwoSpecialFibreOpens.specialFibre p k f).presheaf.map (residueInclusion p k f i).op
      (WittTwoSpecialFibreOpens.residueOpenSections p k f hV b) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let g := pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
  let j := pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra g (WittTwoSpecialFibreOpens.residueOpen p k f V)
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra g (WittTwoSpecialFibreOpens.residueOpen p k f U)
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  let r := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom g (residueInclusion p k f i)
  apply nativeTensorNaturality β
    (WittTwoSpecialFibreOpens.residueOpenSections p k f hV).toAlgHom
    (WittTwoSpecialFibreOpens.residueOpenSections p k f hU).toAlgHom r
  intro a
  exact (residueOpenSections_tmul_one p k f hU (β a)).trans
    ((nativeReductionNaturality j i (residueInclusion p k f i) a).trans
      (congrArg r (residueOpenSections_tmul_one p k f hV a)).symm)

end EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreReduction
