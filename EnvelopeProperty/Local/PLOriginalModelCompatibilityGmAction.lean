import EnvelopeProperty.Local.PLIdealGmCategoricalModels
import EnvelopeProperty.Local.PLIdealNormalizedModels
import EnvelopeProperty.Berkovich.NormalizationMultiplicativeAction
import EnvelopeProperty.Global.NativeTestConfigurationData

/-! # The genuine action on the same original normalized simultaneous PL model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.PLOriginalModelCompatibility
variable {C : Type*} [Category C] [MonoidalCategory C] (G : C) [MonObj G]

/-- Transporting a module structure along an isomorphism `e : N ≅ N'` (with the identity on
the monoid) makes `e.inv ≫ p` equivariant whenever `p` is. -/
theorem isModHom_ofIso_inv_comp {N N' B : C} [ModObj G N] [ModObj G B] (e : N ≅ N')
    (p : N ⟶ B) [IsMonHom (Iso.refl G).hom] [IsModHom G p] :
    letI := ModObj.ofIso (Iso.refl G) e
    IsModHom G (e.inv ≫ p) := by
  let := ModObj.ofIso (Iso.refl G) e
  constructor
  rw [ModObj.ofIso_smul]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, IsModHom.smul_hom, Iso.refl_inv]
  simp

/-- Transport of a module structure along an isomorphism makes the isomorphism equivariant. -/
theorem isModHom_ofIso_hom {N N' : C} [ModObj G N] (e : N ≅ N')
    [IsMonHom (Iso.refl G).hom] :
    letI := ModObj.ofIso (Iso.refl G) e
    IsModHom G e.hom := by
  let := ModObj.ofIso (Iso.refl G) e
  constructor
  rw [ModObj.ofIso_smul]
  simp

end EnvelopeProperty.PLOriginalModelCompatibility

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] M))
variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

/-- Universal invariance of the two original homogeneous ideals constructs
the actual categorical action on the original simultaneous blowup. -/
@[instance_reducible]
def simultaneousIdealBlowupNativeGmModObj :
    ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J) :=
    nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I J hI hJ
  let e := (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose
  let : IsMonHom (Iso.refl (nativeMultiplicativeGroup k)).hom :=
    inferInstanceAs (IsMonHom (𝟙 (nativeMultiplicativeGroup k)))
  exact ModObj.ofIso (Iso.refl _) e

variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

omit hI hJ in
/-- The canonical original normalization projection over the same original
coefficient field, between the literal unchanged original total objects. -/
def normalizedSimultaneousNativeOverProjection :
    totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) ⟶
      X.simultaneousIdealBlowupAsOver I J :=
  Over.homMk (X.normalizedSimultaneousIdealBlowupProjection
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) (by
      simp only [simultaneousIdealBlowupAsOver, totalOver, Over.mk_hom,
        normalizedSimultaneousIdealBlowupStructure, simultaneousIdealBlowupStructure,
        Category.assoc]; rfl)

omit hI hJ in
private def normalizedSimultaneousNormalizationOverIso :
    letI : IsIntegral (X.simultaneousIdealBlowupAsOver I J).left :=
      X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
        (hfin X.triv).1 (hfin X.triv).2
    Over.mk (IntegralSchemeNormalization.projection
      (X.simultaneousIdealBlowupAsOver I J).left ≫
        (X.simultaneousIdealBlowupAsOver I J).hom) ≅
      totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowupAsOver I J).left :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
      (hfin X.triv).1 (hfin X.triv).2
  refine Over.isoMk (Iso.refl _) ?_
  simp only [simultaneousIdealBlowupAsOver, totalOver, Over.mk_hom, Iso.refl_hom,
    normalizedSimultaneousIdealBlowupStructure, simultaneousIdealBlowupStructure,
    normalizedSimultaneousIdealBlowupProjection, Category.id_comp, Category.assoc]
  rfl

omit hI hJ in
private theorem normalizedSimultaneousNormalizationOverIso_projection :
    letI : IsIntegral (X.simultaneousIdealBlowupAsOver I J).left :=
      X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
        (hfin X.triv).1 (hfin X.triv).2
    (X.normalizedSimultaneousNormalizationOverIso I J hfin).hom ≫
        X.normalizedSimultaneousNativeOverProjection I J hfin =
      Over.homMk (IntegralSchemeNormalization.projection
        (X.simultaneousIdealBlowupAsOver I J).left) rfl := by
  let : IsIntegral (X.simultaneousIdealBlowupAsOver I J).left :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
      (hfin X.triv).1 (hfin X.triv).2
  apply Over.OverMorphism.ext
  exact Category.id_comp _

/-- The true original ideal invariance constructs an action on the same
original normalized simultaneous model, with its literal original structure
map. Normal-product geometry, dominant lift, unit and associativity are
supplied by the proved generic normalization action, not by input fields. -/
@[instance_reducible]
def normalizedSimultaneousNativeGmModObj :
    ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) := by
  let : IsIntegral (X.simultaneousIdealBlowupAsOver I J).left :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
      (hfin X.triv).1 (hfin X.triv).2
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k)
      (Over.mk (IntegralSchemeNormalization.projection
        (X.simultaneousIdealBlowupAsOver I J).left ≫
          (X.simultaneousIdealBlowupAsOver I J).hom)) :=
    IntegralSchemeNormalization.normalizationMultiplicativeModObj
      (X.simultaneousIdealBlowupAsOver I J)
  let : IsMonHom (Iso.refl (nativeMultiplicativeGroup k)).hom :=
    inferInstanceAs (IsMonHom (𝟙 (nativeMultiplicativeGroup k)))
  exact ModObj.ofIso (Iso.refl _)
    (X.normalizedSimultaneousNormalizationOverIso I J hfin)

/-- The literal original normalization projection is equivariant for the
constructed actual actions, through its unchanged original scheme morphism. -/
theorem normalizedSimultaneousNativeOverProjection_isModHom :
    letI := X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    IsModHom (nativeMultiplicativeGroup k)
      (X.normalizedSimultaneousNativeOverProjection I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowupAsOver I J).left :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
      (hfin X.triv).1 (hfin X.triv).2
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let B := X.simultaneousIdealBlowupAsOver I J
  let N := Over.mk (IntegralSchemeNormalization.projection B.left ≫ B.hom)
  let : ModObj (nativeMultiplicativeGroup k) N :=
    IntegralSchemeNormalization.normalizationMultiplicativeModObj B
  let e : N ≅ totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) :=
    X.normalizedSimultaneousNormalizationOverIso I J hfin
  let p : N ⟶ B := Over.homMk (IntegralSchemeNormalization.projection B.left) rfl
  have he : e.hom ≫ X.normalizedSimultaneousNativeOverProjection I J hfin = p :=
    X.normalizedSimultaneousNormalizationOverIso_projection I J hfin
  have hi : e.inv ≫ p = X.normalizedSimultaneousNativeOverProjection I J hfin := by
    rw [← he, Iso.inv_hom_id_assoc]
  let : IsModHom (nativeMultiplicativeGroup k) p :=
    ⟨IntegralSchemeNormalization.normalizationMultiplicativeModObj_projection B⟩
  let : IsMonHom (Iso.refl (nativeMultiplicativeGroup k)).hom :=
    inferInstanceAs (IsMonHom (𝟙 (nativeMultiplicativeGroup k)))
  rw [← hi]
  exact PLOriginalModelCompatibility.isModHom_ofIso_inv_comp (nativeMultiplicativeGroup k) e p

end EnvelopeProperty.ProjSubvariety
