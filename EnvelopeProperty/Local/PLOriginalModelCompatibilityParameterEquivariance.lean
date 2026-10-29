import EnvelopeProperty.Local.PLOriginalModelCompatibilityParameterAction
import EnvelopeProperty.Local.PLOriginalModelCompatibilityGmCartierFactors

/-! # The unchanged original normalized parameter map is genuinely equivariant -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.ProjBerk
open PLOriginalModelCompatibilityParameterAction
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}
variable (K : HomogeneousIdeal (ProjectiveGrading k n))
variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] n))

/-- The actual coordinate blowup's unchanged original ordinary parameter map. -/
def nativeClosedBlowupParameterStructure :
    (nativeClosedProductIdeal K I J).blowUp ⟶ Spec (CommRingCat.of k[X]) :=
  (nativeClosedProductIdeal K I J).blowUpπ ≫
    (nativeConstantIdeal K).subschemeι ≫ nativeStructureMap

/-- The actual coordinate parameter map is a morphism over the original field. -/
def nativeClosedBlowupParameterOver :
    nativeClosedBlowupAsOver K I J ⟶ nativeParameterLine k :=
  Over.homMk (nativeClosedBlowupParameterStructure K I J) (by
    dsimp only [nativeClosedBlowupParameterStructure, nativeClosedBlowupAsOver,
      nativeClosedBlowupBaseStructure, nativeClosedBaseStructure]
    simp only [Category.assoc]
    rfl)

omit I J in
/-- The entire closed parameter-family map retains its actual parameter square. -/
theorem nativeClosedParameterFamilyMap_parameter {S : Type u} [CommRing S]
    (f : k →+* S) (a : Sˣ) :
    nativeClosedParameterFamilyMap K f a ≫
        (nativeConstantIdeal K).subschemeι ≫ nativeStructureMap =
      (nativeConstantIdeal (K.map (coefficientGradedMap f))).subschemeι ≫
        nativeStructureMap ≫ Spec.map (CommRingCat.ofHom (parameterUnitBaseChangeHom f a)) := by
  rw [nativeClosedParameterFamilyMap_ι_assoc]
  change _ ≫ nativeCoefficientMap (parameterUnitBaseChangeHom f a) ≫ nativeStructureMap = _
  rw [nativeCoefficientMap_over_base]

variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

/-- The actual coordinate blowup action covers the actual standard action
on the unchanged original ordinary parameter line. -/
theorem nativeClosedBlowupParameterOver_isModHom :
    letI := nativeClosedProductIdealGmModObj K I J hI hJ
    letI := nativeParameterLineModObj k
    IsModHom (nativeMultiplicativeGroup k) (nativeClosedBlowupParameterOver K I J) := by
  let : ModObj (nativeMultiplicativeGroup k) (nativeClosedBlowupAsOver K I J) :=
    nativeClosedProductIdealGmModObj K I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k) (nativeParameterLine k) :=
    nativeParameterLineModObj k
  let E := nativeClosedBlowupFamilyProductIso K I J LaurentPolynomial.C
  let σ := pullbackSymmetry (nativeMultiplicativeGroup k).hom
    (nativeClosedBlowupBaseStructure K I J)
  let F := E.hom ≫ σ.inv
  let q := pullback.snd (nativeClosedProductIdeal K I J).blowUpπ
      (nativeClosedParameterFamilyMap K LaurentPolynomial.C 1) ≫
    (nativeConstantIdeal (K.map (coefficientGradedMap
      (LaurentPolynomial.C : k →+* k[T;T⁻¹])))).subschemeι ≫ nativeStructureMap
  let p := nativeClosedBlowupParameterOver K I J
  have hFa : F ≫ (nativeClosedProductIdealGmSmul K I J hI hJ).left =
      nativeClosedProductIdealFamilyLift K I J hI hJ
        LaurentPolynomial.C (parameterLaurentUnit k) := by
    simp only [F, E, σ, nativeClosedProductIdealGmSmul, Over.homMk_left,
      nativeClosedProductIdealGmAction, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc]
  have hFp : F ≫ (nativeMultiplicativeGroup k ◁ p).left =
      q ≫ (PLOriginalModelCompatibilityParameterAction.nativeParameterProductIso k).hom := by
    have h1 : ((nativeClosedBlowupFamilyProductIso K I J LaurentPolynomial.C).hom ≫
        (pullbackSymmetry (nativeMultiplicativeGroup k).hom
          (nativeClosedBlowupBaseStructure K I J)).inv) ≫
        pullback.fst (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure K I J) =
        pullback.snd (nativeClosedProductIdeal K I J).blowUpπ
          (nativeClosedParameterFamilyMap K LaurentPolynomial.C 1) ≫
          nativeClosedBaseStructure (K.map (coefficientGradedMap
            (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) := by
      rw [Category.assoc, pullbackSymmetry_inv_comp_fst]
      exact nativeClosedBlowupFamilyProductIso_hom_snd K I J LaurentPolynomial.C
    have h2 : ((nativeClosedBlowupFamilyProductIso K I J LaurentPolynomial.C).hom ≫
        (pullbackSymmetry (nativeMultiplicativeGroup k).hom
          (nativeClosedBlowupBaseStructure K I J)).inv) ≫
        pullback.snd (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure K I J) =
        pullback.fst (nativeClosedProductIdeal K I J).blowUpπ
          (nativeClosedParameterFamilyMap K LaurentPolynomial.C 1) := by
      rw [Category.assoc, pullbackSymmetry_inv_comp_snd]
      exact nativeClosedBlowupFamilyProductIso_hom_fst K I J LaurentPolynomial.C
    apply pullback.hom_ext
    · rw [Category.assoc, Over.whiskerLeft_left_fst]
      refine h1.trans ?_
      rw [Category.assoc, PLOriginalModelCompatibilityParameterAction.nativeParameterProductIso_fst]
      simp only [q, nativeClosedBaseStructure, Category.assoc]
    · rw [Category.assoc, Over.whiskerLeft_left_snd]
      calc
        _ = pullback.fst (nativeClosedProductIdeal K I J).blowUpπ
            (nativeClosedParameterFamilyMap K LaurentPolynomial.C 1) ≫
              nativeClosedBlowupParameterStructure K I J :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun x => x ≫ nativeClosedBlowupParameterStructure K I J) h2)
        _ = pullback.snd (nativeClosedProductIdeal K I J).blowUpπ
            (nativeClosedParameterFamilyMap K LaurentPolynomial.C 1) ≫
              nativeClosedParameterFamilyMap K LaurentPolynomial.C 1 ≫
                (nativeConstantIdeal K).subschemeι ≫ nativeStructureMap := by
          dsimp only [nativeClosedBlowupParameterStructure]
          rw [pullback.condition_assoc]
        _ = q ≫ Spec.map (CommRingCat.ofHom
            (Polynomial.mapRingHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) := by
          rw [nativeClosedParameterFamilyMap_parameter,
            parameterUnitBaseChangeHom_one]
          rfl
        _ = _ := (congrArg (fun x => q ≫ x)
          (PLOriginalModelCompatibilityParameterAction.nativeParameterProductIso_snd k)).symm.trans
            (Category.assoc _ _ _).symm
  have hlift : nativeClosedProductIdealFamilyLift K I J hI hJ LaurentPolynomial.C
      (parameterLaurentUnit k) ≫ nativeClosedBlowupParameterStructure K I J =
      q ≫ Spec.map (CommRingCat.ofHom (parameterLaurentHom (R := k))) := by
    rw [nativeClosedBlowupParameterStructure, nativeClosedProductIdealFamilyLift_π_assoc,
      nativeClosedParameterFamilyMap_parameter]
    simp only [q, Category.assoc]
    rfl
  have hleft : F ≫ (nativeClosedProductIdealGmSmul K I J hI hJ).left ≫ p.left =
      q ≫ Spec.map (CommRingCat.ofHom (parameterLaurentHom (R := k))) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ p.left) hFa).trans hlift)
  constructor
  apply Over.OverMorphism.ext
  apply (cancel_epi F).mp
  change F ≫ ((nativeClosedProductIdealGmSmul K I J hI hJ).left ≫ p.left) =
    F ≫ ((nativeMultiplicativeGroup k ◁ p).left ≫
      (ModObj.smul (M := nativeMultiplicativeGroup k) (X := nativeParameterLine k)).left)
  calc F ≫ ((nativeClosedProductIdealGmSmul K I J hI hJ).left ≫ p.left)
      = q ≫ Spec.map (CommRingCat.ofHom (parameterLaurentHom (R := k))) := hleft
    _ = q ≫ ((PLOriginalModelCompatibilityParameterAction.nativeParameterProductIso k).hom ≫
          (ModObj.smul (M := nativeMultiplicativeGroup k) (X := nativeParameterLine k)).left) :=
        congrArg (fun x => q ≫ x)
          (PLOriginalModelCompatibilityParameterAction.nativeParameterProductIso_smul k).symm
    _ = (q ≫ (PLOriginalModelCompatibilityParameterAction.nativeParameterProductIso k).hom) ≫
          (ModObj.smul (M := nativeMultiplicativeGroup k) (X := nativeParameterLine k)).left :=
        (Category.assoc _ _ _).symm
    _ = (F ≫ (nativeMultiplicativeGroup k ◁ p).left) ≫
          (ModObj.smul (M := nativeMultiplicativeGroup k) (X := nativeParameterLine k)).left :=
        congrArg (fun x => x ≫
          (ModObj.smul (M := nativeMultiplicativeGroup k)
              (X := nativeParameterLine k)).left) hFp.symm
    _ = F ≫ ((nativeMultiplicativeGroup k ◁ p).left ≫
          (ModObj.smul (M := nativeMultiplicativeGroup k) (X := nativeParameterLine k)).left) :=
        Category.assoc _ _ _

end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] M))

/-- The simultaneous model's literal original parameter map over the original field. -/
def simultaneousNativeParameterOver :
    X.simultaneousIdealBlowupAsOver I J ⟶ nativeParameterLine k :=
  Over.homMk (X.simultaneousIdealBlowupStructure (X.nativeProductIdeal I)
    (X.nativeProductIdeal J)) (by
      simp only [simultaneousIdealBlowupAsOver, simultaneousIdealBlowupStructure, Over.mk_hom,
        Category.assoc]; rfl)

variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

/-- The chosen actual simultaneous-model action covers the actual standard
ordinary-parameter action through its unchanged original structure map. -/
theorem simultaneousNativeParameterOver_isModHom :
    letI := X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
    letI := nativeParameterLineModObj k
    IsModHom (nativeMultiplicativeGroup k) (X.simultaneousNativeParameterOver I J) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J) :=
    nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k) (nativeParameterLine k) :=
    nativeParameterLineModObj k
  let e := (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose
  let : IsModHom (nativeMultiplicativeGroup k) e.hom :=
    X.simultaneousNativeCoordinateIso_isModHom I J hI hJ
  let : IsModHom (nativeMultiplicativeGroup k) e.inv := inferInstance
  let p := nativeClosedBlowupParameterOver X.nativeHomogeneousIdeal I J
  let : IsModHom (nativeMultiplicativeGroup k) p :=
    nativeClosedBlowupParameterOver_isModHom X.nativeHomogeneousIdeal I J hI hJ
  have he : e.hom ≫ X.simultaneousNativeParameterOver I J = p := by
    apply Over.OverMorphism.ext
    change e.hom.left ≫ X.simultaneousIdealBlowupProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) ≫ X.nativeProductStructure =
      (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫ nativeStructureMap
    rw [← Category.assoc,
      (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose_spec,
      Category.assoc, X.nativeConstantFamilyModelIso_over_base]
  have hi : e.inv ≫ p = X.simultaneousNativeParameterOver I J := by
    rw [← he, Iso.inv_hom_id_assoc]
  have h : IsModHom (nativeMultiplicativeGroup k) (e.inv ≫ p) := inferInstance
  simpa only [hi] using h

variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The same actual normalized projection covers the genuine standard
action on the original ordinary parameter line. -/
theorem normalizedSimultaneousNativeParameterOver_isModHom :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    letI := nativeParameterLineModObj k
    IsModHom (nativeMultiplicativeGroup k)
      (structureOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) := by
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  let : ModObj (nativeMultiplicativeGroup k) (nativeParameterLine k) :=
    nativeParameterLineModObj k
  let : IsModHom (nativeMultiplicativeGroup k)
      (X.normalizedSimultaneousNativeOverProjection I J hfin) :=
    X.normalizedSimultaneousNativeOverProjection_isModHom I J hI hJ hfin
  let : IsModHom (nativeMultiplicativeGroup k) (X.simultaneousNativeParameterOver I J) :=
    X.simultaneousNativeParameterOver_isModHom I J hI hJ
  have hp : X.normalizedSimultaneousNativeOverProjection I J hfin ≫
      X.simultaneousNativeParameterOver I J =
      structureOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) := by
    apply Over.OverMorphism.ext
    rfl
  have h : IsModHom (nativeMultiplicativeGroup k)
      (X.normalizedSimultaneousNativeOverProjection I J hfin ≫
        X.simultaneousNativeParameterOver I J) := inferInstance
  simpa only [hp] using h

end EnvelopeProperty.ProjSubvariety
