import EnvelopeProperty.Local.PLOriginalModelCompatibilityGmCartierFactors
import EnvelopeProperty.Local.PLNormalizedOriginalProjection
import EnvelopeProperty.Local.PLIdealNormalizedRatioPullback

/-! # The original normalized PL action fixes the same original variety projection -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

/-- The same whole parameter-family map is independent of its scale after
forgetting the parameter to the original native projective scheme. -/
theorem parameterFamily_forgets_scaling (f : R →+* S) (a : Sˣ) :
    nativeParameterFamilyMap (n := n) f a ≫ nativeCoefficientMap Polynomial.C =
      nativeParameterFamilyMap f 1 ≫ nativeCoefficientMap Polynomial.C := by
  rw [nativeParameterFamilyMap, nativeParameterFamilyMap, ← nativeCoefficientMap_comp,
    ← nativeCoefficientMap_comp]
  congr 1
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, parameterUnitBaseChangeHom_C]

variable (K : HomogeneousIdeal (ProjectiveGrading R n))

/-- The actual closed-family maps retain this equality on the entire
original ambient projective scheme, without reducing the original ideals. -/
theorem closedParameterFamily_forgets_scaling (f : R →+* S) (a : Sˣ) :
    nativeClosedParameterFamilyMap K f a ≫ (nativeConstantIdeal K).subschemeι ≫
        nativeCoefficientMap Polynomial.C =
      nativeClosedParameterFamilyMap K f 1 ≫ (nativeConstantIdeal K).subschemeι ≫
        nativeCoefficientMap Polynomial.C := by
  rw [← Category.assoc, nativeClosedParameterFamilyMap_ι,
    ← Category.assoc, nativeClosedParameterFamilyMap_ι]
  rw [Category.assoc, Category.assoc, parameterFamily_forgets_scaling]

end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.PLOriginalModelCompatibility

variable {S : Scheme.{u}} (G : Over S) [MonObj G]
variable {A B : Over S} [ModObj G A] [ModObj G B] {Z : Scheme.{u}}

/-- An equivariant morphism pulls back the equality of the entire action
and projection after an unchanged original target morphism. -/
theorem invariantMorphism_comp (f : A ⟶ B) [IsModHom G f] (q : B.left ⟶ Z)
    (hq : (ModObj.smul (M := G) (X := B)).left ≫ q =
      pullback.snd G.hom B.hom ≫ q) :
    (ModObj.smul (M := G) (X := A)).left ≫ f.left ≫ q =
      pullback.snd G.hom A.hom ≫ f.left ≫ q := by
  have ha : (ModObj.smul (M := G) (X := A)).left ≫ f.left =
      (G ◁ f).left ≫ (ModObj.smul (M := G) (X := B)).left :=
    congrArg (fun a => a.left) (IsModHom.smul_hom (A := G) (f := f))
  rw [← Category.assoc, ha, Category.assoc, hq, ← Category.assoc,
    Over.whiskerLeft_left_snd, Category.assoc]

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

private theorem nativeClosedGmAction_originalAmbientProjection :
    nativeClosedProductIdealGmAction X.nativeHomogeneousIdeal I J hI hJ ≫
        (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
        nativeCoefficientMap Polynomial.C =
      pullback.fst (nativeClosedBlowupBaseStructure X.nativeHomogeneousIdeal I J)
        (nativeMultiplicativeGroup k).hom ≫
        (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
        nativeCoefficientMap Polynomial.C := by
  rw [nativeClosedProductIdealGmAction]
  simp only [Category.assoc]
  rw [nativeClosedProductIdealFamilyLift_π_assoc,
    closedParameterFamily_forgets_scaling X.nativeHomogeneousIdeal
      LaurentPolynomial.C (parameterLaurentUnit k), ← pullback.condition_assoc]
  apply (cancel_epi (nativeClosedBlowupFamilyProductIso
    X.nativeHomogeneousIdeal I J LaurentPolynomial.C).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (nativeClosedBlowupFamilyProductIso_hom_fst_assoc X.nativeHomogeneousIdeal I J
    LaurentPolynomial.C _).symm

private theorem nativeClosedGmSmul_originalAmbientProjection :
    letI := nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I J hI hJ
    (ModObj.smul (M := nativeMultiplicativeGroup k)
      (X := nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J)).left ≫
        (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
        nativeCoefficientMap Polynomial.C =
      pullback.snd (nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J).hom ≫
        (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
        nativeCoefficientMap Polynomial.C := by
  change ((pullbackSymmetry (nativeMultiplicativeGroup k).hom
      (nativeClosedBlowupBaseStructure X.nativeHomogeneousIdeal I J)).hom ≫
    nativeClosedProductIdealGmAction X.nativeHomogeneousIdeal I J hI hJ) ≫ _ = _
  simp only [Category.assoc]
  rw [X.nativeClosedGmAction_originalAmbientProjection I J hI hJ,
    pullbackSymmetry_hom_comp_fst_assoc]
  rfl

omit hI hJ in
private theorem simultaneousOriginalProjection_eq :
    X.simultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) =
      X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) ≫
        X.nativeProductOriginalProjection := by
  dsimp only [simultaneousOriginalProjection, nativeProductModelIso, Iso.trans_hom,
    nativeStructure, nativeProductOriginalProjection, nativeInclusion]
  simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst]
  erw [pullbackSymmetry_hom_comp_fst]

omit hI hJ in
private theorem nativeCoordinateIso_originalAmbientProjection :
    (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose.hom.left ≫
        X.simultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) ≫
        X.nativeInclusion =
      (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
        (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
        nativeCoefficientMap Polynomial.C := by
  rw [X.simultaneousOriginalProjection_eq I J]
  simp only [Category.assoc]
  rw [X.nativeProductOriginalProjection_inclusion]
  rw [← Category.assoc, ← Category.assoc,
    (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose_spec]
  simp only [Category.assoc]
  rw [X.nativeConstantFamilyModelIso_hom_inclusion_assoc]
  change _ ≫ (nativeConstantIdeal X.nativeHomogeneousIdeal).subschemeι ≫
    (nativeCoefficientBaseChangeIso (n := M) Polynomial.C).hom ≫ _ = _
  rw [nativeCoefficientBaseChangeIso_hom_fst]

/-- The actual original simultaneous blowup action fixes its literal
projection to the original variety, on the whole original group product. -/
theorem simultaneousNativeOriginalProjection_invariant :
    letI := X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
    let B := X.simultaneousIdealBlowupAsOver I J
    (ModObj.smul (M := nativeMultiplicativeGroup k) (X := B)).left ≫
        X.simultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) =
      pullback.snd (nativeMultiplicativeGroup k).hom B.hom ≫
        X.simultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J) :=
    nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let e := (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose
  let : IsModHom (nativeMultiplicativeGroup k) e.hom :=
    X.simultaneousNativeCoordinateIso_isModHom I J hI hJ
  let : IsModHom (nativeMultiplicativeGroup k) e.inv := inferInstance
  let q := X.simultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J)
  have hq : (ModObj.smul (M := nativeMultiplicativeGroup k)
      (X := nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J)).left ≫ e.hom.left ≫ q =
      pullback.snd (nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J).hom ≫ e.hom.left ≫ q := by
    apply (cancel_mono X.nativeInclusion).mp
    simp only [Category.assoc]
    rw [show e.hom.left ≫ q ≫ X.nativeInclusion = _ from
      X.nativeCoordinateIso_originalAmbientProjection I J]
    exact X.nativeClosedGmSmul_originalAmbientProjection I J hI hJ
  have h := PLOriginalModelCompatibility.invariantMorphism_comp
    (nativeMultiplicativeGroup k) e.inv (e.hom.left ≫ q) hq
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ :=
    congrArg (fun f => f.left) e.inv_hom_id
  have hiq : e.inv.left ≫ e.hom.left ≫ q = q := by
    rw [← Category.assoc, hei, Category.id_comp]
  simpa only [hiq] using h

variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The same original normalization projection to the original variety is
fixed by the constructed actual action, as a whole morphism equality. -/
theorem normalizedSimultaneousNativeOriginalProjection_invariant :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    (ModObj.smul (M := nativeMultiplicativeGroup k) (X := N)).left ≫
        X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin =
      pullback.snd (nativeMultiplicativeGroup k).hom N.hom ≫
        X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin := by
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  let : IsModHom (nativeMultiplicativeGroup k)
      (X.normalizedSimultaneousNativeOverProjection I J hfin) :=
    X.normalizedSimultaneousNativeOverProjection_isModHom I J hI hJ hfin
  exact PLOriginalModelCompatibility.invariantMorphism_comp
    (nativeMultiplicativeGroup k) (X.normalizedSimultaneousNativeOverProjection I J hfin)
    (X.simultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))
    (X.simultaneousNativeOriginalProjection_invariant I J hI hJ)

end EnvelopeProperty.ProjSubvariety
