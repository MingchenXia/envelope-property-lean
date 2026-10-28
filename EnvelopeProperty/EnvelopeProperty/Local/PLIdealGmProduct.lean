/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealLaurentAction
import EnvelopeProperty.Projective.NativeMultiplicativeGroup

/-!
# Actual geometric multiplicative-group product source and action

The universal whole family is transported to the actual product with the genuine
Laurent Hopf group scheme, with its true unit components and entire unit diagram.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {n : ℕ}
variable (J : HomogeneousIdeal (ProjectiveGrading k n))
variable (I L : HomogeneousIdeal (ProjectiveGrading k[X] n))

/-- The whole original-field structure of the actual constructed ideal blowup. -/
def nativeClosedBlowupBaseStructure : (nativeClosedProductIdeal J I L).blowUp ⟶ Spec (.of k) :=
  (nativeClosedProductIdeal J I L).blowUpπ ≫ nativeClosedBaseStructure J

/-- The actual entire blowup family source is the whole original-base
geometric coefficient product, by genuine pullback pasting. -/
def nativeClosedBlowupFamilyProductIso {S : Type u} [CommRing S] (f : k →+* S) :
    pullback (nativeClosedProductIdeal J I L).blowUpπ (nativeClosedParameterFamilyMap J f 1) ≅
      pullback (nativeClosedBlowupBaseStructure J I L) (Spec.map (CommRingCat.ofHom f)) :=
  ((IsPullback.of_hasPullback (nativeClosedProductIdeal J I L).blowUpπ
    (nativeClosedParameterFamilyMap J f 1)).paste_vert
      (isPullback_nativeClosedParameterProduct J f)).isoPullback

/-- The actual whole blowup-family product comparison preserves its original component. -/
@[reassoc]
theorem nativeClosedBlowupFamilyProductIso_hom_fst {S : Type u} [CommRing S] (f : k →+* S) :
    (nativeClosedBlowupFamilyProductIso J I L f).hom ≫ pullback.fst _ _ = pullback.fst _ _ :=
  ((IsPullback.of_hasPullback (nativeClosedProductIdeal J I L).blowUpπ
    (nativeClosedParameterFamilyMap J f 1)).paste_vert
      (isPullback_nativeClosedParameterProduct J f)).isoPullback_hom_fst

/-- The whole blowup-family comparison has its true entire coefficient projection. -/
@[reassoc]
theorem nativeClosedBlowupFamilyProductIso_hom_snd {S : Type u} [CommRing S] (f : k →+* S) :
    (nativeClosedBlowupFamilyProductIso J I L f).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ nativeClosedBaseStructure (J.map (coefficientGradedMap f)) :=
  ((IsPullback.of_hasPullback (nativeClosedProductIdeal J I L).blowUpπ
    (nativeClosedParameterFamilyMap J f 1)).paste_vert
      (isPullback_nativeClosedParameterProduct J f)).isoPullback_hom_snd

/-- The entire actual closed Laurent evaluation has its genuine coefficient-base triangle. -/
@[reassoc]
theorem nativeClosedLaurentEvaluationMap_base {S : Type u} [CommRing S]
    (K : HomogeneousIdeal (ProjectiveGrading S n)) (f : k →+* S)
    (h : J.map (coefficientGradedMap f) = K) (v u : Sˣ) :
    nativeClosedLaurentEvaluationMap J K f h v u ≫
        nativeClosedBaseStructure (J.map (coefficientGradedMap LaurentPolynomial.C)) =
      nativeClosedBaseStructure K ≫ Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f v)) :=
  nativeClosedParameterMapOfIdealMap_base _ _ _ _ _

variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hL : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

/-- The single actual action morphism on the whole product with the genuine
existing multiplicative-group scheme. -/
def nativeClosedProductIdealGmAction :
    pullback (nativeClosedBlowupBaseStructure J I L) (nativeMultiplicativeGroup k).hom ⟶
      (nativeClosedProductIdeal J I L).blowUp :=
  (nativeClosedBlowupFamilyProductIso J I L LaurentPolynomial.C).inv ≫
    nativeClosedProductIdealFamilyLift J I L hI hL LaurentPolynomial.C (parameterLaurentUnit k)

/-- The true unit section into the entire geometric group product. -/
def nativeClosedProductIdealGmUnitSection :
    (nativeClosedProductIdeal J I L).blowUp ⟶
      pullback (nativeClosedBlowupBaseStructure J I L) (nativeMultiplicativeGroup k).hom :=
  (nativeClosedProductIdeal J I L).parameterFamilyUnitSection
    (nativeClosedParameterFamilyMap J LaurentPolynomial.C 1) (nativeClosedLaurentUnitSection J)
      (nativeClosedLaurentUnitSection_projection J) ≫
        (nativeClosedBlowupFamilyProductIso J I L LaurentPolynomial.C).hom

/-- The entire geometric group-product unit section has identity blowup component. -/
@[reassoc]
theorem nativeClosedProductIdealGmUnitSection_fst :
    nativeClosedProductIdealGmUnitSection J I L ≫ pullback.fst _ _ = 𝟙 _ := by
  change nativeClosedProductIdealGmUnitSection J I L ≫
    pullback.fst (nativeClosedBlowupBaseStructure J I L)
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) = _
  rw [nativeClosedProductIdealGmUnitSection, Category.assoc,
    nativeClosedBlowupFamilyProductIso_hom_fst]
  exact pullback.lift_fst _ _ _

/-- The entire geometric unit section has precisely the actual group-object
unit as its coefficient component at the original blowup base point. -/
@[reassoc]
theorem nativeClosedProductIdealGmUnitSection_snd :
    nativeClosedProductIdealGmUnitSection J I L ≫ pullback.snd _ _ =
      nativeClosedBlowupBaseStructure J I L ≫
        (MonObj.one (X := nativeMultiplicativeGroup k)).left := by
  change nativeClosedProductIdealGmUnitSection J I L ≫
    pullback.snd (nativeClosedBlowupBaseStructure J I L)
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) = _
  rw [nativeClosedProductIdealGmUnitSection, Category.assoc,
    nativeClosedBlowupFamilyProductIso_hom_snd, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ _ = _
  rw [pullback.lift_snd, Category.assoc]
  change (nativeClosedProductIdeal J I L).blowUpπ ≫
    (nativeClosedLaurentEvaluationMap J J (RingHom.id k)
      (homogeneousIdeal_coefficient_map_id J) 1 1 ≫ _) = _
  rw [nativeClosedLaurentEvaluationMap_base, nativeMultiplicativeGroup_one]
  rfl

/-- The genuine unit action diagram on the actual whole multiplicative-group
product of the constructed blowup. -/
theorem nativeClosedProductIdealGmAction_unit :
    nativeClosedProductIdealGmUnitSection J I L ≫
      nativeClosedProductIdealGmAction J I L hI hL = 𝟙 _ := by
  rw [nativeClosedProductIdealGmUnitSection, nativeClosedProductIdealGmAction,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact nativeClosedProductIdealFamilyLift_unit J I L hI hL

/-- The whole actual family lift preserves the original-field base structure. -/
theorem nativeClosedProductIdealFamilyLift_over_base {S : Type u} [CommRing S]
    (f : k →+* S) (u : Sˣ) :
    nativeClosedProductIdealFamilyLift J I L hI hL f u ≫ nativeClosedBlowupBaseStructure J I L =
      pullback.fst _ _ ≫ nativeClosedBlowupBaseStructure J I L := by
  have hb : nativeClosedParameterFamilyMap J f u ≫ nativeClosedBaseStructure J =
      nativeClosedParameterFamilyMap J f 1 ≫ nativeClosedBaseStructure J := by
    exact (nativeClosedParameterMapOfIdealMap_base J (J.map (coefficientGradedMap f)) f rfl u).trans
      (nativeClosedParameterMapOfIdealMap_base J (J.map (coefficientGradedMap f)) f rfl 1).symm
  dsimp only [nativeClosedBlowupBaseStructure]
  rw [← Category.assoc, nativeClosedProductIdealFamilyLift_π, Category.assoc,
    hb, ← Category.assoc, ← pullback.condition, Category.assoc]

/-- The actual whole multiplicative-group action morphism is over the original
field, with its true product projection and no base-preservation assumption. -/
theorem nativeClosedProductIdealGmAction_over_base :
    nativeClosedProductIdealGmAction J I L hI hL ≫ nativeClosedBlowupBaseStructure J I L =
      pullback.fst _ _ ≫ nativeClosedBlowupBaseStructure J I L := by
  change ((nativeClosedBlowupFamilyProductIso J I L LaurentPolynomial.C).inv ≫
    nativeClosedProductIdealFamilyLift J I L hI hL LaurentPolynomial.C (parameterLaurentUnit k)) ≫
      nativeClosedBlowupBaseStructure J I L =
    pullback.fst _ (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) ≫ _
  rw [Category.assoc,
    nativeClosedProductIdealFamilyLift_over_base,
    ← nativeClosedBlowupFamilyProductIso_hom_fst J I L LaurentPolynomial.C]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The true whole product map with the original blowup component and a
prescribed actual coefficient-extended group coordinate. -/
def nativeClosedProductIdealGmEvaluationMap {S : Type u} [CommRing S]
    (f : k →+* S) (w : Sˣ) :
    pullback (nativeClosedProductIdeal J I L).blowUpπ (nativeClosedParameterFamilyMap J f 1) ⟶
      pullback (nativeClosedBlowupBaseStructure J I L) (nativeMultiplicativeGroup k).hom :=
  (nativeClosedProductIdeal J I L).parameterFamilyBaseChangeMap
    (nativeClosedParameterFamilyMap J LaurentPolynomial.C 1) (nativeClosedParameterFamilyMap J f 1)
    (nativeClosedLaurentEvaluationMap J (J.map (coefficientGradedMap f)) f rfl w 1)
    (by rw [nativeClosedLaurentEvaluationMap_comp_family, map_one, one_mul,
      nativeClosedParameterMapOfIdealMap_eq_family]) ≫
    (nativeClosedBlowupFamilyProductIso J I L LaurentPolynomial.C).hom

/-- The whole evaluation product map preserves the original blowup component. -/
@[reassoc]
theorem nativeClosedProductIdealGmEvaluationMap_fst {S : Type u} [CommRing S]
    (f : k →+* S) (w : Sˣ) :
    nativeClosedProductIdealGmEvaluationMap J I L f w ≫ pullback.fst _ _ = pullback.fst _ _ := by
  change nativeClosedProductIdealGmEvaluationMap J I L f w ≫
    pullback.fst _ (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) = _
  rw [nativeClosedProductIdealGmEvaluationMap, Category.assoc,
    nativeClosedBlowupFamilyProductIso_hom_fst]
  exact pullback.lift_fst _ _ _

/-- The entire evaluation product map has its true prescribed group coordinate. -/
@[reassoc]
theorem nativeClosedProductIdealGmEvaluationMap_snd {S : Type u} [CommRing S]
    (f : k →+* S) (w : Sˣ) :
    nativeClosedProductIdealGmEvaluationMap J I L f w ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ nativeClosedBaseStructure (J.map (coefficientGradedMap f)) ≫
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f w)) := by
  change nativeClosedProductIdealGmEvaluationMap J I L f w ≫
    pullback.snd _ (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) = _
  rw [nativeClosedProductIdealGmEvaluationMap, Category.assoc,
    nativeClosedBlowupFamilyProductIso_hom_snd, ← Category.assoc,
    Scheme.IdealSheafData.parameterFamilyBaseChangeMap_snd, Category.assoc,
    nativeClosedLaurentEvaluationMap_base]

/-- Every entire coefficient-unit action is evaluation of this same actual
single geometric multiplicative-group action morphism. -/
theorem nativeClosedProductIdealGmEvaluationMap_action {S : Type u} [CommRing S]
    (f : k →+* S) (w : Sˣ) :
    nativeClosedProductIdealGmEvaluationMap J I L f w ≫
        nativeClosedProductIdealGmAction J I L hI hL =
      nativeClosedProductIdealFamilyLift J I L hI hL f w := by
  rw [nativeClosedProductIdealGmEvaluationMap, nativeClosedProductIdealGmAction,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact nativeClosedProductIdealFamilyLift_naturality J I L hI hL f w

private local instance familyProjectionFlat {S : Type u} [CommRing S] (f : k →+* S) :
    Flat (nativeClosedParameterFamilyMap J f 1) :=
  nativeClosedParameterFamilyProjection_flat J f

/-- The actual whole geometric product map acting first by u and retaining
v as its true second group coordinate. -/
def nativeClosedProductIdealGmThenMap {S : Type u} [CommRing S] (f : k →+* S) (u v : Sˣ) :
    pullback (nativeClosedProductIdeal J I L).blowUpπ (nativeClosedParameterFamilyMap J f 1) ⟶
      pullback (nativeClosedBlowupBaseStructure J I L) (nativeMultiplicativeGroup k).hom :=
  (nativeClosedProductIdeal J I L).parameterFamilyThenMap
    (nativeClosedParameterFamilyMap J LaurentPolynomial.C 1)
    (nativeClosedParameterFamilyMap J f 1) (nativeClosedParameterFamilyMap J f u)
    (nativeClosedProductIdeal_family_invariant J I L f u (hI S f u) (hL S f u))
    (nativeClosedLaurentEvaluationMap J (J.map (coefficientGradedMap f)) f rfl v u)
    (by rw [nativeClosedLaurentEvaluationMap_comp_family, map_one, mul_one,
      nativeClosedParameterMapOfIdealMap_eq_family]) ≫
      (nativeClosedBlowupFamilyProductIso J I L LaurentPolynomial.C).hom

/-- The actual sequential product map has the whole first action as blowup component. -/
@[reassoc]
theorem nativeClosedProductIdealGmThenMap_fst {S : Type u} [CommRing S]
    (f : k →+* S) (u v : Sˣ) :
    nativeClosedProductIdealGmThenMap J I L hI hL f u v ≫ pullback.fst _ _ =
      nativeClosedProductIdealFamilyLift J I L hI hL f u := by
  change nativeClosedProductIdealGmThenMap J I L hI hL f u v ≫
    pullback.fst _ (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) = _
  rw [nativeClosedProductIdealGmThenMap, Category.assoc,
    nativeClosedBlowupFamilyProductIso_hom_fst]
  exact pullback.lift_fst _ _ _

/-- The actual sequential product map has precisely the second true group coordinate. -/
@[reassoc]
theorem nativeClosedProductIdealGmThenMap_snd {S : Type u} [CommRing S]
    (f : k →+* S) (u v : Sˣ) :
    nativeClosedProductIdealGmThenMap J I L hI hL f u v ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ nativeClosedBaseStructure (J.map (coefficientGradedMap f)) ≫
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f v)) := by
  change nativeClosedProductIdealGmThenMap J I L hI hL f u v ≫
    pullback.snd _ (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) = _
  rw [nativeClosedProductIdealGmThenMap, Category.assoc,
    nativeClosedBlowupFamilyProductIso_hom_snd, ← Category.assoc,
    Scheme.IdealSheafData.parameterFamilyThenMap_snd, Category.assoc,
    nativeClosedLaurentEvaluationMap_base]

/-- The actual whole group-product multiplication diagram. The true group
operations are identified by the preceding exact component formulas and the
genuine Hopf group-coordinate comparison. -/
theorem nativeClosedProductIdealGmAction_multiplication {S : Type u} [CommRing S]
    (f : k →+* S) (u v : Sˣ) :
    nativeClosedProductIdealGmThenMap J I L hI hL f u v ≫
        nativeClosedProductIdealGmAction J I L hI hL =
      nativeClosedProductIdealGmEvaluationMap J I L f (u * v) ≫
        nativeClosedProductIdealGmAction J I L hI hL := by
  rw [nativeClosedProductIdealGmEvaluationMap_action,
    nativeClosedProductIdealGmThenMap, nativeClosedProductIdealGmAction,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact nativeClosedProductIdealFamilyLift_multiplication J I L hI hL f u v

end EnvelopeProperty.ProjBerk
