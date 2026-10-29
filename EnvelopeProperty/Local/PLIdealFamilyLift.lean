/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeParameterClosedFamily
import EnvelopeProperty.Local.PLIdealEquivariantData
import EnvelopeProperty.Local.PLIdealSubvarietyModels
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
import Hironaka.Scheme.BlowUp.FlatBaseChange
import Hironaka.Scheme.BlowUp.Transform.StrictTransform

/-!
# Actual lifting of the constructed invariant ideal families

Flat family projection and actual whole-ideal equality make the true product
admissible for the constructed blowup. Its universal property then constructs
the unique actual family map. The later PL consumer derives that equality from
the very produced parameter-monomial ideals, rather than assuming an action.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {Y Y' : Scheme.{u}} (K : Y.IdealSheafData) (p a : Y' ⟶ Y) [Flat p]

/-- The actual whole ideal equality and true flat pullback make the entire
geometric family product admissible for the original blowup. -/
theorem parameterFamily_admissible (hK : K.comap a = K.comap p) :
    (K.comap (pullback.snd K.blowUpπ p ≫ a)).IsInvertible := by
  rw [comap_comp, hK, ← comap_comp, ← pullback.condition, comap_comp]
  exact (blowUp.isInvertible_comap_π K).comap_of_flat (pullback.fst K.blowUpπ p)

/-- The actual unique family morphism supplied by the blowup universal property. -/
def parameterFamilyLift (hK : K.comap a = K.comap p) :
    pullback K.blowUpπ p ⟶ K.blowUp :=
  blowUp.lift K (pullback.snd K.blowUpπ p ≫ a) (K.parameterFamily_admissible p a hK)

/-- The constructed actual family lift has the full original projection triangle. -/
@[reassoc]
theorem parameterFamilyLift_π (hK : K.comap a = K.comap p) :
    K.parameterFamilyLift p a hK ≫ K.blowUpπ = pullback.snd K.blowUpπ p ≫ a :=
  (blowUp.exists_lift K _ (K.parameterFamily_admissible p a hK)).choose_spec

/-- Uniqueness of the actual whole family lift is a genuine blowup property. -/
theorem parameterFamilyLift_unique (hK : K.comap a = K.comap p)
    (g : pullback K.blowUpπ p ⟶ K.blowUp)
    (hg : g ≫ K.blowUpπ = pullback.snd K.blowUpπ p ≫ a) :
    g = K.parameterFamilyLift p a hK :=
  blowUp.hom_ext K _ (K.parameterFamily_admissible p a hK) _ _ hg
    (K.parameterFamilyLift_π p a hK)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace EnvelopeProperty.ProjBerk
variable {k S : Type u} [Field k] [CommRing S] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual product of the two original ideals restricted to the genuine
native closed parameter family. -/
def nativeClosedProductIdeal (J : HomogeneousIdeal (ProjectiveGrading k n))
    (I L : HomogeneousIdeal (ProjectiveGrading k[X] n)) :
    (nativeConstantIdeal J).subscheme.IdealSheafData :=
  ((nativeHomogeneousIdealSheaf I).comap (nativeConstantIdeal J).subschemeι) *
    ((nativeHomogeneousIdealSheaf L).comap (nativeConstantIdeal J).subschemeι)

/-- The true closed-family projection is flat over every actual coefficient
extension of the original field, by its proved whole product square. -/
theorem nativeClosedParameterFamilyProjection_flat
    (J : HomogeneousIdeal (ProjectiveGrading k n)) (f : k →+* S) :
    Flat (nativeClosedParameterFamilyMap J f 1) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (isPullback_nativeClosedParameterProduct J f).flip inferInstance

/-- The whole actual original restricted product ideal is preserved by the
entire family, using the actual ring-ideal equalities of its two factors. -/
theorem nativeClosedProductIdeal_family_invariant
    (J : HomogeneousIdeal (ProjectiveGrading k n))
    (I L : HomogeneousIdeal (ProjectiveGrading k[X] n)) (f : k →+* S) (u : Sˣ)
    (hI : (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
      (MvPolynomial.map (parameterScaleHom (u : S))) =
        I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
    (hL : (L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
      (MvPolynomial.map (parameterScaleHom (u : S))) =
        L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) :
    (nativeClosedProductIdeal J I L).comap (nativeClosedParameterFamilyMap J f u) =
      (nativeClosedProductIdeal J I L).comap (nativeClosedParameterFamilyMap J f 1) := by
  simp only [nativeClosedProductIdeal, Scheme.IdealSheafData.comap_mul]
  rw [nativeClosedIdeal_comap_parameterFamily_eq J I f u hI,
    nativeClosedIdeal_comap_parameterFamily_eq J L f u hL]

/-- The concrete entire closed-family product has a unique actual blowup map,
with flatness and ideal-sheaf equality proved from the genuine input data. -/
theorem nativeClosedProductIdeal_existsUnique_familyLift
    (J : HomogeneousIdeal (ProjectiveGrading k n))
    (I L : HomogeneousIdeal (ProjectiveGrading k[X] n)) (f : k →+* S) (u : Sˣ)
    (hI : (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
      (MvPolynomial.map (parameterScaleHom (u : S))) =
        I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
    (hL : (L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
      (MvPolynomial.map (parameterScaleHom (u : S))) =
        L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) :
    ∃! g : pullback (nativeClosedProductIdeal J I L).blowUpπ
        (nativeClosedParameterFamilyMap J f 1) ⟶ (nativeClosedProductIdeal J I L).blowUp,
      g ≫ (nativeClosedProductIdeal J I L).blowUpπ =
        pullback.snd _ _ ≫ nativeClosedParameterFamilyMap J f u := by
  let := nativeClosedParameterFamilyProjection_flat J f
  have hK := nativeClosedProductIdeal_family_invariant J I L f u hI hL
  refine ⟨(nativeClosedProductIdeal J I L).parameterFamilyLift _ _ hK,
    (nativeClosedProductIdeal J I L).parameterFamilyLift_π _ _ hK, ?_⟩
  intro g hg
  exact (nativeClosedProductIdeal J I L).parameterFamilyLift_unique _ _ hK g hg

end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.ProjSubvariety
variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}
open ProjBerk EnvelopeProperty.Berkovich
attribute [local instance] MvPolynomial.gradedAlgebra
private local instance productModelProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := M)) :=
  nativePolynomialLineProductStructure_isProper

/-- An actual PL function constructs the very vertical ideals realizing its
finite exact Gauss formula, together with unique entire blowup lifts for every
actual extended-coefficient unit family, including the universal Laurent unit.
There is no ideal invariance, flatness or lift hypothesis in this producer. -/
theorem IsPL.exists_verticalIdeal_models_with_familyLift {φ : X.an → ℝ}
    (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ J.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) ∧
      (∀ v : X.an,
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal I)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) ≠ ⊥) ∧
      (∀ v : X.an, (((r : ℝ) * φ v : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal I)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) -
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) + ((C : ℝ) : EReal)) ∧
      ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
        ∃! g : pullback (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ
          (nativeClosedParameterFamilyMap X.nativeHomogeneousIdeal f 1) ⟶
            (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUp,
          g ≫ (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ =
            pullback.snd _ _ ≫ nativeClosedParameterFamilyMap X.nativeHomogeneousIdeal f u := by
  obtain ⟨r, hr, C, I, J, hfgI, hfgJ, hAI, hBJ, hscaleI, hscaleJ, hfin, hlog⟩ :=
    hφ.exists_parameterInvariant_vertical_productIdeal_models
  refine ⟨r, hr, C, I, J, hfgI, hfgJ, hAI, hBJ, hfin, hlog, ?_⟩
  intro S _inst f u
  exact nativeClosedProductIdeal_existsUnique_familyLift X.nativeHomogeneousIdeal I J f u
    (hscaleI S f u) (hscaleJ S f u)

end EnvelopeProperty.ProjSubvariety
