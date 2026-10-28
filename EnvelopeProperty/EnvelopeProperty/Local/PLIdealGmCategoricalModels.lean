/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealGmAssociativity
import EnvelopeProperty.Local.PLIdealNativeCoordinates

/-!
# The existing categorical group action on the original actual PL model

The entire native coordinate comparison is genuinely over the original field.
The actual existing group action therefore transports to the same original
simultaneous blowup. The final producer uses only the actual PL input.

Normalization, model polarization, its analytic comparison and nefness remain
further geometric obligations.
-/

open scoped Classical Polynomial LaurentPolynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I L : HomogeneousIdeal (ProjectiveGrading k[X] M))

/-- The actual original simultaneous blowup, with its original structure over
its original coefficient field. -/
abbrev simultaneousIdealBlowupAsOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal L) ≫
    X.nativeProductStructure ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))

/-- The genuine same-model coordinate isomorphism is over the original field,
and retains the entire original projection triangle. -/
theorem exists_simultaneousIdealBlowup_nativeCoordinateOverIso :
    ∃ e : nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I L ≅
        X.simultaneousIdealBlowupAsOver I L,
      e.hom.left ≫ X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal L) =
        (nativeClosedProductIdeal X.nativeHomogeneousIdeal I L).blowUpπ ≫
          X.nativeConstantFamilyModelIso.hom := by
  obtain ⟨e, he⟩ := X.exists_simultaneousIdealBlowup_nativeCoordinateIso I L
  refine ⟨Over.isoMk e ?_, he⟩
  change e.hom ≫ (X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I)
    (X.nativeProductIdeal L) ≫ X.nativeProductStructure ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) = _
  rw [← Category.assoc, ← Category.assoc, he]
  simp only [Category.assoc]
  rw [X.nativeConstantFamilyModelIso_over_base_assoc]
  rfl

/-- Actual entire ideal invariance supplies the existing categorical action
on the same original simultaneous blowup by actual over-isomorphism transport. -/
theorem nonempty_simultaneousIdealBlowup_modObj
    (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
      (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
        (MvPolynomial.map (parameterScaleHom (u : S))) =
          I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
    (hL : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
      (L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
        (MvPolynomial.map (parameterScaleHom (u : S))) =
          L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) :
    Nonempty (ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I L)) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I L) :=
    nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I L hI hL
  obtain ⟨e, _he⟩ := X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I L
  let : IsMonHom (Iso.refl (nativeMultiplicativeGroup k)).hom := by
    change IsMonHom (𝟙 (nativeMultiplicativeGroup k))
    infer_instance
  exact ⟨ModObj.ofIso (Iso.refl _) e⟩

private local instance productModelProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := M)) :=
  nativePolynomialLineProductStructure_isProper

/-- The original PL input alone produces actual finite vertical ideals,
their exact finite Gauss formula, and the existing categorical Gm action on
the same original simultaneous blowup. No action or comparison is assumed. -/
theorem IsPL.exists_verticalIdeal_models_with_categoricalGmAction
    {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I L : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ L.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X ^ B) ∈ L.toIdeal) ∧
      (∀ v : X.an,
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal I)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal L)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) ≠ ⊥) ∧
      (∀ v : X.an, (((r : ℝ) * φ v : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal I)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) -
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal L)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) + ((C : ℝ) : EReal)) ∧
      Nonempty (ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I L)) ∧
      ∃ e : nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I L ≅
          X.simultaneousIdealBlowupAsOver I L,
        e.hom.left ≫ X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal L) =
          (nativeClosedProductIdeal X.nativeHomogeneousIdeal I L).blowUpπ ≫
            X.nativeConstantFamilyModelIso.hom := by
  obtain ⟨r, hr, C, I, L, hfgI, hfgL, hAI, hBL, hI, hL, hfin, hlog⟩ :=
    hφ.exists_parameterInvariant_vertical_productIdeal_models
  exact ⟨r, hr, C, I, L, hfgI, hfgL, hAI, hBL, hfin, hlog,
    X.nonempty_simultaneousIdealBlowup_modObj I L hI hL,
    X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I L⟩

end EnvelopeProperty.ProjSubvariety
