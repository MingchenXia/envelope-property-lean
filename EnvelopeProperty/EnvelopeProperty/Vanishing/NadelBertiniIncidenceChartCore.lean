import EnvelopeProperty.Vanishing.NadelBertiniRestrictionAlgebra
import EnvelopeProperty.Vanishing.NadelBertiniRestrictionCover
/-! # Native actual whole-ideal charts retain their entire original parameter ring -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartCore
open NadelBertiniUniversal NadelBertiniRestrictionAlgebra

theorem nativeChart_parameter {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (q : Y ⟶ Spec (.of A)) (V : Y.affineOpens) :
    I.subschemeCover.f V ≫ I.subschemeι ≫ q =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (I.ideal V)).comp
        (V.1.topIso.hom.hom.comp (ProperBirationalSections.coefficientMap (V.1.ι ≫ q))))) := by
  let : IsAffine V.1.toScheme := V.2
  rw [← Category.assoc, I.subschemeCover_map_subschemeι]
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal V))) ≫ V.2.isoSpec.inv) ≫ V.1.ι ≫ q = _
  have hn : V.2.isoSpec.inv ≫ (V.1.ι ≫ q) =
      Spec.map (CommRingCat.ofHom (V.1.topIso.hom.hom.comp
        (ProperBirationalSections.coefficientMap (V.1.ι ≫ q)))) := by
    change (Spec.map V.1.topIso.hom ≫ V.1.toScheme.isoSpec.inv) ≫ (V.1.ι ≫ q) = _
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality (V.1.ι ≫ q),
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [Category.assoc, hn, ← Spec.map_comp]
  rfl
private theorem coefficientMap_spec_comp {A B : Type u} [CommRing A] [CommRing B]
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of B)) (φ : A →+* B) (r : A) :
    ProperBirationalSections.coefficientMap (pY ≫ Spec.map (CommRingCat.ofHom φ)) r =
      ProperBirationalSections.coefficientMap pY (φ r) := by
  unfold ProperBirationalSections.coefficientMap
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

private theorem coefficientMap_comp {A : Type u} [CommRing A] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (.of A)) (f : Z ⟶ Y) (r : A) :
    f.appTop (ProperBirationalSections.coefficientMap p r) = ProperBirationalSections.coefficientMap (f ≫ p) r := by
  simp only [ProperBirationalSections.coefficientMap, Scheme.Hom.comp_appTop]
  rfl

def coefficientPolynomialMap {R : Type u} [CommRing R] {m : ℕ} {U : Scheme.{u}}
    (p : U ⟶ Spec (.of R)) : parameterRing R m →+* MvPolynomial (Fin (m + 1)) Γ(U, ⊤) :=
  MvPolynomial.map (ProperBirationalSections.coefficientMap p)

theorem squareSectionsEquiv_parameter {R : Type u} [CommRing R] {m : ℕ}
    {U V : Scheme.{u}} [IsAffine U] (p : U ⟶ Spec (.of R)) (g : V ⟶ U)
    (q : V ⟶ Spec (.of (parameterRing R m)))
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R (parameterRing R m)))))
    (F : parameterRing R m) :
    squareSectionsEquiv p g q H (coefficientPolynomialMap p F) = ProperBirationalSections.coefficientMap q F := by
  have he : ((squareSectionsEquiv p g q H).toRingHom.comp (coefficientPolynomialMap p)) =
      ProperBirationalSections.coefficientMap q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, coefficientPolynomialMap, MvPolynomial.map_C]
      change squareSectionsEquiv p g q H (MvPolynomial.C (ProperBirationalSections.coefficientMap p r)) = _
      rw [squareSectionsEquiv_C, coefficientMap_comp, H.w]
      exact coefficientMap_spec_comp q (algebraMap R (parameterRing R m)) r
    · intro i
      simp only [RingHom.comp_apply, coefficientPolynomialMap, MvPolynomial.map_X]
      change squareSectionsEquiv p g q H (MvPolynomial.X i) = _
      exact squareSectionsEquiv_X p g q H i
  exact DFunLike.congr_fun he F

end EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartCore
