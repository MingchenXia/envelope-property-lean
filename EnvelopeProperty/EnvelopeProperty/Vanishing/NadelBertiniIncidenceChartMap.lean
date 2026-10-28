import EnvelopeProperty.Vanishing.NadelBertiniIncidenceChart
/-! # Genuine polynomial quotient spectra enter the same original incidence with their original parameter map -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartMap
open NadelBertiniUniversal NadelBertiniIncidenceChartCore NadelBertiniIncidenceChart NadelBertiniLinearSmooth
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}
  (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : IsInvertible L)
  (W : X.affineOpens) (e : (pullback W.1.ι).obj L ≅ unitObj W.1.toScheme)
  (s : Fin (m + 1) → Γ(L, ⊤))

theorem nativeChart_isOpenImmersion {Y : Scheme.{u}} (I : Y.IdealSheafData) (V : Y.affineOpens) :
    IsOpenImmersion (I.subschemeCover.f V) := I.subschemeCover.openCover.map_prop V

abbrev quotientRing := MvPolynomial (Fin (m + 1)) Γ(W.1.toScheme, ⊤) ⧸ linearIdeal (coefficients L W e s)

def parameterRingMap : parameterRing R m →+* quotientRing L W e s :=
  (Ideal.Quotient.mk (linearIdeal (coefficients L W e s))).comp (coefficientPolynomialMap (W.1.ι ≫ p))

def quotientEquiv : quotientRing L W e s ≃+*
    (Γ(product (m := m) p, productOpen p W) ⧸ (incidenceIdeal p L hL s).ideal (productAffineOpen p W)) :=
  Ideal.quotientEquiv _ _ (polynomialEquiv p W) (wholeIdeal p L hL W e s)

theorem quotientEquiv_mk (F : MvPolynomial (Fin (m + 1)) Γ(W.1.toScheme, ⊤)) :
    quotientEquiv p L hL W e s (Ideal.Quotient.mk (linearIdeal (coefficients L W e s)) F) =
      Ideal.Quotient.mk ((incidenceIdeal p L hL s).ideal (productAffineOpen p W)) (polynomialEquiv p W F) := by
  rfl

def quotientSpecIso : Spec (.of (quotientRing L W e s)) ≅
    Spec (.of (Γ(product (m := m) p, productOpen p W) ⧸ (incidenceIdeal p L hL s).ideal (productAffineOpen p W))) :=
  Scheme.Spec.mapIso (quotientEquiv p L hL W e s).symm.toCommRingCatIso.op

def map : Spec (.of (quotientRing L W e s)) ⟶ incidence p L hL s :=
  (quotientSpecIso p L hL W e s).hom ≫ (incidenceIdeal p L hL s).subschemeCover.f (productAffineOpen p W)

instance map_isOpenImmersion : IsOpenImmersion (map p L hL W e s) := by
  exact @IsOpenImmersion.comp _ _ _ (quotientSpecIso p L hL W e s).hom
    ((incidenceIdeal p L hL s).subschemeCover.f (productAffineOpen p W))
    (inferInstanceAs (IsOpenImmersion (quotientSpecIso p L hL W e s).hom))
    (nativeChart_isOpenImmersion _ _)

theorem map_opensRange :
    (map p L hL W e s).opensRange = (incidenceIdeal p L hL s).subschemeι ⁻¹ᵁ productOpen p W := by
  have h := @Scheme.Hom.opensRange_comp_of_isIso _ _ _ (quotientSpecIso p L hL W e s).hom
    ((incidenceIdeal p L hL s).subschemeCover.f (productAffineOpen p W))
    (inferInstanceAs (IsIso (quotientSpecIso p L hL W e s).hom))
    (nativeChart_isOpenImmersion _ _)
  exact h.trans ((incidenceIdeal p L hL s).opensRange_subschemeCover_map (productAffineOpen p W))

theorem map_parameter : map p L hL W e s ≫ toParameters p L hL s =
    Spec.map (CommRingCat.ofHom (parameterRingMap p L W e s)) := by
  let I := incidenceIdeal p L hL s
  let V := productOpen (m := m) p W
  let q := FlatGlobalSections.structureMap (S := parameterRing R m) p
  let E := quotientEquiv p L hL W e s
  change (Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ I.subschemeCover.f (productAffineOpen p W)) ≫ I.subschemeι ≫ q = _
  erw [Category.assoc]
  erw [nativeChart_parameter]
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro F
  change E.symm (Ideal.Quotient.mk (I.ideal (productAffineOpen p W))
      (V.topIso.hom (ProperBirationalSections.coefficientMap (V.ι ≫ q) F))) =
    Ideal.Quotient.mk (linearIdeal (coefficients L W e s)) (coefficientPolynomialMap (W.1.ι ≫ p) F)
  have hf := (polynomialEquiv_parameter p W F).symm
  have hmk := E.symm_apply_apply (Ideal.Quotient.mk (linearIdeal (coefficients L W e s))
    (coefficientPolynomialMap (W.1.ι ≫ p) F))
  rw [quotientEquiv_mk] at hmk
  exact (congrArg (fun z => E.symm (Ideal.Quotient.mk (I.ideal (productAffineOpen p W)) z)) hf).trans hmk
end EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartMap
