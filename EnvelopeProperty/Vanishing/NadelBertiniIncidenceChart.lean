import EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartCore
import EnvelopeProperty.AlgGeom.SchemeLineZeroIdealNativeFrameOrders
/-! # Actual original incidence whole ideals on their genuine affine source-open products -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniIncidenceChart
open NadelBertiniUniversal NadelBertiniRestrictionAlgebra NadelBertiniLinearSmooth
  NadelBertiniIncidenceChartCore SchemeLineSectionEvaluation
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}

abbrev productOpen (p : X ⟶ Spec (.of R)) (W : X.affineOpens) : (product (m := m) p).Opens :=
  FlatGlobalSections.firstProjection (S := parameterRing R m) p ⁻¹ᵁ W.1

theorem square (p : X ⟶ Spec (.of R)) (W : X.affineOpens) :
    IsPullback (FlatGlobalSections.firstProjection (S := parameterRing R m) p ∣_ W.1)
      ((productOpen p W).ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) p)
      (W.1.ι ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R (parameterRing R m)))) :=
  (isPullback_morphismRestrict (FlatGlobalSections.firstProjection (S := parameterRing R m) p) W.1).paste_vert
    (IsPullback.of_hasPullback _ _)

theorem productOpen_affine (p : X ⟶ Spec (.of R)) (W : X.affineOpens) :
    IsAffineOpen (productOpen (m := m) p W) := by
  let : IsAffine W.1.toScheme := W.2
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap R (parameterRing R m)))
  let : IsAffineHom ρ := inferInstance
  exact IsAffine.of_isPullback (square p W)

abbrev productAffineOpen (p : X ⟶ Spec (.of R)) (W : X.affineOpens) : (product (m := m) p).affineOpens :=
  ⟨productOpen p W, productOpen_affine p W⟩

def coefficients (L : X.Modules) (W : X.affineOpens)
    (e : (pullback W.1.ι).obj L ≅ unitObj W.1.toScheme) (s : Fin (m + 1) → Γ(L, ⊤)) :
    Fin (m + 1) → Γ(W.1.toScheme, ⊤) := fun b => e.hom.app ⊤ (affinePullbackUnitTop W.1.ι L (s b))

def polynomialEquiv (p : X ⟶ Spec (.of R)) (W : X.affineOpens) :
    MvPolynomial (Fin (m + 1)) Γ(W.1.toScheme, ⊤) ≃+* Γ(product (m := m) p, (productOpen p W)) := by
  let : IsAffine W.1.toScheme := W.2
  exact (squareSectionsEquiv (W.1.ι ≫ p)
    (FlatGlobalSections.firstProjection (S := parameterRing R m) p ∣_ W.1)
    ((productOpen p W).ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) p) (square p W)).trans
      (productOpen p W).topIso.commRingCatIsoToRingEquiv

theorem wholeIdeal (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : IsInvertible L)
    (W : X.affineOpens) (e : (pullback W.1.ι).obj L ≅ unitObj W.1.toScheme)
    (s : Fin (m + 1) → Γ(L, ⊤)) :
    (incidenceIdeal p L hL s).ideal (productAffineOpen p W) =
      Ideal.map (polynomialEquiv p W).toRingHom (linearIdeal (coefficients L W e s)) := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing R m) p
  let V := productOpen (m := m) p W
  let E := localPullbackFrame f W.1 e
  let α := SchemeModuleGlobalSections.sectionHom (productLine (m := m) p L) (universalSection p L s)
  let : IsAffine W.1.toScheme := W.2
  have h := SchemeLineZeroIdealNativeFrameOrders.zeroIdeal_ideal_of_pullback_frame
    (productLine (m := m) p L) (hL.pullback f) α (productAffineOpen p W) E
  have hc : (show Γ(V.toScheme, ⊤) from sectionAtOne (pullbackSectionHom V.ι α ≫ E.hom)) =
      squareSectionsEquiv (W.1.ι ≫ p) (f ∣_ W.1)
        (V.ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) p) (square p W)
        (linearForm (coefficients L W e s)) := by
    change E.hom.app ⊤ (sectionAtOne (pullbackSectionHom V.ι
      (topSectionHom (productLine (m := m) p L) (universalSection p L s)))) = _
    have hu := congrArg (fun z => E.hom.app ⊤ z)
      (Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne V.ι
        (productLine (m := m) p L) (universalSection p L s))
    apply hu.symm.trans
    exact (restricted_universal_frame p L W.1 e s).trans
      (squareSectionsEquiv_linearForm (W.1.ι ≫ p) (f ∣_ W.1)
        (V.ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) p) (square p W)
        (coefficients L W e s)).symm
  apply h.trans
  rw [linearIdeal, Ideal.map_span, Set.image_singleton]
  apply congrArg (fun r : Γ(product (m := m) p, V) => Ideal.span ({r} : Set Γ(product (m := m) p, V)))
  exact congrArg V.topIso.hom hc
theorem polynomialEquiv_parameter (p : X ⟶ Spec (.of R)) (W : X.affineOpens) (F : parameterRing R m) :
    polynomialEquiv p W (coefficientPolynomialMap (W.1.ι ≫ p) F) =
      (productOpen p W).topIso.hom (ProperBirationalSections.coefficientMap
        ((productOpen p W).ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) p) F) := by
  let : IsAffine W.1.toScheme := W.2
  exact congrArg (productOpen p W).topIso.hom (squareSectionsEquiv_parameter (W.1.ι ≫ p)
    (FlatGlobalSections.firstProjection (S := parameterRing R m) p ∣_ W.1)
    ((productOpen p W).ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) p) (square p W) F)

end EnvelopeProperty.Vanishing.NadelBertiniIncidenceChart
