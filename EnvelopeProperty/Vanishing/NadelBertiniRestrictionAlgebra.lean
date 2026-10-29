import EnvelopeProperty.Vanishing.NadelBertiniAffineSmooth
import EnvelopeProperty.Vanishing.NadelBertiniPullbackSections
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
/-! # Actual cartesian coefficient charts and original whole-section restriction -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniRestrictionAlgebra
open NadelBertiniUniversal NadelBertiniPolynomial NadelBertiniPullbackSections
variable {R : Type u} [CommRing R] {m : ℕ} {U V : Scheme.{u}} [IsAffine U]
  (p : U ⟶ Spec (.of R)) (g : V ⟶ U) (q : V ⟶ Spec (.of (parameterRing R m)))
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R (parameterRing R m)))))

def squareSectionsEquiv : MvPolynomial (Fin (m + 1)) Γ(U, ⊤) ≃+* Γ(V, ⊤) :=
  (sectionsEquiv p).trans (Scheme.Γ.mapIso H.isoPullback.op).commRingCatIsoToRingEquiv

theorem squareSectionsEquiv_C (b : Γ(U, ⊤)) :
    squareSectionsEquiv p g q H (MvPolynomial.C b) = g.appTop b := by
  change H.isoPullback.hom.appTop (sectionsEquiv p (MvPolynomial.C b)) = _
  rw [sectionsEquiv_C]
  have h := congrArg (fun f => f.appTop b) H.isoPullback_hom_fst
  rw [Scheme.Hom.comp_appTop] at h
  exact h

theorem squareSectionsEquiv_X (a : Fin (m + 1)) :
    squareSectionsEquiv p g q H (MvPolynomial.X a) =
      ProperBirationalSections.coefficientMap q (MvPolynomial.X a) := by
  change H.isoPullback.hom.appTop (sectionsEquiv p (MvPolynomial.X a)) = _
  rw [sectionsEquiv_X]
  have h := congrArg (fun f => ProperBirationalSections.coefficientMap f (MvPolynomial.X a)) H.isoPullback_hom_snd
  simp only [ProperBirationalSections.coefficientMap, Scheme.Hom.comp_appTop] at h
  exact h

def squareSectionsAlgEquiv :
    let : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
    MvPolynomial (Fin (m + 1)) Γ(U, ⊤) ≃ₐ[Γ(U, ⊤)] Γ(V, ⊤) := by
  let : Algebra Γ(U, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
  refine { toRingEquiv := squareSectionsEquiv p g q H, commutes' := ?_ }
  exact squareSectionsEquiv_C p g q H

theorem squareSectionsEquiv_linearForm (c : Fin (m + 1) → Γ(U, ⊤)) :
    squareSectionsEquiv p g q H (NadelBertiniLinearSmooth.linearForm c) =
      ∑ a, g.appTop (c a) * ProperBirationalSections.coefficientMap q (MvPolynomial.X a) := by
  simp only [NadelBertiniLinearSmooth.linearForm, map_sum, map_mul,
    squareSectionsEquiv_C, squareSectionsEquiv_X]

section LocalFrame
variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) (W : X.Opens)
  (e : (Scheme.Modules.pullback W.ι).obj L ≅ unitObj W.toScheme)
open SchemeLineSectionEvaluation Berkovich.SchemeFramedSectionPullback

theorem localFrame_section (s : Γ(L, ⊤)) :
    (localPullbackFrame f W e).hom.app ⊤
      (affinePullbackUnitTop (f ⁻¹ᵁ W).ι ((Scheme.Modules.pullback f).obj L) (affinePullbackUnitTop f L s)) =
      (f ∣_ W).appTop (e.hom.app ⊤ (affinePullbackUnitTop W.ι L s)) := by
  change (frameViaFactor (f ∣_ W) W.ι ((f ⁻¹ᵁ W).ι ≫ f) (morphismRestrict_ι f W) e).hom.app ⊤
      (((pullbackComp (f ⁻¹ᵁ W).ι f).hom.app L).app ⊤
        (affinePullbackUnitTop (f ⁻¹ᵁ W).ι ((Scheme.Modules.pullback f).obj L) (affinePullbackUnitTop f L s))) = _
  rw [affinePullbackUnitTop_comp]
  exact frameViaFactor_unitSection (f ∣_ W) W.ι ((f ⁻¹ᵁ W).ι ≫ f) (morphismRestrict_ι f W) L e s
end LocalFrame

section UniversalRestriction
open SchemeLineSectionEvaluation

def pullbackAddHom {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) :
    Γ(L, ⊤) →+ Γ((Scheme.Modules.pullback f).obj L, ⊤) where
  toFun := affinePullbackUnitTop f L
  map_zero' := by unfold affinePullbackUnitTop; erw [map_zero, map_zero]
  map_add' := pullback_add f L

theorem restricted_universal_frame {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of R)) (L : X.Modules) (W : X.Opens)
    (e : (Scheme.Modules.pullback W.ι).obj L ≅ unitObj W.toScheme)
    (s : Fin (m + 1) → Γ(L, ⊤)) :
    let f := FlatGlobalSections.firstProjection (S := parameterRing R m) pX
    let V := f ⁻¹ᵁ W
    let g := f ∣_ W
    let q := V.ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) pX
    (localPullbackFrame f W e).hom.app ⊤
      (affinePullbackUnitTop V.ι ((Scheme.Modules.pullback f).obj L) (universalSection pX L s)) =
      ∑ a, g.appTop (e.hom.app ⊤ (affinePullbackUnitTop W.ι L (s a))) *
        ProperBirationalSections.coefficientMap q (MvPolynomial.X a) := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing R m) pX
  let V := f ⁻¹ᵁ W
  let q := V.ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) pX
  let E := localPullbackFrame f W e
  change E.hom.app ⊤ ((pullbackAddHom V.ι ((Scheme.Modules.pullback f).obj L))
    (∑ a, coefficient pX a • affinePullbackUnitTop f L (s a))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  change E.hom.app ⊤ (affinePullbackUnitTop V.ι _ (coefficient pX a • affinePullbackUnitTop f L (s a))) = _
  rw [pullback_smul, Hom.app_smul]
  have hs := localFrame_section f L W e (s a)
  have hc : V.ι.appTop (coefficient pX a) =
      ProperBirationalSections.coefficientMap q (MvPolynomial.X a) := by
    simp only [q, coefficient, ProperBirationalSections.coefficientMap, Scheme.Hom.comp_appTop]
    rfl
  change V.ι.appTop (coefficient pX a) *
    (show Γ(V.toScheme, ⊤) from E.hom.app ⊤
      (affinePullbackUnitTop V.ι _ (affinePullbackUnitTop f L (s a)))) = _
  rw [hs, hc, mul_comm]
end UniversalRestriction

end EnvelopeProperty.Vanishing.NadelBertiniRestrictionAlgebra
