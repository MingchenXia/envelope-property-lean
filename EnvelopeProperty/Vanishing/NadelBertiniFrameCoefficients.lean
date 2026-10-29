import EnvelopeProperty.Vanishing.NadelBertiniUniversal
import EnvelopeProperty.Vanishing.NadelBertiniPolynomial

/-! # The whole original universal incidence section retains its actual frame coefficients -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniFrameCoefficients
open SchemeLineSectionEvaluation NadelBertiniUniversal NadelBertiniPolynomial

private theorem unitEnd_sectionAtOne {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
  change 1 * X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r
  simp

/-- The native pulled structure section is exactly the actual pulled scalar. -/
theorem unit_pullback_scalar {X Y : Scheme.{u}} (f : Y ⟶ X) (r : Γ(X, ⊤)) :
    (pullbackUnitIso f).hom.app ⊤
      (affinePullbackUnitTop f (unitObj X) (show Γ(unitObj X, ⊤) from r)) = f.appTop r := by
  have hs : topSectionHom (unitObj X) (show Γ(unitObj X, ⊤) from r) =
      ModularCurves.unitEndomorphismOfTopSection r :=
    (unitHom_eq_globalScalar _).trans (congrArg ModularCurves.unitEndomorphismOfTopSection
      (topSectionHom_app_top_apply_one (unitObj X) (show Γ(unitObj X, ⊤) from r)))
  have hu := Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne f
    (unitObj X) (show Γ(unitObj X, ⊤) from r)
  have hu' := hu.trans (congrArg (fun a => sectionAtOne (pullbackSectionHom f a)) hs)
  have hm := congrArg sectionAtOne (ModularCurves.pullback_unitEndomorphismOfTopSection f r)
  change (pullbackUnitIso f).hom.app ⊤
      (sectionAtOne (pullbackSectionHom f (ModularCurves.unitEndomorphismOfTopSection r))) =
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection (f.appTop r)) at hm
  exact (congrArg ((pullbackUnitIso f).hom.app ⊤) hu').trans
    (hm.trans (unitEnd_sectionAtOne _))

/-- The actual pulled frame uses the native original structure-line unit comparison. -/
def pulledFrame {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) (e : L ≅ unitObj X) :
    (Scheme.Modules.pullback f).obj L ≅ unitObj Y :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f

/-- The same whole original pulled section has its actual original pulled frame coefficient. -/
theorem pulledFrame_section {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (e : L ≅ unitObj X) (s : Γ(L, ⊤)) :
    (pulledFrame f L e).hom.app ⊤ (affinePullbackUnitTop f L s) = f.appTop (e.hom.app ⊤ s) := by
  have hn := (Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_naturality f e.hom s).symm
  exact (congrArg ((pullbackUnitIso f).hom.app ⊤) hn).trans (unit_pullback_scalar f _)

/-- The actual entire universal section maps to the exact original linear polynomial,
under the genuine original affine coefficient-product equivalence. -/
theorem universal_frame_coefficient {R : Type u} [CommRing R] {m : ℕ}
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of R)) (L : X.Modules)
    (e : L ≅ unitObj X) (s : Fin (m + 1) → Γ(L, ⊤)) :
    (pulledFrame (FlatGlobalSections.firstProjection (S := parameterRing R m) p) L e).hom.app ⊤
        (universalSection p L s) =
      sectionsEquiv (S := Fin (m + 1)) p (∑ a, MvPolynomial.C (show Γ(X, ⊤) from e.hom.app ⊤ (s a)) * MvPolynomial.X a) := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing R m) p
  let E := pulledFrame f L e
  have hs : E.hom.app ⊤ (universalSection p L s) =
      ∑ a, coefficient p a * f.appTop (e.hom.app ⊤ (s a)) := by
    change E.hom.app ⊤ (∑ a, coefficient p a • affinePullbackUnitTop f L (s a)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    have h := Hom.app_smul E.hom (coefficient p a) (affinePullbackUnitTop f L (s a))
    change E.hom.app ⊤ (coefficient p a • affinePullbackUnitTop f L (s a)) =
      coefficient p a * (show Γ(product (m := m) p, ⊤) from
        E.hom.app ⊤ (affinePullbackUnitTop f L (s a))) at h
    exact h.trans (congrArg (fun z : Γ(product (m := m) p, ⊤) => coefficient p a * z)
      (pulledFrame_section f L e (s a)))
  have hc : (∑ a, coefficient p a * f.appTop (e.hom.app ⊤ (s a))) =
      ∑ a, f.appTop (e.hom.app ⊤ (s a)) * coefficient p a :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  exact hs.trans (hc.trans (sectionsEquiv_linearForm (S := Fin (m + 1)) p (fun a => e.hom.app ⊤ (s a))).symm)

end EnvelopeProperty.Vanishing.NadelBertiniFrameCoefficients
