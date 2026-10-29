import EnvelopeProperty.Vanishing.NadelBertiniFrameCoefficients
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
/-! # Native whole-section pullback retains sums, scalars and actual factor-frame coefficients -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniPullbackSections
open SchemeLineSectionEvaluation Berkovich.SchemeFramedSectionPullback

theorem pullback_add {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) (s t : Γ(L, ⊤)) :
    affinePullbackUnitTop f L (s + t) = affinePullbackUnitTop f L s + affinePullbackUnitTop f L t := by
  unfold affinePullbackUnitTop
  erw [map_add, map_add]

theorem pullback_smul {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (r : Γ(X, ⊤)) (s : Γ(L, ⊤)) :
    affinePullbackUnitTop f L (r • s) = f.appTop r • affinePullbackUnitTop f L s := by
  let P := (pullback f).obj L
  let k := (eqToHom (show (⊤ : Y.Opens) = f ⁻¹ᵁ (⊤ : X.Opens) by simp)).op
  let a := ((pullbackPushforwardAdjunction f).unit.app L).val.app (op (⊤ : X.Opens))
  have hu := a.hom.map_smul r s
  change a (r • s) = (f.app ⊤ r) • (show Γ(P, f ⁻¹ᵁ ⊤) from a s) at hu
  change P.presheaf.map k (a (r • s)) = f.appTop r • P.presheaf.map k (a s)
  rw [hu]
  have hm := P.val.map_smul k (f.app ⊤ r) (a s)
  change P.presheaf.map k (f.app ⊤ r • (show Γ(P, f ⁻¹ᵁ ⊤) from a s)) =
    Y.presheaf.map k (f.app ⊤ r) • P.presheaf.map k (a s) at hm
  refine hm.trans ?_
  congr 1
  change Y.presheaf.map k (f.appTop r) = f.appTop r
  have hk : k = 𝟙 (op (⊤ : Y.Opens)) := Subsingleton.elim _ _
  rw [hk]
  erw [CategoryTheory.Functor.map_id]
  rfl

theorem frameViaFactor_unitSection {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (f : A ⟶ C) (hf : g ≫ b = f)
    (M : C.Modules) (e : (pullback b).obj M ≅ unitObj B) (s : Γ(M, ⊤)) :
    (frameViaFactor g b f hf e).hom.app ⊤ (affinePullbackUnitTop f M s) =
      g.appTop (e.hom.app ⊤ (affinePullbackUnitTop b M s)) := by
  have hr : pullbackSectionHom b (topSectionHom M s) ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (e.hom.app ⊤ (affinePullbackUnitTop b M s)) := by
    refine (unitHom_eq_globalScalar _).trans ?_
    apply congrArg ModularCurves.unitEndomorphismOfTopSection
    exact congrArg (fun z => e.hom.app ⊤ z) (affinePullbackUnitTop_eq_sectionAtOne b M s).symm
  have hs := frameViaFactor_sectionHom_scalar_apply g b f hf e (topSectionHom M s) _ hr
  exact (congrArg (fun z => (frameViaFactor g b f hf e).hom.app ⊤ z)
    (affinePullbackUnitTop_eq_sectionAtOne f M s)).trans hs
end EnvelopeProperty.Vanishing.NadelBertiniPullbackSections
