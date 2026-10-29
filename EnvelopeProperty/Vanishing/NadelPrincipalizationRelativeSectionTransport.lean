import EnvelopeProperty.Vanishing.NadelPrincipalizationHomSection
import EnvelopeProperty.Char0.GlobalRoundedQuotientOpenPullback

/-! # Genuine whole Hom-section transport through actual source and target maps -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSectionTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def isoTriple {C : Type*} [Category C] {A B D E : C}
    (e₀ : A ≅ B) (e₁ : B ≅ D) (e₂ : D ≅ E) : A ≅ E where
  hom := e₀.hom ≫ e₁.hom ≫ e₂.hom
  inv := e₂.inv ≫ e₁.inv ≫ e₀.inv
  hom_inv_id := by simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id]
  inv_hom_id := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

private theorem section_paste {C : Type*} [Category C] {U A B D E : C}
    (s : U ⟶ A) (a : A ≅ B) (b : B ≅ D) (c : D ≅ E)
    (s' : U ⟶ B) (t : U ⟶ E) (ha : s ≫ a.hom = s')
    (hbc : s' ≫ b.hom ≫ c.hom = t) : s ≫ (isoTriple a b c).hom = t := by
  change s ≫ a.hom ≫ b.hom ≫ c.hom = t
  rw [← Category.assoc s a.hom, ha]
  exact hbc

variable {X Y : Scheme.{u}} (v : Y ⟶ X)
    (A : X.Modules) (hA : Scheme.Modules.IsInvertible A) (B : X.Modules)
    (A' B' : Y.Modules) (hA' : Scheme.Modules.IsInvertible A')
    (eA : (pullback v).obj A ≅ A') (eB : (pullback v).obj B ≅ B')

/-- The actual relative Hom-module pullback comparison uses genuine native
unit-section pullback, the actual source-line adjunction mate, and target tensor. -/
def transportIso :
    (pullback v).obj (tensorObj B (dualObj A)) ≅ tensorObj B' (dualObj A') :=
  isoTriple (Char0.AffineOpenGlobalRoundedKernel.homSectionPullbackIso v A hA B)
    (NadelPrincipalizationHomSection.lineHomIso ((pullback v).obj A) (hA.pullback v)
      A' hA' eA ((pullback v).obj B))
    (tensorObjCongr eB (Iso.refl (dualObj A')))

/-- An actual whole-map square carries the SAME original native Hom section
to the SAME actual new section. Geometric consumers must prove that square. -/
theorem transport_section (φ : A ⟶ B) (φ' : A' ⟶ B')
    (hφ : (pullback v).map φ ≫ eB.hom = eA.hom ≫ φ') :
    (pullbackUnitIso v).inv ≫
      (pullback v).map (SchemeInvertibleHomSection.equiv A hA B φ) ≫
      (transportIso v A hA B A' B' hA' eA eB).hom =
    SchemeInvertibleHomSection.equiv A' hA' B' φ' := by
  rw [← Category.assoc (pullbackUnitIso v).inv
    ((pullback v).map (SchemeInvertibleHomSection.equiv A hA B φ))]
  exact section_paste (C := Y.Modules)
    ((pullbackUnitIso v).inv ≫ (pullback v).map (SchemeInvertibleHomSection.equiv A hA B φ))
    (Char0.AffineOpenGlobalRoundedKernel.homSectionPullbackIso v A hA B)
    (NadelPrincipalizationHomSection.lineHomIso ((pullback v).obj A) (hA.pullback v)
      A' hA' eA ((pullback v).obj B))
    (tensorObjCongr eB (Iso.refl (dualObj A')))
    (SchemeInvertibleHomSection.equiv ((pullback v).obj A) (hA.pullback v)
      ((pullback v).obj B) ((pullback v).map φ))
    (SchemeInvertibleHomSection.equiv A' hA' B' φ')
    (Char0.AffineOpenGlobalRoundedKernel.homSectionPullbackIso_section v A hA B φ)
    (NadelPrincipalizationHomSection.lineHomIso_square_section
      ((pullback v).obj A) (hA.pullback v) A' hA' eA ((pullback v).obj B) B' eB
      ((pullback v).map φ) φ' hφ)

end EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSectionTransport
