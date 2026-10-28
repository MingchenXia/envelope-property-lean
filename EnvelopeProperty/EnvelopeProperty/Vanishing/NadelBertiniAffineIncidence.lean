import EnvelopeProperty.Vanishing.NadelBertiniFrameCoefficients

/-! # The actual entire original affine incidence ideal is the original linear polynomial ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAffineIncidence
open NadelBertiniUniversal NadelBertiniPolynomial NadelBertiniFrameCoefficients

private theorem originalSection_one {Y : Scheme.{u}} (L : Y.Modules) (s : Γ(L, ⊤)) :
    (SchemeModuleGlobalSections.sectionHom L s).val.app (op ⊤) (1 : Γ(Y, ⊤)) = s := by
  change (L.unitHomEquiv (L.unitHomEquiv.symm (ModularCurves.moduleSectionsOfTop L s))).val
    (op ⊤) = s
  rw [Equiv.apply_symm_apply]
  change L.val.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op s = s
  simp
  rfl

/-- The genuine whole zero ideal on an original affine global frame, with the
actual entire section and its actual original coefficient retained. -/
theorem zeroIdeal_top {Y : Scheme.{u}} [IsAffine Y] (L : Y.Modules) (hL : IsInvertible L)
    (e : L ≅ unitObj Y) (s : Γ(L, ⊤)) :
    (LineSectionZeroIdeal.zeroIdeal L hL (SchemeModuleGlobalSections.sectionHom L s)).ideal
        ⟨⊤, isAffineOpen_top Y⟩ =
      Ideal.span ({(show Γ(Y, ⊤) from e.hom.app ⊤ s)} : Set Γ(Y, ⊤)) := by
  let eO : L.over ⊤ ≅ SheafOfModules.unit (Y.ringCatSheaf.over ⊤) :=
    (SheafOfModules.overFunctor Y.ringCatSheaf ⊤).mapIso e
  have h := LineSectionZeroIdeal.zeroIdeal_ideal_of_frame L hL
    (SchemeModuleGlobalSections.sectionHom L s) ⟨⊤, isAffineOpen_top Y⟩ eO
  apply h.trans
  apply congrArg (fun r : Γ(Y, ⊤) => Ideal.span ({r} : Set Γ(Y, ⊤)))
  exact congrArg (fun z : Γ(L, ⊤) => (show Γ(Y, ⊤) from e.hom.val.app (op ⊤) z))
    (originalSection_one L s)

/-- The whole actual original universal incidence ideal is the image of the
entire original linear polynomial ideal under the actual product-ring equivalence. -/
theorem incidenceIdeal_top {R : Type u} [CommRing R] {m : ℕ}
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : IsInvertible L)
    (e : L ≅ unitObj X) (s : Fin (m + 1) → Γ(L, ⊤)) :
    (incidenceIdeal p L hL s).ideal ⟨⊤, isAffineOpen_top (product (m := m) p)⟩ =
      Ideal.map (sectionsEquiv (S := Fin (m + 1)) p).toRingHom
        (Ideal.span {∑ a, MvPolynomial.C (show Γ(X, ⊤) from e.hom.app ⊤ (s a)) * MvPolynomial.X a}) := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing R m) p
  let E := pulledFrame f L e
  have hi := zeroIdeal_top (productLine (m := m) p L) (hL.pullback f) E (universalSection p L s)
  have hc := universal_frame_coefficient p L e s
  apply hi.trans
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun r : Γ(product (m := m) p, ⊤) => Ideal.span ({r} : Set Γ(product (m := m) p, ⊤))) hc

end EnvelopeProperty.Vanishing.NadelBertiniAffineIncidence
