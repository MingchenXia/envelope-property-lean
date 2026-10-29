import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations
/-! # Actual affine subscheme sections retain their entire original projection algebra -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSubschemeSections
private theorem top_kernel {Y : Scheme.{u}} [IsAffine Y] (I : Y.IdealSheafData) :
    RingHom.ker I.subschemeι.appTop.hom = I.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
  have h := congrArg (fun J : Y.IdealSheafData => J.ideal ⟨⊤, isAffineOpen_top Y⟩)
    (Scheme.ker_of_isAffine I.subschemeι)
  have h' := h.symm
  simp only [I.ker_subschemeι, Scheme.IdealSheafData.ofIdealTop_ideal,
    homOfLE_refl, op_id] at h'
  have hm := congrArg (fun f : Γ(Y, ⊤) ⟶ Γ(Y, ⊤) =>
      Ideal.map f.hom (RingHom.ker I.subschemeι.appTop.hom))
    (Y.presheaf.map_id (op (⊤ : Y.Opens)))
  have hm' : Ideal.map (Y.presheaf.map (𝟙 (op (⊤ : Y.Opens)))).hom
      (RingHom.ker I.subschemeι.appTop.hom) = RingHom.ker I.subschemeι.appTop.hom :=
    hm.trans (Ideal.map_id _)
  exact hm'.symm.trans h'


def quotientEquivSections {Y : Scheme.{u}} [IsAffine Y] (I : Y.IdealSheafData) :
    (Γ(Y, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top Y⟩) ≃+* Γ(I.subscheme, ⊤) :=
  (Ideal.quotientEquivAlgOfEq Γ(Y, ⊤) (top_kernel I).symm).toRingEquiv.trans
    (RingHom.quotientKerEquivOfSurjective (f := I.subschemeι.appTop.hom)
      (IsClosedImmersion.isAffine_surjective_of_isAffine I.subschemeι).2)

theorem quotientEquivSections_mk {Y : Scheme.{u}} [IsAffine Y] (I : Y.IdealSheafData)
    (b : Γ(Y, ⊤)) :
    quotientEquivSections I (Ideal.Quotient.mk _ b) = I.subschemeι.appTop b := by
  rfl

def quotientAlgEquivSections {X Y : Scheme.{u}} [IsAffine Y] (I : Y.IdealSheafData)
    (g : Y ⟶ X) :
    let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    let : Algebra Γ(X, ⊤) Γ(I.subscheme, ⊤) := (I.subschemeι ≫ g).appTop.hom.toAlgebra
    (Γ(Y, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top Y⟩) ≃ₐ[Γ(X, ⊤)] Γ(I.subscheme, ⊤) := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(I.subscheme, ⊤) := (I.subschemeι ≫ g).appTop.hom.toAlgebra
  refine { toRingEquiv := quotientEquivSections I, commutes' := ?_ }
  intro b
  change quotientEquivSections I (Ideal.Quotient.mk _ (g.appTop b)) =
    (I.subschemeι ≫ g).appTop b
  rw [quotientEquivSections_mk, Scheme.Hom.comp_appTop]
  rfl
end EnvelopeProperty.Vanishing.NadelBertiniSubschemeSections
