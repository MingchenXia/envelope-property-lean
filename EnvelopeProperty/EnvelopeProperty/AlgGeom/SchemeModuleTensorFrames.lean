import ModularCurves.EllipticCurve.PoleSheaf

/-! # Actual tensor frames retain original restriction and scalar transitions -/
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleTensorFrames
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The actual canonical coefficient-preserving frame of the original tensor module. -/
def tensorFrame (U : X.Opens) (e : M.restrict U.ι ≅ unitObj U.toScheme)
    (g : N.restrict U.ι ≅ unitObj U.toScheme) :
    (M ⊗ N).restrict U.ι ≅ unitObj U.toScheme :=
  ModularCurves.restrictMonoidalTensorIso U.ι M N ≪≫ (e ⊗ᵢ g) ≪≫
    ModularCurves.unitObjTensorIso U.toScheme

/-- Restriction of the true original tensor frame is the tensor frame of
those SAME original restricted module frames. -/
theorem tensorFrame_restrict {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme)
    (g : N.restrict U.ι ≅ unitObj U.toScheme) :
    restrictOpenTrivialization h (tensorFrame M N U e g) =
      tensorFrame M N V (restrictOpenTrivialization h e)
        (restrictOpenTrivialization h g) :=
  ModularCurves.restrictMonoidalTensorTrivialization_restrictOpen M N h e g

/-- Tensoring genuine original frame changes multiplies their actual
original whole scalar transition functions. -/
theorem tensorFrame_hom_eq_comp_scalars (U : X.Opens)
    (e e' : M.restrict U.ι ≅ unitObj U.toScheme)
    (g g' : N.restrict U.ι ≅ unitObj U.toScheme)
    (r s : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
    (he : e.hom = e'.hom ≫ ModularCurves.unitEndomorphismOfTopSection r)
    (hg : g.hom = g'.hom ≫ ModularCurves.unitEndomorphismOfTopSection s) :
    (tensorFrame M N U e g).hom =
      (tensorFrame M N U e' g').hom ≫ ModularCurves.unitEndomorphismOfTopSection (r*s) := by
  have htensor₀ : e.hom ⊗ₘ g.hom =
      (e'.hom ≫ ModularCurves.unitEndomorphismOfTopSection r) ⊗ₘ
        (g'.hom ≫ ModularCurves.unitEndomorphismOfTopSection s) :=
    congrArg₂ (fun a b => a ⊗ₘ b) he hg
  have htensor : e.hom ⊗ₘ g.hom = (e'.hom ⊗ₘ g'.hom) ≫
      (ModularCurves.unitEndomorphismOfTopSection r ⊗ₘ
        ModularCurves.unitEndomorphismOfTopSection s) :=
    htensor₀.trans (tensorHom_comp_tensorHom e'.hom g'.hom
      (ModularCurves.unitEndomorphismOfTopSection r)
      (ModularCurves.unitEndomorphismOfTopSection s)).symm
  simp only [tensorFrame, Iso.trans_hom, tensorIso_hom, Category.assoc]
  rw [htensor]
  simp only [Category.assoc]
  rw [ModularCurves.unitObjTensorIso_hom_comp_scalars]

end EnvelopeProperty.SchemeModuleTensorFrames
