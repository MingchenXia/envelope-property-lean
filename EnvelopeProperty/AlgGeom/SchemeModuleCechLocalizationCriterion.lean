import EnvelopeProperty.AlgGeom.SheafCechKernelRestrictions

/-! # Actual whole section localization from SAME native Cech term localizations -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleCechLocalizationCriterion

open SheafCechKernelRestrictions

/-- Native localization properties themselves DERIVE the localized target
actions and the SAME actual kernel restriction is a localization. -/
theorem kernelRestriction_isLocalizedModule {A : Type u} [CommRing A] {T : TopCat.{u}}
    (F : TopCat.Sheaf (ModuleCat.{u} A) T) {ι : Type u} (U : ι → Opens T)
    {V W : Opens T} (h : V ≤ W) (S : Submonoid A)
    [IsLocalizedModule S (termRestriction F U h 0).hom]
    [IsLocalizedModule S (termRestriction F U h 1).hom] :
    IsLocalizedModule S (kernelRestriction F U h) := by
  let Aₛ := Localization S
  let : Module Aₛ ((TopCat.Sheaf.moduleCechSectionsComplex F U V).X 0) :=
    IsLocalizedModule.module (A := Aₛ) S (termRestriction F U h 0).hom
  let : Module Aₛ ((TopCat.Sheaf.moduleCechSectionsComplex F U V).X 1) :=
    IsLocalizedModule.module (A := Aₛ) S (termRestriction F U h 1).hom
  let : IsScalarTower A Aₛ ((TopCat.Sheaf.moduleCechSectionsComplex F U V).X 0) :=
    IsLocalizedModule.isScalarTower_module (A := Aₛ) S (termRestriction F U h 0).hom
  let : IsScalarTower A Aₛ ((TopCat.Sheaf.moduleCechSectionsComplex F U V).X 1) :=
    IsLocalizedModule.isScalarTower_module (A := Aₛ) S (termRestriction F U h 1).hom
  exact LocalizedKernelSquares.kernelMap_isLocalizedModule Aₛ S
    ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom
    ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom
    (termRestriction F U h 0).hom (termRestriction F U h 1).hom
    (differential_square_linear F U h)

private theorem localizes_of_kernel_square {A : Type u} [CommRing A]
    (S : Submonoid A) {P Q K L : ModuleCat.{u} A}
    (eP : P ≅ K) (eQ : Q ≅ L) (f : P ⟶ Q) (g : K ⟶ L)
    [IsLocalizedModule S g.hom] (comm : f ≫ eQ.hom = eP.hom ≫ g) :
    IsLocalizedModule S f.hom := by
  have hc : eQ.hom.hom ∘ₗ f.hom = g.hom ∘ₗ eP.hom.hom :=
    congrArg ModuleCat.Hom.hom comm
  apply (IsLocalizedModule.comp_iff_of_bijective_left S eQ.hom.hom
    (ConcreteCategory.bijective_of_isIso eQ.hom)).mp
  rw [hc]
  exact (IsLocalizedModule.comp_iff_of_bijective_right S eP.hom.hom
    (ConcreteCategory.bijective_of_isIso eP.hom)).mpr inferInstance

/-- The whole ORIGINAL section restriction is localized, from the actual
two original Cech term localizations and the internally proved kernel diagram. -/
theorem sectionRestriction_isLocalizedModule {X B : Scheme.{u}} (π : X ⟶ B)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    {V W : X.Opens} (h : V ≤ W) (S : Submonoid Γ(B, ⊤))
    [IsLocalizedModule S (termRestriction (Scheme.Modules.baseModuleTopSheaf π M) U h 0).hom]
    [IsLocalizedModule S (termRestriction (Scheme.Modules.baseModuleTopSheaf π M) U h 1).hom] :
    IsLocalizedModule S ((Scheme.Modules.baseModulePresheaf π M).map (homOfLE h).op).hom := by
  let := kernelRestriction_isLocalizedModule (Scheme.Modules.baseModuleTopSheaf π M) U h S
  exact localizes_of_kernel_square S
    (SchemeModuleOpenSectionsKernel.openSectionsKernelIso π M U hU W)
    (SchemeModuleOpenSectionsKernel.openSectionsKernelIso π M U hU V)
    ((Scheme.Modules.baseModulePresheaf π M).map (homOfLE h).op)
    (ModuleCat.ofHom (kernelRestriction (Scheme.Modules.baseModuleTopSheaf π M) U h))
    (openSectionsKernelIso_naturality π M U hU h)

end EnvelopeProperty.SchemeModuleCechLocalizationCriterion
