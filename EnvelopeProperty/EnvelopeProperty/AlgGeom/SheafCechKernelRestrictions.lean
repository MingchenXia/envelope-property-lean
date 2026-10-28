import EnvelopeProperty.AlgGeom.SchemeModuleOpenSectionsKernel
import EnvelopeProperty.Algebra.LocalizedKernelSquares

/-! # SAME actual sheaf-Cech restriction on whole original kernels -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.SheafCechKernelRestrictions

variable {A : Type u} [CommRing A] {T : TopCat.{u}}
variable (F : TopCat.Sheaf (ModuleCat.{u} A) T)
variable {ι : Type u} (U : ι → Opens T)

/-- The SAME original sheaf term restriction, retaining the whole coefficient action. -/
def termRestriction {V W : Opens T} (h : V ≤ W) (n : ℕ) :
    (TopCat.Sheaf.moduleCechSectionsComplex F U W).X n ⟶
      (TopCat.Sheaf.moduleCechSectionsComplex F U V).X n :=
  (TopCat.Sheaf.moduleCechTerm F U n).obj.map (homOfLE h).op

/-- Original sheaf naturality gives the ENTIRE actual differential square. -/
theorem differential_square {V W : Opens T} (h : V ≤ W) :
    termRestriction F U h 0 ≫ (TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1 =
      (TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1 ≫ termRestriction F U h 1 := by
  rw [TopCat.Sheaf.moduleCechSectionsComplex_d F U V 0,
    TopCat.Sheaf.moduleCechSectionsComplex_d F U W 0]
  exact (TopCat.Sheaf.moduleCechDifferential F U 0).hom.naturality (homOfLE h).op

/-- The square is the SAME actual square of original coefficient-linear maps. -/
theorem differential_square_linear {V W : Opens T} (h : V ≤ W) :
    ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom ∘ₗ
        (termRestriction F U h 0).hom =
      (termRestriction F U h 1).hom ∘ₗ
        ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom :=
  congrArg ModuleCat.Hom.hom (differential_square F U h)

/-- The actual original term restriction on the SAME two evaluated kernels. -/
def kernelRestriction {V W : Opens T} (h : V ≤ W) :
    LinearMap.ker ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom →ₗ[A]
      LinearMap.ker ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom :=
  LocalizedKernelSquares.kernelMap
    ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom
    ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom
    (termRestriction F U h 0).hom (termRestriction F U h 1).hom
    (differential_square_linear F U h)

/-- EVERY actual kernel element keeps its SAME original restricted value. -/
theorem kernelRestriction_apply {V W : Opens T} (h : V ≤ W)
    (s : LinearMap.ker ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom) :
    (kernelRestriction F U h s : (TopCat.Sheaf.moduleCechSectionsComplex F U V).X 0) =
      (termRestriction F U h 0).hom s := rfl

/-- The actual kernel inclusion square is the WHOLE original degree-zero restriction. -/
theorem kernelRestriction_subtype {V W : Opens T} (h : V ≤ W) :
    ModuleCat.ofHom (kernelRestriction F U h) ≫
        ModuleCat.ofHom (LinearMap.ker
          ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom).subtype =
      ModuleCat.ofHom (LinearMap.ker
        ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom).subtype ≫
        termRestriction F U h 0 := rfl

private theorem kernel_equivalences_natural {V W : Opens T} (h : V ≤ W)
    {P Q : ModuleCat.{u} A}
    (eW : P ≅ ModuleCat.of A (LinearMap.ker
      ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom))
    (eV : Q ≅ ModuleCat.of A (LinearMap.ker
      ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom))
    (aW : P ⟶ (TopCat.Sheaf.moduleCechSectionsComplex F U W).X 0)
    (aV : Q ⟶ (TopCat.Sheaf.moduleCechSectionsComplex F U V).X 0)
    (f : P ⟶ Q)
    (hW : eW.hom ≫ ModuleCat.ofHom (LinearMap.ker
      ((TopCat.Sheaf.moduleCechSectionsComplex F U W).d 0 1).hom).subtype = aW)
    (hV : eV.hom ≫ ModuleCat.ofHom (LinearMap.ker
      ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom).subtype = aV)
    (hf : f ≫ aV = aW ≫ termRestriction F U h 0) :
    f ≫ eV.hom = eW.hom ≫ ModuleCat.ofHom (kernelRestriction F U h) := by
  apply (cancel_mono (ModuleCat.ofHom (LinearMap.ker
    ((TopCat.Sheaf.moduleCechSectionsComplex F U V).d 0 1).hom).subtype)).1
  simp only [Category.assoc]
  rw [hV, kernelRestriction_subtype, ← Category.assoc, hW]
  exact hf

/-- The WHOLE original section restriction agrees with the SAME actual
evaluated Cech kernel restriction, with its original base coefficient action. -/
theorem openSectionsKernelIso_naturality {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    {V W : X.Opens} (h : V ≤ W) :
    (Scheme.Modules.baseModulePresheaf π M).map (homOfLE h).op ≫
        (SchemeModuleOpenSectionsKernel.openSectionsKernelIso π M U hU V).hom =
      (SchemeModuleOpenSectionsKernel.openSectionsKernelIso π M U hU W).hom ≫
        ModuleCat.ofHom (kernelRestriction (Scheme.Modules.baseModuleTopSheaf π M) U h) := by
  apply kernel_equivalences_natural (Scheme.Modules.baseModuleTopSheaf π M) U h
    (SchemeModuleOpenSectionsKernel.openSectionsKernelIso π M U hU W)
    (SchemeModuleOpenSectionsKernel.openSectionsKernelIso π M U hU V)
    ((TopCat.Sheaf.moduleCechAugmentation
      (Scheme.Modules.baseModuleTopSheaf π M) U).hom.app (op W))
    ((TopCat.Sheaf.moduleCechAugmentation
      (Scheme.Modules.baseModuleTopSheaf π M) U).hom.app (op V))
    ((Scheme.Modules.baseModulePresheaf π M).map (homOfLE h).op)
    (SchemeModuleOpenSectionsKernel.openSectionsKernelIso_hom_subtype π M U hU W)
    (SchemeModuleOpenSectionsKernel.openSectionsKernelIso_hom_subtype π M U hU V)
  exact (TopCat.Sheaf.moduleCechAugmentation
    (Scheme.Modules.baseModuleTopSheaf π M) U).hom.naturality (homOfLE h).op

end EnvelopeProperty.SheafCechKernelRestrictions
