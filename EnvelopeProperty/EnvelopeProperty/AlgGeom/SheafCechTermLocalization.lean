import EnvelopeProperty.AlgGeom.SheafCechKernelRestrictions
import EnvelopeProperty.Algebra.FiniteProductModuleLocalization
import ModularCurves.ForMathlib.SheafModuleCechSectionsDifferential

/-! # Same actual finite Cech term restrictions retain localization -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SheafCechTermLocalization

open SheafCechKernelRestrictions
variable {A : Type u} [CommRing A] {T : TopCat.{u}}
variable (F : TopCat.Sheaf (ModuleCat.{u} A) T)
variable {ι : Type u} (U : ι → Opens T)

/-- Each SAME original intersection restriction with its original coefficient action. -/
def factorRestriction {V W : Opens T} (h : V ≤ W) (n : ℕ) (i : Fin (n + 1) → ι) :
    F.obj.obj (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) →ₗ[A]
      F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  (F.obj.map (homOfLE (inf_le_inf_right
    (∏ᶜ fun k : Fin (n + 1) => U (i k)) h)).op).hom

/-- Every original coordinate of the true native term equivalence retains restriction. -/
theorem termSections_restrict_apply {V W : Opens T} (h : V ≤ W) (n : ℕ)
    (x : (TopCat.Sheaf.moduleCechSectionsComplex F U W).X n)
    (i : Fin (n + 1) → ι) :
    TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n V
        ((termRestriction F U h n).hom x) i =
      factorRestriction F U h n i
        (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n W x i) := by
  have hl := TopCat.Sheaf.moduleCechTermSectionsLinearEquiv_apply F U n V
    ((termRestriction F U h n).hom x) i
  have hr := TopCat.Sheaf.moduleCechTermSectionsLinearEquiv_apply F U n W x i
  have hp := ConcreteCategory.congr_hom
    ((Pi.π (TopCat.Sheaf.moduleCechTermFactor F U n) i).hom.naturality (homOfLE h).op) x
  have hfactor :
      (TopCat.Sheaf.moduleCechTermFactorSectionsIso F U n V i).hom
          (((TopCat.Sheaf.moduleCechTermFactor F U n i).obj.map (homOfLE h).op).hom
            ((Pi.π (TopCat.Sheaf.moduleCechTermFactor F U n) i).hom.app (op W) x)) =
        factorRestriction F U h n i
          ((TopCat.Sheaf.moduleCechTermFactorSectionsIso F U n W i).hom
            ((Pi.π (TopCat.Sheaf.moduleCechTermFactor F U n) i).hom.app (op W) x)) := by
    change (F.obj.map _ ≫ F.obj.map _) _ = (F.obj.map _ ≫ F.obj.map _) _
    exact ConcreteCategory.congr_hom
      ((F.obj.map_comp _ _).symm.trans
        ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
          (F.obj.map_comp _ _))) _
  exact hl.trans ((congrArg
    (fun y => (TopCat.Sheaf.moduleCechTermFactorSectionsIso F U n V i).hom y) hp).trans
      (hfactor.trans (congrArg (factorRestriction F U h n i) hr.symm)))

/-- The ENTIRE native term equivalence gives the actual coordinate restriction square. -/
theorem termSections_restrict {V W : Opens T} (h : V ≤ W) (n : ℕ) :
    (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n V).toLinearMap ∘ₗ
        (termRestriction F U h n).hom =
      FiniteProductModuleLocalization.piMap (factorRestriction F U h n) ∘ₗ
        (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n W).toLinearMap := by
  ext x i
  exact termSections_restrict_apply F U h n x i

/-- TRUE localizations of the finite actual intersection restrictions imply
localization of the SAME whole original native Cech term restriction. -/
theorem termRestriction_isLocalizedModule [Finite ι] {V W : Opens T}
    (h : V ≤ W) (n : ℕ) (S : Submonoid A)
    [∀ i : Fin (n + 1) → ι, IsLocalizedModule S (factorRestriction F U h n i)] :
    IsLocalizedModule S (termRestriction F U h n).hom := by
  apply (IsLocalizedModule.comp_iff_of_bijective_left S
    (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n V).toLinearMap
    (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n V).bijective).mp
  rw [termSections_restrict]
  exact (IsLocalizedModule.comp_iff_of_bijective_right S
    (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n W).toLinearMap
    (TopCat.Sheaf.moduleCechTermSectionsLinearEquiv F U n W).bijective).mpr
      (FiniteProductModuleLocalization.piMap_isLocalizedModule S (factorRestriction F U h n))

end EnvelopeProperty.SheafCechTermLocalization
