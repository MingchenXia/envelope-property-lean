import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsMonoidal
import EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsIdeal
/-! # Actual original tensor-inclusion sections have the exact whole original branch product -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSections
open NadelAuxiliaryBranchSectionsMonoidal NadelAuxiliaryBranchSectionsIdeal NadelBertiniFibreIdeals
  SchemeLineSectionEvaluation
variable {X : Scheme.{u}}

def branchSection (M : X.Modules) (D : X.IdealSheafData) (α : unitObj X ⟶ tensorObj M D.toModules) : unitObj X ⟶ M :=
  α ≫ SchemeTensorObjMorphisms.tensorObjIdealMap M D.toModules D.toModulesInclusion

theorem zeroIdeal_branch_of_frame (M : X.Modules) (hM : IsInvertible M)
    (D : X.IdealSheafData) (hD : D.IsInvertible) (e : M ≅ unitObj X)
    (α : unitObj X ⟶ tensorObj M D.toModules) :
    LineSectionZeroIdeal.zeroIdeal M hM (branchSection M D α) =
      D * LineSectionZeroIdeal.zeroIdeal (tensorObj M D.toModules) (hM.tensorObj hD.isInvertibleModule_toModules) α := by
  let T := SchemeTensorObjMorphisms.tensorObjIdealMap M D.toModules D.toModulesInclusion
  let E := untwist M D.toModules e
  let δ := α ≫ E.hom
  have hα := zeroIdeal_iso (tensorObj M D.toModules) D.toModules (hM.tensorObj hD.isInvertibleModule_toModules)
    hD.isInvertibleModule_toModules E α
  have hs := zeroIdeal_iso M (unitObj X) hM (isInvertible_unit (X := X)) e (α ≫ T)
  have hcomp : (α ≫ T) ≫ e.hom = δ ≫ D.toModulesInclusion := by
    exact (Category.assoc α T e.hom).trans
      ((congrArg (fun h => α ≫ h) (untwist_inclusion M D.toModules e D.toModulesInclusion)).trans
        (Category.assoc α E.hom D.toModulesInclusion).symm)
  rw [hcomp] at hs
  exact hs.trans ((ideal_section_product D hD δ).trans (congrArg (fun J : X.IdealSheafData => D * J) hα.symm))
theorem branchSection_pullback {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (D : X.IdealSheafData) (α : unitObj X ⟶ tensorObj M D.toModules) :
    branchSection ((pullback f).obj M) (D.comap f)
      (pullbackSectionHom f α ≫ (SchemeTensorIdealPullback.idealTensorOpenPullbackIso f M D).hom) =
      pullbackSectionHom f (branchSection M D α) := by
  unfold branchSection
  rw [Category.assoc, SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion]
  unfold pullbackSectionHom
  rw [Functor.map_comp, Category.assoc]

theorem zeroIdeal_branch (M : X.Modules) (hM : IsInvertible M) (D : X.IdealSheafData)
    (hD : D.IsInvertible) (α : unitObj X ⟶ tensorObj M D.toModules) :
    LineSectionZeroIdeal.zeroIdeal M hM (branchSection M D α) =
      D * LineSectionZeroIdeal.zeroIdeal (tensorObj M D.toModules) (hM.tensorObj hD.isInvertibleModule_toModules) α := by
  classical
  let P := tensorObj M D.toModules
  let hP := hM.tensorObj hD.isInvertibleModule_toModules
  let Zs := LineSectionZeroIdeal.zeroIdeal M hM (branchSection M D α)
  let Za := LineSectionZeroIdeal.zeroIdeal P hP α
  choose U hx eU using fun x : X => exists_affine_frame M hM x
  have hcover : ⨆ x, (U x).1 = ⊤ := top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro x
  let f := (U x).1.ι
  let : IsAffine (U x).1.toScheme := (U x).2
  let M' := (pullback f).obj M
  let D' := D.comap f
  let hM' := hM.pullback f
  let hD' := hD.comap_of_isOpenImmersion f
  let E := SchemeTensorIdealPullback.idealTensorOpenPullbackIso f M D
  let α' := pullbackSectionHom f α ≫ E.hom
  let P' := tensorObj M' D'.toModules
  let hP' := hM'.tensorObj hD'.isInvertibleModule_toModules
  have hloc := zeroIdeal_branch_of_frame M' hM' D' hD' (eU x).some α'
  have ha0 := zeroIdeal_comap f P hP α
  have ha1 := zeroIdeal_iso ((pullback f).obj P) P' (hP.pullback f) hP' E (pullbackSectionHom f α)
  have ha : Za.comap f = LineSectionZeroIdeal.zeroIdeal P' hP' α' := ha0.trans ha1
  have hs := zeroIdeal_comap f M hM (branchSection M D α)
  have hc := branchSection_pullback f M D α
  have hs' : Zs.comap f = D' * Za.comap f :=
    hs.trans ((congrArg (LineSectionZeroIdeal.zeroIdeal M' hM') hc.symm).trans
      (hloc.trans (congrArg (fun J : (U x).1.toScheme.IdealSheafData => D' * J) ha.symm)))
  have htop := congrArg (fun J : (U x).1.toScheme.IdealSheafData => J.ideal ⟨⊤, isAffineOpen_top _⟩) hs'
  have hm := congrArg (Ideal.map (U x).1.topIso.hom.hom) htop
  change Ideal.map (U x).1.topIso.hom.hom ((Zs.comap (U x).1.ι).ideal ⟨⊤, isAffineOpen_top _⟩) =
    Ideal.map (U x).1.topIso.hom.hom
      (((D.comap (U x).1.ι).ideal ⟨⊤, isAffineOpen_top _⟩) *
        ((Za.comap (U x).1.ι).ideal ⟨⊤, isAffineOpen_top _⟩)) at hm
  rw [Ideal.map_mul, map_comap_top, map_comap_top, map_comap_top] at hm
  change Zs.ideal (U x) = (D * Za).ideal (U x)
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  exact hm

end EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSections
