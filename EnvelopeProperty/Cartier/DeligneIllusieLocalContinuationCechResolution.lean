import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechAbelianExchange
import ModularCurves.ForMathlib.SheafCechSheafResolution
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.SingleHomology

/-! # The same original module Cech augmentation is a quasi-isomorphism for an honest cover -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechResolution
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace Opposite
open DeligneIllusieLocalContinuationCechModules DeligneIllusieLocalContinuationCechAugmentation
open DeligneIllusieLocalContinuationCechAbelianExchange
universe u
variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- The SAME native module complex with the original actual augmentation inserted before it. -/
def augmentedComplex : CochainComplex X.Modules ℕ :=
  CochainComplex.augment (complex M U) (augmentation U M) (augmentation_comp_d U M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire actual augmented exchange, constructed from the original units and whole complex iso. -/
def augmentedIso :
    ((forgetAb X).mapHomologicalComplex (.up ℕ)).obj (augmentedComplex M U) ≅
      TopCat.Sheaf.cechAugmentedComplex ((forgetAb X).obj M) U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => match q with
      | 0 => Iso.refl _
      | q+1 => termIso M U q) (by
    rintro q _ (rfl : q+1 = _)
    cases q with
    | zero =>
      change 𝟙 _ ≫ TopCat.Sheaf.cechAugmentation ((forgetAb X).obj M) U =
        (forgetAb X).map (augmentation U M) ≫ (termIso M U 0).hom
      exact (Category.id_comp _).trans (augmentation_compatibility M U).symm
    | succ q =>
      exact (complexIso M U).hom.comm q (q+1))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual cover acyclicity is reflected to the original module category, without an exactness input. -/
theorem augmented_acyclic (hU : ⨆ i, U i = ⊤) : (augmentedComplex M U).Acyclic := by
  intro q
  apply (forgetAb X).reflects_exact_of_faithful ((augmentedComplex M U).sc q)
  change (((forgetAb X).mapHomologicalComplex (.up ℕ)).obj
    (augmentedComplex M U)).ExactAt q
  exact ((TopCat.Sheaf.cechAugmentedComplex_acyclic ((forgetAb X).obj M) U hU) q).of_iso
    (augmentedIso M U).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original augmentation monicity is internally derived from the honest cover. -/
theorem augmentation_mono (hU : ⨆ i, U i = ⊤) : Mono (augmentation U M) := by
  have h := augmented_acyclic M U hU 0
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)] at h
  exact (ShortComplex.exact_iff_mono _ rfl).mp h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME original augmentation/first-differential short complex is actually exact. -/
theorem augmentation_exact (hU : ⨆ i, U i = ⊤) :
    (ShortComplex.mk (augmentation U M) ((complex M U).d 0 1)
      (augmentation_comp_d U M)).Exact := by
  have h := augmented_acyclic M U hU 1
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ALL positive degrees of the SAME original native module Cech complex are actually exact. -/
theorem complex_exactAt_positive (hU : ⨆ i, U i = ⊤) (q : ℕ) :
    (complex M U).ExactAt (q+1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q+1) (q+2) (by simp) (by simp)]
  have h := augmented_acyclic M U hU (q+2)
  rw [HomologicalComplex.exactAt_iff' _ (q+1) (q+2) (q+3) (by simp) (by simp)] at h
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', augmentedComplex,
    CochainComplex.augment_X_succ, CochainComplex.augment_d_succ_succ] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual quasi-isomorphism of the ORIGINAL module augmentation; no row exactness or mono input. -/
theorem augmentation_quasiIso (hU : ⨆ i, U i = ⊤) :
    QuasiIso (augmentationCochainMap U M) := by
  rw [quasiIso_iff]
  rintro (_ | q)
  · rw [CochainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_of_zeros _
      (by
        change ((CochainComplex.single₀ X.Modules).obj M).d 0 0 = 0
        exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 0)
      (by
        change ((CochainComplex.single₀ X.Modules).obj M).d 0 1 = 0
        exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 1)
      (by exact (complex M U).shape 0 0 (by simp))]
    change (ShortComplex.mk ((augmentationCochainMap U M).f 0) ((complex M U).d 0 1) _).Exact ∧
      Mono ((augmentationCochainMap U M).f 0)
    simpa only [augmentationCochainMap_f_zero] using
      And.intro (augmentation_exact M U hU) (augmentation_mono M U hU)
  · apply (quasiIsoAt_iff_exactAt _ _
      (HomologicalComplex.exactAt_single_obj (.up ℕ) 0 M (q+1) (Nat.succ_ne_zero q))).mpr
    exact complex_exactAt_positive M U hU q

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechResolution
