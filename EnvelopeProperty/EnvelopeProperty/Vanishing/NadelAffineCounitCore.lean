import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverDetection
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit

/-! # Whole original morphisms detected by their affine pushforwards

Only the source module needs to be finite-type quasicoherent.  No claim of
faithfulness on the category of all sheaves of modules is made.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAffineCounitCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual top-section map determines the action on every compatible
global section, with the whole restriction maps retained. -/
theorem sectionsMap_eq_of_top {X : Scheme.{u}} {M N : X.Modules}
    {a b : M ⟶ N} (h : a.app ⊤ = b.app ⊤) (s : M.sections) :
    SheafOfModules.sectionsMap a s = SheafOfModules.sectionsMap b s := by
  apply PresheafOfModules.sections_ext
  intro U
  let t := SheafOfModules.sectionsMap a s
  let v := SheafOfModules.sectionsMap b s
  have ht := PresheafOfModules.sections_property t
    (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
  have hv := PresheafOfModules.sections_property v
    (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
  have htop : t.val (op ⊤) = v.val (op ⊤) :=
    ConcreteCategory.congr_hom h (s.val (op ⊤))
  exact ht.symm.trans ((congrArg (fun z => N.val.map
    (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op z) htop).trans hv)

/-- A true generating family makes top-section equality detect the entire
original module morphisms, even into a non-quasicoherent target. -/
theorem hom_ext_of_generators {X : Scheme.{u}} {M N : X.Modules}
    (G : M.GeneratingSections) {a b : M ⟶ N} (h : a.app ⊤ = b.app ⊤) : a = b := by
  apply (cancel_epi G.π).mp
  rw [SheafOfModules.freeHomEquiv_symm_comp, SheafOfModules.freeHomEquiv_symm_comp]
  congr 1
  funext i
  exact sectionsMap_eq_of_top h (G.s i)

/-- On the actual original affine scheme, genuine finite-type quasicoherence
internally supplies the generating family used for whole-map detection. -/
theorem hom_ext_of_affine_top {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    {a b : M ⟶ N} (h : a.app ⊤ = b.app ⊤) : a = b := by
  obtain ⟨G, _hG⟩ := exists_generatingSections_of_isFiniteType_of_isAffine M
  exact hom_ext_of_generators G h

end EnvelopeProperty.Vanishing.NadelAffineCounitCore
