import EnvelopeProperty.Vanishing.NadelBertiniFibreIdeals
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves
import Hironaka.Scheme.Modules.IdealSheaf
/-! # A section of the original invertible ideal retains its whole original product ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsIdeal
private theorem overFrame_reconstruct {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (z : Γ(M, U)) :
    z = (show Γ(X, U) from e.hom.val.app (op (Over.mk (𝟙 U))) z) •
      (show Γ(M, U) from e.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) := by
  have he := congrArg (fun f => f.val.app (op (Over.mk (𝟙 U))) z) e.hom_inv_id
  change (show Γ(M, U) from e.inv.val.app (op (Over.mk (𝟙 U)))
    (e.hom.val.app (op (Over.mk (𝟙 U))) z)) = z at he
  apply he.symm.trans
  let c : Γ(X, U) := e.hom.val.app (op (Over.mk (𝟙 U))) z
  have hs := (e.inv.val.app (op (Over.mk (𝟙 U)))).hom.map_smul c (1 : Γ(X, U))
  change (show Γ(M, U) from e.inv.val.app (op (Over.mk (𝟙 U))) (c * (1 : Γ(X, U)))) =
    c • (show Γ(M, U) from e.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at hs
  rw [mul_one] at hs
  exact hs

theorem ideal_eq_span_of_frame {X : Scheme.{u}} (D : X.IdealSheafData) (U : X.affineOpens)
    (e : D.toModules.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    D.ideal U = Ideal.span ({D.toModulesInclusion.val.app (op U.1)
      (e.inv.val.app (op (Over.mk (𝟙 U.1))) (1 : Γ(X, U.1)))} : Set Γ(X, U.1)) := by
  let z0 : Γ(D.toModules, U.1) := e.inv.val.app (op (Over.mk (𝟙 U.1))) (1 : Γ(X, U.1))
  let d : Γ(X, U.1) := D.toModulesInclusion.val.app (op U.1) z0
  change D.ideal U = Ideal.span {d}
  apply le_antisymm
  · intro r hr
    let z := (D.toModulesSectionsEquiv U).symm ⟨r, hr⟩
    have hz : D.toModulesInclusion.val.app (op U.1) z = r := rfl
    have he := overFrame_reconstruct D.toModules U.1 e z
    have hh := congrArg (D.toModulesInclusion.val.app (op U.1)) he
    let c : Γ(X, U.1) := e.hom.val.app (op (Over.mk (𝟙 U.1))) z
    have hm := (D.toModulesInclusion.val.app (op U.1)).hom.map_smul c z0
    have hh' : r = c * d := hh.trans hm
    rw [hh']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self d)
  · apply Ideal.span_le.mpr
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact (D.toModulesSectionsEquiv U z0).property
theorem ideal_section_product_ideal {X : Scheme.{u}} (D : X.IdealSheafData)
    (hD : IsInvertible D.toModules) (δ : unitObj X ⟶ D.toModules) (U : X.affineOpens)
    (e : D.toModules.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    (LineSectionZeroIdeal.zeroIdeal (unitObj X) (isInvertible_unit (X := X)) (δ ≫ D.toModulesInclusion)).ideal U =
      (D * LineSectionZeroIdeal.zeroIdeal D.toModules hD δ).ideal U := by
  let z : Γ(D.toModules, U.1) := δ.val.app (op U.1) (1 : Γ(X, U.1))
  let z0 : Γ(D.toModules, U.1) := e.inv.val.app (op (Over.mk (𝟙 U.1))) (1 : Γ(X, U.1))
  let c : Γ(X, U.1) := e.hom.val.app (op (Over.mk (𝟙 U.1))) z
  let d : Γ(X, U.1) := D.toModulesInclusion.val.app (op U.1) z0
  have hz := overFrame_reconstruct D.toModules U.1 e z
  have h1 := congrArg (D.toModulesInclusion.val.app (op U.1)) hz
  have h2 := (D.toModulesInclusion.val.app (op U.1)).hom.map_smul c z0
  have heq : D.toModulesInclusion.val.app (op U.1) z = c * d := h1.trans h2
  rw [LineSectionZeroIdeal.zeroIdeal_ideal_of_frame (unitObj X) (isInvertible_unit (X := X))
      (δ ≫ D.toModulesInclusion) U (Iso.refl _), Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    ideal_eq_span_of_frame D U e, LineSectionZeroIdeal.zeroIdeal_ideal_of_frame D.toModules hD δ U e]
  change Ideal.span {(show Γ(X, U.1) from D.toModulesInclusion.val.app (op U.1) z)} = Ideal.span {d} * Ideal.span {c}
  rw [Ideal.span_singleton_mul_span_singleton, heq, mul_comm c d]

theorem ideal_section_product {X : Scheme.{u}} (D : X.IdealSheafData) (hD : D.IsInvertible)
    (δ : unitObj X ⟶ D.toModules) :
    LineSectionZeroIdeal.zeroIdeal (unitObj X) (isInvertible_unit (X := X)) (δ ≫ D.toModulesInclusion) =
      D * LineSectionZeroIdeal.zeroIdeal D.toModules hD.isInvertibleModule_toModules δ := by
  classical
  choose U hx eU using fun x : X =>
    NadelBertiniFibreIdeals.exists_affine_frame D.toModules hD.isInvertibleModule_toModules x
  have hcover : ⨆ x, (U x).1 = ⊤ :=
    top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro x
  let e := overTrivializationOfRestrictIso D.toModules (U x).1
    (restrictIsoOfPullbackIso D.toModules (U x).1 (eU x).some)
  exact ideal_section_product_ideal D hD.isInvertibleModule_toModules δ (U x) e

end EnvelopeProperty.Vanishing.NadelAuxiliaryBranchSectionsIdeal
