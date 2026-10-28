import ModularCurves.ForMathlib.SchemeModuleSheaf
import ModularCurves.ForMathlib.SheafCohomologyExact
import ModularCurves.ForMathlib.FlasqueCohomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Actual sheaf-cohomology vanishing for finite sums of scheme modules -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.SchemeFiniteSumCohomology

/-- Finite sums preserve vanishing of actual sheaf cohomology in every degree,
without quasicoherence, finite-type or flatness hypotheses. -/
theorem subsingleton_H_coproduct {X : Scheme.{u}} {I : Type} [Finite I]
    (M : I → X.Modules) (q : ℕ)
    (hM : ∀ i, Subsingleton (CategoryTheory.Sheaf.H (M i).sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H (∐ M).sheaf q) := by
  classical
  let := Fintype.ofFinite I
  let : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  let G : X.Modules ⥤ CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X)
      AddCommGrpCat.{u} := AlgebraicGeometry.Scheme.Modules.toSheaf X
  let : G.Additive := by
    change (SheafOfModules.toSheaf X.ringCatSheaf).Additive
    infer_instance
  let F : X.Modules ⥤ AddCommGrpCat.{u} := G ⋙
    CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q
  let : F.Additive := by dsimp only [F]; infer_instance
  let (i : I) : Subsingleton (F.obj (M i)) := hM i
  have hzero : IsZero (F.obj (⨁ M)) := by
    rw [IsZero.iff_id_eq_zero, ← F.map_id, ← biproduct.total, F.map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [F.map_comp, (AddCommGrpCat.isZero_of_subsingleton (F.obj (M i))).eq_of_tgt
      (F.map (biproduct.π M i)) 0, zero_comp]
  exact AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso hzero (F.mapIso (biproduct.isoCoproduct M)).symm)

end EnvelopeProperty.SchemeFiniteSumCohomology
