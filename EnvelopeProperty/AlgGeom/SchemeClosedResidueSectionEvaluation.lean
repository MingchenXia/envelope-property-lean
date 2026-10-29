import EnvelopeProperty.AlgGeom.AffineModuleFlatBaseChange
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import EnvelopeProperty.AlgGeom.SchemePointClosureCurve
/-! # Literal whole original global sections evaluated linearly in SAME native residue fields -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeClosedResidueSectionEvaluation
variable {E : Type u} [Field E] {X : Scheme.{u}}
    (b : X ⟶ Spec (.of E)) (M : X.Modules)

/-- The whole actual original base coefficient evaluated at its SAME native point. -/
def coefficients (x : X) : E →+* X.residueField x :=
  (X.Γevaluation x).hom.comp (ProperBirationalSections.coefficientMap b)

/-- EVERY native coefficient agrees with the actual original structure-stalk-residue action. -/
theorem coefficients_eq_native (x : X) :
    letI := SchemePointClosureCurve.residueAlgebra x b
    coefficients b x = algebraMap E (X.residueField x) := by
  rfl

/-- Restrict the SAME whole original section, apply its actual local frame, then native germ/residue. -/
def value (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (s : Γ(M,⊤)) : X.residueField x :=
  X.evaluation U.1 x hx (e.hom.val.app (op (Over.mk (𝟙 U.1)))
    (M.val.map (homOfLE (le_top : U.1 ≤ ⊤)).op s))

/-- The SAME entire original section module carries its genuine E-linear native residue evaluation. -/
def linearMap (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    letI := (coefficients b x).toAlgebra
    AffineModuleFlatBaseChange.sections b M →ₗ[E] X.residueField x := by
  let := (coefficients b x).toAlgebra
  refine { toFun := value M U x hx e, map_add' := ?_, map_smul' := ?_ }
  · intro s t
    simp only [value,map_add]
  · intro a s
    change X.evaluation U.1 x hx (e.hom.val.app (op (Over.mk (𝟙 U.1)))
      (M.val.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        ((ProperBirationalSections.coefficientMap b a) • s))) =
      coefficients b x a * value M U x hx e s
    rw [M.val.map_smul,(e.hom.val.app (op (Over.mk (𝟙 U.1)))).hom.map_smul]
    change X.evaluation U.1 x hx
      ((X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ProperBirationalSections.coefficientMap b a)) *
        (show Γ(X,U.1) from (e.hom.val.app (op (Over.mk (𝟙 U.1))))
          (M.val.map (homOfLE (le_top : U.1 ≤ ⊤)).op s))) = _
    rw [map_mul]
    congr 1
    change X.residue x (X.presheaf.germ U.1 x hx
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (ProperBirationalSections.coefficientMap b a))) =
      X.residue x (X.presheaf.germ ⊤ x trivial (ProperBirationalSections.coefficientMap b a))
    rw [X.presheaf.germ_res_apply]

/-- Its true linear kernel is EXACTLY the actual zero-ideal support condition for the SAME original section. -/
theorem value_eq_zero_iff (hM : IsInvertible M) (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) (s : Γ(M,⊤)) :
    value M U x hx e s = 0 ↔
      x ∈ (LineSectionZeroIdeal.zeroIdeal M hM (SchemeModuleGlobalSections.sectionHom M s)).support := by
  let I := LineSectionZeroIdeal.zeroIdeal M hM (SchemeModuleGlobalSections.sectionHom M s)
  rw [I.mem_support_iff_of_mem hx,LineSectionZeroIdeal.zeroIdeal_ideal_of_frame M hM _ U e,
    X.zeroLocus_span,X.zeroLocus_singleton]
  change value M U x hx e s = 0 ↔ x ∉ X.basicOpen _
  rw [← X.evaluation_eq_zero_iff_notMem_basicOpen x hx]
  have hs : (SchemeModuleGlobalSections.sectionHom M s).val.app (op U.1) (1 : Γ(X,U.1)) =
      M.val.map (homOfLE (le_top : U.1 ≤ ⊤)).op s := by
    change (1 : Γ(X,U.1)) • M.val.map (homOfLE (le_top : U.1 ≤ ⊤)).op s = _
    exact one_smul _ _
  rw [hs]
  rfl
end EnvelopeProperty.SchemeClosedResidueSectionEvaluation
