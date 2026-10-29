import EnvelopeProperty.AlgGeom.NativePulledProjectiveSectionNorms
import EnvelopeProperty.AlgGeom.SchemeScalarModulePresheaf

/-! # The pulled-line section equivalence is linear over the base field -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite
open Alterations Scheme.Modules
open scoped Classical
noncomputable section
universe u
namespace EnvelopeProperty.NativePulledProjectiveLinearSections
open CanonicalGeometry NativePulledProjectiveLineFrames NativePulledProjectiveModelSections
open NativePulledProjectiveSectionNorms ProjectiveChartFunctionFieldGeneration
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (t : Fin (m + 1)) (d : ℕ) [IsClosedImmersion f]

/-- The module of global sections of the pulled line, with its action of the base field `k`. -/
abbrev globalSections : ModuleCat k :=
  SchemeScalarModulePresheaf.openSections (f ≫ projectiveSpaceStructure k m) (line f t d) ⊤

variable (i : Fin (m + 1)) [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

/-- The generic coefficient of a global section, as a `k`-linear map to the function field. -/
def coefficientLinearMap :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    globalSections f t d →ₗ[k] X.functionField := by
  let p := f ≫ projectiveSpaceStructure k m
  let := p.stalkAlgebra (genericPoint X)
  let := p.sectionsAlgebra ⊤
  refine {
    toFun := coefficient f i t d
    map_add' := ?_
    map_smul' := ?_ }
  · intro s v
    rw [coefficient_eq_sectionRatio,coefficient_eq_sectionRatio,coefficient_eq_sectionRatio]
    exact map_add _ _ _
  · intro a s
    change coefficient f i t d ((algebraMap k Γ(X,⊤) a) • s) =
      (algebraMap k X.functionField a) * coefficient f i t d s
    rw [coefficient_eq_sectionRatio,coefficient_eq_sectionRatio,
      (sectionRatio (line f t d) (line_isInvertible f t d)
        (coordinatePowerSection f t d i) (coordinatePowerSection_ne_zero f t d i) ⊤).map_smulₛₗ]
    exact congrArg (fun r => r * sectionRatio (line f t d) (line_isInvertible f t d)
      (coordinatePowerSection f t d i) (coordinatePowerSection_ne_zero f t d i) ⊤ s)
      ((p.sectionsFunctionFieldAlgHom ⊤).commutes a)

/-- The `k`-linear coefficient map is the generic coefficient. -/
theorem coefficientLinearMap_apply (s : globalSections f t d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    coefficientLinearMap f t d i s = coefficient f i t d s := rfl

/-- The module of global sections is `k`-linearly equivalent to the section module of the
function-field model. -/
def sectionLinearEquiv :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    globalSections f t d ≃ₗ[k] (fullFieldModel f i).sections (fun _ => (d : ℤ)) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let φ := (coefficientLinearMap f t d i).codRestrict
    ((fullFieldModel f i).sections (fun _ => (d : ℤ)))
    (fun s => coefficient_mem_sections f i t d s)
  apply LinearEquiv.ofBijective φ
  constructor
  · intro s v h
    exact coefficient_injective f i t d (congrArg Subtype.val h)
  · intro g
    obtain ⟨s,hs⟩ := coefficient_surjective f i t d g
    exact ⟨s,Subtype.ext hs⟩

/-- The linear equivalence sends a global section to its generic coefficient. -/
theorem sectionLinearEquiv_apply (s : globalSections f t d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (sectionLinearEquiv f t d i s : X.functionField) = coefficient f i t d s := rfl

/-- The underlying equivalence of `sectionLinearEquiv` is `sectionEquiv`. -/
theorem sectionLinearEquiv_toEquiv :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (sectionLinearEquiv f t d i).toEquiv = sectionEquiv f i t d := by
  apply Equiv.ext
  intro s
  rfl

end EnvelopeProperty.NativePulledProjectiveLinearSections
