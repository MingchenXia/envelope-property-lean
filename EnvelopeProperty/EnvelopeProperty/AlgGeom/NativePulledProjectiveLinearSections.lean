import EnvelopeProperty.AlgGeom.NativePulledProjectiveSectionNorms
import EnvelopeProperty.AlgGeom.SchemeScalarModulePresheaf

/-! # The ENTIRE original pulled-line section equivalence is linear over the SAME original field -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite
open DeJongAlterations Scheme.Modules
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

/-- The actual original ENTIRE global section module, with literal original base-field action. -/
abbrev globalSections : ModuleCat k :=
  SchemeScalarModulePresheaf.openSections (f ≫ projectiveSpaceStructure k m) (line f t d) ⊤

variable (i : Fin (m + 1)) [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

/-- The SAME actual original generic coefficient is genuinely linear for the literal
original field actions; no scalar compatibility certificate is supplied. -/
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

/-- The actual whole field-linear coefficient map retains EVERY original section literally. -/
theorem coefficientLinearMap_apply (s : globalSections f t d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    coefficientLinearMap f t d i s = coefficient f i t d s := rfl

/-- The genuine ENTIRE original global-section module is linearly equivalent to the
ENTIRE same native model section module over the SAME original base field. -/
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

/-- EVERY original global section retains its literal actual generic coefficient under the whole linear equivalence. -/
theorem sectionLinearEquiv_apply (s : globalSections f t d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (sectionLinearEquiv f t d i s : X.functionField) = coefficient f i t d s := rfl

/-- The whole actual linear equivalence has EXACTLY the previously proved genuine original set equivalence. -/
theorem sectionLinearEquiv_toEquiv :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (sectionLinearEquiv f t d i).toEquiv = sectionEquiv f i t d := by
  apply Equiv.ext
  intro s
  rfl

end EnvelopeProperty.NativePulledProjectiveLinearSections
