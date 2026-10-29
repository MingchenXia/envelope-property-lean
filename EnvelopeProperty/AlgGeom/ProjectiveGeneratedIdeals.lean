import EnvelopeProperty.AlgGeom.ProjectiveIntegralGlobalFunctions
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial

/-! # Genuine globally generated ideals on the SAME original integral projective scheme -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveGeneratedIdeals
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]

/-- A genuinely nonzero original global ideal section forces the SAME
original ideal to be the unit ideal, from actual projective geometry alone. -/
theorem eq_top_of_nonzero_globalSection (p : X ⟶ Spec (.of k))
    (hp : IsProjectiveFactorization p) (I : X.IdealSheafData)
    (s : Γ(I.toModules, ⊤)) (hs : s ≠ 0) : I = ⊤ := by
  have hc : (s : I.toSubmodule.obj (op (⊤ : X.Opens))).1 ≠ 0 := by
    intro h
    exact hs (Subtype.ext h)
  have hu := ProjectiveIntegralGlobalFunctions.section_isUnit p hp _ hc
  apply top_le_iff.mp
  intro U
  have hm := s.property U le_top
  have hunit := hu.map (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom
  rw [(I.ideal U).eq_top_of_isUnit_mem hm hunit]
  exact le_top

/-- Every SAME original global section of a proper original ideal is
actually zero; no global-function constancy certificate occurs. -/
theorem globalSection_eq_zero_of_ne_top (p : X ⟶ Spec (.of k))
    (hp : IsProjectiveFactorization p) (I : X.IdealSheafData) (hI : I ≠ ⊤)
    (s : Γ(I.toModules, ⊤)) : s = 0 := by
  by_contra hs
  exact hI (eq_top_of_nonzero_globalSection p hp I s hs)

/-- ANY actual original globally generated ideal on an integral projective
scheme is the zero or unit ideal. No finite family/normality premise occurs. -/
theorem eq_bot_or_top_of_generatingSections (p : X ⟶ Spec (.of k))
    (hp : IsProjectiveFactorization p) (I : X.IdealSheafData)
    (G : I.toModules.GeneratingSections) : I = ⊥ ∨ I = ⊤ := by
  by_cases hI : I = ⊤
  · exact Or.inr hI
  left
  have hgen : ∀ i : G.I,
      SchemeGeneratingSectionsUnit.generatorHom G i ≫ I.toModulesInclusion = 0 := by
    intro i
    let α := SchemeGeneratingSectionsUnit.generatorHom G i ≫ I.toModulesInclusion
    have hs := globalSection_eq_zero_of_ne_top p hp I hI
      (((SchemeGeneratingSectionsUnit.generatorHom G i).val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
    have hα := unitHom_eq_globalScalar α
    have hc : ((α.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) = 0 := by
      exact congrArg (fun z : Γ(I.toModules, ⊤) =>
        (z : I.toSubmodule.obj (op (⊤ : X.Opens))).1) hs
    have hα' : α = ModularCurves.unitEndomorphismOfTopSection 0 :=
      hα.trans (congrArg ModularCurves.unitEndomorphismOfTopSection hc)
    change α = 0
    rw [hα']
    apply SheafOfModules.hom_ext
    ext U
    change (1 : Γ(X, U.unop)) *
      X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op 0 = 0
    simp only [map_zero, mul_zero]
  have hπ : G.π ≫ I.toModulesInclusion = 0 := by
    apply Sigma.hom_ext
    intro i
    change SheafOfModules.ιFree i ≫ (G.π ≫ I.toModulesInclusion) = _
    simpa only [← Category.assoc, SchemeGeneratingSectionsUnit.generatorHom, comp_zero] using hgen i
  have hι : I.toModulesInclusion = 0 := by
    apply G.epi.left_cancellation
    exact hπ.trans comp_zero.symm
  apply le_antisymm ?_ bot_le
  intro U a ha
  let s := (I.toModulesSectionsEquiv U).symm ⟨a, ha⟩
  have h := congrArg (fun α : I.toModules ⟶ unitObj X =>
    (α.val.app (op U.1)).hom s) hι
  change a = 0 at h
  exact h

end EnvelopeProperty.ProjectiveGeneratedIdeals
