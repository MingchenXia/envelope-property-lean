import EnvelopeProperty.AlgGeom.GeneratedLineFramedAffineCover
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections

/-! # Exact original generator scalars through actual open-frame restriction -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.GeneratedLineLocalCoefficients
open SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation SchemeGeneratedLineCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {L : X.Modules}

/-- The SAME original generating section's actual coefficient in an actual original open frame. -/
def localCoefficient (G : L.GeneratingSections) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme) (i : G.I) :
    Γ(U.toScheme, ⊤) :=
  coefficient (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.ι G) e i

/-- The ENTIRE SAME original pulled generator followed by the actual frame is its genuine scalar. -/
theorem localCoefficient_scalar (G : L.GeneratingSections) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme) (i : G.I) :
    pullbackSectionHom U.ι (generatorHom G i) ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G U e i) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections U.ι G
  have hgen : generatorHom (framedGenerators H e) i =
      pullbackSectionHom U.ι (generatorHom G i) ≫ e.hom := by
    simp only [framedGenerators, generatorHom_ofEpi, H, generatorHom_pullback,
      pullbackSectionHom]
  exact hgen.symm.trans (unitHom_eq_globalScalar (generatorHom (framedGenerators H e) i))

private theorem scalarAtOne {B : Scheme.{u}} (r : Γ(B, ⊤)) :
    ((ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤)).hom
      (1 : Γ(B, ⊤)) = r := by
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id, one_mul]
  change (B.presheaf.map (𝟙 (op (⊤ : B.Opens)))).hom r = r
  exact congrArg (fun q : Γ(B, ⊤) ⟶ Γ(B, ⊤) => q.hom r)
    (B.presheaf.map_id (op (⊤ : B.Opens)))

private theorem unitScalar_injective {B : Scheme.{u}} {r s : Γ(B, ⊤)}
    (h : ModularCurves.unitEndomorphismOfTopSection r = ModularCurves.unitEndomorphismOfTopSection s) :
    r = s :=
  (scalarAtOne r).symm.trans ((congrArg (fun q : unitObj B ⟶ unitObj B =>
    (q.val.app (op ⊤)).hom (1 : Γ(B, ⊤))) h).trans (scalarAtOne s))

private theorem restrict_frameViaFactor {U W : X.Opens} (h : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme) :
    frameViaFactor (X.homOfLE h) U.ι W.ι (X.homOfLE_ι h) e = restrictTrivialization h e := by
  apply Iso.ext
  simp only [frameViaFactor, frameFactorIso, restrictTrivialization,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom]
  rfl

/-- Actual native restriction of the actual original frame retains EVERY
SAME original generator coefficient and its literal original coefficient map. -/
theorem localCoefficient_restrict (G : L.GeneratingSections) {U W : X.Opens} (h : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme) (i : G.I) :
    localCoefficient G W (restrictTrivialization h e) i =
      (X.homOfLE h).appTop.hom (localCoefficient G U e i) := by
  have hs := frameViaFactor_sectionHom_scalar (X.homOfLE h) U.ι W.ι (X.homOfLE_ι h)
    e (generatorHom G i) (localCoefficient G U e i) (localCoefficient_scalar G U e i)
  rw [restrict_frameViaFactor, localCoefficient_scalar] at hs
  exact unitScalar_injective hs

end EnvelopeProperty.GeneratedLineLocalCoefficients
