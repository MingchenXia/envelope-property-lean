import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import Mathlib.AlgebraicGeometry.Stalk

/-! # Original global unit-module generators give the genuine whole coefficient-open cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeGeneratorCoefficientOpens
open SchemeLineSectionEvaluation SchemeLineSectionUnitFrames SchemeGeneratingSectionsUnit
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}}

/-- The actual original coefficient of the SAME original free-evaluation generator. -/
def coefficient (G : (unitObj X).GeneratingSections) (i : G.I) : Γ(X, ⊤) :=
  ((generatorHom G i).val.app (op ⊤)).hom (1 : Γ(X, ⊤))

/-- This is the literal original value at one of that SAME original generator. -/
@[simp] theorem coefficient_eq (G : (unitObj X).GeneratingSections) (i : G.I) :
    coefficient G i = sectionAtOne (generatorHom G i) := rfl

/-- Pullback with the SAME original basis index and actual unit comparison
retains the ENTIRE original generator scalar. -/
theorem generatorHom_pullback_unitScalar (f : Y ⟶ X)
    (G : (unitObj X).GeneratingSections) (i : G.I) :
    generatorHom ((ClosedProjectiveGlobalGeneration.pullback_generatingSections f G).ofEpi
      (pullbackUnitIso f).hom) i =
      ModularCurves.unitEndomorphismOfTopSection (f.appTop.hom (coefficient G i)) := by
  rw [generatorHom_ofEpi, generatorHom_pullback]
  have hscalar : generatorHom G i =
      ModularCurves.unitEndomorphismOfTopSection (coefficient G i) :=
    unitHom_eq_globalScalar (generatorHom G i)
  rw [hscalar]
  exact ModularCurves.pullback_unitEndomorphismOfTopSection f (coefficient G i)

private theorem scalarAtOne {B : Scheme.{u}} (r : Γ(B, ⊤)) :
    ((ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤)).hom
      (1 : Γ(B, ⊤)) = r := by
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id, one_mul]
  change (B.presheaf.map (𝟙 (op (⊤ : B.Opens)))).hom r = r
  exact congrArg (fun q : Γ(B, ⊤) ⟶ Γ(B, ⊤) => q.hom r)
    (B.presheaf.map_id (op (⊤ : B.Opens)))

/-- The actual original coefficient ring equality after genuine pullback. -/
theorem coefficient_pullback (f : Y ⟶ X)
    (G : (unitObj X).GeneratingSections) (i : G.I) :
    coefficient ((ClosedProjectiveGlobalGeneration.pullback_generatingSections f G).ofEpi
      (pullbackUnitIso f).hom) i = f.appTop.hom (coefficient G i) :=
  (congrArg (fun q : unitObj Y ⟶ unitObj Y =>
    (q.val.app (op ⊤)).hom (1 : Γ(Y, ⊤)))
    (generatorHom_pullback_unitScalar f G i)).trans (scalarAtOne _)

private theorem exists_local_coefficient {A : Type u} [CommRing A] [IsLocalRing A]
    (G : (unitObj (Spec (.of A))).GeneratingSections) :
    ∃ i : G.I, IsUnit ((Scheme.ΓSpecIso (.of A)).hom.hom (coefficient G i)) :=
  exists_isUnit_coefficient G

/-- EVERY original point lies on a true original generator coefficient basic open. -/
theorem exists_mem_basicOpen (G : (unitObj X).GeneratingSections) (x : X) :
    ∃ i : G.I, x ∈ X.basicOpen (coefficient G i) := by
  let A := X.presheaf.stalk x
  let : IsLocalRing A := inferInstanceAs (IsLocalRing (X.presheaf.stalk x))
  let f := X.fromSpecStalk x
  let H := (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G).ofEpi
    (pullbackUnitIso f).hom
  obtain ⟨i, hi⟩ := @exists_local_coefficient (X.presheaf.stalk x) inferInstance
    (inferInstance : IsLocalRing (X.presheaf.stalk x)) H
  have hs := coefficient_pullback f G i
  have hi' : IsUnit ((Scheme.ΓSpecIso A).hom.hom (f.appTop.hom (coefficient G i))) :=
    Eq.mp (congrArg IsUnit (congrArg (Scheme.ΓSpecIso A).hom.hom hs)) hi
  have he : f.appTop ≫ (Scheme.ΓSpecIso A).hom = X.presheaf.germ ⊤ x trivial := by
    dsimp only [f, A]
    rw [Scheme.fromSpecStalk_appTop]
    simp only [homOfLE_refl, op_id]
    have hid := (Spec (X.presheaf.stalk x)).presheaf.map_id (op (⊤ : (Spec (X.presheaf.stalk x)).Opens))
    rw [hid]
    simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id]
  have hv := congrArg (fun q => q.hom (coefficient G i)) he
  change (Scheme.ΓSpecIso A).hom.hom (f.appTop.hom (coefficient G i)) =
    (X.presheaf.germ ⊤ x trivial).hom (coefficient G i) at hv
  refine ⟨i, (X.mem_basicOpen (coefficient G i) x trivial).mpr ?_⟩
  exact hv ▸ hi'

/-- The SAME actual original coefficient opens cover the ENTIRE original scheme. -/
theorem iSup_basicOpen_eq_top (G : (unitObj X).GeneratingSections) :
    ⨆ i : G.I, X.basicOpen (coefficient G i) = ⊤ := by
  apply top_le_iff.mp
  intro x _hx
  obtain ⟨i, hi⟩ := exists_mem_basicOpen G x
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- On an original affine scheme the SAME ENTIRE actual coefficient family
generates the unit ideal; no supplied coefficient-spanning premise is needed. -/
theorem span_coefficients_eq_top [IsAffine X] (G : (unitObj X).GeneratingSections) :
    Ideal.span (Set.range (coefficient G)) = ⊤ := by
  apply (isAffineOpen_top X).self_le_iSup_basicOpen_iff.mp
  intro x _hx
  obtain ⟨i, hi⟩ := exists_mem_basicOpen G x
  exact Opens.mem_iSup.mpr ⟨⟨coefficient G i, ⟨i, rfl⟩⟩, hi⟩

/-- The canonical true whole local frame uses the SAME actual original generator itself. -/
def generatorFrame (G : (unitObj X).GeneratingSections) (i : G.I) :
    (Scheme.Modules.pullback (X.basicOpen (coefficient G i)).ι).obj (unitObj X) ≅
      unitObj (X.basicOpen (coefficient G i)).toScheme :=
  basicOpenFrame (Iso.refl (unitObj X)) (generatorHom G i)

/-- The SAME original generator has coefficient EXACTLY one in its genuine local frame. -/
theorem generatorFrame_section (G : (unitObj X).GeneratingSections) (i : G.I) :
    pullbackSectionHom (X.basicOpen (coefficient G i)).ι (generatorHom G i) ≫
      (generatorFrame G i).hom = 𝟙 _ :=
  basicOpenFrame_section (Iso.refl (unitObj X)) (generatorHom G i)

end EnvelopeProperty.SchemeGeneratorCoefficientOpens
