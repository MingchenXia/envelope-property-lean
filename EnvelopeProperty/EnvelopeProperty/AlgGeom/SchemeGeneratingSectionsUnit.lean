import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Actual local unit coefficients among original global generators -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeGeneratingSectionsUnit
open AlgebraicGeometry.Scheme.Modules

/-- The actual original generator morphism is its TRUE original free basis
inclusion followed by the SAME original free evaluation epimorphism. -/
def generatorHom {X : Scheme.{u}} {M : X.Modules}
    (G : M.GeneratingSections) (i : G.I) : unitObj X ⟶ M :=
  SheafOfModules.ιFree i ≫ G.π

/-- Original epimorphic images preserve the actual original generator morphisms. -/
theorem generatorHom_ofEpi {X : Scheme.{u}} {M N : X.Modules}
    (G : M.GeneratingSections) (p : M ⟶ N) [Epi p] (i : G.I) :
    generatorHom (G.ofEpi p) i = generatorHom G i ≫ p := by
  simp only [generatorHom, SheafOfModules.GeneratingSections.ofEpi_π, Category.assoc]

/-- Genuine pulled generators use the actual original unit pullback map. -/
theorem generatorHom_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (G : M.GeneratingSections) (i : G.I) :
    generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G) i =
      (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (generatorHom G i) := by
  let : PreservesColimitsOfSize.{u,u} (Scheme.Modules.pullback f) :=
    (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  unfold ClosedProjectiveGlobalGeneration.pullback_generatingSections generatorHom
  rw [SheafOfModules.GeneratingSections.map_π_eq]
  have hb := SheafOfModules.ιFree_mapFreeIso_hom
    (Scheme.Modules.pullback f) G.I (pullbackUnitIso f).symm i
  have hc := congrArg (fun q => q ≫ (Scheme.Modules.pullback f).map G.π) hb
  exact (Category.assoc _ _ _).symm.trans
    (hc.trans ((Category.assoc _ _ _).trans
      (congrArg (fun q => (pullbackUnitIso f).inv ≫ q)
        ((Scheme.Modules.pullback f).map_comp _ _).symm)))

private theorem generatorHom_not_all_zero {A : Type u} [CommRing A] [Nontrivial A]
    (G : (unitObj (Spec (.of A))).GeneratingSections) :
    ¬ ∀ i : G.I, generatorHom G i = 0 := by
  intro hz
  have hp : G.π = 0 := by
    apply Sigma.hom_ext
    intro i
    exact (hz i).trans (comp_zero.symm)
  have hi : (𝟙 (unitObj (Spec (.of A))) : unitObj (Spec (.of A)) ⟶ _) = 0 := by
    apply G.epi.left_cancellation
    exact (Category.comp_id G.π).trans (hp.trans comp_zero.symm)
  have hh := congrArg (fun q => (q.val.app (op ⊤)).hom
    (1 : Γ(Spec (.of A), ⊤))) hi
  change (1 : Γ(Spec (.of A), ⊤)) = 0 at hh
  have hc := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom hh
  exact one_ne_zero (by simpa only [map_one, map_zero] using hc)

/-- EVERY actual generating family of the actual local-spectrum unit module
has a genuine original unit coefficient, with no finite-family premise. -/
theorem exists_isUnit_coefficient {A : Type u} [CommRing A] [IsLocalRing A]
    (G : (unitObj (Spec (.of A))).GeneratingSections) :
    ∃ i : G.I, IsUnit ((Scheme.ΓSpecIso (.of A)).hom.hom
      (((generatorHom G i).val.app (op ⊤)).hom (1 : Γ(Spec (.of A), ⊤)))) := by
  classical
  by_contra h
  push Not at h
  let B := IsLocalRing.ResidueField A
  let p : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let H := (ClosedProjectiveGlobalGeneration.pullback_generatingSections p G).ofEpi
    (pullbackUnitIso p).hom
  apply generatorHom_not_all_zero H
  intro i
  rw [generatorHom_ofEpi, generatorHom_pullback]
  let r : Γ(Spec (.of A), ⊤) :=
    ((generatorHom G i).val.app (op ⊤)).hom (1 : Γ(Spec (.of A), ⊤))
  have hr : IsLocalRing.residue A ((Scheme.ΓSpecIso (.of A)).hom.hom r) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact h i)
  have hp : p.appTop.hom r = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).hom).1
    have hn := congrArg (fun q => q.hom r)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue A)))
    exact hn.trans (hr.trans (map_zero _).symm)
  rw [unitHom_eq_globalScalar (generatorHom G i)]
  change (pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map
      (ModularCurves.unitEndomorphismOfTopSection r) ≫ (pullbackUnitIso p).hom = 0
  rw [ModularCurves.pullback_unitEndomorphismOfTopSection, hp]
  apply SheafOfModules.hom_ext
  ext U
  change (1 : Γ(Spec (.of B), U.unop)) *
    (Spec (.of B)).presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op 0 = 0
  simp only [map_zero, mul_zero]

end EnvelopeProperty.SchemeGeneratingSectionsUnit
