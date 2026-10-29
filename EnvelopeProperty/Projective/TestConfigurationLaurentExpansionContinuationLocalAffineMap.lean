import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationOpenBaseComparison

/-! # Original local base-change maps through the actual canonical sheaf iso

Native original-base restriction isomorphisms and the genuine open square
identify the original open map with the original restricted-square map.
No section comparison or local bijectivity is supplied.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

/-- Actual module-sheaf isomorphisms induce actual original-base section
presheaf isomorphisms; all functions are the native original ones. -/
def originalBaseOpenModuleIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {M N : X.Modules} (e : M ≅ N) :
    originalBaseOpenPresheaf f M ≅ originalBaseOpenPresheaf f N :=
  Functor.isoWhiskerRight ((baseModulePresheafFunctor f).mapIso e)
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

/-- The original-base whole-section iso from an actual original sheaf iso. -/
def originalBaseWholeModuleIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {M N : X.Modules} (e : M ≅ N) :
    originalBaseSections f M ≅ originalBaseSections f N :=
  (originalBaseOpenTopIso f M).symm ≪≫ (originalBaseOpenModuleIso f e).app (op ⊤) ≪≫
    originalBaseOpenTopIso f N

/-- The induced whole-section iso retains every actual section value. -/
theorem originalBaseWholeModuleIso_hom_apply {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {M N : X.Modules} (e : M ≅ N)
    (s : originalBaseSections f M) :
    (originalBaseWholeModuleIso f e).hom s = e.hom.val.app (op ⊤) s := by
  rfl

/-- The native base-linear restriction iso on the SAME original open,
with the actual original restricted structural morphism. -/
def originalBaseRestrictedSectionsIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : X.Opens) :
    originalBaseSections (U.ι ≫ f) (M.restrict U.ι) ≅
      (originalBaseOpenPresheaf f M).obj (op U) :=
  (originalBaseOpenTopIso (U.ι ≫ f) (M.restrict U.ι)).symm ≪≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapIso
      (baseModulePresheafRestrictAppIso f U.ι M ⊤) ≪≫
    ((originalBaseOpenPresheaf f M).mapIso (eqToIso U.ι_image_top).op).symm

/-- This ACTUAL base-linear iso is exactly the frozen original section iso. -/
theorem originalBaseRestrictedSectionsIso_hom_apply {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : X.Opens)
    (s : originalBaseSections (U.ι ≫ f) (M.restrict U.ι)) :
    (originalBaseRestrictedSectionsIso f M U).hom s = (originalOpenSectionsIso M U).hom s := by
  rfl

/-- The inverse gives the SAME canonical restriction-sheaf presentation. -/
theorem originalBaseRestrictedSectionsIso_inv_apply {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : X.Opens)
    (s : (originalBaseOpenPresheaf f M).obj (op U)) :
    (originalBaseRestrictedSectionsIso f M U).inv s = (originalOpenSectionsIso M U).inv s := by
  rfl

/-- The original local section iso comes from the ACTUAL canonical
restriction/pullback sheaf iso on the SAME inverse-image open. -/
def originalBaseOpenLocalIso {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (originalBaseOpenPresheaf q ((pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) ≅
      originalBaseSections ((g ⁻¹ᵁ U).ι ≫ q) ((pullback (g ∣_ U)).obj (M.restrict U.ι)) :=
  (originalBaseRestrictedSectionsIso q ((pullback g).obj M) (g ⁻¹ᵁ U)).symm ≪≫
    originalBaseWholeModuleIso ((g ⁻¹ᵁ U).ι ≫ q) ((originalOpenPullbackIso g U).app M)

/-- Every original section is transported through the SAME original E. -/
theorem originalBaseOpenLocalIso_hom_apply {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (s : (originalBaseOpenPresheaf q ((pullback g).obj M)).obj (op (g ⁻¹ᵁ U))) :
    (originalBaseOpenLocalIso q g M U).hom s =
      (((originalOpenPullbackIso g U).hom.app M).app ⊤)
        ((originalOpenSectionsIso ((pullback g).obj M) (g ⁻¹ᵁ U)).inv s) := by
  rfl

section OriginalSquare
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X)
  (hg : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

include hg

/-- The restricted original base equality is derived from the actual
open-inclusion square and the original geometric base equality. -/
theorem originalRestrictedBaseCondition (U : X.Opens) :
    (g ∣_ U) ≫ (U.ι ≫ f) =
      ((g ⁻¹ᵁ U).ι ≫ q) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hg, ← Category.assoc]

/-- The frozen original-base pullback map has precisely the original
geometric whole-section unit as its underlying function. -/
theorem originalBasePullbackMap_apply_originalUnit (M : X.Modules)
    (s : originalBaseSections f M) :
    originalBasePullbackMap f q g hg M s =
      (show originalBaseSections q ((pullback g).obj M) from pullbackTopRestrictMap g M s) := by
  rfl

/-- The actual original open scalar-extension map is the actual original
restricted-square map through the ACTUAL canonical sheaf isomorphism.
The equality holds on ALL original local sections and tensors. -/
theorem originalBaseOpenChangeMap_local_square (M : X.Modules) (U : X.Opens) :
    originalBaseOpenChangeMap f q g hg M U ≫ (originalBaseOpenLocalIso q g M U).hom =
      (ModuleCat.extendScalars (algebraMap R S)).map
          (originalBaseRestrictedSectionsIso f M U).inv ≫
        originalBaseChangeMap (U.ι ≫ f) ((g ⁻¹ᵁ U).ι ≫ q) (g ∣_ U)
          (originalRestrictedBaseCondition f q g hg U) (M.restrict U.ι) := by
  apply ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  simp only [originalBaseOpenChangeMap, originalBaseChangeMap, Equiv.apply_symm_apply]
  ext s
  change (originalBaseOpenLocalIso q g M U).hom (pullbackOpenRestrictMap g M U s) =
    originalBasePullbackMap (U.ι ≫ f) ((g ⁻¹ᵁ U).ι ≫ q) (g ∣_ U)
      (originalRestrictedBaseCondition f q g hg U) (M.restrict U.ι)
        ((originalBaseRestrictedSectionsIso f M U).inv s)
  rw [originalBaseOpenLocalIso_hom_apply, originalBasePullbackMap_apply_originalUnit,
    originalBaseRestrictedSectionsIso_inv_apply, pullbackTopRestrictMap_apply]
  exact originalOpenPullbackIso_unit_section g U M s

end OriginalSquare
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
