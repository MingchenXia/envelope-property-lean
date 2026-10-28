import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationMap

/-! # Actual original pullback sections commute with actual open restriction

These identities are derived from the same original pullback-adjunction unit.
They are the restriction producer for whole-section Laurent descent, without
any supplied local comparison or decomposition of an arbitrary section.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

/-- The SAME actual pullback-adjunction unit on ANY original open,
with its SAME original coefficient ring map. -/
def pullbackOpenRestrictMap {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ModuleCat.of Γ(X, U) Γ(M, U) ⟶
      (ModuleCat.restrictScalars (g.app U).hom).obj
        (ModuleCat.of Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (g.app U).hom).obj
    (ModuleCat.of Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)))
    { toFun := (((pullbackPushforwardAdjunction g).unit.app M).val.app (op U)).hom
      map_add' := (((pullbackPushforwardAdjunction g).unit.app M).val.app (op U)).hom.map_add
      map_smul' := (((pullbackPushforwardAdjunction g).unit.app M).val.app (op U)).hom.map_smul }

/-- The actual original open pullback maps retain literal restriction on
BOTH original sheaves, by naturality of the original geometric unit. -/
theorem pullbackOpenRestrictMap_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (hUV : U ≤ V) (s : Γ(M, V)) :
    pullbackOpenRestrictMap g M U (M.presheaf.map (homOfLE hUV).op s) =
      ((pullback g).obj M).presheaf.map
        (homOfLE (show g ⁻¹ᵁ U ≤ g ⁻¹ᵁ V from fun _ hx => hUV hx)).op
          (pullbackOpenRestrictMap g M V s) := by
  exact PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction g).unit.app M).val (homOfLE hUV).op s

/-- Restricting the SAME original whole pullback section gives the actual
open pullback of the SAME restricted original whole section. -/
theorem affinePullbackUnitTop_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (s : Γ(M, ⊤)) :
    ((pullback g).obj M).presheaf.map
        (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op (affinePullbackUnitTop g M s) =
      pullbackOpenRestrictMap g M U
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  rw [← pullbackTopRestrictMap_apply]
  exact (pullbackOpenRestrictMap_restrict g M (le_top : U ≤ ⊤) s).symm

/-- Open restriction of the ACTUAL original base-map pure tensor retains
its original coefficient restricted through the SAME original second map. -/
theorem originalBaseChangeMap_tmul_restrict {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X)
    (hg : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (M : X.Modules) (U : X.Opens) (b : S) (s : originalBaseSections f M) :
    ((pullback g).obj M).presheaf.map
        (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op
          (originalBaseChangeMap f q g hg M (b ⊗ₜ[R, algebraMap R S] s)) =
      ((Y.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op).hom
        (ProperBirationalSections.coefficientMap q b)) •
          pullbackOpenRestrictMap g M U
            (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  rw [originalBaseChangeMap_tmul]
  change ((pullback g).obj M).presheaf.map
      (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op
        ((ProperBirationalSections.coefficientMap q b) • affinePullbackUnitTop g M s) = _
  erw [((pullback g).obj M).val.map_smul, affinePullbackUnitTop_restrict]
  rfl

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
