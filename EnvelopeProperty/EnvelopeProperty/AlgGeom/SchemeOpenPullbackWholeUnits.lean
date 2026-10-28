import EnvelopeProperty.AlgGeom.SchemeOpenPullbackSectionEquiv

/-! # Actual native open pullback of EVERY whole original module section -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeOpenPullbackWholeUnits
open SchemePullbackLocalSections SchemeOpenPullbackSectionEquiv
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- The genuine original local-open pullback unit of a whole-section restriction is EXACTLY its actual whole native pullback unit. -/
theorem openPullbackSection_global (s : Γ(M,⊤)) :
    openPullbackSection M U (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
      affinePullbackUnitTop U.ι M s := by
  let Q := (pullback U.ι).obj M
  let v := ((pullbackPushforwardAdjunction U.ι).unit.app M).mapPresheaf
  let i := (homOfLE (le_top : U ≤ ⊤)).op
  let a := (eqToHom U.ι_preimage_self.symm).op
  let b := (eqToHom (show (⊤ : U.toScheme.Opens) = U.ι ⁻¹ᵁ (⊤ : X.Opens) by simp)).op
  have hn := ConcreteCategory.congr_hom (v.naturality i) s
  change ((pullbackPushforwardAdjunction U.ι).unit.app M).app U (M.presheaf.map i s) =
    Q.presheaf.map (((Opens.map U.ι.base).map (homOfLE (le_top : U ≤ ⊤))).op)
      (((pullbackPushforwardAdjunction U.ι).unit.app M).app ⊤ s) at hn
  have hh := congrArg (Q.presheaf.map a) hn
  erw [← Q.presheaf.map_comp_apply] at hh
  have hm : (((Opens.map U.ι.base).map (homOfLE (le_top : U ≤ ⊤))).op ≫ a) = b := Subsingleton.elim _ _
  rw [hm] at hh
  exact hh

/-- The ACTUAL entire additive local-section equivalence sends EVERY original whole restriction to its EXACT native whole open pullback unit. -/
theorem openSectionsEquiv_global (s : Γ(M,⊤)) :
    openSectionsEquiv M U (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
      affinePullbackUnitTop U.ι M s :=
  (openSectionsEquiv_apply M U _).trans (openPullbackSection_global M U s)

end EnvelopeProperty.SchemeOpenPullbackWholeUnits
