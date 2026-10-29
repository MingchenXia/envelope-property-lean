import EnvelopeProperty.Vanishing.NadelFiniteDuality
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Actual coextension composition for the original coefficient homomorphisms

The natural isomorphism is constructed by composing native restriction/coextension
adjunctions and using uniqueness of right adjoints.  Its concrete functional and
counit formulas retain the actual original ring maps.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelFiniteDualityTower

open CategoryTheory ModuleCat

universe u
variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- The existing native composite adjunction transported through actual coefficient restriction. -/
def coextensionCompositeAdjunction (f : R →+* S) (g : S →+* T) :
    restrictScalars (g.comp f) ⊣ coextendScalars f ⋙ coextendScalars g :=
  ((restrictCoextendScalarsAdj g).comp (restrictCoextendScalarsAdj f)).ofNatIsoLeft
    (restrictScalarsComp f g).symm

/-- The canonical whole coextension-composition isomorphism from native right-adjoint uniqueness. -/
def coextensionCompIso (f : R →+* S) (g : S →+* T) :
    coextendScalars f ⋙ coextendScalars g ≅ coextendScalars (g.comp f) :=
  Adjunction.rightAdjointUniq (coextensionCompositeAdjunction f g)
    (restrictCoextendScalarsAdj (g.comp f))

/-- The composite duality counit is evaluation at the original two units. -/
theorem coextensionCompositeAdjunction_counit_apply (f : R →+* S) (g : S →+* T)
    (M : ModuleCat R) (φ : (coextendScalars g).obj ((coextendScalars f).obj M)) :
    (coextensionCompositeAdjunction f g).counit.app M φ = φ (1 : T) (1 : S) := rfl

/-- The canonical composition comparison preserves the actual native duality counit. -/
theorem coextensionCompIso_counit (f : R →+* S) (g : S →+* T) (M : ModuleCat R) :
    (restrictScalars (g.comp f)).map ((coextensionCompIso f g).hom.app M) ≫
        (restrictCoextendScalarsAdj (g.comp f)).counit.app M =
      (coextensionCompositeAdjunction f g).counit.app M :=
  Adjunction.rightAdjointUniq_hom_app_counit (coextensionCompositeAdjunction f g)
    (restrictCoextendScalarsAdj (g.comp f)) M

/-- The actual canonical comparison flattens a nested functional by its original inner unit. -/
theorem coextensionCompIso_hom_apply (f : R →+* S) (g : S →+* T)
    (M : ModuleCat R) (φ : (coextendScalars g).obj ((coextendScalars f).obj M)) (t : T) :
    (coextensionCompIso f g).hom.app M φ t = φ t (1 : S) := by
  have h := congrArg (fun q => q (t • φ)) (coextensionCompIso_counit f g M)
  change (((coextensionCompIso f g).hom.app M).hom (t • φ)) (1 : T) =
    (t • φ) (1 : T) (1 : S) at h
  simpa only [map_smul, CoextendScalars.smul_apply', one_mul] using h

/-- The canonical identity-coextension comparison, from the same native adjunction uniqueness. -/
def coextensionIdIso (R : Type u) [Ring R] :
    coextendScalars (RingHom.id R) ≅ 𝟭 (ModuleCat R) :=
  Adjunction.rightAdjointUniq
    ((restrictCoextendScalarsAdj (RingHom.id R)).ofNatIsoLeft (restrictScalarsId R))
    Adjunction.id

/-- The original identity-coextension comparison is evaluation at one. -/
theorem coextensionIdIso_hom_apply (M : ModuleCat R)
    (φ : (coextendScalars (RingHom.id R)).obj M) :
    (coextensionIdIso R).hom.app M φ = φ (1 : R) := by
  have h := congrArg (fun q => q φ)
    (Adjunction.rightAdjointUniq_hom_app_counit
      ((restrictCoextendScalarsAdj (RingHom.id R)).ofNatIsoLeft (restrictScalarsId R))
      Adjunction.id M)
  exact h

/-- The inverse identity-coextension frame has its literal scalar-multiplication formula. -/
theorem coextensionIdIso_inv_apply (M : ModuleCat R) (x : M) (r : R) :
    (coextensionIdIso R).inv.app M x r = r • x := by
  have hunit : (coextensionIdIso R).inv.app M x (1 : R) = x := by
    rw [← coextensionIdIso_hom_apply]
    exact ConcreteCategory.congr_hom ((coextensionIdIso R).inv_hom_id_app M) x
  have h := (CoextendScalars.equiv (RingHom.id R) M
    ((coextensionIdIso R).inv.app M x)).map_smul r (1 : R)
  let F : R → M := (coextensionIdIso R).inv.app M x
  have hF : F (r * 1) = r • F 1 := h
  change F 1 = x at hunit
  change F r = r • x
  simpa only [mul_one, hunit] using hF

end EnvelopeProperty.Vanishing.NadelFiniteDualityTower
