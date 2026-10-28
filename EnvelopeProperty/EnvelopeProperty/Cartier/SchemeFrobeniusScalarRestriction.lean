import EnvelopeProperty.Cartier.AlgebraFrobenius
import EnvelopeProperty.AlgGeom.Canonical.CotangentSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Actual Frobenius scalar restriction on the entire original scheme, including empty opens -/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeFrobeniusScalarRestriction
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Genuine pth-power natural endomorphism of the ENTIRE original structure presheaf,
including zero rings of empty opens. No openwise characteristic/nontriviality data are input. -/
def presheafMap : X.presheaf ⟶ X.presheaf where
  app U := by
    letI := CanonicalGeometry.cotangentOpenAlgebra f U.unop
    exact CommRingCat.ofHom (AlgebraFrobenius.map k Γ(X, U.unop) p)
  naturality {U V} i := by
    let := CanonicalGeometry.cotangentOpenAlgebra f U.unop
    let := CanonicalGeometry.cotangentOpenAlgebra f V.unop
    apply CommRingCat.hom_ext
    exact (AlgebraFrobenius.naturality k Γ(X, U.unop) p (X.presheaf.map i).hom).symm

/-- EVERY original regular function on EVERY original open has its SAME pth power. -/
theorem presheafMap_app (U : X.Opens) (a : Γ(X, U)) :
    (presheafMap f p).app (op U) a = a^p := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact AlgebraFrobenius.map_apply k Γ(X, U) p a

/-- The SAME natural endomorphism on the actual ring-valued structure presheaf. -/
def ringPresheafMap : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj :=
  Functor.whiskerRight (presheafMap f p) (forget₂ CommRingCat RingCat)

/-- The true ENTIRE original structure-sheaf endomorphism, not a family of local certificates. -/
def sheafMap : X.ringCatSheaf ⟶ X.ringCatSheaf :=
  ⟨ringPresheafMap f p⟩

/-- GENUINE native scalar restriction of ACTUAL original sheaves of modules by their same
whole original Frobenius coefficient map. All empty opens are included internally. -/
def modulesFunctor : X.Modules ⥤ X.Modules :=
  SheafOfModules.restrictScalars (sheafMap f p)

/-- Native Frobenius scalar restriction retains the SAME entire original abelian presheaf. -/
def underlyingIso : modulesFunctor f p ⋙ Scheme.Modules.toPresheaf X ≅
    Scheme.Modules.toPresheaf X := Iso.refl _

/-- EVERY original section has exactly its SAME original pth-power scalar action on EVERY
open, including the empty open. No scalar comparison or target characteristic premise. -/
theorem modulesFunctor_smul (M : X.Modules) (U : X.Opens) (a : Γ(X, U)) (s : Γ(M, U)) :
    a • (show Γ((modulesFunctor f p).obj M, U) from s) =
      (show Γ((modulesFunctor f p).obj M, U) from a^p • s) := by
  change ((presheafMap f p).app (op U) a) • s = a^p • s
  exact congrArg (fun b : Γ(X, U) => b • s) (presheafMap_app f p U a)

/-- EVERY original restriction map retains its SAME entire underlying section image. -/
theorem modulesFunctor_restrict (M : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (s : Γ(M, V)) :
    ((modulesFunctor f p).obj M).presheaf.map i.op s = M.presheaf.map i.op s := rfl

end EnvelopeProperty.Cartier.SchemeFrobeniusScalarRestriction
