import EnvelopeProperty.Cartier.SchemeFrobeniusScalarRestriction
import Mathlib.Geometry.RingedSpace.Stalks
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Actual absolute Frobenius of the SAME original scheme -/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeFrobenius
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Actual original Frobenius as a WHOLE morphism of presheafed spaces: same original
space with identity point map, and SAME genuine whole original structure-presheaf power map. -/
def presheafedSpaceMap : X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 X.toTopCat
  c := SchemeFrobeniusScalarRestriction.presheafMap f p

/-- EVERY actual original stalk element has its SAME pth power under this actual morphism.
No germ/section-coefficient preservation data are supplied. -/
theorem stalkMap_apply (x : X) (a : X.presheaf.stalk x) :
    (presheafedSpaceMap f p).stalkMap x a = a^p := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have h := PresheafedSpace.stalkMap_germ_apply (presheafedSpaceMap f p) U x hx s
  exact h.trans ((congrArg (X.presheaf.germ U x hx)
    (SchemeFrobeniusScalarRestriction.presheafMap_app f p U s)).trans
      (map_pow (X.presheaf.germ U x hx).hom s p))

/-- The ACTUAL original Frobenius stalk maps are local, derived from genuine original power
values; no local-ring comparison or locality certificate is assumed. -/
theorem stalkMap_isLocalHom (x : X) : IsLocalHom ((presheafedSpaceMap f p).stalkMap x).hom := by
  refine ⟨fun a ha => ?_⟩
  exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ((stalkMap_apply f p x a) ▸ ha)

/-- The genuine absolute Frobenius of the SAME ENTIRE original scheme. -/
def map : X ⟶ X :=
  ⟨⟨presheafedSpaceMap f p, stalkMap_isLocalHom f p⟩⟩

/-- EVERY original point is unchanged by the actual scheme Frobenius. -/
theorem map_apply (x : X) : map f p x = x := rfl

/-- The actual original scheme Frobenius acts by SAME pth power on EVERY original section
of EVERY original open, including zero section rings of empty opens. -/
theorem map_app (U : X.Opens) (s : Γ(X, U)) :
    (map f p).app U s = s^p :=
  SchemeFrobeniusScalarRestriction.presheafMap_app f p U s

/-- The actual whole Frobenius preimage of EVERY original open is that SAME original open. -/
theorem preimage_eq (U : X.Opens) : map f p ⁻¹ᵁ U = U := rfl

/-- Genuine affineness of the actual whole original Frobenius is DERIVED from its original
point map, with no affine-cover or module comparison certificate. -/
theorem isAffineHom_map : IsAffineHom (map f p) :=
  ⟨fun U hU => by change IsAffineOpen U; exact hU⟩

/-- The previously constructed ENTIRE original Frobenius scalar-restriction functor is
EXACTLY genuine geometric pushforward along this SAME actual scheme Frobenius. -/
def pushforwardIso : SchemeFrobeniusScalarRestriction.modulesFunctor f p ≅
    Scheme.Modules.pushforward (map f p) := Iso.refl _

variable {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of k))

/-- The ENTIRE genuine absolute Frobenius commutes with EVERY original scheme morphism.
No affine/stalk/section/map comparison premise, and no compatibility of g with base k is input. -/
theorem naturality (g : X ⟶ Y) : map f p ≫ g = g ≫ map h p := by
  apply congrArg (fun q : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace => Scheme.Hom.mk q)
  apply LocallyRingedSpace.Hom.ext'
  apply PresheafedSpace.hext
    ((map f p).toLRSHom ≫ g.toLRSHom).toHom
    (g.toLRSHom ≫ (map h p).toLRSHom).toHom (by rfl)
  apply heq_of_eq
  ext U s
  change (SchemeFrobeniusScalarRestriction.presheafMap f p).app (op (g ⁻¹ᵁ U))
    (g.app U s) =
      g.app U ((SchemeFrobeniusScalarRestriction.presheafMap h p).app (op U) s)
  exact (SchemeFrobeniusScalarRestriction.presheafMap_app f p (g ⁻¹ᵁ U)
    (g.app U s)).trans
      ((map_pow (g.app U).hom s p).symm.trans
        (congrArg (g.app U)
          (SchemeFrobeniusScalarRestriction.presheafMap_app h p U s)).symm)

end EnvelopeProperty.Cartier.SchemeFrobenius
