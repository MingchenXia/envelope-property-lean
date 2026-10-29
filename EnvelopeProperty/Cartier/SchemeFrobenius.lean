import EnvelopeProperty.Cartier.SchemeFrobeniusScalarRestriction
import Mathlib.Geometry.RingedSpace.Stalks
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The absolute Frobenius of a scheme over a field of characteristic `p` -/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeFrobenius
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The absolute Frobenius as a morphism of presheafed spaces: the identity on the underlying
space and the `p`-th power map on the structure presheaf. -/
def presheafedSpaceMap : X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 X.toTopCat
  c := SchemeFrobeniusScalarRestriction.presheafMap f p

/-- On stalks, the absolute Frobenius is the `p`-th power map. -/
theorem stalkMap_apply (x : X) (a : X.presheaf.stalk x) :
    (presheafedSpaceMap f p).stalkMap x a = a^p := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have h := PresheafedSpace.stalkMap_germ_apply (presheafedSpaceMap f p) U x hx s
  exact h.trans ((congrArg (X.presheaf.germ U x hx)
    (SchemeFrobeniusScalarRestriction.presheafMap_app f p U s)).trans
      (map_pow (X.presheaf.germ U x hx).hom s p))

/-- The stalk maps of the absolute Frobenius are local: `a^p` is a unit only if `a` is. -/
theorem stalkMap_isLocalHom (x : X) : IsLocalHom ((presheafedSpaceMap f p).stalkMap x).hom := by
  refine ⟨fun a ha => ?_⟩
  exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ((stalkMap_apply f p x a) ▸ ha)

/-- The absolute Frobenius `X ⟶ X`. -/
def map : X ⟶ X :=
  ⟨⟨presheafedSpaceMap f p, stalkMap_isLocalHom f p⟩⟩

/-- The absolute Frobenius is the identity on points. -/
theorem map_apply (x : X) : map f p x = x := rfl

/-- The absolute Frobenius acts on sections over every open by `s ↦ s^p`. -/
theorem map_app (U : X.Opens) (s : Γ(X, U)) :
    (map f p).app U s = s^p :=
  SchemeFrobeniusScalarRestriction.presheafMap_app f p U s

/-- The preimage of an open under the absolute Frobenius is the same open. -/
theorem preimage_eq (U : X.Opens) : map f p ⁻¹ᵁ U = U := rfl

/-- The absolute Frobenius is affine, since it preserves every open. -/
theorem isAffineHom_map : IsAffineHom (map f p) :=
  ⟨fun U hU => by change IsAffineOpen U; exact hU⟩

/-- The Frobenius scalar-restriction functor on modules is the pushforward along the absolute
Frobenius. -/
def pushforwardIso : SchemeFrobeniusScalarRestriction.modulesFunctor f p ≅
    Scheme.Modules.pushforward (map f p) := Iso.refl _

variable {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of k))

/-- The absolute Frobenius commutes with every morphism of schemes `g : X ⟶ Y`; no
compatibility of `g` with the structure morphisms to `Spec k` is needed. -/
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
