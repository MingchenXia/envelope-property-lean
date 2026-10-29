import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
import EnvelopeProperty.Cartier.SmoothExteriorQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affineness and quasicoherent terms of the original geometric relative complex -/

noncomputable section
namespace EnvelopeProperty.Cartier.GeometricRelativeFrobeniusQuasicoherent
open AlgebraicGeometry CategoryTheory Limits
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "Fk" => SchemeRelativeFrobenius.baseMap (k := k) p
local notation "π₁" => pullback.fst f (Fk)

/-- The original relative Frobenius is affine, derived from its original projection triangle. -/
theorem isAffineHom_map : IsAffineHom (Fr) := by
  have hbase : IsAffineHom (Fk) := inferInstance
  have hπ : IsAffineHom (π₁) :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback _ _ _
      isAffineHom_isStableUnderBaseChange _ _ _ _ _ _ _ _
        (IsPullback.of_hasPullback f (Fk)).flip hbase
  have h : IsAffineHom ((Fr) ≫ (π₁)) := by
    rw [SchemeRelativeFrobenius.map_fst]
    exact SchemeFrobenius.isAffineHom_map f p
  exact (@IsAffineHom.comp_iff _ _ _ (Fr) (π₁) hπ).mp h

/-- Every degree of the original global geometric relative complex is genuinely quasicoherent. -/
theorem complex_term_isQuasicoherent (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    ((SchemeRelativeFrobeniusBasisDifferential.complex f p n).X q).IsQuasicoherent := by
  let : (CanonicalGeometry.exteriorCotangentSheaf f q).IsQuasicoherent :=
    SmoothExteriorQuasicoherent.exterior_isQuasicoherent f n q
  let : IsAffineHom (Fr) := isAffineHom_map f p
  change ((Scheme.Modules.pushforward (Fr)).obj
    (CanonicalGeometry.exteriorCotangentSheaf f q)).IsQuasicoherent
  exact Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (Fr)

end EnvelopeProperty.Cartier.GeometricRelativeFrobeniusQuasicoherent
