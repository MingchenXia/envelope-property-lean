import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineBasis

/-! # The original relative Frobenius and twist projection give inverse maps on opens

The reverse ENTIRE scheme composite is the actual absolute Frobenius of the
twist. Its original preimage identity then applies to every actual twist open.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistedOpenInverse
open AlgebraicGeometry CategoryTheory Limits
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fk" => SchemeRelativeFrobenius.baseMap (k := k) p
local notation "π₁" => (pullback.fst f Fk : Y ⟶ X)
local notation "π₂" => (pullback.snd f Fk : Y ⟶ Spec (CommRingCat.of k))
local notation "Fr" => SchemeRelativeFrobenius.map p f

/-- The reverse WHOLE original composite is the genuine absolute Frobenius
of the SAME twist with its ORIGINAL coefficient structure. -/
theorem projection_relativeFrobenius : (π₁) ≫ (Fr) = SchemeFrobenius.map (π₂) p := by
  apply pullback.hom_ext
  · calc
      ((π₁) ≫ (Fr)) ≫ (π₁) = (π₁) ≫ SchemeFrobenius.map f p :=
        (Category.assoc (π₁) (Fr) (π₁)).trans
          (congrArg (fun z => (π₁) ≫ z) (SchemeRelativeFrobenius.map_fst p f))
      _ = SchemeFrobenius.map (π₂) p ≫ (π₁) :=
        (SchemeFrobenius.naturality (π₂) p f (π₁)).symm
  · calc
      ((π₁) ≫ (Fr)) ≫ (π₂) = (π₁) ≫ f :=
        (Category.assoc (π₁) (Fr) (π₂)).trans
          (congrArg (fun z => (π₁) ≫ z) (SchemeRelativeFrobenius.map_snd p f))
      _ = (π₂) ≫ Fk := pullback.condition
      _ = SchemeFrobenius.map (π₂) p ≫ (π₂) :=
        (SchemeRelativeFrobenius.base_square p (π₂)).symm

/-- EVERY original twist open is EXACTLY the original twist of its actual
relative inverse image, including empty opens and schemes. -/
theorem twistedOpen_relative_preimage (W : (Y).Opens) :
    RelativeTwistedAffineBasis.twistedOpen f p ((Fr) ⁻¹ᵁ W) = W := by
  have h := congrArg (fun z : Y ⟶ Y => z ⁻¹ᵁ W) (projection_relativeFrobenius f p)
  exact h.trans (SchemeFrobenius.preimage_eq (π₂) p W)

end EnvelopeProperty.Cartier.RelativeTwistedOpenInverse
