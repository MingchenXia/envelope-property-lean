import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationMapTrace

/-! # The actual original purification square before canonical sections

Only the original ring homomorphisms and spectrum maps occur here.  The
purification and every root factor are the same original produced ones.
The canonical-section square is a separate consumer of this geometry.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] mixedPurificationIso

private def schemeSquareSealedValue {α : Type u} (a : α) : α :=
  Classical.choose (show ∃ b : α, b = a from ⟨a, rfl⟩)

private theorem over_unit_of_actual_values
    {S C P : Type u} [CommRing S] [CommRing C] [CommRing P]
    [Algebra S C] [Algebra S P] (e : C ≃ₐ[S] P) (f : C →+* P)
    (h : ∀ w, f w = e.toRingHom.toFun w) :
    f.comp (algebraMap S C) = algebraMap S P := by
  apply RingHom.ext
  intro s
  exact (h _).trans (e.commutes s)

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
local notation "Bₘ" => mixedRing x N I σ u
local notation "Sᵤ" => UnitCover N u
local notation "Cₘ" => extendedMixedRing x N I σ u
local notation "Pₘ" => mixedPureRing (k := k) x N I σ u

/-- The SAME produced ring map preserves EVERY coefficient of the entire
original unit cover.  No scalar-compatibility certificate is an input. -/
theorem mixedPurificationMap_over_unit (hN : ∀ i, 0 < N i) :
    (mixedPurificationMap (k := k) x N I σ u hN).hom.comp
        (algebraMap Sᵤ Cₘ) = algebraMap Sᵤ Pₘ := by
  let e := schemeSquareSealedValue (mixedPurificationIso (k := k) x N I σ u hN)
  exact over_unit_of_actual_values e
    (mixedPurificationMap (k := k) x N I σ u hN).hom (fun _ => rfl)

/-- The whole original ring square, internally from tensor balancing and
the same original purification, with no incoming square or matching input. -/
theorem mixedPurification_ring_square (hN : ∀ i, 0 < N i) :
    (mixedPurificationMap (k := k) x N I σ u hN).hom.comp
        ((Algebra.TensorProduct.includeRight (R := A) (A := Sᵤ) (B := Bₘ)).toRingHom.comp
          (algebraMap A Bₘ)) =
      (algebraMap Sᵤ Pₘ).comp (algebraMap A Sᵤ) := by
  have hTensor :
      (Algebra.TensorProduct.includeRight (R := A) (A := Sᵤ) (B := Bₘ)).toRingHom.comp
          (algebraMap A Bₘ) =
        (algebraMap Sᵤ Cₘ).comp (algebraMap A Sᵤ) :=
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := A) (A := Sᵤ) (B := Bₘ)).symm
  rw [hTensor, ← RingHom.comp_assoc, mixedPurificationMap_over_unit]

/-- Applying Spec retains the SAME whole original tensor-right projection,
purification, and base maps.  All ordinary geometry is proved internally. -/
theorem mixedPurification_scheme_square (hN : ∀ i, 0 < N i) :
    (Spec.map (mixedPurificationMap (k := k) x N I σ u hN) ≫
        mixedUnitProjection x N I σ u) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A Bₘ)) =
      Spec.map (CommRingCat.ofHom (algebraMap Sᵤ Pₘ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A Sᵤ)) := by
  dsimp only [mixedUnitProjection]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of Pₘ => Spec.map f)
  apply CommRingCat.hom_ext
  exact mixedPurification_ring_square x N I σ u hN

/-- The original mixed structural morphism is exactly the original base
map followed by its original field structure. -/
theorem mixedBase_structure_triangle :
    Spec.map (CommRingCat.ofHom (algebraMap A Bₘ)) ≫
        affineStructuralMap k (.of A) = mixedStructure (k := k) x N I σ u := by
  exact affineAlgebraMap_structuralSquare k (.of A) (.of Bₘ)
    (IsScalarTower.toAlgHom k A Bₘ)

/-- The original pure target over the unit cover retains its original
field structure.  This only instantiates ordinary algebra-map naturality. -/
theorem mixedPure_structure_triangle :
    Spec.map (CommRingCat.ofHom (algebraMap Sᵤ Pₘ)) ≫
        affineStructuralMap k (.of Sᵤ) = affineStructuralMap k (.of Pₘ) := by
  exact affineAlgebraMap_structuralSquare k (.of Sᵤ) (.of Pₘ)
    (IsScalarTower.toAlgHom k Sᵤ Pₘ)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
