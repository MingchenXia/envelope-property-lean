import EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerMorphisms
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherenceCartesian
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherenceRecovery

/-! # Actual inverse identities of the constructed model maps

This assembly retains both genuine model maps. The subsequent producer supplies
their original-field recovery equations from the actual section construction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerIso
open ArithmeticOriginalLinePowerSections ArithmeticOriginalLinePowerBaseChange
open ArithmeticOriginalLinePowerMorphisms ArithmeticOriginalLineHomCoherence
open Alterations.StableModification.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverseIdentityOfRecovered {D : Type*} [Category D]
    {A' B' A B : D} (eA : A' ≅ A) (eB : B' ≅ B) (e : A ≅ B)
    (a : A' ⟶ B') (b : B' ⟶ A')
    (ha : eA.inv ≫ a ≫ eB.hom = e.hom) (hb : eB.inv ≫ b ≫ eA.hom = e.inv) :
    a ≫ b = 𝟙 A' := by
  have h : eA.inv ≫ (a ≫ b) ≫ eA.hom = 𝟙 A := by
    calc
      _ = (eA.inv ≫ a ≫ eB.hom) ≫ (eB.inv ≫ b ≫ eA.hom) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = e.hom ≫ e.inv := by rw [ha, hb]
      _ = 𝟙 A := e.hom_inv_id
  apply (cancel_epi eA.inv).mp
  apply (cancel_mono eA.hom).mp
  simpa only [Category.assoc, Category.comp_id, Iso.inv_hom_id] using h

variable {R k : Type u} [CommRing R] [Field k] [Algebra R k]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Flat p]
  (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) (hB : IsInvertible B)
  (C : FGSubalgebra R (⊤ : Subalgebra R k))

/-- Actual forward and reverse maps whose whole original recoveries are an
original isomorphism and its actual inverse give a genuine model isomorphism.
Both inverse identities are detected through the constructed cartesian fibre.
This is an assembly step; recovery of the two maps is produced separately. -/
def isoOfRecoveredPair
    (e : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ≅
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B)
    (a : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B)
    (b : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A)
    (ha : (transitionIso (S := C.1) (T := k) p A).inv ≫
      (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map a ≫
        (transitionIso (S := C.1) (T := k) p B).hom = e.hom)
    (hb : (transitionIso (S := C.1) (T := k) p B).inv ≫
      (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map b ≫
        (transitionIso (S := C.1) (T := k) p A).hom = e.inv) :
    (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A ≅
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B := by
  let w := transition (S := C.1) (T := k) p
  let q := FlatGlobalSections.structureMap (S := C.1) p
  let : Flat q := by
    change Flat (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R C.1))))
    infer_instance
  have h₁ := inverseIdentityOfRecovered (transitionIso (S := C.1) (T := k) p A)
    (transitionIso (S := C.1) (T := k) p B) e
    ((Scheme.Modules.pullback w).map a) ((Scheme.Modules.pullback w).map b) ha hb
  have h₂ := inverseIdentityOfRecovered (transitionIso (S := C.1) (T := k) p B)
    (transitionIso (S := C.1) (T := k) p A) e.symm
    ((Scheme.Modules.pullback w).map b) ((Scheme.Modules.pullback w).map a) hb ha
  exact isoOfPulledInverse_of_isPullback q (show Function.Injective (algebraMap C.1 k) from Subtype.val_injective)
    w (FlatGlobalSections.structureMap (S := k) p) (isPullback_transition (S := C.1) (T := k) p)
    _ (hA.pullback _) _ (hB.pullback _) a b h₁ h₂

include hA hB

omit C in
/-- An actual original field-fibre isomorphism descends to a constructed
isomorphism on a produced finite coefficient stage. Both entire original
forward and inverse morphisms are recovered; no model map or inverse is given. -/
theorem exists_iso_stage [CompactSpace X] [X.IsSeparated]
    (hi : Function.Injective (algebraMap R k))
    (e : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ≅
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B) :
    ∃ (C : FGSubalgebra R (⊤ : Subalgebra R k))
      (eC : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A ≅
        (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B),
      (transitionIso (S := C.1) (T := k) p A).inv ≫
        (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map eC.hom ≫
          (transitionIso (S := C.1) (T := k) p B).hom = e.hom ∧
      (transitionIso (S := C.1) (T := k) p B).inv ≫
        (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map eC.inv ≫
          (transitionIso (S := C.1) (T := k) p A).hom = e.inv := by
  let : Module.Flat R k := ArithmeticOriginalLineHom.field_extension_flat hi
  obtain ⟨C, a, b, ha, hb⟩ := exists_pair_maps_recovery p A hA B hB e.hom e.inv
  exact ⟨C, isoOfRecoveredPair p A hA B hB C e a b ha hb, ha, hb⟩

omit C in
/-- Properness internally supplies the actual compact/separated hypotheses
for the same original finite-coefficient isomorphism producer. -/
theorem exists_iso_stage_of_proper [IsProper p]
    (hi : Function.Injective (algebraMap R k))
    (e : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ≅
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B) :
    ∃ (C : FGSubalgebra R (⊤ : Subalgebra R k))
      (eC : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A ≅
        (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B),
      (transitionIso (S := C.1) (T := k) p A).inv ≫
        (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map eC.hom ≫
          (transitionIso (S := C.1) (T := k) p B).hom = e.hom ∧
      (transitionIso (S := C.1) (T := k) p B).inv ≫
        (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map eC.inv ≫
          (transitionIso (S := C.1) (T := k) p A).hom = e.inv := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  exact exists_iso_stage p A hA B hB hi e

end EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerIso
