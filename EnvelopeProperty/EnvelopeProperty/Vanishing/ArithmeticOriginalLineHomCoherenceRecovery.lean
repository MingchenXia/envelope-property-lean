import EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherenceTensor

/-! # Genuine finite coefficient descent of original whole fibre morphisms -/
noncomputable section
open AlgebraicGeometry CategoryTheory TensorProduct
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence
open ArithmeticOriginalLinePowerSections ArithmeticOriginalLinePowerMorphisms
open ArithmeticOriginalLinePowerBaseChange ArithmeticOriginalLineCoefficients
open DeJongAlterations.StableModification.Limits

variable {R k : Type u} [CommRing R] [Field k] [Algebra R k] [Module.Flat R k]
  {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of R))
  (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) (hB : IsInvertible B)

/-- The actual finite tensor lift recovers the entire original field-fibre map. -/
theorem mapOfTensor_recovery
    (a : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B)
    (C : FGSubalgebra R (⊤ : Subalgebra R k))
    (zC : C.1 ⊗[R] AffineModuleFlatBaseChange.sections p (homLine A B))
    (hz : coefficientMap C zC = tensorOfMap p A hA B hB a) :
    (transitionIso (S := C.1) (T := k) p A).inv ≫
      (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map
        (mapOfTensor p A hA B zC) ≫ (transitionIso (S := C.1) (T := k) p B).hom = a := by
  have ht := mapOfTensor_transition p A hA B zC (T := k)
  have hc : TensorProduct.map (IsScalarTower.toAlgHom R C.1 k).toLinearMap
      (LinearMap.id : AffineModuleFlatBaseChange.sections p (homLine A B) →ₗ[R]
        AffineModuleFlatBaseChange.sections p (homLine A B)) zC =
      tensorOfMap p A hA B hB a := hz
  exact ht.trans ((congrArg (mapOfTensor p A hA B) hc).trans
    (mapOfTensor_tensorOfMap p A hA B hB a))

include hA hB

/-- Both original whole field-fibre maps descend together as actual module maps
on one produced finite coefficient stage and recover exactly the prescribed maps. -/
theorem exists_pair_maps_recovery
    (a : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B)
    (b : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B ⟶
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj A) :
    ∃ (C : FGSubalgebra R (⊤ : Subalgebra R k))
      (aC : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A ⟶
        (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B)
      (bC : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj B ⟶
        (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj A),
      (transitionIso (S := C.1) (T := k) p A).inv ≫
        (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map aC ≫
          (transitionIso (S := C.1) (T := k) p B).hom = a ∧
      (transitionIso (S := C.1) (T := k) p B).inv ≫
        (Scheme.Modules.pullback (transition (S := C.1) (T := k) p)).map bC ≫
          (transitionIso (S := C.1) (T := k) p A).hom = b := by
  obtain ⟨C, zC, wC, hz, hw⟩ := exists_pair_tensor_lifts p A hA B hB a b
  exact ⟨C, mapOfTensor p A hA B zC, mapOfTensor p B hB A wC,
    mapOfTensor_recovery p A hA B hB a C zC hz,
    mapOfTensor_recovery p B hB A hA b C wC hw⟩

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence
