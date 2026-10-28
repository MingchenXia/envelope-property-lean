import EnvelopeProperty.Cartier.EtaleCartierCycleRepresentatives
import EnvelopeProperty.Cartier.EtaleCohomologyCoordinates

/-! # Canonical all-degree original etale Cartier maps -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCartierCoordinateIndependence
open CategoryTheory
open scoped Classical
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {n m : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP B p]
local notation "W" => KaehlerDifferential R B

/-- EVERY original universal differential has its SAME original whole-complex native
Cartier cycle class, with no coordinate-generator premise. -/
theorem inverseCartier_function_class (a : B) :
    EtaleCartierCycleRepresentatives.inverseCartier v hv p 1
      ((exteriorPower.oneEquiv B W).symm (KaehlerDifferential.D R B a)) =
      EtaleCohomologyProducts.nativeCycleClass v hv p 1
        (show EtaleCohomologyProducts.cycles v hv p 1 from IntrinsicCartierOne.generatorCycle v hv p a) :=
  (EtaleCartierCycleRepresentatives.inverseCartier_D v hv p a).trans
    (EtaleCartierCycleRepresentatives.oneHomologyIso_cycleClass v hv p
      (IntrinsicCartierOne.generatorCycle v hv p a))

/-- The ENTIRE actual degree-one maps commute with the genuine SAME-form native cohomology
comparison for ANY TWO actual etale coordinate tuples, even of different lengths. -/
theorem inverseCartier_one_map :
    (EtaleCohomologyCoordinates.nativeHomologyIso v hv w hw p 1).hom.hom.comp
      (EtaleCartierCycleRepresentatives.inverseCartier v hv p 1) =
        EtaleCartierCycleRepresentatives.inverseCartier w hw p 1 := by
  have h : ((EtaleCohomologyCoordinates.nativeHomologyIso v hv w hw p 1).hom.hom.comp
        (EtaleCartierCycleRepresentatives.inverseCartier v hv p 1)).comp
          (exteriorPower.oneEquiv B W).symm.toLinearMap =
      (EtaleCartierCycleRepresentatives.inverseCartier w hw p 1).comp
        (exteriorPower.oneEquiv B W).symm.toLinearMap := by
    apply (Char0.etaleDifferentialBasis w hw).ext
    intro i
    rw [Char0.etaleDifferentialBasis_apply]
    change (EtaleCohomologyCoordinates.nativeHomologyIso v hv w hw p 1).hom.hom
      (EtaleCartierCycleRepresentatives.inverseCartier v hv p 1
        ((exteriorPower.oneEquiv B W).symm (KaehlerDifferential.D R B (w i)))) =
      EtaleCartierCycleRepresentatives.inverseCartier w hw p 1
        ((exteriorPower.oneEquiv B W).symm (KaehlerDifferential.D R B (w i)))
    have hm := EtaleCohomologyCoordinates.nativeHomologyIso_cycleClass v hv w hw p 1
      (IntrinsicCartierOne.generatorCycle v hv p (w i))
    have hg : EtaleCohomologyCoordinates.cycleIso v hv w hw p 1
        (IntrinsicCartierOne.generatorCycle v hv p (w i)) =
        (show EtaleCohomologyProducts.cycles w hw p 1 from
          IntrinsicCartierOne.generatorCycle w hw p (w i)) := by
      apply Subtype.ext
      rfl
    exact (congrArg (EtaleCohomologyCoordinates.nativeHomologyIso v hv w hw p 1).hom.hom
      (inverseCartier_function_class v hv p (w i))).trans
        ((hm.trans (congrArg (EtaleCohomologyProducts.nativeCycleClass w hw p 1) hg)).trans
          (inverseCartier_function_class w hw p (w i)).symm)
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := (exteriorPower.oneEquiv B W).symm.surjective a
  exact congrArg (fun F => F z) h

/-- The ENTIRE original ALL-degree Cartier maps are independent of actual etale coordinates.
The whole degree-one comparison and true exterior universal determination DERIVE every degree;
no higher naturality, representative matching or zero-degree agreement is supplied. -/
theorem inverseCartier_map (q : ℕ) :
    (EtaleCohomologyCoordinates.nativeHomologyIso v hv w hw p q).hom.hom.comp
      (EtaleCartierCycleRepresentatives.inverseCartier v hv p q) =
        EtaleCartierCycleRepresentatives.inverseCartier w hw p q := by
  let f := EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p
  let g := (EtaleCohomologyCoordinates.cycleIso v hv w hw p 1).toLinearMap.comp f
  have h1 : EtaleClosedExteriorLift.nativeClassMap w hw p g 1 =
      EtaleClosedExteriorLift.nativeClassMap w hw p
        (EtaleCartierCycleRepresentatives.coordinateCycleMap w hw p) 1 := by
    apply LinearMap.ext
    intro a
    have ht := EtaleCohomologyCoordinates.nativeClassMap_map v hv w hw p f 1 a
    have hc := congrArg (fun F => F a) (inverseCartier_one_map v hv w hw p)
    exact ht.symm.trans hc
  have hq := EtaleClosedExteriorLift.nativeClassMap_eq_of_one w hw p g
    (EtaleCartierCycleRepresentatives.coordinateCycleMap w hw p) h1 q
  apply LinearMap.ext
  intro a
  exact (EtaleCohomologyCoordinates.nativeClassMap_map v hv w hw p f q a).trans
    (congrArg (fun F => F a) hq)

end EnvelopeProperty.Cartier.EtaleCartierCoordinateIndependence
