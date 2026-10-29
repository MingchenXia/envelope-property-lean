/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.CoefficientUniverseTransport

/-!
# True chart-isomorphism transport of original divisorial valuation rings

The actual source algebra is retained inside its actual function field.
Its DVR is constructed by the genuine fraction-field extension of the
specified original algebra isomorphism. Element and whole-ideal maps
commute literally; no valuation-approximation assumption is supplied.
-/

noncomputable section

namespace EnvelopeProperty.Char0.ChartDVRTransport

open IsDiscreteValuationRing

universe u v w

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
variable {F : Type w} [Field F] [Algebra k F]
variable (C : Subalgebra k F) [IsFractionRing C F] (e : A ≃ₐ[k] C)
variable (V : BirationalDVR k A)

/-- The genuine fraction-field extension of the original chart isomorphism. -/
abbrev fieldEquiv : FractionRing A ≃ₐ[k] F :=
  IsFractionRing.algEquivOfAlgEquiv e

/-- The entire original DVR transported into the actual original function field. -/
def ring : Subalgebra k F := V.ring.map (fieldEquiv C e).toAlgHom

/-- The literal restriction of the actual fraction-field map to the entire DVR. -/
def ringEquiv : V.ring ≃ₐ[k] ring C e V :=
  Subalgebra.equivMapOfInjective V.ring (fieldEquiv C e).toAlgHom (fieldEquiv C e).injective

instance isDVR : IsDiscreteValuationRing (ring C e V) :=
  RingEquivClass.isDiscreteValuationRing (ringEquiv C e V)

instance essFiniteType : Algebra.EssFiniteType k (ring C e V) :=
  (Algebra.EssFiniteType.iff_of_algEquiv (ringEquiv C e V)).mp inferInstance

omit [IsDomain A] in
/-- The actual fraction-field extension retains every original source element. -/
theorem fieldEquiv_algebraMap (a : A) :
    fieldEquiv C e (algebraMap A (FractionRing A) a) = (e a : F) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap e a

instance isFractionRing : IsFractionRing (ring C e V) F := by
  let := V.isFractionRing
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective V.ring ((fieldEquiv C e).symm z)
  refine ⟨ringEquiv C e V a, ringEquiv C e V b, ?_⟩
  change z = fieldEquiv C e (a : FractionRing A) / fieldEquiv C e (b : FractionRing A)
  have h := congrArg (fieldEquiv C e) hab
  simpa only [map_div₀, AlgEquiv.apply_symm_apply, Subalgebra.algebraMap_apply] using h.symm

/-- The entire original source lies in the actual transported DVR. -/
theorem source_le : C ≤ ring C e V := by
  intro c hc
  obtain ⟨a, ha⟩ := e.surjective (⟨c, hc⟩ : C)
  refine ⟨algebraMap A (FractionRing A) a, V.algebraMap_mem a, ?_⟩
  simpa using (fieldEquiv_algebraMap C e a).trans (congrArg Subtype.val ha)

/-- The actual source inclusion and actual DVR isomorphism agree on every
original chart element, with no supplied commutative-square certificate. -/
theorem source_inclusion (a : A) :
    Subalgebra.inclusion (source_le C e V) (e a) = ringEquiv C e V (V.toRing a) := by
  apply Subtype.ext
  change (e a : F) = fieldEquiv C e (V.toRing a : FractionRing A)
  rw [BirationalDVR.coe_toRing, fieldEquiv_algebraMap]

/-- The actual normalized order of every original chart element is retained,
including zero and its infinite order. -/
theorem order_source (a : A) :
    addVal (ring C e V) (Subalgebra.inclusion (source_le C e V) (e a)) = V.ord a := by
  rw [source_inclusion]
  exact addVal_ringEquiv (ringEquiv C e V).toRingEquiv (V.toRing a)

/-- The entire mapped original ideal agrees under the actual original maps. -/
theorem ideal_map (I : Ideal A) :
    (I.map e.toRingHom).map (Subalgebra.inclusion (source_le C e V)).toRingHom =
      (I.map V.toRing.toRingHom).map (ringEquiv C e V).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact source_inclusion C e V a

/-- The whole actual ideal order is unchanged by the true chart transport;
the zero ideal and its infinite order are included. -/
theorem ideal_order (I : Ideal A) :
    dvrIdealOrder ((I.map e.toRingHom).map
      (Subalgebra.inclusion (source_le C e V)).toRingHom) =
        dvrIdealOrder (I.map V.toRing.toRingHom) := by
  rw [ideal_map, CoefficientUniverseTransport.dvrIdealOrder_map_ringEquiv]

end EnvelopeProperty.Char0.ChartDVRTransport
