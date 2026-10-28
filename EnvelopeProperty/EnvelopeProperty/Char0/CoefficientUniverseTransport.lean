import EnvelopeProperty.Char0.ValuativeMultiplierIdeal
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.EssentialFiniteness

/-! # Actual coefficient-field and ambient-field transport across universes -/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.CoefficientUniverseTransport

open IsLocalRing IsDiscreteValuationRing

universe u v

variable {k K : Type u} {k' K' : Type v}
    [Field k] [Field K] [Algebra k K] [Field k'] [Field K'] [Algebra k' K']
    (ek : k ≃+* k') (eK : K ≃+* K')
    (he : ∀ a : k, eK (algebraMap k K a) = algebraMap k' K' (ek a))

include he in
/-- The inverse actual scalar square, derived from the specified whole square. -/
theorem inverseCoefficientSquare (a : k') :
    eK.symm (algebraMap k' K' a) = algebraMap k K (ek.symm a) := by
  apply eK.injective
  rw [eK.apply_symm_apply, he, ek.apply_symm_apply]

/-- The entire original subalgebra transported through the actual field maps. -/
def mapSubalgebra (C : Subalgebra k K) : Subalgebra k' K' where
  carrier := {x | eK.symm x ∈ C}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy := by
    change eK.symm (_ + _) ∈ C
    rw [map_add]
    exact C.add_mem hx hy
  mul_mem' hx hy := by
    change eK.symm (_ * _) ∈ C
    rw [map_mul]
    exact C.mul_mem hx hy
  algebraMap_mem' a := by
    change eK.symm (algebraMap k' K' a) ∈ C
    rw [inverseCoefficientSquare ek eK he]
    exact C.algebraMap_mem _

/-- The literal original ambient map restricted to the entire subalgebra. -/
def subalgebraEquiv (C : Subalgebra k K) : C ≃+* mapSubalgebra ek eK he C where
  toFun a := ⟨eK a, by
    change eK.symm (eK a) ∈ C
    simpa only [eK.symm_apply_apply] using a.property⟩
  invFun b := ⟨eK.symm b, b.property⟩
  left_inv a := Subtype.ext (eK.symm_apply_apply a)
  right_inv b := Subtype.ext (eK.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul eK (a : K) (b : K))
  map_add' a b := Subtype.ext (map_add eK (a : K) (b : K))

/-- Inclusion of the WHOLE actual subalgebras is preserved and reflected. -/
theorem mapSubalgebra_le_iff (C D : Subalgebra k K) :
    mapSubalgebra ek eK he C ≤ mapSubalgebra ek eK he D ↔ C ≤ D := by
  constructor
  · intro h a ha
    have hx : eK a ∈ mapSubalgebra ek eK he C := by
      change eK.symm (eK a) ∈ C
      simpa using ha
    have hd := h hx
    change eK.symm (eK a) ∈ D at hd
    simpa using hd
  · intro h a ha
    exact h ha

/-- The actual scalar action is retained by the restricted entire ring equivalence. -/
theorem subalgebraEquiv_coefficients (C : Subalgebra k K) (a : k) :
    subalgebraEquiv ek eK he C (algebraMap k C a) =
      algebraMap k' (mapSubalgebra ek eK he C) (ek a) := by
  apply Subtype.ext
  exact he a

/-- Every original inclusion coefficient commutes with the actual entire maps. -/
theorem subalgebraEquiv_inclusion (C D : Subalgebra k K) (hCD : C ≤ D) (a : C) :
    subalgebraEquiv ek eK he D (Subalgebra.inclusion hCD a) =
      Subalgebra.inclusion ((mapSubalgebra_le_iff ek eK he C D).mpr hCD)
        (subalgebraEquiv ek eK he C a) := rfl

/-- The actual target subalgebra is a DVR whenever the original one is. -/
theorem mapSubalgebra_isDVR (V : Subalgebra k K) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (mapSubalgebra ek eK he V) :=
  RingEquivClass.isDiscreteValuationRing (subalgebraEquiv ek eK he V)

/-- The actual specified ambient field remains the fraction field of the WHOLE source. -/
theorem mapSubalgebra_isFractionRing (C : Subalgebra k K) [IsFractionRing C K] :
    IsFractionRing (mapSubalgebra ek eK he C) K' := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective C (eK.symm z)
  refine ⟨subalgebraEquiv ek eK he C a, subalgebraEquiv ek eK he C b, ?_⟩
  change z = eK (a : K) / eK (b : K)
  have h := congrArg eK hab
  simpa only [map_div₀, eK.apply_symm_apply, Subalgebra.algebraMap_apply] using h.symm

/-- Every actual essential finite type source remains so over the actual new base. -/
theorem mapSubalgebra_essFiniteType (C : Subalgebra k K) [Algebra.EssFiniteType k C] :
    Algebra.EssFiniteType k' (mapSubalgebra ek eK he C) := by
  let : Algebra k k' := ek.toRingHom.toAlgebra
  let : Algebra k (mapSubalgebra ek eK he C) :=
    ((algebraMap k' (mapSubalgebra ek eK he C)).comp ek.toRingHom).toAlgebra
  let : IsScalarTower k k' (mapSubalgebra ek eK he C) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let E : C ≃ₐ[k] mapSubalgebra ek eK he C :=
    { subalgebraEquiv ek eK he C with
      commutes' := subalgebraEquiv_coefficients ek eK he C }
  let : Algebra.EssFiniteType k (mapSubalgebra ek eK he C) :=
    (Algebra.EssFiniteType.iff_of_algEquiv E).mp inferInstance
  exact Algebra.EssFiniteType.of_comp k k' _

/-- Whole residue-coordinate transcendence bases are transported through actual
base and ambient field isomorphisms, without a target basis hypothesis. -/
theorem isTranscendenceBasis_ringEquiv
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] (ek : R ≃+* S) (eK : A ≃+* B)
    (he : ∀ a : R, eK (algebraMap R A a) = algebraMap S B (ek a))
    {ι : Type*} {x : ι → A} (hx : IsTranscendenceBasis R x) :
    IsTranscendenceBasis S (eK ∘ x) := by
  have hsq : (algebraMap S B).comp ek.toRingHom = eK.toRingHom.comp (algebraMap R A) :=
    RingHom.ext fun a => (he a).symm
  refine ⟨hx.1.ringHom_of_comp_eq ek eK ek.surjective eK.injective hsq, ?_⟩
  intro s hs hsub
  let t : Set A := eK ⁻¹' s
  have ht : AlgebraicIndepOn R id t := by
    have hg : AlgebraicIndependent S (eK ∘ fun a : t => (a : A)) :=
      hs.comp (fun a : t => (⟨eK a, a.property⟩ : s))
        (fun a b hab => Subtype.ext (eK.injective (congrArg Subtype.val hab)))
    exact hg.of_ringHom_of_comp_eq ek eK ek.injective hsq
  have hxs : Set.range x ⊆ t := by
    rintro _ ⟨i, rfl⟩
    exact hsub ⟨i, rfl⟩
  have ht_eq := hx.2 t ht hxs
  apply Set.Subset.antisymm hsub
  intro b hb
  have ha : eK.symm b ∈ t := by
    change eK (eK.symm b) ∈ s
    simpa using hb
  rw [← ht_eq] at ha
  obtain ⟨i, hi⟩ := ha
  refine ⟨i, ?_⟩
  change eK (x i) = b
  rw [hi, eK.apply_symm_apply]

/-- The ENTIRE original and new subalgebra lattices are actually order isomorphic. -/
def subalgebraOrderIso : Subalgebra k K ≃o Subalgebra k' K' where
  toFun := mapSubalgebra ek eK he
  invFun := mapSubalgebra ek.symm eK.symm (inverseCoefficientSquare ek eK he)
  left_inv C := by
    apply Subalgebra.ext
    intro x
    change eK.symm (eK x) ∈ C ↔ x ∈ C
    rw [eK.symm_apply_apply]
  right_inv C := by
    apply Subalgebra.ext
    intro x
    change eK (eK.symm x) ∈ C ↔ x ∈ C
    rw [eK.apply_symm_apply]
  map_rel_iff' := mapSubalgebra_le_iff ek eK he _ _

/-- Canonical actual residue-field equivalence, with all rings and fields retained. -/
def residueEquiv (V : Subalgebra k K) [IsDiscreteValuationRing V] :
    let := mapSubalgebra_isDVR ek eK he V
    ResidueField V ≃+* ResidueField (mapSubalgebra ek eK he V) := by
  let := mapSubalgebra_isDVR ek eK he V
  exact IsLocalRing.ResidueField.mapEquiv (subalgebraEquiv ek eK he V)

/-- EVERY original residue coefficient has its literal actual residue readback. -/
theorem residueEquiv_residue (V : Subalgebra k K) [IsDiscreteValuationRing V] (a : V) :
    let := mapSubalgebra_isDVR ek eK he V
    residueEquiv ek eK he V (residue V a) =
      residue (mapSubalgebra ek eK he V) (subalgebraEquiv ek eK he V a) := rfl

/-- The actual residue-field equivalence retains the original base coefficient square. -/
theorem residueEquiv_coefficients (V : Subalgebra k K) [IsDiscreteValuationRing V] (a : k) :
    let := mapSubalgebra_isDVR ek eK he V
    residueEquiv ek eK he V (algebraMap k (ResidueField V) a) =
      algebraMap k' (ResidueField (mapSubalgebra ek eK he V)) (ek a) := by
  let := mapSubalgebra_isDVR ek eK he V
  change residueEquiv ek eK he V (residue V (algebraMap k V a)) =
    residue (mapSubalgebra ek eK he V) (algebraMap k' (mapSubalgebra ek eK he V) (ek a))
  rw [residueEquiv_residue, subalgebraEquiv_coefficients]

/-- The actual original residue-coordinate basis transports internally. -/
theorem residue_transcendenceBasis (V : Subalgebra k K) [IsDiscreteValuationRing V]
    {ι : Type*} (v : ι → V) (hv : IsTranscendenceBasis k (residue V ∘ v)) :
    let := mapSubalgebra_isDVR ek eK he V
    IsTranscendenceBasis k' (residue (mapSubalgebra ek eK he V) ∘
      fun i => subalgebraEquiv ek eK he V (v i)) := by
  let := mapSubalgebra_isDVR ek eK he V
  have h := isTranscendenceBasis_ringEquiv ek (residueEquiv ek eK he V)
    (residueEquiv_coefficients ek eK he V) hv
  change IsTranscendenceBasis k' (fun i => residueEquiv ek eK he V (residue V (v i))) at h
  simpa only [Function.comp_def, residueEquiv_residue] using h

/-- Whole ideal orders are retained by actual mixed-universe DVR ring isomorphisms. -/
theorem dvrIdealOrder_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    (E : R ≃+* S) (I : Ideal R) : dvrIdealOrder (I.map E.toRingHom) = dvrIdealOrder I := by
  unfold dvrIdealOrder
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    have h : (⨅ y ∈ I.map E.toRingHom, addVal S y) ≤ addVal S (E x) :=
      iInf₂_le (E x) (Ideal.mem_map_of_mem E.toRingHom hx)
    simpa only [addVal_ringEquiv] using h
  · refine le_iInf₂ fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv E y).mp hy
    rw [addVal_ringEquiv]
    exact iInf₂_le x hx

/-- Every actual original divisorial DVR has the actual transported divisorial conditions. -/
theorem mem_divisorialDVRs_map (C V : Subalgebra k K) (hV : V ∈ divisorialDVRs C) :
    mapSubalgebra ek eK he V ∈ divisorialDVRs (mapSubalgebra ek eK he C) := by
  rcases hV with ⟨hCV, hDVR, hFrac, hFT⟩
  let : IsDiscreteValuationRing V := hDVR
  let : IsFractionRing V K := hFrac
  let : Algebra.EssFiniteType k V := hFT
  exact ⟨(mapSubalgebra_le_iff ek eK he C V).mpr hCV,
    mapSubalgebra_isDVR ek eK he V, mapSubalgebra_isFractionRing ek eK he V,
    mapSubalgebra_essFiniteType ek eK he V⟩

/-- Actual bijection of the ENTIRE all-original-divisorial-DVR indexing types. -/
def divisorialEquiv (C : Subalgebra k K) :
    divisorialDVRs C ≃ divisorialDVRs (mapSubalgebra ek eK he C) where
  toFun D := ⟨mapSubalgebra ek eK he D.val, mem_divisorialDVRs_map ek eK he C D.val D.property⟩
  invFun D := ⟨mapSubalgebra ek.symm eK.symm (inverseCoefficientSquare ek eK he) D.val, by
    have h := mem_divisorialDVRs_map ek.symm eK.symm (inverseCoefficientSquare ek eK he)
      (mapSubalgebra ek eK he C) D.val D.property
    have hC : mapSubalgebra ek.symm eK.symm (inverseCoefficientSquare ek eK he)
        (mapSubalgebra ek eK he C) = C := (subalgebraOrderIso ek eK he).left_inv C
    rw [hC] at h
    exact h⟩
  left_inv D := by
    apply Subtype.ext
    exact (subalgebraOrderIso ek eK he).left_inv D.val
  right_inv D := by
    apply Subtype.ext
    exact (subalgebraOrderIso ek eK he).right_inv D.val

end EnvelopeProperty.Char0.CoefficientUniverseTransport
