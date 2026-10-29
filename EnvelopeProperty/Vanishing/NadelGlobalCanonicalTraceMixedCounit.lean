import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNative
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePureSections
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceEquivalence
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitBase
import EnvelopeProperty.Vanishing.NadelCanonicalTensorBaseChange

/-! # The actual extended mixed canonical counit on the same whole cover

Every comparison and the pure counit are instantiated internally from the
original field, etale coordinates, degrees, active set and unit family.
The map below is the actual candidate for faithful descent.  Its overlap
equality is a subsequent proof obligation, not a hypothesis of this map.
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

-- Keep the proved same purification opaque to elaboration; its equality
-- transport history is not part of the scalar-commutation computation.
attribute [local irreducible] mixedPurificationIso

private theorem nativeTensorRightStructure
    (K A S B : Type u) [Field K] [CommRing A] [CommRing S] [CommRing B]
    [Algebra K A] [Algebra K S] [Algebra K B] [Algebra A S] [Algebra A B]
    [IsScalarTower K A S] [IsScalarTower K A B] :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom) ≫
      affineStructuralMap K (.of B) = affineStructuralMap K (.of (S ⊗[A] B)) := by
  let : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower K B (S ⊗[A] B) :=
    NadelCanonicalBaseChange.tensorRight_scalarTower
  exact affineAlgebraMap_structuralSquare K (.of B) (.of (S ⊗[A] B))
    (IsScalarTower.toAlgHom K B (S ⊗[A] B))

-- A proof-backed seal prevents the kernel from evaluating the original
-- dependent coefficient-transport program while projecting algebra fields.
-- The value is propositionally the SAME produced object, by choose_spec.
private def sealedValue {α : Type u} (a : α) : α :=
  Classical.choose (show ∃ b : α, b = a from ⟨a, rfl⟩)

private theorem sealedValue_eq {α : Type u} (a : α) : sealedValue a = a :=
  Classical.choose_spec (show ∃ b : α, b = a from ⟨a, rfl⟩)

private theorem sealedAlgEquiv_apply
    {S C P : Type u} [CommSemiring S] [Semiring C] [Semiring P]
    [Algebra S C] [Algebra S P] (e : C ≃ₐ[S] P) (w : C) :
    (sealedValue e).toRingHom.toFun w = e.toRingHom.toFun w :=
  congrArg (fun d : C ≃ₐ[S] P => d.toRingHom.toFun w) (sealedValue_eq e)

private def nativeAlgHomOfRingHom
    {R C P : Type u} [CommSemiring R] [Semiring C] [Semiring P]
    [Algebra R C] [Algebra R P] (h : C →+* P)
    (hc : ∀ r : R, h (algebraMap R C r) = algebraMap R P r) : C →ₐ[R] P :=
  { toRingHom := h, commutes' := hc }

private theorem nativeTensorLeft_tower
    {K A S T : Type u} [CommSemiring K] [CommSemiring A]
    [CommSemiring S] [Semiring T]
    [Algebra K A] [Algebra K S] [Algebra A S] [Algebra A T]
    [IsScalarTower K A S] :
    IsScalarTower K S (S ⊗[A] T) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
local notation "Bₘ" => mixedRing x N I σ u
local notation "Sᵤ" => UnitCover N u
local notation "Cₘ" => extendedMixedRing x N I σ u
local notation "Pₘ" => mixedPureRing (k := k) x N I σ u
local notation "fC" => mixedUnitProjection x N I σ u ≫ mixedStructure (k := k) x N I σ u

/-- The actual whole source on the full unit cover is smooth of the SAME
original relative dimension, from actual mixed smoothness and etaleness. -/
theorem extendedMixedStructure_smooth
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    SmoothOfRelativeDimension n fC := by
  let := mixedStructure_smooth x N I σ u hx hN htame
  let := mixedUnitProjection_etale x N I σ u hN htame
  have h : SmoothOfRelativeDimension (0 + n) fC := inferInstance
  simpa only [Nat.zero_add] using h

/-- The original tensor right inclusion retains the SAME original field
structural map, using the actual proved scalar tower. -/
theorem extendedMixedStructure_eq :
    fC = affineStructuralMap k (.of Cₘ) := by
  exact nativeTensorRightStructure k A Sᵤ Bₘ

private def sealedPurification (hN : ∀ i, 0 < N i) :=
  sealedValue (mixedPurificationIso (k := k) x N I σ u hN)

-- Cache the internally produced FIELD algebra map, retaining its inferred
-- original algebra structures instead of re-elaborating a large annotation.
private def mixedPurificationFieldHom (hN : ∀ i, 0 < N i) := by
  letI := nativeTensorLeft_tower (K := k) (A := A) (S := Sᵤ) (T := Bₘ)
  exact nativeAlgHomOfRingHom (R := k)
    (sealedPurification (k := k) x N I σ u hN).toRingHom
    (fun z => _root_.AlgHom.map_algebraMap (R := k) (S := Sᵤ)
      (sealedPurification (k := k) x N I σ u hN).toAlgHom z)

/-- The literal ring map of the SAME produced whole purification. -/
def mixedPurificationMap (hN : ∀ i, 0 < N i) :
    CommRingCat.of Cₘ ⟶ CommRingCat.of Pₘ :=
  CommRingCat.ofHom (mixedPurificationFieldHom (k := k) x N I σ u hN).toRingHom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Every value is the SAME value of the original S-purification. -/
theorem mixedPurificationMap_apply (hN : ∀ i, 0 < N i) (w : Cₘ) :
    mixedPurificationMap (k := k) x N I σ u hN w =
      (mixedPurificationIso (k := k) x N I σ u hN).toRingHom.toFun w := by
  have h₀ : mixedPurificationMap (k := k) x N I σ u hN w =
      (sealedValue (mixedPurificationIso (k := k) x N I σ u hN)).toRingHom.toFun w := rfl
  exact h₀.trans (sealedAlgEquiv_apply
    (mixedPurificationIso (k := k) x N I σ u hN) w)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem mixedPurification_affine_structure (hN : ∀ i, 0 < N i) :
    Spec.map (mixedPurificationMap (k := k) x N I σ u hN) ≫
      affineStructuralMap k (.of Cₘ) = affineStructuralMap k (.of Pₘ) := by
  exact affineAlgebraMap_structuralSquare k (.of Cₘ) (.of Pₘ)
    (mixedPurificationFieldHom (k := k) x N I σ u hN)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The SAME actual purification preserves the original field structure. -/
theorem mixedPurification_structure (hN : ∀ i, 0 < N i) :
    Spec.map (mixedPurificationMap (k := k) x N I σ u hN) ≫
      fC = affineStructuralMap k (.of Pₘ) := by
  have h₁ := congrArg (fun f =>
    Spec.map (mixedPurificationMap (k := k) x N I σ u hN) ≫ f)
      (extendedMixedStructure_eq (k := k) x N I σ u)
  have h₂ := mixedPurification_affine_structure (k := k) x N I σ u hN
  exact h₁.trans h₂


-- Only literal ring maps enter the scalar comparison.  The original
-- S-algebra equivalence is used only for its coefficient identity.
private theorem nativeAlgEquiv_coefficients
    {S C P : Type u} [CommSemiring S] [Semiring C] [Semiring P]
    [Algebra S C] [Algebra S P] (e : C ≃ₐ[S] P) :
    algebraMap S P = e.toRingHom.comp (algebraMap S C) := by
  apply RingHom.ext
  intro s
  exact (e.commutes s).symm

private def nativeRingEquivSectionsIso
    {K : Type u} [Field K] {S C P : CommRingCat.{u}}
    [Algebra K P] (α : S →+* C) (β : S →+* P)
    (f : Spec C ⟶ Spec (.of K)) (d : ℕ) [SmoothOfRelativeDimension d f]
    (e : C ≃+* P) (hs : β = e.toRingHom.comp α)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f = affineStructuralMap K P) :
    (ModuleCat.restrictScalars α).obj
      ((moduleSpecΓFunctor (R := C)).obj (exteriorCotangentSheaf f d)) ≅
    (ModuleCat.restrictScalars β).obj
      ((moduleSpecΓFunctor (R := P)).obj
        (exteriorCotangentSheaf (affineStructuralMap K P) d)) := by
  let Q := (moduleSpecΓFunctor (R := P)).obj
    (exteriorCotangentSheaf (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f) d)
  let E := nativeEquivSectionsIso f e d
  exact (ModuleCat.restrictScalars α).mapIso E ≪≫
    (ModuleCat.restrictScalarsComp'App α e.toRingHom β hs Q).symm ≪≫
    (ModuleCat.restrictScalars β).mapIso
      ((moduleSpecΓFunctor (R := P)).mapIso
        (eqToIso (congrArg (fun z => exteriorCotangentSheaf z d) he)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same produced purification carries the actual entire canonical
sections along its native canonical differential, with original S action. -/
def mixedPurificationSectionsIso
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (ModuleCat.restrictScalars (R := CommRingCat.of Sᵤ) (S := CommRingCat.of Cₘ)
      (algebraMap Sᵤ Cₘ)).obj (extendedMixedCanonicalModule (k := k) x N I σ u) ≅
      (ModuleCat.restrictScalars (R := CommRingCat.of Sᵤ) (S := CommRingCat.of Pₘ)
        (algebraMap Sᵤ Pₘ)).obj
          ((moduleSpecΓFunctor (R := .of Pₘ)).obj
            (exteriorCotangentSheaf (affineStructuralMap k (.of Pₘ)) n)) := by
  letI := extendedMixedStructure_smooth x N I σ u hx hN htame
  let E := sealedPurification (k := k) x N I σ u hN
  exact nativeRingEquivSectionsIso
    (S := .of Sᵤ) (C := .of Cₘ) (P := .of Pₘ)
    (algebraMap Sᵤ Cₘ) (algebraMap Sᵤ Pₘ) fC n E.toRingEquiv
    (nativeAlgEquiv_coefficients E)
    (mixedPurification_structure (k := k) x N I σ u hN)

variable [Nontrivial A]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual whole mixed extended counit.  All native canonical maps,
purification and pure counit are produced from the original geometric data. -/
def mixedExtendedCounit
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (ModuleCat.extendScalars (R := CommRingCat.of A) (S := CommRingCat.of Sᵤ)
      (algebraMap A Sᵤ)).obj (mixedCanonicalModuleOverBase (k := k) x N I σ u) ⟶
      (ModuleCat.extendScalars (R := CommRingCat.of A) (S := CommRingCat.of Sᵤ)
        (algebraMap A Sᵤ)).obj
          ((moduleSpecΓFunctor (R := .of A)).obj
            (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)) := by
  letI : Nontrivial Sᵤ := unitCover_nontrivial N u hN
  let aS := unitCoordinateMap (k := k) x N u
  have haS : aS.toRingHom.FormallyEtale :=
    unitCoordinateMap_formallyEtale x N u hx hN htame
  have htameS : ∀ i, IsUnit (N i : Sᵤ) := fun i => by
    simpa only [map_natCast] using (htame i).map (algebraMap A Sᵤ)
  exact (mixedExtendedSectionsIso x N I σ u hx hN htame).hom ≫
    (mixedPurificationSectionsIso x N I σ u hx hN htame).hom ≫
    pureCanonicalSectionsCounit N I σ hN aS haS htameS ≫
    (unitBaseSectionsIso x N u hx hN htame).inv

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
