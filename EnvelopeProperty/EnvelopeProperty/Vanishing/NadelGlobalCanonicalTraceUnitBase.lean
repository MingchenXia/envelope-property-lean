import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceSpectrum
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePurification

/-! # The actual original base canonical module on the same whole unit cover

The coefficient-side comparison in the extended mixed counit is constructed
from the original etale coordinates and the same native differential.  It
does not require a chosen canonical frame or a desired comparison map.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (u : Fin q → Aˣ)

/-- Original etale coordinates derive the exact relative dimension of
the original base structure map by the actual polynomial-space triangle. -/
theorem coordinateStructure_smooth
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    SmoothOfRelativeDimension n (affineStructuralMap k (.of A)) := by
  let a := MvPolynomial.aeval (R := k) x
  let g := Spec.map (CommRingCat.ofHom a.toRingHom)
  let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
  let : Etale g := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact hx
  let : SmoothOfRelativeDimension n f :=
    CoordinateSubspace.smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial k n
  have h : SmoothOfRelativeDimension (0 + n) (g ≫ f) := inferInstance
  have he : g ≫ f = affineStructuralMap k (.of A) :=
    affineAlgebraMap_structuralSquare k (.of (MvPolynomial (Fin n) k)) (.of A) a
  exact Eq.mp (congrArg (fun z => SmoothOfRelativeDimension n z) he)
    (by simpa only [Nat.zero_add] using h)

/-- The SAME entire unit-cover projection retains the original field
structural map, using the actual coefficient homomorphism. -/
theorem unitBaseStructure :
    Spec.map (CommRingCat.ofHom (algebraMap A (UnitCover N u))) ≫
        affineStructuralMap k (.of A) =
      affineStructuralMap k (.of (UnitCover N u)) :=
  affineAlgebraMap_structuralSquare k (.of A) (.of (UnitCover N u))
    (IsScalarTower.toAlgHom k A (UnitCover N u))

/-- The original base canonical sections after the SAME whole unit cover.
Every isomorphism here is constructed internally from the original data. -/
def unitBaseSectionsIso
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (ModuleCat.extendScalars (R := CommRingCat.of A)
      (S := CommRingCat.of (UnitCover N u)) (algebraMap A (UnitCover N u))).obj
        ((moduleSpecΓFunctor (R := .of A)).obj
          (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)) ≅
      (moduleSpecΓFunctor (R := .of (UnitCover N u))).obj
        (exteriorCotangentSheaf (affineStructuralMap k (.of (UnitCover N u))) n) := by
  letI := coordinateStructure_smooth x hx
  let φ : CommRingCat.of A ⟶ CommRingCat.of (UnitCover N u) :=
    CommRingCat.ofHom (algebraMap A (UnitCover N u))
  letI : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr (unitCover_etale N u hN htame)
  exact nativeSectionsIso (affineStructuralMap k (.of A)) φ n ≪≫
    (moduleSpecΓFunctor (R := .of (UnitCover N u))).mapIso
      (eqToIso (congrArg (fun z => exteriorCotangentSheaf z n)
        (unitBaseStructure (k := k) N u)))

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
