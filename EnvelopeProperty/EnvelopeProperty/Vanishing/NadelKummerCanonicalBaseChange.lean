import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeCore
import EnvelopeProperty.Vanishing.NadelKummerCoverTowerBasis

/-! # Actual arbitrary base change of the original power-map dual frame

The tensor ring, both original maps, and its complete native dual frame are
constructed from the original power map and the new coefficient homomorphism.
No pairing or base-change comparison certificate is an input.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange

open CategoryTheory ModuleCat TensorProduct
open scoped TensorProduct
open NadelKummerCanonicalTrace NadelKummerCover

universe u

private theorem baseChangedFrame_bijective_of_pairing
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Module.Free A B] [Module.Finite A B]
    (ℓ : B →ₗ[A] A) (hℓ : Function.Bijective (coefficientPairing ℓ)) :
    Function.Bijective (baseChangedFrame (S := S) ℓ) := by
  let e := LinearEquiv.ofBijective (coefficientPairing ℓ) hℓ
  have hbc : Function.Bijective ((coefficientPairing ℓ).baseChange S) :=
    (e.baseChange A S).bijective
  have hpair : Function.Bijective (coefficientPairing (Module.Dual.baseChange S ℓ)) := by
    rw [← coefficientPairing_baseChange]
    exact (dualBaseChangeEquiv (A := A) (B := B) (S := S)).bijective.comp hbc
  have hcomp (x : S ⊗[A] B) :
      nativeFunctionalEquiv (baseChangedFrame (S := S) ℓ x) =
        coefficientPairing (Module.Dual.baseChange S ℓ) x := by
    apply LinearMap.ext
    intro y
    rw [nativeFunctionalEquiv_apply, baseChangedFrame_apply]
    change Module.Dual.baseChange S ℓ (y * x) = Module.Dual.baseChange S ℓ (x * y)
    rw [mul_comm]
  constructor
  · intro x y h
    apply hpair.1
    rw [← hcomp x, ← hcomp y, h]
  · intro φ
    obtain ⟨x, hx⟩ := hpair.2 (nativeFunctionalEquiv φ)
    refine ⟨x, (nativeFunctionalEquiv).injective ?_⟩
    rw [hcomp]
    exact hx

variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)

/-- The actual original power-map coefficient viewed with its original A-module action. -/
def polynomialCoefficient :
    let _ : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
    let _ : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
    Module.Dual (PolynomialRing R n) (PolynomialRing R n) := by
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  exact (coefficientMap R d).comp (algebraRestrictionEquiv).symm.toLinearMap

private theorem polynomialPairing_bijective :
    let _ : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
    let _ : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
    Function.Bijective (coefficientPairing (polynomialCoefficient R d)) := by
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  have h := (nativeFunctionalEquiv (A := PolynomialRing R n) (B := PolynomialRing R n)).bijective.comp
    (powerDualizingMap_bijective R d)
  convert h using 1
  funext x
  apply DFunLike.ext
  intro y
  change coefficientMap R d (x * y) = coefficientMap R d (y * x)
  rw [mul_comm]

/-- The literal commutative tensor algebra using the original nonidentity power coefficient action. -/
def powerBaseChangeRing (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) : CommRingCat := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  exact CommRingCat.of (S ⊗[PolynomialRing R n] PolynomialRing R n)

/-- The actual new coefficient inclusion into the literal original tensor algebra. -/
def powerBaseChangeLeft (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    S →+* powerBaseChangeRing R d S a := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  exact Algebra.TensorProduct.includeLeftRingHom (R := PolynomialRing R n)
    (A := S) (B := PolynomialRing R n)

/-- The actual original target-polynomial inclusion into the same tensor algebra. -/
def powerBaseChangeRight (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    PolynomialRing R n →+* powerBaseChangeRing R d S a := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  exact (Algebra.TensorProduct.includeRight (R := PolynomialRing R n)
    (A := S) (B := PolynomialRing R n)).toRingHom

omit [Nontrivial R] in
/-- The original two coefficient paths agree on the entire original polynomial algebra. -/
theorem powerBaseChange_square (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    (powerBaseChangeLeft R d S a).comp a =
      (powerBaseChangeRight R d S a).comp (powerMap R d) := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  apply RingHom.ext
  intro r
  exact ((Algebra.TensorProduct.includeRight (R := PolynomialRing R n)
    (A := S) (B := PolynomialRing R n)).commutes r).symm

/-- The actual extended composite top-coefficient functional on the original tensor algebra. -/
def powerBaseChangeCoefficient (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    powerBaseChangeRing R d S a → S := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  exact fun x => Module.Dual.baseChange S (polynomialCoefficient R d) x

/-- A literal pure tensor in the same actual power-map tensor algebra. -/
def powerBaseChangeTensor (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (s : S) (b : PolynomialRing R n) : powerBaseChangeRing R d S a := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  exact s ⊗ₜ[PolynomialRing R n] b

/-- The actual extended counit coefficient agrees with the original coefficient on every pure tensor. -/
theorem powerBaseChangeCoefficient_tensor (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (s : S) (b : PolynomialRing R n) :
    powerBaseChangeCoefficient R d S a (powerBaseChangeTensor R d S a s b) =
      s * a (coefficientMap R d b) := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  change Module.Dual.baseChange S (polynomialCoefficient R d)
    (s ⊗ₜ[PolynomialRing R n] b) = _
  rw [Module.Dual.baseChange_apply_tmul, Algebra.smul_def]
  change a (coefficientMap R d b) * s = s * a (coefficientMap R d b)
  rw [mul_comm]

omit [Nontrivial R] in
/-- The actual original target-polynomial map is the literal original unit pure tensor. -/
theorem powerBaseChangeRight_tensor (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (b : PolynomialRing R n) :
    powerBaseChangeRight R d S a b = powerBaseChangeTensor R d S a 1 b := rfl

/-- The actual extended counit preserves the original target-polynomial coefficient after coefficient extension. -/
theorem powerBaseChangeCoefficient_right (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (b : PolynomialRing R n) :
    powerBaseChangeCoefficient R d S a (powerBaseChangeRight R d S a b) =
      a (coefficientMap R d b) := by
  rw [powerBaseChangeRight_tensor, powerBaseChangeCoefficient_tensor, one_mul]

/-- The actual complete tensor-algebra-linear native dual frame, internally produced from the original power frame. -/
def powerBaseChangeIso (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S) :
    ModuleCat.of (powerBaseChangeRing R d S a) (powerBaseChangeRing R d S a) ≅
      (coextendScalars (powerBaseChangeLeft R d S a)).obj (ModuleCat.of S S) := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  let : Module.Free (PolynomialRing R n) (PolynomialRing R n) := coordinatePowerHom_free R d
  let : Module.Finite (PolynomialRing R n) (PolynomialRing R n) := coordinatePowerHom_finite_of_basis R d
  exact LinearEquiv.toModuleIso
    (X₁ := ModuleCat.of (S ⊗[PolynomialRing R n] PolynomialRing R n)
      (S ⊗[PolynomialRing R n] PolynomialRing R n))
    (X₂ := (coextendScalars (algebraMap S (S ⊗[PolynomialRing R n] PolynomialRing R n))).obj
      (ModuleCat.of S S))
    (LinearEquiv.ofBijective (baseChangedFrame (S := S) (polynomialCoefficient R d))
      (baseChangedFrame_bijective_of_pairing (polynomialCoefficient R d) (polynomialPairing_bijective R d)))

/-- The entire native tensor dual frame has its actual original multiplication formula. -/
theorem powerBaseChangeIso_apply (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (x y : powerBaseChangeRing R d S a) :
    (powerBaseChangeIso R d S a).hom x y = powerBaseChangeCoefficient R d S a (y * x) := by
  let : Algebra (PolynomialRing R n) S := a.toAlgebra
  let : Algebra (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra
  let : Module (PolynomialRing R n) (PolynomialRing R n) := (powerMap R d).toAlgebra.toModule
  exact baseChangedFrame_apply (polynomialCoefficient R d) x y

/-- The native counit of the entire actual tensor dual frame is the same original extended coefficient. -/
theorem powerBaseChangeIso_counit (S : Type u) [CommRing S] (a : PolynomialRing R n →+* S)
    (x : powerBaseChangeRing R d S a) :
    (restrictCoextendScalarsAdj (powerBaseChangeLeft R d S a)).counit.app (ModuleCat.of S S)
        ((powerBaseChangeIso R d S a).hom x) = powerBaseChangeCoefficient R d S a x := by
  change (powerBaseChangeIso R d S a).hom x (1 : powerBaseChangeRing R d S a) = _
  rw [powerBaseChangeIso_apply, one_mul]

/-- The original native counit and original coefficient extension commute on all actual pure tensors. -/
theorem powerBaseChangeIso_counit_tensor (S : Type u) [CommRing S]
    (a : PolynomialRing R n →+* S) (s : S) (b : PolynomialRing R n) :
    (restrictCoextendScalarsAdj (powerBaseChangeLeft R d S a)).counit.app (ModuleCat.of S S)
        ((powerBaseChangeIso R d S a).hom (powerBaseChangeTensor R d S a s b)) =
      s * a (coefficientMap R d b) := by
  rw [powerBaseChangeIso_counit, powerBaseChangeCoefficient_tensor]

end EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange
