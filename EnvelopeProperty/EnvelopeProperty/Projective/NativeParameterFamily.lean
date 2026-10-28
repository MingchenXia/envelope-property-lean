/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeParameterAction
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Actual Laurent-parameter morphisms

Whole ring maps and native scheme morphisms encode the parameter family and
its actual universal-unit specialization.  The source is expressed as native
polynomial Proj, before comparison with the geometric multiplicative-group
product or lifting the action to the constructed ideal blowup.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Actual coefficient extension followed by genuine unit parameter scaling. -/
def parameterUnitBaseChangeHom (f : R →+* S) (u : Sˣ) : R[X] →+* S[X] :=
  (parameterScaleHom (u : S)).comp (Polynomial.mapRingHom f)

@[simp]
theorem parameterUnitBaseChangeHom_C (f : R →+* S) (u : Sˣ) (r : R) :
    parameterUnitBaseChangeHom f u (Polynomial.C r) = Polynomial.C (f r) := by
  simp [parameterUnitBaseChangeHom]

@[simp]
theorem parameterUnitBaseChangeHom_X (f : R →+* S) (u : Sˣ) :
    parameterUnitBaseChangeHom f u Polynomial.X = Polynomial.C (u : S) * Polynomial.X := by
  simp [parameterUnitBaseChangeHom]

/-- The actual entire parameter-family maps compose by multiplication of the
second unit with the coefficient-extended original unit. -/
theorem parameterUnitBaseChangeHom_comp (f : R →+* S) (g : S →+* T)
    (u : Sˣ) (v : Tˣ) :
    (parameterUnitBaseChangeHom g v).comp (parameterUnitBaseChangeHom f u) =
      parameterUnitBaseChangeHom (g.comp f) (v * Units.map g.toMonoidHom u) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp only [RingHom.comp_apply, parameterUnitBaseChangeHom_X, map_mul,
      parameterUnitBaseChangeHom_C, Units.val_mul, Units.coe_map]
    change Polynomial.C (g (u : S)) * (Polynomial.C (v : T) * Polynomial.X) =
      Polynomial.C (v : T) * Polynomial.C (g (u : S)) * Polynomial.X
    ring

/-- The actual family for identity coefficients and unit one is identity. -/
theorem parameterUnitBaseChangeHom_id :
    parameterUnitBaseChangeHom (RingHom.id R) 1 = RingHom.id R[X] := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

/-- Unit one gives the genuine original coefficient-extension polynomial map. -/
theorem parameterUnitBaseChangeHom_one (f : R →+* S) :
    parameterUnitBaseChangeHom f 1 = Polynomial.mapRingHom f := by
  change (parameterScaleHom (1 : S)).comp (Polynomial.mapRingHom f) = _
  rw [parameterScaleHom_one, RingHom.id_comp]

/-- The genuine universal Laurent parameter unit with its actual inverse. -/
def parameterLaurentUnit (R : Type u) [CommRing R] : R[T;T⁻¹]ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; rfl
  inv_val := by rw [← LaurentPolynomial.T_add]; rfl

/-- The actual single universal ring family t ↦ z t. -/
def parameterLaurentHom : R[X] →+* R[T;T⁻¹][X] :=
  parameterUnitBaseChangeHom LaurentPolynomial.C (parameterLaurentUnit R)

/-- Evaluating the entire universal family at any actual extended coefficient
unit gives exactly the corresponding full polynomial ring map. -/
theorem parameterLaurentHom_evaluate (f : R →+* S) (u : Sˣ) :
    (Polynomial.mapRingHom (LaurentPolynomial.eval₂ f u)).comp parameterLaurentHom =
      parameterUnitBaseChangeHom f u := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [parameterLaurentHom]
  · simp [parameterLaurentHom, parameterLaurentUnit]

namespace ProjBerk
variable {n : ℕ}

/-- The actual native polynomial-Proj morphism of the entire parameter family. -/
def nativeParameterFamilyMap (f : R →+* S) (u : Sˣ) :
    NativeProjectiveScheme S[X] n ⟶ NativeProjectiveScheme R[X] n :=
  nativeCoefficientMap (parameterUnitBaseChangeHom f u)

/-- Whole scheme morphisms of the actual parameter family compose by the
genuine coefficient-extended unit product. -/
theorem nativeParameterFamilyMap_comp (f : R →+* S) (g : S →+* T)
    (u : Sˣ) (v : Tˣ) :
    nativeParameterFamilyMap (n := n) (g.comp f) (v * Units.map g.toMonoidHom u) =
      nativeParameterFamilyMap g v ≫ nativeParameterFamilyMap f u := by
  unfold nativeParameterFamilyMap
  rw [← parameterUnitBaseChangeHom_comp, nativeCoefficientMap_comp]

/-- The identity parameter family is the identity whole native scheme map. -/
theorem nativeParameterFamilyMap_id :
    nativeParameterFamilyMap (n := n) (RingHom.id R) 1 = 𝟙 _ := by
  unfold nativeParameterFamilyMap
  rw [parameterUnitBaseChangeHom_id, nativeCoefficientMap_id]

/-- A single genuine native scheme morphism carries the universal Laurent
parameter, before geometric product comparison and blowup lifting. -/
def nativeParameterLaurentFamily :
    NativeProjectiveScheme R[T;T⁻¹][X] n ⟶ NativeProjectiveScheme R[X] n :=
  nativeParameterFamilyMap LaurentPolynomial.C (parameterLaurentUnit R)

end ProjBerk
end EnvelopeProperty
