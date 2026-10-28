import EnvelopeProperty.Potential.CurveClopenPolynomialFactors
import EnvelopeProperty.Potential.CurvePrimitiveParameter
import EnvelopeProperty.Potential.CurvePrimitiveCharacteristic
import EnvelopeProperty.Potential.CurveGlobalMaximum

/-! # Derived whole analytic preconnectedness and native maxima on integral affine curves -/

open scoped NNReal Polynomial Classical Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

universe u
variable {K B : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsAlgClosed K] [CommRing B] [IsDomain B] [Algebra K B]
  [Algebra.FiniteType K B] [Ring.KrullDimLE 1 B]

/-- Genuine integral affine curve geometry derives preconnectedness of the
whole original relative analytic point space, for every original field norm. -/
theorem preconnectedSpace_integral_affineCurve :
    PreconnectedSpace (RelativeSpectrum (NormedField.valuation (K := K)) B) := by
  classical
  by_cases hB : IsField B
  · let := hB.toField
    have : Module.Finite K B := finite_of_finite_type_of_isJacobsonRing K B
    have : Algebra.IsIntegral K B := Algebra.IsIntegral.of_finite K B
    have hcoeff := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B)
    have : Subsingleton (RelativeSpectrum (NormedField.valuation (K := K)) B) := by
      refine ⟨fun x y => ext_val fun b => ?_⟩
      obtain ⟨a, rfl⟩ := hcoeff.surjective b
      rw [val_algebraMap, val_algebraMap]
    infer_instance
  · obtain ⟨φ, ψ, b, _, hfinite, hfree, hcompat, hprim⟩ :=
      exists_finiteFree_primitive_polynomial_of_dimension_le_one K B hB
    let : Algebra K[X] B := φ.toRingHom.toAlgebra
    let : IsScalarTower K K[X] B :=
      IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    let : Module.Finite K[X] B := hfinite
    let : Module.Free K[X] B := hfree
    let F := FractionRing K[X]
    let L := FractionRing B
    let : Algebra F L := ψ.toAlgebra
    let : IsScalarTower K[X] F L := IsScalarTower.of_algebraMap_eq fun p => by
      rw [IsScalarTower.algebraMap_apply K[X] B L]
      exact (hcompat p).symm
    have hirr := CurvePrimitiveCharacteristic.irreducible_charpoly_lmul K[X] B F L b hprim
    let basis := Module.Free.chooseBasis K[X] B
    let : Fintype (Module.Free.ChooseBasisIndex K[X] B) := Fintype.ofFinite _
    exact FCStandardAffinoid.preconnectedSpace_of_irreducible_charpoly basis b hirr

/-- Native original local psh and an attained whole maximum now derive whole
original constancy, with actual curve connectedness proved from geometry. -/
theorem IsLocallyPSHOn.eq_of_isMaxOn_univ_integral_affineCurve
    {f : RelativeSpectrum (NormedField.valuation (K := K)) B → EReal}
    (hf : IsLocallyPSHOn Set.univ f)
    (y : RelativeSpectrum (NormedField.valuation (K := K)) B)
    (hmax : IsMaxOn f Set.univ y) : ∀ z, f z = f y := by
  let := preconnectedSpace_integral_affineCurve (K := K) (B := B)
  exact hf.eq_of_isMaxOn_univ_of_preconnected y hmax

end EnvelopeProperty.Berkovich.RelativeSpectrum
