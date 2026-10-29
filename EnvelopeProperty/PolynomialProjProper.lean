import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Pure polynomial Proj over its actual coefficient ring

Only Mathlib is imported. The variable type can be any finite type, including
empty; the original coefficient ring is arbitrary and may be nonreduced or zero.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.PolynomialProj
variable (A ι : Type u) [CommRing A]

/-- The ORIGINAL constant coefficient map into the whole genuine degree-zero component. -/
def coefficientZero : A →+* MvPolynomial.homogeneousSubmodule ι A 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C ι a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coefficientZero_coe (a : A) :
    (coefficientZero A ι a : MvPolynomial ι A) = MvPolynomial.C a := rfl

/-- Original constants are exactly the true zero-degree homogeneous elements. -/
theorem coefficientZero_bijective : Function.Bijective (coefficientZero A ι) := by
  constructor
  · intro a b h
    exact MvPolynomial.C_injective ι A (congrArg Subtype.val h)
  · intro p
    refine ⟨MvPolynomial.coeff 0 (p : MvPolynomial ι A), Subtype.ext ?_⟩
    exact (MvPolynomial.homogeneousComponent_zero _).symm.trans
      (MvPolynomial.homogeneousComponent_eq_self p.2)

/-- The actual original coefficient scheme map uses this proved whole degree-zero isomorphism. -/
def coefficientZeroIso : CommRingCat.of A ≅ CommRingCat.of (MvPolynomial.homogeneousSubmodule ι A 0) :=
  (RingEquiv.ofBijective (coefficientZero A ι) (coefficientZero_bijective A ι)).toCommRingCatIso

private local instance coefficientZeroTower :
    IsScalarTower A (MvPolynomial.homogeneousSubmodule ι A 0) (MvPolynomial ι A) :=
  IsScalarTower.of_algebraMap_eq (R := A) (S := MvPolynomial.homogeneousSubmodule ι A 0)
    (A := MvPolynomial ι A) fun _ => rfl

/-- The true polynomial projective scheme, allowing any actual variable type. -/
abbrev Scheme := Proj (MvPolynomial.homogeneousSubmodule ι A)

/-- The original polynomial Proj structure morphism into the ORIGINAL coefficient scheme. -/
def projection : Scheme A ι ⟶ Spec (CommRingCat.of A) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι A) ≫
    Spec.map (CommRingCat.ofHom (coefficientZero A ι))

/-- The actual polynomial projective structure morphism is proper for every finite variable type. -/
theorem projection_isProper [Finite ι] : IsProper (projection A ι) := by
  let : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι A 0) (MvPolynomial ι A) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (MvPolynomial.homogeneousSubmodule ι A 0) _
  change IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι A) ≫
    Spec.map (coefficientZeroIso A ι).hom)
  infer_instance

end EnvelopeProperty.PolynomialProj
