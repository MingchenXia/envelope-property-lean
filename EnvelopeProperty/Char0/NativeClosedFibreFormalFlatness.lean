import EnvelopeProperty.AlgGeom.ClosedFibreLocalLiftFlatness
import EnvelopeProperty.Char0.NativeFormalCompletion
import EnvelopeProperty.ComplexGeometry.Germs.SchemeAffineNativeFormal
import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeFormalNaturality
import Mathlib.RingTheory.FiniteStability
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The actual original smooth affine closed fibre in its native formal ring

Every coefficient action comes from the SAME original affine morphism and
its actual Taylor maps. No flatness or completion comparison for these
maps is supplied as a hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeClosedFibreFormalFlatness

open CategoryTheory AlgebraicGeometry ComplexSchemes
open HolomorphicGerms
open ClosedFibreLocalRing ClosedFibreStalkCompletion ClosedFibreLocalLiftFlatness
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HironakaActualFormalCoordinatePowerDivision
open scoped TensorProduct

variable {R A : Type} [CommRing R] [CommRing A]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Spec (.of A) ⟶ Spec (.of R))
  (n m : ℕ) [hSource : SmoothOfRelativeDimension n (π ≫ f)] [hBase : SmoothOfRelativeDimension m f]
  [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]
  (p : SchemeComplexPoint (π ≫ f))

/-- The original affine R-action is literally the contravariant map of the SAME π. -/
@[instance_reducible] def originalMorphismAlgebra : Algebra R A :=
  (Spec.preimage π).hom.toAlgebra

/-- The actual original target point, before introducing any tensor or completion. -/
def originalBasePoint : SchemeComplexPoint f :=
  schemeComplexPointMap (π ≫ f) f π rfl p

/-- The original residue action is evaluation at the actual image of p. -/
@[instance_reducible] def originalResidueAlgebra : Algebra R ℂ :=
  (schemeAffineOriginalPoint f (originalBasePoint f π p)).toAlgebra

/-- The actual original source point regarded over the actual original base point. -/
def originalPoint :
    letI := originalMorphismAlgebra π
    letI := originalResidueAlgebra f π p
    A →ₐ[R] ℂ := by
  letI := originalMorphismAlgebra π
  letI := originalResidueAlgebra f π p
  exact { schemeAffineOriginalPoint (π ≫ f) p with
    commutes' r := by
      change (Spec.preimage p.val).hom ((Spec.preimage π).hom r) =
        (Spec.preimage (p.val ≫ π)).hom r
      rw [Spec.preimage_comp]
      rfl }

omit [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f] in
/-- The actual whole residue map on the original base point is surjective. -/
theorem originalResidue_surjective :
    letI := originalResidueAlgebra f π p
    Function.Surjective (algebraMap R ℂ) :=
  schemeAffineOriginalPoint_surjective f (originalBasePoint f π p)

omit [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f] in
/-- The actual whole original source point is surjective. -/
theorem originalPoint_surjective : Function.Surjective (originalPoint f π p) :=
  schemeAffineOriginalPoint_surjective (π ≫ f) p

include hSource in
omit [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f] in
/-- Finite type of the original affine R-algebra follows from the actual source smoothness. -/
theorem originalMorphism_finiteType :
    letI := originalMorphismAlgebra π
    Algebra.FiniteType R A := by
  let := originalMorphismAlgebra π
  let : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
  let : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π f
  have hs : LocallyOfFiniteType (Spec.map (Spec.preimage π)) := by
    rw [Spec.map_preimage]
    infer_instance
  change (Spec.preimage π).hom.FiniteType
  exact HasRingHomProperty.Spec_iff.mp hs

/-- The actual original base Taylor map supplies the original R-action on S. -/
@[instance_reducible] def baseFormalAlgebra : Algebra R (MvPowerSeries (Fin m) ℂ) :=
  (schemeAffineNativeFormal f m (originalBasePoint f π p)).toAlgebra

/-- The actual source Taylor map and original π supply the original R-action on F. -/
@[instance_reducible] def sourceFormalAlgebra : Algebra R (MvPowerSeries (Fin n) ℂ) :=
  ((schemeAffineNativeFormal (π ≫ f) n p).comp (Spec.preimage π).hom).toAlgebra

/-- The literal original affine coefficient map, with its derived original R-action. -/
def originalFormal :
    letI := originalMorphismAlgebra π
    letI := sourceFormalAlgebra f π n p
    letI : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
    A →ₐ[R] MvPowerSeries (Fin n) ℂ := by
  letI := originalMorphismAlgebra π
  letI := sourceFormalAlgebra f π n p
  letI : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  exact { schemeAffineNativeFormal (π ≫ f) n p with commutes' _ := rfl }

/-- The actual base formal residue map, over the actual original base residue action. -/
def baseFormalResidue :
    letI := originalResidueAlgebra f π p
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    MvPowerSeries (Fin m) ℂ →ₐ[R] ℂ := by
  letI := originalResidueAlgebra f π p
  letI := baseFormalAlgebra f π m p
  letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  exact { MvPowerSeries.constantCoeff with
    commutes' r := schemeAffineNativeFormal_constantCoeff f m (originalBasePoint f π p) r }

/-- Whole original Taylor naturality manufactures the actual R-algebra substitution on ALL series. -/
def originalFormalPullback :
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := sourceFormalAlgebra f π n p
    letI : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
    MvPowerSeries (Fin m) ℂ →ₐ[R] MvPowerSeries (Fin n) ℂ := by
  letI := baseFormalAlgebra f π m p
  letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  letI := sourceFormalAlgebra f π n p
  letI : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  exact { (schemeMorphismFormalPullback f π n m p).toRingHom with
    commutes' r := (schemeAffineNativeFormal_naturality f π n m p r).symm }

include hSource in
omit [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] in
/-- The original affine tensor ring is noetherian by actual source finite type and formal base noetherianity. -/
theorem originalTensor_noetherian :
    letI := originalMorphismAlgebra π
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    IsNoetherianRing (A ⊗[R] MvPowerSeries (Fin m) ℂ) := by
  let := originalMorphismAlgebra π
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let : Algebra.FiniteType R A := originalMorphism_finiteType f π n
  let : IsNoetherianRing (MvPowerSeries (Fin m) ℂ ⊗[R] A) :=
    Algebra.FiniteType.isNoetherianRing (MvPowerSeries (Fin m) ℂ) _
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin m) ℂ ⊗[R] A)
    (Algebra.TensorProduct.comm R (MvPowerSeries (Fin m) ℂ) A).toRingEquiv

/-- The actual localization at the SAME original closed-fibre tensor point. -/
abbrev OriginalClosedFibreLocalRing :=
  letI := originalMorphismAlgebra π
  letI := originalResidueAlgebra f π p
  letI := baseFormalAlgebra f π m p
  letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  PointLocalRing (pointTensorMap (baseFormalResidue f π m p) (originalPoint f π p))

private theorem formalResidue_kernel (k : ℕ) :
    RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin k) ℂ →+* ℂ) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin k) ℂ) := by
  ext s
  exact IsLocalRing.mem_maximalIdeal_mvPowerSeries_iff.symm

omit [IsSeparated f] [QuasiCompact f] in
private theorem originalFormal_residue :
    letI := originalMorphismAlgebra π
    letI := originalResidueAlgebra f π p
    letI := sourceFormalAlgebra f π n p
    letI : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
    MvPowerSeries.constantCoeff.comp (originalFormal f π n p).toRingHom =
      (originalPoint f π p).toRingHom := by
  let := originalMorphismAlgebra π
  let := originalResidueAlgebra f π p
  let := sourceFormalAlgebra f π n p
  let : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  exact RingHom.ext (schemeAffineNativeFormal_constantCoeff (π ≫ f) n p)

private theorem originalFormalPullback_residue :
    letI := originalResidueAlgebra f π p
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := sourceFormalAlgebra f π n p
    letI : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
    MvPowerSeries.constantCoeff.comp (originalFormalPullback f π n m p).toRingHom =
      (baseFormalResidue f π m p).toRingHom := by
  let := originalResidueAlgebra f π p
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let := sourceFormalAlgebra f π n p
  let : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  exact RingHom.ext (schemeMorphismFormalPullback_constantCoeff f π n m p)

/-- The SAME actual tensor-local lift, manufactured from original coefficients and ALL formal series. -/
def originalClosedFibreLocalLift :
    OriginalClosedFibreLocalRing f π m p →+* MvPowerSeries (Fin n) ℂ := by
  letI := originalMorphismAlgebra π
  letI := originalResidueAlgebra f π p
  letI := baseFormalAlgebra f π m p
  letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  letI := sourceFormalAlgebra f π n p
  letI : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  exact localTensorLift (baseFormalResidue f π m p) (originalPoint f π p)
    MvPowerSeries.constantCoeff (originalFormal f π n p) (originalFormalPullback f π n m p)
    (formalResidue_kernel n) (originalFormal_residue f π n p)
    (originalFormalPullback_residue f π n m p)

/-- Every original affine coefficient retains its literal actual Taylor series. -/
theorem originalClosedFibreLocalLift_includeLeft (a : A) :
    letI := originalMorphismAlgebra π
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    originalClosedFibreLocalLift f π n m p
      (algebraMap (A ⊗[R] MvPowerSeries (Fin m) ℂ) (OriginalClosedFibreLocalRing f π m p)
        ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] MvPowerSeries (Fin m) ℂ) a)) =
      schemeAffineNativeFormal (π ≫ f) n p a := by
  let := originalMorphismAlgebra π
  let := originalResidueAlgebra f π p
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let := sourceFormalAlgebra f π n p
  let : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  exact localTensorLift_includeLeft (baseFormalResidue f π m p) (originalPoint f π p)
    MvPowerSeries.constantCoeff (originalFormal f π n p) (originalFormalPullback f π n m p)
    (formalResidue_kernel n) (originalFormal_residue f π n p)
    (originalFormalPullback_residue f π n m p) a

/-- EVERY original formal base series, including nonconvergent series, retains the SAME original pullback. -/
theorem originalClosedFibreLocalLift_includeRight (s : MvPowerSeries (Fin m) ℂ) :
    letI := originalMorphismAlgebra π
    letI := baseFormalAlgebra f π m p
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    originalClosedFibreLocalLift f π n m p
      (algebraMap (A ⊗[R] MvPowerSeries (Fin m) ℂ) (OriginalClosedFibreLocalRing f π m p)
        ((Algebra.TensorProduct.includeRight : MvPowerSeries (Fin m) ℂ →ₐ[R]
          A ⊗[R] MvPowerSeries (Fin m) ℂ) s)) =
      schemeMorphismFormalPullback f π n m p s := by
  let := originalMorphismAlgebra π
  let := originalResidueAlgebra f π p
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let := sourceFormalAlgebra f π n p
  let : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  exact localTensorLift_includeRight (baseFormalResidue f π m p) (originalPoint f π p)
    MvPowerSeries.constantCoeff (originalFormal f π n p) (originalFormalPullback f π n m p)
    (formalResidue_kernel n) (originalFormal_residue f π n p)
    (originalFormalPullback_residue f π n m p) s

/-- Smooth original geometry derives faithful flatness of this SAME actual full-coefficient map. -/
theorem originalClosedFibreLocalLift_faithfullyFlat :
    (originalClosedFibreLocalLift f π n m p).FaithfullyFlat := by
  let := originalMorphismAlgebra π
  let := originalResidueAlgebra f π p
  let := baseFormalAlgebra f π m p
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let := sourceFormalAlgebra f π n p
  let : Module R (MvPowerSeries (Fin n) ℂ) := Algebra.toModule
  let : Module.Flat R (MvPowerSeries (Fin m) ℂ) := by
    apply RingHom.flat_algebraMap_iff.mp
    change (schemeAffineNativeFormal f m (originalBasePoint f π p)).Flat
    exact schemeAffineNativeFormal_flat f m (originalBasePoint f π p)
  let : IsNoetherianRing (A ⊗[R] MvPowerSeries (Fin m) ℂ) :=
    originalTensor_noetherian f π n m p
  let : IsNoetherianRing (OriginalClosedFibreLocalRing f π m p) := by
    dsimp [OriginalClosedFibreLocalRing]
    infer_instance
  let := NativeFormalCompletion.formalSeries_complete n
  have hker : RingHom.ker (baseFormalResidue f π m p).toRingHom =
      (RingHom.ker (algebraMap R ℂ)).map (algebraMap R (MvPowerSeries (Fin m) ℂ)) := by
    change RingHom.ker MvPowerSeries.constantCoeff =
      (schemeAffineOriginalPointIdeal f (originalBasePoint f π p)).map
        (schemeAffineNativeFormal f m (originalBasePoint f π p))
    rw [schemeAffineNativeFormal_map_pointIdeal, formalVariables_eq_ker_constantCoeff]
  have hm : (pointIdeal (originalPoint f π p)).map (originalFormal f π n p).toRingHom =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) ℂ) := by
    change (schemeAffineOriginalPointIdeal (π ≫ f) p).map
      (schemeAffineNativeFormal (π ≫ f) n p) = _
    rw [schemeAffineNativeFormal_map_pointIdeal, formalVariables_eq_ker_constantCoeff]
    exact formalResidue_kernel n
  exact localTensorLift_faithfullyFlat (baseFormalResidue f π m p) (originalPoint f π p)
    MvPowerSeries.constantCoeff (originalFormal f π n p) (originalFormalPullback f π n m p)
    (formalResidue_kernel n) (originalFormal_residue f π n p)
    (originalFormalPullback_residue f π n m p) (originalResidue_surjective f π p) hker
    (originalPoint_surjective f π p) (schemeAffineNativeFormal_flat (π ≫ f) n p) hm

end EnvelopeProperty.Char0.NativeClosedFibreFormalFlatness
