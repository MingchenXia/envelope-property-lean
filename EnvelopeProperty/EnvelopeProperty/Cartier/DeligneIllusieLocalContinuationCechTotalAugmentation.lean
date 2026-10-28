import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechBicomplex
import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdge

/-! # The actual native total Cech augmentation with original structure-sheaf coefficients -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace Opposite
open DeligneIllusieLocalContinuationCechAugmentation DeligneIllusieLocalContinuationCechBicomplex
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- The EXISTING native total of the SAME actual original module Cech bicomplex. -/
def totalComplex (E : CochainComplex X.Modules ℕ) : CochainComplex X.Modules ℕ :=
  HomologicalComplex₂.total (bicomplex U E) (ComplexShape.up ℕ)

/-- Actual original units give a genuine total cochain map; all required equations are DERIVED. -/
def totalAugmentation (E : CochainComplex X.Modules ℕ) : E ⟶ totalComplex U E :=
  HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex U E) E
    (fun q => augmentation U (E.X q))
    (fun q q' _ => augmentation_naturality U (E.d q q'))
    (fun q => augmentationToBicomplex_inner_d U E q)

/-- EVERY entire native component is the SAME original unit followed by the actual total injection. -/
theorem totalAugmentation_f (E : CochainComplex X.Modules ℕ) (q : ℕ) :
    (totalAugmentation U E).f q =
      augmentation U (E.X q) ≫ HomologicalComplex₂.ιTotal (bicomplex U E) (ComplexShape.up ℕ) q 0 q rfl := rfl

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation
