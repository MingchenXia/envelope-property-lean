import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalQuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Deligne Illusie Čech Good Truncation

Good truncation of the original honest-cover Cech augmentation. -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieCechGoodTruncation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open DeligneIllusieLocalContinuationCechTotalAugmentation
universe w u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (E : CochainComplex X.Modules ℕ)

/-- The original complex, extended by zero and then genuinely good-truncated. -/
def goodTruncation (p : ℕ) : CochainComplex X.Modules ℤ :=
  CochainComplex.truncLE (E.extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1)

/-- Its top object is the actual outgoing kernel, via the native cycle object. -/
def topCyclesIso (p : ℕ) :
    (goodTruncation E p).X ((p : ℤ) - 1) ≅
      (E.extend ComplexShape.embeddingUpNat).cycles ((p : ℤ) - 1) :=
  CochainComplex.truncLEXIsoCycles (E.extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1)

/-- Good truncation of the same actual total augmentation. -/
def augmentation (p : ℕ) : goodTruncation E p ⟶
    goodTruncation (totalComplex U E) p :=
  CochainComplex.truncLEMap
    (HomologicalComplex.extendMap (totalAugmentation U E) ComplexShape.embeddingUpNat)
    ((p : ℤ) - 1)

/-- The honest cover internally supplies the quasi-isomorphism before truncation. -/
theorem augmentation_quasiIso (hU : ⨆ i, U i = ⊤) (p : ℕ) :
    QuasiIso (augmentation U E p) := by
  let : QuasiIso (totalAugmentation U E) :=
    DeligneIllusieLocalContinuationCechTotalQuasiIso.totalAugmentation_quasiIso U E hU
  let a := HomologicalComplex.extendMap (totalAugmentation U E) ComplexShape.embeddingUpNat
  let : QuasiIso a := inferInstance
  change QuasiIso (CochainComplex.truncLEMap a ((p : ℤ) - 1))
  rw [CochainComplex.quasiIso_truncLEMap_iff]
  intro q hq
  infer_instance

/-- The actual right leg of the truncated Cech roof in the original derived category. -/
def derivedAugmentationIso [HasDerivedCategory.{w} X.Modules]
    (hU : ⨆ i, U i = ⊤) (p : ℕ) :
    DerivedCategory.Q.obj (goodTruncation E p) ≅
      DerivedCategory.Q.obj (goodTruncation (totalComplex U E) p) := by
  let : QuasiIso (augmentation U E p) := augmentation_quasiIso U E hU p
  exact asIso (DerivedCategory.Q.map (augmentation U E p))

/-- The entire forward map remains the image of the original truncated augmentation. -/
theorem derivedAugmentationIso_hom [HasDerivedCategory.{w} X.Modules]
    (hU : ⨆ i, U i = ⊤) (p : ℕ) :
    (derivedAugmentationIso U E hU p).hom =
      DerivedCategory.Q.map (augmentation U E p) := rfl

end EnvelopeProperty.Cartier.DeligneIllusieCechGoodTruncation
