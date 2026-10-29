import EnvelopeProperty.DI.CechDegreeOneNative
import EnvelopeProperty.AlgGeom.SchemeOpenRestrictionHomology

/-! # The SAME original local representative under native open restriction and counit -/
noncomputable section
namespace EnvelopeProperty.DI.LocalRepresentativeRestriction
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CechDegreeOneDescent
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieLocalContinuationCechAugmentation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (V : X.Opens)
private instance restrictionZero : (Scheme.Modules.restrictFunctor V.ι).PreservesZeroMorphisms :=
  inferInstance

/-- The entire original local map is recovered by the SAME actual adjunction counit. -/
theorem localAdjoint_counit {M N : X.Modules} (φ : LocalMap M N V) :
    (Scheme.Modules.restrictFunctor V.ι).map (localAdjoint V φ) ≫
      (Scheme.Modules.restrictAdjunction V.ι).counit.app (N.restrict V.ι) = φ := by
  exact ((Scheme.Modules.restrictAdjunction V.ι).homEquiv M (N.restrict V.ι)).symm_apply_apply φ

/-- The original counit is a genuine whole complex map on the SAME factor target. -/
def factorCounitComplex (E : CochainComplex X.Modules ℕ) :
    SchemeOpenRestrictionHomology.restrictedComplex V.ι (factorComplex V E) ⟶
      SchemeOpenRestrictionHomology.restrictedComplex V.ι E where
  f q := (Scheme.Modules.restrictAdjunction V.ι).counit.app ((E.X q).restrict V.ι)
  comm' q r _ :=
    ((Scheme.Modules.restrictAdjunction V.ι).counit.naturality
      ((Scheme.Modules.restrictFunctor V.ι).map (E.d q r))).symm

variable {ι : Type u} (U : ι → X.Opens) {M : X.Modules} {E : CochainComplex X.Modules ℕ}
  (D : LocalData U M E) (i : Fin 1 → ι)

/-- The SAME native local representative, genuinely restricted and followed by its original counit. -/
def restrictedRepresentative :
    (HomologicalComplex.single ((tupleOpen U 0 i).toScheme.Modules) (.up ℕ) 1).obj
      (M.restrict (tupleOpen U 0 i).ι) ⟶
      SchemeOpenRestrictionHomology.restrictedComplex (tupleOpen U 0 i).ι E :=
  ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor (tupleOpen U 0 i).ι) (.up ℕ) 1).app M).inv ≫
    ((Scheme.Modules.restrictFunctor (tupleOpen U 0 i).ι).mapHomologicalComplex (.up ℕ)).map
      (localRepresentative U D i) ≫ factorCounitComplex (tupleOpen U 0 i) E

/-- The whole original cochain map becomes precisely the native cochain of the SAME local xi. -/
theorem restrictedRepresentative_eq :
    restrictedRepresentative U D i =
      HomologicalComplex.mkHomFromSingle (D.ξ i) (by
        intro j hj
        have hj' : j = 2 := by simpa using hj.symm
        subst j
        exact D.closed i) := by
  apply HomologicalComplex.from_single_hom_ext
  change _ = (HomologicalComplex.singleObjXSelf (.up ℕ) 1
    (M.restrict (tupleOpen U 0 i).ι)).hom ≫ D.ξ i
  change (Scheme.Modules.restrictFunctor (tupleOpen U 0 i).ι).map
    (localAdjoint (tupleOpen U 0 i) (D.ξ i)) ≫
      (Scheme.Modules.restrictAdjunction (tupleOpen U 0 i).ι).counit.app
        ((E.X 1).restrict (tupleOpen U 0 i).ι) = D.ξ i
  exact localAdjoint_counit _ _

/-- Native homology of the SAME whole factor representative retains the original local cochain. -/
theorem localRepresentative_homology_restrict :
    HomologicalComplex.homologyMap
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.restrictFunctor (tupleOpen U 0 i).ι) (.up ℕ) 1).app M).inv 1 ≫
      HomologicalComplex.homologyMap
        (((Scheme.Modules.restrictFunctor (tupleOpen U 0 i).ι).mapHomologicalComplex (.up ℕ)).map
          (localRepresentative U D i)) 1 ≫
      HomologicalComplex.homologyMap (factorCounitComplex (tupleOpen U 0 i) E) 1 =
      HomologicalComplex.homologyMap
        (HomologicalComplex.mkHomFromSingle (D.ξ i) (by
          intro j hj
          have hj' : j = 2 := by simpa using hj.symm
          subst j
          exact D.closed i)) 1 := by
  rw [← restrictedRepresentative_eq U D i]
  unfold restrictedRepresentative
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
end EnvelopeProperty.DI.LocalRepresentativeRestriction
