import EnvelopeProperty.AlgGeom.SegreProjectiveTwist
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionModelNormIsometries
import EnvelopeProperty.AlgGeom.SchemeGlobalSectionTensorPowerNorms

/-! # Actual original Segre line comparison on WHOLE original global sections -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules MvPolynomial Alterations
open Alterations.Geometry.Segre Alterations.Algebra.Segre
open scoped Classical NNReal
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveSegrePullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SchemeLineSectionEvaluation SchemeLineSectionFactorization SchemeTensorSectionHoms
open SchemeGlobalSectionModelNormIsometries SchemeModuleIsoGlobalSections
open Berkovich RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {m n : ℕ}
  (f : X ⟶ projectiveSpace R m) (g : X ⟶ projectiveSpace R n)
  (hfg : f ≫ projectiveSpaceStructure R m = g ≫ projectiveSpaceStructure R n)

/-- The actual original pair map into the genuine original projective product. -/
def pair : X ⟶ projectiveProduct R m n := pullback.lift f g hfg

/-- The actual original Segre composite of the same two original maps. -/
def morphism : X ⟶ projectiveSpace R (dimension m n) := pair f g hfg ≫ segre R m n

/-- The actual Segre composite keeps the SAME entire original base structure. -/
theorem morphism_structure : morphism f g hfg ≫ projectiveSpaceStructure R (dimension m n) =
    f ≫ projectiveSpaceStructure R m := by
  rw [morphism,Category.assoc,segre_structure,← Category.assoc]
  exact congrArg (fun q => q ≫ projectiveSpaceStructure R m) (pullback.lift_fst f g hfg)

/-- The SAME actual whole original O(1) pullback. -/
def line {a : ℕ} (q : X ⟶ projectiveSpace R a) : X.Modules :=
  (Scheme.Modules.pullback q).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (a+1)) 1)

/-- Original projective invertibility is retained by the true original pullback. -/
theorem line_isInvertible {a : ℕ} (q : X ⟶ projectiveSpace R a) : IsInvertible (line q) :=
  (coordinateHyperplanePoleSheafPower_isInvertible (R := R) (0 : Fin (a+1)) 1).pullback q

/-- The actual original coordinate section, as its WHOLE original unit-section morphism. -/
def coordinateSection {a : ℕ} (q : X ⟶ projectiveSpace R a) (i : Fin (a+1)) :
    unitObj X ⟶ line q :=
  pullbackSectionHom q (ProjectiveHomogeneousSections.sectionHom (R := R) 0 1
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i))

/-- The TRUE whole original Segre pullback is the tensor of the SAME original factor pullbacks. -/
def lineIso : line (morphism f g hfg) ≅ line f ⊗ line g :=
  (frameFactorIso (pair f g hfg) (segre R m n) (morphism f g hfg) rfl
    (coordinateHyperplaneTwist (R := R) (0 : Fin (dimension m n+1)) 1)).symm ≪≫
  (Scheme.Modules.pullback (pair f g hfg)).mapIso (SegreProjectiveTwist.twistIso R m n) ≪≫
  (Functor.Monoidal.μIso (Scheme.Modules.pullback (pair f g hfg))
    (SegreProjectiveTwist.leftLine R m n) (SegreProjectiveTwist.rightLine R m n)).symm ≪≫
  (frameFactorIso (pair f g hfg)
      (pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)) f
      (pullback.lift_fst f g hfg) (coordinateHyperplaneTwist (R := R) (0 : Fin (m+1)) 1) ⊗ᵢ
    frameFactorIso (pair f g hfg)
      (pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)) g
      (pullback.lift_snd f g hfg) (coordinateHyperplaneTwist (R := R) (0 : Fin (n+1)) 1))

/-- EVERY original Segre coordinate becomes its SAME actual whole original tensor section. -/
theorem lineIso_coordinate (a : Fin (m+1) × Fin (n+1)) :
    coordinateSection (morphism f g hfg) (indexEquiv m n a) ≫ (lineIso f g hfg).hom =
      tensorSectionHom (coordinateSection f a.1) (coordinateSection g a.2) := by
  let δ := pair f g hfg
  let α := ProjectiveHomogeneousSections.sectionHom (R := R) 0 1
    (MvPolynomial.X (indexEquiv m n a)) (MvPolynomial.isHomogeneous_X R _)
  let e0 := frameFactorIso δ (segre R m n) (morphism f g hfg) rfl
    (coordinateHyperplaneTwist (R := R) (0 : Fin (dimension m n+1)) 1)
  have hc : pullbackSectionHom δ (SegreProjectiveTwist.segreSection R m n a) ≫ e0.hom =
      coordinateSection (morphism f g hfg) (indexEquiv m n a) :=
    pullbackSectionHom_factor δ (segre R m n) (morphism f g hfg) rfl α
  have hcancel : coordinateSection (morphism f g hfg) (indexEquiv m n a) ≫ e0.inv =
      pullbackSectionHom δ (SegreProjectiveTwist.segreSection R m n a) := by
    rw [← hc,Category.assoc,e0.hom_inv_id]
    exact Category.comp_id _
  change coordinateSection (morphism f g hfg) (indexEquiv m n a) ≫
    e0.inv ≫ (Scheme.Modules.pullback δ).map (SegreProjectiveTwist.twistIso R m n).hom ≫ _ = _
  rw [← Category.assoc,hcancel]
  change pullbackSectionHom δ (SegreProjectiveTwist.segreSection R m n a) ≫ _ = _
  rw [← Category.assoc]
  rw [show pullbackSectionHom δ (SegreProjectiveTwist.segreSection R m n a) ≫
      (Scheme.Modules.pullback δ).map (SegreProjectiveTwist.twistIso R m n).hom =
      pullbackSectionHom δ (SegreProjectiveTwist.tensorSection R m n a) by
    rw [← SegreProjectiveTwist.twistIso_section R m n a]
    simp only [pullbackSectionHom,Functor.map_comp,Category.assoc]]
  simp only [Iso.trans_hom,Iso.symm_hom,tensorIso_hom]
  rw [SegreProjectiveTwist.tensorSection,← Category.assoc,pullback_tensorSectionHom,tensorSectionHom_comp,
    pullbackSectionHom_factor,pullbackSectionHom_factor]
  rfl

/-- The derived geometric whole line isomorphism gives the true ENTIRE original section equivalence. -/
def wholeSectionsEquiv : Γ(line (morphism f g hfg),⊤) ≃ Γ(line f ⊗ line g,⊤) :=
  moduleIsoTopEquiv (lineIso f g hfg)

variable {v : Valuation R ℝ≥0} {p : X ⟶ Spec (.of R)} [IsProper p]
  (hb : ∀ r,v r ≤ 1) (y : RelativeSchemeValuedPoint v p)

/-- EVERY original whole section retains its true original proper-model norm under this DERIVED geometric iso. -/
theorem wholeSectionsNorm (s : Γ(line (morphism f g hfg),⊤)) :
    globalSectionNorm hb y (line (morphism f g hfg)) (line_isInvertible _) s =
      globalSectionNorm hb y (line f ⊗ line g)
        ((line_isInvertible f).monoidalTensor (line_isInvertible g))
        (wholeSectionsEquiv f g hfg s) :=
  globalSectionNorm_moduleIso hb y (line_isInvertible _)
    ((line_isInvertible f).monoidalTensor (line_isInvertible g)) (lineIso f g hfg) s

/-- Every actual original finite weighted family keeps its ENTIRE true norm evaluation and SAME weights. -/
theorem weightedNormEval (d : ℕ) (T : Finset (Γ(line (morphism f g hfg),⊤) × ℝ)) :
    SchemeGlobalSectionModelNormIsometries.weightedNormEval hb y d
      (line (morphism f g hfg)) (line_isInvertible _) T =
    SchemeGlobalSectionModelNormIsometries.weightedNormEval hb y d
      (line f ⊗ line g) ((line_isInvertible f).monoidalTensor (line_isInvertible g))
      (T.image fun q => (wholeSectionsEquiv f g hfg q.1,q.2)) :=
  weightedNormEval_moduleIso hb y d (line_isInvertible _)
    ((line_isInvertible f).monoidalTensor (line_isInvertible g)) (lineIso f g hfg) T

/-- The original proper-model norm of EVERY actual Segre coordinate is its actual factor product, INCLUDING zero and nongeneric supports. -/
theorem coordinateNorm (a : Fin (m+1) × Fin (n+1)) :
    modelHomNorm hb y (isInvertible_unit (X := X)) (line_isInvertible _)
      (coordinateSection (morphism f g hfg) (indexEquiv m n a)) =
    modelHomNorm hb y (isInvertible_unit (X := X)) (line_isInvertible f) (coordinateSection f a.1) *
      modelHomNorm hb y (isInvertible_unit (X := X)) (line_isInvertible g) (coordinateSection g a.2) := by
  have h := congrArg (modelHomNorm hb y (isInvertible_unit (X := X))
    ((line_isInvertible f).monoidalTensor (line_isInvertible g))) (lineIso_coordinate f g hfg a)
  rw [modelHomNorm_comp hb y (isInvertible_unit (X := X)) (line_isInvertible _)
    ((line_isInvertible f).monoidalTensor (line_isInvertible g)),
    modelHomNorm_iso hb y (line_isInvertible _)
      ((line_isInvertible f).monoidalTensor (line_isInvertible g)) (lineIso f g hfg),mul_one,
    SchemeGlobalSectionTensorPowerNorms.modelHomNorm_tensorSectionHom] at h
  exact h

end EnvelopeProperty.ProjectiveSegrePullbackSections
