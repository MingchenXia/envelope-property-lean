import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf

/-! # Finite free local frames for every exterior cotangent sheaf

All degrees, including degree zero and degrees above the relative dimension,
use the same actual standard-smooth charts.  The empty exterior basis is allowed.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SmoothExteriorFiniteType

open CanonicalGeometry

private theorem generatingSections_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules R} (I : Type u) (e : M ≅ SheafOfModules.free I) :
    IsIso ((SheafOfModules.free.generatingSections I).ofEpi e.inv).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  exact (congrArg IsIso (Category.id_comp e.inv)).mpr
    (inferInstance : IsIso e.inv)

set_option backward.isDefEq.respectTransparency false in
/-- Exterior powers of the standard-smooth differential basis give a finite
free frame of the actual affine exterior sheaf. -/
def affineFrame (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]
    (n q : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    exteriorCotangentSheaf (affineStructuralMap K A) q ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf)
        (ULift.{u} (Set.powersetCard (Fin n) q)) :=
  affineExteriorCotangentSheafIso K A (standardSmoothDifferentialBasis K A n) q ≪≫
    (tilde.functor A).mapIso
      ((((standardSmoothDifferentialBasis K A n).exteriorPower q).reindex
        Equiv.ulift.symm).repr.toModuleIso) ≪≫
      tildeFinsupp (ULift.{u} (Set.powersetCard (Fin n) q))

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

set_option backward.isDefEq.respectTransparency false in
/-- A genuine standard-smooth chart gives a finite free exterior frame on
the original open site, with the coefficient isomorphisms retained. -/
def chartFrame {V : X.Opens} (hV : IsAffineOpen V) (n q : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op V)).hom) :
    (exteriorCotangentSheaf f q).over V ≅
      SheafOfModules.free (R := X.ringCatSheaf.over V)
        (ULift.{u} (Set.powersetCard (Fin n) q)) := by
  let A : CommRingCat := Γ(X, V)
  let φ : CommRingCat.of K ⟶ A := (schemeConstantPresheafMap f).app (.op V)
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K A := hs
  have he : hV.fromSpec ≫ f = affineStructuralMap K A := affineChartStructuralMap f hV
  let I := ULift.{u} (Set.powersetCard (Fin n) q)
  let E : (Scheme.Modules.restrictFunctor hV.fromSpec).obj (exteriorCotangentSheaf f q) ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf) I :=
    exteriorCotangentSheafOpenImmersionIso f hV.fromSpec q ≪≫
      eqToIso (congrArg (fun g => exteriorCotangentSheaf g q) he) ≪≫
      affineFrame K A n q
  let EV : (Scheme.Modules.restrictFunctor V.ι).obj (exteriorCotangentSheaf f q) ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) I :=
    (Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).symm.app
      (exteriorCotangentSheaf f q) ≪≫
    (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app
      (exteriorCotangentSheaf f q) ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso E ≪≫
      openImmersionRestrictFreeIso hV.isoSpec.hom I
  exact (Scheme.Modules.overEquiv V).unitIso.app ((exteriorCotangentSheaf f q).over V) ≪≫
    (Scheme.Modules.overEquiv V).inverse.mapIso
      ((Scheme.Modules.overFunctorEquiv V).app (exteriorCotangentSheaf f q) ≪≫ EV) ≪≫
    schemeOverEquivInverseFreeIso V I

/-- The exterior frame on the selected smooth chart, retaining the original
coefficient ring and open site. -/
def selectedChartFrame (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) (x : X) :
    (exteriorCotangentSheaf f q).over (smoothCotangentChart f n x).val ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (smoothCotangentChart f n x).val)
        (ULift.{u} (Set.powersetCard (Fin n) q)) :=
  chartFrame f (smoothCotangentChart f n x).property.1 n q
    (smoothCotangentChart f n x).property.2.2

/-- The actual smooth charts give finite local generators of every degree. -/
def localGeneratorsData (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    (exteriorCotangentSheaf f q).LocalGeneratorsData where
  I := X
  X x := (smoothCotangentChart f n x).val
  coversTop := smoothCotangentCharts_coversTop f n
  generators x := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over (smoothCotangentChart f n x).val)
    (ULift.{u} (Set.powersetCard (Fin n) q))).ofEpi
      (selectedChartFrame f n q x).inv

/-- Every displayed local generator family is a basis of the actual sheaf. -/
theorem localGeneratorsData_isLocallyFreeData
    (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    (localGeneratorsData f n q).IsLocallyFreeData := by
  constructor
  intro x
  dsimp only [localGeneratorsData] at x
  exact generatingSections_isIso _ _ (selectedChartFrame f n q x)

/-- Every actual exterior cotangent sheaf on the smooth scheme is locally free. -/
theorem isLocallyFree (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    (exteriorCotangentSheaf f q).IsLocallyFree := by
  let := localGeneratorsData_isLocallyFreeData f n q
  exact (localGeneratorsData f n q).isLocallyFree

/-- Quasicoherence follows from the constructed original local free frames. -/
theorem isQuasicoherent (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    (exteriorCotangentSheaf f q).IsQuasicoherent := by
  let G := localGeneratorsData f n q
  let := localGeneratorsData_isLocallyFreeData f n q
  exact G.quasiCoherentData.isQuasicoherent

/-- Smooth geometry, without a supplied finite-presentation certificate,
produces finite type for every original exterior cotangent sheaf. -/
theorem isFiniteType (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    (exteriorCotangentSheaf f q).IsFiniteType := by
  let G := localGeneratorsData f n q
  have hG : G.IsFiniteType := by
    constructor
    intro x
    constructor
    change Finite (ULift.{u} (Set.powersetCard (Fin n) q))
    infer_instance
  refine { exists_localGeneratorsData := ?_ }
  refine ⟨G.shrink, ?_⟩
  constructor
  intro i
  dsimp [SheafOfModules.LocalGeneratorsData.shrink]
  exact hG.isFiniteType i.2.choose

end EnvelopeProperty.Vanishing.SmoothExteriorFiniteType
