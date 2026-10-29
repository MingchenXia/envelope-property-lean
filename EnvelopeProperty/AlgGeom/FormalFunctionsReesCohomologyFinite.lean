import EnvelopeProperty.AlgGeom.FormalFunctionsProjectiveFamily
import EnvelopeProperty.AlgGeom.ReesCechChartSections
import ModularCurves.ForMathlib.ProjectiveFactorizationFiniteSections
import ModularCurves.ForMathlib.ProjectiveFactorizationCechHOne
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Genuine finite cohomology of the actual projective schematic Rees family -/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FormalFunctionsReesCohomologyFinite

private theorem structureQuasicoherent (Y : Scheme.{u}) :
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) (unitObj Y) := by
  let e : SheafOfModules.free.{u} (R := Y.ringCatSheaf) PUnit ≅ SheafOfModules.unit.{u} Y.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit.{u} Y.ringCatSheaf)
  obtain ⟨q⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
    (M := SheafOfModules.free.{u} (R := Y.ringCatSheaf) PUnit)
  exact (SheafOfModules.QuasicoherentData.ofIsIso.{u, u, u, u}
    (R := Y.ringCatSheaf) e.hom q).isQuasicoherent

private theorem structureFiniteType (Y : Scheme.{u}) :
    SheafOfModules.IsFiniteType (R := Y.ringCatSheaf) (unitObj Y) := by
  let e : SheafOfModules.free.{u} (R := Y.ringCatSheaf) PUnit ≅ SheafOfModules.unit.{u} Y.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit.{u} Y.ringCatSheaf)
  let G := SheafOfModules.free.generatingSections (R := Y.ringCatSheaf) PUnit
  have : IsIso e.hom := inferInstance
  let H := G.ofEpi e.hom
  let q : SheafOfModules.LocalGeneratorsData.{u} (R := Y.ringCatSheaf) (unitObj Y) :=
    H.localGeneratorsData
  have hq : SheafOfModules.LocalGeneratorsData.IsFiniteType (R := Y.ringCatSheaf) q := by
    constructor
    intro V
    constructor
    change Finite PUnit
    infer_instance
  exact SheafOfModules.IsFiniteType.mk (R := Y.ringCatSheaf) ⟨q, hq⟩

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable (hf : IsProjectiveFactorization f)
variable {ι : Type u} [LinearOrder ι] [Finite ι]
variable (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))

include hf hU hUaff

/-- Actual projectivity and true affine chart pullbacks prove finite cohomology
of the WHOLE actual ordered Rees structure-module Cech complex, in every degree. -/
theorem orderedReesCech_finite (n : ℕ) :
    Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
        (unitObj (FcReesFormalFamily.family I f))
        (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j)).homology n) := by
  let : (unitObj (FcReesFormalFamily.family I f)).IsQuasicoherent :=
    structureQuasicoherent _
  let : (unitObj (FcReesFormalFamily.family I f)).IsFiniteType :=
    structureFiniteType _
  let g := FcReesFormalFamily.familyProjection I f
  let V := fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j
  have hg : IsProjectiveFactorization g :=
    FormalFunctionsProjectiveFamily.family_isProjectiveFactorization I f hf
  have hV : IsOpenCover V :=
    (FcReesFormalChartSheaf.projection I f).iSup_preimage_eq_top hU
  have hVaff : ∀ j, IsAffineOpen (V j) :=
    fun j => (hUaff j).preimage (FcReesFormalChartSheaf.projection I f)
  cases n with
  | zero =>
    exact hg.orderedBaseCechComplex_homology_zero_module_finite
      (unitObj (FcReesFormalFamily.family I f)) V hV
  | succ n =>
    let : Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
        ((baseCechComplex g (unitObj (FcReesFormalFamily.family I f)) V).homology (n + 1)) :=
      hg.baseModuleCech_homology_succ_module_finite_of_affine_openCover
        (unitObj (FcReesFormalFamily.family I f)) V hV hVaff n
    exact Module.Finite.equiv
      (baseCechOrderedHomologyIso g (unitObj (FcReesFormalFamily.family I f)) V (n + 1)).toLinearEquiv

/-- The SAME original finite Rees coefficient modules occur in the explicit
actual original-chart Rees complex, retaining its literal restriction maps. -/
theorem chartReesCech_finite [X.IsSeparated] (n : ℕ) :
    Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((FcReesCechChartSections.chartComplex I f U hUaff).homology n) := by
  let : Module.Finite Γ(Spec (.of (reesAlgebra I)), ⊤)
      ((orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
        (unitObj (FcReesFormalFamily.family I f))
        (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j)).homology n) :=
    orderedReesCech_finite I f hf U hU hUaff n
  let e : (orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
      (unitObj (FcReesFormalFamily.family I f))
      (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j)).homology n ≅
        (FcReesCechChartSections.chartComplex I f U hUaff).homology n :=
    (HomologicalComplex.homologyFunctor _ (.up ℕ) n).mapIso
      (FcReesCechChartSections.orderedCechComplexIso I f U hUaff)
  exact Module.Finite.equiv e.toLinearEquiv

end EnvelopeProperty.FormalFunctionsReesCohomologyFinite
