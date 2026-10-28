import EnvelopeProperty.AlgGeom.SchemeCoherentEulerIndex
import EnvelopeProperty.AlgGeom.CohomologyEulerAdditivity
import ModularCurves.ForMathlib.SchemeModuleBaseCechExact

/-! # The actual coherent Euler relation from the original short exact sequence -/
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules TopCat TopCat.Sheaf
noncomputable section
universe u
namespace EnvelopeProperty.SchemeCoherentEulerExact
open SchemeCoherentEulerIndex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}

private def homologyZeroKernelIso {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    C.homology 0 ≅ ModuleCat.of R (LinearMap.ker (C.d 0 1).hom) := by
  let S := C.sc' 0 0 1
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 := CochainComplex.prev_nat_zero
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  have hzero : S.moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d 0 0).hom x = 0
    rw [C.shape 0 0 (by simp)]
    rfl
  have hrange : LinearMap.range S.moduleCatToCycles = ⊥ := by rw [hzero, LinearMap.range_zero]
  exact C.homologyIsoSc' 0 0 1 hprev hnext ≪≫ S.moduleCatHomologyIso ≪≫
    ((LinearMap.range S.moduleCatToCycles).quotEquivOfEqBot hrange).toModuleIso

/-- The actual original sections are the whole original field Cech H⁰. -/
def fieldSectionsCechZeroIso (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    fieldSections f M ≅ fieldCech f M U 0 :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).mapIso
    (baseSectionsIsoKernelBaseCechDifferential f M U hU ≪≫
      (homologyZeroKernelIso (baseCechComplex f M U)).symm)

/-- The actual field-linear Cech complex, functorially in the SAME original module. -/
def fieldComplexFunctor (f : X ⟶ Spec (.of k)) {ι : Type u} (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{u} k) ℕ :=
  baseCechComplexFunctor f U ⋙
    (ModuleCat.restrictScalars (baseScalar (k := k))).mapHomologicalComplex (.up ℕ)

instance fieldComplexFunctor_preservesZeroMorphisms (f : X ⟶ Spec (.of k))
    {ι : Type u} (U : ι → X.Opens) : (fieldComplexFunctor f U).PreservesZeroMorphisms := by
  dsimp only [fieldComplexFunctor]
  infer_instance

/-- Homology retains precisely the original base-field action under restriction of scalars. -/
def fieldComplexHomologyIso (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    ((fieldComplexFunctor f U).obj M).homology n ≅ fieldCech f M U n :=
  ((baseCechComplex f M U).sc n).mapHomologyIso
    (ModuleCat.restrictScalars (baseScalar (k := k)))

/-- The coherent Euler index is the Euler index of the SAME actual field complex on every affine cover. -/
theorem eulerIndex_eq_fieldComplex [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) :
    SchemeCoherentEulerIndex.eulerIndex f M =
      CohomologyEulerAdditivity.eulerIndex ((fieldComplexFunctor f U).obj M) := by
  rw [SchemeCoherentEulerIndex.eulerIndex_eq_on_cover f M U hU hUa]
  unfold CohomologyEulerAdditivity.eulerIndex
  rw [(fieldComplexHomologyIso f M U 0).toLinearEquiv.finrank_eq,
    (fieldComplexHomologyIso f M U 1).toLinearEquiv.finrank_eq,
    (fieldSectionsCechZeroIso f M U hU).toLinearEquiv.finrank_eq]

/-- The actual original short exact sequence satisfies the genuine coherent Euler
relation whenever the actual whole original left H² vanishes. No cohomology
finiteness, Cech exactness, cover or degree-additivity certificate is supplied. -/
theorem eulerIndex_add [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [S.X₁.IsFiniteType] [S.X₂.IsFiniteType] [S.X₃.IsFiniteType]
    (h₂ : Subsingleton (CategoryTheory.Sheaf.H S.X₁.sheaf 2)) :
    SchemeCoherentEulerIndex.eulerIndex f S.X₂ =
      SchemeCoherentEulerIndex.eulerIndex f S.X₁ + SchemeCoherentEulerIndex.eulerIndex f S.X₃ := by
  let U := finiteAffineOpens X
  have hU := finiteAffineOpens_cover X
  have hUa := finiteAffineOpens_isAffine X
  have hfinite (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) (hn : n ≤ 1) :
      Module.Finite k (((fieldComplexFunctor f U).obj M).homology n) := by
    let : Module.Finite k (fieldCech f M U n) := by
      cases n with
      | zero =>
        let : Module.Finite k (fieldSections f M) := fieldSections_finite f hf M
        exact Module.Finite.equiv (fieldSectionsCechZeroIso f M U hU).toLinearEquiv
      | succ n => exact fieldCech_succ_finite f hf M U hU hUa n
    exact Module.Finite.equiv (fieldComplexHomologyIso f M U n).symm.toLinearEquiv
  let : Module.Finite k (((S.map (fieldComplexFunctor f U)).X₁).homology 0) := hfinite S.X₁ 0 (by omega)
  let : Module.Finite k (((S.map (fieldComplexFunctor f U)).X₂).homology 0) := hfinite S.X₂ 0 (by omega)
  let : Module.Finite k (((S.map (fieldComplexFunctor f U)).X₃).homology 0) := hfinite S.X₃ 0 (by omega)
  let : Module.Finite k (((S.map (fieldComplexFunctor f U)).X₁).homology 1) := hfinite S.X₁ 1 (by omega)
  let : Module.Finite k (((S.map (fieldComplexFunctor f U)).X₂).homology 1) := hfinite S.X₂ 1 (by omega)
  let : Module.Finite k (((S.map (fieldComplexFunctor f U)).X₃).homology 1) := hfinite S.X₃ 1 (by omega)
  have hbase := hS.map_baseCechComplexFunctor_of_affine_openCover f U hUa
  have hfield : (S.map (fieldComplexFunctor f U)).ShortExact :=
    hbase.map_of_exact ((ModuleCat.restrictScalars (baseScalar (k := k))).mapHomologicalComplex (.up ℕ))
  have hzero : IsZero (((fieldComplexFunctor f U).obj S.X₁).homology 2) := by
    have hnative := cechComplex_exactAt_succ_of_affine_openCover S.X₁ U hU hUa 1 h₂
    have hbaseExact := (baseCechComplex_exactAt_iff f S.X₁ U 2).mpr hnative
    have hbaseZero := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hbaseExact
    apply IsZero.of_iso _ (fieldComplexHomologyIso f S.X₁ U 2)
    exact (ModuleCat.restrictScalars (baseScalar (k := k))).map_isZero hbaseZero
  rw [eulerIndex_eq_fieldComplex f S.X₁ U hU hUa,
    eulerIndex_eq_fieldComplex f S.X₂ U hU hUa,
    eulerIndex_eq_fieldComplex f S.X₃ U hU hUa]
  exact CohomologyEulerAdditivity.eulerIndex_add (S.map (fieldComplexFunctor f U)) hfield hzero

end EnvelopeProperty.SchemeCoherentEulerExact
