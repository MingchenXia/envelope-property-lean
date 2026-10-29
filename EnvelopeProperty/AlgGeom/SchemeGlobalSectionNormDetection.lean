import EnvelopeProperty.AlgGeom.SchemeGlobalSectionModelNormIsometries
import EnvelopeProperty.AlgGeom.Canonical.NativeLineSectionRatios
import EnvelopeProperty.Berkovich.SchemeCenterAffine
import EnvelopeProperty.Berkovich.SchemeLineLocalSectionEvaluation

/-! # Actual original global line sections are detected by genuine native model norms -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
open scoped Classical NNReal
noncomputable section
universe u
namespace EnvelopeProperty.SchemeGlobalSectionNormDetection
open Berkovich RelativeSchemeValuedPoint CanonicalGeometry SchemeLineSectionEvaluation
open SchemeGlobalSectionModelNormIsometries
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- EVERY actual original scheme point has its TRUE relative native point with trivial residue valuation. -/
def trivialPoint (x : X) : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p := by
  let y : SchemeValuedPoint X := ⟨x,1⟩
  refine ⟨y,?_⟩
  apply (SchemeValuedPoint.spectrumHomeomorph (A := k)).injective
  rw [SchemeValuedPoint.basePoint,Homeomorph.apply_symm_apply]
  apply Spectrum.ext_val
  intro a
  rw [SchemeValuedPoint.spectrumHomeomorph_val_apply,SchemeValuedPoint.evalTop_map]
  let ρ : k →+* X.residueField x := (X.Γevaluation x).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  change (1 : _root_.Valuation (X.residueField x) ℝ≥0) (ρ a) = (1 : _root_.Valuation k ℝ≥0) a
  have hρ : ρ a = 0 ↔ a = 0 := by
    constructor
    · intro h
      exact ρ.injective (h.trans ρ.map_zero.symm)
    · intro h
      rw [h,map_zero]
  rw [_root_.Valuation.one_apply_def,_root_.Valuation.one_apply_def,hρ]

/-- The actual native support is the SAME original scheme point. -/
theorem trivialPoint_support (x : X) : (trivialPoint p x).1.point = x := rfl

private theorem sectionHom_zero (M : X.Modules) : SchemeModuleGlobalSections.sectionHom M 0 = 0 := by
  apply M.unitHomEquiv.injective
  change M.unitHomEquiv (M.unitHomEquiv.symm (ModularCurves.moduleSectionsOfTop M 0)) = _
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op 0 = 0
  exact map_zero _

variable [IsProper p]

/-- The TRUE proper-model norm of the SAME actual original zero section is zero at EVERY native point. -/
theorem globalSectionNorm_zero (M : X.Modules) (hM : IsInvertible M)
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p) :
    globalSectionNorm _root_.Valuation.one_apply_le_one y M hM 0 = 0 := by
  rw [globalSectionNorm,(modelLineNorm_eq_zero_iff _root_.Valuation.one_apply_le_one y hM _)]
  rw [sectionHom_zero]
  unfold fibreSection pullbackSectionHom
  rw [Functor.map_zero,comp_zero]
  rfl

private theorem exists_affine_frame (M : X.Modules) (hM : IsInvertible M) (x : X) :
    ∃ U : X.affineOpens,x ∈ U.1 ∧ Nonempty (M.restrict U.1.ι ≅ unitObj U.1.toScheme) := by
  obtain ⟨ι,V,hV,eV⟩ := hM
  have hx : x ∈ ⨆ i,V i := by rw [hV];trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  let EM := overTrivializationOfRestrictIso M (V i)
    (restrictIsoOfPullbackIso M (V i) (eV i).some)
  obtain ⟨U,hUa,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hi
  let E := ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (V i) EM
    (Over.mk (homOfLE hUV))
  exact ⟨⟨U,hUa⟩,hxU,⟨ModularCurves.restrictTrivializationOfOverIso M U E⟩⟩

variable [IsIntegral X]

/-- Every ACTUAL original nonzero whole global line section has TRUE model norm one
at the original generic point with its genuine trivial residue valuation. -/
theorem globalSectionNorm_trivialGenericPoint_eq_one (M : X.Modules) (hM : IsInvertible M)
    (s : Γ(M,⊤)) (hs : s ≠ 0) :
    globalSectionNorm _root_.Valuation.one_apply_le_one (trivialPoint p (genericPoint X)) M hM s = 1 := by
  obtain ⟨U,hU,⟨e⟩⟩ := exists_affine_frame M hM (genericPoint X)
  let : Nonempty U.1 := ⟨⟨genericPoint X,hU⟩⟩
  let y := trivialPoint p (genericPoint X)
  have hy : y.1.point ∈ U.1 := hU
  have hc : center _root_.Valuation.one_apply_le_one y ∈ U.1 :=
    center_mem_of_bounded_affine _root_.Valuation.one_apply_le_one y U hy
      (fun c => _root_.Valuation.one_apply_le_one _)
  let c := ModularCurves.localTrivializationCoefficient M U e s
  have hg : X.germToFunctionField U.1 c ≠ 0 := by
    have h := nativeLocalFrameCoefficient_generator_ne_zero M hM s hs U.1 e
    rw [nativeLocalFrameCoefficient_global] at h
    exact h
  unfold globalSectionNorm
  rw [modelLineNorm_fibreSection_eq_localEval _root_.Valuation.one_apply_le_one y hM U.1 hc
    (pullbackIsoOfRestrictIso M U.1 e) (SchemeModuleGlobalSections.sectionHom M s) c
    (sectionHom_localScalar M U e s)]
  change (1 : _root_.Valuation (X.residueField (genericPoint X)) ℝ≥0)
    (X.residue (genericPoint X) (X.germToFunctionField U.1 c)) = 1
  apply _root_.Valuation.one_apply_of_ne_zero
  intro hz
  exact hg ((X.residue (genericPoint X)).hom.injective (hz.trans (map_zero _).symm))

/-- True original native model norms detect EVERY actual original nonzero global line section. -/
theorem exists_globalSectionNorm_ne_zero (M : X.Modules) (hM : IsInvertible M)
    (s : Γ(M,⊤)) (hs : s ≠ 0) :
    ∃ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p,
      globalSectionNorm _root_.Valuation.one_apply_le_one y M hM s ≠ 0 :=
  ⟨trivialPoint p (genericPoint X),by rw [globalSectionNorm_trivialGenericPoint_eq_one p M hM s hs];exact one_ne_zero⟩

/-- A whole original line section is zero EXACTLY when its TRUE model norm vanishes on the ENTIRE native space. -/
theorem eq_zero_iff_forall_globalSectionNorm_eq_zero (M : X.Modules) (hM : IsInvertible M) (s : Γ(M,⊤)) :
    s = 0 ↔ ∀ y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p,
      globalSectionNorm _root_.Valuation.one_apply_le_one y M hM s = 0 := by
  constructor
  · intro hs y
    rw [hs,globalSectionNorm_zero p M hM y]
  · intro h
    by_contra hs
    obtain ⟨y,hy⟩ := exists_globalSectionNorm_ne_zero p M hM s hs
    exact hy (h y)

end EnvelopeProperty.SchemeGlobalSectionNormDetection
