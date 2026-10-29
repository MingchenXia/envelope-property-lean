import EnvelopeProperty.AlgGeom.SchemeLineSectionStandardUnitLifting
import EnvelopeProperty.AlgGeom.SchemeAmpleCoherentGlobalGeneration
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionFixedCoefficientCutStability
import EnvelopeProperty.Projective.TestConfigurationSectionTransport

/-! # Actual fixed-cut uniform local generation

The two eventual bounds are chosen internally, before all points of the same
actual cut. The final inputs contain neither standard-unit surjectivity nor a
cut generating family. Every resulting open frame uses the same original section.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionFixedCutUniformLocalGeneration
open CanonicalGeometry SchemeCoherentEulerIndex SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native ampleness on the SAME actual cut internally gives, uniformly before
all its points, nonzero original point fibers and SAME-section open singleton
finite generation of every large original fixed-coefficient twist. -/
theorem exists_eventual_cut_point_open_singleton_generatingSections
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L)
    (r : ℕ) (hr : 0 < r) (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p)
      ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : X, x ∈ I.support →
      ∃ t : unitObj X ⟶ E ⊗ bundleTensorPower L (n + r),
        pullbackSectionHom (X.fromSpecResidueField x) t ≠ 0 ∧
        ∃ U : X.Opens, x ∈ U ∧ IsIso (pullbackSectionHom U.ι t) ∧
          ∃ G : ((Scheme.Modules.pullback U.ι).obj
            (E ⊗ bundleTensorPower L (n + r))).GeneratingSections,
            G.IsFiniteType ∧ Nat.card G.I = 1 ∧
              ∀ a : G.I, SchemeGeneratingSectionsUnit.generatorHom G a =
                pullbackSectionHom U.ι t := by
  classical
  dsimp only
  intro hI
  let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s
  let g := I.subschemeι
  let F := Scheme.Modules.pullback g
  let ED := F.obj E
  let LD := F.obj L
  let hp := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : X.IsSeparated := ⟨by
    have hsep : IsSeparated (p ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let U := finiteAffineOpens X
  obtain ⟨Ns, hNs⟩ :=
    SeshadriAmplenessCriterionFixedCoefficientCutStability.exists_fixedCoefficient_singleCut_sections_surjective_of_ample
      p hp U (finiteAffineOpens_cover X) (finiteAffineOpens_isAffine X)
      E L hE hL r hr s hs hI
  have hED : IsInvertible ED := hE.pullback g
  let : ED.IsQuasicoherent := hED.isQuasicoherent
  let : ED.IsFinitePresentation := hED.isFinitePresentation
  let : ED.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
    (R := I.subscheme.ringCatSheaf) ED
  obtain ⟨Ng, hNg⟩ := SchemeAmpleCoherentGlobalGeneration.exists_eventual_generatingSections
    (g ≫ p) ED LD hI
  refine ⟨max Ns Ng, ?_⟩
  intro n hn x hx
  let M := E ⊗ bundleTensorPower L (n + r)
  have hM : IsInvertible M :=
    (hE.tensorObj (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (n + r))).of_iso
      (ModularCurves.monoidalTensorObjIso E (bundleTensorPower L (n + r)))
  obtain ⟨G, hG⟩ := hNg (n + r)
    ((le_max_right Ns Ng).trans (hn.trans (Nat.le_add_right n r)))
  let : G.IsFiniteType := hG
  let : F.Monoidal := pullbackMonoidal g
  let e : F.obj M ≅ ED ⊗ bundleTensorPower LD (n + r) :=
    (Functor.Monoidal.μIso F E (bundleTensorPower L (n + r))).symm ≪≫
      (Iso.refl ED ⊗ᵢ TestConfigurationSectionTransport.tensorPowerPullbackIso g L (n + r))
  let H := G.ofEpi e.inv
  have honto : Function.Surjective (((pullbackPushforwardAdjunction g).unit.app M).app ⊤) :=
    hNs n ((le_max_left Ns Ng).trans hn)
  have hx' : x ∈ Set.range g := by
    rw [I.range_subschemeι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨t, ht⟩ := SchemeLineSectionStandardUnitLifting.exists_nonzero_pointFiber_lift_of_standardUnit_surjective
    g M hM H honto y
  refine ⟨t, ht, ?_⟩
  exact SchemeLineSectionFiberOpenFrame.exists_open_singleton_generatingSections_of_pullbackSectionHom_ne_zero
    M hM t (g y) ht

#print axioms exists_eventual_cut_point_open_singleton_generatingSections
end EnvelopeProperty.SeshadriAmplenessCriterionFixedCutUniformLocalGeneration
