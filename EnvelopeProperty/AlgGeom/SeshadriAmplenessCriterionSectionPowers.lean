import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading
import EnvelopeProperty.AlgGeom.SchemeGeneratorFrameNeighborhoods
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionFiniteGeneratingSections

/-!
# Seshadri Ampleness Criterion Section Powers

Original whole section powers retain actual local frames and produce
finite generators of all multiples of an actually generated original power. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open CanonicalGeometry SchemeLineSectionEvaluation SchemeTensorSectionHoms
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.pullbackMonoidal

/-- Two actual original section frames pull back to an actual tensor frame. -/
theorem isIso_pullback_tensorSectionHom {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (a : unitObj X ⟶ M) (b : unitObj X ⟶ N)
    (ha : IsIso (pullbackSectionHom f a)) (hb : IsIso (pullbackSectionHom f b)) :
    IsIso (pullbackSectionHom f (tensorSectionHom a b)) := by
  let := ha
  let := hb
  have ht : IsIso (tensorSectionHom (pullbackSectionHom f a) (pullbackSectionHom f b)) :=
    tensorSectionHom_isIso _ _
  let e := Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N
  have hc : IsIso (pullbackSectionHom f (tensorSectionHom a b) ≫ e.inv) :=
    (pullback_tensorSectionHom f a b).symm ▸ ht
  let := hc
  exact IsIso.of_isIso_comp_right (pullbackSectionHom f (tensorSectionHom a b)) e.inv

private theorem isIso_pullback_postcomposeIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (a : unitObj X ⟶ M) (e : M ≅ N)
    (ha : IsIso (pullbackSectionHom f a)) :
    IsIso (pullbackSectionHom f (a ≫ e.hom)) := by
  let F := Scheme.Modules.pullback f
  have h : pullbackSectionHom f (a ≫ e.hom) =
      pullbackSectionHom f a ≫ F.map e.hom :=
    (congrArg (fun q => (pullbackUnitIso f).inv ≫ q) (F.map_comp a e.hom)).trans
      (Category.assoc (pullbackUnitIso f).inv (F.map a) (F.map e.hom)).symm
  let := ha
  have ht : IsIso (pullbackSectionHom f a ≫ F.map e.hom) := inferInstance
  exact h.symm ▸ ht

/-- Actual repeated tensor sections of the SAME original power, including zero. -/
def sectionPowerHom {X : Scheme.{u}} (L : X.Modules) (r : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L r) :
    (q : ℕ) → unitObj X ⟶ bundleTensorPower L (r * q)
  | 0 => 𝟙 (unitObj X)
  | q + 1 => tensorSectionHom (sectionPowerHom L r s q) s ≫
      (TensorPowerBaseIdealGrading.tensorPowerAddIso L (r * q) r ≪≫
        eqToIso (congrArg (bundleTensorPower L) (Nat.mul_succ r q).symm)).hom

/-- Every original repeated section is an actual frame wherever the original
section is a frame. The original pullback and section maps are unchanged. -/
theorem isIso_pullback_sectionPowerHom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) (r : ℕ) (s : unitObj X ⟶ bundleTensorPower L r)
    (hs : IsIso (pullbackSectionHom f s)) :
    ∀ q : ℕ, IsIso (pullbackSectionHom f (sectionPowerHom L r s q)) := by
  intro q
  induction q with
  | zero =>
      change IsIso ((pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (𝟙 (unitObj X)))
      infer_instance
  | succ q ih =>
      exact isIso_pullback_postcomposeIso f
        (tensorSectionHom (sectionPowerHom L r s q) s)
        (TensorPowerBaseIdealGrading.tensorPowerAddIso L (r * q) r ≪≫
          eqToIso (congrArg (bundleTensorPower L) (Nat.mul_succ r q).symm))
        (isIso_pullback_tensorSectionHom f _ _ ih hs)

/-- Actual global generators of one original line power internally produce
finite actual global generators of every multiple power. -/
theorem exists_finite_generatingSections_multiple_of_generatingSections
    {X : Scheme.{u}} [CompactSpace X] (L : X.Modules) (hL : IsInvertible L)
    (b : ℕ) (G : (bundleTensorPower L b).GeneratingSections) (q : ℕ) :
    ∃ H : (bundleTensorPower L (b * q)).GeneratingSections, H.IsFiniteType := by
  classical
  have hlocal (x : X) : ∃ (U : X.Opens)
      (t : unitObj X ⟶ bundleTensorPower L b),
      x ∈ U ∧ IsIso (pullbackSectionHom U.ι t) := by
    obtain ⟨U, hxU, i, hi⟩ := SchemeGeneratorFrameNeighborhoods.exists_affine_generator_frame
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL b) G x
    exact ⟨U.1, SchemeGeneratingSectionsUnit.generatorHom G i, hxU, hi⟩
  choose U t hxU hi using hlocal
  exact exists_finite_generatingSections_of_openSectionIsos
    (bundleTensorPower L (b * q)) U (fun x => sectionPowerHom L b (t x) q)
    (fun x => ⟨x, hxU x⟩)
    (fun x => isIso_pullback_sectionPowerHom (U x).ι L b (t x) (hi x) q)

#check @isIso_pullback_tensorSectionHom
#print axioms isIso_pullback_tensorSectionHom
#check @sectionPowerHom
#print axioms sectionPowerHom
#check @isIso_pullback_sectionPowerHom
#print axioms isIso_pullback_sectionPowerHom
#check @exists_finite_generatingSections_multiple_of_generatingSections
#print axioms exists_finite_generatingSections_multiple_of_generatingSections
end EnvelopeProperty.SeshadriAmplenessCriterion
