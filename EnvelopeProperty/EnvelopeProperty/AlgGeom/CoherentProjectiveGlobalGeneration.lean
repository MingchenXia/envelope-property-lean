import EnvelopeProperty.AlgGeom.ProjectiveTwistGlobalGeneration
import EnvelopeProperty.AlgGeom.ProjectiveTwistTensorAddition
import EnvelopeProperty.AlgGeom.SchemeModuleGeneratingCoproduct
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistFinitePresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Genuine eventual global generation on original polynomial projective space -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.CoherentProjectiveGlobalGeneration
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem negative_twist_eq_idealPower (j : σ) (n : ℕ) :
    coordinateHyperplaneTwist (R := R) j (-(n : ℤ)) =
      coordinateHyperplaneIdealModulePower (R := R) j n := by
  cases n with
  | zero => rfl
  | succ n => rfl

private theorem nonnegative_difference (n d : ℕ) (h : n ≤ d) :
    -(n : ℤ) + (d : ℤ) = ((d-n : ℕ) : ℤ) := by
  omega

private theorem tensorMap_epi {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi ((tensorRight L).map f) := by
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  infer_instance

private def tensorCoproductQuotient {X : Scheme.{u}} {ι : Type}
    (L : X.Modules) (hL : IsInvertible L) (M : ι → X.Modules)
    {N : X.Modules} (f : (∐ M) ⟶ N) :
    (∐ fun i => M i ⊗ L) ⟶ N ⊗ L := by
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  exact (PreservesCoproduct.iso (tensorRight L) M).inv ≫ (tensorRight L).map f

private theorem tensorCoproductQuotient_epi {X : Scheme.{u}} {ι : Type}
    (L : X.Modules) (hL : IsInvertible L) (M : ι → X.Modules)
    {N : X.Modules} (f : (∐ M) ⟶ N) [Epi f] :
    Epi (tensorCoproductQuotient L hL M f) := by
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  let : Epi ((tensorRight L).map f) := tensorMap_epi L hL f
  unfold tensorCoproductQuotient
  infer_instance

private def pullGenerators {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (G : N.GeneratingSections) : M.GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso e.symm G

private theorem pullGenerators_isFiniteType {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (G : N.GeneratingSections) [G.IsFiniteType] :
    (pullGenerators e G).IsFiniteType := by
  constructor
  change Finite G.I
  exact (inferInstance : G.IsFiniteType).finite

private def pushGenerators {X : Scheme.{u}} {M N : X.Modules}
    (G : M.GeneratingSections) (f : M ⟶ N) (hf : Epi f) : N.GeneratingSections :=
  @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ G f hf

private theorem pushGenerators_isFiniteType {X : Scheme.{u}} {M N : X.Modules}
    (G : M.GeneratingSections) (f : M ⟶ N) (hf : Epi f) [G.IsFiniteType] :
    (pushGenerators G f hf).IsFiniteType := by
  constructor
  change Finite G.I
  exact (inferInstance : G.IsFiniteType).finite

private def negativeTensorIso (i j k : σ) (n d : ℕ) (h : n ≤ d) :
    coordinateHyperplaneIdealModulePower (R := R) i n ⊗
        coordinateHyperplaneTwist (R := R) j (d : ℤ) ≅
      coordinateHyperplaneTwist (R := R) k ((d-n : ℕ) : ℤ) :=
  ((eqToIso (negative_twist_eq_idealPower (R := R) i n).symm ⊗ᵢ Iso.refl _) ≪≫
    ProjectiveTwistTensorAddition.tensorIso i j k (-(n : ℤ)) (d : ℤ)) ≪≫
    eqToIso (congrArg (coordinateHyperplaneTwist (R := R) k) (nonnegative_difference n d h))

/-- The original finite-type quasicoherent module on actual finite-coordinate
polynomial projective space has ACTUAL finite global generating sections after
EVERY sufficiently large original nonnegative twist. The bound, generating
sections and their actual free evaluation epimorphism are all derived from
the original geometry and finite-type hypothesis, not supplied as certificates. -/
theorem exists_eventual_generatingSections [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : (M ⊗ coordinateHyperplaneTwist (R := R) j (d : ℤ)).GeneratingSections,
        G.IsFiniteType := by
  classical
  obtain ⟨r, jj, nn, f, hf⟩ := exists_fin_coordinateNegativeTwist_quotient M
  refine ⟨Finset.univ.sup nn, ?_⟩
  intro d hd
  have hn (i : Fin r) : nn i ≤ d :=
    (Finset.le_sup (f := nn) (Finset.mem_univ i)).trans hd
  let Q : Fin r → (Proj (homogeneousSubmodule σ R)).Modules :=
    fun i => coordinateHyperplaneIdealModulePower (R := R) (jj i) (nn i)
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  let hL : IsInvertible L := coordinateHyperplaneTwist_isInvertible j (d : ℤ)
  let e (i : Fin r) : Q i ⊗ L ≅
      coordinateHyperplaneTwist (R := R) j ((d-nn i : ℕ) : ℤ) :=
    negativeTensorIso (jj i) j j (nn i) d (hn i)
  let G (i : Fin r) : (Q i ⊗ L).GeneratingSections :=
    pullGenerators (e i) (ProjectiveTwistGlobalGeneration.generatingSections j (d-nn i))
  have hG (i : Fin r) : (G i).IsFiniteType := by
    let : (ProjectiveTwistGlobalGeneration.generatingSections
      (R := R) j (d-nn i)).IsFiniteType :=
      ProjectiveTwistGlobalGeneration.generatingSections_isFiniteType j (d-nn i)
    exact pullGenerators_isFiniteType (e i)
      (ProjectiveTwistGlobalGeneration.generatingSections j (d-nn i))
  let : ∀ i, (G i).IsFiniteType := hG
  let H := SchemeModuleGeneratingCoproduct.generatingSections (fun i => Q i ⊗ L) G
  let : H.IsFiniteType :=
    SchemeModuleGeneratingCoproduct.generatingSections_isFiniteType (fun i => Q i ⊗ L) G
  let : Epi f := hf
  let q := tensorCoproductQuotient L hL Q f
  have hq : Epi q := tensorCoproductQuotient_epi L hL Q f
  exact ⟨pushGenerators H q hq, pushGenerators_isFiniteType H q hq⟩

/-- Every sufficiently large original twist is the quotient of an ACTUAL
finite free structure module by its actual original generating sections. -/
theorem exists_eventual_free_epi [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ (I : Type u) (_ : Finite I)
        (p : SheafOfModules.free I ⟶
          (M ⊗ coordinateHyperplaneTwist (R := R) j (d : ℤ) :
            (Proj (homogeneousSubmodule σ R)).Modules)),
        Epi p := by
  obtain ⟨N, hN⟩ := exists_eventual_generatingSections M j
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨G, hG⟩ := hN d hd
  exact ⟨G.I, hG.finite, G.π, G.epi⟩

/-- The actual canonical evaluation from ALL original global sections of the
SAME original module, with no finite-family choice in its definition. -/
def canonicalEvaluation {X : Scheme.{u}} (M : X.Modules) :
    SheafOfModules.free M.sections ⟶ M :=
  M.freeHomEquiv.symm (fun s => s)

private theorem epi_of_epi_factor {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hh : Epi h) (hw : f ≫ g = h) :
    Epi g := by
  let : Epi h := hh
  exact epi_of_epi_fac hw

private theorem canonicalEvaluation_epi_of_generators {X : Scheme.{u}}
    {M : X.Modules} (G : M.GeneratingSections) : Epi (canonicalEvaluation M) := by
  have hfac : SheafOfModules.freeMap G.s ≫ canonicalEvaluation M = G.π := by
    apply M.freeHomEquiv.injective
    funext i
    have h₁ := SheafOfModules.freeHomEquiv_comp_apply
      (SheafOfModules.freeMap G.s) (canonicalEvaluation M) i
    have h₂ := congrArg (SheafOfModules.sectionsMap (canonicalEvaluation M))
      (congrFun (SheafOfModules.freeHomEquiv_freeMap (R := X.ringCatSheaf) G.s) i)
    have h₃ := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (M := M) (fun s : M.sections => s) (G.s i)
    have h₄ := congrFun (M.freeHomEquiv.apply_symm_apply G.s) i
    exact h₁.trans (h₂.trans (h₃.trans h₄.symm))
  exact epi_of_epi_factor _ _ _ G.epi hfac

/-- The actual canonical evaluation from ALL original global sections is
surjective after every sufficiently large original twist; this is derived
from the constructed finite original generating families. -/
theorem exists_eventual_canonicalEvaluation_epi [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      Epi (canonicalEvaluation (M ⊗ coordinateHyperplaneTwist (R := R) j (d : ℤ))) := by
  obtain ⟨N, hN⟩ := exists_eventual_generatingSections M j
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨G, _hG⟩ := hN d hd
  exact canonicalEvaluation_epi_of_generators G

end EnvelopeProperty.CoherentProjectiveGlobalGeneration
