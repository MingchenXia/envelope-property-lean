import EnvelopeProperty.Vanishing.NadelBlowupCanonicalExceptionalGenerators
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverDetection
import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
/-! # The original ideal generators produce the actual exceptional-line generating family -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigExceptionalGenerators
open NadelBlowupCanonicalExceptionalGenerators

private theorem epi_of_pullback_cover {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u})
    (c : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (c i)]
    (hcover : ∀ x : X, ∃ i y, c i y = x) {M N : X.Modules} (q : M ⟶ N)
    (hq : ∀ i, Epi ((pullback (c i)).map q)) : Epi q := by
  constructor
  intro P a b hab
  apply SchemeModuleOpenCoverDetection.hom_ext Y c hcover
  intro i
  let : Epi ((pullback (c i)).map q) := hq i
  apply (cancel_epi ((pullback (c i)).map q)).mp
  rw [← Functor.map_comp, hab, Functor.map_comp]

variable {A : Type u} [CommRing A] (I : Ideal A) {ι : Type u}
    (g : ι → I) (hspan : Ideal.span (Set.range (fun i => (g i : A))) = I)

def generatingMap : SheafOfModules.free (R := (affineBlowUp I).ringCatSheaf) ι ⟶
    (affineBlowUp.exceptionalIdeal I).toModules :=
  ((affineBlowUp.exceptionalIdeal I).toModules).freeHomEquiv.symm
    (fun i => ((affineBlowUp.exceptionalIdeal I).toModules).unitHomEquiv (exceptionalSection I (g i)))

theorem generatingMap_ι (i : ι) :
    SheafOfModules.ιFree (R := (affineBlowUp I).ringCatSheaf) i ≫ generatingMap I g =
      exceptionalSection I (g i) := by
  apply ((affineBlowUp.exceptionalIdeal I).toModules).unitHomEquiv.injective
  exact congrFun (((affineBlowUp.exceptionalIdeal I).toModules).freeHomEquiv.apply_symm_apply
    (fun k => ((affineBlowUp.exceptionalIdeal I).toModules).unitHomEquiv
      (exceptionalSection I (g k)))) i

include hspan in
theorem generatingMap_epi : Epi (generatingMap I g) := by
  apply epi_of_pullback_cover (fun i => Spec (.of (affineBlowUpAlgebra I (g i))))
    (fun i => affineBlowUp.chart I (g i)) ?_
  · intro i
    let F := pullback (affineBlowUp.chart I (g i))
    have hIso : IsIso (F.map (exceptionalSection I (g i))) := by
      have h := chart_pivot_isIso I (g i)
      change IsIso ((pullbackUnitIso (affineBlowUp.chart I (g i))).inv ≫
        F.map (exceptionalSection I (g i))) at h
      let := h
      exact IsIso.of_isIso_comp_left (pullbackUnitIso (affineBlowUp.chart I (g i))).inv _
    let hE : Epi (F.map (exceptionalSection I (g i))) :=
      @CategoryTheory.IsIso.epi_of_iso _ _ _ _ (F.map (exceptionalSection I (g i))) hIso
    have hw := ((F.map_comp (SheafOfModules.ιFree i) (generatingMap I g)).symm).trans
      (congrArg F.map (generatingMap_ι I g i))
    exact @epi_of_epi_fac _ _ _ _ _ (F.map (SheafOfModules.ιFree i))
      (F.map (generatingMap I g)) (F.map (exceptionalSection I (g i))) hE hw
  · intro x
    obtain ⟨a, ha⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq I
      (Set.range (fun i => (g i : A))) hspan x
    obtain ⟨i, hi⟩ := a.property
    have hmem : (a : A) ∈ I := hi ▸ (g i).property
    have hgi : (⟨a, hmem⟩ : I) = g i := Subtype.ext hi.symm
    change x ∈ (affineBlowUp.chart I ⟨a, hmem⟩).opensRange at ha
    rw [hgi] at ha
    exact ⟨i, ha⟩

def generatingSections : ((affineBlowUp.exceptionalIdeal I).toModules).GeneratingSections where
  I := ι
  s i := ((affineBlowUp.exceptionalIdeal I).toModules).unitHomEquiv (exceptionalSection I (g i))
  epi := generatingMap_epi I g hspan

theorem generatingSections_isFiniteType [Finite ι] : (generatingSections I g hspan).IsFiniteType :=
  ⟨show Finite ι from inferInstance⟩

theorem generatorHom_generatingSections (i : ι) :
    SchemeGeneratingSectionsUnit.generatorHom (generatingSections I g hspan) i =
      exceptionalSection I (g i) := generatingMap_ι I g i
end EnvelopeProperty.Vanishing.NadelNefBigExceptionalGenerators
