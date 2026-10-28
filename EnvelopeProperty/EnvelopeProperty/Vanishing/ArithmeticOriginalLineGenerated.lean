import EnvelopeProperty.Vanishing.ArithmeticOriginalLineTuple
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist

/-! # Actual original generated lines over a domain base

The original scheme is arbitrary.  Genuine generator frames and the transported
universal tuple comparisons construct the original O(1) pullback isomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineGenerated
open SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation SchemeGeneratedLineCoefficients
open GeneratedLineAffineTwistFrames GeneratedLineProjectiveAffineMap GeneratedLineProjectiveMap
open SchemeGeneratorFrameNeighborhoods GeneratedLineLocalCoefficients SchemeLineSectionFactorization
open GeneratedLineProjectiveTwist
open DeJongAlterations.Geometry.FiniteProjective

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] [IsDomain R] {X : Scheme.{u}} {L : X.Modules}

private instance generatorSite_affine (G : L.GeneratingSections) (a : GeneratorAffineSite G) :
    IsAffine a.1.1.1.toScheme := a.1.1.2

private theorem affinePivot_isIso {Y : Scheme.{u}} [IsAffine Y] {M : Y.Modules}
    (p : Y ⟶ Spec (.of R)) (G : M.GeneratingSections) [Fintype G.I]
    (e : M ≅ unitObj Y) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) :
    IsIso (pullbackSectionHom (affineMap p G e) (coordinateSectionHom (R := R) G k i)) := by
  let a := paddedCoefficients (coefficient G e)
  let ha := span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e)
  exact isIso_pullbackSectionHom_factor Y.isoSpec.hom
    (affineTupleMap (baseCoefficients p) a ha) (affineMap p G e) rfl _
    (ArithmeticOriginalLineTuple.pulledPivot_isIso (baseCoefficients p) a ha
      (generatorCoordinate G i) ((paddedCoefficient_generator G e i).trans hi) k)

private theorem isoSpec_coefficient {Y : Scheme.{u}} [IsAffine Y] (c : Γ(Y, ⊤)) :
    Y.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso (.of Γ(Y, ⊤))).inv.hom c) = c := by
  change Y.toSpecΓ.appTop.hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom c) = c
  rw [Scheme.toSpecΓ_appTop]
  exact (Scheme.ΓSpecIso Γ(Y, ⊤)).inv_hom_id_apply c

private theorem affineCoordinate_relation {Y : Scheme.{u}} [IsAffine Y] {M : Y.Modules}
    (p : Y ⟶ Spec (.of R)) (G : M.GeneratingSections) [Fintype G.I]
    (e : M ≅ unitObj Y) (i : G.I) (hi : coefficient G e i = 1)
    (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    pullbackSectionHom (affineMap p G e) (coordinateSectionHom (R := R) G k j) =
      ModularCurves.unitEndomorphismOfTopSection (coefficient G e j) ≫
        pullbackSectionHom (affineMap p G e) (coordinateSectionHom (R := R) G k i) := by
  let a := paddedCoefficients (coefficient G e)
  let ha := span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e)
  have h := factor_scalar_relation Y.isoSpec.hom
    (affineTupleMap (baseCoefficients p) a ha) (affineMap p G e) rfl _ _ _
    (ArithmeticOriginalLineTuple.pulledCoordinate_relation (baseCoefficients p) a ha
      (generatorCoordinate G i) ((paddedCoefficient_generator G e i).trans hi) k
      (generatorCoordinate G j))
  rw [isoSpec_coefficient] at h
  exact h.trans (congrArg (fun c => ModularCurves.unitEndomorphismOfTopSection c ≫
    pullbackSectionHom (affineMap p G e) (coordinateSectionHom (R := R) G k i))
      (paddedCoefficient_generator G e j))

private theorem localPivot_isIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) :
    IsIso (pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2))) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections a.1.1.1.ι G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  have h := affinePivot_isIso (a.1.1.1.ι ≫ p) H (localFrame G a) a.1.2
    (localFrame_coefficient G a) k
  have hh : IsIso (pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)) ≫
        (frameFactorIso a.1.1.1.ι (projectiveMap p hL G)
          (localMap p G a.1.1 (localFrame G a)) (localMap_eq p hL G a)
          (coordinateHyperplaneTwist (R := R) k 1)).hom) := by
    rw [pullbackSectionHom_factor]
    exact h
  let := hh
  exact IsIso.of_isIso_comp_right _
    (frameFactorIso a.1.1.1.ι (projectiveMap p hL G)
      (localMap p G a.1.1 (localFrame G a)) (localMap_eq p hL G a)
      (coordinateHyperplaneTwist (R := R) k 1)).hom

private theorem localCoordinate_relation (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j)) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom a.1.1.1.ι
          (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections a.1.1.1.ι G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  apply (cancel_mono (frameFactorIso a.1.1.1.ι (projectiveMap p hL G)
    (localMap p G a.1.1 (localFrame G a)) (localMap_eq p hL G a)
    (coordinateHyperplaneTwist (R := R) k 1)).hom).mp
  rw [pullbackSectionHom_factor, Category.assoc, pullbackSectionHom_factor]
  exact affineCoordinate_relation (a.1.1.1.ι ≫ p) H
    (localFrame G a) a.1.2 (localFrame_coefficient G a) k j

private theorem original_relation (G : L.GeneratingSections) (a : GeneratorAffineSite G)
    (j : G.I) :
    pullbackSectionHom a.1.1.1.ι (generatorHom G j) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom a.1.1.1.ι (generatorHom G a.1.2) := by
  apply (cancel_mono (localFrame G a).hom).mp
  have hp : pullbackSectionHom a.1.1.1.ι (generatorHom G a.1.2) ≫
      (localFrame G a).hom = 𝟙 _ := generatorFrame_section G a.1.1.1 a.1.2 a.2.2
  rw [Category.assoc, localCoefficient_scalar, hp, Category.comp_id]

private def localComparison (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) :
    (Scheme.Modules.pullback a.1.1.1.ι).obj
      ((Scheme.Modules.pullback (projectiveMap p hL G)).obj
        (coordinateHyperplaneTwist (R := R) k 1)) ≅
      (Scheme.Modules.pullback a.1.1.1.ι).obj L :=
  letI := localPivot_isIso p hL G k a
  letI := a.2.2
  (asIso (pullbackSectionHom a.1.1.1.ι
    (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)))).symm ≪≫
    asIso (pullbackSectionHom a.1.1.1.ι (generatorHom G a.1.2))

private theorem localComparison_sections (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j)) ≫
        (localComparison p hL G k a).hom =
      pullbackSectionHom a.1.1.1.ι (generatorHom G j) := by
  let := localPivot_isIso p hL G k a
  let := a.2.2
  rw [localCoordinate_relation, original_relation G a j, localComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  exact congrArg (fun t =>
    ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫ t)
      ((asIso (pullbackSectionHom a.1.1.1.ι
        (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)))).hom_inv_id_assoc _)

/-- The same actual original generated-line morphism pulls original O(1) back
to the same original line on an arbitrary original scheme over a domain. -/
def projectiveTwistIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) :
    (Scheme.Modules.pullback (projectiveMap p hL G)).obj
      (coordinateHyperplaneTwist (R := R) k 1) ≅ L :=
  SchemeSectionPreservingGluing.glueOfSections
    (M := (Scheme.Modules.pullback (projectiveMap p hL G)).obj
      (coordinateHyperplaneTwist (R := R) k 1)) (N := L)
    (fun a : GeneratorAffineSite G => a.1.1.1) (generatorCover hL G)
    (localComparison p hL G k)
    (fun j => pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j))
    (generatorHom G) (fun a => a.1.2) (fun a => a.2.2) (localComparison_sections p hL G k)

/-- The constructed whole comparison retains every same original generating
section, including its original padded coordinate index. -/
theorem projectiveTwistIso_sectionHom (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j) ≫
      (projectiveTwistIso p hL G k).hom = generatorHom G j :=
  SchemeSectionPreservingGluing.glueOfSections_section
    (fun a : GeneratorAffineSite G => a.1.1.1) (generatorCover hL G)
    (localComparison p hL G k)
    (fun j => pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j))
    (generatorHom G) (fun a => a.1.2) (fun a => a.2.2) (localComparison_sections p hL G k) j

/-- Finite original generators construct an actual original projective morphism
and O(1) comparison, with no integrality hypothesis on the original scheme. -/
theorem exists_projective_morphism (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) (hG : G.IsFiniteType) :
    ∃ (n : ℕ) (f : X ⟶ DeJongAlterations.projectiveSpace R n)
      (_e : (Scheme.Modules.pullback f).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≅ L),
      f ≫ DeJongAlterations.projectiveSpaceStructure R n = p := by
  let := hG
  let : Fintype G.I := Fintype.ofFinite G.I
  exact ⟨Fintype.card G.I, projectiveMap p hL G, projectiveTwistIso p hL G 0,
    projectiveMap_structure p hL G⟩

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineGenerated
