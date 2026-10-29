import EnvelopeProperty.AlgGeom.GeneratedLineAffineTwistFrames
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveMap
import EnvelopeProperty.AlgGeom.SchemeGeneratorFrameNeighborhoods
import EnvelopeProperty.AlgGeom.SchemeSectionPreservingGluing

/-! # SAME whole original generated-line morphism and ORIGINAL O(1) pullback -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.GeneratedLineProjectiveTwist
open SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation SchemeGeneratedLineCoefficients
open GeneratedLineAffineTwistFrames GeneratedLineProjectiveAffineMap GeneratedLineProjectiveMap
open SchemeGeneratorFrameNeighborhoods GeneratedLineLocalCoefficients SchemeLineSectionFactorization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {L : X.Modules}

/-- ALL actual original nonempty affine opens where a SAME original global generator is an isomorphism. -/
def GeneratorAffineSite (G : L.GeneratingSections) :=
  {a : X.AffineZariskiSite × G.I // Nonempty a.1.1 ∧
    IsIso (pullbackSectionHom a.1.1.ι (generatorHom G a.2))}

private instance generatorSite_affine (G : L.GeneratingSections) (a : GeneratorAffineSite G) :
    IsAffine a.1.1.1.toScheme := a.1.1.2

private instance generatorSite_nonempty (G : L.GeneratingSections) (a : GeneratorAffineSite G) :
    Nonempty a.1.1.1 := a.2.1

private instance generatorSite_integral [IsIntegral X]
    (G : L.GeneratingSections) (a : GeneratorAffineSite G) : IsIntegral a.1.1.1.toScheme :=
  inferInstance

/-- EVERY original point is covered by a genuine SAME-original-generator affine frame. -/
theorem generatorCover (hL : IsInvertible L) (G : L.GeneratingSections) (x : X) :
    ∃ a : GeneratorAffineSite G, x ∈ a.1.1.1 := by
  obtain ⟨U, hx, i, hi⟩ := exists_affine_generator_frame hL G x
  exact ⟨⟨⟨U, i⟩, ⟨⟨⟨x, hx⟩⟩, hi⟩⟩, hx⟩

/-- The actual canonical SAME original generator frame on its actual original affine open. -/
def localFrame (G : L.GeneratingSections) (a : GeneratorAffineSite G) :
    (Scheme.Modules.pullback a.1.1.1.ι).obj L ≅ unitObj a.1.1.1.toScheme :=
  generatorFrame G a.1.1.1 a.1.2 a.2.2

/-- The SAME chosen original generator has literal coefficient one, internally DERIVED. -/
theorem localFrame_coefficient (G : L.GeneratingSections) (a : GeneratorAffineSite G) :
    coefficient (ClosedProjectiveGlobalGeneration.pullback_generatingSections a.1.1.1.ι G)
      (localFrame G a) a.1.2 = 1 :=
  localCoefficient_generatorFrame G a.1.1.1 a.1.2 a.2.2

/-- The SAME original global morphism has its exact actual affine generated-line map in this frame. -/
theorem localMap_eq (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (a : GeneratorAffineSite G) :
    a.1.1.1.ι ≫ projectiveMap p hL G = localMap p G a.1.1 (localFrame G a) :=
  projectiveMap_on_frame p hL G a.1.1 (localFrame G a)

private theorem iteratedSection_isIso {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α : unitObj D ⟶ M)
    (hf : IsIso (pullbackSectionHom f α)) :
    IsIso (pullbackSectionHom g (pullbackSectionHom b α)) := by
  have h : IsIso (pullbackSectionHom g (pullbackSectionHom b α) ≫
      (frameFactorIso g b f hg M).hom) := by
    rw [pullbackSectionHom_factor g b f hg α]
    exact hf
  let := h
  exact IsIso.of_isIso_comp_right _ (frameFactorIso g b f hg M).hom

private theorem iteratedSection_relation {B C D : Scheme.{u}} (g : B ⟶ C) (b : C ⟶ D)
    (f : B ⟶ D) (hg : g ≫ b = f) {M : D.Modules} (α β : unitObj D ⟶ M)
    (r : Γ(B, ⊤)) (hf : pullbackSectionHom f α =
      ModularCurves.unitEndomorphismOfTopSection r ≫ pullbackSectionHom f β) :
    pullbackSectionHom g (pullbackSectionHom b α) =
      ModularCurves.unitEndomorphismOfTopSection r ≫
        pullbackSectionHom g (pullbackSectionHom b β) := by
  apply (cancel_mono (frameFactorIso g b f hg M).hom).mp
  rw [pullbackSectionHom_factor, Category.assoc, pullbackSectionHom_factor]
  exact hf

private theorem relation_of_frame {B : Scheme.{u}} {M : B.Modules}
    (α β : unitObj B ⟶ M) (e : M ≅ unitObj B) (r : Γ(B, ⊤))
    (hα : α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r)
    (hβ : β ≫ e.hom = 𝟙 _) :
    α = ModularCurves.unitEndomorphismOfTopSection r ≫ β := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, hα, hβ, Category.comp_id]

variable [IsIntegral X]

private theorem localAffinePivot_isIso (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) (a : GeneratorAffineSite G) :
    IsIso (pullbackSectionHom (localMap p G a.1.1 (localFrame G a))
      (coordinateSectionHom (R := R) G k a.1.2)) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections a.1.1.1.ι G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact pulledCoordinateSection_isIso (a.1.1.1.ι ≫ p) H
    (localFrame G a) a.1.2 (localFrame_coefficient G a) k

private theorem localAffine_relation (p : X ⟶ Spec (.of R)) (G : L.GeneratingSections)
    [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom (localMap p G a.1.1 (localFrame G a))
      (coordinateSectionHom (R := R) G k j) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom (localMap p G a.1.1 (localFrame G a))
          (coordinateSectionHom (R := R) G k a.1.2) := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections a.1.1.1.ι G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact pulledCoordinateSection_relation (a.1.1.1.ι ≫ p) H
    (localFrame G a) a.1.2 (localFrame_coefficient G a) k j

/-- The SAME actual globally pulled original pivot section is a true isomorphism on its actual affine chart. -/
theorem localPulledPivot_isIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) :
    IsIso (pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2))) :=
  iteratedSection_isIso a.1.1.1.ι (projectiveMap p hL G)
    (localMap p G a.1.1 (localFrame G a)) (localMap_eq p hL G a)
    (coordinateSectionHom (R := R) G k a.1.2) (localAffinePivot_isIso p G k a)

/-- EVERY SAME original coordinate section retains its original generator scalar relation on the whole chart. -/
theorem localPulled_relation (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j)) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom a.1.1.1.ι
          (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)) :=
  iteratedSection_relation a.1.1.1.ι (projectiveMap p hL G)
    (localMap p G a.1.1 (localFrame G a)) (localMap_eq p hL G a)
    (coordinateSectionHom (R := R) G k j) (coordinateSectionHom (R := R) G k a.1.2)
    (localCoefficient G a.1.1.1 (localFrame G a) j) (localAffine_relation p G k a j)

omit [IsIntegral X] in
private theorem localOriginal_relation (G : L.GeneratingSections) (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι (generatorHom G j) =
      ModularCurves.unitEndomorphismOfTopSection (localCoefficient G a.1.1.1 (localFrame G a) j) ≫
        pullbackSectionHom a.1.1.1.ι (generatorHom G a.1.2) :=
  relation_of_frame _ _ (localFrame G a) _
    (localCoefficient_scalar G a.1.1.1 (localFrame G a) j)
    (generatorFrame_section G a.1.1.1 a.1.2 a.2.2)

/-- The actual local O(1) comparison uses the SAME original pulled pivot and SAME original generator. -/
def localTwistIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) :
    (Scheme.Modules.pullback a.1.1.1.ι).obj
      ((Scheme.Modules.pullback (projectiveMap p hL G)).obj
        (coordinateHyperplaneTwist (R := R) k 1)) ≅
      (Scheme.Modules.pullback a.1.1.1.ι).obj L :=
  letI := localPulledPivot_isIso p hL G k a
  letI := a.2.2
  (asIso (pullbackSectionHom a.1.1.1.ι
    (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k a.1.2)))).symm ≪≫
    asIso (pullbackSectionHom a.1.1.1.ι (generatorHom G a.1.2))

private theorem pivotIso_preserves_relation {C : Type*} [Category C] {A B D : C}
    (α α₀ : A ⟶ B) (β β₀ : A ⟶ D) (s : A ⟶ A)
    (hα₀ : IsIso α₀) (hβ₀ : IsIso β₀) (hα : α = s ≫ α₀) (hβ : β = s ≫ β₀) :
    α ≫ ((asIso α₀).symm ≪≫ asIso β₀).hom = β := by
  let := hα₀
  let := hβ₀
  rw [hα, hβ]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  exact congrArg (fun t => s ≫ t) ((asIso α₀).hom_inv_id_assoc β₀)

/-- EVERY SAME original global coordinate section maps to its SAME original
global generator on each ENTIRE original affine cover neighborhood. -/
theorem localTwistIso_sectionHom (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) (j : G.I) :
    pullbackSectionHom a.1.1.1.ι
      (pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j)) ≫
        (localTwistIso p hL G k a).hom =
      pullbackSectionHom a.1.1.1.ι (generatorHom G j) :=
  pivotIso_preserves_relation _ _ _ _ _ (localPulledPivot_isIso p hL G k a) a.2.2
    (localPulled_relation p hL G k a j) (localOriginal_relation G a j)

/-- The SAME constructed WHOLE original projective morphism pulls ORIGINAL O(1)
back to the SAME ORIGINAL generated line. All original local data are internally derived. -/
def projectiveTwistIso (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) :
    (Scheme.Modules.pullback (projectiveMap p hL G)).obj
      (coordinateHyperplaneTwist (R := R) k 1) ≅ L :=
  SchemeSectionPreservingGluing.glueOfSections
    (M := (Scheme.Modules.pullback (projectiveMap p hL G)).obj
      (coordinateHyperplaneTwist (R := R) k 1)) (N := L)
    (fun a : GeneratorAffineSite G => a.1.1.1) (generatorCover hL G)
    (localTwistIso p hL G k)
    (fun j => pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j))
    (generatorHom G) (fun a => a.1.2) (fun a => a.2.2) (localTwistIso_sectionHom p hL G k)

/-- The WHOLE original O(1) comparison retains EVERY SAME actual local original comparison. -/
theorem projectiveTwistIso_restrict (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1))
    (a : GeneratorAffineSite G) :
    (SheafOfModules.overFunctor X.ringCatSheaf a.1.1.1).mapIso
      (projectiveTwistIso p hL G k) =
        SchemeSectionPreservingGluing.overIsoOfPullback a.1.1.1 (localTwistIso p hL G k a) :=
  SchemeSectionPreservingGluing.glueOfSections_restrict
    (fun a : GeneratorAffineSite G => a.1.1.1) (generatorCover hL G)
    (localTwistIso p hL G k)
    (fun j => pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j))
    (generatorHom G) (fun a => a.1.2) (fun a => a.2.2) (localTwistIso_sectionHom p hL G k) a

/-- EVERY SAME original projective coordinate section maps to the SAME original
global generator on the ENTIRE ORIGINAL scheme. -/
theorem projectiveTwistIso_sectionHom (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (k : Fin (Fintype.card G.I + 1)) (j : G.I) :
    pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j) ≫
      (projectiveTwistIso p hL G k).hom = generatorHom G j :=
  SchemeSectionPreservingGluing.glueOfSections_section
    (fun a : GeneratorAffineSite G => a.1.1.1) (generatorCover hL G)
    (localTwistIso p hL G k)
    (fun j => pullbackSectionHom (projectiveMap p hL G) (coordinateSectionHom (R := R) G k j))
    (generatorHom G) (fun a => a.1.2) (fun a => a.2.2) (localTwistIso_sectionHom p hL G k) j

/-- Actual finite generation INTERNALLY constructs an original projective morphism,
actual original O(1) isomorphism and ALL literal original coordinate/generator identities. -/
theorem exists_projective_morphism (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) (hG : G.IsFiniteType) :
    ∃ (n : ℕ) (f : X ⟶ Alterations.projectiveSpace R n)
      (c : G.I → Fin (n + 1))
      (e : (Scheme.Modules.pullback f).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≅ L),
      f ≫ Alterations.projectiveSpaceStructure R n = p ∧ ∀ j,
        pullbackSectionHom f
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n + 1)) 1
            (MvPolynomial.X (c j)) (MvPolynomial.isHomogeneous_X R (c j))) ≫ e.hom =
          generatorHom G j := by
  let := hG
  let : Fintype G.I := Fintype.ofFinite G.I
  exact ⟨Fintype.card G.I, projectiveMap p hL G, generatorCoordinate G,
    projectiveTwistIso p hL G 0, projectiveMap_structure p hL G,
    projectiveTwistIso_sectionHom p hL G 0⟩

end EnvelopeProperty.GeneratedLineProjectiveTwist
