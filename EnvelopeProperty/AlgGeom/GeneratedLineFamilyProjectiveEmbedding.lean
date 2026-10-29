import EnvelopeProperty.AlgGeom.FiniteRelativeProjectiveProducts
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist

/-! # Actual original finite generated-line families on ONE genuine whole projective product embedding -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.GeneratedLineFamilyProjectiveEmbedding
open FiniteRelativeProjectiveProducts
open SchemeLineSectionEvaluation SchemeGeneratingSectionsUnit
variable (R : Type u) [CommRing R]

/-- The SAME actual original finite family of polynomial projective spaces over the SAME coefficient ring. -/
def polynomialFamily {n : ℕ} (d : Fin n → ℕ) (j : Fin n) : Over (Spec (.of R)) :=
  Over.mk (Alterations.projectiveSpaceStructure R (d j))

/-- Every literal original polynomial factor internally has its finite projective factorization. -/
theorem polynomialFamily_isProjectiveFactorization {n : ℕ} (d : Fin n → ℕ) (j : Fin n) :
    IsProjectiveFactorization (polynomialFamily R d j).hom := by
  change IsProjectiveFactorization (Alterations.projectiveSpaceStructure R (d j))
  apply (ProjectiveBlowupSequence.isProjectiveOver_iff _).mp
  exact ⟨d j, 𝟙 _, inferInstance, Category.id_comp _⟩

variable {R} {X : Scheme.{u}} [IsIntegral X]

/-- ANY actual finite original generated-line family is simultaneously realized on one
DERIVED actual closed projective product embedding, with WHOLE O(1) line isomorphisms
and EVERY literal original coordinate-section/generator equality. -/
theorem exists_projective_product_embedding (p : X ⟶ Spec (.of R)) [IsProjective p] {n : ℕ}
    (L : Fin n → X.Modules) (hL : ∀ j, IsInvertible (L j))
    (G : ∀ j, (L j).GeneratingSections) (hG : ∀ j, (G j).IsFiniteType) :
    ∃ d : Fin (n + 1) → ℕ,
      ∃ f : X ⟶ (product (n + 1) (polynomialFamily R d)).left,
        IsClosedImmersion f ∧ f ≫ (product (n + 1) (polynomialFamily R d)).hom = p ∧
          ∀ j : Fin n,
            ∃ c : (G j).I → Fin (d j.succ + 1),
              ∃ e : (Scheme.Modules.pullback (f ≫ (projection (polynomialFamily R d) j.succ).left)).obj
                (coordinateHyperplaneTwist (R := R) (0 : Fin (d j.succ + 1)) 1) ≅ L j,
                ∀ a, pullbackSectionHom (f ≫ (projection (polynomialFamily R d) j.succ).left)
                  (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (d j.succ + 1)) 1
                    (MvPolynomial.X (c a)) (MvPolynomial.isHomogeneous_X R (c a))) ≫ e.hom =
                      generatorHom (G j) a := by
  choose m q c e hq using fun j => GeneratedLineProjectiveTwist.exists_projective_morphism p
    (hL j) (G j) (hG j)
  obtain ⟨m₀, i, hi, hip⟩ := (ProjectiveBlowupSequence.isProjectiveOver_iff p).mpr
    (ProjectiveFactorizationRingIso.of_isProjective p)
  let d : Fin (n + 1) → ℕ := Fin.cases m₀ m
  let F := polynomialFamily R d
  let g : ∀ j : Fin (n + 1), Over.mk p ⟶ F j := Fin.cases (Over.homMk i hip)
    (fun j => Over.homMk (q j) (hq j).1)
  let f := (lift F g).left
  have hf : IsClosedImmersion f := by
    apply lift_isClosedImmersion F (polynomialFamily_isProjectiveFactorization R d) g
    exact ⟨0, hi⟩
  refine ⟨d, f, hf, (lift F g).w, fun j => ?_⟩
  have hj : f ≫ (projection F j.succ).left = q j := by
    exact congrArg (fun h => h.left) (lift_projection F g j.succ)
  change ∃ c' : (G j).I → Fin (m j + 1),
    ∃ e' : (Scheme.Modules.pullback (f ≫ (projection F j.succ).left)).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (m j + 1)) 1) ≅ L j,
      ∀ a, pullbackSectionHom (f ≫ (projection F j.succ).left)
        (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m j + 1)) 1
          (MvPolynomial.X (c' a)) (MvPolynomial.isHomogeneous_X R (c' a))) ≫ e'.hom = generatorHom (G j) a
  rw [hj]
  exact ⟨c j, e j, (hq j).2⟩

end EnvelopeProperty.GeneratedLineFamilyProjectiveEmbedding
