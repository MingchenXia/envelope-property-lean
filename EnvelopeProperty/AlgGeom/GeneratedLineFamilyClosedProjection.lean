import EnvelopeProperty.AlgGeom.GeneratedLineFamilyProjectiveEmbedding

/-! # The SAME original simultaneous embedding retains its actual closed first constituent -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.GeneratedLineFamilyClosedProjection
open FiniteRelativeProjectiveProducts GeneratedLineFamilyProjectiveEmbedding
open SchemeLineSectionEvaluation SchemeGeneratingSectionsUnit
variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]

/-- Actual native projectivity and original generators INTERNALLY construct a whole
closed product embedding with a TRUE CLOSED first constituent, original O(1) isomorphisms
and EVERY original generator identity. No closed-projection/class comparison premise. -/
theorem exists_embedding_with_closed_first_projection (p : X ⟶ Spec (.of R)) [IsProjective p] {n : ℕ}
    (L : Fin n → X.Modules) (hL : ∀ j, IsInvertible (L j))
    (G : ∀ j, (L j).GeneratingSections) (hG : ∀ j, (G j).IsFiniteType) :
    ∃ d : Fin (n + 1) → ℕ,
      ∃ f : X ⟶ (product (n + 1) (polynomialFamily R d)).left,
        IsClosedImmersion f ∧ f ≫ (product (n + 1) (polynomialFamily R d)).hom = p ∧
          IsClosedImmersion (f ≫ (projection (polynomialFamily R d) (0 : Fin (n + 1))).left) ∧
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
  have hfirst : f ≫ (projection F (0 : Fin (n + 1))).left = i :=
    congrArg (fun h => h.left) (lift_projection F g (0 : Fin (n + 1)))
  have hf0 : IsClosedImmersion (f ≫ (projection F (0 : Fin (n + 1))).left) := by
    rw [hfirst]
    exact hi
  refine ⟨d, f, hf, (lift F g).w, hf0, fun j => ?_⟩
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

end EnvelopeProperty.GeneratedLineFamilyClosedProjection
