import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonOpenTransfer

/-! # The same original lifted-form scalar relations under canonical open pullback -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
  DeJongAlterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem scalarRelation_of_common_right
    {C : Type u} [Category C] {A B D : C}
    {b b' : A ⟶ B} {a : A ⟶ A} {t : B ⟶ D} [Mono t]
    {γ γ' : A ⟶ D} (hb : b ≫ t = γ) (hb' : b' ≫ t = γ')
    (hγ : γ = a ≫ γ') : b = a ≫ b' := by
  apply (cancel_mono t).mp
  exact hb.trans (hγ.trans ((congrArg (fun q : A ⟶ D => a ≫ q) hb'.symm).trans
    (Category.assoc a b' t).symm))

/-- A scalar relation between the same original composite lifts transports to
the pullbacks of the same old lifts. The common canonical comparison and its
monicity are derived from the two actual original-form naturality identities. -/
theorem liftedFormSection_open_scalarRelation
    {R : Type u} [hR : CommRing R] {n : ℕ} {X Z W : Scheme.{u}}
    (μ : Z ⟶ X) (c : W ⟶ Z) [hcOpen : IsOpenImmersion c]
    (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F G : MvPolynomial (Fin (n+1)) R)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hFJ : F ∈ J.toIdeal) (hGJ : G ∈ J.toIdeal) (r : Γ(W, ⊤))
    (h : liftedFormSection (R := R) (n := n) (X := X) (Z := W)
        (c ≫ μ) j J d F hF hFJ =
      ModularCurves.unitEndomorphismOfTopSection r ≫
        liftedFormSection (R := R) (n := n) (X := X) (Z := W)
          (c ≫ μ) j J d G hG hGJ) :
    SchemeLineSectionEvaluation.pullbackSectionHom c
        (liftedFormSection (R := R) (n := n) (X := X) (Z := Z) μ j J d F hF hFJ) =
      ModularCurves.unitEndomorphismOfTopSection r ≫
        SchemeLineSectionEvaluation.pullbackSectionHom c
          (liftedFormSection (R := R) (n := n) (X := X) (Z := Z) μ j J d G hG hGJ) := by
  exact scalarRelation_of_common_right
    (@liftedFormSection_openNaturality R hR n X Z W μ c hcOpen j J d F hF hFJ)
    (@liftedFormSection_openNaturality R hR n X Z W μ c hcOpen j J d G hG hGJ) h

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
