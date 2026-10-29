import EnvelopeProperty.AlgGeom.NativeNumericalProjectivePresentations
import EnvelopeProperty.AlgGeom.GeneratedLineFamilyClosedProjection
import EnvelopeProperty.AlgGeom.FiniteProjectiveNativeFieldModels

/-! # SAME original finite numerical classes and genuine homogeneous models on ENTIRE native K(X) -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial TopologicalSpace
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeNumericalWholeFieldPresentations
open FiniteRelativeProjectiveProducts GeneratedLineFamilyProjectiveEmbedding
open NativeNumericalProjectivePresentations
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem tensorInvertible {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- ALL original finite numerical classes, SAME X/product embedding, original O(1) classes,
and a TRUE model over ENTIRE SAME native K(X) are produced internally. All original factor
dimensions and projective-ratio coordinates are retained; no desired comparison input. -/
theorem exists_simultaneous_whole_field_presentation {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    {ι : Type v} [Fintype ι] (θ : ι → NativeRealNumericalClasses.Space p) :
    letI := p.stalkAlgebra (genericPoint X)
    ∃ n : ℕ, ∃ d : Fin (n + 1 + 1) → ℕ,
      ∃ f : X ⟶ (product (n + 1 + 1) (polynomialFamily k d)).left,
        IsClosedImmersion f ∧ f ≫ (product (n + 1 + 1) (polynomialFamily k d)).hom = p ∧
          IsClosedImmersion (f ≫ (projection (polynomialFamily k d) (0 : Fin (n + 1 + 1))).left) ∧
            ∃ P : MultiModel k X.functionField (n + 1 + 1), P.M = d ∧
              HEq P.coord (FiniteProjectiveNativeFieldModels.coordinate
                (fun j => f ≫ (projection (polynomialFamily k d) j).left)) ∧
              ∃ a : ι → Fin n → ℝ, ∀ j, θ j = ∑ i, a j i •
                (NativeRealNumericalClasses.lineClass p (factorLine d f i.succ.succ)
                  (factorLine_isInvertible d f i.succ.succ) -
                    NativeRealNumericalClasses.lineClass p (factorLine d f (0 : Fin (n + 1)).succ)
                      (factorLine_isInvertible d f (0 : Fin (n + 1)).succ)) := by
  classical
  let := p.stalkAlgebra (genericPoint X)
  obtain ⟨n, L, hL, a, T, hT, H, hH, hGG, hθ⟩ :=
    NativeRealNumericalClasses.exists_common_generated_line_family p θ
  choose G hG using hGG
  let M : Fin (n + 1) → X.Modules := Fin.cases T (fun i => L i ⊗ T)
  let hM : ∀ i, IsInvertible (M i) := Fin.cases hT (fun i => tensorInvertible (hL i) hT)
  let GM : ∀ i, (M i).GeneratingSections := Fin.cases H G
  have hGM : ∀ i, (GM i).IsFiniteType := Fin.cases hH hG
  obtain ⟨d, f, hf, hfp, h0, he⟩ :=
    GeneratedLineFamilyClosedProjection.exists_embedding_with_closed_first_projection p M hM GM hGM
  let q := fun j : Fin (n + 1 + 1) => f ≫ (projection (polynomialFamily k d) j).left
  have hq (j : Fin (n + 1 + 1)) : q j ≫ Alterations.projectiveSpaceStructure k (d j) = p := by
    change (f ≫ (projection (polynomialFamily k d) j).left) ≫ (polynomialFamily k d j).hom = p
    rw [Category.assoc, (projection (polynomialFamily k d) j).w]
    exact hfp
  let P := @FiniteProjectiveNativeFieldModels.model k _ X _ (n + 1) d q p hq h0
  have hclasses (i : Fin (n + 1)) :
      NativeRealNumericalClasses.lineClass p (factorLine d f i.succ) (factorLine_isInvertible d f i.succ) =
        NativeRealNumericalClasses.lineClass p (M i) (hM i) := by
    obtain ⟨_, e, _⟩ := he i
    exact NativeRealNumericalClasses.lineClass_eq_of_iso p _ _ e
  refine ⟨n, d, f, hf, hfp, h0, P, rfl, HEq.rfl, a, fun j => ?_⟩
  rw [hθ j]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z => a j i • z)
  exact congrArg₂ (fun x y => x - y) (hclasses i.succ).symm (hclasses 0).symm

end EnvelopeProperty.NativeNumericalWholeFieldPresentations
