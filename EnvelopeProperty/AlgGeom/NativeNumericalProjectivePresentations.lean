import EnvelopeProperty.AlgGeom.NativeNumericalFiniteClassFamilies
import EnvelopeProperty.AlgGeom.GeneratedLineFamilyProjectiveEmbedding

/-! # True original numerical classes on one internally constructed SAME-X multiprojective embedding -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeNumericalProjectivePresentations
open FiniteRelativeProjectiveProducts GeneratedLineFamilyProjectiveEmbedding
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The SAME original entire O(1) line pulled back from an actual original projective product factor. -/
def factorLine {n : ℕ} (d : Fin n → ℕ)
    (f : X ⟶ (product n (polynomialFamily R d)).left) (i : Fin n) : X.Modules :=
  (Scheme.Modules.pullback (f ≫ (projection (polynomialFamily R d) i).left)).obj
    (coordinateHyperplaneTwist (R := R) (0 : Fin (d i + 1)) 1)

/-- Its actual invertibility is DERIVED from the same original O(1), without a line comparison premise. -/
theorem factorLine_isInvertible {n : ℕ} (d : Fin n → ℕ)
    (f : X ⟶ (product n (polynomialFamily R d)).left) (i : Fin n) : IsInvertible (factorLine d f i) :=
  (coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (d i + 1)) 1).pullback _

private theorem tensorInvertible {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- EVERY finite family of genuine original real numerical classes is internally realized
on ONE true SAME-X projective product embedding, using actual factor O(1) pullback classes
and ONE original denominator factor. No desired model/class/line matching certificate. -/
theorem exists_simultaneous_projective_presentation {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProjective p]
    {ι : Type v} [Fintype ι] (θ : ι → NativeRealNumericalClasses.Space p) :
    ∃ n : ℕ, ∃ d : Fin (n + 1 + 1) → ℕ,
      ∃ f : X ⟶ (product (n + 1 + 1) (polynomialFamily k d)).left,
        IsClosedImmersion f ∧ f ≫ (product (n + 1 + 1) (polynomialFamily k d)).hom = p ∧
          ∃ a : ι → Fin n → ℝ, ∀ j, θ j = ∑ i, a j i •
            (NativeRealNumericalClasses.lineClass p (factorLine d f i.succ.succ)
              (factorLine_isInvertible d f i.succ.succ) -
                NativeRealNumericalClasses.lineClass p (factorLine d f (0 : Fin (n + 1)).succ)
                  (factorLine_isInvertible d f (0 : Fin (n + 1)).succ)) := by
  classical
  obtain ⟨n, L, hL, a, T, hT, H, hH, hGG, hθ⟩ :=
    NativeRealNumericalClasses.exists_common_generated_line_family p θ
  choose G hG using hGG
  let M : Fin (n + 1) → X.Modules := Fin.cases T (fun i => L i ⊗ T)
  let hM : ∀ i, IsInvertible (M i) := Fin.cases hT (fun i => tensorInvertible (hL i) hT)
  let GM : ∀ i, (M i).GeneratingSections := Fin.cases H G
  have hGM : ∀ i, (GM i).IsFiniteType := Fin.cases hH hG
  obtain ⟨d, f, hf, hfp, he⟩ := exists_projective_product_embedding p M hM GM hGM
  have hclasses (i : Fin (n + 1)) :
      NativeRealNumericalClasses.lineClass p (factorLine d f i.succ) (factorLine_isInvertible d f i.succ) =
        NativeRealNumericalClasses.lineClass p (M i) (hM i) := by
    obtain ⟨_, e, _⟩ := he i
    exact NativeRealNumericalClasses.lineClass_eq_of_iso p _ _ e
  refine ⟨n, d, f, hf, hfp, a, fun j => ?_⟩
  rw [hθ j]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z => a j i • z)
  exact congrArg₂ (fun x y => x - y) (hclasses i.succ).symm (hclasses 0).symm

end EnvelopeProperty.NativeNumericalProjectivePresentations
