import EnvelopeProperty.Vanishing.RelativeArithmeticJointModel
import EnvelopeProperty.Vanishing.RelativeArithmeticProjectiveModel

/-! # The original relative projective embedding produces its arithmetic model

All arithmetic affine-base and ambient data are selected internally from
the original arbitrary finite-type algebra.  The entire original closed
embedding is then descended with its original total smooth dimension.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticOriginalProjectiveModel
open ProjBerk Alterations.StableModification.Limits

/-- The original relative projective geometry itself constructs its arithmetic
base, whole smooth source model, and original closed embedding at one actual
finite stage.  There is no domain assumption on the original affine algebra. -/
theorem exists_original_projective_stage
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (g : X ⟶ Spec (.of R))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (d : ℕ) (j : X ⟶ NativeProjectiveScheme R d) [hjClosed : IsClosedImmersion j]
    (hj : j ≫ nativeStructureMap = g) :
    ∃ (A : Subalgebra ℤ k), Algebra.Smooth ℤ A ∧ Algebra.FiniteType ℤ A ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
        Algebra.FinitePresentation A B ∧
        ∃ e : k ⊗[A] B ≃ₐ[k] R,
          let r := RelativeArithmeticJointModel.projectiveAmbient_fixedModel
            e (show Function.Injective (algebraMap A k) from Subtype.val_injective) d
          ∃ (l : (FGSubalgebra A (⊤ : Subalgebra A k))ᵒᵖ)
            (h : l ⟶ op (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)))
            (m : Model ((fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec)
              (fgSpecCone (⊤ : Subalgebra A k))
              (f ≫ (ArithmeticFixedSmoothModel.topScalarIso A k).hom) l)
            (ι : m.Y ⟶ (r.baseChange h).Y),
            m.IsFP ∧ SmoothOfRelativeDimension n m.fY ∧ IsClosedImmersion ι ∧
              ι ≫ (r.baseChange h).fY = m.fY ∧
                m.g ≫ ι = j ≫ (r.baseChange h).g := by
  obtain ⟨A, hSmooth, hFT, _, B, hB, hAB, hFP, e, _⟩ :=
    RelativeArithmeticBaseModel.exists_original_base_model (k := k) (R := R) ∅
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Algebra.FiniteType ℤ A := hFT
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let : Algebra.FinitePresentation A B := hFP
  let : IsProper g := (show IsProjectiveFactorization g from
    ⟨d, j, hjClosed, hj⟩).isProper
  let : QuasiCompact f := by
    rw [← hg]
    infer_instance
  let E := ArithmeticFixedSmoothModel.topScalarIso A k
  let f₀ := f ≫ E.hom
  let fP := (nativeStructureMap (R := R) (n := d) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R))) ≫ E.hom
  let : SmoothOfRelativeDimension n f₀ := by
    simpa only [Nat.add_zero] using
      (smoothOfRelativeDimension_comp (n := n) (m := 0) f E.hom)
  let : QuasiCompact f₀ := inferInstance
  let : QuasiSeparated f₀ := inferInstance
  let r := RelativeArithmeticJointModel.projectiveAmbient_fixedModel
    e (show Function.Injective (algebraMap A k) from Subtype.val_injective) d
  have hr : r.IsFP := RelativeArithmeticJointModel.projectiveAmbient_fixedModel_isFP
    e Subtype.val_injective d
  have hj₀ : j ≫ fP = f₀ := by
    dsimp only [fP, f₀]
    simp only [← Category.assoc, hj, hg]
  obtain ⟨l, h, m, ι, hm, hn, hι, hbase, horiginal⟩ :=
    RelativeArithmeticProjectiveModel.exists_smooth_closed_model fP f₀ n r hr j hj₀
  exact ⟨A, hSmooth, hFT, B, hB, hAB, hFP, e,
    l, h, m, ι, hm, hn, hι, hbase, horiginal⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticOriginalProjectiveModel
