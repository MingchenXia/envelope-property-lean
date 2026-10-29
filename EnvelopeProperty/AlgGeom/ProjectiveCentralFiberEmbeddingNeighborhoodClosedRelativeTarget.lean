import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients

/-! # The actual native projective target over an original affine base open -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeTarget
open GeneratedLineProjectiveAffineMap
open Alterations.Geometry.BlowupProjectiveEmbedding
variable {R : Type u} [CommRing R]

private theorem spectrumCoefficient_eq (B : (Spec (CommRingCat.of R)).Opens)
    [IsAffine B.toScheme] :
    Spec.map (CommRingCat.ofHom (baseCoefficients B.ι)) = B.toScheme.isoSpec.inv ≫ B.ι := by
  have h := congrArg (fun f => B.toScheme.isoSpec.inv ≫ f) (baseCoefficients_structure B.ι)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h

private theorem coefficientMap_range (B : (Spec (CommRingCat.of R)).Opens)
    [IsAffine B.toScheme] (n : ℕ) :
    Set.range (projectiveCoefficientMap (baseCoefficients B.ι) n) ⊆
      Set.range (Alterations.projectiveSpaceStructure R n ⁻¹ᵁ B).ι := by
  let C := projectiveCoefficientMap (baseCoefficients B.ι) n
  let q := Alterations.projectiveSpaceStructure R n
  let qB := Alterations.projectiveSpaceStructure Γ(B.toScheme, ⊤) n
  let V := q ⁻¹ᵁ B
  have ht : C ≫ q = qB ≫ (B.toScheme.isoSpec.inv ≫ B.ι) :=
    (projectiveCoefficientMap_structure (baseCoefficients B.ι) n).trans
      (congrArg (fun f => qB ≫ f) (spectrumCoefficient_eq B))
  rintro _ ⟨z, rfl⟩
  rw [V.range_ι]
  change q (C z) ∈ B
  have hpoint := congrArg (fun f => f z) ht
  change q (C z) = B.ι (B.toScheme.isoSpec.inv (qB z)) at hpoint
  rw [hpoint]
  exact (B.toScheme.isoSpec.inv (qB z)).property

/-- The ACTUAL native coefficient map from projective space over the actual
section ring of the original affine base open factors through the original
target open. Its whole range condition is internally proved. -/
def coefficientOpenFactor (B : (Spec (CommRingCat.of R)).Opens)
    [IsAffine B.toScheme] (n : ℕ) :
    Alterations.projectiveSpace Γ(B.toScheme, ⊤) n ⟶
      (Alterations.projectiveSpaceStructure R n ⁻¹ᵁ B).toScheme :=
  IsOpenImmersion.lift (Alterations.projectiveSpaceStructure R n ⁻¹ᵁ B).ι
    (projectiveCoefficientMap (baseCoefficients B.ι) n) (coefficientMap_range B n)

/-- The ENTIRE actual factor retains the SAME original coefficient morphism. -/
theorem coefficientOpenFactor_inclusion (B : (Spec (CommRingCat.of R)).Opens)
    [IsAffine B.toScheme] (n : ℕ) :
    coefficientOpenFactor B n ≫ (Alterations.projectiveSpaceStructure R n ⁻¹ᵁ B).ι =
      projectiveCoefficientMap (baseCoefficients B.ι) n :=
  IsOpenImmersion.lift_fac _ _ _

/-- The ACTUAL internally constructed projective coefficient factor is
separated, without an incoming factor or separatedness certificate. -/
theorem coefficientOpenFactor_isSeparated (B : (Spec (CommRingCat.of R)).Opens)
    [IsAffine B.toScheme] (n : ℕ) : IsSeparated (coefficientOpenFactor B n) := by
  let C := projectiveCoefficientMap (baseCoefficients B.ι) n
  let q := Alterations.projectiveSpaceStructure R n
  let : IsSeparated (C ≫ q) :=
    (projectiveCoefficientMap_structure (baseCoefficients B.ι) n).symm ▸
      (inferInstance : IsSeparated (Alterations.projectiveSpaceStructure Γ(B.toScheme, ⊤) n ≫
        Spec.map (CommRingCat.ofHom (baseCoefficients B.ι))))
  let : IsSeparated C := IsSeparated.of_comp C q
  let V := q ⁻¹ᵁ B
  let : IsSeparated (coefficientOpenFactor B n ≫ V.ι) :=
    (coefficientOpenFactor_inclusion B n).symm ▸ (inferInstance : IsSeparated C)
  exact IsSeparated.of_comp (coefficientOpenFactor B n) V.ι

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeTarget
