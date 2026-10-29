import EnvelopeProperty.AlgGeom.SymmetricPolynomialBasisComparison
import EnvelopeProperty.AlgGeom.PolynomialProjectiveCoefficientIso
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Original native projectivity from genuine finite polynomial factorizations -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
noncomputable section
universe u
namespace EnvelopeProperty.NativeProjectivityFromPolynomialFactorization
attribute [local instance] MvPolynomial.gradedAlgebra

private def freeSheaf (Y : Scheme.{u}) (n : ℕ) : Y.Modules :=
  SheafOfModules.free (ULift.{u} (Fin (n + 1)))

private instance freeSheaf_quasicoherent (Y : Scheme.{u}) (n : ℕ) :
    (freeSheaf Y n).IsQuasicoherent := by
  unfold freeSheaf
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private instance freeSheaf_finiteType (Y : Scheme.{u}) (n : ℕ) :
    (freeSheaf Y n).IsFiniteType := by
  unfold freeSheaf
  let G := SheafOfModules.free.generatingSections
    (R := Y.ringCatSheaf) (ULift.{u} (Fin (n + 1)))
  let : G.IsFiniteType := ⟨show Finite (ULift.{u} (Fin (n + 1))) from inferInstance⟩
  constructor
  refine ⟨G.localGeneratorsData, ?_⟩
  constructor
  intro U
  dsimp only [SheafOfModules.GeneratingSections.localGeneratorsData]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def freeSectionsBasis (Y : Scheme.{u}) (n : ℕ) :
    Module.Basis (Fin (n + 1)) Γ(Y, ⊤) Γ(freeSheaf Y n, ⊤) := by
  let I := ULift.{u} (Fin (n + 1))
  let F := SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)
  let U := fun _ : I => SheafOfModules.unit Y.ringCatSheaf
  let : HasBiproduct U := HasBiproduct.of_hasCoproduct U
  let : F.Additive := by
    change (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).Additive
    unfold SheafOfModules.evaluation
    infer_instance
  let : PreservesLimit (Discrete.functor U) F := by
    dsimp [F]
    infer_instance
  let : PreservesBiproduct U F := preservesBiproduct_of_preservesProduct F
  let e : F.obj (SheafOfModules.free I) ≅
      ModuleCat.of Γ(Y, ⊤) (I → Γ(Y, ⊤)) :=
    F.mapIso (biproduct.isoCoproduct U).symm ≪≫ F.mapBiproduct U ≪≫
      biproduct.isoProduct (F.obj ∘ U) ≪≫ ModuleCat.piIsoPi (F.obj ∘ U)
  exact ((Pi.basisFun Γ(Y, ⊤) I).map e.symm.toLinearEquiv).reindex Equiv.ulift

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def polynomialBundleIso (R : Type u) [CommRing R] (n : ℕ) :
    Proj (homogeneousSubmodule (Fin (n + 1)) R) ≅
      (freeSheaf (Spec (.of R)) n).projectiveBundle := by
  let E := freeSheaf (Spec (.of R)) n
  let b := freeSectionsBasis (Spec (.of R)) n
  let e : Γ(Spec (.of R), ⊤) ≃+* R :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  exact PolynomialProjectiveCoefficientIso.iso e ≪≫
    SymmetricPolynomialBasisComparison.iso b ≪≫ AffineProjectiveBundleComparison.wholeIso E

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem polynomialBundleIso_structure (R : Type u) [CommRing R] (n : ℕ) :
    (polynomialBundleIso R n).hom ≫ (freeSheaf (Spec (.of R)) n).projectiveBundleπ =
      homogeneousProjπ := by
  let E := freeSheaf (Spec (.of R)) n
  let b := freeSectionsBasis (Spec (.of R)) n
  let e : Γ(Spec (.of R), ⊤) ≃+* R :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  change ((PolynomialProjectiveCoefficientIso.iso e).hom ≫
    (SymmetricPolynomialBasisComparison.iso b).hom ≫
    (AffineProjectiveBundleComparison.wholeIso E).hom) ≫ E.projectiveBundleπ = _
  rw [Category.assoc, Category.assoc, AffineProjectiveBundleComparison.wholeIso_structure]
  calc
    _ = ((PolynomialProjectiveCoefficientIso.iso e).hom ≫
        ((SymmetricPolynomialBasisComparison.iso b).hom ≫
          affineProjectiveBundle.π Γ(Spec (.of R), ⊤) Γ(E, ⊤))) ≫
        (Spec (.of R)).isoSpec.inv := by simp only [Category.assoc]
    _ = ((PolynomialProjectiveCoefficientIso.iso e).hom ≫ homogeneousProjπ) ≫
        (Spec (.of R)).isoSpec.inv := by
      rw [SymmetricPolynomialBasisComparison.iso_structure]
    _ = (homogeneousProjπ ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
        (Spec (.of R)).isoSpec.inv := by
      rw [PolynomialProjectiveCoefficientIso.iso_structure]
    _ = homogeneousProjπ := by
      have he : Spec.map (CommRingCat.ofHom e.toRingHom) = (Spec (.of R)).isoSpec.hom :=
        (Scheme.isoSpec_Spec_hom (.of R)).symm
      rw [he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original finite polynomial projective projection is genuinely native-projective. -/
theorem polynomialProjection_isProjective (R : Type u) [CommRing R] (n : ℕ) :
    IsProjective (homogeneousProjπ (R := R) (σ := Fin (n + 1))) := by
  let E := freeSheaf (Spec (.of R)) n
  exact ⟨E, inferInstance, inferInstance, (polynomialBundleIso R n).hom,
    inferInstance, polynomialBundleIso_structure R n⟩

/-- A genuine original finite polynomial closed factorization gives the SAME original
morphism native projectivity, with no bundle-comparison/projectivity certificate. -/
theorem of_isProjectiveFactorization {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (hf : IsProjectiveFactorization f) : IsProjective f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  obtain ⟨E, hE, hEt, j, hj, hjp⟩ :=
    (polynomialProjection_isProjective R n).exists_isClosedImmersion
  let := hE
  let := hEt
  let : IsClosedImmersion i := hi
  let : IsClosedImmersion j := hj
  exact ⟨E, hE, hEt, i ≫ j, inferInstance, by rw [Category.assoc, hjp, hif]⟩

/-- Over the original affine coefficient spectrum the TWO actual projectivity notions agree. -/
theorem iff_isProjectiveFactorization {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) : IsProjective f ↔ IsProjectiveFactorization f := by
  constructor
  · intro h
    let := h
    exact ProjectiveFactorizationRingIso.of_isProjective f
  · exact of_isProjectiveFactorization f

end EnvelopeProperty.NativeProjectivityFromPolynomialFactorization
