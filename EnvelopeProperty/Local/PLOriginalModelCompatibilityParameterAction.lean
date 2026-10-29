import EnvelopeProperty.Projective.NativeParameterLineMonoid
import EnvelopeProperty.Projective.NativeParameterFamily
import EnvelopeProperty.Projective.NativeMultiplicativeGroupProjections
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# PL Original Model Compatibility Parameter Action

Whole original product coordinates and the actual parameter action.
The coefficient ring and both original product projections are retained. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial TensorProduct MonoidalCategory CategoryTheory.MonObj
noncomputable section
universe u

namespace EnvelopeProperty.PLOriginalModelCompatibilityParameterAction

variable (R : Type u) [CommRing R]

private theorem polynomialTensorEquiv_comp_includeLeft
    (A : Type u) [CommRing A] [Algebra R A] :
    (polyEquivTensor R A).symm.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      (Polynomial.C : A →+* A[X]) := by
  apply RingHom.ext
  intro a
  change (polyEquivTensor R A).symm (a ⊗ₜ[R] (1 : R[X])) = Polynomial.C a
  simp [Polynomial.smul_eq_C_mul]

private theorem polynomialTensorEquiv_comp_includeRight
    (A : Type u) [CommRing A] [Algebra R A] :
    (polyEquivTensor R A).symm.toRingHom.comp
        (Algebra.TensorProduct.includeRight : R[X] →ₐ[R] A ⊗[R] R[X]).toRingHom =
      Polynomial.mapRingHom (algebraMap R A) := by
  apply RingHom.ext
  intro p
  change (polyEquivTensor R A).symm ((1 : A) ⊗ₜ[R] p) = p.map (algebraMap R A)
  simp

/-- The original group--parameter product is the original Laurent-coefficient
polynomial spectrum, through the canonical whole tensor-product comparison. -/
def nativeParameterProductIso :
    Spec (CommRingCat.of R[T;T⁻¹][X]) ≅
      pullback (ProjBerk.nativeMultiplicativeGroup R).hom (ProjBerk.nativeParameterLine R).hom :=
  (Scheme.Spec.mapIso
    (polyEquivTensor R R[T;T⁻¹]).symm.toRingEquiv.toCommRingCatIso.op).trans
      (pullbackSpecIso R R[T;T⁻¹] R[X]).symm

/-- The complete original first product projection is the original Laurent
coefficient inclusion into its polynomial ring. -/
@[reassoc]
theorem nativeParameterProductIso_fst :
    (nativeParameterProductIso R).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][X])) := by
  change ((Scheme.Spec.mapIso
    (polyEquivTensor R R[T;T⁻¹]).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
      (pullbackSpecIso R R[T;T⁻¹] R[X]).inv) ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
      (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) = _
  rw [Category.assoc, pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (polyEquivTensor R R[T;T⁻¹]).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((polyEquivTensor R R[T;T⁻¹]).symm.toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom)) = _
  rw [polynomialTensorEquiv_comp_includeLeft]

/-- The complete original second product projection is exactly extension
of the original polynomial coefficients to the original Laurent ring. -/
@[reassoc]
theorem nativeParameterProductIso_snd :
    (nativeParameterProductIso R).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (LaurentPolynomial.C : R →+* R[T;T⁻¹]))) := by
  change ((Scheme.Spec.mapIso
    (polyEquivTensor R R[T;T⁻¹]).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
      (pullbackSpecIso R R[T;T⁻¹] R[X]).inv) ≫
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
      (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) = _
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (polyEquivTensor R R[T;T⁻¹]).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : R[X] →ₐ[R] R[T;T⁻¹] ⊗[R] R[X]).toRingHom) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((polyEquivTensor R R[T;T⁻¹]).symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight : R[X] →ₐ[R] R[T;T⁻¹] ⊗[R] R[X]).toRingHom)) = _
  rw [polynomialTensorEquiv_comp_includeRight]
  rfl

private def parameterMonoidCoaction :
    R[X] →ₐ[R] R[T;T⁻¹] ⊗[R] R[X] :=
  (Algebra.TensorProduct.map (ProjBerk.nativeParameterExponentMap R).toAlgHom
      (Polynomial.toFinsuppIsoAlg R).symm.toAlgHom).comp
    ((Bialgebra.comulAlgHom R (AddMonoidAlgebra R ℕ)).comp
      (Polynomial.toFinsuppIsoAlg R).toAlgHom)

private theorem parameterMonoidCoaction_eq :
    (polyEquivTensor R R[T;T⁻¹]).symm.toRingHom.comp
        (parameterMonoidCoaction R).toRingHom = parameterLaurentHom (R := R) := by
  apply Polynomial.ringHom_ext
  · intro r
    have h := ((polyEquivTensor R R[T;T⁻¹]).symm.toAlgHom.comp
      (parameterMonoidCoaction R)).commutes r
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, ← LaurentPolynomial.C_eq_algebraMap] at h
    simp only [RingHom.comp_apply, parameterLaurentHom, parameterUnitBaseChangeHom_C]
    exact h
  · have hX : (Polynomial.toFinsuppIsoAlg R) Polynomial.X =
        (AddMonoidAlgebra.single 1 1 : AddMonoidAlgebra R ℕ) := Polynomial.toFinsupp_X
    have hXinv : (Polynomial.toFinsuppIsoAlg R).symm.toAlgHom
        (AddMonoidAlgebra.single 1 1 : AddMonoidAlgebra R ℕ) = Polynomial.X :=
      (Polynomial.toFinsuppIsoAlg R).symm_apply_eq.mpr hX.symm
    have hcomul : (Bialgebra.comulAlgHom R (AddMonoidAlgebra R ℕ))
        (AddMonoidAlgebra.single 1 1) =
        (AddMonoidAlgebra.single 1 1 : AddMonoidAlgebra R ℕ) ⊗ₜ[R] AddMonoidAlgebra.single 1 1 := by
      change Coalgebra.comul (R := R) (AddMonoidAlgebra.single 1 (1 : R) : AddMonoidAlgebra R ℕ) = _
      simp
    have hexponent : (ProjBerk.nativeParameterExponentMap R).toAlgHom
        (AddMonoidAlgebra.single 1 1 : AddMonoidAlgebra R ℕ) = LaurentPolynomial.T 1 := by
      simp [ProjBerk.nativeParameterExponentMap]
    change (polyEquivTensor R R[T;T⁻¹]).symm
      ((Algebra.TensorProduct.map (ProjBerk.nativeParameterExponentMap R).toAlgHom
        (Polynomial.toFinsuppIsoAlg R).symm.toAlgHom)
        ((Bialgebra.comulAlgHom R (AddMonoidAlgebra R ℕ))
          ((Polynomial.toFinsuppIsoAlg R) Polynomial.X))) = _
    rw [hX, hcomul, Algebra.TensorProduct.map_tmul, hexponent, hXinv]
    simp [parameterLaurentHom, parameterLaurentUnit, Polynomial.smul_eq_C_mul]

/-- Naturality of the tensor comparison of `Spec` on algebras over an arbitrary base:
the product of two `Spec` maps is `Spec` of the tensor product map. -/
private theorem algSpec_tensorHom_left {B : CommRingCat.{u}} {A A' C C' : Type u}
    [CommRing A] [CommRing A'] [CommRing C] [CommRing C']
    [Algebra B A] [Algebra B A'] [Algebra B C] [Algebra B C']
    (f : A' →ₐ[B] A) (g : C' →ₐ[B] C) :
    ((algSpec B).map (CommAlgCat.ofHom f).op ⊗ₘ (algSpec B).map (CommAlgCat.ofHom g).op).left ≫
        (pullbackSpecIso B A' C').hom =
      (pullbackSpecIso B A C).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map f g).toRingHom) := by
  have h := congrArg Over.Hom.left
    (Functor.LaxMonoidal.μ_natural (algSpec B) (CommAlgCat.ofHom f).op (CommAlgCat.ofHom g).op)
  simp only [Over.comp_left, μ_algSpec_left, algSpec_map_left] at h
  exact h

private theorem exponentPolynomial_tensorSpec :
    ((ProjBerk.nativeParameterGroupToMonoid R ⊗ₘ
        (ProjBerk.nativeParameterLineMonoidIso R).inv).left) ≫
        (pullbackSpecIso R (AddMonoidAlgebra R ℕ) (AddMonoidAlgebra R ℕ)).hom =
      (pullbackSpecIso R R[T;T⁻¹] R[X]).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (ProjBerk.nativeParameterExponentMap R).toAlgHom
            (Polynomial.toFinsuppIsoAlg R).symm.toAlgHom).toRingHom) :=
  algSpec_tensorHom_left (B := CommRingCat.of R)
    (ProjBerk.nativeParameterExponentMap R).toAlgHom (Polynomial.toFinsuppIsoAlg R).symm.toAlgHom

private theorem nativeParameterLine_smul_expansion :
    letI := ProjBerk.nativeParameterLineModObj R
    (ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup R)
      (X := ProjBerk.nativeParameterLine R)).left =
      (ProjBerk.nativeParameterGroupToMonoid R ⊗ₘ
        (ProjBerk.nativeParameterLineMonoidIso R).inv).left ≫
      (MonObj.mul (X :=
        (Spec (CommRingCat.of (AddMonoidAlgebra R ℕ))).asOver (Spec (CommRingCat.of R)))).left ≫
      (ProjBerk.nativeParameterLineMonoidIso R).hom.left := by
  let := ProjBerk.nativeParameterLineModObj R
  let e := ProjBerk.nativeParameterLineMonoidIso R
  have ht : (ProjBerk.nativeParameterGroupInclusion R ▷ ProjBerk.nativeParameterLine R) ≫
      (e.inv ⊗ₘ e.inv) = ProjBerk.nativeParameterGroupToMonoid R ⊗ₘ e.inv := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom]
    simp [ProjBerk.nativeParameterGroupInclusion, Category.assoc, e]
  change ((ProjBerk.nativeParameterGroupInclusion R ▷ ProjBerk.nativeParameterLine R) ≫
    ((e.inv ⊗ₘ e.inv) ≫ MonObj.mul (X :=
      (Spec (CommRingCat.of (AddMonoidAlgebra R ℕ))).asOver (Spec (CommRingCat.of R))) ≫
      e.hom)).left = _
  rw [← Category.assoc, ← Category.assoc, ht]
  simp only [Over.comp_left, Category.assoc]
  rfl

private theorem nativeParameterProductIso_tensor :
    (nativeParameterProductIso R).hom ≫ (pullbackSpecIso R R[T;T⁻¹] R[X]).hom =
      Spec.map (CommRingCat.ofHom (polyEquivTensor R R[T;T⁻¹]).symm.toRingHom) := by
  change (Spec.map (CommRingCat.ofHom (polyEquivTensor R R[T;T⁻¹]).symm.toRingHom) ≫
      (pullbackSpecIso R R[T;T⁻¹] R[X]).inv) ≫
      (pullbackSpecIso R R[T;T⁻¹] R[X]).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The SAME selected native parameter action is literally the original whole
Laurent-coefficient scaling morphism, with no supplied action square. -/
@[reassoc]
theorem nativeParameterProductIso_smul :
    letI := ProjBerk.nativeParameterLineModObj R
    (nativeParameterProductIso R).hom ≫
      (ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup R)
        (X := ProjBerk.nativeParameterLine R)).left =
      Spec.map (CommRingCat.ofHom (parameterLaurentHom (R := R))) := by
  let := ProjBerk.nativeParameterLineModObj R
  let tf := (Polynomial.toFinsuppIsoAlg R).toAlgHom.toRingHom
  let cm := (Bialgebra.comulAlgHom R (AddMonoidAlgebra R ℕ)).toRingHom
  let mp := (Algebra.TensorProduct.map (ProjBerk.nativeParameterExponentMap R).toAlgHom
    (Polynomial.toFinsuppIsoAlg R).symm.toAlgHom).toRingHom
  let sy := (polyEquivTensor R R[T;T⁻¹]).symm.toRingHom
  -- All rewriting below is done by `Eq.trans`/`congrArg`, since the objects of the
  -- monoidal products are only definitionally (not syntactically) `pullback`s.
  have k1 : (ModObj.smul (M := ProjBerk.nativeMultiplicativeGroup R)
      (X := ProjBerk.nativeParameterLine R)).left =
      (ProjBerk.nativeParameterGroupToMonoid R ⊗ₘ
          (ProjBerk.nativeParameterLineMonoidIso R).inv).left ≫
        (pullbackSpecIso R (AddMonoidAlgebra R ℕ) (AddMonoidAlgebra R ℕ)).hom ≫
          Spec.map (CommRingCat.ofHom cm) ≫ Spec.map (CommRingCat.ofHom tf) :=
    (nativeParameterLine_smul_expansion R).trans
      (congrArg (fun x => (ProjBerk.nativeParameterGroupToMonoid R ⊗ₘ
        (ProjBerk.nativeParameterLineMonoidIso R).inv).left ≫ x)
        (Category.assoc (pullbackSpecIso R (AddMonoidAlgebra R ℕ) (AddMonoidAlgebra R ℕ)).hom
          (Spec.map (CommRingCat.ofHom cm)) (Spec.map (CommRingCat.ofHom tf))))
  have k2 := (Category.assoc
      (ProjBerk.nativeParameterGroupToMonoid R ⊗ₘ
          (ProjBerk.nativeParameterLineMonoidIso R).inv).left
      (pullbackSpecIso R (AddMonoidAlgebra R ℕ) (AddMonoidAlgebra R ℕ)).hom
      (Spec.map (CommRingCat.ofHom cm) ≫ Spec.map (CommRingCat.ofHom tf))).symm.trans
    ((congrArg (fun x => x ≫ Spec.map (CommRingCat.ofHom cm) ≫ Spec.map (CommRingCat.ofHom tf))
      (exponentPolynomial_tensorSpec R)).trans
      (Category.assoc (pullbackSpecIso R R[T;T⁻¹] R[X]).hom (Spec.map (CommRingCat.ofHom mp))
        (Spec.map (CommRingCat.ofHom cm) ≫ Spec.map (CommRingCat.ofHom tf))))
  have k3 := (Category.assoc (nativeParameterProductIso R).hom (pullbackSpecIso R R[T;T⁻¹] R[X]).hom
      (Spec.map (CommRingCat.ofHom mp) ≫ Spec.map (CommRingCat.ofHom cm) ≫
        Spec.map (CommRingCat.ofHom tf))).symm.trans
    (congrArg (fun x => x ≫ Spec.map (CommRingCat.ofHom mp) ≫ Spec.map (CommRingCat.ofHom cm) ≫
        Spec.map (CommRingCat.ofHom tf)) (nativeParameterProductIso_tensor R))
  have hR : Spec.map (CommRingCat.ofHom sy) ≫ Spec.map (CommRingCat.ofHom mp) ≫
        Spec.map (CommRingCat.ofHom cm) ≫ Spec.map (CommRingCat.ofHom tf) =
      Spec.map (CommRingCat.ofHom (parameterLaurentHom (R := R))) := by
    rw [← parameterMonoidCoaction_eq]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact ((congrArg (fun x => (nativeParameterProductIso R).hom ≫ x) k1).trans
    ((congrArg (fun x => (nativeParameterProductIso R).hom ≫ x) k2).trans k3)).trans hR

end EnvelopeProperty.PLOriginalModelCompatibilityParameterAction
