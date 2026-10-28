import EnvelopeProperty.Char0.AffineSpecRoundedCanonicalKernel
import EnvelopeProperty.AlgGeom.FlatSectionKernel
import EnvelopeProperty.AlgGeom.ClosedFibreLocalLiftFlatness
import EnvelopeProperty.AlgGeom.AffineModuleGermLocalization
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # The SAME original rounded quotient under actual tensor-local scalar extension

The original étale differential bases derive the entire actual section kernel.
Flat exactness then tests arbitrary extended coefficients on the SAME original
quotient differential section; no quotient-comparison certificate is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open EnvelopeProperty.CanonicalGeometry EnvelopeProperty.FlatSectionKernel

noncomputable section
universe u

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

variable {k : Type u} [Field k] (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The entire intrinsic kernel is the coefficient kernel of the SAME actual original section. -/
theorem specQuotientKernel_eq_originalSectionKernel :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Spec B, ⊤))
    specQuotientKernel A B φ z hz J hJ q = sectionKernel (𝟙 (Spec B)) M m := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let α := quotientDifferentialSection f g n J hJ q
  ext a
  refine (mem_specQuotientKernel_iff A B φ z hz J hJ q a).trans ?_
  change α.val.app (.op ⊤) ((Scheme.ΓSpecIso B).inv.hom a) = 0 ↔
    (ProperBirationalSections.coefficientMap (𝟙 (Spec B)) a) •
      (α.val.app (.op ⊤) (1 : Γ(Spec B, ⊤))) = 0
  have hc : ProperBirationalSections.coefficientMap (𝟙 (Spec B)) a =
      (Scheme.ΓSpecIso B).inv.hom a := by
    simp [ProperBirationalSections.coefficientMap]
  rw [hc]
  have h := (α.val.app (.op ⊤)).hom.map_smul ((Scheme.ΓSpecIso B).inv.hom a)
    (1 : Γ(Spec B, ⊤))
  simpa only [smul_eq_mul, mul_one] using Iff.of_eq (congrArg (fun w => w = 0) h)

/-- Actual source and target étale bases derive the WHOLE kernel as colon by the SAME Jacobian. -/
theorem specQuotientKernel_eq_jacobian_colon
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI : Algebra A B := φ.toAlgebra
    specQuotientKernel A B φ z hz J hJ q =
      (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).colon
        {relativeDifferentialDet (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)} := by
  let : Algebra A B := φ.toAlgebra
  rw [specQuotientKernel_eq_colon A B φ z hz J hJ q v hv,
    affineRelativeJacobianIdeal_eq_span z hz, Ideal.colon_span]

variable {D : Type u} [CommRing D] [Algebra B D]

/-- Every flat extended scalar acts on the literal tensor of the SAME original quotient section. -/
theorem originalQuotientTensor_eq_zero_iff [Module.Flat B D]
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (t : D) :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Spec B, ⊤))
    letI : Algebra A B := φ.toAlgebra
    t ⊗ₜ[B] m = (0 : D ⊗[B] AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M) ↔
      t * algebraMap B D
        (relativeDifferentialDet (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)) ∈
          (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).map (algebraMap B D) := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let M := quotient f g n J hJ q
  let m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
    (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Spec B, ⊤))
  let : Algebra A B := φ.toAlgebra
  change t ⊗ₜ[B] m = (0 : D ⊗[B] AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M) ↔ _
  have hk := specQuotientKernel_eq_originalSectionKernel A B φ z hz J hJ q
  have he := map_kernel_eq (S := D) (LinearMap.toSpanSingleton B _ m)
  have ht : t ⊗ₜ[B] m = (0 : D ⊗[B] AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M) ↔
      t ∈ (specQuotientKernel A B φ z hz J hJ q).map (algebraMap B D) := by
    rw [hk]
    change _ ↔ t ∈ Ideal.map (algebraMap B D) (LinearMap.toSpanSingleton B _ m).ker
    rw [he]
    simp only [LinearMap.mem_ker, coefficientBaseChange_apply,
      LinearMap.toSpanSingleton_apply, one_smul]
  rw [ht, specQuotientKernel_eq_jacobian_colon A B φ z hz J hJ q v hv,
    map_colon_singleton_of_flat, Submodule.mem_colon_singleton, smul_eq_mul]

/-- The actual affine pullback-unit section has the SAME exact rounded-ideal membership test. -/
theorem originalPulledQuotient_eq_zero_iff [Module.Flat B D]
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (t : D) :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Spec B, ⊤))
    letI : Algebra A B := φ.toAlgebra
    (ProperBirationalSections.coefficientMap
      (FlatGlobalSections.structureMap (S := D) (𝟙 (Spec B))) t) •
        pulledSection (S := D) (𝟙 (Spec B)) M m = 0 ↔
      t * algebraMap B D
        (relativeDifferentialDet (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)) ∈
          (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).map (algebraMap B D) := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : SmoothOfRelativeDimension n (g ≫ f) := by
    have heq : g ≫ f = affineStructuralMap k B := affineAlgebraMap_structuralSquare k A B φ
    exact heq.symm ▸ smoothOfRelativeDimension_of_etale_coordinates v hv
  let M := quotient f g n J hJ q
  let : M.IsQuasicoherent := quotient_isQuasicoherent f g n J hJ q
  let m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
    (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Spec B, ⊤))
  let : Algebra A B := φ.toAlgebra
  change (ProperBirationalSections.coefficientMap
    (FlatGlobalSections.structureMap (S := D) (𝟙 (Spec B))) t) •
      pulledSection (S := D) (𝟙 (Spec B)) M m = 0 ↔ _
  have he := (AffineModuleFlatBaseChange.tensorEquiv (S := D) (𝟙 (Spec B)) M).map_eq_zero_iff
    (x := t ⊗ₜ[B] m)
  rw [AffineModuleFlatBaseChange.tensorEquiv_tmul] at he
  exact he.trans (originalQuotientTensor_eq_zero_iff A B φ z hz J hJ q v hv t)

private theorem originalIdeal_mem_iff_faithfullyFlat {C E : Type u}
    [CommRing C] [CommRing E] (liftHom : C →+* E) (hlift : liftHom.FaithfullyFlat)
    (I : Ideal C) (c : C) : c ∈ I ↔ liftHom c ∈ I.map liftHom := by
  let : Algebra C E := liftHom.toAlgebra
  let : Module.FaithfullyFlat C E := hlift
  change c ∈ I ↔ c ∈ (I.map (algebraMap C E)).comap (algebraMap C E)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- At the actual tensor-local point, the SAME original quotient is tested by the actual
manufactured faithfully flat lift, retaining ALL original coefficient actions. -/
theorem originalQuotientTensor_tensorLocal_eq_zero_iff
    {S K F : Type u} [CommRing S] [Field K] [CommRing F] [IsLocalRing F]
    [Algebra A S] [Algebra A K] [Algebra A F] [Module.Flat A S]
    [IsAdicComplete (IsLocalRing.maximalIdeal F) F]
    (β : S →ₐ[A] K) (ε : F →+* K) (η : S →ₐ[A] F)
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI : Algebra A B := φ.toAlgebra
    ∀ (p : B →ₐ[A] K) (γ : B →ₐ[A] F)
      (_hε : RingHom.ker ε = IsLocalRing.maximalIdeal F)
      (_hγ : ε.comp γ.toRingHom = p.toRingHom)
      (_hη : ε.comp η.toRingHom = β.toRingHom)
      (_hR : Function.Surjective (algebraMap A K))
      (_hker : RingHom.ker β.toRingHom =
        (RingHom.ker (algebraMap A K)).map (algebraMap A S))
      (_hp : Function.Surjective p)
      (_hflat : γ.toRingHom.Flat)
      (_hm : (ClosedFibreLocalRing.pointIdeal p).map γ.toRingHom = IsLocalRing.maximalIdeal F)
      [IsNoetherianRing (ClosedFibreLocalRing.PointLocalRing
        (ClosedFibreLocalRing.pointTensorMap β p))] (s : S),
    let T := B ⊗[A] S
    let D := ClosedFibreLocalRing.PointLocalRing (ClosedFibreLocalRing.pointTensorMap β p)
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    let M := quotient f g n J hJ q
    let m : AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M :=
      (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) (1 : Γ(Spec B, ⊤))
    (algebraMap T D ((Algebra.TensorProduct.includeRight : S →ₐ[A] T) s)) ⊗ₜ[B] m =
        (0 : D ⊗[B] AffineModuleFlatBaseChange.sections (𝟙 (Spec B)) M) ↔
      η s * γ (relativeDifferentialDet
        (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)) ∈
          (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)).map γ.toRingHom := by
  let : Algebra A B := φ.toAlgebra
  intro p γ hε hγ hη hR hker hp hflat hm hNoeth s
  let T := B ⊗[A] S
  let D := ClosedFibreLocalRing.PointLocalRing (ClosedFibreLocalRing.pointTensorMap β p)
  let : Module.Flat B D := Module.Flat.trans B T D
  let liftHom := ClosedFibreStalkCompletion.localTensorLift β p ε γ η hε hγ hη
  have hlift : liftHom.FaithfullyFlat :=
    ClosedFibreLocalLiftFlatness.localTensorLift_faithfullyFlat
      β p ε γ η hε hγ hη hR hker hp hflat hm
  let t : D := algebraMap T D ((Algebra.TensorProduct.includeRight : S →ₐ[A] T) s)
  let j : B := relativeDifferentialDet
    (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)
  let I := idealOfSpecSheaf (RoundedSncIdealSheaf.rounded J hJ q)
  have hleft : liftHom.comp (algebraMap B D) = γ.toRingHom :=
    RingHom.ext (ClosedFibreStalkCompletion.localTensorLift_includeLeft β p ε γ η hε hγ hη)
  have hright : liftHom t = η s :=
    ClosedFibreStalkCompletion.localTensorLift_includeRight β p ε γ η hε hγ hη s
  have he : t * algebraMap B D j ∈ I.map (algebraMap B D) ↔
      η s * γ j ∈ I.map γ.toRingHom := by
    rw [originalIdeal_mem_iff_faithfullyFlat liftHom hlift, map_mul, hright,
      show liftHom (algebraMap B D j) = γ j from RingHom.congr_fun hleft j,
      Ideal.map_map, hleft]
  exact (originalQuotientTensor_eq_zero_iff A B φ z hz J hJ q v hv t).trans he

end EnvelopeProperty.Char0.RoundedCanonicalModule
