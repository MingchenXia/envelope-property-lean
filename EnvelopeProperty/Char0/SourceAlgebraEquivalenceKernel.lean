import EnvelopeProperty.Char0.SpecPushedKernelOpenCover
import Mathlib.RingTheory.RingHom.Etale

/-!
# Whole original affine quotient kernels under an actual source equivalence

All source-function determinant generators are transported bijectively;
no Jacobian or quotient-kernel comparison is supplied as an assumption.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory Module

universe u

/-- The actual image coordinates under an actual algebra equivalence remain etale. -/
theorem etale_coordinates_sourceAlgEquiv
    {k A D : Type u} [CommRing k] [CommRing A] [CommRing D]
    [Algebra k A] [Algebra k D] (e : A ≃ₐ[k] D) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) (fun i => e (z i))).toRingHom.Etale := by
  have hcomp : (MvPolynomial.aeval (R := k) (fun i => e (z i))).toRingHom =
      e.toRingHom.comp (MvPolynomial.aeval (R := k) z).toRingHom := by
    change (MvPolynomial.aeval (R := k) (fun i => e (z i))).toRingHom =
      (e.toAlgHom.comp (MvPolynomial.aeval (R := k) z)).toRingHom
    congr 1
    ext i
    simp
  rw [hcomp]
  exact RingHom.Etale.stableUnderComposition _ _ hz (RingHom.Etale.of_bijective e.bijective)

/-- Every original source-function determinant has the SAME actual target image under source equivalence. -/
theorem affineRelativeJacobianIdeal_sourceAlgEquiv
    {k A D B : Type u} [CommRing k] [CommRing A] [CommRing D] [CommRing B]
    [Algebra k A] [Algebra k D] [Algebra k B] [Algebra A B] [Algebra D B]
    (e : A ≃ₐ[k] D) (hcoeff : ∀ a : A, algebraMap D B (e a) = algebraMap A B a)
    {n : ℕ} (b : Basis (Fin n) B (KaehlerDifferential k B)) :
    affineRelativeJacobianIdeal (R := A) b = affineRelativeJacobianIdeal (R := D) b := by
  apply congrArg Ideal.span
  apply Set.Subset.antisymm
  · rintro x ⟨w, rfl⟩
    refine ⟨fun i => e (w i), ?_⟩
    apply congrArg Matrix.det
    ext i j
    change b.coord i (KaehlerDifferential.D k B (algebraMap D B (e (w j)))) = _
    rw [hcoeff]
    rfl
  · rintro x ⟨w, rfl⟩
    refine ⟨fun i => e.symm (w i), ?_⟩
    apply congrArg Matrix.det
    ext i j
    change b.coord i (KaehlerDifferential.D k B (algebraMap A B (e.symm (w j)))) = _
    rw [← hcoeff, e.apply_symm_apply]
    rfl

namespace RoundedCanonicalModule

/-- The WHOLE actual quotient kernel retains every target coefficient under source equivalence. -/
theorem specQuotientKernel_sourceAlgEquiv
    {k : Type u} [Field k] [CharZero k]
    (A D B : CommRingCat.{u}) [Algebra k A] [Algebra k D] [Algebra k B]
    (φ : A →ₐ[k] B) (e : A ≃ₐ[k] D) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    specQuotientKernel A B φ z hz J hJ q =
      specQuotientKernel D B (φ.comp e.symm.toAlgHom) (fun i => e (z i))
        (etale_coordinates_sourceAlgEquiv e z hz) J hJ q := by
  rw [specQuotientKernel_eq_colon A B φ z hz J hJ q v hv,
    specQuotientKernel_eq_colon D B (φ.comp e.symm.toAlgHom) (fun i => e (z i))
      (etale_coordinates_sourceAlgEquiv e z hz) J hJ q v hv]
  let : Algebra A B := φ.toAlgebra
  let : Algebra D B := (φ.comp e.symm.toAlgHom).toAlgebra
  rw [affineRelativeJacobianIdeal_sourceAlgEquiv e (fun a => e.symm_apply_apply a |> congrArg φ)]

/-- The ENTIRE actual original pushed quotient kernel maps to the actual source-equivalent kernel. -/
theorem specPushedQuotientKernel_sourceAlgEquiv
    {k : Type u} [Field k] [CharZero k]
    (A D : CommRingCat.{u}) [Algebra k A] [Algebra k D]
    (e : A ≃ₐ[k] D) {Y : Scheme.{u}} (g : Y ⟶ Spec A) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    [SmoothOfRelativeDimension n (g ≫ CanonicalGeometry.affineStructuralMap k A)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    {ι : Type u} (B : ι → CommRingCat.{u}) [∀ i, Algebra k (B i)]
    (φ : (i : ι) → A →ₐ[k] B i) (j : (i : ι) → Spec (B i) ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (htriangle : ∀ i, j i ≫ g = Spec.map (CommRingCat.ofHom (φ i).toRingHom))
    (hcover : ∀ y : Y, ∃ (i : ι) (x : Spec (B i)), j i x = y)
    (v : (i : ι) → Fin n → B i)
    (hv : ∀ i, (MvPolynomial.aeval (R := k) (v i)).toRingHom.Etale) :
    (specPushedQuotientKernel A g z hz J hJ q).map e.toRingHom =
      specPushedQuotientKernel D (g ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom))
        (fun i => e (z i)) (etale_coordinates_sourceAlgEquiv e z hz) J hJ q := by
  let gD := g ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hstruct : gD ≫ CanonicalGeometry.affineStructuralMap k D =
      g ≫ CanonicalGeometry.affineStructuralMap k A := by
    dsimp [gD, CanonicalGeometry.affineStructuralMap]
    rw [Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact e.symm.commutes r
  let : SmoothOfRelativeDimension n (gD ≫ CanonicalGeometry.affineStructuralMap k D) :=
    hstruct.symm ▸ inferInstance
  let : Smooth (g ≫ CanonicalGeometry.affineStructuralMap k A) :=
    SmoothOfRelativeDimension.smooth n _
  let : Smooth (gD ≫ CanonicalGeometry.affineStructuralMap k D) :=
    SmoothOfRelativeDimension.smooth n _
  let φD (i : ι) : D →ₐ[k] B i := (φ i).comp e.symm.toAlgHom
  have htriangleD : ∀ i, j i ≫ gD = Spec.map (CommRingCat.ofHom (φD i).toRingHom) := by
    intro i
    dsimp [gD, φD]
    rw [← Category.assoc, htriangle, ← Spec.map_comp]
    rfl
  have hOld := specPushedQuotientKernel_eq_iInf_open_cover A g z hz J hJ q
    B φ j htriangle hcover
  have hNew := specPushedQuotientKernel_eq_iInf_open_cover D gD (fun i => e (z i))
    (etale_coordinates_sourceAlgEquiv e z hz) J hJ q B φD j htriangleD hcover
  have hmap (K : Ideal A) : K.map e.toRingHom = K.comap e.symm.toRingHom :=
    Ideal.map_comap_of_equiv e.toRingEquiv
  rw [hOld, hNew, hmap, Ideal.comap_iInf]
  apply iInf_congr
  intro i
  rw [Ideal.comap_comap]
  exact congrArg (fun K : Ideal (B i) => K.comap (φD i).toRingHom)
    (specQuotientKernel_sourceAlgEquiv A D (B i) (φ i) e z hz (v i) (hv i)
      (J.comap (j i)) (hJ.comap_of_smooth (g ≫ CanonicalGeometry.affineStructuralMap k A) (j i)) q)

end RoundedCanonicalModule

end EnvelopeProperty.Char0
