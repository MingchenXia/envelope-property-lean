import EnvelopeProperty.Char0.SpecPushedKernelOpenCover

/-!
# Whole actual pushed quotient kernels under actual model isomorphism

The actual original affine cover transports every model point, ideal and
original coefficient triangle. Both ENTIRE kernels use these same actual
chart kernels; no isomorphism comparison is supplied as a premise.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.RoundedCanonicalModule

open AlgebraicGeometry CategoryTheory
open EnvelopeProperty.CanonicalGeometry

universe u v

private theorem kernel_congr_ideal
    {k : Type u} [Field k] (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) {n : ℕ} (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    {J J' : (Spec B).IdealSheafData} (h : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ) :
    specQuotientKernel A B φ z hz J hJ q = specQuotientKernel A B φ z hz J' hJ' q := by
  cases h
  rfl

/-- Actual model isomorphism preserves the ENTIRE original-coefficient quotient kernel. -/
theorem specPushedQuotientKernel_modelIso
    {k : Type u} [Field k] [CharZero k]
    (A : CommRingCat.{u}) [Algebra k A]
    {Y Z : Scheme.{u}} (g : Y ⟶ Spec A) (e : Y ≅ Z) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    {ι : Type v} (B : ι → CommRingCat.{u}) [∀ i, Algebra k (B i)]
    (φ : (i : ι) → A →ₐ[k] B i) (j : (i : ι) → Spec (B i) ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (htriangle : ∀ i, j i ≫ g = Spec.map (CommRingCat.ofHom (φ i).toRingHom))
    (hcover : ∀ y : Y, ∃ (i : ι) (x : Spec (B i)), j i x = y) :
    letI : Smooth (g ≫ affineStructuralMap k A) := SmoothOfRelativeDimension.smooth n _
    specPushedQuotientKernel A g z hz J hJ q =
      specPushedQuotientKernel A (e.inv ≫ g) z hz (J.comap e.inv)
        (hJ.comap_of_smooth (g ≫ affineStructuralMap k A) e.inv) q := by
  let : Smooth (g ≫ affineStructuralMap k A) := SmoothOfRelativeDimension.smooth n _
  have hs : SmoothOfRelativeDimension (0 + n) (e.inv ≫ (g ≫ affineStructuralMap k A)) :=
    inferInstance
  let : SmoothOfRelativeDimension n ((e.inv ≫ g) ≫ affineStructuralMap k A) := by
    simpa only [Nat.zero_add, Category.assoc] using hs
  let : Smooth ((e.inv ≫ g) ≫ affineStructuralMap k A) :=
    SmoothOfRelativeDimension.smooth n _
  let jZ (i : ι) : Spec (B i) ⟶ Z := j i ≫ e.hom
  let : ∀ i, IsOpenImmersion (jZ i) := fun _ => inferInstance
  have htriangleZ : ∀ i, jZ i ≫ (e.inv ≫ g) =
      Spec.map (CommRingCat.ofHom (φ i).toRingHom) := by
    intro i
    simpa only [jZ, Category.assoc, Iso.hom_inv_id_assoc] using htriangle i
  have hcoverZ : ∀ y : Z, ∃ (i : ι) (x : Spec (B i)), jZ i x = y := by
    intro y
    obtain ⟨i, x, hx⟩ := hcover (e.inv y)
    refine ⟨i, x, ?_⟩
    change e.hom (j i x) = y
    rw [hx]
    exact congrArg (fun t : Z ⟶ Z => t y) e.inv_hom_id
  have hOld := specPushedQuotientKernel_eq_iInf_open_cover A g z hz J hJ q
    B φ j htriangle hcover
  have hNew := specPushedQuotientKernel_eq_iInf_open_cover A (e.inv ≫ g) z hz
    (J.comap e.inv) (hJ.comap_of_smooth (g ≫ affineStructuralMap k A) e.inv) q
    B φ jZ htriangleZ hcoverZ
  rw [hOld, hNew]
  apply iInf_congr
  intro i
  congr 1
  refine kernel_congr_ideal A (B i) (φ i) z hz ?_ _ _ q
  rw [← Scheme.IdealSheafData.comap_comp]
  simp only [jZ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end EnvelopeProperty.Char0.RoundedCanonicalModule
