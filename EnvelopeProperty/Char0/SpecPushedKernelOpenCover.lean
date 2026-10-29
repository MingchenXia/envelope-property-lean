import EnvelopeProperty.Char0.SpecPushedRoundedCanonicalKernel
import EnvelopeProperty.Char0.SpecQuotientKernelFactorization

/-! # The SAME whole original pushed kernel equals genuine original open-chart kernels -/

open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.CanonicalGeometry
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem wholeOriginalFactorCongr {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    (g₁ g₂ : Y ⟶ X) (he : g₁ = g₂) (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a b : Γ(Y, ⊤)) (hab : a = b) :
    (∃ θ : (Scheme.Modules.pullback g₁).obj (canonicalLineSheaf f n) ⟶ absolute (g₁ ≫ f) n J hJ q,
      θ ≫ absoluteRoundedInclusion (g₁ ≫ f) n J hJ q =
        SchemeUnitScalarAction.globalScalarAction _ a ≫ exteriorCotangentSheafPullbackMap f g₁ n) ↔
    (∃ θ : (Scheme.Modules.pullback g₂).obj (canonicalLineSheaf f n) ⟶ absolute (g₂ ≫ f) n J hJ q,
      θ ≫ absoluteRoundedInclusion (g₂ ≫ f) n J hJ q =
        SchemeUnitScalarAction.globalScalarAction _ b ≫ exteriorCotangentSheafPullbackMap f g₂ n) := by
  cases he
  cases hab
  rfl

private theorem wholeKernelIntersectionExt {R : Type u} [CommRing R] {ι : Type v}
    (S : ι → Type u) [∀ i, CommRing (S i)] (I : Ideal R) (K : (i : ι) → Ideal (S i))
    (φ : (i : ι) → R →+* S i) (h : ∀ a, a ∈ I ↔ ∀ i, φ i a ∈ K i) :
    I = ⨅ i, (K i).comap (φ i) := by
  ext a
  exact (h a).trans (by simp only [Ideal.mem_iInf, Ideal.mem_comap])

/-- SAME ENTIRE original pushed quotient kernel is the intersection of
SAME ENTIRE original quotient kernels on an actual open affine-spectrum cover.
All coefficient/map/quotient comparisons are DERIVED, not assumed. -/
theorem specPushedQuotientKernel_eq_iInf_open_cover
    {k : Type u} [Field k] [CharZero k] (A : CommRingCat.{u}) [Algebra k A]
    {Y : Scheme.{u}} (g : Y ⟶ Spec A) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    {ι : Type v} (B : ι → CommRingCat.{u}) [∀ i, Algebra k (B i)]
    (φ : (i : ι) → A →ₐ[k] B i) (j : (i : ι) → Spec (B i) ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (htriangle : ∀ i, j i ≫ g = Spec.map (CommRingCat.ofHom (φ i).toRingHom))
    (hcover : ∀ y : Y, ∃ (i : ι) (x : Spec (B i)), j i x = y) :
    letI : Smooth (g ≫ affineStructuralMap k A) :=
      SmoothOfRelativeDimension.smooth n (g ≫ affineStructuralMap k A)
    specPushedQuotientKernel A g z hz J hJ q =
      ⨅ i, (specQuotientKernel A (B i) (φ i) z hz (J.comap (j i))
        (hJ.comap_of_smooth (g ≫ affineStructuralMap k A) (j i)) q).comap (φ i).toRingHom := by
  let f := affineStructuralMap k A
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
  apply wholeKernelIntersectionExt (fun i => B i)
  intro a
  refine (mem_specPushedQuotientKernel_iff A g z hz J hJ q a).trans ?_
  have hc := quotientDifferentialSection_apply_eq_zero_iff_open_cover_factorization f g n J hJ q
    (g.appTop ((Scheme.ΓSpecIso A).inv.hom a)) (fun i => Spec (B i)) j hcover
  refine hc.trans ?_
  apply forall_congr'
  intro i
  have hcoeff : (j i).appTop (g.appTop ((Scheme.ΓSpecIso A).inv.hom a)) =
      (Scheme.ΓSpecIso (B i)).inv.hom (φ i a) := by
    have ht := congrArg (fun t : Spec (B i) ⟶ Spec A =>
      t.appTop.hom ((Scheme.ΓSpecIso A).inv.hom a)) (htriangle i)
    have hn := congrArg (fun t : A ⟶ Scheme.Γ.obj (.op (Spec (B i))) => t.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (φ i).toRingHom))
    exact ht.trans hn.symm
  have hsmOpen : SmoothOfRelativeDimension n ((j i ≫ g) ≫ f) := by
    rw [Category.assoc]
    exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := j i) (n := 0) (m := n) (g ≫ f))
  have hsmLeaf : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (φ i).toRingHom) ≫ f) :=
    (htriangle i) ▸ hsmOpen
  let : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (φ i).toRingHom) ≫ affineStructuralMap k A) := hsmLeaf
  have hfg := wholeOriginalFactorCongr f n (j i ≫ g)
    (Spec.map (CommRingCat.ofHom (φ i).toRingHom)) (htriangle i)
    (J.comap (j i)) (hJ.comap_of_smooth (g ≫ f) (j i)) q _ _ hcoeff
  exact hfg.trans (mem_specQuotientKernel_iff_factorization A (B i) (φ i) z hz
    (J.comap (j i)) (hJ.comap_of_smooth (g ≫ f) (j i)) q (φ i a)).symm

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
