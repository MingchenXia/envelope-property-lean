import EnvelopeProperty.Char0.GlobalRoundedQuotientOpenPullback
import EnvelopeProperty.Char0.NativeRoundedQuotientStalk
import EnvelopeProperty.AlgGeom.PullbackUnitSectionKernel
import EnvelopeProperty.Char0.ResolutionScalarTowers

/-! # The intrinsic actual affine section kernel of the SAME whole original global quotient -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Char0.AffineOpenGlobalRoundedKernel
open RoundedCanonicalModule
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k]

private theorem idealMapEquivMem {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (a : S) : a ∈ I.map e.toRingHom ↔ e.symm a ∈ I := by
  have hmap : a ∈ I.map e.toRingHom ↔ ∃ b, b ∈ I ∧ e.toRingHom b = a :=
    Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := hmap.mp ha
    have heq : b = e.symm a := e.injective (hba.trans (e.apply_symm_apply a).symm)
    exact heq ▸ hb
  · intro ha
    exact hmap.mpr ⟨e.symm a, ha, e.apply_symm_apply a⟩

private theorem pullbackSectionKernel_eq_of_zero_iff {Y : Scheme.{u}} (B : CommRingCat.{u})
    (c : Spec B ⟶ Y) (N : Y.Modules) (δ : Scheme.Modules.unitObj Y ⟶ N) (K : Ideal B)
    (hK : ∀ b : B,
      ((Scheme.Modules.pullbackUnitIso c).inv ≫ (Scheme.Modules.pullback c).map δ).val.app
        (.op ⊤) ((Scheme.ΓSpecIso B).inv.hom b) = 0 ↔ b ∈ K) :
    FlatSectionKernel.sectionKernel (R := B) (𝟙 (Spec B)) ((Scheme.Modules.pullback c).obj N)
      (Scheme.Modules.affinePullbackUnitTop c N (δ.val.app (.op ⊤) (1 : Γ(Y, ⊤)))) = K := by
  ext b
  exact (PullbackUnitSectionKernel.mem_sectionKernel_iff_pulledUnitHom B c δ b).trans (hK b)

/-- The actual intrinsic coefficient kernel of the whole quotient for the original affine composite. -/
def affineCompositeQuotientKernel (B : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (γ : Spec B ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n f]
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Ideal B :=
  (Scheme.Modules.unitMapKernelIdeal (quotientDifferentialSection (k := k) f γ n J hJ q)
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso B).hom.hom

private theorem mem_affineCompositeQuotientKernel_iff (B : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (γ : Spec B ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n f]
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (b : B) :
    b ∈ affineCompositeQuotientKernel B f γ n J hJ q ↔
      (quotientDifferentialSection (k := k) f γ n J hJ q).val.app (.op ⊤)
        ((Scheme.ΓSpecIso B).inv.hom b) = 0 :=
  idealMapEquivMem (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv
    (Scheme.Modules.unitMapKernelIdeal (quotientDifferentialSection (k := k) f γ n J hJ q)
      ⟨⊤, isAffineOpen_top _⟩) b

/-- On an actual spectrum map, the intrinsic composite kernel is the existing entire
original coefficient kernel. This source-only readback precedes any global pullback data. -/
theorem affineCompositeQuotientKernel_eq_specQuotientKernel
    (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : (Spec B).IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    let f := CanonicalGeometry.affineStructuralMap k A
    letI : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
    affineCompositeQuotientKernel B f (Spec.map (CommRingCat.ofHom φ.toRingHom)) n J hJ q =
      specQuotientKernel A B φ z hz J hJ q := rfl

/-- The SAME pulled whole global quotient and original section have exactly the
intrinsic composite kernel, for EVERY affine source coefficient and without coordinate hypotheses. -/
theorem globalQuotient_sourceKernel_eq_compositeKernel [CharZero k]
    {X Y : Scheme.{u}} (B : CommRingCat.{u}) (f : X ⟶ Spec (.of k))
    (π : Y ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension n (π ≫ f)] (c : Spec B ⟶ Y) [IsOpenImmersion c]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    letI : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
    let Q := quotient (k := k) f π n J hJ q
    let M := (Scheme.Modules.pullback c).obj Q
    let μ : AffineModuleFlatBaseChange.sections (R := B) (𝟙 (Spec B)) M :=
      Scheme.Modules.affinePullbackUnitTop c Q
        ((quotientDifferentialSection (k := k) f π n J hJ q).val.app (.op ⊤) (1 : Γ(Y, ⊤)))
    FlatSectionKernel.sectionKernel (R := B) (𝟙 (Spec B)) M μ =
      affineCompositeQuotientKernel B f (c ≫ π) n (J.comap c)
        (hJ.comap_of_smooth (π ≫ f) c) q := by
  let : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
  let Q := quotient (k := k) f π n J hJ q
  let δ : Scheme.Modules.unitObj Y ⟶ Q := quotientDifferentialSection (k := k) f π n J hJ q
  exact pullbackSectionKernel_eq_of_zero_iff B c Q δ
    (affineCompositeQuotientKernel B f (c ≫ π) n (J.comap c)
      (hJ.comap_of_smooth (π ≫ f) c) q)
    (fun b => (pulledQuotientDifferentialSection_apply_eq_zero_iff_openComposite
      f π n c J hJ q ((Scheme.ΓSpecIso B).inv.hom b)).trans
        (mem_affineCompositeQuotientKernel_iff B f (c ≫ π) n (J.comap c)
          (hJ.comap_of_smooth (π ≫ f) c) q b).symm)

/-- On an actual affine source open, the intrinsic entire section kernel of the
SAME pulled GLOBAL original quotient is its original rounded ideal colon the
SAME original relative differential determinant. The only morphism equality
records the actual original affine source factorization. -/
theorem sourceAffineGlobalQuotient_sectionKernel_eq_jacobian_colon [CharZero k]
    (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    {Y : Scheme.{u}} (π : Y ⟶ Spec A)
    [SmoothOfRelativeDimension n (π ≫ CanonicalGeometry.affineStructuralMap k A)]
    (c : Spec B ⟶ Y) [IsOpenImmersion c]
    (hc : c ≫ π = Spec.map (CommRingCat.ofHom φ.toRingHom))
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    let f := CanonicalGeometry.affineStructuralMap k A
    letI : SmoothOfRelativeDimension n f :=
      smoothOfRelativeDimension_of_etale_coordinates z hz
    letI : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
    letI : Algebra A B := φ.toAlgebra
    let Q := quotient (k := k) f π n J hJ q
    let M := (Scheme.Modules.pullback c).obj Q
    let μ : AffineModuleFlatBaseChange.sections (R := B) (𝟙 (Spec B)) M :=
      Scheme.Modules.affinePullbackUnitTop c Q
        ((quotientDifferentialSection (k := k) f π n J hJ q).val.app (.op ⊤) (1 : Γ(Y, ⊤)))
    FlatSectionKernel.sectionKernel (R := B) (𝟙 (Spec B)) M μ =
      (idealOfSpecSheaf (RoundedSncIdealSheaf.rounded (J.comap c)
        (hJ.comap_of_smooth (π ≫ f) c) q)).colon
          {relativeDifferentialDet (etaleDifferentialBasis z hz) (etaleDifferentialBasis v hv)} := by
  intro f
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
  let : Algebra A B := φ.toAlgebra
  let JL := J.comap c
  let hJL := hJ.comap_of_smooth (π ≫ f) c
  have hglobal := globalQuotient_sourceKernel_eq_compositeKernel B f π n c J hJ q
  have hcomp := congrArg (fun γ : Spec B ⟶ Spec A =>
    affineCompositeQuotientKernel B f γ n JL hJL q) hc
  have hspec : affineCompositeQuotientKernel B f (Spec.map (CommRingCat.ofHom φ.toRingHom)) n JL hJL q =
      specQuotientKernel A B φ z hz JL hJL q :=
    affineCompositeQuotientKernel_eq_specQuotientKernel A B φ z hz JL hJL q
  exact hglobal.trans (hcomp.trans (hspec.trans
    (specQuotientKernel_eq_jacobian_colon (k := k) A B φ z hz JL hJL q v hv)))

end EnvelopeProperty.Char0.AffineOpenGlobalRoundedKernel
