import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralMap
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeTarget
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeSource
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # The actual original line is genuinely very ample near the original zero fibre -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeEmbedding
open ProjectiveCentralFiberSectionLifting GeneratedLineProjectiveMap
open GeneratedLineProjectiveAffineMap
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeTarget
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeSource
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding

/-- The ACTUAL original near-zero lifted map internally gives a genuine
native relative closed embedding and WHOLE original O(1) pullback for the SAME
original line. The original central H1 vanishing is still explicit. -/
theorem exists_veryAmple_near_zero
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsDominant p]
    (hp : IsProjectiveFactorization p) (L : Y.Modules) (hL : IsInvertible L)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj L).sheaf 1))
    {m : ℕ} (i₀ : zeroFiber p ⟶ DeJongAlterations.projectiveSpace k m)
    [IsClosedImmersion i₀]
    (hi₀ : i₀ ≫ DeJongAlterations.projectiveSpaceStructure k m =
      pullback.snd p (zeroMap k)) (j : Fin (m + 1))
    (E₀ : (Scheme.Modules.pullback i₀).obj (coordinateHyperplaneTwist (R := k) j 1) ≅
      (Scheme.Modules.pullback (zeroInclusion p)).obj L) :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
      let W := p ⁻¹ᵁ B
      SchemeLineAmpleness.IsVeryAmple (R := Γ(B.toScheme, ⊤))
        ((p ∣_ B) ≫ B.toScheme.toSpecΓ)
        ((Scheme.Modules.pullback W.ι).obj L) := by
  obtain ⟨a, _ha, G, hF, _hG, _hI, _E, _hcoords, g, hg, hsubset, hclosed⟩ :=
    ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralMap.exists_finite_generators_closed_neighborhood_with_twist
      p hp L hL h₀ i₀ hi₀ j E₀
  let U := p ⁻¹ᵁ PrimeSpectrum.basicOpen a
  let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
  let W := p ⁻¹ᵁ B
  let : IsAffine B.toScheme := by
    change IsAffineOpen B
    exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Polynomial k)) g
  let : Fintype G.I := hF
  let t : W.toScheme ⟶ U.toScheme := Y.homOfLE hsubset
  have ht : t ≫ U.ι = W.ι := Scheme.homOfLE_ι Y hsubset
  let : IsAffineHom t := baseOpenSourceFactor_isAffine p U B hsubset
  let hU := hL.pullback U.ι
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections t G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  let hH := hU.pullback t
  let Φ := projectiveMap (U.ι ≫ p) hU G
  let q := DeJongAlterations.projectiveSpaceStructure (Polynomial k) (Fintype.card G.I)
  have hf : Φ ≫ q = U.ι ≫ p := projectiveMap_structure (U.ι ≫ p) hU G
  let V := q ⁻¹ᵁ B
  let : IsClosedImmersion (Φ ∣_ V) := hclosed
  let e := baseOpenSourceIso p q U Φ hf B hsubset
  have he : e.hom ≫ (Φ ⁻¹ᵁ V).ι = t :=
    baseOpenSourceIso_inclusion p q U Φ hf B hsubset
  let A : CommRingCat.{u} := Γ(B.toScheme, ⊤)
  let r : Polynomial k →+* A := baseCoefficients (R := Polynomial k) B.ι
  let pg : W.toScheme ⟶ Spec A := (p ∣_ B) ≫ B.toScheme.isoSpec.hom
  let Ψ := projectiveMap (R := A) pg hH H
  let C := projectiveCoefficientMap (R := Polynomial k) (A := A) r (Fintype.card G.I)
  let ρ := coefficientOpenFactor B (Fintype.card G.I)
  have hbase : pg ≫ Spec.map (CommRingCat.ofHom (R := Polynomial k) (S := A) r) =
      t ≫ (U.ι ≫ p) := by
    have hb : B.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (R := Polynomial k) (S := A) r) = B.ι :=
      baseCoefficients_structure (R := Polynomial k) B.ι
    exact (Category.assoc (p ∣_ B) B.toScheme.isoSpec.hom (Spec.map (CommRingCat.ofHom (R := Polynomial k) (S := A) r))).trans
      ((congrArg (fun f => (p ∣_ B) ≫ f) hb).trans
        ((morphismRestrict_ι p B).trans
          ((congrArg (fun f => f ≫ p) ht).symm.trans (Category.assoc t U.ι p))))
  have hwhole : Ψ ≫ C = t ≫ Φ := by
    have hcoeff :=
      ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients.projectiveMap_comp_coefficient
        (R := Polynomial k) (A := A) r pg hH H
    have hsource :=
      ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorPullback.projectiveMap_pullback
        t (U.ι ≫ p) hU G
    exact hcoeff.trans
      ((congrArg (fun r => projectiveMap (R := Polynomial k) r hH H) hbase).trans hsource.symm)
  have hfactor : Ψ ≫ ρ = e.hom ≫ (Φ ∣_ V) := by
    have hρ : ρ ≫ V.ι = C := coefficientOpenFactor_inclusion B (Fintype.card G.I)
    have hres : (Φ ∣_ V) ≫ V.ι = (Φ ⁻¹ᵁ V).ι ≫ Φ := morphismRestrict_ι Φ V
    apply (cancel_mono V.ι).mp
    calc
      (Ψ ≫ ρ) ≫ V.ι = Ψ ≫ C :=
        (Category.assoc Ψ ρ V.ι).trans (congrArg (fun f => Ψ ≫ f) hρ)
      _ = t ≫ Φ := hwhole
      _ = (e.hom ≫ (Φ ∣_ V)) ≫ V.ι :=
        ((Category.assoc e.hom (Φ ∣_ V) V.ι).trans
          ((congrArg (fun f => e.hom ≫ f) hres).trans
            ((Category.assoc e.hom (Φ ⁻¹ᵁ V).ι Φ).symm.trans
              (congrArg (fun f => f ≫ Φ) he)))).symm
  have hρSeparated : IsSeparated ρ := coefficientOpenFactor_isSeparated B (Fintype.card G.I)
  have hcomposite : IsClosedImmersion (Ψ ≫ ρ) := hfactor.symm ▸
    (inferInstance : IsClosedImmersion (e.hom ≫ (Φ ∣_ V)))
  have hΨ : IsClosedImmersion Ψ :=
    @IsClosedImmersion.of_comp _ _ _ Ψ ρ hcomposite hρSeparated
  let : IsProper p := hp.isProper
  let : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  let z₀ := zeroMap k (IsLocalRing.closedPoint k)
  have hz₀ : z₀ ∈ B := by
    change (Polynomial.evalRingHom (0 : k)) g ∉ (IsLocalRing.closedPoint k).asIdeal
    rw [show IsLocalRing.closedPoint k = (⊥ : PrimeSpectrum k) from Subsingleton.elim _ _]
    exact hg
  obtain ⟨y, hy⟩ := p.surjective z₀
  have hyW : y ∈ W := by
    change p y ∈ B
    rw [hy]
    exact hz₀
  let : Nonempty W := ⟨⟨y, hyW⟩⟩
  let : IsIntegral W.toScheme := inferInstance
  let E := GeneratedLineProjectiveTwist.projectiveTwistIso (R := A) pg hH H 0 ≪≫
    frameFactorIso t U.ι W.ι ht L
  refine ⟨g, hg, Fintype.card G.I, Ψ, hΨ, ?_, ⟨E⟩⟩
  exact projectiveMap_structure (R := A) pg hH H

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeEmbedding
