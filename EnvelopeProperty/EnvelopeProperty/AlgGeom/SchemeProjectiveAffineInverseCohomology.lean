import EnvelopeProperty.AlgGeom.SchemeProjectiveSectionPositiveBasis
import EnvelopeProperty.AlgGeom.SchemeLineSectionFiniteProductOpens
import EnvelopeProperty.AlgGeom.SchemeLineSectionPowerInverseVanishing
import EnvelopeProperty.AlgGeom.SchemeOpenNestedCohomology
import EnvelopeProperty.AlgGeom.CompactSeparatedPushforwardQuasicoherent

/-! # Actual affine inverse-image vanishing from original global projective twists

The actual projective embedding internally refines original affine U by
positive-degree original section opens. Actual finite products identify
ALL native Cech intersections, original global twists prove their genuine
inverse-image higher H vanishing, and internally derived whole pushforward
quasicoherence on affine U makes the actual source Cech complex exact.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits (IsZero)
open MvPolynomial TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeProjectiveAffineInverseCohomology
open CanonicalGeometry SchemeLineSectionEvaluation SchemeModuleCechLineSectionLocalization
open SchemeProjectiveSectionPositiveBasis SchemeLineSectionFiniteProductOpens
open SchemeLineSectionPowerInverseVanishing SchemeOpenNestedCohomology
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual eventual GLOBAL higher H vanishing of F twisted by the SAME
original projective embedding line pulled to proper source Y implies ALL
ordinary positive H vanishing on the literal inverse image of EVERY original
affine base open. Every refinement, intersection, nested coefficient/module
comparison, native H bridge and pushforward QC producer is internal.
No LOCAL acyclicity, refinement or matching certificate is an input. -/
theorem projective_affine_inverseImage_H_succ_subsingleton
    {R : Type u} [CommRing R] {n : ℕ} {X Y : Scheme.{u}}
    (j : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion j]
    (f : Y ⟶ X) [IsProper f] (F : Y.Modules) [F.IsQuasicoherent]
    (hGlobal : ∀ r : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H
        (F ⊗ bundleTensorPower ((pullback f).obj (embeddingLine j)) m).sheaf (r + 1)))
    (U : X.affineOpens) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H (F.restrict (f ⁻¹ᵁ U.1).ι).sheaf (q + 1)) := by
  classical
  let p := DeJongAlterations.projectiveSpaceStructure R n
  let : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (j ≫ p)]
    infer_instance⟩
  let : Y.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (f ≫ j ≫ p)]
    infer_instance⟩
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ j ≫ p)
  let H := embeddingLine j
  let hH := embeddingLine_isInvertible j
  obtain ⟨I, hI, d, s, hd, hVa, hVU, hVcover⟩ := exists_finite_positive_sectionOpen_refinement j U
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let V (i : I) : X.Opens := sectionOpen _
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (d i)) (s i)
  let VU (i : I) : U.1.toScheme.Opens := U.1.ι ⁻¹ᵁ V i
  let : IsAffine U.1.toScheme := U.2
  let : U.1.toScheme.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from U.1.ι]
    infer_instance⟩
  have hUCover : IsOpenCover VU := by
    change (⨆ i, VU i) = ⊤
    apply top_le_iff.mp
    intro x _hx
    have hxU : U.1.ι x ∈ U.1 := x.2
    have hxV : U.1.ι x ∈ ⨆ i, V i := by rw [hVcover]; exact hxU
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxV
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  have hUAff (i : I) : IsAffineOpen (VU i) :=
    (hVa i).preimage_of_isOpenImmersion U.1.ι (by
      simpa only [Scheme.Opens.opensRange_ι] using hVU i)
  let YU := f ⁻¹ᵁ U.1
  let fU := f ∣_ U.1
  let FU := F.restrict YU.ι
  let : YU.toScheme.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from YU.ι]
    infer_instance⟩
  let : CompactSpace YU.toScheme := QuasiCompact.compactSpace_of_compactSpace fU
  let : FU.IsQuasicoherent := inferInstance
  let Q := (pushforward fU).obj FU
  let : Q.IsQuasicoherent := CompactSeparatedPushforwardQuasicoherent.isQuasicoherent_pushforward fU FU
  let W (i : I) : YU.toScheme.Opens := fU ⁻¹ᵁ VU i
  have hWCover : IsOpenCover W := fU.iSup_preimage_eq_top hUCover
  have hInter (a : ℕ) (i : Fin (a + 1) → I) (r : ℕ) :
      Subsingleton (CategoryTheory.Sheaf.H
        ((TopCat.Sheaf.restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (a + 1) => W (i k)).isOpenEmbedding).obj FU.sheaf) (r + 1)) := by
    let C : X.Opens := ∏ᶜ fun k : Fin (a + 1) => V (i k)
    let Z : YU.toScheme.Opens := ∏ᶜ fun k : Fin (a + 1) => W (i k)
    have hCaff : IsAffineOpen C := IsAffineOpen.cechIntersection V hVa a i
    have hCU : C ≤ U.1 :=
      (leOfHom (Limits.Pi.π (fun k : Fin (a + 1) => V (i k)) 0)).trans (hVU (i 0))
    have hZ : Z = YU.ι ⁻¹ᵁ f ⁻¹ᵁ C := by
      calc
        Z = fU ⁻¹ᵁ (∏ᶜ fun k : Fin (a + 1) => VU (i k)) :=
          (fU.preimage_cechIntersection VU a i).symm
        _ = fU ⁻¹ᵁ U.1.ι ⁻¹ᵁ C := congrArg (fun A => fU ⁻¹ᵁ A)
          (U.1.ι.preimage_cechIntersection V a i).symm
        _ = YU.ι ⁻¹ᵁ f ⁻¹ᵁ C := by
          change (f ∣_ U.1) ⁻¹ᵁ U.1.ι ⁻¹ᵁ C = YU.ι ⁻¹ᵁ f ⁻¹ᵁ C
          rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]
    let A := YU.ι ''ᵁ Z
    have hA : A = f ⁻¹ᵁ C := by
      rw [show A = YU.ι ''ᵁ Z from rfl, hZ,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      apply inf_eq_right.mpr
      exact fun y hy => hCU hy
    have hAcompact : IsCompact (A : Set Y) := by
      rw [hA]
      exact f.isCompact_preimage hCaff.isCompact
    let : CompactSpace A.toScheme := isCompact_iff_compactSpace.mp hAcompact
    let ds : Fin (a + 1) → ℕ := fun k => d (i k)
    let ss : ∀ k : Fin (a + 1), unitObj X ⟶ bundleTensorPower H (ds k) := fun k => s (i k)
    let t := tuplePowerSection H ds ss
    have hDegree : 0 < tupleSectionDegree ds := tupleSectionDegree_pos ds (fun k => hd (i k))
    have hProduct : sectionOpen _
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (tupleSectionDegree ds)) t = C :=
      tuplePowerSection_open H hH ds ss
    have hCoh := inverseImage_powerSection_H_succ_subsingleton f H hH F
      (tupleSectionDegree ds) hDegree t r (hGlobal r)
    have hDirect : Subsingleton (CategoryTheory.Sheaf.H (F.restrict A.ι).sheaf (r + 1)) := by
      have hOpen : (f ⁻¹ᵁ sectionOpen _
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH (tupleSectionDegree ds)) t) = A :=
        (congrArg (fun B => f ⁻¹ᵁ B) hProduct).trans hA.symm
      exact hOpen ▸ hCoh
    change Subsingleton (CategoryTheory.Sheaf.H (FU.restrict Z.ι).sheaf (r + 1))
    exact (nested_restrict_H_succ_iff_image F YU Z r).mpr hDirect
  have hBase : ((cechComplexFunctor VU).obj Q.sheaf.obj).ExactAt (q + 1) :=
    cechComplex_exactAt_succ_of_affine_openCover Q VU hUCover hUAff q (affine_subsingleton_H Q q)
  have hzBase : IsZero ((baseCechComplex (𝟙 U.1.toScheme) Q VU).homology (q + 1)) :=
    ((baseCechComplex_exactAt_iff (𝟙 U.1.toScheme) Q VU (q + 1)).mpr hBase).isZero_homology
  have hzOrdered : IsZero ((orderedBaseCechComplex (𝟙 U.1.toScheme) Q VU).homology (q + 1)) :=
    IsZero.of_iso hzBase (baseCechOrderedHomologyIso (𝟙 U.1.toScheme) Q VU (q + 1)).symm
  have hzWOrdered : IsZero ((orderedBaseCechComplex (fU ≫ 𝟙 U.1.toScheme) FU W).homology (q + 1)) :=
    IsZero.of_iso hzOrdered (HomologicalComplex.homologyMapIso
      (orderedBaseCechComplexPushforwardIso fU (𝟙 U.1.toScheme) FU VU) (q + 1))
  have hzW : IsZero ((baseCechComplex (fU ≫ 𝟙 U.1.toScheme) FU W).homology (q + 1)) :=
    IsZero.of_iso hzWOrdered (baseCechOrderedHomologyIso (fU ≫ 𝟙 U.1.toScheme) FU W (q + 1))
  have hNative := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hzW
  have hCech := (baseCechComplex_exactAt_iff (fU ≫ 𝟙 U.1.toScheme) FU W (q + 1)).mp hNative
  exact (TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    W FU.sheaf hWCover hInter q).mp hCech

end EnvelopeProperty.SchemeProjectiveAffineInverseCohomology
