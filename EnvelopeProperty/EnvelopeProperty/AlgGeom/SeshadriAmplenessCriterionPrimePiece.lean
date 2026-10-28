import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionPrimeDescent
import EnvelopeProperty.AlgGeom.ProjectiveCoherentLineSubobject

/-! # Actual coherent line prime-pieces in the original projective module

The original associated-point descent and the original projective integral
line-subobject producer are composed through the actual canonical closed
unit. The original pushed-forward line is genuinely nonzero and coherent.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

private theorem isProjective_closedComp {Z X Y : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Y) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  refine ⟨E, hE, hEF, i ≫ j, inferInstance, ?_⟩
  exact (Category.assoc i j E.projectiveBundleπ).trans
    (congrArg (fun q => i ≫ q) hjp)

/-- The actual original nonzero coherent module contains the actual nonzero
closed pushforward of an internally constructed invertible line on the SAME
original reduced point closure. -/
theorem exists_nonzero_coherent_line_primePiece
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hF : ¬ IsZero F) :
    ∃ eta : X,
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      ∃ T : I.subscheme.Modules, IsInvertible T ∧
        let P := (Scheme.Modules.pushforward I.subschemeι).obj T
        P.IsQuasicoherent ∧ P.IsFiniteType ∧
        ¬ Subsingleton (P.presheaf.stalk eta) ∧ ∃ a : P ⟶ F, Mono a := by
  classical
  obtain ⟨eta, K, a, hKQC, hKFT, ha, hunit, hNQC, hNFT, hNnz, hZ, hgeneric⟩ :=
    exists_nonzero_coherent_pointClosure_descent p F hF
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
  let Z := I.subscheme
  let i : Z ⟶ X := I.subschemeι
  let N : Z.Modules := (Scheme.Modules.pullback i).obj K
  let z : Z := SchemePointClosureIntegral.pointClosureLift eta
  let : IsIntegral Z := hZ
  let : N.IsQuasicoherent := hNQC
  let : N.IsFiniteType := hNFT
  let : IsProjective (i ≫ p) := isProjective_closedComp i p
  have hzg : z = genericPoint Z := hgeneric.eq (genericPoint_spec Z)
  have hNg : ¬ Subsingleton (N.presheaf.stalk (genericPoint Z)) := by
    rw [← hzg]
    exact hNnz
  have hNg' : ∃ m : N.presheaf.stalk (genericPoint Z), m ≠ 0 := by
    by_contra hz
    push Not at hz
    exact hNg ⟨fun m n => (hz m).trans (hz n).symm⟩
  obtain ⟨T, hT, v, hv⟩ :=
    ProjectiveCoherentLineSubobject.exists_invertible_mono_of_isProjective (i ≫ p) N hNg'
  let G : Z.Modules ⥤ X.Modules := Scheme.Modules.pushforward i
  let P : X.Modules := G.obj T
  let ua : K ⟶ G.obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app K
  let eK : K ≅ G.obj N := @asIso X.Modules inferInstance _ _ ua hunit
  let : PreservesLimits G :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).rightAdjoint_preservesLimits
  have hmap : Mono (G.map v) :=
    @CategoryTheory.preserves_mono_of_preservesLimit Z.Modules X.Modules
      inferInstance inferInstance G _ _ v inferInstance hv
  let w : P ⟶ F := G.map v ≫ eK.inv ≫ a
  have hw : Mono w := mono_comp' hmap (mono_comp' (inferInstance : Mono eK.inv) ha)
  let : T.IsQuasicoherent := hT.isQuasicoherent
  have hFP : T.IsFinitePresentation := hT.isFinitePresentation
  let : T.IsFiniteType :=
    @SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _ _ _ Z.ringCatSheaf _ _ T hFP
  have hPQC : P.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom i
  have hPFT : P.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion i
  obtain ⟨U, hU, ⟨eU⟩⟩ :=
    (CanonicalGeometry.invertibleLineAtlas T hT).exists_generic_frame
  let : Nonempty U := ⟨⟨genericPoint Z, hU⟩⟩
  have hTz : ∃ t : T.presheaf.stalk z, t ≠ 0 := by
    rw [hzg]
    exact ⟨CanonicalGeometry.genericFrameGenerator eU,
      CanonicalGeometry.genericFrameGenerator_ne_zero eU⟩
  let q := T.presheaf.stalkPushforward AddCommGrpCat i.base z
  have hq : IsIso q :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing T.presheaf z
  let eP : P.presheaf.stalk eta ≅ T.presheaf.stalk z :=
    @asIso AddCommGrpCat.{u} inferInstance _ _ q hq
  obtain ⟨t, ht⟩ := hTz
  have htP : eP.inv t ≠ 0 := by
    intro hz
    apply ht
    apply ((ConcreteCategory.isIso_iff_bijective eP.inv).mp inferInstance).injective
    exact hz.trans eP.inv.hom.map_zero.symm
  refine ⟨eta, T, hT, hPQC, hPFT, ?_, w, hw⟩
  intro hzero
  exact htP (hzero.elim _ _)

#check @exists_nonzero_coherent_line_primePiece
#print axioms exists_nonzero_coherent_line_primePiece

end EnvelopeProperty.SeshadriAmplenessCriterion
