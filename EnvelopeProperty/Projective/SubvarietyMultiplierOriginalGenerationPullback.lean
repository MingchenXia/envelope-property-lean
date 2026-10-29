import EnvelopeProperty.Projective.SubvarietyMultiplierOriginalGenerationCore

/-! # The literal pulled original homogeneous evaluation has the whole comap image -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CategoryTheory.MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierOriginalGenerationCore
open Scheme.Modules InvertibleSectionFamilyImage
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem imageIdeal_eq_of_epi_factor {X : Scheme.{u}} {N : X.Modules}
    [N.IsQuasicoherent] (a : N ⟶ unitObj X) (I : X.IdealSheafData)
    (p : N ⟶ I.toModules) [Epi p] (hp : p ≫ I.toModulesInclusion = a) :
    QuasicoherentImageIdeal.imageIdeal N a = I := by
  apply le_antisymm
  · exact (QuasicoherentImageFactorization.imageIdeal_le_iff_factor a I).mpr ⟨p, hp⟩
  · let J := QuasicoherentImageIdeal.imageIdeal N a
    let : StrongEpi p := strongEpi_of_epi p
    let F : StrongEpiMonoFactorisation a :=
      { I := I.toModules
        m := I.toModulesInclusion
        e := p
        fac := hp }
    let G : MonoFactorisation a :=
      { I := J.toModules
        m := J.toModulesInclusion
        e := QuasicoherentImageModule.imageFactor a
        fac := QuasicoherentImageModule.imageFactor_inclusion a }
    let l : I.toModules ⟶ J.toModules := F.toMonoIsImage.lift G
    have hl : l ≫ J.toModulesInclusion = I.toModulesInclusion :=
      F.toMonoIsImage.lift_fac G
    intro U c hc
    let z : Γ(I.toModules, U.1) := (I.toModulesSectionsEquiv U).symm ⟨c, hc⟩
    have hz := (J.toModulesSectionsEquiv U (l.val.app (op U.1) z)).property
    have he := congrArg (fun q : I.toModules ⟶ unitObj X =>
      q.val.app (op U.1) z) hl
    change (l.val.app (op U.1) z).1 = c at he
    exact he ▸ hz

/-- The pullback of the SAME original free-tensor-dual source is genuinely
quasicoherent: pullback preserves its actual coproduct of invertible modules. -/
theorem pullbackFreeTensorDual_isQuasicoherent {X Y : Scheme.{u}} (μ : Y ⟶ X)
    (L : X.Modules) (hL : IsInvertible L) (ι : Type u) [Finite ι] :
    ((Scheme.Modules.pullback μ).obj ((tensorRight (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) ι))).IsQuasicoherent := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let P := Scheme.Modules.pullback μ
  let : PreservesColimitsOfSize.{u,u} P :=
    (pullbackPushforwardAdjunction μ).leftAdjoint_preservesColimits
  let Q := ∐ (fun _ : Fin (Fintype.card ι) => P.obj (dualObj L))
  have hQ : Q.IsQuasicoherent := isQuasicoherent_coproduct
    (fun _ : Fin (Fintype.card ι) => P.obj (dualObj L))
    (fun _ => (hL.dual.pullback μ).isQuasicoherent)
  let e : P.obj ((tensorRight (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) ι)) ≅ Q :=
    P.mapIso (freeTensorDualIso hL ι) ≪≫ PreservesCoproduct.iso P (fun _ : ι => dualObj L) ≪≫
      Sigma.whiskerEquiv (Fintype.equivFin ι) (fun _ => Iso.refl (P.obj (dualObj L)))
  exact (isQuasicoherent Y).prop_of_iso e.symm hQ

/-- Actual whole image ideals commute with arbitrary genuine pullback of the
original map to the unit. The original native ideal-module epimorphism handles
nonflat maps; no matching image or desired comap certificate is supplied. -/
theorem pullbackEvaluation_imageIdeal {X Y : Scheme.{u}} (μ : Y ⟶ X)
    (M : X.Modules) [M.IsQuasicoherent] [((Scheme.Modules.pullback μ).obj M).IsQuasicoherent]
    (α : M ⟶ unitObj X)
    (I : X.IdealSheafData) (hi : QuasicoherentImageIdeal.imageIdeal M α = I) :
    QuasicoherentImageIdeal.imageIdeal ((Scheme.Modules.pullback μ).obj M)
      ((Scheme.Modules.pullback μ).map α ≫ (pullbackUnitIso μ).hom) = I.comap μ := by
  let p := ProjectiveBaseIdealEpimorphism.imageFactorOfEq α I hi
  let : Epi p := ProjectiveBaseIdealEpimorphism.imageFactorOfEq_epi α I hi
  let : (Scheme.Modules.pullback μ).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (pullbackPushforwardAdjunction μ)
  let : Epi (I.toModulesComapPullbackMap μ) := I.toModulesComapPullbackMap_epi μ
  let q : (Scheme.Modules.pullback μ).obj M ⟶ (I.comap μ).toModules :=
    (Scheme.Modules.pullback μ).map p ≫ I.toModulesComapPullbackMap μ
  let : Epi q := by dsimp only [q]; infer_instance
  have hunit : SheafOfModules.pullbackObjUnitToUnit μ.toRingCatSheafHom =
      (pullbackUnitIso μ).hom := rfl
  have hq : q ≫ (I.comap μ).toModulesInclusion =
      (Scheme.Modules.pullback μ).map α ≫ (pullbackUnitIso μ).hom := by
    dsimp only [q]
    rw [Category.assoc, I.toModulesComapPullbackMap_inclusion μ, hunit,
      ← Category.assoc, ← Functor.map_comp,
      ProjectiveBaseIdealEpimorphism.imageFactorOfEq_inclusion]
  exact imageIdeal_eq_of_epi_factor _ _ q hq

end EnvelopeProperty.ProjSubvariety.MultiplierOriginalGenerationCore
