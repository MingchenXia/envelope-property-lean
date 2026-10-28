import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationDualUnitLocalEnds

/-!
# Actual local unit and whole-functional compatibility for canonical dual pullback

The mathematical route is in owned
`closed-projective-dual-unit-coherence-mathematical-route.tex`.
No unit, scalar, functional, section or frame matching equation is assumed.
-/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.OriginalDualPullbackCoherence
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual local module comparison followed by the actual global unit map is the actual local unit comparison. -/
theorem localModuleComparison_unit (U : X.Opens) :
    (localPullbackModuleIso f (unitObj X) U).hom ≫
        (overEquiv (f ⁻¹ᵁ U)).functor.map
          ((pullbackUnitIso f).hom.over (f ⁻¹ᵁ U)) =
      (localPullbackUnitIso f U).hom := by
  let V := f ⁻¹ᵁ U
  let g := f ∣_ U
  let P := pullback g
  let S := pullbackSquareIso g U.ι V.ι f (morphismRestrict_ι f U)
  let a := P.map ((overFunctorEquiv U).hom.app (unitObj X))
  let b := P.map ((restrictFunctorIsoPullback U.ι).hom.app (unitObj X))
  let r := (restrictFunctorIsoPullback V.ι).inv.app ((pullback f).obj (unitObj X))
  let o := (overFunctorEquiv V).inv.app ((pullback f).obj (unitObj X))
  let q := (pullbackUnitIso f).hom
  let vq := (overEquiv V).functor.map (q.over V)
  let uU := (pullbackUnitIso U.ι).hom
  let uV := (pullbackUnitIso V.ι).hom
  let ug := (pullbackUnitIso g).hom
  have ht : r ≫ o ≫ vq = (pullback V.ι).map q ≫ uV :=
    localComparisonTarget_unit f U
  have hs : a ≫ b ≫ P.map uU = 𝟙 _ := localComparisonSource_unit f U
  have hm : S.hom.app (unitObj X) ≫ (pullback V.ι).map q ≫ uV = P.map uU ≫ ug :=
    ModularCurves.pullbackSquareIso_unitLow g U.ι V.ι f (morphismRestrict_ι f U)
  rw [localPullbackUnitIso_hom_eqP]
  change a ≫ b ≫ S.hom.app (unitObj X) ≫ r ≫ o ≫ vq = ug
  calc
    a ≫ b ≫ S.hom.app (unitObj X) ≫ r ≫ o ≫ vq =
        a ≫ b ≫ S.hom.app (unitObj X) ≫ ((pullback V.ι).map q ≫ uV) :=
      congrArg (fun t => a ≫ b ≫ S.hom.app (unitObj X) ≫ t) ht
    _ = a ≫ b ≫ (P.map uU ≫ ug) := congrArg (fun t => a ≫ b ≫ t) hm
    _ = (a ≫ b ≫ P.map uU) ≫ ug := by simp only [Category.assoc]
    _ = ug := by rw [hs, Category.id_comp]

/-- Local dual pullback of every actual whole functional is the literal actual pulled functional and unit comparison. -/
theorem localDualPullback_wholeHom {M : X.Modules} (q : M ⟶ unitObj X) (U : X.Opens) :
    localDualPullback f M U (q.over U) =
      ((pullback f).map q ≫ (pullbackUnitIso f).hom).over (f ⁻¹ᵁ U) := by
  let V := f ⁻¹ᵁ U
  let b := (pullback (f ∣_ U)).map ((overEquiv U).functor.map (q.over U))
  let eM := localPullbackModuleIso f M U
  let eO := localPullbackModuleIso f (unitObj X) U
  let vq := (overEquiv V).functor.map (((pullback f).map q).over V)
  let vu := (overEquiv V).functor.map ((pullbackUnitIso f).hom.over V)
  have hn : b ≫ eO.hom = eM.hom ≫ vq :=
    localPullbackModuleIso_naturalityD f q U
  have hu : eO.hom ≫ vu = (localPullbackUnitIso f U).hom :=
    localModuleComparison_unit f U
  apply (overEquiv V).functor.map_injective
  simp only [localDualPullback, Functor.FullyFaithful.map_preimage]
  change eM.inv ≫ b ≫ (localPullbackUnitIso f U).hom = _
  calc
    eM.inv ≫ b ≫ (localPullbackUnitIso f U).hom =
        eM.inv ≫ (b ≫ eO.hom) ≫ vu := by rw [← hu]; simp only [Category.assoc]
    _ = eM.inv ≫ (eM.hom ≫ vq) ≫ vu := by rw [hn]
    _ = (overEquiv V).functor.map
        (((pullback f).map q ≫ (pullbackUnitIso f).hom).over V) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      dsimp only [vq, vu, SheafOfModules.Hom.over]
      simp only [Functor.map_comp]

end EnvelopeProperty.OriginalDualPullbackCoherence

#check @EnvelopeProperty.OriginalDualPullbackCoherence.localModuleComparison_unit
#print axioms EnvelopeProperty.OriginalDualPullbackCoherence.localModuleComparison_unit
#check @EnvelopeProperty.OriginalDualPullbackCoherence.localDualPullback_wholeHom
#print axioms EnvelopeProperty.OriginalDualPullbackCoherence.localDualPullback_wholeHom
