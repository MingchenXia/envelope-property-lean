import EnvelopeProperty.Berkovich.SchemeLineSectionRatioNorms
import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms

/-! # Actual original local ratio sections have their same native fibre and model norm -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
open scoped NNReal
universe u
namespace EnvelopeProperty.SchemeLocalSectionRatioPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f
open SchemeLineSectionEvaluation SchemeSectionTensorDivision

private theorem unit_hom_ext {X : Scheme.{u}} {P : X.Modules} {a b : unitObj X ⟶ P}
    (h : sectionAtOne a = sectionAtOne b) : a = b := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply a.val i (1 : Γ(X,⊤))
  have hb := PresheafOfModules.naturality_apply b.val i (1 : Γ(X,⊤))
  change a.val.app V (X.presheaf.map i (1 : Γ(X,⊤))) = P.presheaf.map i (sectionAtOne a) at ha
  change b.val.app V (X.presheaf.map i (1 : Γ(X,⊤))) = P.presheaf.map i (sectionAtOne b) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun q => P.presheaf.map i q) h).trans hb.symm)

private theorem topSectionHom_sectionAtOne {X : Scheme.{u}} {P : X.Modules} (a : unitObj X ⟶ P) :
    Scheme.Modules.topSectionHom P (sectionAtOne a) = a := by
  apply unit_hom_ext
  exact Scheme.Modules.topSectionHom_app_top_apply_one P _

private theorem tensorRight_eq {X : Scheme.{u}} {M T : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ T) :
    tensorRight a b = SchemeTensorSectionHoms.tensorSectionHom a b := by
  have h := ModularCurves.topSectionHom_tensorSection M T (sectionAtOne a) (sectionAtOne b)
  rw [topSectionHom_sectionAtOne,topSectionHom_sectionAtOne] at h
  apply unit_hom_ext
  exact (sectionAtOne_tensorRight a b).trans
    ((Scheme.Modules.topSectionHom_app_top_apply_one (M ⊗ T) _).symm.trans (congrArg sectionAtOne h))

/-- Every actual native scheme pullback retains the entire original tensor of section maps. -/
theorem tensorRight_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {M T : X.Modules}
    (a : unitObj X ⟶ M) (b : unitObj X ⟶ T) :
    pullbackSectionHom f (tensorRight a b) ≫ (Functor.Monoidal.μIso (pullback f) M T).inv =
      tensorRight (pullbackSectionHom f a) (pullbackSectionHom f b) := by
  rw [tensorRight_eq,SchemeTensorSectionHoms.pullback_tensorSectionHom,← tensorRight_eq]

/-- The actual whole local section transported through the genuine composition triangle. -/
def sectionViaFactor {Y A N : Scheme.{u}} (q : Y ⟶ A) (j : A ⟶ N) (p : Y ⟶ N)
    (h : q ≫ j = p) {M : N.Modules} (s : unitObj A ⟶ (pullback j).obj M) :
    unitObj Y ⟶ (pullback p).obj M :=
  pullbackSectionHom q s ≫ (frameFactorIso q j p h M).hom

/-- True factor transport of the SAME original global section. -/
theorem sectionViaFactor_global {Y A N : Scheme.{u}} (q : Y ⟶ A) (j : A ⟶ N) (p : Y ⟶ N)
    (h : q ≫ j = p) {M : N.Modules} (s : unitObj N ⟶ M) :
    sectionViaFactor q j p h (pullbackSectionHom j s) = pullbackSectionHom p s := by
  subst p
  change pullbackSectionHom q (pullbackSectionHom j s) ≫ (pullbackComp q j).hom.app M =
    pullbackSectionHom (q ≫ j) s
  exact pullbackSectionHom_comp q j s

private theorem factor_tensorator {Y A N : Scheme.{u}} (q : Y ⟶ A) (j : A ⟶ N) (p : Y ⟶ N)
    (h : q ≫ j = p) (M T : N.Modules) :
    (Functor.Monoidal.μIso (pullback q) ((pullback j).obj M) ((pullback j).obj T)).inv ≫
      ((frameFactorIso q j p h M).hom ⊗ₘ (frameFactorIso q j p h T).hom) =
      (pullback q).map (Functor.Monoidal.μIso (pullback j) M T).hom ≫
        (frameFactorIso q j p h (M ⊗ T)).hom ≫
          (Functor.Monoidal.μIso (pullback p) M T).inv := by
  let c : pullback j ⋙ pullback q ≅ pullback p := pullbackComp q j ≪≫ pullbackCongr h
  have : (pullbackComp q j).hom.IsMonoidal := pullbackComp_hom_isMonoidal q j
  have : (pullbackCongr h).hom.IsMonoidal := by
    subst p
    change NatTrans.IsMonoidal (𝟙 (pullback (q ≫ j)))
    infer_instance
  have : c.hom.IsMonoidal := by dsimp only [c,Iso.trans_hom]; infer_instance
  have ht := NatTrans.IsMonoidal.tensor (τ := c.hom) M T
  apply (cancel_epi (Functor.Monoidal.μIso (pullback q) ((pullback j).obj M) ((pullback j).obj T)).hom).mp
  apply (cancel_mono (Functor.Monoidal.μIso (pullback p) M T).hom).mp
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.inv_hom_id,Category.comp_id]
  exact ht.symm

/-- Entire genuine local section factor transport preserves the original native tensorator. -/
theorem sectionViaFactor_tensor {Y A N : Scheme.{u}} (q : Y ⟶ A) (j : A ⟶ N) (p : Y ⟶ N)
    (h : q ≫ j = p) {M T : N.Modules}
    (a : unitObj A ⟶ (pullback j).obj M) (b : unitObj A ⟶ (pullback j).obj T) :
    tensorRight (sectionViaFactor q j p h a) (sectionViaFactor q j p h b) =
      sectionViaFactor q j p h (tensorRight a b ≫ (Functor.Monoidal.μIso (pullback j) M T).hom) ≫
        (Functor.Monoidal.μIso (pullback p) M T).inv := by
  rw [tensorRight_eq,sectionViaFactor,sectionViaFactor,← SchemeTensorSectionHoms.tensorSectionHom_comp,
    ← tensorRight_eq,← tensorRight_pullback]
  rw [Category.assoc,factor_tensorator]
  simp only [sectionViaFactor,pullbackSectionHom,Functor.map_comp,Category.assoc]

variable {A N : Scheme.{u}} (j : A ⟶ N) {M T : N.Modules}
    (eT : (pullback j).obj T ≅ unitObj A) (α : unitObj N ⟶ M ⊗ T) (β : unitObj N ⟶ T)

/-- The genuine original local denominator coefficient basic open. -/
def denominatorOpen : A.Opens :=
  A.basicOpen (SchemeLineSectionUnitFrames.frameScalar eT (pullbackSectionHom j β))

/-- Actual denominator invertibility on its genuine open, transported to the SAME original composite. -/
theorem denominatorPullback_isIso : IsIso (pullbackSectionHom ((denominatorOpen j eT β).ι ≫ j) β) := by
  let : IsIso (pullbackSectionHom (denominatorOpen j eT β).ι (pullbackSectionHom j β)) :=
    SchemeLineSectionUnitFrames.basicOpenSection_isIso eT (pullbackSectionHom j β)
  rw [← pullbackSectionHom_comp (denominatorOpen j eT β).ι j β]
  infer_instance

/-- The actual original M local section ratio on the same genuine denominator open. -/
def ratioOnDenominatorOpen : unitObj (denominatorOpen j eT β).toScheme ⟶
    (pullback ((denominatorOpen j eT β).ι ≫ j)).obj M :=
  let k := (denominatorOpen j eT β).ι ≫ j
  letI := denominatorPullback_isIso j eT β
  divide (pullbackSectionHom k α ≫ (Functor.Monoidal.μIso (pullback k) M T).inv)
    (asIso (pullbackSectionHom k β))

/-- Entire original numerator equals the true ratio tensor the same original denominator on the genuine open. -/
theorem ratioOnDenominatorOpen_tensor :
    let k := (denominatorOpen j eT β).ι ≫ j
    tensorRight (ratioOnDenominatorOpen j eT α β) (pullbackSectionHom k β) =
      pullbackSectionHom k α ≫ (Functor.Monoidal.μIso (pullback k) M T).inv := by
  let := denominatorPullback_isIso j eT β
  exact tensorRight_divide _ _

private theorem native_section_ne_zero_of_iso {N : Scheme.{u}} (x : N) {T : (Spec (N.residueField x)).Modules}
    (b : unitObj (Spec (N.residueField x)) ⟶ T) [IsIso b] : sectionAtOne b ≠ 0 := by
  intro hz
  have hv := congrArg (fun t : unitObj (Spec (N.residueField x)) ⟶ unitObj (Spec (N.residueField x)) =>
    t.val.app (op ⊤) (1 : Γ(Spec (N.residueField x),⊤))) (asIso b).hom_inv_id
  change ((asIso b).inv.val.app (op ⊤)).hom (sectionAtOne b) =
    (1 : Γ(Spec (N.residueField x),⊤)) at hv
  rw [hz,map_zero] at hv
  have hn := congrArg (Scheme.ΓSpecIso (N.residueField x)).hom.hom hv.symm
  rw [map_one,map_zero] at hn
  exact one_ne_zero hn

open Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {f : N ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ a, v a ≤ 1) (y : Berkovich.RelativeSchemeValuedPoint v f)

/-- Actual original denominator-open factorization internally derives the SAME denominator fibre nonvanishing and exact local/native ratio equality. -/
theorem ratioOnDenominatorOpen_native_eq (hT : IsInvertible T)
    (q : Spec (N.residueField y.1.point) ⟶ (denominatorOpen j eT β).toScheme)
    (hq : q ≫ ((denominatorOpen j eT β).ι ≫ j) = N.fromSpecResidueField y.1.point) :
    ∃ hβ : fibreSection y β ≠ 0,
      sectionAtOne (sectionViaFactor q ((denominatorOpen j eT β).ι ≫ j)
        (N.fromSpecResidueField y.1.point) hq (ratioOnDenominatorOpen j eT α β)) =
      fibreRatio hb y hT α β hβ := by
  let k := (denominatorOpen j eT β).ι ≫ j
  let : IsIso (pullbackSectionHom k β) := denominatorPullback_isIso j eT β
  let : IsIso (pullbackSectionHom (N.fromSpecResidueField y.1.point) β) := by
    rw [← sectionViaFactor_global q k _ hq β]
    change IsIso (((pullbackUnitIso q).inv ≫ (pullback q).map (pullbackSectionHom k β)) ≫
      (frameFactorIso q k (N.fromSpecResidueField y.1.point) hq T).hom)
    infer_instance
  have hβ : fibreSection y β ≠ 0 := native_section_ne_zero_of_iso y.1.point _
  refine ⟨hβ,?_⟩
  have ht : tensorRight
      (sectionViaFactor q k (N.fromSpecResidueField y.1.point) hq (ratioOnDenominatorOpen j eT α β))
      (pullbackSectionHom (N.fromSpecResidueField y.1.point) β) =
      pullbackSectionHom (N.fromSpecResidueField y.1.point) α ≫
        (Functor.Monoidal.μIso (pullback (N.fromSpecResidueField y.1.point)) M T).inv := by
    rw [← sectionViaFactor_global q k _ hq β,sectionViaFactor_tensor]
    have hr : tensorRight (ratioOnDenominatorOpen j eT α β) (pullbackSectionHom k β) ≫
        (Functor.Monoidal.μIso (pullback k) M T).hom = pullbackSectionHom k α := by
      rw [ratioOnDenominatorOpen_tensor,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [hr,sectionViaFactor_global]
  have hh := congrArg (fun a => divide a (asIso (pullbackSectionHom (N.fromSpecResidueField y.1.point) β))) ht
  have hd := divide_tensorRight
    (sectionViaFactor q k (N.fromSpecResidueField y.1.point) hq (ratioOnDenominatorOpen j eT α β))
    (asIso (pullbackSectionHom (N.fromSpecResidueField y.1.point) β))
  exact congrArg sectionAtOne (hd.symm.trans hh)

/-- The SAME actual original local ratio section has the true quotient model norm, with no local/native matching input. -/
theorem modelLineNorm_ratioOnDenominatorOpen (hM : IsInvertible M) (hT : IsInvertible T)
    (q : Spec (N.residueField y.1.point) ⟶ (denominatorOpen j eT β).toScheme)
    (hq : q ≫ ((denominatorOpen j eT β).ι ≫ j) = N.fromSpecResidueField y.1.point) :
    modelLineNorm hb y hM (sectionAtOne (sectionViaFactor q ((denominatorOpen j eT β).ι ≫ j)
      (N.fromSpecResidueField y.1.point) hq (ratioOnDenominatorOpen j eT α β))) =
      modelLineNorm hb y (hM.monoidalTensor hT) (fibreSection y α) /
        modelLineNorm hb y hT (fibreSection y β) := by
  obtain ⟨hβ,he⟩ := ratioOnDenominatorOpen_native_eq j eT α β hb y hT q hq
  rw [he]
  exact modelLineNorm_fibreRatio hb y hM hT α β hβ

end EnvelopeProperty.SchemeLocalSectionRatioPullback
