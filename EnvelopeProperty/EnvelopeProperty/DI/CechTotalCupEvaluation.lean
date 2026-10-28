import EnvelopeProperty.DI.CechTotalCupZeroRow
import EnvelopeProperty.DI.CechWholeSectionLeibniz
import EnvelopeProperty.DI.AffineLocalMapRestriction

/-! # The SAME actual total cup under original zero-row and local evaluation -/
noncomputable section
namespace EnvelopeProperty.DI.CechTotalCup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Preadditive
open CechAlexanderWhitneyProduct
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieLocalContinuationCechAugmentation
open Cartier.DeligneIllusieCechCupProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
  (n : ℕ) [SmoothOfRelativeDimension n f]
  {ι : Type u} (U : ι → Scheme.Opens (Cartier.SchemeRelativeFrobenius.twist p f))
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "K" => Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q
local notation "C" => Cartier.DeligneIllusieLocalContinuationCechBicomplex.bicomplex U
  (Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n)
local notation "T" => Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex U
  (Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n)

private theorem selfCut {Z : Scheme.{u}} (V : Z.Opens) :
    V.ι ''ᵁ (V.ι ⁻¹ᵁ V) = V := by
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]

private theorem selfUnit_bijective {Z : Scheme.{u}} (M : Z.Modules) (V : Z.Opens) :
    Function.Bijective ((factorUnit M V).val.app (op V)) := by
  change Function.Bijective (M.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op)
  have h : (homOfLE (V.ι.image_preimage_le V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ V) ⟶ V) =
      eqToHom (selfCut V) := Subsingleton.elim _ _
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

private def selfUnitIso {Z : Scheme.{u}} (M : Z.Modules) (V : Z.Opens) :
    M.val.obj (op V) ≅ (factor M V).val.obj (op V) :=
  (LinearEquiv.ofBijective ((factorUnit M V).val.app (op V)).hom (selfUnit_bijective M V)).toModuleIso

/-- The actual native evaluation on original member sections, followed by the inverse ORIGINAL unit on the same open. -/
def memberEvaluation (a : ℕ) (i : ι) :
    Γ((T).X a,U i) →ₗ[Γ(Y,U i)] Γ((K).X a,U i) :=
  ((Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f a).val.app (op (U i)) |>.hom |>
    ((selfUnitIso ((K).X a) (U i)).inv.hom.comp)

private theorem memberEvaluation_unit (a : ℕ) (i : ι) (x : Γ((T).X a,U i)) :
    ((factorUnit ((K).X a) (U i)).val.app (op (U i))) (memberEvaluation f p n U a i x) =
      ((Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f a).val.app (op (U i)) x :=
  Iso.inv_hom_id_apply (selfUnitIso ((K).X a) (U i)) _

private theorem unit_wedge (a b : ℕ) (V W : (Y).Opens)
    (x : Γ(E a,W)) (y : Γ(E b,W)) :
    ((factorUnit (E (b+a)) V).val.app (op W)) (formWedge f p a b W x y) =
      factorWedge f p a b V W
        (((factorUnit (E a) V).val.app (op W)) x)
        (((factorUnit (E b) V).val.app (op W)) y) :=
  formWedge_restrict f p a b (homOfLE (V.ι.image_preimage_le W)) x y

private theorem unit_cast {a b : ℕ} (h : a=b) (V : (Y).Opens) (x : Γ(E a,V)) :
    ((factorUnit (E b) V).val.app (op V)) (CechWholeSectionLeibniz.degreeCast f p h V x) =
      (eqToHom (congrArg (fun q => factor (E q) V) h)).val.app (op V)
        (((factorUnit (E a) V).val.app (op V)) x) := by
  cases h
  rfl

/-- On EVERY pair of whole original member sections, native total cup evaluates to the SAME original form wedge. -/
theorem memberEvaluation_totalCupSection (a b : ℕ) (i : ι)
    (x : Γ((T).X a,U i)) (y : Γ((T).X b,U i)) :
    memberEvaluation f p n U (a+b) i (totalCupSection f p n U a b (U i) x y) =
      CechWholeSectionLeibniz.degreeCast f p (Nat.add_comm b a) (U i)
        (formWedge f p a b (U i) (memberEvaluation f p n U a i x) (memberEvaluation f p n U b i y)) := by
  apply (ConcreteCategory.bijective_of_isIso (selfUnitIso ((K).X (a+b)) (U i)).hom).1
  let α := (Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f a
  let β := (Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f b
  let γ := (Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f (a+b)
  let c := eqToHom (congrArg (fun q => factor (E q) (U i)) (Nat.add_comm b a))
  have hl : γ.val.app (op (U i)) (totalCupSection f p n U a b (U i) x y) =
      c.val.app (op (U i))
        (factorWedge f p a b (U i) (U i) (α.val.app (op (U i)) x) (β.val.app (op (U i)) y)) :=
    (congrArg (fun z => z.val.app (op (U i))
      (CanonicalGeometry.tensorSection ((T).X a) ((T).X b) (U i) x y))
        (totalCup_evaluation f p n U a b i)).trans
      (congrArg (c.val.app (op (U i))) (factorWedgeAlong_tensorSection f p a b (U i) (U i) α β x y))
  have hw := (unit_wedge f p a b (U i) (U i)
    (memberEvaluation f p n U a i x) (memberEvaluation f p n U b i y)).trans
      (congrArg₂ (fun z w => factorWedge f p a b (U i) (U i) z w)
        (memberEvaluation_unit f p n U a i x) (memberEvaluation_unit f p n U b i y))
  have hr := (unit_cast f p (Nat.add_comm b a) (U i)
    (formWedge f p a b (U i) (memberEvaluation f p n U a i x)
      (memberEvaluation f p n U b i y))).trans (congrArg (c.val.app (op (U i))) hw)
  exact (memberEvaluation_unit f p n U (a+b) i (totalCupSection f p n U a b (U i) x y)).trans
    (hl.trans hr.symm)

/-- The ORIGINAL restriction-top section unit, with its original image-open equality. -/
def originalLocalSection {Z : Scheme.{u}} (M : Z.Modules) (V : Z.Opens) (x : Γ(M,V)) :
    Γ(M.restrict V.ι, (⊤ : V.toScheme.Opens)) :=
  M.presheaf.map (eqToHom (show V.ι ''ᵁ (⊤ : V.toScheme.Opens) = V by simp)).op x

private theorem originalLocalSection_naturality {Z : Scheme.{u}} {M N : Z.Modules}
    (φ : M ⟶ N) (V : Z.Opens) (x : Γ(M,V)) :
    ((Scheme.Modules.restrictFunctor V.ι).map φ).val.app (op (⊤ : V.toScheme.Opens))
        (originalLocalSection M V x) = originalLocalSection N V (φ.val.app (op V) x) := by
  exact ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality
      (eqToHom (show V.ι ''ᵁ (⊤ : V.toScheme.Opens) = V by simp)).op) x

/-- Member evaluation is literally the native localEvaluation, read through ORIGINAL restriction-top units. -/
theorem memberEvaluation_native (a : ℕ) (i : ι) (x : Γ((T).X a,U i)) :
    ((Cartier.DeligneIllusieCechTotalEvaluation.localEvaluation U (K) i).f a).val.app
        (op (⊤ : (U i).toScheme.Opens)) (originalLocalSection ((T).X a) (U i) x) =
      originalLocalSection ((K).X a) (U i) (memberEvaluation f p n U a i x) := by
  let V := U i
  let L := Scheme.Modules.restrictFunctor V.ι
  let α := (Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f a
  let η := factorUnit ((K).X a) V
  let ε := (Scheme.Modules.restrictAdjunction V.ι).counit.app (((K).X a).restrict V.ι)
  let z := memberEvaluation f p n U a i x
  have hα := originalLocalSection_naturality α V x
  have hη := originalLocalSection_naturality η V z
  have ht := congrArg
    (fun φ : L.obj ((K).X a) ⟶ L.obj ((K).X a) =>
      φ.val.app (op (⊤ : V.toScheme.Opens)) (originalLocalSection ((K).X a) V z))
    ((Scheme.Modules.restrictAdjunction V.ι).left_triangle_components ((K).X a))

  calc
    _ = ε.val.app (op (⊤ : V.toScheme.Opens))
        (originalLocalSection (factor ((K).X a) V) V (α.val.app (op V) x)) :=
      congrArg (ε.val.app (op (⊤ : V.toScheme.Opens))) hα
    _ = ε.val.app (op (⊤ : V.toScheme.Opens))
        (originalLocalSection (factor ((K).X a) V) V (η.val.app (op V) z)) :=
      congrArg (fun w => ε.val.app (op (⊤ : V.toScheme.Opens))
        (originalLocalSection (factor ((K).X a) V) V w))
          (memberEvaluation_unit f p n U a i x).symm
    _ = ε.val.app (op (⊤ : V.toScheme.Opens))
        ((L.map η).val.app (op (⊤ : V.toScheme.Opens)) (originalLocalSection ((K).X a) V z)) :=
      congrArg (ε.val.app (op (⊤ : V.toScheme.Opens))) hη.symm
    _ = _ := ht


section AffineReadback
variable {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V)
private abbrev originalSpectrumSections : (Spec (Z.presheaf.obj (op V))).Modules ⥤
    ModuleCat (Z.presheaf.obj (op V)) := moduleSpecΓFunctor
local notation "γ" => originalSpectrumSections (V := V)
local notation "RI" => Scheme.Modules.restrictFunctor hV.isoSpec.inv
local notation "RJ" => Scheme.Modules.restrictFunctor hV.fromSpec
local notation "RL" => Scheme.Modules.restrictFunctor V.ι

private theorem readback_comp (M N P : Z.Modules)
    (φ : M.restrict V.ι ⟶ N.restrict V.ι) (ψ : N.restrict V.ι ⟶ P.restrict V.ι) :
    AffineLocalMapRestriction.sectionReadback hV M P (φ ≫ ψ) =
      AffineLocalMapRestriction.sectionReadback hV M N φ ≫
        AffineLocalMapRestriction.sectionReadback hV N P ψ := by
  simp only [AffineLocalMapRestriction.sectionReadback, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc]

private theorem readback_id (M : Z.Modules) :
    AffineLocalMapRestriction.sectionReadback hV M M (𝟙 (M.restrict V.ι)) = 𝟙 _ := by
  let r := AffineLocalMapRestriction.specReadbackIso hV M
  let e := Cartier.GeometricAffineHomology.moduleSectionsIso hV M
  have hi : r.inv ≫ (RI).map (𝟙 (M.restrict V.ι)) ≫ r.hom = 𝟙 (M.restrict hV.fromSpec) :=
    (congrArg (fun z => r.inv ≫ z ≫ r.hom) ((RI).map_id (M.restrict V.ι))).trans
      (by simp only [Category.id_comp, Iso.inv_hom_id])
  exact (congrArg (fun z => e.inv ≫ (γ).map z ≫ e.hom) hi).trans
    ((congrArg (fun z => e.inv ≫ z ≫ e.hom) ((γ).map_id (M.restrict hV.fromSpec))).trans
      (by simp only [Category.id_comp, Iso.inv_hom_id]))

private theorem specReadback_naturality {M N : Z.Modules} (φ : M ⟶ N) :
    (RI).map ((RL).map φ) ≫ (AffineLocalMapRestriction.specReadbackIso hV N).hom =
      (AffineLocalMapRestriction.specReadbackIso hV M).hom ≫ (RJ).map φ := by
  change (RI).map ((RL).map φ) ≫
      ((RI).map (AffineLocalMapRestriction.chartRestrictionIso hV N).hom ≫
        (AffineLocalMapRestriction.specReturn hV).hom.app ((RJ).obj N)) =
    ((RI).map (AffineLocalMapRestriction.chartRestrictionIso hV M).hom ≫
      (AffineLocalMapRestriction.specReturn hV).hom.app ((RJ).obj M)) ≫ (RJ).map φ
  rw [← Category.assoc, ← Functor.map_comp,
    AffineLocalMapRestriction.chartRestriction_naturality, Functor.map_comp, Category.assoc]
  exact (congrArg (fun t => (RI).map (AffineLocalMapRestriction.chartRestrictionIso hV M).hom ≫ t)
    ((AffineLocalMapRestriction.specReturn hV).hom.naturality ((RJ).map φ))).trans
      (Category.assoc _ _ _).symm

private theorem readback_restrict (M N : Z.Modules) (φ : M ⟶ N) :
    AffineLocalMapRestriction.sectionReadback hV M N ((RL).map φ) = φ.val.app (op V) := by
  let rM := AffineLocalMapRestriction.specReadbackIso hV M
  let rN := AffineLocalMapRestriction.specReadbackIso hV N
  let eM := Cartier.GeometricAffineHomology.moduleSectionsIso hV M
  let eN := Cartier.GeometricAffineHomology.moduleSectionsIso hV N
  have hi : rM.inv ≫ (RI).map ((RL).map φ) ≫ rN.hom = (RJ).map φ :=
    (congrArg (fun z => rM.inv ≫ z) (specReadback_naturality hV φ)).trans (rM.inv_hom_id_assoc _)
  have hΓ := congrArg (fun z => eM.inv ≫ (γ).map z ≫ eN.hom) hi
  have hn := AffineLocalMapRestriction.moduleSections_naturality hV M N φ
  exact hΓ.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun z => eM.inv ≫ z) hn).trans (eM.inv_hom_id_assoc _)))

private theorem readback_counit (N : Z.Modules) :
    AffineLocalMapRestriction.sectionReadback hV (factor N V) N
      ((Scheme.Modules.restrictAdjunction V.ι).counit.app (N.restrict V.ι)) = (selfUnitIso N V).inv := by
  let η := factorUnit N V
  let ε := (Scheme.Modules.restrictAdjunction V.ι).counit.app (N.restrict V.ι)
  have hread := congrArg (AffineLocalMapRestriction.sectionReadback hV N N)
    ((Scheme.Modules.restrictAdjunction V.ι).left_triangle_components N)
  have hc := readback_comp hV N (factor N V) N ((RL).map η) ε
  have hr := readback_restrict hV N (factor N V) η
  have hi := readback_id hV N
  have hwhole : η.val.app (op V) ≫
      AffineLocalMapRestriction.sectionReadback hV (factor N V) N ε = 𝟙 _ :=
    (congrArg (fun z => z ≫ AffineLocalMapRestriction.sectionReadback hV (factor N V) N ε) hr.symm).trans
      (hc.symm.trans (hread.trans hi))
  apply (cancel_epi (selfUnitIso N V).hom).mp
  exact hwhole.trans (selfUnitIso N V).hom_inv_id.symm
end AffineReadback

/-- Exact ORIGINAL affine readback of a globally supplied map followed by the LITERAL native local evaluation. -/
theorem memberEvaluation_sectionReadback (a : ℕ) (i : ι) (hUi : IsAffineOpen (U i))
    (M : (Y).Modules) (φ : M ⟶ (T).X a) :
    (memberEvaluation f p n U a i).comp (φ.val.app (op (U i))).hom =
      (AffineLocalMapRestriction.sectionReadback hUi M ((K).X a)
        ((Scheme.Modules.restrictFunctor (U i).ι).map φ ≫
          (Cartier.DeligneIllusieCechTotalEvaluation.localEvaluation U (K) i).f a)).hom := by
  let V := U i
  let L := Scheme.Modules.restrictFunctor V.ι
  let α := (Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f a
  let ε := (Scheme.Modules.restrictAdjunction V.ι).counit.app (((K).X a).restrict V.ι)
  have heval : L.map φ ≫ (Cartier.DeligneIllusieCechTotalEvaluation.localEvaluation U (K) i).f a =
      L.map (φ ≫ α) ≫ ε := by
    change L.map φ ≫ (L.map α ≫ ε) = _
    rw [Functor.map_comp, Category.assoc]
  have hwhole : AffineLocalMapRestriction.sectionReadback hUi M ((K).X a)
      (L.map φ ≫ (Cartier.DeligneIllusieCechTotalEvaluation.localEvaluation U (K) i).f a) =
      (φ ≫ α).val.app (op V) ≫ (selfUnitIso ((K).X a) V).inv :=
    (congrArg (AffineLocalMapRestriction.sectionReadback hUi M ((K).X a)) heval).trans
      ((readback_comp hUi M (factor ((K).X a) V) ((K).X a) (L.map (φ ≫ α)) ε).trans
        (congrArg₂ (fun x y => x ≫ y) (readback_restrict hUi M (factor ((K).X a) V) (φ ≫ α))
          (readback_counit hUi ((K).X a))))
  exact congrArg ModuleCat.Hom.hom hwhole.symm

end EnvelopeProperty.DI.CechTotalCup
