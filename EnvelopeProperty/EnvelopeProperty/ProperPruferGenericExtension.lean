import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Actual proper extension from integral schemes with valuation-ring stalks

True valuative lifts at all original stalks spread to genuine partial maps.
Their generic equality and the real maximal rational-map domain construct the
whole extension, retaining both original scheme triangles.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty

/-- The actual whole generic restriction factors through every original stalk in the true domain. -/
theorem partialMap_fromFunctionField_eq_stalk_comp
    {X Y : Scheme.{u}} [IsIntegral X] (p : X.PartialMap Y)
    (x : X) (hx : x ∈ p.domain) :
    p.fromFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        p.fromSpecStalkOfMem hx := by
  dsimp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono p.domain.ι).mp
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    ((genericPoint_spec X).specializes (Set.mem_univ x))).symm

/-- Genuine properness lifts the actual generic map to each original valuation-ring stalk, retaining both entire triangles. -/
theorem proper_generic_stalkLift
    {X Y S : Scheme.{u}} [IsIntegral X] (sX : X ⟶ S) (f : Y ⟶ S) [IsProper f]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ f = X.fromSpecStalk (genericPoint X) ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ l : Spec (X.presheaf.stalk x) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ l = φ ∧
      l ≫ f = X.fromSpecStalk x ≫ sX := by
  have hdom : IsDomain (X.presheaf.stalk x) :=
    Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  let sq : ValuativeCommSq f := {
    R := X.presheaf.stalk x
    commRing := (X.presheaf.stalk x).commRing
    domain := hdom
    valuationRing := inferInstance
    K := X.functionField
    field := inferInstance
    algebra := inferInstance
    isFractionRing := inferInstance
    i₁ := φ
    i₂ := X.fromSpecStalk x ≫ sX
    commSq := ⟨by
      rw [hφ]
      rw [← Category.assoc]
      congr 1
      exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
        ((genericPoint_spec X).specializes (Set.mem_univ x))).symm⟩ }
  have hp : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hp
  let l := (Classical.choice (hp.1.1.1 sq)).default
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/-- Actual valuation-ring stalk lifts force the maximal domain of the SAME generic rational map to be the whole source. -/
theorem proper_generic_rationalMap_domain_eq_top
    {X Y S : Scheme.{u}} [IsIntegral X] (sX : X ⟶ S) (f : Y ⟶ S) [IsProper f]
    [∀ x : X, ValuationRing (X.presheaf.stalk x)]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ f = X.fromSpecStalk (genericPoint X) ≫ sX) :
    (Scheme.RationalMap.ofFunctionField sX f φ hφ).domain = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨l, hl₁, hl₂⟩ := proper_generic_stalkLift sX f φ hφ x
  let p := Scheme.PartialMap.ofFromSpecStalk sX f l hl₂
  have hx : x ∈ p.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX f l hl₂
  apply Scheme.RationalMap.mem_domain.mpr
  refine ⟨p, hx, ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_ofFunctionField,
    partialMap_fromFunctionField_eq_stalk_comp p x hx]
  change _ ≫ (Scheme.PartialMap.ofFromSpecStalk sX f l hl₂).fromSpecStalkOfMem hx = φ
  rw [Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
  exact hl₁

/-- A full-domain actual partial map has precisely the original whole generic restriction after inverting its true domain inclusion. -/
theorem partialMap_fromFunctionField_eq_invDomain_comp
    {X Y : Scheme.{u}} [IsIntegral X] (p : X.PartialMap Y) [IsIso p.domain.ι] :
    p.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ inv p.domain.ι ≫ p.hom := by
  have hη : genericPoint X ∈ p.domain :=
    (genericPoint_specializes _).mem_open p.domain.2 p.dense_domain.nonempty.choose_spec
  change p.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ p.hom = _
  rw [show X.fromSpecStalk (genericPoint X) =
    p.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ p.domain.ι from
      (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _).symm]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

/-- The actual generic-point morphism is dominant on the entire integral source. -/
theorem isDominant_fromSpecFunctionField {X : Scheme.{u}} [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  have hs : ({genericPoint X} : Set X) ⊆ Set.range (X.fromSpecStalk (genericPoint X)) := by
    intro x hx
    have hx' : x = genericPoint X := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)), Scheme.fromSpecStalk_closedPoint⟩
  constructor
  intro x
  apply closure_mono hs
  rw [(genericPoint_spec X).def]
  trivial

/-- True properness and actual valuation-ring stalks construct the UNIQUE whole extension, including its original base and generic triangles. -/
theorem existsUnique_proper_generic_extension
    {X Y S : Scheme.{u}} [IsIntegral X] [S.IsSeparated]
    (sX : X ⟶ S) (f : Y ⟶ S) [IsProper f]
    [∀ x : X, ValuationRing (X.presheaf.stalk x)]
    (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ f = X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃! g : X ⟶ Y, g ≫ f = sX ∧ X.fromSpecStalk (genericPoint X) ≫ g = φ := by
  let : Y.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from f]
    infer_instance⟩
  let r := Scheme.RationalMap.ofFunctionField sX f φ hφ
  let p := r.toPartialMap
  have hdom : p.domain = ⊤ := proper_generic_rationalMap_domain_eq_top sX f φ hφ
  have : IsIso p.domain.ι := by
    rw [hdom]
    change IsIso X.topIso.hom
    infer_instance
  let g := inv p.domain.ι ≫ p.hom
  have hpφ : p.fromFunctionField = φ := by
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      show p.toRationalMap = r from Scheme.RationalMap.toRationalMap_toPartialMap r]
    exact Scheme.RationalMap.fromFunctionField_ofFunctionField sX f φ hφ
  have hgen : X.fromSpecStalk (genericPoint X) ≫ g = φ :=
    (partialMap_fromFunctionField_eq_invDomain_comp p).symm.trans hpφ
  let := isDominant_fromSpecFunctionField (X := X)
  have hbase : g ≫ f = sX :=
    AlgebraicGeometry.ext_of_isDominant (X.fromSpecStalk (genericPoint X)) (by
      simpa only [Category.assoc, hφ] using congrArg (fun k => k ≫ f) hgen)
  refine ⟨g, ⟨hbase, hgen⟩, ?_⟩
  intro z hz
  exact AlgebraicGeometry.ext_of_isDominant (X.fromSpecStalk (genericPoint X)) (hz.2.trans hgen.symm)

end EnvelopeProperty
