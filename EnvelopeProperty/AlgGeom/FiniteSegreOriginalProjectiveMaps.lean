import EnvelopeProperty.AlgGeom.ProjectiveSegreNativeCoordinates

/-! # Actual finite original Segre projective maps and whole original tensor lines -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules Alterations Alterations.Geometry.Segre
open scoped Classical NNReal
noncomputable section
universe u
namespace EnvelopeProperty.FiniteSegreOriginalProjectiveMaps
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open ProjectiveSegrePullbackSections SchemeTensorSectionHoms
open SchemeGlobalSectionModelNormIsometries SchemeModuleIsoGlobalSections
open Berkovich RelativeSchemeValuedPoint
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual iterated original Segre target dimension, retaining every factor. -/
def dimension : {r : ℕ} → (Fin (r+1) → ℕ) → ℕ
  | 0,d => d 0
  | r+1,d => Alterations.Algebra.Segre.dimension (d 0) (dimension (fun j : Fin (r+1) => d j.succ))

/-- The actual target coordinate of EVERY tuple of original factor coordinates. -/
def index : {r : ℕ} → (d : Fin (r+1) → ℕ) → (∀ j,Fin (d j+1)) → Fin (dimension d+1)
  | 0,_,a => a 0
  | r+1,d,a => Alterations.Algebra.Segre.indexEquiv (d 0)
    (dimension (fun j : Fin (r+1) => d j.succ))
      (a 0,index (fun j : Fin (r+1) => d j.succ) (fun j => a j.succ))

/-- Actual finite Segre coordinates are in bijection with ALL original factor-coordinate tuples. -/
theorem index_bijective {r : ℕ} (d : Fin (r+1) → ℕ) : Function.Bijective (index d) := by
  induction r with
  | zero =>
    constructor
    · intro a b h
      funext j
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst j
      exact h
    · intro a
      exact ⟨Fin.cases a (fun j => Fin.elim0 j),rfl⟩
  | succ r ih =>
    have ht := ih (fun j : Fin (r+1) => d j.succ)
    constructor
    · intro a b h
      have hab := (Alterations.Algebra.Segre.indexEquiv (d 0)
        (dimension (fun j : Fin (r+1) => d j.succ))).injective h
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact congrArg Prod.fst hab
      · exact congrFun (ht.1 (congrArg Prod.snd hab)) j
    · intro z
      obtain ⟨⟨a,b⟩,he⟩ := (Alterations.Algebra.Segre.indexEquiv (d 0)
        (dimension (fun j : Fin (r+1) => d j.succ))).surjective z
      obtain ⟨t,ht⟩ := ht.2 b
      refine ⟨Fin.cases a t,?_⟩
      change Alterations.Algebra.Segre.indexEquiv _ _ (a,index _ t) = z
      rw [ht]
      exact he

/-- The genuine original finite Segre map together with its entire SAME base triangle. -/
def presentation : {r : ℕ} → (d : Fin (r+1) → ℕ) →
    (q : ∀ j,X ⟶ projectiveSpace k (d j)) → (p : X ⟶ Spec (.of k)) →
    (∀ j,q j ≫ projectiveSpaceStructure k (d j) = p) →
    {s : X ⟶ projectiveSpace k (dimension d) // s ≫ projectiveSpaceStructure k (dimension d) = p}
  | 0,_,q,_,hq => ⟨q 0,hq 0⟩
  | r+1,d,q,p,hq =>
    let e := presentation (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ)
    let h := (hq 0).trans e.property.symm
    ⟨ProjectiveSegrePullbackSections.morphism (q 0) e.val h,
      (ProjectiveSegrePullbackSections.morphism_structure (q 0) e.val h).trans (hq 0)⟩

/-- The actual original finite Segre morphism on the SAME unchanged original X. -/
def morphism {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (p : X ⟶ Spec (.of k)) (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p) :
    X ⟶ projectiveSpace k (dimension d) := (presentation d q p hq).val

/-- The entire original coefficient triangle is retained exactly. -/
theorem morphism_structure {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
    (p : X ⟶ Spec (.of k)) (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p) :
    morphism d q p hq ≫ projectiveSpaceStructure k (dimension d) = p :=
  (presentation d q p hq).property

/-- One actual original closed factor makes this SAME finite original Segre morphism a genuine closed embedding. -/
theorem morphism_isClosedImmersion {r : ℕ} (d : Fin (r+1) → ℕ)
    (q : ∀ j,X ⟶ projectiveSpace k (d j)) (p : X ⟶ Spec (.of k))
    (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p) [IsClosedImmersion (q 0)] :
    IsClosedImmersion (morphism d q p hq) := by
  cases r with
  | zero => exact inferInstanceAs (IsClosedImmersion (q 0))
  | succ r =>
    exact ProjectiveSegreNativeCoordinates.morphism_isClosedImmersion (q 0)
      (morphism (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ)) _

/-- The actual entire original tensor line of ALL original finite family factors. -/
def tensorLine : {r : ℕ} → (d : Fin (r+1) → ℕ) → (∀ j,X ⟶ projectiveSpace k (d j)) → X.Modules
  | 0,_,q => line (q 0)
  | r+1,d,q => line (q 0) ⊗ tensorLine (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ)

/-- The actual finite original tensor line is genuinely invertible. -/
theorem tensorLine_isInvertible {r : ℕ} (d : Fin (r+1) → ℕ)
    (q : ∀ j,X ⟶ projectiveSpace k (d j)) : IsInvertible (tensorLine d q) := by
  induction r with
  | zero => exact line_isInvertible (q 0)
  | succ r ih =>
    exact (line_isInvertible (q 0)).monoidalTensor
      (ih (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ))

/-- The actual WHOLE original tensor coordinate section for EVERY tuple of original coordinates. -/
def tensorCoordinate : {r : ℕ} → (d : Fin (r+1) → ℕ) →
    (q : ∀ j,X ⟶ projectiveSpace k (d j)) → (∀ j,Fin (d j+1)) → (unitObj X ⟶ tensorLine d q)
  | 0,_,q,a => coordinateSection (q 0) (a 0)
  | r+1,d,q,a => tensorSectionHom (coordinateSection (q 0) (a 0))
      (tensorCoordinate (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) (fun j => a j.succ))

/-- The genuine whole original O1 comparison is DERIVED for the SAME entire finite family. -/
def lineIso : {r : ℕ} → (d : Fin (r+1) → ℕ) → (q : ∀ j,X ⟶ projectiveSpace k (d j)) →
    (p : X ⟶ Spec (.of k)) → (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p) →
      line (morphism d q p hq) ≅ tensorLine d q
  | 0,_,_,_,_ => Iso.refl _
  | r+1,d,q,p,hq =>
      ProjectiveSegrePullbackSections.lineIso (q 0)
        (morphism (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ))
        ((hq 0).trans (morphism_structure _ _ p (fun j => hq j.succ)).symm) ≪≫
      (Iso.refl _ ⊗ᵢ lineIso (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ))

/-- EVERY actual original finite Segre coordinate becomes its SAME entire original tensor section. -/
theorem lineIso_coordinate {r : ℕ} (d : Fin (r+1) → ℕ)
    (q : ∀ j,X ⟶ projectiveSpace k (d j)) (p : X ⟶ Spec (.of k))
    (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p) (a : ∀ j,Fin (d j+1)) :
    coordinateSection (morphism d q p hq) (index d a) ≫ (lineIso d q p hq).hom =
      tensorCoordinate d q a := by
  induction r with
  | zero => exact Category.comp_id _
  | succ r ih =>
    change coordinateSection (ProjectiveSegrePullbackSections.morphism _ _ _)
      (Alterations.Algebra.Segre.indexEquiv _ _ (a 0,index _ (fun j => a j.succ))) ≫
      (ProjectiveSegrePullbackSections.lineIso _ _ _).hom ≫
        ((Iso.refl _).hom ⊗ₘ (lineIso _ _ p (fun j => hq j.succ)).hom) = _
    rw [← Category.assoc,ProjectiveSegrePullbackSections.lineIso_coordinate,tensorSectionHom_comp]
    simp only [Iso.refl_hom,Category.comp_id]
    rw [ih]
    rfl

variable {r : ℕ} (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ projectiveSpace k (d j))
  (p : X ⟶ Spec (.of k)) (hq : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)

/-- The DERIVED finite original Segre line iso identifies the ENTIRE original global section spaces. -/
def wholeSectionsEquiv : Γ(line (morphism d q p hq),⊤) ≃ Γ(tensorLine d q,⊤) :=
  moduleIsoTopEquiv (lineIso d q p hq)

variable {v : Valuation k ℝ≥0} [IsProper p] (hb : ∀ c,v c ≤ 1)
  (y : RelativeSchemeValuedPoint v p)

/-- EVERY actual whole original section retains its SAME true original proper-model norm. -/
theorem wholeSectionsNorm (s : Γ(line (morphism d q p hq),⊤)) :
    globalSectionNorm hb y (line (morphism d q p hq)) (line_isInvertible _) s =
      globalSectionNorm hb y (tensorLine d q) (tensorLine_isInvertible d q)
        (wholeSectionsEquiv d q p hq s) :=
  globalSectionNorm_moduleIso hb y (line_isInvertible _) (tensorLine_isInvertible d q)
    (lineIso d q p hq) s

/-- Every actual finite weighted WHOLE original section family retains its full norm evaluation and SAME weights. -/
theorem weightedNormEval (a : ℕ) (T : Finset (Γ(line (morphism d q p hq),⊤) × ℝ)) :
    SchemeGlobalSectionModelNormIsometries.weightedNormEval hb y a
      (line (morphism d q p hq)) (line_isInvertible _) T =
    SchemeGlobalSectionModelNormIsometries.weightedNormEval hb y a
      (tensorLine d q) (tensorLine_isInvertible d q)
      (T.image fun z => (wholeSectionsEquiv d q p hq z.1,z.2)) :=
  weightedNormEval_moduleIso hb y a (line_isInvertible _) (tensorLine_isInvertible d q)
    (lineIso d q p hq) T

/-- EVERY actual finite Segre coordinate norm is the actual product of ALL SAME original factor coordinate norms at EVERY native support, including zeros. -/
theorem coordinateNorm (a : ∀ j,Fin (d j+1)) :
    modelHomNorm hb y (isInvertible_unit (X := X)) (line_isInvertible _)
      (coordinateSection (morphism d q p hq) (index d a)) =
        ∏ j,modelHomNorm hb y (isInvertible_unit (X := X)) (line_isInvertible (q j))
          (coordinateSection (q j) (a j)) := by
  induction r with
  | zero =>
    rw [Fin.prod_univ_one]
    rfl
  | succ r ih =>
    change modelHomNorm hb y (isInvertible_unit (X := X)) (line_isInvertible _)
      (coordinateSection (ProjectiveSegrePullbackSections.morphism (q 0)
        (morphism (fun j : Fin (r+1) => d j.succ) (fun j => q j.succ) p (fun j => hq j.succ)) _)
        (Alterations.Algebra.Segre.indexEquiv _ _ (a 0,index _ (fun j => a j.succ)))) = _
    rw [ProjectiveSegrePullbackSections.coordinateNorm,ih]
    exact (Fin.prod_univ_succ (fun j : Fin (r+2) =>
      modelHomNorm hb y (isInvertible_unit (X := X)) (line_isInvertible (q j))
        (coordinateSection (q j) (a j)))).symm

end EnvelopeProperty.FiniteSegreOriginalProjectiveMaps
