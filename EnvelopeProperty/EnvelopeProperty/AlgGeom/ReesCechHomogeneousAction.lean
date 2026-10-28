import EnvelopeProperty.AlgGeom.ReesCechDegreeInclusions
import EnvelopeProperty.AlgGeom.ReesCechHomogeneousMultiplication
import EnvelopeProperty.AlgGeom.ReesCechHomologyModule
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # The genuine original homogeneous scalar action on the Rees complex -/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open scoped Polynomial DirectSum
noncomputable section
universe u
namespace EnvelopeProperty.FcReesCechHomogeneousAction

open FcReesCechDegreeComplex FcReesFormalRestriction

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual original Rees coefficient map preserves the entire original
homogeneous monomial, with its actual extended coefficient. -/
theorem chartCoefficient_monomial {V : X.Opens} (hV : IsAffineOpen V)
    {e : ℕ} (a : ↥(I ^ e)) :
    letI := chartAlgebra f hV
    FcReesFormalChartSheaf.reesCoefficient I f hV
        (FormalFunctionsReesMultiplication.monomial I e a) =
      FormalFunctionsReesMultiplication.monomial
        (I.map (chartCoefficient f hV)) e
        (FormalFunctionsReesMultiplication.mappedPower I a) := by
  let := chartAlgebra f hV
  apply Subtype.ext
  exact Polynomial.map_monomial _

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- The inverse of the WHOLE actual degree decomposition takes each actual
original summand to precisely its literal homogeneous original chart monomial. -/
theorem termPowerEquiv_symm_lof (d n : ℕ) (x : degreeTerm I f U hU d n)
    (i : OrderedCechIndex ι n) :
    letI : ∀ j : OrderedCechIndex ι n,
        Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (j.1 a)) :=
      fun j => chartAlgebra f (IsAffineOpen.cechIntersection U hU n j.1)
    letI : ∀ k : ℕ, Module R (degreeTerm I f U hU k n) :=
      fun k => (degreeTerm I f U hU k n).isModule
    (((termPowerEquiv I f U hU n).symm
      (DirectSum.lof R ℕ (fun k => degreeTerm I f U hU k n) d x) i) :
        Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a))[X]) =
      Polynomial.monomial d (x i : Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a))) := by
  let : ∀ j : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (j.1 a)) :=
    fun j => chartAlgebra f (IsAffineOpen.cechIntersection U hU n j.1)
  let : ∀ k : ℕ, Module R (degreeTerm I f U hU k n) :=
    fun k => (degreeTerm I f U hU k n).isModule
  apply Polynomial.ext
  intro k
  have h := congrArg (fun y => (y k i : Γ(X, ∏ᶜ fun a : Fin (n + 1) => U (i.1 a))))
    ((termPowerEquiv I f U hU n).apply_symm_apply
      (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j n) d x))
  rw [termPowerEquiv_apply] at h
  refine h.trans ?_
  by_cases hk : k = d
  · subst k
    rw [DirectSum.lof_apply]
    simp only [Polynomial.coeff_monomial, ↓reduceIte]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk]
    simp only [Polynomial.coeff_monomial, if_neg (Ne.symm hk)]
    rfl

/-- The genuine global coefficient of an original homogeneous Rees monomial. -/
abbrev homogeneousScalar {e : ℕ} (a : ↥(I ^ e)) :
    Γ(Spec (.of (reesAlgebra I)), ⊤) :=
  (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv.hom
    (FormalFunctionsReesMultiplication.monomial I e a)

/-- On the ENTIRE original term, the actual homogeneous Rees scalar action
is literal original coefficient multiplication followed by the exact degree shift. -/
theorem term_homogeneous {e : ℕ} (a : ↥(I ^ e)) (d n : ℕ) :
    letI : ∀ k : ℕ, Module R (degreeTerm I f U hU k n) :=
      fun k => (degreeTerm I f U hU k n).isModule
    ModuleCat.ofHom (DirectSum.lof R ℕ (fun k => degreeTerm I f U hU k n) d) ≫
        (termPowerIso I f U hU n).inv ≫
        (ModuleCat.restrictScalars (baseScalar I)).map
          (homogeneousScalar I a • 𝟙 (FcReesCechChartSections.orderedChartModule I f U hU n)) ≫
        (termPowerIso I f U hU n).hom =
      FcReesCechHomogeneousMultiplication.termMultiply I f U hU a d n ≫
        ModuleCat.ofHom (DirectSum.lof R ℕ (fun k => degreeTerm I f U hU k n) (e + d)) := by
  let : ∀ j : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (j.1 b)) :=
    fun j => chartAlgebra f (IsAffineOpen.cechIntersection U hU n j.1)
  let : ∀ k : ℕ, Module R (degreeTerm I f U hU k n) :=
    fun k => (degreeTerm I f U hU k n).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply DirectSum.ext
  intro k
  funext i
  apply Subtype.ext
  have hs :
      ((((ModuleCat.restrictScalars (baseScalar I)).map
        (homogeneousScalar I a • 𝟙 (FcReesCechChartSections.orderedChartModule I f U hU n))).hom
        ((termPowerEquiv I f U hU n).symm
          (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j n) d x)) i) :
            Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (i.1 b))[X]) =
        Polynomial.monomial (e + d)
          (chartCoefficient f (IsAffineOpen.cechIntersection U hU n i.1) a *
            (x i : Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (i.1 b)))) := by
    change
      (FcReesFormalChartSheaf.reesCoefficient I f
          (IsAffineOpen.cechIntersection U hU n i.1)
          ((Scheme.ΓSpecIso (.of (reesAlgebra I))).hom (homogeneousScalar I a)) :
            Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (i.1 b))[X]) *
        (((termPowerEquiv I f U hU n).symm
          (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j n) d x) i) :
            Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (i.1 b))[X]) = _
    rw [termPowerEquiv_symm_lof]
    have hc : (Scheme.ΓSpecIso (.of (reesAlgebra I))).hom (homogeneousScalar I a) =
        FormalFunctionsReesMultiplication.monomial I e a :=
      (Scheme.ΓSpecIso (.of (reesAlgebra I))).commRingCatIsoToRingEquiv.apply_symm_apply _
    rw [hc, chartCoefficient_monomial]
    exact Polynomial.monomial_mul_monomial _ _ _ _
  change
    (termPowerEquiv I f U hU n
      (((ModuleCat.restrictScalars (baseScalar I)).map
        (homogeneousScalar I a • 𝟙 (FcReesCechChartSections.orderedChartModule I f U hU n))).hom
        ((termPowerEquiv I f U hU n).symm
          (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j n) d x))) k i :
            Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (i.1 b))) =
      (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j n) (e + d)
        ((FcReesCechHomogeneousMultiplication.termMultiply I f U hU a d n).hom x) k i :
          Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (i.1 b)))
  rw [termPowerEquiv_apply]
  change
    (↑(((ModuleCat.restrictScalars (baseScalar I)).map
      (homogeneousScalar I a • 𝟙 (FcReesCechChartSections.orderedChartModule I f U hU n))).hom
      ((termPowerEquiv I f U hU n).symm
        (DirectSum.lof R ℕ (fun j => degreeTerm I f U hU j n) d x)) i) :
          Γ(X, ∏ᶜ fun b : Fin (n + 1) => U (i.1 b))[X]).coeff k = _
  rw [hs]
  by_cases hk : k = e + d
  · subst k
    rw [DirectSum.lof_apply]
    simp only [Polynomial.coeff_monomial, ↓reduceIte]
    rfl
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk]
    simp only [Polynomial.coeff_monomial, if_neg (Ne.symm hk)]
    rfl

/-- Transport the genuine homogeneous coefficient action on the ACTUAL
original chart complex through its genuine whole degree comparison. -/
def gradedHomogeneous {e : ℕ} (a : ↥(I ^ e)) :
    gradedComplex I f U hU ⟶ gradedComplex I f U hU :=
  (chartDegreeComplexIso I f U hU).inv ≫
    ((ModuleCat.restrictScalars (baseScalar I)).mapHomologicalComplex (.up ℕ)).map
      (homogeneousScalar I a • 𝟙 (FcReesCechChartSections.chartComplex I f U hU)) ≫
    (chartDegreeComplexIso I f U hU).hom

/-- The ENTIRE actual original cochain summand has exactly the literal
homogeneous multiplication and exact original degree shift under the genuine action. -/
theorem degreeInclusion_homogeneous {e : ℕ} (a : ↥(I ^ e)) (d : ℕ) :
    FcReesCechDegreeInclusions.degreeInclusion I f U hU d ≫
        gradedHomogeneous I f U hU a =
      FcReesCechHomogeneousMultiplication.degreeMultiply I f U hU a d ≫
        FcReesCechDegreeInclusions.degreeInclusion I f U hU (e + d) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact term_homogeneous I f U hU a d n

private theorem comparison_comp {C : Type*} [Category C]
    {A B D E G : C} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ E} {d : E ⟶ D}
    {t : D ⟶ G} {z : E ⟶ G} (h : a ≫ b = c ≫ d) (hz : d ≫ t = z) :
    a ≫ b ≫ t = c ≫ z := by
  rw [← Category.assoc, h, Category.assoc, hz]

/-- Applying cohomology to the genuine homogeneous action preserves every
WHOLE original summand and gives precisely the literal degree-shift cohomology map. -/
theorem homologyInclusion_homogeneous {e : ℕ} (a : ↥(I ^ e)) (d n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (FcReesCechDegreeInclusions.degreeInclusion I f U hU d) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (gradedHomogeneous I f U hU a) ≫
      (FcReesCechDegreeHomology.gradedHomologyIso I f U hU n).hom =
    FcReesCechHomogeneousMultiplication.homologyMultiply I f U hU a d n ≫
      ModuleCat.ofHom (DirectSum.lof R ℕ
        (fun j => (degreeComplex I f U hU j).homology n) (e + d)) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n
  have h := congrArg (fun b => H.map b) (degreeInclusion_homogeneous I f U hU a d)
  have h' := (H.map_comp _ _).symm.trans (h.trans (H.map_comp _ _))
  exact comparison_comp h'
    (FcReesCechDegreeInclusions.homologyInclusion I f U hU (e + d) n)

private instance homologyFunctor_linear (S : Type u) [CommRing S] (n : ℕ) :
    Functor.Linear S (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (.up ℕ) n) where
  map_smul φ a := by
    have h :
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map (a • φ) =
          a • (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map φ := by
      apply ShortComplex.Hom.ext <;> rfl
    change ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map (a • φ)) =
      a • ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) n).map φ)
    rw [h]
    exact ShortComplex.homologyMap_smul _ a

private theorem conjugate_scalar {S C D : Type*} [CommRing S]
    [Category C] [Preadditive C] [CategoryTheory.Linear S C] [Category D]
    (F : C ⥤ D) {A B : C} {E : D} (e : A ≅ B) (t : F.obj B ≅ E) (a : S) :
    (F.mapIso e ≪≫ t).inv ≫ F.map (a • 𝟙 A) ≫ (F.mapIso e ≪≫ t).hom =
      t.inv ≫ F.map (a • 𝟙 B) ≫ t.hom := by
  have h : e.inv ≫ (a • 𝟙 A) ≫ e.hom = a • 𝟙 B := by simp
  calc
    _ = t.inv ≫ F.map (e.inv ≫ (a • 𝟙 A) ≫ e.hom) ≫ t.hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Functor.map_comp, Category.assoc]
    _ = _ := by rw [h]

/-- The genuine original structure-module homogeneous scalar becomes the
SAME actual homogeneous cochain action under the whole ordered degree comparison. -/
theorem ordered_homogeneous {e : ℕ} (a : ↥(I ^ e)) :
    (orderedDegreeComplexIso I f U hU).inv ≫
      ((ModuleCat.restrictScalars (baseScalar I)).mapHomologicalComplex (.up ℕ)).map
        (homogeneousScalar I a • 𝟙
          (orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
            (unitObj (FcReesFormalFamily.family I f))
            (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j))) ≫
      (orderedDegreeComplexIso I f U hU).hom = gradedHomogeneous I f U hU a :=
  conjugate_scalar _ (FcReesCechChartSections.orderedCechComplexIso I f U hU)
    (chartDegreeComplexIso I f U hU) (homogeneousScalar I a)

private abbrev originalComplex :=
  orderedBaseCechComplex (FcReesFormalFamily.familyProjection I f)
    (unitObj (FcReesFormalFamily.family I f))
    (fun j => FcReesFormalChartSheaf.projection I f ⁻¹ᵁ U j)

/-- Original structure-module cohomology compares with the WHOLE graded
complex cohomology before the actual direct-sum splitting. -/
def originalHomologyIso (n : ℕ) :
    (ModuleCat.restrictScalars (baseScalar I)).obj ((originalComplex I f U).homology n) ≅
      (gradedComplex I f U hU).homology n :=
  (FcReesCechHomologyModule.scalarHomologyIso I f U n).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).mapIso
      (orderedDegreeComplexIso I f U hU)

private theorem intertwine_conjugate {C : Type*} [Category C]
    {A B : C} (e : A ≅ B) {a : A ⟶ A} {b : B ⟶ B}
    (h : e.inv ≫ a ≫ e.hom = b) : a ≫ e.hom = e.hom ≫ b := by
  rw [← h, Iso.hom_inv_id_assoc]

private theorem square_comp {C : Type*} [Category C]
    {A B D : C} {a : A ⟶ A} {b : B ⟶ B} {d : D ⟶ D}
    {s : A ⟶ B} {t : B ⟶ D} (hs : a ≫ s = s ≫ b) (ht : b ≫ t = t ≫ d) :
    a ≫ (s ≫ t) = (s ≫ t) ≫ d := by
  rw [← Category.assoc, hs, Category.assoc, ht, Category.assoc]

/-- The genuine original coefficient action on WHOLE cohomology is the
actual homogeneous chart-complex action under the whole cohomology comparison. -/
theorem originalHomologyIso_homogeneous {e : ℕ} (a : ↥(I ^ e)) (n : ℕ) :
    (ModuleCat.restrictScalars (baseScalar I)).map
        (homogeneousScalar I a • 𝟙 ((originalComplex I f U).homology n)) ≫
        (originalHomologyIso I f U hU n).hom =
      (originalHomologyIso I f U hU n).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
          (gradedHomogeneous I f U hU a) := by
  let F := ModuleCat.restrictScalars (baseScalar I)
  let C := originalComplex I f U
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n
  let HG := HomologicalComplex.homologyFunctor
    (ModuleCat.{u} Γ(Spec (.of (reesAlgebra I)), ⊤)) (.up ℕ) n
  let μ : C ⟶ C := homogeneousScalar I a • 𝟙 C
  have hs : F.map (homogeneousScalar I a • 𝟙 (C.homology n)) ≫
      (FcReesCechHomologyModule.scalarHomologyIso I f U n).inv =
    (FcReesCechHomologyModule.scalarHomologyIso I f U n).inv ≫
      H.map ((F.mapHomologicalComplex (.up ℕ)).map μ) := by
    have h := ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map μ) F
    change F.map (HG.map μ) ≫ _ = _ at h
    have hμ : HG.map μ = homogeneousScalar I a • 𝟙 (C.homology n) :=
      (HG.map_smul (homogeneousScalar I a) (𝟙 C)).trans
        (congrArg (fun b => homogeneousScalar I a • b) (HG.map_id C))
    have h0 : F.map (HG.map μ) ≫
        (FcReesCechHomologyModule.scalarHomologyIso I f U n).inv =
      (FcReesCechHomologyModule.scalarHomologyIso I f U n).inv ≫
        H.map ((F.mapHomologicalComplex (.up ℕ)).map μ) := h
    exact (congrArg (fun b => F.map b ≫
      (FcReesCechHomologyModule.scalarHomologyIso I f U n).inv) hμ).symm.trans h0
  have hc := intertwine_conjugate (orderedDegreeComplexIso I f U hU)
    (ordered_homogeneous I f U hU a)
  have ht := congrArg (fun b => H.map b) hc
  have ht' := (H.map_comp _ _).symm.trans (ht.trans (H.map_comp _ _))
  exact square_comp hs ht'

/-- The ACTUAL transported finite Rees-module structure on the SAME original
cohomology direct sum has its literal homogeneous degree-shift action on EVERY
original cohomology class, with no graded-action hypothesis. -/
theorem reesModule_homogeneous {e : ℕ} (a : ↥(I ^ e)) (d n : ℕ)
    (x : (degreeComplex I f U hU d).homology n) :
    letI := FcReesCechHomologyModule.reesModule I f U hU n
    FormalFunctionsReesMultiplication.monomial I e a •
        DirectSum.lof R ℕ (fun j => (degreeComplex I f U hU j).homology n) d x =
      DirectSum.lof R ℕ (fun j => (degreeComplex I f U hU j).homology n) (e + d)
        ((FcReesCechHomogeneousMultiplication.homologyMultiply I f U hU a d n).hom x) := by
  let := FcReesCechHomologyModule.coefficientModule I f U hU n
  let := FcReesCechHomologyModule.reesModule I f U hU n
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n
  let E := FcReesCechHomologyModule.homologyEquiv I f U hU n
  let P := (originalHomologyIso I f U hU n).toLinearEquiv
  let Q := (FcReesCechDegreeHomology.gradedHomologyIso I f U hU n).toLinearEquiv
  let u : (gradedComplex I f U hU).homology n :=
    (H.map (FcReesCechDegreeInclusions.degreeInclusion I f U hU d)).hom x
  have he (y) : E y = Q (P y) := rfl
  have hu : Q u =
      DirectSum.lof R ℕ (fun j => (degreeComplex I f U hU j).homology n) d x :=
    congrArg (fun b => b.hom x)
      (FcReesCechDegreeInclusions.homologyInclusion I f U hU d n)
  have hi : E.symm
      (DirectSum.lof R ℕ (fun j => (degreeComplex I f U hU j).homology n) d x) = P.symm u := by
    apply E.injective
    rw [E.apply_symm_apply, he, P.apply_symm_apply]
    exact hu.symm
  have hs : P (homogeneousScalar I a • P.symm u) =
      (H.map (gradedHomogeneous I f U hU a)).hom u := by
    have h := congrArg (fun b => b.hom (P.symm u))
      (originalHomologyIso_homogeneous I f U hU a n)
    change P (homogeneousScalar I a • P.symm u) =
      (H.map (gradedHomogeneous I f U hU a)).hom (P (P.symm u)) at h
    simpa only [P.apply_symm_apply] using h
  have ht := congrArg (fun b => b.hom x)
    (homologyInclusion_homogeneous I f U hU a d n)
  rw [FcReesCechHomologyModule.reesModule_smul]
  change E (homogeneousScalar I a • E.symm
    (DirectSum.lof R ℕ (fun j => (degreeComplex I f U hU j).homology n) d x)) = _
  rw [hi, he, hs]
  exact ht

end EnvelopeProperty.FcReesCechHomogeneousAction
