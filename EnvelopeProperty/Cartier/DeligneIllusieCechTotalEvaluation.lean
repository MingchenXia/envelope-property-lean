import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalQuasiIso
import EnvelopeProperty.AlgGeom.SchemeOpenRestrictionHomology

/-! # Evaluation of the original Cech total complex on a cover member -/

noncomputable section

namespace EnvelopeProperty.Cartier.DeligneIllusieCechTotalEvaluation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open DeligneIllusieLocalContinuationCechModules
open DeligneIllusieLocalContinuationCechAugmentation
open DeligneIllusieLocalContinuationCechBicomplex
open DeligneIllusieLocalContinuationCechTotalAugmentation

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (E : CochainComplex X.Modules ℕ)

private instance factorZero (V : X.Opens) : (factorFunctor V).PreservesZeroMorphisms where
  map_zero M N := by
    change (Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pushforward V.ι).map
      (0 : M ⟶ N) = 0
    exact Functor.map_zero _ _ _

private def totalProjection : totalComplex U E ⟶ augmentationColumn U E where
  f q := HomologicalComplex₂.πTotalUpNat (bicomplex U E) q 0 q
  comm' n m h := by
    change n + 1 = m at h
    subst m
    change HomologicalComplex₂.πTotalUpNat (bicomplex U E) n 0 n ≫ ((bicomplex U E).d n (n+1)).f 0 =
      (HomologicalComplex₂.total (bicomplex U E) (.up ℕ)).d n (n+1) ≫ HomologicalComplex₂.πTotalUpNat (bicomplex U E) (n+1) 0 (n+1)
    symm
    apply HomologicalComplex₂.total.hom_ext
    intro q r hqr
    change q + r = n at hqr
    subst n
    rw [← Category.assoc, HomologicalComplex₂.ιTotal_d_upNat (bicomplex U E) q r]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
    by_cases hr : r = 0
    · subst r
      simp [HomologicalComplex₂.ιTotal_πTotalUpNat]
    · simp [HomologicalComplex₂.ιTotal_πTotalUpNat, hr]

private theorem member_le_tuple (i : ι) :
    U i ≤ ∏ᶜ (fun _ : Fin 1 => U i) :=
  leOfHom (Pi.lift (fun _ : Fin 1 => 𝟙 (U i)))

/-- The original product projection followed by restriction to a cover member. -/
def component (M : X.Modules) (i : ι) :
    (complex M U).X 0 ⟶ factor M (U i) :=
  Pi.π (fun j : Fin 1 → ι => factor M (∏ᶜ fun k : Fin 1 => U (j k)))
      (fun _ => i) ≫
    factorMap M (member_le_tuple U i)

set_option backward.isDefEq.respectTransparency false in
private def columnEvaluation (i : ι) : augmentationColumn U E ⟶
    ((factorFunctor (U i)).mapHomologicalComplex (.up ℕ)).obj E where
  f q := component U (E.X q) i
  comm' n m _ := by
    change component U (E.X n) i ≫ (factorFunctor (U i)).map (E.d n m) =
      ((complexFunctor U).map (E.d n m)).f 0 ≫ component U (E.X m) i
    let V : X.Opens := ∏ᶜ (fun _ : Fin 1 => U i)
    let πM := Pi.π
      (fun j : Fin 1 → ι => factor (E.X n) (∏ᶜ fun k : Fin 1 => U (j k)))
      (fun _ => i)
    let πN := Pi.π
      (fun j : Fin 1 → ι => factor (E.X m) (∏ᶜ fun k : Fin 1 => U (j k)))
      (fun _ => i)
    let rM := factorMap (E.X n) (member_le_tuple U i)
    let rN := factorMap (E.X m) (member_le_tuple U i)
    let φ := E.d n m
    have hn : rM ≫ (factorFunctor (U i)).map φ =
        (factorFunctor V).map φ ≫ rN :=
      (factorPresheafMap φ).naturality (homOfLE (member_le_tuple U i)).op
    have hπ : ((complexFunctor U).map φ).f 0 ≫ πN =
        πM ≫ (factorFunctor V).map φ :=
      complexMap_pi U φ 0 (fun _ => i)
    change (πM ≫ rM) ≫ (factorFunctor (U i)).map φ =
      ((complexFunctor U).map φ).f 0 ≫ (πN ≫ rN)
    exact (Category.assoc πM rM ((factorFunctor (U i)).map φ)).trans
      ((congrArg (fun z => πM ≫ z) hn).trans
        (((Category.assoc πM ((factorFunctor V).map φ) rN).symm).trans
          ((congrArg (fun z => z ≫ rN) hπ.symm).trans
            (Category.assoc (((complexFunctor U).map φ).f 0) πN rN))))

/-- The actual total complex evaluates into the original pushforward-restriction
complex on a chosen member, without choosing new components or differentials. -/
def evaluation (i : ι) : totalComplex U E ⟶
    ((factorFunctor (U i)).mapHomologicalComplex (.up ℕ)).obj E :=
  totalProjection U E ≫ columnEvaluation U E i

/-- Its whole component is the original total projection, product projection,
and the actual restriction to the chosen cover member. -/
theorem evaluation_f (i : ι) (q : ℕ) :
    (evaluation U E i).f q =
      HomologicalComplex₂.πTotalUpNat (bicomplex U E) q 0 q ≫
        (Pi.π (fun j : Fin 1 → ι => factor (E.X q) (∏ᶜ fun k : Fin 1 => U (j k)))
            (fun _ => i) ≫
          factorMap (E.X q) (member_le_tuple U i)) := rfl

private theorem cancel_summand {C : Type*} [Category* C] {A B T D Z : C}
    (a : A ⟶ B) (i : B ⟶ T) (p : T ⟶ B) (b : B ⟶ D) (r : D ⟶ Z)
    (h : i ≫ p = 𝟙 B) :
    (a ≫ i) ≫ (p ≫ (b ≫ r)) = (a ≫ b) ≫ r := by
  simp only [Category.assoc]
  rw [← Category.assoc i p (b ≫ r), h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same augmentation followed by evaluation is the genuine original
restriction-adjunction unit in every degree. -/
theorem totalAugmentation_evaluation_f (i : ι) (q : ℕ) :
    (totalAugmentation U E ≫ evaluation U E i).f q = factorUnit (E.X q) (U i) := by
  let a : E.X q ⟶ ((bicomplex U E).X q).X 0 := augmentation U (E.X q)
  let t := HomologicalComplex₂.ιTotal (bicomplex U E) (.up ℕ) q 0 q rfl
  let p := HomologicalComplex₂.πTotalUpNat (bicomplex U E) q 0 q
  let b := Pi.π (fun j : Fin 1 → ι =>
    factor (E.X q) (∏ᶜ fun k : Fin 1 => U (j k))) (fun _ => i)
  let r := factorMap (E.X q) (member_le_tuple U i)
  have htp : t ≫ p = 𝟙 _ :=
    HomologicalComplex₂.ιTotal_πTotalUpNat_self (bicomplex U E) q 0
  have hab : a ≫ b = factorUnit (E.X q) (∏ᶜ fun _ : Fin 1 => U i) :=
    augmentation_pi U (E.X q) (fun _ : Fin 1 => i)
  change (a ≫ t) ≫ (p ≫ (b ≫ r)) = factorUnit (E.X q) (U i)
  exact (cancel_summand a t p b r htp).trans
    ((congrArg (fun z => z ≫ r) hab).trans
      (factorUnit_comp_factorMap (E.X q) (member_le_tuple U i)))

/-- Restrict the original evaluation and apply the actual adjunction counit.
No contraction or chosen comparison map is an input. -/
def localEvaluation (i : ι) :
    SchemeOpenRestrictionHomology.restrictedComplex (U i).ι (totalComplex U E) ⟶
      SchemeOpenRestrictionHomology.restrictedComplex (U i).ι E :=
  ((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex (.up ℕ)).map
      (evaluation U E i) ≫
    (NatTrans.mapHomologicalComplex (Scheme.Modules.restrictAdjunction (U i).ι).counit
      (.up ℕ)).app (SchemeOpenRestrictionHomology.restrictedComplex (U i).ι E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original augmentation is a section of the local evaluation. -/
theorem totalAugmentation_localEvaluation (i : ι) :
    ((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex (.up ℕ)).map
        (totalAugmentation U E) ≫ localEvaluation U E i = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  let L := Scheme.Modules.restrictFunctor (U i).ι
  change L.map ((totalAugmentation U E).f q) ≫
    (L.map ((evaluation U E i).f q) ≫
      (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (L.obj (E.X q))) = 𝟙 _
  have hunit : (totalAugmentation U E).f q ≫ (evaluation U E i).f q =
      factorUnit (E.X q) (U i) := totalAugmentation_evaluation_f U E i q
  have hm := congrArg (fun z => L.map z ≫
    (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (L.obj (E.X q))) hunit
  have ht := (Scheme.Modules.restrictAdjunction (U i).ι).left_triangle_components (E.X q)
  simpa only [Functor.map_comp, Category.assoc] using hm.trans ht

/-- Under the honest cover condition the original local evaluation is a
quasi-isomorphism, using the existing total augmentation theorem. -/
theorem localEvaluation_quasiIso (hU : ⨆ i, U i = ⊤) (i : ι) :
    QuasiIso (localEvaluation U E i) := by
  let L := Scheme.Modules.restrictFunctor (U i).ι
  let : L.PreservesHomology := SchemeOpenRestrictionHomology.preservesHomology (U i).ι
  let : QuasiIso (totalAugmentation U E) :=
    DeligneIllusieLocalContinuationCechTotalQuasiIso.totalAugmentation_quasiIso U E hU
  let a := (L.mapHomologicalComplex (.up ℕ)).map (totalAugmentation U E)
  let : QuasiIso a := inferInstance
  let idR : (L.mapHomologicalComplex (.up ℕ)).obj E ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj E := 𝟙 _
  let : IsIso idR := IsIso.id _
  have hid : QuasiIso idR := quasiIso_of_isIso idR
  apply (quasiIso_iff_comp_left a (localEvaluation U E i)).mp
  have he : a ≫ localEvaluation U E i = idR := totalAugmentation_localEvaluation U E i
  exact he.symm ▸ hid

end EnvelopeProperty.Cartier.DeligneIllusieCechTotalEvaluation
