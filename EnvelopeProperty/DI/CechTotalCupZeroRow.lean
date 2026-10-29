import EnvelopeProperty.DI.CechTotalCupComponents
import EnvelopeProperty.DI.CechTotalTensorExt
import EnvelopeProperty.Cartier.DeligneIllusieCechTotalEvaluation

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

private theorem projection_factor_congr (M : (Y).Modules) (V : (Y).Opens)
    {s t : Fin 1 → ι} (h : s = t)
    (hs : V ≤ ∏ᶜ fun a : Fin 1 => U (s a)) (ht : V ≤ ∏ᶜ fun a : Fin 1 => U (t a)) :
    Pi.π (fun v : Fin 1 → ι => factor M (∏ᶜ fun a : Fin 1 => U (v a))) s ≫ factorMap M hs =
      Pi.π (fun v : Fin 1 → ι => factor M (∏ᶜ fun a : Fin 1 => U (v a))) t ≫ factorMap M ht := by
  cases h
  rfl

private theorem prefix_zero (M : (Y).Modules) (i : Fin 1 → ι) :
    prefixProjection f p U M 0 0 i =
      Pi.π (fun t : Fin 1 → ι => factor M (∏ᶜ fun a : Fin 1 => U (t a))) i := by
  unfold prefixProjection
  have hi : i ∘ tuplePrefix 0 0 = i := by
    funext a
    rfl
  exact (projection_factor_congr f p U M (∏ᶜ fun a : Fin 1 => U (i a)) hi
    (tupleOpen_le_prefix U 0 0 i) (le_refl _)).trans
      (by rw [factorMap_id, Category.comp_id])

private theorem suffix_zero (M : (Y).Modules) (i : Fin 1 → ι) :
    suffixProjection f p U M 0 0 i =
      Pi.π (fun t : Fin 1 → ι => factor M (∏ᶜ fun a : Fin 1 => U (t a))) i := by
  unfold suffixProjection
  have hi : i ∘ tupleSuffix 0 0 = i := by
    funext a
    apply congrArg i
    apply Fin.ext
    exact Nat.zero_add _
  exact (projection_factor_congr f p U M (∏ᶜ fun a : Fin 1 => U (i a)) hi
    (tupleOpen_le_suffix U 0 0 i) (le_refl _)).trans
      (by rw [factorMap_id, Category.comp_id])

private theorem orderedCup_zero_pi (a b : ℕ) (i : Fin 1 → ι) :
    orderedCup f p U a b 0 0 ≫
      Pi.π (fun t : Fin 1 → ι => factor (E (b+a)) (∏ᶜ fun j : Fin 1 => U (t j))) i =
    factorWedgeAlong f p a b (∏ᶜ fun j : Fin 1 => U (i j))
      (Pi.π (fun t : Fin 1 → ι => factor (E a) (∏ᶜ fun j : Fin 1 => U (t j))) i)
      (Pi.π (fun t : Fin 1 → ι => factor (E b) (∏ᶜ fun j : Fin 1 => U (t j))) i) := by
  rw [cup_pi, prefix_zero, suffix_zero]

private theorem wedge_zero_left (a b : ℕ) (V : (Y).Opens) {A B : (Y).Modules}
    (β : B ⟶ factor (E b) V) :
    factorWedgeAlong f p a b V (0 : A ⟶ factor (E a) V) β = 0 := by
  apply tensorSection_hom_ext
  intro W x y
  rw [factorWedgeAlong_tensorSection]
  change factorWedge f p a b V W 0 (β.val.app (op W) y) = 0
  rw [map_zero, LinearMap.zero_apply]

private theorem wedge_zero_right (a b : ℕ) (V : (Y).Opens) {A B : (Y).Modules}
    (α : A ⟶ factor (E a) V) :
    factorWedgeAlong f p a b V α (0 : B ⟶ factor (E b) V) = 0 := by
  apply tensorSection_hom_ext
  intro W x y
  rw [factorWedgeAlong_tensorSection]
  change factorWedge f p a b V W (α.val.app (op W) x) 0 = 0
  exact map_zero _
private theorem ι_π_same (q j d : ℕ) (h : q+j=d) :
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q j d h ≫
      HomologicalComplex₂.πTotalUpNat (C) q j d = 𝟙 _ := by
  subst d
  exact HomologicalComplex₂.ιTotal_πTotalUpNat_self (C) q j

private theorem ι_π_form_ne (q j d : ℕ) (h : q+j=d) (r s : ℕ) (hne : q ≠ r) :
    HomologicalComplex₂.ιTotal (C) (.up ℕ) q j d h ≫
      HomologicalComplex₂.πTotalUpNat (C) r s d = 0 := by
  simpa only [dif_neg hne] using HomologicalComplex₂.ιTotal_πTotalUpNat (C) q j d h r s

private theorem cancel_middle {A B D F : (Y).Modules}
    (a : A ⟶ B) (i : B ⟶ D) (π : D ⟶ B) (b : B ⟶ F) (h : i ≫ π = 𝟙 B) :
    (a ≫ i) ≫ (π ≫ b) = a ≫ b := by
  simp only [Category.assoc]
  rw [← Category.assoc i π b, h, Category.id_comp]

private theorem cancel_prefix {A B D : (Y).Modules}
    (i : A ⟶ B) (π : B ⟶ A) (b : A ⟶ D) (h : i ≫ π = 𝟙 A) :
    i ≫ (π ≫ b) = b :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ b) h).trans (Category.id_comp b))

private theorem zero_middle {A B D F G : (Y).Modules}
    (a : A ⟶ B) (i : B ⟶ D) (π : D ⟶ F) (b : F ⟶ G) (h : i ≫ π = 0) :
    (a ≫ i) ≫ (π ≫ b) = 0 := by
  simp only [Category.assoc]
  rw [← Category.assoc i π b, h, zero_comp, comp_zero]

private theorem zero_prefix {A B D F : (Y).Modules}
    (i : A ⟶ B) (π : B ⟶ D) (b : D ⟶ F) (h : i ≫ π = 0) :
    i ≫ (π ≫ b) = 0 :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ b) h).trans (zero_comp))

/-- The ENTIRE original zero-Cech-row tuple component retains the SAME factor wedge in native degree b+a. -/
theorem totalCup_zeroRow_pi_native (a b : ℕ) (i : Fin 1 → ι) :
    totalCup f p n U a b ≫ HomologicalComplex₂.πTotalUpNat (C) (b+a) 0 (a+b) ≫
      Pi.π (fun t : Fin 1 → ι => factor (E (b+a)) (∏ᶜ fun j : Fin 1 => U (t j))) i =
    factorWedgeAlong f p a b (∏ᶜ fun j : Fin 1 => U (i j))
      (HomologicalComplex₂.πTotalUpNat (C) a 0 a ≫
        Pi.π (fun t : Fin 1 → ι => factor (E a) (∏ᶜ fun j : Fin 1 => U (t j))) i)
      (HomologicalComplex₂.πTotalUpNat (C) b 0 b ≫
        Pi.π (fun t : Fin 1 → ι => factor (E b) (∏ᶜ fun j : Fin 1 => U (t j))) i) := by
  apply CechTotalTensorExt.totalTensor_hom_ext f p n U a b
  intro q j r j' ha hb
  rw [← Category.assoc, CechTotalCupComponents.totalCup_ιTotal, zsmul_comp,
    factorWedgeAlong_tensorMap]
  by_cases hj : j = 0
  · subst j
    by_cases hj' : j' = 0
    · subst j'
      have hq : q = a := by omega
      have hr : r = b := by omega
      subst a b
      simp only [Nat.add_zero, Nat.zero_mul, pow_zero, one_smul]
      have ho := cancel_middle f p
        (orderedCup f p U q r 0 0)
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) 0 (q+r) (by change (r+q)+0=q+r; omega))
        (HomologicalComplex₂.πTotalUpNat (C) (r+q) 0 (q+r))
        (Pi.π (fun t : Fin 1 → ι => factor (E (r+q)) (∏ᶜ fun j : Fin 1 => U (t j))) i)
        (ι_π_same f p n U (r+q) 0 (q+r) (by omega))
      have hq := cancel_prefix f p
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) q 0 q rfl)
        (HomologicalComplex₂.πTotalUpNat (C) q 0 q)
        (Pi.π (fun t : Fin 1 → ι => factor (E q) (∏ᶜ fun j : Fin 1 => U (t j))) i)
        (ι_π_same f p n U q 0 q rfl)
      have hr := cancel_prefix f p
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) r 0 r rfl)
        (HomologicalComplex₂.πTotalUpNat (C) r 0 r)
        (Pi.π (fun t : Fin 1 → ι => factor (E r) (∏ᶜ fun j : Fin 1 => U (t j))) i)
        (ι_π_same f p n U r 0 r rfl)
      exact ho.trans ((orderedCup_zero_pi f p U q r i).trans
        (congrArg₂ (factorWedgeAlong f p q r (∏ᶜ fun j : Fin 1 => U (i j))) hq.symm hr.symm))

    · have hr : r ≠ b := by omega
      have hout : r+q ≠ b+a := by omega
      have hz := ι_π_form_ne f p n U r j' b hb b 0 hr
      have hzo := ι_π_form_ne f p n U (r+q) (0+j') (a+b) (by omega) (b+a) 0 hout
      have hl := zero_middle f p (orderedCup f p U q r 0 j')
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (0+j') (a+b)
          (by change (r+q)+(0+j')=a+b; omega))
        (HomologicalComplex₂.πTotalUpNat (C) (b+a) 0 (a+b))
        (Pi.π (fun t : Fin 1 → ι => factor (E (b+a)) (∏ᶜ fun j : Fin 1 => U (t j))) i) hzo
      have hp := zero_prefix f p
        (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb)
        (HomologicalComplex₂.πTotalUpNat (C) b 0 b)
        (Pi.π (fun t : Fin 1 → ι => factor (E b) (∏ᶜ fun j : Fin 1 => U (t j))) i) hz
      exact (congrArg (fun z => ((-1 : ℤ)^(0*r)) • z) hl).trans
        ((smul_zero _).trans
          ((congrArg (fun β => factorWedgeAlong f p a b (∏ᶜ fun j : Fin 1 => U (i j))
            (HomologicalComplex₂.ιTotal (C) (.up ℕ) q 0 a ha ≫
              HomologicalComplex₂.πTotalUpNat (C) a 0 a ≫
                Pi.π (fun t : Fin 1 → ι => factor (E a) (∏ᶜ fun j : Fin 1 => U (t j))) i) β) hp).trans
              (wedge_zero_right f p a b _ _)).symm)

  · have hq : q ≠ a := by omega
    have hout : r+q ≠ b+a := by omega
    have hz := ι_π_form_ne f p n U q j a ha a 0 hq
    have hzo := ι_π_form_ne f p n U (r+q) (j+j') (a+b) (by omega) (b+a) 0 hout
    have hl := zero_middle f p (orderedCup f p U q r j j')
      (HomologicalComplex₂.ιTotal (C) (.up ℕ) (r+q) (j+j') (a+b)
        (by change (r+q)+(j+j')=a+b; omega))
      (HomologicalComplex₂.πTotalUpNat (C) (b+a) 0 (a+b))
      (Pi.π (fun t : Fin 1 → ι => factor (E (b+a)) (∏ᶜ fun j : Fin 1 => U (t j))) i) hzo
    have hp := zero_prefix f p
      (HomologicalComplex₂.ιTotal (C) (.up ℕ) q j a ha)
      (HomologicalComplex₂.πTotalUpNat (C) a 0 a)
      (Pi.π (fun t : Fin 1 → ι => factor (E a) (∏ᶜ fun j : Fin 1 => U (t j))) i) hz
    exact (congrArg (fun z => ((-1 : ℤ)^(j*r)) • z) hl).trans
      ((smul_zero _).trans
        ((congrArg (fun α => factorWedgeAlong f p a b (∏ᶜ fun j : Fin 1 => U (i j)) α
          (HomologicalComplex₂.ιTotal (C) (.up ℕ) r j' b hb ≫
            HomologicalComplex₂.πTotalUpNat (C) b 0 b ≫
              Pi.π (fun t : Fin 1 → ι => factor (E b) (∏ᶜ fun j : Fin 1 => U (t j))) i)) hp).trans
                (wedge_zero_left f p a b _ _)).symm)

private theorem zeroProjection_cast (d a b : ℕ) (h : a=b) (i : Fin 1 → ι) :
    (HomologicalComplex₂.πTotalUpNat (C) a 0 d ≫
      Pi.π (fun t : Fin 1 → ι => factor (E a) (∏ᶜ fun j : Fin 1 => U (t j))) i) ≫
        eqToHom (congrArg (fun q => factor (E q) (∏ᶜ fun j : Fin 1 => U (i j))) h) =
    HomologicalComplex₂.πTotalUpNat (C) b 0 d ≫
      Pi.π (fun t : Fin 1 → ι => factor (E b) (∏ᶜ fun j : Fin 1 => U (t j))) i := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

/-- The ENTIRE original zero-row tuple formula in canonical total degree a+b, retaining the ORIGINAL degree cast. -/
theorem totalCup_zeroRow_pi (a b : ℕ) (i : Fin 1 → ι) :
    totalCup f p n U a b ≫ HomologicalComplex₂.πTotalUpNat (C) (a+b) 0 (a+b) ≫
      Pi.π (fun t : Fin 1 → ι => factor (E (a+b)) (∏ᶜ fun j : Fin 1 => U (t j))) i =
    factorWedgeAlong f p a b (∏ᶜ fun j : Fin 1 => U (i j))
      (HomologicalComplex₂.πTotalUpNat (C) a 0 a ≫
        Pi.π (fun t : Fin 1 → ι => factor (E a) (∏ᶜ fun j : Fin 1 => U (t j))) i)
      (HomologicalComplex₂.πTotalUpNat (C) b 0 b ≫
        Pi.π (fun t : Fin 1 → ι => factor (E b) (∏ᶜ fun j : Fin 1 => U (t j))) i) ≫
      eqToHom (congrArg (fun q => factor (E q) (∏ᶜ fun j : Fin 1 => U (i j))) (Nat.add_comm b a)) := by
  let e := eqToHom (congrArg (fun q => factor (E q) (∏ᶜ fun j : Fin 1 => U (i j))) (Nat.add_comm b a))
  have hp := zeroProjection_cast f p n U (a+b) (b+a) (a+b) (Nat.add_comm b a) i
  calc
    _ = totalCup f p n U a b ≫
        ((HomologicalComplex₂.πTotalUpNat (C) (b+a) 0 (a+b) ≫
          Pi.π (fun t : Fin 1 → ι => factor (E (b+a)) (∏ᶜ fun j : Fin 1 => U (t j))) i) ≫ e) :=
      congrArg (fun z => totalCup f p n U a b ≫ z) hp.symm
    _ = (totalCup f p n U a b ≫ HomologicalComplex₂.πTotalUpNat (C) (b+a) 0 (a+b) ≫
          Pi.π (fun t : Fin 1 → ι => factor (E (b+a)) (∏ᶜ fun j : Fin 1 => U (t j))) i) ≫ e :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≫ e) (totalCup_zeroRow_pi_native f p n U a b i)

private abbrev rowFactor (a : ℕ) (i : Fin 1 → ι) :
    (T).X a ⟶ factor (E a) (∏ᶜ fun j : Fin 1 => U (i j)) :=
  HomologicalComplex₂.πTotalUpNat (C) a 0 a ≫
    Pi.π (fun t : Fin 1 → ι => factor (E a) (∏ᶜ fun j : Fin 1 => U (t j))) i

private theorem member_le_tuple (i : ι) : U i ≤ ∏ᶜ (fun _ : Fin 1 => U i) :=
  leOfHom (Pi.lift (fun _ : Fin 1 => 𝟙 (U i)))

private theorem factorMap_cast {a b : ℕ} (h : a=b) {V W : (Y).Opens} (hWV : W ≤ V) :
    eqToHom (congrArg (fun q => factor (E q) V) h) ≫ factorMap (E b) hWV =
      factorMap (E a) hWV ≫ eqToHom (congrArg (fun q => factor (E q) W) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Native original member-factor evaluation preserves the SAME total cup, with the ORIGINAL degree transport. -/
theorem totalCup_evaluation (a b : ℕ) (i : ι) :
    totalCup f p n U a b ≫
      (Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f (a+b) =
    factorWedgeAlong f p a b (U i)
      ((Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f a)
      ((Cartier.DeligneIllusieCechTotalEvaluation.evaluation U (K) i).f b) ≫
      eqToHom (congrArg (fun q => factor (E q) (U i)) (Nat.add_comm b a)) := by
  let V : (Y).Opens := ∏ᶜ (fun _ : Fin 1 => U i)
  let α := rowFactor f p n U a (fun _ => i)
  let β := rowFactor f p n U b (fun _ => i)
  let cV := eqToHom (congrArg (fun q => factor (E q) V) (Nat.add_comm b a))
  let cU := eqToHom (congrArg (fun q => factor (E q) (U i)) (Nat.add_comm b a))
  have hz := totalCup_zeroRow_pi f p n U a b (fun _ => i)
  have hc := factorMap_cast f p (Nat.add_comm b a) (member_le_tuple f p U i)
  calc
    _ = (totalCup f p n U a b ≫ rowFactor f p n U (a+b) (fun _ => i)) ≫
        factorMap (E (a+b)) (member_le_tuple f p U i) := rfl
    _ = (factorWedgeAlong f p a b V α β ≫ cV) ≫
        factorMap (E (a+b)) (member_le_tuple f p U i) :=
      congrArg (fun z => z ≫ factorMap (E (a+b)) (member_le_tuple f p U i)) hz
    _ = factorWedgeAlong f p a b V α β ≫
        (factorMap (E (b+a)) (member_le_tuple f p U i) ≫ cU) :=
      (Category.assoc _ _ _).trans (congrArg (fun z => factorWedgeAlong f p a b V α β ≫ z) hc)
    _ = (factorWedgeAlong f p a b V α β ≫
        factorMap (E (b+a)) (member_le_tuple f p U i)) ≫ cU := (Category.assoc _ _ _).symm
    _ = factorWedgeAlong f p a b (U i)
        (α ≫ factorMap (E a) (member_le_tuple f p U i))
        (β ≫ factorMap (E b) (member_le_tuple f p U i)) ≫ cU :=
      congrArg (fun z => z ≫ cU)
        (factorWedgeAlong_factorMap f p a b (member_le_tuple f p U i) α β)
    _ = _ := rfl

end EnvelopeProperty.DI.CechTotalCup
