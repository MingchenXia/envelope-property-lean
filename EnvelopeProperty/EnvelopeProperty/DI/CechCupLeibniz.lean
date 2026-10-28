import EnvelopeProperty.DI.CechAlexanderWhitneyProduct
import EnvelopeProperty.DI.CechCupNaturality
import EnvelopeProperty.DI.CechCupSigns

/-! # The actual alternating Čech differential of the original ordered product -/

noncomputable section
universe u
namespace EnvelopeProperty.DI.CechAlexanderWhitneyProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Preadditive
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieCechCupProduct

variable {Z : Scheme.{u}} {ι : Type u} (U : ι → Z.Opens)

/-- The actual full intersection lies in its original deleted-face intersection. -/
theorem faceIntersection_le (j : ℕ) (k : Fin (j+2)) (i : Fin (j+2) → ι) :
    (∏ᶜ fun a : Fin (j+2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (j+1) => U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i)

/-- Every actual native coface projection is the SAME deleted tuple and
the SAME original factor restriction. -/
theorem coface_pi (M : Z.Modules) (j : ℕ) (k : Fin (j+2)) (i : Fin (j+2) → ι) :
    coface M U j k ≫ Pi.π (fun t : Fin (j+2) → ι =>
        factor M (∏ᶜ fun a : Fin (j+2) => U (t a))) i =
      Pi.π (fun t : Fin (j+1) → ι =>
        factor M (∏ᶜ fun a : Fin (j+1) => U (t a)))
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      factorMap M (faceIntersection_le U j k i) :=
  Pi.lift_π _ i

/-- The ENTIRE original differential projection is its actual finite signed
sum of original deleted-tuple restrictions. -/
theorem differential_pi (M : Z.Modules) (j : ℕ) (i : Fin (j+2) → ι) :
    (complex M U).d j (j+1) ≫ Pi.π (fun t : Fin (j+2) → ι =>
        factor M (∏ᶜ fun a : Fin (j+2) => U (t a))) i =
      ∑ k : Fin (j+2), (-1 : ℤ)^k.val •
        (Pi.π (fun t : Fin (j+1) → ι =>
          factor M (∏ᶜ fun a : Fin (j+1) => U (t a)))
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        factorMap M (faceIntersection_le U j k i)) := by
  rw [complex_d, sum_comp]
  simp only [zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun z => (-1 : ℤ)^k.val • z) (coface_pi U M j k i)

/-- The original indexed object transport of the SAME native Čech complex. -/
def degreeMap (M : Z.Modules) {a b : ℕ} (h : a = b) :
    (complex M U).X a ⟶ (complex M U).X b :=
  eqToHom (congrArg (fun n => (complex M U).X n) h)

/-- The original full intersection lies in every original selected subtuple. -/
theorem selectedIntersection_le {a b : ℕ} (g : Fin (a+1) → Fin (b+1))
    (i : Fin (b+1) → ι) :
    (∏ᶜ fun k : Fin (b+1) => U (i k)) ≤
      ∏ᶜ fun k : Fin (a+1) => U ((i ∘ g) k) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower g).φ i)

/-- Native projection to any original selected subtuple, followed by its
actual restriction to the original full intersection. -/
def tupleProjection (M : Z.Modules) {a b : ℕ}
    (g : Fin (a+1) → Fin (b+1)) (i : Fin (b+1) → ι) :
    (complex M U).X a ⟶ factor M (∏ᶜ fun k : Fin (b+1) => U (i k)) :=
  Pi.π (fun t : Fin (a+1) → ι => factor M (∏ᶜ fun k : Fin (a+1) => U (t k)))
    (i ∘ g) ≫ factorMap M (selectedIntersection_le U g i)

/-- Selecting a subtuple and then restricting composes the SAME original
factor restrictions, so it is the original composite subtuple projection. -/
theorem tupleProjection_restrict (M : Z.Modules) {a b c : ℕ}
    (g : Fin (a+1) → Fin (b+1)) (h : Fin (b+1) → Fin (c+1))
    (i : Fin (c+1) → ι) :
    tupleProjection U M g (i ∘ h) ≫ factorMap M (selectedIntersection_le U h i) =
      tupleProjection U M (h ∘ g) i := by
  rw [tupleProjection, Category.assoc, factorMap_comp]
  rfl

/-- The original coface followed by an original selected-tuple projection is
EXACTLY deletion in that selected original tuple. -/
theorem coface_tupleProjection (M : Z.Modules) {a b : ℕ} (k : Fin (a+2))
    (g : Fin (a+2) → Fin (b+1)) (i : Fin (b+1) → ι) :
    coface M U a k ≫ tupleProjection U M g i =
      tupleProjection U M (g ∘ (SimplexCategory.δ k).toOrderHom.toFun) i := by
  rw [tupleProjection, ← Category.assoc, coface_pi, Category.assoc, factorMap_comp]
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q
variable {κ : Type u} (V : κ → Scheme.Opens (Cartier.SchemeRelativeFrobenius.twist p f))

theorem prefixProjection_as_tupleProjection (M : (Y).Modules) (j j' : ℕ)
    (i : Fin (j+j'+1) → κ) :
    prefixProjection f p V M j j' i = tupleProjection V M (tuplePrefix j j') i := rfl

theorem suffixProjection_as_tupleProjection (M : (Y).Modules) (j j' : ℕ)
    (i : Fin (j+j'+1) → κ) :
    suffixProjection f p V M j j' i = tupleProjection V M (tupleSuffix j j') i := rfl

/-- The original prefix written in an equal ORIGINAL output degree. -/
def prefixInDegree (j j' n : ℕ) (h : j+j' = n) : Fin (j+1) → Fin (n+1) :=
  fun a => ⟨a.val, by omega⟩

/-- The corresponding original suffix, retaining its SAME shared vertex. -/
def suffixInDegree (j j' n : ℕ) (h : j+j' = n) : Fin (j'+1) → Fin (n+1) :=
  fun a => ⟨j+a.val, by omega⟩

/-- The SAME original cup in a specified equal output degree. All components
still use the SAME original tuple restrictions and the SAME actual wedge. -/
def orderedCupInDegree (q r j j' n : ℕ) (h : j+j' = n) :
    CanonicalGeometry.bundleTensor ((complex (E q) V).X j) ((complex (E r) V).X j') ⟶
      (complex (E (r+q)) V).X n :=
  Pi.lift (fun i : Fin (n+1) → κ =>
    factorWedgeAlong f p q r (∏ᶜ fun a : Fin (n+1) => V (i a))
      (tupleProjection V (E q) (prefixInDegree j j' n h) i)
      (tupleProjection V (E r) (suffixInDegree j j' n h) i))

/-- This construction is exactly the original native indexed-object transport
of the already constructed ordinary cup, not a new chosen product. -/
theorem orderedCupInDegree_eq (q r j j' n : ℕ) (h : j+j' = n) :
    orderedCup f p V q r j j' ≫ degreeMap V (E (r+q)) h =
      orderedCupInDegree f p V q r j j' n h := by
  cases h
  rw [degreeMap, eqToHom_refl, Category.comp_id]
  rfl

/-- Every specified-degree output retains its original selected tuple pair. -/
theorem orderedCupInDegree_pi (q r j j' n : ℕ) (h : j+j' = n) (i : Fin (n+1) → κ) :
    orderedCupInDegree f p V q r j j' n h ≫
        Pi.π (fun t : Fin (n+1) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (n+1) => V (t a))) i =
      factorWedgeAlong f p q r (∏ᶜ fun a : Fin (n+1) => V (i a))
        (tupleProjection V (E q) (prefixInDegree j j' n h) i)
        (tupleProjection V (E r) (suffixInDegree j j' n h) i) := Pi.lift_π _ i

/-- An actual coface of the original ordered cup retains the exact original
prefix/suffix pair followed by restriction to the full deleted-face intersection. -/
theorem cup_coface_pi (q r j j' : ℕ) (k : Fin (j+j'+2)) (i : Fin (j+j'+2) → κ) :
    orderedCup f p V q r j j' ≫ coface (E (r+q)) V (j+j') k ≫
        Pi.π (fun t : Fin (j+j'+2) → κ =>
          factor (E (r+q)) (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i =
      factorWedgeAlong f p q r (∏ᶜ fun a : Fin (j+j'+2) => V (i a))
        (prefixProjection f p V (E q) j j'
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          factorMap (E q) (faceIntersection_le V (j+j') k i))
        (suffixProjection f p V (E r) j j'
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          factorMap (E r) (faceIntersection_le V (j+j') k i)) := by
  rw [coface_pi, ← Category.assoc, cup_pi, factorWedgeAlong_factorMap]

/-- The coface of the original cup expressed entirely through the SAME
original full-intersection tuple projections. -/
theorem cup_coface_tupleProjection (q r j j' : ℕ)
    (k : Fin (j+j'+2)) (i : Fin (j+j'+2) → κ) :
    orderedCup f p V q r j j' ≫ coface (E (r+q)) V (j+j') k ≫
        Pi.π (fun t : Fin (j+j'+2) → κ =>
          factor (E (r+q)) (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i =
      factorWedgeAlong f p q r (∏ᶜ fun a : Fin (j+j'+2) => V (i a))
        (tupleProjection V (E q)
          ((SimplexCategory.δ k).toOrderHom.toFun ∘ tuplePrefix j j') i)
        (tupleProjection V (E r)
          ((SimplexCategory.δ k).toOrderHom.toFun ∘ tupleSuffix j j') i) := by
  rw [cup_coface_pi, prefixProjection_as_tupleProjection,
    suffixProjection_as_tupleProjection, tupleProjection_restrict, tupleProjection_restrict]

/-- The actual cup after a left Čech differential, retaining the SAME output
complex object in the original total Čech degree. -/
def cupAfterLeft (q r j j' : ℕ) :
    CanonicalGeometry.bundleTensor ((complex (E q) V).X (j+1)) ((complex (E r) V).X j') ⟶
      (complex (E (r+q)) V).X (j+j'+1) :=
  orderedCupInDegree f p V q r (j+1) j' (j+j'+1) (by omega)

/-- The corresponding actual cup after a right Čech differential. -/
def cupAfterRight (q r j j' : ℕ) :
    CanonicalGeometry.bundleTensor ((complex (E q) V).X j) ((complex (E r) V).X (j'+1)) ⟶
      (complex (E (r+q)) V).X (j+j'+1) :=
  orderedCupInDegree f p V q r j (j'+1) (j+j'+1) (by omega)

/-- A projected specified-degree cup retains the actual two input maps. -/
theorem indexedCup_tensorMap_pi (q r j j' n : ℕ) (h : j+j' = n)
    {A B : (Y).Modules}
    (a : A ⟶ (complex (E q) V).X j) (b : B ⟶ (complex (E r) V).X j')
    (i : Fin (n+1) → κ) :
    tensorMap a b ≫ orderedCupInDegree f p V q r j j' n h ≫
        Pi.π (fun t : Fin (n+1) → κ => factor (E (r+q))
          (∏ᶜ fun k : Fin (n+1) => V (t k))) i =
      factorWedgeAlong f p q r (∏ᶜ fun k : Fin (n+1) => V (i k))
        (a ≫ tupleProjection V (E q) (prefixInDegree j j' n h) i)
        (b ≫ tupleProjection V (E r) (suffixInDegree j j' n h) i) := by
  rw [orderedCupInDegree_pi, factorWedgeAlong_tensorMap]

theorem leftSourceCoface_pi (q r j j' : ℕ) (k : Fin (j+2)) (i : Fin (j+j'+2) → κ) :
    tensorMap (coface (E q) V j k) (𝟙 ((complex (E r) V).X j')) ≫
        cupAfterLeft f p V q r j j' ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i =
      factorWedgeAlong f p q r (∏ᶜ fun a : Fin (j+j'+2) => V (i a))
        (tupleProjection V (E q)
          (prefixInDegree (j+1) j' (j+j'+1) (by omega) ∘
            (SimplexCategory.δ k).toOrderHom.toFun) i)
        (tupleProjection V (E r) (suffixInDegree (j+1) j' (j+j'+1) (by omega)) i) := by
  rw [cupAfterLeft, indexedCup_tensorMap_pi, coface_tupleProjection, Category.id_comp]

theorem rightSourceCoface_pi (q r j j' : ℕ) (k : Fin (j'+2)) (i : Fin (j+j'+2) → κ) :
    tensorMap (𝟙 ((complex (E q) V).X j)) (coface (E r) V j' k) ≫
        cupAfterRight f p V q r j j' ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i =
      factorWedgeAlong f p q r (∏ᶜ fun a : Fin (j+j'+2) => V (i a))
        (tupleProjection V (E q) (prefixInDegree j (j'+1) (j+j'+1) (by omega)) i)
        (tupleProjection V (E r)
          (suffixInDegree j (j'+1) (j+j'+1) (by omega) ∘
            (SimplexCategory.δ k).toOrderHom.toFun) i) := by
  rw [cupAfterRight, indexedCup_tensorMap_pi, Category.id_comp, coface_tupleProjection]

theorem prefix_face_left (j j' : ℕ) (k : Fin (j+1)) :
    (SimplexCategory.δ (⟨k.val, by omega⟩ : Fin (j+j'+2))).toOrderHom.toFun ∘ tuplePrefix j j' =
      prefixInDegree (j+1) j' (j+j'+1) (by omega) ∘
        (SimplexCategory.δ k.castSucc).toOrderHom.toFun := by
  funext a
  apply Fin.ext
  exact CechCupSigns.prefix_delete_left j j' k a

theorem suffix_face_left (j j' : ℕ) (k : Fin (j+1)) :
    (SimplexCategory.δ (⟨k.val, by omega⟩ : Fin (j+j'+2))).toOrderHom.toFun ∘ tupleSuffix j j' =
      suffixInDegree (j+1) j' (j+j'+1) (by omega) := by
  funext a
  apply Fin.ext
  exact CechCupSigns.suffix_delete_left j j' k a

theorem prefix_face_right (j j' : ℕ) (k : Fin (j'+1)) :
    (SimplexCategory.δ (⟨j+1+k.val, by omega⟩ : Fin (j+j'+2))).toOrderHom.toFun ∘ tuplePrefix j j' =
      prefixInDegree j (j'+1) (j+j'+1) (by omega) := by
  funext a
  apply Fin.ext
  exact CechCupSigns.prefix_delete_right j j' k a

theorem suffix_face_right (j j' : ℕ) (k : Fin (j'+1)) :
    (SimplexCategory.δ (⟨j+1+k.val, by omega⟩ : Fin (j+j'+2))).toOrderHom.toFun ∘ tupleSuffix j j' =
      suffixInDegree j (j'+1) (j+j'+1) (by omega) ∘
        (SimplexCategory.δ k.succ).toOrderHom.toFun := by
  funext a
  apply Fin.ext
  exact CechCupSigns.suffix_delete_right j j' k a

theorem prefix_shared_face (j j' : ℕ) :
    prefixInDegree (j+1) j' (j+j'+1) (by omega) ∘
        (SimplexCategory.δ (Fin.last (j+1))).toOrderHom.toFun =
      prefixInDegree j (j'+1) (j+j'+1) (by omega) := by
  funext a
  apply Fin.ext
  change ((Fin.last (j+1)).succAbove a).val = a.val
  rw [Fin.succAbove_of_castSucc_lt _ _ (by exact a.isLt)]
  rfl

theorem suffix_shared_face (j j' : ℕ) :
    suffixInDegree (j+1) j' (j+j'+1) (by omega) =
      suffixInDegree j (j'+1) (j+j'+1) (by omega) ∘
        (SimplexCategory.δ (0 : Fin (j'+2))).toOrderHom.toFun := by
  funext a
  apply Fin.ext
  change j+1+a.val = j+((0 : Fin (j'+2)).succAbove a).val
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
  simp only [Fin.val_succ]
  omega

/-- Every deletion in the prefix range is its SAME original source coface. -/
theorem cup_left_face_pi (q r j j' : ℕ) (k : Fin (j+1)) (i : Fin (j+j'+2) → κ) :
    orderedCup f p V q r j j' ≫
        coface (E (r+q)) V (j+j') (⟨k.val, by omega⟩ : Fin (j+j'+2)) ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i =
      tensorMap (coface (E q) V j k.castSucc) (𝟙 ((complex (E r) V).X j')) ≫
        cupAfterLeft f p V q r j j' ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i := by
  rw [cup_coface_tupleProjection, leftSourceCoface_pi, prefix_face_left, suffix_face_left]

/-- Every deletion in the suffix range is its SAME original source coface. -/
theorem cup_right_face_pi (q r j j' : ℕ) (k : Fin (j'+1)) (i : Fin (j+j'+2) → κ) :
    orderedCup f p V q r j j' ≫
        coface (E (r+q)) V (j+j') (⟨j+1+k.val, by omega⟩ : Fin (j+j'+2)) ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i =
      tensorMap (𝟙 ((complex (E q) V).X j)) (coface (E r) V j' k.succ) ≫
        cupAfterRight f p V q r j j' ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i := by
  rw [cup_coface_tupleProjection, rightSourceCoface_pi, prefix_face_right, suffix_face_right]

/-- The two ACTUAL shared-vertex source faces coincide as whole native maps. -/
theorem cup_shared_face_pi (q r j j' : ℕ) (i : Fin (j+j'+2) → κ) :
    tensorMap (coface (E q) V j (Fin.last (j+1))) (𝟙 ((complex (E r) V).X j')) ≫
        cupAfterLeft f p V q r j j' ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i =
      tensorMap (𝟙 ((complex (E q) V).X j)) (coface (E r) V j' (0 : Fin (j'+2))) ≫
        cupAfterRight f p V q r j j' ≫
        Pi.π (fun t : Fin (j+j'+2) → κ => factor (E (r+q))
          (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i := by
  rw [leftSourceCoface_pi, rightSourceCoface_pi, prefix_shared_face, suffix_shared_face]

/-- The ACTUAL ordinary all-tuple Čech differential is a derivation of the
ACTUAL ordered sheaf cup. Both summands retain the original indexed objects;
their arithmetic output-degree transport is the already proved original cup. -/
theorem cup_cech_leibniz (q r j j' : ℕ) :
    orderedCup f p V q r j j' ≫ (complex (E (r+q)) V).d (j+j') (j+j'+1) =
      tensorMap ((complex (E q) V).d j (j+1)) (𝟙 ((complex (E r) V).X j')) ≫
          cupAfterLeft f p V q r j j' +
        (-1 : ℤ)^j •
          (tensorMap (𝟙 ((complex (E q) V).X j)) ((complex (E r) V).d j' (j'+1)) ≫
            cupAfterRight f p V q r j j') := by
  classical
  apply Pi.hom_ext
  intro i
  change Fin (j+j'+2) → κ at i
  let πi : (complex (E (r+q)) V).X (j+j'+1) ⟶
      factor (E (r+q)) (∏ᶜ fun a : Fin (j+j'+2) => V (i a)) :=
    Pi.π (fun t : Fin (j+j'+2) → κ =>
      factor (E (r+q)) (∏ᶜ fun a : Fin (j+j'+2) => V (t a))) i
  change (orderedCup f p V q r j j' ≫
      (complex (E (r+q)) V).d (j+j') (j+j'+1)) ≫ πi =
    (tensorMap ((complex (E q) V).d j (j+1)) (𝟙 ((complex (E r) V).X j')) ≫
        cupAfterLeft f p V q r j j' +
      (-1 : ℤ)^j •
        (tensorMap (𝟙 ((complex (E q) V).X j)) ((complex (E r) V).d j' (j'+1)) ≫
          cupAfterRight f p V q r j j')) ≫ πi
  let G := CanonicalGeometry.bundleTensor ((complex (E q) V).X j) ((complex (E r) V).X j') ⟶
    factor (E (r+q)) (∏ᶜ fun a : Fin (j+j'+2) => V (i a))
  let L : Fin (j+2) → G := fun k =>
    tensorMap (coface (E q) V j k) (𝟙 ((complex (E r) V).X j')) ≫
      cupAfterLeft f p V q r j j' ≫ πi
  let R : Fin (j'+2) → G := fun k =>
    tensorMap (𝟙 ((complex (E q) V).X j)) (coface (E r) V j' k) ≫
      cupAfterRight f p V q r j j' ≫ πi
  let C₀ : Fin (j+j'+2) → G := fun k =>
    orderedCup f p V q r j j' ≫ coface (E (r+q)) V (j+j') k ≫ πi
  let C : Fin ((j+1)+(j'+1)) → G := fun k => C₀ ⟨k.val, by omega⟩
  have hleft (k : Fin (j+1)) : C (Fin.castAdd (j'+1) k) = L k.castSucc :=
    cup_left_face_pi f p V q r j j' k i
  have hright (k : Fin (j'+1)) : C (Fin.natAdd (j+1) k) = R k.succ :=
    cup_right_face_pi f p V q r j j' k i
  have hshared : L (Fin.last (j+1)) = R 0 := cup_shared_face_pi f p V q r j j' i
  have hsum := CechCupSigns.alternating_join_of_faces j j' L R C hleft hright hshared
  have sum_cast {a b : ℕ} (h : a = b) (t : Fin b → G) :
      (∑ k : Fin a, t (Fin.cast h k)) = ∑ k : Fin b, t k := by
    cases h
    rfl
  have hcast := sum_cast (show (j+1)+(j'+1) = j+j'+2 by omega)
    (fun k : Fin (j+j'+2) => (-1 : ℤ)^k.val • C₀ k)
  change (∑ k : Fin ((j+1)+(j'+1)), (-1 : ℤ)^k.val • C k) =
    ∑ k : Fin (j+j'+2), (-1 : ℤ)^k.val • C₀ k at hcast
  have hC : orderedCup f p V q r j j' ≫
      (complex (E (r+q)) V).d (j+j') (j+j'+1) ≫ πi =
        ∑ k : Fin (j+j'+2), (-1 : ℤ)^k.val • C₀ k := by
    rw [complex_d]
    simp only [sum_comp, comp_sum, comp_zsmul, zsmul_comp]
    rfl
  have hLM : tensorMap ((complex (E q) V).d j (j+1)) (𝟙 ((complex (E r) V).X j')) =
      ∑ k : Fin (j+2), (-1 : ℤ)^k.val •
        tensorMap (coface (E q) V j k) (𝟙 ((complex (E r) V).X j')) := by
    change tensorMapHomLeft (𝟙 ((complex (E r) V).X j'))
      ((complex (E q) V).d j (j+1)) = _
    rw [complex_d, map_sum]
    simp only [map_zsmul]
    rfl
  have hRM : tensorMap (𝟙 ((complex (E q) V).X j)) ((complex (E r) V).d j' (j'+1)) =
      ∑ k : Fin (j'+2), (-1 : ℤ)^k.val •
        tensorMap (𝟙 ((complex (E q) V).X j)) (coface (E r) V j' k) := by
    change tensorMapHomRight (𝟙 ((complex (E q) V).X j))
      ((complex (E r) V).d j' (j'+1)) = _
    rw [complex_d, map_sum]
    simp only [map_zsmul]
    rfl
  have hL : tensorMap ((complex (E q) V).d j (j+1)) (𝟙 ((complex (E r) V).X j')) ≫
      cupAfterLeft f p V q r j j' ≫ πi = ∑ k : Fin (j+2), (-1 : ℤ)^k.val • L k := by
    rw [hLM]
    simp only [sum_comp, zsmul_comp]
    rfl
  have hR : tensorMap (𝟙 ((complex (E q) V).X j)) ((complex (E r) V).d j' (j'+1)) ≫
      cupAfterRight f p V q r j j' ≫ πi = ∑ k : Fin (j'+2), (-1 : ℤ)^k.val • R k := by
    rw [hRM]
    simp only [sum_comp, zsmul_comp]
    rfl
  change orderedCup f p V q r j j' ≫
      (complex (E (r+q)) V).d (j+j') (j+j'+1) ≫ πi = _
  rw [hC]
  calc
    _ = (∑ k : Fin (j+2), (-1 : ℤ)^k.val • L k) +
        (-1 : ℤ)^j • (∑ k : Fin (j'+2), (-1 : ℤ)^k.val • R k) := hcast.symm.trans hsum
    _ = _ := by
      simp only [add_comp, zsmul_comp, Category.assoc]
      rw [hL, hR]

end EnvelopeProperty.DI.CechAlexanderWhitneyProduct
