import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Entire original fibres are unchanged by an isomorphism on a neighbourhood -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.PLOriginalModelCompatibility

variable {S T Y Z V : Scheme.{u}} (s : T ⟶ S)

/-- The whole original induced fibre map, with its two canonical projections. -/
def fibreMap (p : Y ⟶ S) (q : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ q = p) :
    pullback p s ⟶ pullback q s :=
  pullback.lift (pullback.fst p s ≫ f) (pullback.snd p s) (by
    rw [Category.assoc, hf]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem fibreMap_fst (p : Y ⟶ S) (q : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ q = p) :
    fibreMap s p q f hf ≫ pullback.fst q s = pullback.fst p s ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreMap_snd (p : Y ⟶ S) (q : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ q = p) :
    fibreMap s p q f hf ≫ pullback.snd q s = pullback.snd p s :=
  pullback.lift_snd _ _ _

theorem fibreMap_comp (p : Y ⟶ S) (q : Z ⟶ S) (r : V ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ q = p) (g : Z ⟶ V) (hg : g ≫ r = q) :
    fibreMap s p r (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      fibreMap s p q f hf ≫ fibreMap s q r g hg := by
  apply pullback.hom_ext <;> simp only [Category.assoc, fibreMap_fst,
    fibreMap_fst_assoc, fibreMap_snd]

theorem fibreMap_isIso (p : Y ⟶ S) (q : Z ⟶ S) (f : Y ⟶ Z)
    (hf : f ≫ q = p) [IsIso f] : IsIso (fibreMap s p q f hf) := by
  have h : IsPullback (fibreMap s p q f hf) (pullback.fst p s)
      (pullback.fst q s) f := by
    have houter : IsPullback (fibreMap s p q f hf ≫ pullback.snd q s)
        (pullback.fst p s) s (f ≫ q) := by
      simpa only [fibreMap_snd, hf] using (IsPullback.of_hasPullback p s).flip
    exact houter.of_right (fibreMap_fst s p q f hf) (IsPullback.of_hasPullback q s).flip
  exact h.isIso_fst_of_isIso

private theorem isPullback_fibreMap_open (p : Y ⟶ S) (U : Y.Opens) :
    IsPullback (fibreMap s (U.ι ≫ p) p U.ι rfl)
      (pullback.fst (U.ι ≫ p) s) (pullback.fst p s) U.ι := by
  have houter : IsPullback
      (fibreMap s (U.ι ≫ p) p U.ι rfl ≫ pullback.snd p s)
      (pullback.fst (U.ι ≫ p) s) s (U.ι ≫ p) := by
    simpa only [fibreMap_snd] using (IsPullback.of_hasPullback (U.ι ≫ p) s).flip
  exact houter.of_right (fibreMap_fst s (U.ι ≫ p) p U.ι rfl)
    (IsPullback.of_hasPullback p s).flip

/-- An open containing the entire original fibre induces an isomorphism on
that same scheme-theoretic fibre, for any original base change morphism. -/
theorem fibreMap_open_isIso (p : Y ⟶ S) (U : Y.Opens)
    (hU : Set.range (pullback.fst p s) ⊆ (U : Set Y)) :
    IsIso (fibreMap s (U.ι ≫ p) p U.ι rfl) := by
  let h := isPullback_fibreMap_open s p U
  let : IsOpenImmersion (fibreMap s (U.ι ≫ p) p U.ι rfl) := by
    have hcomp : IsOpenImmersion
        (h.isoPullback.hom ≫ pullback.fst (pullback.fst p s) U.ι) := inferInstance
    simpa only [h.isoPullback_hom_fst] using hcomp
  have hs : Function.Surjective (fibreMap s (U.ι ≫ p) p U.ι rfl) := by
    intro y
    have hy : y ∈ Set.range (pullback.fst (pullback.fst p s) U.ι) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨⟨pullback.fst p s y, hU ⟨y, rfl⟩⟩, rfl⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨h.isoPullback.inv z, ?_⟩
    exact (congrArg (fun a => a z) h.isoPullback_inv_fst).trans hz
  let : Surjective (fibreMap s (U.ι ≫ p) p U.ι rfl) := ⟨hs⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

/-- A whole original isomorphism over a neighbourhood of the entire target
fibre induces an isomorphism of the two original scheme-theoretic fibres. -/
theorem fibreMap_isIso_of_morphismRestrict (p : Y ⟶ S) (q : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ q = p) (U : Z.Opens)
    (hU : Set.range (pullback.fst q s) ⊆ (U : Set Z)) [IsIso (f ∣_ U)] :
    IsIso (fibreMap s p q f hf) := by
  let W := f ⁻¹ᵁ U
  let p' := W.ι ≫ p
  let q' := U.ι ≫ q
  let f' := f ∣_ U
  have hf' : f' ≫ q' = p' := by
    dsimp only [f', q', p', W]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf]
  have hW : Set.range (pullback.fst p s) ⊆ (W : Set Y) := by
    rintro _ ⟨y, rfl⟩
    change f (pullback.fst p s y) ∈ U
    have hh : pullback.fst q s (fibreMap s p q f hf y) = f (pullback.fst p s y) :=
      congrArg (fun a => a y) (fibreMap_fst s p q f hf)
    rw [← hh]
    exact hU ⟨_, rfl⟩
  let : IsIso (fibreMap s p' p W.ι rfl) := fibreMap_open_isIso s p W hW
  let : IsIso (fibreMap s q' q U.ι rfl) := fibreMap_open_isIso s q U hU
  let : IsIso (fibreMap s p' q' f' hf') := fibreMap_isIso s p' q' f' hf'
  have hc : fibreMap s p' q' f' hf' ≫ fibreMap s q' q U.ι rfl =
      fibreMap s p' p W.ι rfl ≫ fibreMap s p q f hf := by
    apply pullback.hom_ext
    · simp only [Category.assoc, fibreMap_fst, fibreMap_fst_assoc]
      exact congrArg (fun a => pullback.fst p' s ≫ a) (morphismRestrict_ι f U)
    · simp only [Category.assoc, fibreMap_snd]
  have hi : IsIso (fibreMap s p' p W.ι rfl ≫ fibreMap s p q f hf) := by
    rw [← hc]
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := MorphismProperty.isomorphisms Scheme)
    (fibreMap s p' p W.ι rfl) (fibreMap s p q f hf)).mp hi

end EnvelopeProperty.PLOriginalModelCompatibility
