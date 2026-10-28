import EnvelopeProperty.Vanishing.ArithmeticOriginalSmoothDimension
import EnvelopeProperty.AlgGeom.ArithmeticSmoothProjectiveOriginalFamily

/-! # The original projective arithmetic family retains its relative dimension

The fixed model is the actual one produced from the original closed
embedding. Its later coefficient family is proved smooth of the original
relative dimension. Canonical further coefficient transitions preserve it.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open ProjBerk ArithmeticProjectiveOriginalFamily ArithmeticSmoothProjectiveOriginalFamily
open DeJongAlterations.StableModification.Limits

private theorem cancel_baseCorner {C : Type*} [Category C] {W Y T B D : C}
    (a : W ⟶ Y) (p : W ⟶ T) (q : Y ⟶ B) (b : T ⟶ B) (F : D ≅ B)
    (q₀ : Y ⟶ D) (b₀ : T ⟶ D) (H : IsPullback a p q b)
    (hq : q = q₀ ≫ F.hom) (hb : b = b₀ ≫ F.hom) : IsPullback a p q₀ b₀ := by
  apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) F.symm
  · simp
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, hq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, hb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]

private theorem relativeDimension_pullback_snd {W Y T B : Scheme.{u}}
    (n : ℕ) (a : W ⟶ Y) (p : W ⟶ T) (q : Y ⟶ B) (b : T ⟶ B)
    (H : IsPullback a p q b) [SmoothOfRelativeDimension n p] :
    SmoothOfRelativeDimension n (pullback.snd q b) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let E := H.isoPullback
  have he : E.hom ≫ pullback.snd q b = p := H.isoPullback_hom_snd
  have hs : SmoothOfRelativeDimension n (E.hom ≫ pullback.snd q b) :=
    he.symm ▸ inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension n) E.hom _).mp hs

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
  (j : X ⟶ NativeProjectiveScheme k N) [IsClosedImmersion j] (extra : Finset k)

/-- The canonical map between two coefficient extensions of the same original family. -/
def scalarTransition (S T : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S) (hST : S ≤ T) :
    scalarFamily j extra T (hRS.trans hST) ⟶ scalarFamily j extra S hRS :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) (by
      rw [Category.assoc, ← Spec.map_comp]
      exact pullback.condition)

theorem scalarTransition_fst (S T : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S)
    (hST : S ≤ T) : scalarTransition j extra S T hRS hST ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  simp only [scalarTransition, pullback.lift_fst]

theorem scalarTransition_projection (S T : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S)
    (hST : S ≤ T) : scalarTransition j extra S T hRS hST ≫ scalarProjection j extra S hRS =
      scalarProjection j extra T (hRS.trans hST) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) := by
  simp only [scalarTransition, scalarProjection, pullback.lift_snd]

/-- The canonical coefficient transition is an actual whole pullback square. -/
theorem isPullback_scalarTransition (S T : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S)
    (hST : S ≤ T) :
    IsPullback (scalarTransition j extra S T hRS hST)
      (scalarProjection j extra T (hRS.trans hST)) (scalarProjection j extra S hRS)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom)) := by
  have ho : IsPullback
      (scalarTransition j extra S T hRS hST ≫ pullback.fst _ _)
      (scalarProjection j extra T (hRS.trans hST)) (familyProjection j extra)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hST).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS).toRingHom)) := by
    rw [scalarTransition_fst, ← Spec.map_comp]
    exact IsPullback.of_hasPullback _ _
  exact ho.of_right (scalarTransition_projection j extra S T hRS hST)
    (IsPullback.of_hasPullback _ _)

/-- Further actual coefficient enlargement preserves the same original relative dimension. -/
theorem relativeDimension_scalarProjection (S T : Subalgebra ℤ k)
    (hRS : coefficientBase j extra ≤ S) (hST : S ≤ T) (n : ℕ)
    (hn : SmoothOfRelativeDimension n (scalarProjection j extra S hRS)) :
    SmoothOfRelativeDimension n (scalarProjection j extra T (hRS.trans hST)) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  exact MorphismProperty.of_isPullback (isPullback_scalarTransition j extra S T hRS hST) hn

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original projective embedding and original n-smooth structure
produce a finite integer coefficient stage where this same family is n-smooth. -/
theorem exists_relativeDimension_integer_stage (p : X ⟶ Spec (.of k))
    (hjp : j ≫ nativeStructureMap = p) (n : ℕ) [SmoothOfRelativeDimension n p] :
    ∃ (S : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S),
      Algebra.FiniteType ℤ S ∧ SmoothOfRelativeDimension n (scalarProjection j extra S hRS) ∧
      IsProjectiveFactorization (scalarProjection j extra S hRS) ∧
      IsPullback (scalarOriginalMap j extra S hRS p hjp) p (scalarProjection j extra S hRS)
        (Spec.map (CommRingCat.ofHom (algebraMap S k))) := by
  let A := coefficientBase j extra
  let Etop := ArithmeticFixedSmoothModel.topScalarIso A k
  let Ebot := ArithmeticFixedSmoothModel.bottomScalarIso A k Subtype.val_injective
  let D := (fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec
  let m := originalFixedModel j extra p hjp
  have hm := originalFixedModel_isFP j extra p hjp
  let : SmoothOfRelativeDimension n (p ≫ Etop.hom) := by
    simpa only [Nat.add_zero] using
      (smoothOfRelativeDimension_comp (n := n) (m := 0) p Etop.hom)
  obtain ⟨level, h, hn⟩ := exists_relativeDimension_fixed_model_baseChange
    (p ≫ Etop.hom) n m hm
  let B := unop level
  have hh : h = (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op :=
    Subsingleton.elim _ _
  subst h
  let a := Spec.map (CommRingCat.ofHom (algebraMap A B.1))
  have ha : D.map
      (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op = a ≫ Ebot.hom :=
    (ArithmeticFixedSmoothModel.bottomScalarIso_hom_stage A k Subtype.val_injective B).symm
  let b := D.map
    (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op
  have HP := cancel_baseCorner (pullback.fst m.fY b) (pullback.snd m.fY b) m.fY b Ebot
    (familyProjection j extra) a (IsPullback.of_hasPullback _ _) rfl ha
  let : SmoothOfRelativeDimension n (pullback.snd m.fY b) := hn
  have hnew := relativeDimension_pullback_snd n _ _ _ _ HP
  let S := B.1.restrictScalars ℤ
  have hRS : coefficientBase j extra ≤ S := by
    intro x hx
    exact B.1.algebraMap_mem (⟨x, hx⟩ : coefficientBase j extra)
  let : Algebra.FiniteType ℤ (coefficientBase j extra) := coefficientBase_finiteType j extra
  let : Algebra.FiniteType (coefficientBase j extra) B.1 :=
    (Subalgebra.fg_iff_finiteType _).mp B.2.1
  have hFT : Algebra.FiniteType ℤ B.1 :=
    Algebra.FiniteType.trans (S := coefficientBase j extra) inferInstance inferInstance
  exact ⟨S, hRS, hFT, hnew, scalarProjection_isProjectiveFactorization j extra S hRS,
    isPullback_scalarOriginalMap j extra S hRS p hjp⟩

/-- The original n-smooth projective scheme produces an actual arithmetic
family with smooth integer base and the same relative dimension, original
whole fibre, original embedding, and all original projective twists. -/
theorem exists_relativeDimension_smooth_projective_arithmetic_family [CharZero k]
    (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p)
    (n : ℕ) [SmoothOfRelativeDimension n p] :
    ∃ (S : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S),
      Algebra.Smooth ℤ S ∧ Algebra.FiniteType ℤ S ∧
      SmoothOfRelativeDimension n (scalarProjection j extra S hRS) ∧
      IsProjectiveFactorization (scalarProjection j extra S hRS) ∧
      IsPullback (scalarOriginalMap j extra S hRS p hjp) p (scalarProjection j extra S hRS)
        (Spec.map (CommRingCat.ofHom (algebraMap S k))) ∧
      scalarOriginalMap j extra S hRS p hjp ≫ scalarEmbedding j extra S hRS =
        j ≫ nativeCoefficientMap (algebraMap S k) ∧
      (∀ d : ℕ, Nonempty
        ((Scheme.Modules.pullback (scalarOriginalMap j extra S hRS p hjp)).obj
          (scalarTwist j extra S hRS d) ≅
          (Scheme.Modules.pullback j).obj
            (coordinateHyperplaneTwist (R := k) (0 : Fin (N + 1)) (d : ℤ)))) := by
  obtain ⟨S, hRS, hFT, hn, -, -⟩ := exists_relativeDimension_integer_stage j extra p hjp n
  let : Algebra.FiniteType ℤ S := hFT
  obtain ⟨s, hs, _, hSmooth, hBaseFT, _, _, _, hSS'⟩ :=
    ArithmeticSmoothCoefficientBase.exists_smooth_localizedCoefficientRing S
  let S' := ArithmeticSmoothCoefficientBase.localizedCoefficientRing S s hs
  have hRS' : coefficientBase j extra ≤ S' := hRS.trans hSS'
  have hn' : SmoothOfRelativeDimension n (scalarProjection j extra S' hRS') :=
    relativeDimension_scalarProjection j extra S S' hRS hSS' n hn
  exact ⟨S', hRS', hSmooth, hBaseFT, hn',
    scalarProjection_isProjectiveFactorization j extra S' hRS',
    isPullback_scalarOriginalMap j extra S' hRS' p hjp,
    scalarOriginalMap_embedding j extra S' hRS' p hjp,
    fun d => ⟨scalarTwistPullbackIso j extra S' hRS' p hjp d⟩⟩

end EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth
