import EnvelopeProperty.AlgGeom.ArithmeticSmoothProjectiveOriginalFamily

/-! # Actual projective morphisms descend on the original arithmetic family

Native finite-presentation descent constructs the later-stage morphism.
The original cartesian family and original projective morphism are retained;
no later-stage map or comparison is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineDescent
open ProjBerk Alterations.StableModification.Limits
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cancelBaseCorner {C : Type*} [Category C] {X Y S B D : C}
    (a : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ B) (b : S ⟶ B) (E : D ≅ B)
    (q₀ : Y ⟶ D) (b₀ : S ⟶ D) (H : IsPullback a p q b)
    (hq : q = q₀ ≫ E.hom) (hb : b = b₀ ≫ E.hom) : IsPullback a p q₀ b₀ := by
  apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) E.symm
  · simp
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, hq, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, hb, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]

private theorem inverse_projection {C : Type*} [Category C] {X Y S : C}
    (E : X ≅ Y) (a : X ⟶ S) (b : Y ⟶ S) (h : E.hom ≫ b = a) : E.inv ≫ a = b := by
  rw [← h, ← Category.assoc, E.inv_hom_id, Category.id_comp]

private theorem coefficientMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (n : ℕ) :
    nativeCoefficientMap (n := n) ψ ≫ nativeCoefficientMap φ =
      nativeCoefficientMap (ψ.comp φ) := by
  unfold nativeCoefficientMap
  rw [← AlgebraicGeometry.Proj.map_comp]
  congr 1
  apply DFunLike.ext
  intro F
  exact MvPolynomial.map_map φ ψ F

section
variable {A k : Type u} [CommRing A] [IsNoetherianRing A] [Field k] [Algebra A k]
  {X Y : Scheme.{u}} (a : X ⟶ Y) (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of A))
  (H : IsPullback a p q (Spec.map (CommRingCat.ofHom (algebraMap A k))))

/-- The actual original map into any literal scalar base change, with the
original structure morphism and both original scalar maps. -/
def originalBaseChangeMap (B : FGSubalgebra A (⊤ : Subalgebra A k)) :
    X ⟶ pullback q (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) :=
  pullback.lift a (p ≫ Spec.map (CommRingCat.ofHom (algebraMap B.1 k))) (by
    rw [Category.assoc, ← Spec.map_comp]
    exact H.w)

/-- Native morphism approximation constructs a projective morphism on a
genuine later coefficient base change of the SAME original cartesian family.
The whole original morphism, including its projective coordinates, is recovered.
Neither the later morphism nor its original comparison is an input. -/
theorem exists_projective_morphism_baseChange [QuasiCompact q] [QuasiSeparated q]
    (hinj : Function.Injective (algebraMap A k)) (n : ℕ)
    (g : X ⟶ NativeProjectiveScheme k n) (hg : g ≫ nativeStructureMap = p) :
    ∃ (B : FGSubalgebra A (⊤ : Subalgebra A k))
      (gB : pullback q (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) ⟶
        NativeProjectiveScheme B.1 n),
      gB ≫ nativeStructureMap = pullback.snd _ _ ∧
      originalBaseChangeMap a p q H B ≫ gB = g ≫ nativeCoefficientMap (algebraMap B.1 k) := by
  let D := (fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec
  let c := fgSpecCone (⊤ : Subalgebra A k)
  let i : (FGSubalgebra A (⊤ : Subalgebra A k))ᵒᵖ := op ⊥
  let Et := ArithmeticFixedSmoothModel.topScalarIso A k
  let Eb := ArithmeticFixedSmoothModel.bottomScalarIso A k hinj
  let q₀ := q ≫ Eb.hom
  have H₀ : IsPullback a (p ≫ Et.hom) q₀ (c.π.app i) := by
    apply H.of_iso (Iso.refl _) (Iso.refl _) Et Eb
    · simp
    · simp
    · simp [q₀]
    · exact (ArithmeticFixedSmoothModel.top_bottom_scalar_triangle A k hinj).symm
  let t := (nativeStructureMap (R := A) (n := n)) ≫ Eb.hom
  let : IsProper (nativeStructureMap (R := A) (n := n)) := nativeStructureMap_isProper
  let : LocallyOfFinitePresentation t := by dsimp [t]; infer_instance
  let : QuasiCompact q₀ := by dsimp [q₀]; infer_instance
  let : QuasiSeparated q₀ := by dsimp [q₀]; infer_instance
  have hgt : (g ≫ nativeCoefficientMap (algebraMap A k)) ≫ t = a ≫ q₀ := by
    have h₁ := congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ Eb.hom) hg
    have h₂ := congrArg (fun f => f ≫ Eb.hom) H.w.symm
    dsimp only [t, q₀]
    rw [Category.assoc g, ← Category.assoc (nativeCoefficientMap (algebraMap A k)),
      nativeCoefficientMap_over_base]
    simpa only [Category.assoc] using h₁.trans h₂
  obtain ⟨J, b, hb, hbOriginal⟩ := exists_hom_of_isPullback D c
    (isLimitFGSpecCone (⊤ : Subalgebra A k)) q₀ t H₀
    (g ≫ nativeCoefficientMap (algebraMap A k)) hgt
  change pullback q₀ (D.map J.hom) ⟶ NativeProjectiveScheme A n at b
  let B := unop J.left
  have hJ : J.hom = (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op :=
    Subsingleton.elim _ _
  have hmap : D.map J.hom =
      Spec.map (CommRingCat.ofHom (algebraMap A B.1)) ≫ Eb.hom := by
    rw [hJ]
    exact (ArithmeticFixedSmoothModel.bottomScalarIso_hom_stage A k hinj B).symm
  have HP := cancelBaseCorner
    (pullback.fst q₀ (D.map J.hom)) (pullback.snd q₀ (D.map J.hom)) q₀ (D.map J.hom)
    Eb q (Spec.map (CommRingCat.ofHom (algebraMap A B.1)))
    (IsPullback.of_hasPullback _ _) rfl hmap
  let E := HP.isoIsPullback _ _
    (IsPullback.of_hasPullback q (Spec.map (CommRingCat.ofHom (algebraMap A B.1))))
  have hEfst : E.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) =
      pullback.fst q₀ (D.map J.hom) := HP.isoIsPullback_hom_fst _ _ _
  have hEsnd : E.hom ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) =
      pullback.snd q₀ (D.map J.hom) := HP.isoIsPullback_hom_snd _ _ _
  have hEinvfst : E.inv ≫ pullback.fst q₀ (D.map J.hom) =
      pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) :=
    HP.isoIsPullback_inv_fst _ _ _
  let s : X ⟶ pullback q₀ (D.map J.hom) := (baseChangeCone D c H₀).π.app J
  have hs : s ≫ E.hom = originalBaseChangeMap a p q H B := by
    apply pullback.hom_ext
    · rw [Category.assoc, hEfst]
      simp only [s, baseChangeCone_π_app, pullback.lift_fst, originalBaseChangeMap]
    · rw [Category.assoc, hEsnd]
      simp only [s, baseChangeCone_π_app, pullback.lift_snd, originalBaseChangeMap]
      exact congrArg (fun f => p ≫ f) (ArithmeticFixedSmoothModel.topScalarIso_hom_stage A k B)
  let b₀ := E.inv ≫ b
  have hbA : b ≫ nativeStructureMap = pullback.fst q₀ (D.map J.hom) ≫ q := by
    apply (cancel_mono Eb.hom).mp
    simpa only [t, q₀, Category.assoc] using hb
  have hb₀ : b₀ ≫ nativeStructureMap = pullback.fst q
      (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) ≫ q := by
    dsimp only [b₀]
    rw [Category.assoc, hbA, ← Category.assoc, hEinvfst]
  let z := pullback.lift b₀ (pullback.snd q
    (Spec.map (CommRingCat.ofHom (algebraMap A B.1))))
    (hb₀.trans pullback.condition)
  let gB := z ≫ (nativeCoefficientBaseChangeIso (n := n) (algebraMap A B.1)).inv
  have hgB_fst : gB ≫ nativeCoefficientMap (algebraMap A B.1) = b₀ := by
    dsimp only [gB]
    rw [Category.assoc, inverse_projection _ _ _ (nativeCoefficientBaseChangeIso_hom_fst _)]
    exact pullback.lift_fst _ _ _
  have hgB_snd : gB ≫ nativeStructureMap = pullback.snd q
      (Spec.map (CommRingCat.ofHom (algebraMap A B.1))) := by
    dsimp only [gB]
    rw [Category.assoc, inverse_projection _ _ _ (nativeCoefficientBaseChangeIso_hom_snd _)]
    exact pullback.lift_snd _ _ _
  refine ⟨B, gB, hgB_snd, ?_⟩
  apply (cancel_mono (nativeCoefficientBaseChangeIso (n := n) (algebraMap A B.1)).hom).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, nativeCoefficientBaseChangeIso_hom_fst, hgB_fst,
      coefficientMap_comp]
    rw [← hs]
    dsimp only [b₀]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hbOriginal
  · simp only [Category.assoc, nativeCoefficientBaseChangeIso_hom_snd, hgB_snd,
      nativeCoefficientMap_over_base]
    rw [originalBaseChangeMap, pullback.lift_snd]
    simpa only [Category.assoc] using congrArg
      (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap B.1 k))) hg.symm

end
end EnvelopeProperty.Vanishing.ArithmeticOriginalLineDescent
