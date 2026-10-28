import EnvelopeProperty.Char0.CanonicalDifferentialSection
import EnvelopeProperty.AlgGeom.Canonical.ExteriorPullbackComposition
import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionRecovery
import EnvelopeProperty.AlgGeom.SchemeLineNonzeroGenerators

/-! # Genuine nonzero canonical differential from an actual nonempty isomorphism open -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
set_option backward.isDefEq.respectTransparency false
variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}

private theorem originalUnitSectionZero {T : Scheme.{u}} {M : T.Modules}
    (s : Scheme.Modules.unitObj T ⟶ M)
    (hs : s.val.app (.op ⊤) (show Γ(T, ⊤) from 1) = 0) : s = 0 := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : T.Opens))).op
  have h := PresheafOfModules.naturality_apply s.val i (show Γ(T, ⊤) from 1)
  change s.val.app V (T.presheaf.map i (show Γ(T, ⊤) from 1)) =
    M.presheaf.map i (s.val.app (.op ⊤) (show Γ(T, ⊤) from 1)) at h
  rw [map_one, hs, map_zero] at h
  exact h

/-- A genuine nonempty original open on which the original map is an open
immersion makes the ENTIRE original canonical differential nonzero. -/
theorem exteriorCotangentSheafPullbackMap_ne_zero_of_open
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (h : Z ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty Z]
    [IsOpenImmersion h] [IsOpenImmersion (h ≫ g)] :
    CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n ≠ 0 := by
  intro hz
  let q := CanonicalGeometry.exteriorCotangentSheafPullbackMap f (h ≫ g) n
  have hq : q = 0 := by
    dsimp only [q]
    rw [CanonicalGeometry.exteriorCotangentSheafPullbackMap_comp, hz, Functor.map_zero]
    simp
  let : IsIso q := CanonicalGeometry.isIso_exteriorCotangentSheafPullbackMap_openImmersion f (h ≫ g) n
  have hid : (𝟙 ((Scheme.Modules.pullback (h ≫ g)).obj
      (CanonicalGeometry.canonicalLineSheaf f n)) : _ ⟶ _) = 0 := by
    change (𝟙 ((Scheme.Modules.pullback (h ≫ g)).obj
      (CanonicalGeometry.exteriorCotangentSheaf f n)) : _ ⟶ _) = 0
    exact (IsIso.hom_inv_id q).symm.trans ((congrArg (fun a => a ≫ inv q) hq).trans zero_comp)
  exact SchemeLineNonzeroGenerators.id_ne_zero _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback (h ≫ g)) hid

private theorem originalZeroMappedComposite
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {A B C' E : C} {P Q : D}
    (l : P ⟶ F.obj A) (u : A ⟶ B) (v : C' ⟶ E) (w : F.obj E ⟶ Q) :
    l ≫ F.map (u ≫ (0 : B ⟶ C') ≫ v) ≫ w = 0 := by
  simp

private theorem originalHomSectionSymmZero {T : Scheme.{u}}
    (A : T.Modules) (hA : Scheme.Modules.IsInvertible A) (B : T.Modules) :
    (SchemeInvertibleHomSection.equiv A hA B).symm
      (0 : Scheme.Modules.unitObj T ⟶ Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) = 0 := by
  rw [SchemeInvertibleHomSection.equiv_symm_tensor_counit]
  let : MonoidalCategory T.Modules := Scheme.Modules.monoidalCategory T
  let : (tensorRight A).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence A hA
  exact originalZeroMappedComposite (tensorRight A) _ _ _ _

/-- The SAME actual Hom-section correspondence preserves genuine nonvanishing
of the original differential, without a section-matching assumption. -/
theorem differentialSection_ne_zero_of_open
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (h : Z ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty Z]
    [IsOpenImmersion h] [IsOpenImmersion (h ≫ g)] :
    differentialSection f g n ≠ 0 := by
  intro hz
  apply exteriorCotangentSheafPullbackMap_ne_zero_of_open f g h n
  have hzero := congrArg
    (SchemeInvertibleHomSection.equiv _
      ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g)
      (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n)).symm hz
  exact (differentialSection_recover f g n).symm.trans
    (hzero.trans (originalHomSectionSymmZero _ _ _))

/-- The true top-section value of the SAME original canonical differential
is nonzero; no generic-germ or coefficient premise is supplied. -/
theorem differentialGlobalSection_ne_zero_of_open
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (h : Z ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty Z]
    [IsOpenImmersion h] [IsOpenImmersion (h ≫ g)] :
    (differentialSection f g n).val.app (.op ⊤) (show Γ(Y, ⊤) from 1) ≠ 0 := by
  intro hz
  exact differentialSection_ne_zero_of_open f g h n
    (originalUnitSectionZero _ hz)

end EnvelopeProperty.Char0.RoundedCanonicalModule
