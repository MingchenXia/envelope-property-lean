import EnvelopeProperty.AlgGeom.ArithmeticProjectiveOriginalFamily
import EnvelopeProperty.AlgGeom.ArithmeticSmoothCoefficientBase
import EnvelopeProperty.AlgGeom.ArithmeticFixedSmoothModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import DeJongAlterations.StableModification.Limits.Descent

/-! # Smooth spreading of the SAME actual original projective family

The whole original family is fixed by27. Its canonical closed embedding and
entire original projective twists will be preserved under the produced scalar
extensions; native fixed-model spreading supplies smoothness internally.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open Scheme.Modules
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.ArithmeticSmoothProjectiveOriginalFamily
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem inverse_projection {C : Type*} [Category C] {A B D : C}
    (E : A ≅ B) (q : A ⟶ D) (p : B ⟶ D) (h : E.hom ≫ p = q) : E.inv ≫ q = p := by
  rw [← h, ← Category.assoc, E.inv_hom_id, Category.id_comp]

section CoefficientEmbedding
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {N : ℕ}
variable {Y : Scheme.{u}} (i : Y ⟶ NativeProjectiveScheme R N) (φ : R →+* S)

private def ambientPullbackMap :
    pullback (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ)) ⟶
      pullback (nativeStructureMap (R := R) (n := N)) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.map (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ))
    (nativeStructureMap (R := R) (n := N)) (Spec.map (CommRingCat.ofHom φ))
    i (𝟙 _) (𝟙 _) (by simp) (by simp)

private theorem ambientPullbackMap_fst :
    ambientPullbackMap i φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ i := by
  simp only [ambientPullbackMap, pullback.map, pullback.lift_fst]

private theorem ambientPullbackMap_snd :
    ambientPullbackMap i φ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [ambientPullbackMap, pullback.map, pullback.lift_snd, Category.comp_id]

private theorem ambientPullbackMap_isPullback :
    IsPullback (pullback.fst (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ)))
      (ambientPullbackMap i φ) i (pullback.fst _ _) := by
  apply IsPullback.of_bot
    (v₂₁ := pullback.snd (nativeStructureMap (R := R) (n := N)) (Spec.map (CommRingCat.ofHom φ)))
    (v₂₂ := nativeStructureMap) ?_ (ambientPullbackMap_fst i φ).symm
    (IsPullback.of_hasPullback _ _)
  rw [ambientPullbackMap_snd]
  exact IsPullback.of_hasPullback _ _

private def coefficientEmbedding :
    pullback (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ)) ⟶ NativeProjectiveScheme S N :=
  ambientPullbackMap i φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv

private theorem coefficientEmbedding_closed [IsClosedImmersion i] :
    IsClosedImmersion (coefficientEmbedding i φ) := by
  let : IsClosedImmersion (ambientPullbackMap i φ) :=
    MorphismProperty.of_isPullback (ambientPullbackMap_isPullback i φ) inferInstance
  change IsClosedImmersion (ambientPullbackMap i φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv)
  infer_instance

private theorem coefficientEmbedding_ambient :
    coefficientEmbedding i φ ≫ nativeCoefficientMap φ = pullback.fst _ _ ≫ i := by
  have h := inverse_projection (nativeCoefficientBaseChangeIso (n := N) φ)
    (nativeCoefficientMap φ) (pullback.fst _ _) (nativeCoefficientBaseChangeIso_hom_fst φ)
  change (ambientPullbackMap i φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv) ≫ _ = _
  rw [Category.assoc, h, ambientPullbackMap_fst]

private theorem coefficientEmbedding_projection :
    coefficientEmbedding i φ ≫ nativeStructureMap = pullback.snd _ _ := by
  have h := inverse_projection (nativeCoefficientBaseChangeIso (n := N) φ)
    (nativeStructureMap (R := S) (n := N)) (pullback.snd _ _) (nativeCoefficientBaseChangeIso_hom_snd φ)
  change (ambientPullbackMap i φ ≫ (nativeCoefficientBaseChangeIso (n := N) φ).inv) ≫ _ = _
  rw [Category.assoc, h, ambientPullbackMap_snd]

private def coefficientEmbedding_twist (d : ℕ) :
    (Scheme.Modules.pullback (coefficientEmbedding i φ)).obj
        (coordinateHyperplaneTwist (R := S) (0 : Fin (N + 1)) (d : ℤ)) ≅
      (Scheme.Modules.pullback (pullback.fst (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ)))).obj
        ((Scheme.Modules.pullback i).obj
          (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (d : ℤ))) :=
  (Scheme.Modules.pullback (coefficientEmbedding i φ)).mapIso
      (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso φ (0 : Fin (N + 1)) d).symm ≪≫
  (Scheme.Modules.pullbackComp (coefficientEmbedding i φ) (nativeCoefficientMap φ)).app _ ≪≫
  (Scheme.Modules.pullbackCongr (coefficientEmbedding_ambient i φ)).app _ ≪≫
  ((Scheme.Modules.pullbackComp (pullback.fst (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ))) i).app _).symm

private theorem coefficientEmbedding_veryAmple [IsClosedImmersion i] :
    SchemeLineAmpleness.IsVeryAmple
      (pullback.snd (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ)))
      ((Scheme.Modules.pullback (coefficientEmbedding i φ)).obj
        (coordinateHyperplaneTwist (R := S) (0 : Fin (N + 1)) 1)) :=
  ⟨N, coefficientEmbedding i φ, coefficientEmbedding_closed i φ,
    coefficientEmbedding_projection i φ, ⟨Iso.refl _⟩⟩

private theorem nativeCoefficientMap_comp (ψ : S →+* T) :
    nativeCoefficientMap (n := N) ψ ≫ nativeCoefficientMap φ = nativeCoefficientMap (ψ.comp φ) := by
  unfold nativeCoefficientMap
  rw [← AlgebraicGeometry.Proj.map_comp]
  congr 1
  apply DFunLike.ext
  intro F
  exact MvPolynomial.map_map φ ψ F

private theorem coefficientEmbedding_original {Z : Scheme.{u}}
    (j : Z ⟶ NativeProjectiveScheme T N) (p : Z ⟶ Spec (.of T)) (ψ : S →+* T)
    (g : Z ⟶ pullback (i ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ)))
    (hold : g ≫ pullback.fst _ _ ≫ i = j ≫ nativeCoefficientMap (ψ.comp φ))
    (hnew : g ≫ pullback.snd _ _ = p ≫ Spec.map (CommRingCat.ofHom ψ))
    (hp : j ≫ nativeStructureMap = p) :
    g ≫ coefficientEmbedding i φ = j ≫ nativeCoefficientMap ψ := by
  apply (cancel_mono (nativeCoefficientBaseChangeIso (n := N) φ).hom).1
  apply pullback.hom_ext
  · simp only [Category.assoc, nativeCoefficientBaseChangeIso_hom_fst,
      coefficientEmbedding_ambient, nativeCoefficientMap_comp]
    exact hold
  · simp only [Category.assoc, nativeCoefficientBaseChangeIso_hom_snd,
      coefficientEmbedding_projection, nativeCoefficientMap_over_base]
    apply hnew.trans
    simpa only [Category.assoc] using
      (congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom ψ)) hp.symm)

end CoefficientEmbedding

private theorem move_baseCorners {C : Type*} [Category C] {X Y S T B D : C}
    (g : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ B) (a : S ⟶ B)
    (H : IsPullback g p q a) (E : S ≅ T) (F : B ≅ D) (b : T ⟶ D)
    (ha : a ≫ F.hom = E.hom ≫ b) : IsPullback g (p ≫ E.hom) (q ≫ F.hom) b :=
  H.of_iso (Iso.refl _) (Iso.refl _) E F (by simp) (by simp) (by simp) ha

private theorem cancel_baseCorner {C : Type*} [Category C] {X Y S B D : C}
    (g : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ B) (a : S ⟶ B) (F : D ≅ B)
    (q₀ : Y ⟶ D) (a₀ : S ⟶ D) (H : IsPullback g p q a)
    (hq : q = q₀ ≫ F.hom) (ha : a = a₀ ≫ F.hom) : IsPullback g p q₀ a₀ := by
  apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) F.symm
  · simp
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, hq, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, ha, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

private theorem smooth_pullback_snd {X Y S B : Scheme.{u}}
    (g : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ B) (a : S ⟶ B)
    (H : IsPullback g p q a) [Smooth p] : Smooth (pullback.snd q a) := by
  let E := H.isoPullback
  have he : E.hom ≫ pullback.snd q a = p := H.isoPullback_hom_snd
  have hs : Smooth (E.hom ≫ pullback.snd q a) := he.symm ▸ inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) E.hom _).mp hs

open DeJongAlterations.StableModification.Limits

private abbrev relativeSystem (A k : Type u) [CommRing A] [CommRing k] [Algebra A k] :=
  (fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec

private abbrev relativeCone (A k : Type u) [CommRing A] [CommRing k] [Algebra A k] :=
  fgSpecCone (⊤ : Subalgebra A k)

private abbrev initialLevel (A k : Type u) [CommRing A] [CommRing k] [Algebra A k] :
    (FGSubalgebra A (⊤ : Subalgebra A k))ᵒᵖ := op ⊥

section FixedModel
variable {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
variable {X Y : Scheme.{u}} (g : X ⟶ Y) (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of A))
variable (H : IsPullback g p q (Spec.map (CommRingCat.ofHom (algebraMap A k))))
variable (Etop : Spec (.of k) ≅ (relativeCone A k).pt)
  (Ebot : Spec (.of A) ≅ (relativeSystem A k).obj (initialLevel A k))
variable (hc : Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ Ebot.hom =
  Etop.hom ≫ (relativeCone A k).π.app (initialLevel A k))

private def fixedModel : Model (relativeSystem A k) (relativeCone A k)
    (p ≫ Etop.hom) (initialLevel A k) where
  Y := Y
  fY := q ≫ Ebot.hom
  g := g
  isPullback := move_baseCorners g p q _ H Etop Ebot _ hc

private theorem fixedModel_isFP [IsProper q] [LocallyOfFinitePresentation q] :
    (fixedModel g p q H Etop Ebot hc).IsFP := by
  change LocallyOfFinitePresentation (q ≫ Ebot.hom) ∧
    QuasiCompact (q ≫ Ebot.hom) ∧ QuasiSeparated (q ≫ Ebot.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end FixedModel

section OriginalCoefficientFibre
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable {X Y : Scheme.{u}} (g₀ : X ⟶ Y) (p : X ⟶ Spec (.of T)) (q : Y ⟶ Spec (.of R))
  (φ : R →+* S) (ψ : S →+* T)
  (H : IsPullback g₀ p q (Spec.map (CommRingCat.ofHom (ψ.comp φ))))

private def coefficientOriginalMap : X ⟶ pullback q (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift g₀ (p ≫ Spec.map (CommRingCat.ofHom ψ)) (by
    rw [Category.assoc, ← Spec.map_comp]
    exact H.w)

private theorem coefficientOriginalMap_fst :
    coefficientOriginalMap g₀ p q φ ψ H ≫ pullback.fst _ _ = g₀ := by
  simp only [coefficientOriginalMap, pullback.lift_fst]

private theorem coefficientOriginalMap_snd :
    coefficientOriginalMap g₀ p q φ ψ H ≫ pullback.snd _ _ = p ≫ Spec.map (CommRingCat.ofHom ψ) := by
  simp only [coefficientOriginalMap, pullback.lift_snd]

private theorem coefficientOriginalMap_isPullback :
    IsPullback (coefficientOriginalMap g₀ p q φ ψ H) p
      (pullback.snd q (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom ψ)) := by
  have ho : IsPullback (coefficientOriginalMap g₀ p q φ ψ H ≫ pullback.fst _ _) p q
      (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ)) := by
    rw [coefficientOriginalMap_fst, ← Spec.map_comp]
    exact H
  exact ho.of_right (coefficientOriginalMap_snd g₀ p q φ ψ H) (IsPullback.of_hasPullback _ _)

private theorem smooth_coefficientBaseChange
    [Smooth (pullback.snd q (Spec.map (CommRingCat.ofHom φ)))] :
    Smooth (pullback.snd q (Spec.map (CommRingCat.ofHom (ψ.comp φ)))) :=
  MorphismProperty.of_isPullback
    (coefficientOriginalMap_isPullback (pullback.fst q (Spec.map (CommRingCat.ofHom (ψ.comp φ))))
      (pullback.snd q (Spec.map (CommRingCat.ofHom (ψ.comp φ)))) q φ ψ
      (IsPullback.of_hasPullback _ _)) inferInstance

end OriginalCoefficientFibre

private theorem exists_smooth_relative_coefficient_stage
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of A))
    (H : IsPullback g p q (Spec.map (CommRingCat.ofHom (algebraMap A k))))
    (hinj : Function.Injective (algebraMap A k))
    [Smooth p] [IsProper q] [LocallyOfFinitePresentation q] :
    ∃ B : FGSubalgebra A (⊤ : Subalgebra A k),
      Smooth (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap A B.1)))) := by
  let Etop := ArithmeticFixedSmoothModel.topScalarIso A k
  let Ebot := ArithmeticFixedSmoothModel.bottomScalarIso A k hinj
  have hc : Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ Ebot.hom =
      Etop.hom ≫ (relativeCone A k).π.app (initialLevel A k) :=
    (ArithmeticFixedSmoothModel.top_bottom_scalar_triangle A k hinj).symm
  let m := fixedModel g p q H Etop Ebot hc
  have hm : m.IsFP := fixedModel_isFP g p q H Etop Ebot hc
  let : Smooth (p ≫ Etop.hom) := inferInstance
  obtain ⟨j, h, hs⟩ := ArithmeticFixedSmoothModel.exists_smooth_fixed_model_baseChange m hm
  let B := unop j
  have hh : h = (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op :=
    Subsingleton.elim _ _
  subst h
  let a := Spec.map (CommRingCat.ofHom (algebraMap A B.1))
  have ha : (relativeSystem A k).map
      (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op = a ≫ Ebot.hom :=
    (ArithmeticFixedSmoothModel.bottomScalarIso_hom_stage A k hinj B).symm
  have HP := cancel_baseCorner
    (pullback.fst m.fY ((relativeSystem A k).map
      (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op))
    (pullback.snd m.fY ((relativeSystem A k).map
      (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op))
    m.fY _ Ebot q a (IsPullback.of_hasPullback _ _) rfl ha
  let : Smooth (pullback.snd m.fY ((relativeSystem A k).map
      (homOfLE (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ B)).op)) := hs
  exact ⟨B, smooth_pullback_snd _ _ _ _ HP⟩

open ArithmeticProjectiveOriginalFamily

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
variable (j : X ⟶ NativeProjectiveScheme k N) [IsClosedImmersion j] (extra : Finset k)

/-- The same actual original projective family in the relative coefficient system. -/
def originalFixedModel (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p) :
    Model ((fgDiagram (⊤ : Subalgebra (coefficientBase j extra) k)).op ⋙ Scheme.Spec)
      (fgSpecCone (⊤ : Subalgebra (coefficientBase j extra) k))
      (p ≫ (ArithmeticFixedSmoothModel.topScalarIso (coefficientBase j extra) k).hom)
      (op (⊥ : FGSubalgebra (coefficientBase j extra) (⊤ : Subalgebra (coefficientBase j extra) k))) :=
  fixedModel (originalMap j extra) p (familyProjection j extra)
    (isPullback_originalMap j extra p hjp)
    (ArithmeticFixedSmoothModel.topScalarIso (coefficientBase j extra) k)
    (ArithmeticFixedSmoothModel.bottomScalarIso (coefficientBase j extra) k Subtype.val_injective)
    (ArithmeticFixedSmoothModel.top_bottom_scalar_triangle (coefficientBase j extra) k
      Subtype.val_injective).symm

/-- Properness and finite presentation belong to this actual original model. -/
theorem originalFixedModel_isFP (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p) :
    (originalFixedModel j extra p hjp).IsFP := by
  let : IsProper (familyProjection j extra) := familyProjection_isProper j extra
  let : LocallyOfFinitePresentation (familyProjection j extra) :=
    familyProjection_locallyOfFinitePresentation j extra
  exact fixedModel_isFP _ _ _ _ _ _ _

section ScalarExtension
variable (S : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S)

/-- Literal coefficient base change of the already constructed original family. -/
def scalarFamily : Scheme.{u} :=
  pullback (familyProjection j extra) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS).toRingHom))

/-- Its original coefficient projection. -/
def scalarProjection : scalarFamily j extra S hRS ⟶ Spec (.of S) := pullback.snd _ _

/-- The actual closed embedding obtained by changing coefficients in the original quotient embedding. -/
def scalarEmbedding : scalarFamily j extra S hRS ⟶ NativeProjectiveScheme S N :=
  coefficientEmbedding (familyEmbedding j extra) (Subalgebra.inclusion hRS).toRingHom

/-- Closedness is proved by its actual ambient pullback square. -/
theorem scalarEmbedding_isClosedImmersion : IsClosedImmersion (scalarEmbedding j extra S hRS) := by
  let : IsClosedImmersion (familyEmbedding j extra) := familyEmbedding_isClosedImmersion j extra
  exact coefficientEmbedding_closed _ _

/-- The entire projective structure triangle agrees with the actual scalar projection. -/
theorem scalarEmbedding_projection :
    scalarEmbedding j extra S hRS ≫ nativeStructureMap = scalarProjection j extra S hRS :=
  coefficientEmbedding_projection _ _

/-- The same original quotient embedding yields a genuine projective family over every actual larger base. -/
theorem scalarProjection_isProjectiveFactorization :
    IsProjectiveFactorization (scalarProjection j extra S hRS) :=
  ⟨N, scalarEmbedding j extra S hRS, scalarEmbedding_isClosedImmersion j extra S hRS,
    scalarEmbedding_projection j extra S hRS⟩

variable (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p)

/-- The whole original scheme maps into this same scalar-extended family. -/
def scalarOriginalMap : X ⟶ scalarFamily j extra S hRS :=
  coefficientOriginalMap (originalMap j extra) p (familyProjection j extra)
    (Subalgebra.inclusion hRS).toRingHom (algebraMap S k)
    (isPullback_originalMap j extra p hjp)

/-- The scalar-extended original map retains the entire old original-to-family morphism. -/
theorem scalarOriginalMap_fst :
    scalarOriginalMap j extra S hRS p hjp ≫ pullback.fst _ _ = originalMap j extra :=
  coefficientOriginalMap_fst _ _ _ _ _ _

/-- Its field projection is exactly the same originally supplied structure morphism. -/
theorem scalarOriginalMap_projection :
    scalarOriginalMap j extra S hRS p hjp ≫ scalarProjection j extra S hRS =
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap S k)) :=
  coefficientOriginalMap_snd _ _ _ _ _ _

/-- The whole original coefficient fibre is cartesian, with the original p. -/
theorem isPullback_scalarOriginalMap :
    IsPullback (scalarOriginalMap j extra S hRS p hjp) p (scalarProjection j extra S hRS)
      (Spec.map (CommRingCat.ofHom (algebraMap S k))) :=
  coefficientOriginalMap_isPullback _ _ _ _ _ _

/-- The canonical comparison has the actual entire original X as its source. -/
def scalarFamilyBaseChangeIso : X ≅ pullback (scalarProjection j extra S hRS)
    (Spec.map (CommRingCat.ofHom (algebraMap S k))) :=
  (isPullback_scalarOriginalMap j extra S hRS p hjp).isoPullback

/-- Its first projection is exactly the constructed whole original map. -/
theorem scalarFamilyBaseChangeIso_hom_fst :
    (scalarFamilyBaseChangeIso j extra S hRS p hjp).hom ≫ pullback.fst _ _ =
      scalarOriginalMap j extra S hRS p hjp :=
  (isPullback_scalarOriginalMap j extra S hRS p hjp).isoPullback_hom_fst

/-- Its second projection is exactly the same original p. -/
theorem scalarFamilyBaseChangeIso_hom_snd :
    (scalarFamilyBaseChangeIso j extra S hRS p hjp).hom ≫ pullback.snd _ _ = p :=
  (isPullback_scalarOriginalMap j extra S hRS p hjp).isoPullback_hom_snd

/-- The entire originally given projective embedding survives the same coefficient change. -/
theorem scalarOriginalMap_embedding :
    scalarOriginalMap j extra S hRS p hjp ≫ scalarEmbedding j extra S hRS =
      j ≫ nativeCoefficientMap (algebraMap S k) := by
  apply coefficientEmbedding_original (familyEmbedding j extra) (Subalgebra.inclusion hRS).toRingHom
    j p (algebraMap S k) (scalarOriginalMap j extra S hRS p hjp) _ _ hjp
  · change scalarOriginalMap j extra S hRS p hjp ≫
        pullback.fst (familyProjection j extra)
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS).toRingHom)) ≫
        familyEmbedding j extra = j ≫ nativeCoefficientMap (algebraMap (coefficientBase j extra) k)
    rw [← Category.assoc, scalarOriginalMap_fst]
    exact originalMap_embedding j extra
  · exact scalarOriginalMap_projection j extra S hRS p hjp

/-- Every actual nonnegative projective twist of this same scalar-extended embedding. -/
def scalarTwist (d : ℕ) : (scalarFamily j extra S hRS).Modules :=
  (Scheme.Modules.pullback (scalarEmbedding j extra S hRS)).obj
    (coordinateHyperplaneTwist (R := S) (0 : Fin (N + 1)) (d : ℤ))

/-- All original twists are recovered as whole sheaves on the same entire original X. -/
def scalarTwistPullbackIso (d : ℕ) :
    (Scheme.Modules.pullback (scalarOriginalMap j extra S hRS p hjp)).obj (scalarTwist j extra S hRS d) ≅
      (Scheme.Modules.pullback j).obj (coordinateHyperplaneTwist (R := k) (0 : Fin (N + 1)) (d : ℤ)) :=
  (Scheme.Modules.pullbackComp (scalarOriginalMap j extra S hRS p hjp) (scalarEmbedding j extra S hRS)).app _ ≪≫
  (Scheme.Modules.pullbackCongr (scalarOriginalMap_embedding j extra S hRS p hjp)).app _ ≪≫
  ((Scheme.Modules.pullbackComp j (nativeCoefficientMap (algebraMap S k))).app _).symm ≪≫
  (Scheme.Modules.pullback j).mapIso
    (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso (algebraMap S k) (0 : Fin (N + 1)) d)

/-- The actual first twist of the same embedding is very ample. -/
theorem scalarTwist_one_isVeryAmple :
    SchemeLineAmpleness.IsVeryAmple (scalarProjection j extra S hRS) (scalarTwist j extra S hRS 1) := by
  let : IsClosedImmersion (familyEmbedding j extra) := familyEmbedding_isClosedImmersion j extra
  exact coefficientEmbedding_veryAmple _ _

/-- Its actual first line is ample. -/
theorem scalarTwist_one_isAmple :
    SchemeLineAmpleness.IsAmple (scalarProjection j extra S hRS) (scalarTwist j extra S hRS 1) :=
  AmpleLineTwistGeneration.isAmple_of_isVeryAmple (scalarTwist_one_isVeryAmple j extra S hRS)

end ScalarExtension

/-- Original smoothness produces an actual finite-type integer subalgebra where the SAME family is smooth. -/
theorem exists_smooth_integer_stage (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p)
    [Smooth p] :
    ∃ (S : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S),
      Algebra.FiniteType ℤ S ∧ Smooth (scalarProjection j extra S hRS) := by
  let : IsProper (familyProjection j extra) := familyProjection_isProper j extra
  let : LocallyOfFinitePresentation (familyProjection j extra) :=
    familyProjection_locallyOfFinitePresentation j extra
  obtain ⟨B, hs⟩ := exists_smooth_relative_coefficient_stage (originalMap j extra) p
    (familyProjection j extra) (isPullback_originalMap j extra p hjp) Subtype.val_injective
  let S := B.1.restrictScalars ℤ
  have hRS : coefficientBase j extra ≤ S := by
    intro x hx
    exact B.1.algebraMap_mem (⟨x, hx⟩ : coefficientBase j extra)
  let : Algebra.FiniteType ℤ (coefficientBase j extra) := coefficientBase_finiteType j extra
  let : Algebra.FiniteType (coefficientBase j extra) B.1 :=
    (Subalgebra.fg_iff_finiteType _).mp B.2.1
  have hFT : Algebra.FiniteType ℤ B.1 :=
    Algebra.FiniteType.trans (S := coefficientBase j extra) inferInstance inferInstance
  exact ⟨S, hRS, hFT, hs⟩

/-- The actual smooth-family stage produces a nonzero localization whose arithmetic base is itself smooth. -/
theorem exists_smooth_localized_integer_stage [CharZero k]
    (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p) [Smooth p] :
    ∃ (S : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S) (s : S) (hs : s ≠ 0),
      Algebra.FiniteType ℤ S ∧ Smooth (scalarProjection j extra S hRS) ∧
      Algebra.Smooth ℤ (ArithmeticSmoothCoefficientBase.localizedCoefficientRing S s hs) ∧
      Algebra.FiniteType ℤ (ArithmeticSmoothCoefficientBase.localizedCoefficientRing S s hs) ∧
      Smooth (scalarProjection j extra (ArithmeticSmoothCoefficientBase.localizedCoefficientRing S s hs)
        (hRS.trans (ArithmeticSmoothCoefficientBase.le_localizedCoefficientRing S s hs))) := by
  obtain ⟨S, hRS, hFT, hSmooth⟩ := exists_smooth_integer_stage j extra p hjp
  let : Algebra.FiniteType ℤ S := hFT
  obtain ⟨s, hs, _, hBaseSmooth, hBaseFT, _, _, _, hSS'⟩ :=
    ArithmeticSmoothCoefficientBase.exists_smooth_localizedCoefficientRing S
  let : Smooth (pullback.snd (familyProjection j extra)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS).toRingHom))) := hSmooth
  refine ⟨S, hRS, s, hs, hFT, hSmooth, hBaseSmooth, hBaseFT, ?_⟩
  exact smooth_coefficientBaseChange (familyProjection j extra)
    (Subalgebra.inclusion hRS).toRingHom (Subalgebra.inclusion hSS').toRingHom

/-- A genuine smooth projective arithmetic family for the same original X, p, j and all nonnegative twists.
The actual base, its smoothness, and all comparison data are produced internally. -/
theorem exists_smooth_projective_arithmetic_family [CharZero k]
    (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p) [Smooth p] :
    ∃ (S : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S),
      Algebra.Smooth ℤ S ∧ Algebra.FiniteType ℤ S ∧
      Smooth (scalarProjection j extra S hRS) ∧
      IsProjectiveFactorization (scalarProjection j extra S hRS) ∧
      IsPullback (scalarOriginalMap j extra S hRS p hjp) p (scalarProjection j extra S hRS)
        (Spec.map (CommRingCat.ofHom (algebraMap S k))) ∧
      scalarOriginalMap j extra S hRS p hjp ≫ scalarEmbedding j extra S hRS =
        j ≫ nativeCoefficientMap (algebraMap S k) ∧
      (∀ d : ℕ, Nonempty
        ((Scheme.Modules.pullback (scalarOriginalMap j extra S hRS p hjp)).obj (scalarTwist j extra S hRS d) ≅
          (Scheme.Modules.pullback j).obj
            (coordinateHyperplaneTwist (R := k) (0 : Fin (N + 1)) (d : ℤ)))) ∧
      SchemeLineAmpleness.IsAmple (scalarProjection j extra S hRS) (scalarTwist j extra S hRS 1) := by
  obtain ⟨S, hRS, s, hs, _, _, hBaseSmooth, hBaseFT, hFamilySmooth⟩ :=
    exists_smooth_localized_integer_stage j extra p hjp
  let S' := ArithmeticSmoothCoefficientBase.localizedCoefficientRing S s hs
  have hRS' : coefficientBase j extra ≤ S' :=
    hRS.trans (ArithmeticSmoothCoefficientBase.le_localizedCoefficientRing S s hs)
  exact ⟨S', hRS', hBaseSmooth, hBaseFT, hFamilySmooth,
    scalarProjection_isProjectiveFactorization j extra S' hRS',
    isPullback_scalarOriginalMap j extra S' hRS' p hjp,
    scalarOriginalMap_embedding j extra S' hRS' p hjp,
    fun d => ⟨scalarTwistPullbackIso j extra S' hRS' p hjp d⟩,
    scalarTwist_one_isAmple j extra S' hRS'⟩

end EnvelopeProperty.ArithmeticSmoothProjectiveOriginalFamily
