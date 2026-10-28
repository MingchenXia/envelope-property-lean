import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionIntegralStrata
import EnvelopeProperty.Projective.TestConfigurationSectionTransport
import EnvelopeProperty.AlgGeom.ProjectiveAmpleSectionContainingClosedSubset

/-! Actual single-section mixed Euler restriction on the original Cartier cut. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace MvPolynomial
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open SchemeCoherentEulerCharacteristic
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory MvPolynomial.gradedAlgebra

theorem isAmple_closedPullback {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsClosedImmersion i] (p : X ⟶ Spec (.of R))
    (L : X.Modules) (hA : SchemeLineAmpleness.IsAmple p L) :
    SchemeLineAmpleness.IsAmple (i ≫ p) ((Scheme.Modules.pullback i).obj L) := by
  obtain ⟨hL, r, hr, n, g, hg, hbase, ⟨e⟩⟩ := hA
  let : IsClosedImmersion g := hg
  let H := coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1
  let e' : (Scheme.Modules.pullback (i ≫ g)).obj H ≅
      CanonicalGeometry.bundleTensorPower ((Scheme.Modules.pullback i).obj L) r :=
    ((pullbackComp i g).app H).symm ≪≫ (Scheme.Modules.pullback i).mapIso e ≪≫
      TestConfigurationSectionTransport.tensorPowerPullbackIso i L r
  refine ⟨hL.pullback i, r, hr, n, i ≫ g, inferInstance, ?_, ⟨e'⟩⟩
  exact (Category.assoc i g _).trans (congrArg (fun q => i ≫ q) hbase)

variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]

theorem mixedEulerDifference_sectionDifference [X.IsSeparated] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProjective f]
    (A : X.Modules) (hA : IsInvertible A) (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    let I := LineSectionZeroIdeal.zeroIdeal A hA s
    letI : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
    ∀ (ls : List X.Modules), (∀ K ∈ ls, IsInvertible K) → ∀ (T : X.Modules), IsInvertible T →
      mixedEulerDifference f (A :: ls) T =
        mixedEulerDifference (I.subschemeι ≫ f) (ls.map (Scheme.Modules.pullback I.subschemeι).obj)
          ((Scheme.Modules.pullback I.subschemeι).obj (T ⊗ A)) := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  let i := I.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let Fi := Scheme.Modules.pullback i
  let : Fi.Monoidal := Scheme.Modules.pullbackMonoidal i
  change ∀ (ls : List X.Modules), (∀ K ∈ ls, IsInvertible K) → ∀ (T : X.Modules), IsInvertible T →
    mixedEulerDifference f (A :: ls) T =
      mixedEulerDifference (i ≫ f) (ls.map Fi.obj) (Fi.obj (T ⊗ A))
  intro ls
  induction ls with
  | nil =>
    intro _ T hT
    have h := eulerCharacteristic_sectionFirstDifference f hf A T hA hT s hs
    change eulerCharacteristic f (A ⊗ T) - eulerCharacteristic f T =
      eulerCharacteristic (i ≫ f) (Fi.obj (A ⊗ T)) at h
    let e : A ⊗ T ≅ T ⊗ A := β_ A T
    rw [eulerCharacteristic_eq_of_iso f e,
      eulerCharacteristic_eq_of_iso (i ≫ f) (Fi.mapIso e)] at h
    exact h
  | cons K ls ih =>
    intro hls T hT
    let hK : IsInvertible K := hls K (by simp)
    have ht : ∀ M ∈ ls, IsInvertible M := fun M hM => hls M (by simp [hM])
    let hTK : IsInvertible (T ⊗ K) :=
      (hT.tensorObj hK).of_iso (ModularCurves.monoidalTensorObjIso T K)
    have h₁ := ih ht (T ⊗ K) hTK
    have h₂ := ih ht T hT
    let e : (T ⊗ K) ⊗ A ≅ (T ⊗ A) ⊗ K :=
      α_ T K A ≪≫ (Iso.refl T ⊗ᵢ β_ K A) ≪≫ (α_ T A K).symm
    let eI : Fi.obj ((T ⊗ K) ⊗ A) ≅ Fi.obj (T ⊗ A) ⊗ Fi.obj K :=
      Fi.mapIso e ≪≫ (Functor.Monoidal.μIso Fi (T ⊗ A) K).symm
    rw [mixedEulerDifference_eq_of_iso (i ≫ f) (ls.map Fi.obj) eI] at h₁
    rw [mixedEulerDifference_swap f A K ls T]
    change mixedEulerDifference f (A :: ls) (T ⊗ K) - mixedEulerDifference f (A :: ls) T =
      mixedEulerDifference (i ≫ f) (ls.map Fi.obj) (Fi.obj (T ⊗ A) ⊗ Fi.obj K) -
        mixedEulerDifference (i ≫ f) (ls.map Fi.obj) (Fi.obj (T ⊗ A))
    rw [h₁, h₂]


private theorem finiteType_unit_sectionIntersection (Y : Scheme.{u}) :
    (unitObj Y).IsFiniteType := by
  let : (unitObj Y).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := Y.ringCatSheaf) (unitObj Y)

theorem mixedEulerDifference_replicate_closed_unit_le [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple f A)
    {Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j] :
    letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace j
    mixedEulerDifference (j ≫ f) (List.replicate d ((Scheme.Modules.pullback j).obj A)) (unitObj Z) ≤
      mixedEulerDifference f (List.replicate d A) (unitObj X) := by
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace j
  let : Z.IsSeparated := ⟨by
    have hsep : IsSeparated (j ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  let : IsProper f := hf.isProper
  let : LocallyOfFiniteType f := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType := finiteType_unit_sectionIntersection X
  let : (unitObj Z).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj Z).IsFiniteType := finiteType_unit_sectionIntersection Z
  let Q := (Scheme.Modules.pushforward j).obj (unitObj Z)
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom j
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion j
  let K := ModularCurves.idealModule j
  let : K.IsQuasicoherent := isQuasicoherent_kernel (FiniteClosedIdealEuler.quotientMap j)
  let : K.IsFiniteType := isFiniteType_kernel (FiniteClosedIdealEuler.quotientMap j)
  let S := FiniteClosedIdealEuler.sequence j
  let : S.X₁.IsQuasicoherent := by change K.IsQuasicoherent; infer_instance
  let : S.X₁.IsFiniteType := by change K.IsFiniteType; infer_instance
  let : S.X₂.IsQuasicoherent := by change (unitObj X).IsQuasicoherent; infer_instance
  let : S.X₂.IsFiniteType := by change (unitObj X).IsFiniteType; infer_instance
  let : S.X₃.IsQuasicoherent := by change Q.IsQuasicoherent; infer_instance
  let : S.X₃.IsFiniteType := by change Q.IsFiniteType; infer_instance
  have hls : ∀ L ∈ List.replicate d A, IsInvertible L := by
    intro L hL
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
    exact hA.1
  have hadd := mixedEulerDifference_add f (List.replicate d A) hls S
    (FiniteClosedIdealEuler.sequence_shortExact j)
  have hpush := mixedEulerDifference_pushforward f j (List.replicate d A) hls (unitObj Z)
  simp only [List.map_replicate] at hpush
  change mixedEulerDifference f (List.replicate d A) (unitObj X) =
    mixedEulerDifference f (List.replicate d A) K + mixedEulerDifference f (List.replicate d A) Q at hadd
  rw [hpush] at hadd
  have hK := mixedEulerDifference_replicate_nonneg_of_isAmple f d hdim K A hA
  omega


private theorem isProjective_closedComp_sectionIntersection {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  refine ⟨E, hE, hEF, i ≫ j, inferInstance, ?_⟩
  exact (Category.assoc i j E.projectiveBundleπ).trans
    (congrArg (fun q => i ≫ q) hjp)

theorem mixedEulerDifference_replicate_pos_of_isAmple [X.IsSeparated] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (d : ℕ)
    (hdim : topologicalKrullDim X = d) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple f A) :
    0 < mixedEulerDifference f (List.replicate d A) (unitObj X) := by
  have all : ∀ m : ℕ, ∀ {Y : Scheme.{u}} [IsIntegral Y] [CompactSpace Y] [Y.IsSeparated]
      (g : Y ⟶ Spec (.of k)) [IsProjective g] (_ : topologicalKrullDim Y = m)
      (B : Y.Modules), SchemeLineAmpleness.IsAmple g B →
      0 < mixedEulerDifference g (List.replicate m B) (unitObj Y) := by
    intro m
    induction m with
    | zero =>
      intro Y _ _ _ g _ hdimY B _hB
      change 0 < eulerCharacteristic g (unitObj Y)
      exact eulerCharacteristic_unit_pos_of_dimension_le_zero g hdimY.le
    | succ d ih =>
      intro Y _ _ _ g _ hdimY B hB
      obtain ⟨eta, hproper, hdimZ⟩ := exists_pointClosure_dimension_eq d hdimY
      let Z : Closeds Y := ⟨closure ({eta} : Set Y), isClosed_closure⟩
      let IZ := Scheme.IdealSheafData.vanishingIdeal Z
      let : IsIntegral IZ.subscheme := SchemePointClosureIntegral.isIntegral_pointClosure eta
      let : CompactSpace IZ.subscheme := QuasiCompact.compactSpace_of_compactSpace IZ.subschemeι
      let : IZ.subscheme.IsSeparated := ⟨by
        have hsep : IsSeparated (IZ.subschemeι ≫ terminal.from Y) := inferInstance
        simpa only [terminal.comp_from] using hsep⟩
      obtain ⟨r, hr, s, hs, j, hj, _htriangle⟩ :=
        ProjectiveAmpleSectionContainingClosedSubset.exists_nonzero_power_section_containing_closed
          g Z hproper B hB
      let P := CanonicalGeometry.bundleTensorPower B r
      let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hB.1 r
      let D := LineSectionZeroIdeal.zeroIdeal P hP s
      let i := D.subschemeι
      let j' : IZ.subscheme ⟶ D.subscheme := j
      let : IsClosedImmersion j' := hj
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
      let : D.subscheme.IsSeparated := ⟨by
        have hsep : IsSeparated (i ≫ terminal.from Y) := inferInstance
        simpa only [terminal.comp_from] using hsep⟩
      let : IsProjective (i ≫ g) := isProjective_closedComp_sectionIntersection i g
      let : IsProjective (j' ≫ (i ≫ g)) := isProjective_closedComp_sectionIntersection j' (i ≫ g)
      let BD := (Scheme.Modules.pullback i).obj B
      let BZ := (Scheme.Modules.pullback j').obj BD
      have hBD : SchemeLineAmpleness.IsAmple (i ≫ g) BD := isAmple_closedPullback i g B hB
      have hBZ : SchemeLineAmpleness.IsAmple (j' ≫ (i ≫ g)) BZ :=
        isAmple_closedPullback j' (i ≫ g) BD hBD
      have hZpos := ih (j' ≫ (i ≫ g)) hdimZ BZ hBZ
      have hdimD : topologicalKrullDim D.subscheme ≤ d :=
        sectionZero_dimension_drop d hdimY.le P hP s hs
      have hmono := mixedEulerDifference_replicate_closed_unit_le (i ≫ g) d hdimD BD hBD j'
      have hDpos : 0 < mixedEulerDifference (i ≫ g) (List.replicate d BD) (unitObj D.subscheme) :=
        lt_of_lt_of_le hZpos hmono
      let : (unitObj Y).IsQuasicoherent := isInvertible_unit.isQuasicoherent
      let : (unitObj Y).IsFiniteType := finiteType_unit_sectionIntersection Y
      have hls : ∀ L ∈ List.replicate d B, IsInvertible L := by
        intro L hL
        obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
        exact hB.1
      have hlsD : ∀ L ∈ List.replicate d BD, IsInvertible L := by
        intro L hL
        obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
        exact hBD.1
      let T := (Scheme.Modules.pullback i).obj (unitObj Y ⊗ P)
      have hUP : IsInvertible (unitObj Y ⊗ P) :=
        (isInvertible_unit.tensorObj hP).of_iso (ModularCurves.monoidalTensorObjIso (unitObj Y) P)
      have hT : IsInvertible T := hUP.pullback i
      have hcoeff := mixedEulerDifference_eq_unit_of_dimension_le (i ≫ g) d hdimD
        (List.replicate d BD) (by simp) hlsD T hT
      have hcut := mixedEulerDifference_sectionDifference g P hP s hs
        (List.replicate d B) hls (unitObj Y) isInvertible_unit
      simp only [List.map_replicate] at hcut
      change mixedEulerDifference g (P :: List.replicate d B) (unitObj Y) =
        mixedEulerDifference (i ≫ g) (List.replicate d BD) T at hcut
      rw [mixedEulerDifference_tensorPower_cons g (d + 1) hdimY.le B hB.1
        (List.replicate d B) (by simp) hls (unitObj Y) r, hcoeff] at hcut
      have hmul : 0 < (r : ℤ) * mixedEulerDifference g (B :: List.replicate d B) (unitObj Y) := by
        rw [hcut]
        exact hDpos
      have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
      have hpos : 0 < mixedEulerDifference g (B :: List.replicate d B) (unitObj Y) := by
        by_contra hn
        have hn' : mixedEulerDifference g (B :: List.replicate d B) (unitObj Y) ≤ 0 := le_of_not_gt hn
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hrZ.le hn')) hmul
      simpa only [List.replicate_succ] using hpos
  exact all d f hdim A hA

#check @isAmple_closedPullback
#print axioms isAmple_closedPullback
#check @mixedEulerDifference_sectionDifference
#print axioms mixedEulerDifference_sectionDifference
#check @mixedEulerDifference_replicate_closed_unit_le
#print axioms mixedEulerDifference_replicate_closed_unit_le
#check @mixedEulerDifference_replicate_pos_of_isAmple
#print axioms mixedEulerDifference_replicate_pos_of_isAmple
end EnvelopeProperty.SeshadriAmplenessCriterion
