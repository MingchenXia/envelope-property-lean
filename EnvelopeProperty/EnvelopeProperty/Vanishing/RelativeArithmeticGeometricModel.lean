import EnvelopeProperty.Vanishing.RelativeArithmeticOriginalProjectiveModel
import EnvelopeProperty.Vanishing.RelativeArithmeticAmbientBaseChange

/-! # The whole original smooth family stays projective over its modeled affine base

The projective base is the actual tensor algebra over the arithmetic
coefficient subalgebra.  The source is smooth of the original total
dimension and separated over that coefficient ring, without being assumed
proper there.  The whole original O(1) pullback is retained.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open Scheme.Modules
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticGeometricModel
open ProjBerk DeJongAlterations.StableModification.Limits
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem original_square
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {i : (FGSubalgebra A (⊤ : Subalgebra A k))ᵒᵖ}
    (m : Model ((fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec)
      (fgSpecCone (⊤ : Subalgebra A k))
      (f ≫ (ArithmeticFixedSmoothModel.topScalarIso A k).hom) i) :
    IsPullback m.g f m.fY
      (Spec.map (CommRingCat.ofHom (algebraMap (unop i).1 k))) := by
  let E := ArithmeticFixedSmoothModel.topScalarIso A k
  apply m.isPullback.of_iso (Iso.refl _) (Iso.refl _) E.symm (Iso.refl _)
  · simp
  · simp [E]
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    have hs : E.hom ≫ (fgSpecCone (⊤ : Subalgebra A k)).π.app i =
        Spec.map (CommRingCat.ofHom (algebraMap (unop i).1 k)) :=
      ArithmeticFixedSmoothModel.topScalarIso_hom_stage A k (unop i)
    exact (Iso.eq_inv_comp E).2 hs

private theorem cancel_baseCorner {P Q S T U : Scheme.{u}}
    (a : P ⟶ Q) (p : P ⟶ S) (q : Q ⟶ T) (b : S ⟶ T)
    (E : U ≅ T) (q₀ : Q ⟶ U) (b₀ : S ⟶ U)
    (H : IsPullback a p q b) (hq : q = q₀ ≫ E.hom)
    (hb : b = b₀ ≫ E.hom) : IsPullback a p q₀ b₀ := by
  apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) E.symm
  · simp
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, hq, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, hb, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- Restrict only the coefficient scalars, keeping the same geometric objects. -/
private theorem restrict_coefficient_model
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    (A : Subalgebra ℤ k) [Algebra.FiniteType ℤ A]
    {B : Type u} [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (C₀ : Subalgebra A k) [Algebra.FiniteType A C₀]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) {d : ℕ}
    (j : X ⟶ NativeProjectiveScheme R d) (e : k ⊗[A] B ≃ₐ[k] R)
    (a : X ⟶ Y) (p : Y ⟶ Spec (.of C₀))
    (q : Y ⟶ Spec (.of (C₀ ⊗[A] B))) (T : Y.Modules)
    (H : IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap C₀ k))))
    (hn : SmoothOfRelativeDimension n p) (hsep : IsSeparated p) (hqc : QuasiCompact p)
    (hqp : q ≫ Spec.map (CommRingCat.ofHom (algebraMap C₀ (C₀ ⊗[A] B))) = p)
    (hVT : SchemeLineAmpleness.IsVeryAmple q T)
    (eT : (Scheme.Modules.pullback a).obj T ≅ (Scheme.Modules.pullback j).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1)) :
    ∃ (C : Subalgebra ℤ k), Algebra.FiniteType ℤ C ∧
      ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D),
        Algebra.FinitePresentation C D ∧ Nonempty (k ⊗[C] D ≃ₐ[k] R) ∧
        ∃ (Y : Scheme.{u}) (a : X ⟶ Y) (fC : Y ⟶ Spec (.of C))
          (gD : Y ⟶ Spec (.of D)) (T : Y.Modules),
          IsPullback a f fC (Spec.map (CommRingCat.ofHom (algebraMap C k))) ∧
          SmoothOfRelativeDimension n fC ∧ IsSeparated fC ∧
          QuasiCompact fC ∧
          gD ≫ Spec.map (CommRingCat.ofHom (algebraMap C D)) = fC ∧
          SchemeLineAmpleness.IsVeryAmple gD T ∧
          Nonempty ((Scheme.Modules.pullback a).obj T ≅
            (Scheme.Modules.pullback j).obj
              (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1)) := by
  let C := C₀.restrictScalars ℤ
  let D := C₀ ⊗[A] B
  let : Algebra (C₀.restrictScalars ℤ) (C₀ ⊗[A] B) := by
    change Algebra C₀ (C₀ ⊗[A] B)
    infer_instance
  have hFTC₀ : Algebra.FiniteType ℤ C₀ :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hFTC : Algebra.FiniteType ℤ C := hFTC₀
  have hFPD : Algebra.FinitePresentation C D :=
    Algebra.FinitePresentation.baseChange (R := A) (A := B) C₀
  let eD : k ⊗[C] D ≃ₐ[k] R :=
    (Algebra.TensorProduct.cancelBaseChange A C₀ k k B).trans e
  exact ⟨C, hFTC, D, inferInstance, inferInstance, hFPD, ⟨eD⟩,
    Y, a, p, q, T, H, hn, hsep, hqc, hqp, hVT, ⟨eT⟩⟩

/-- Assemble the native geometric family from its already produced coefficient stage. -/
private theorem geometric_of_stage
    {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    (A : Subalgebra ℤ k) [Algebra.FiniteType ℤ A]
    {B : Type u} [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n d : ℕ)
    (j : X ⟶ NativeProjectiveScheme R d) (e : k ⊗[A] B ≃ₐ[k] R)
    {l : (FGSubalgebra A (⊤ : Subalgebra A k))ᵒᵖ}
    (h : l ⟶ op (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)))
    (m : Model ((fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec)
      (fgSpecCone (⊤ : Subalgebra A k))
      (f ≫ (ArithmeticFixedSmoothModel.topScalarIso A k).hom) l)
    (ι : m.Y ⟶ ((RelativeArithmeticJointModel.projectiveAmbient_fixedModel
      e Subtype.val_injective d).baseChange h).Y)
    (hm : m.IsFP) (hn : SmoothOfRelativeDimension n m.fY)
    (hι : IsClosedImmersion ι)
    (hbase : ι ≫ ((RelativeArithmeticJointModel.projectiveAmbient_fixedModel
      e Subtype.val_injective d).baseChange h).fY = m.fY)
    (horiginal : m.g ≫ ι = j ≫ ((RelativeArithmeticJointModel.projectiveAmbient_fixedModel
      e Subtype.val_injective d).baseChange h).g) :
    ∃ (C : Subalgebra ℤ k), Algebra.FiniteType ℤ C ∧
      ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D),
        Algebra.FinitePresentation C D ∧ Nonempty (k ⊗[C] D ≃ₐ[k] R) ∧
        ∃ (Y : Scheme.{u}) (a : X ⟶ Y) (fC : Y ⟶ Spec (.of C))
          (gD : Y ⟶ Spec (.of D)) (T : Y.Modules),
          IsPullback a f fC (Spec.map (CommRingCat.ofHom (algebraMap C k))) ∧
          SmoothOfRelativeDimension n fC ∧ IsSeparated fC ∧
          QuasiCompact fC ∧
          gD ≫ Spec.map (CommRingCat.ofHom (algebraMap C D)) = fC ∧
          SchemeLineAmpleness.IsVeryAmple gD T ∧
          Nonempty ((Scheme.Modules.pullback a).obj T ≅
            (Scheme.Modules.pullback j).obj
              (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1)) := by
  let C₀ := unop l
  let D := C₀.1 ⊗[A] B
  let r := RelativeArithmeticJointModel.projectiveAmbient_fixedModel
    e (show Function.Injective (algebraMap A k) from Subtype.val_injective) d
  let qB := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let qP := nativeStructureMap (R := B) (n := d) ≫ qB
  let Eb := ArithmeticFixedSmoothModel.bottomScalarIso A k Subtype.val_injective
  let c := Spec.map (CommRingCat.ofHom (algebraMap A C₀.1))
  have hh : h = (homOfLE
      (bot_le : (⊥ : FGSubalgebra A (⊤ : Subalgebra A k)) ≤ C₀)).op :=
    Subsingleton.elim _ _
  have hmap : ((fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec).map h = c ≫ Eb.hom := by
    rw [hh]
    exact (ArithmeticFixedSmoothModel.bottomScalarIso_hom_stage A k
      Subtype.val_injective C₀).symm
  let rπ : (r.baseChange h).Y ⟶ NativeProjectiveScheme B d :=
    pullback.fst r.fY (((fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec).map h)
  have HC : IsPullback rπ (r.baseChange h).fY qP c :=
    cancel_baseCorner _ _ _ _ Eb qP c (IsPullback.of_hasPullback _ _) rfl hmap
  let E : (r.baseChange h).Y ≅ pullback qP c := HC.isoPullback
  have hEsnd : E.hom ≫ pullback.snd qP c = (r.baseChange h).fY :=
    HC.isoPullback_hom_snd
  have hEfst : E.hom ≫ pullback.fst qP c = rπ := HC.isoPullback_hom_fst
  let jC : m.Y ⟶ pullback qP c := ι ≫ E.hom
  let gD := jC ≫ RelativeArithmeticAmbientBaseChange.relativeMap
    (A := A) (B := B) (C := C₀.1) d
  let O := coordinateHyperplaneTwist (R := B) (0 : Fin (d + 1)) 1
  let T := (Scheme.Modules.pullback jC).obj
    ((Scheme.Modules.pullback (pullback.fst qP c)).obj O)
  let : IsClosedImmersion ι := hι
  let : IsClosedImmersion jC := inferInstance
  have hVT : SchemeLineAmpleness.IsVeryAmple gD T :=
    SchemeAmpleClosedRestriction.veryAmple_pullback
      (RelativeArithmeticAmbientBaseChange.twist_isVeryAmple
        (A := A) (B := B) (C := C₀.1) d) jC
  have hjCbase : jC ≫ pullback.snd qP c = m.fY :=
    (Category.assoc ι E.hom (pullback.snd qP c)).trans
      ((congrArg (fun z => ι ≫ z) hEsnd).trans hbase)
  have hCoeff : RelativeArithmeticAmbientBaseChange.relativeMap
      (A := A) (B := B) (C := C₀.1) d ≫
        Spec.map (CommRingCat.ofHom (algebraMap C₀.1 D)) = pullback.snd qP c :=
    RelativeArithmeticAmbientBaseChange.relativeMap_coefficient
      (A := A) (B := B) (C := C₀.1) d
  have htriangle : gD ≫ Spec.map (CommRingCat.ofHom (algebraMap C₀.1 D)) = m.fY :=
    (Category.assoc jC (RelativeArithmeticAmbientBaseChange.relativeMap
      (A := A) (B := B) (C := C₀.1) d)
        (Spec.map (CommRingCat.ofHom (algebraMap C₀.1 D)))).trans
      ((congrArg (fun z => jC ≫ z) hCoeff).trans hjCbase)
  have hRπ : (r.baseChange h).g ≫ rπ =
      nativeCoefficientMap (RelativeArithmeticBaseModel.originalMap e) := by
    change (r.baseChange h).g ≫ pullback.fst r.fY
      (((fgDiagram (⊤ : Subalgebra A k)).op ⋙ Scheme.Spec).map h) = r.g
    dsimp only [Model.baseChange]
    rw [baseChangeCone_π_app]
    exact pullback.lift_fst _ _ _
  have horiginalAmbient : (m.g ≫ jC) ≫ pullback.fst qP c =
      j ≫ nativeCoefficientMap (RelativeArithmeticBaseModel.originalMap e) := by
    have hassoc : (m.g ≫ jC) ≫ pullback.fst qP c =
        (m.g ≫ ι) ≫ (E.hom ≫ pullback.fst qP c) := by
      simp only [jC, Category.assoc]
    exact hassoc.trans
      ((congrArg₂ (fun z w => z ≫ w) horiginal hEfst).trans
        ((Category.assoc j (r.baseChange h).g rπ).trans
          (congrArg (fun z => j ≫ z) hRπ)))
  let eT : (Scheme.Modules.pullback m.g).obj T ≅
      (Scheme.Modules.pullback j).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1) :=
    (Scheme.Modules.pullbackComp m.g jC).app _ ≪≫
      (Scheme.Modules.pullbackComp (m.g ≫ jC) (pullback.fst qP c)).app O ≪≫
      (Scheme.Modules.pullbackCongr horiginalAmbient).app O ≪≫
      ((Scheme.Modules.pullbackComp j
        (nativeCoefficientMap (RelativeArithmeticBaseModel.originalMap e))).app O).symm ≪≫
      (Scheme.Modules.pullback j).mapIso
        (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso
          (RelativeArithmeticBaseModel.originalMap e) (0 : Fin (d + 1)) 1)
  let : Algebra.FiniteType A C₀.1 := (Subalgebra.fg_iff_finiteType _).mp C₀.2.1
  let : IsProper (nativeStructureMap (R := B) (n := d)) := nativeStructureMap_isProper
  let : IsSeparated (nativeStructureMap (R := B) (n := d)) := inferInstance
  let : IsSeparated qP := inferInstance
  let : IsSeparated (pullback.snd qP c) := inferInstance
  have hsepComp : IsSeparated (jC ≫ pullback.snd qP c) := inferInstance
  have hsep : IsSeparated m.fY := by
    exact hjCbase ▸ hsepComp
  exact restrict_coefficient_model A C₀.1 f n j e m.g m.fY gD T
    (original_square f m) hn hsep hm.2.1 htriangle hVT eT

/-- The original relative embedding constructs a smooth separated arithmetic
family, projective over a distinct modeled affine algebra with its actual
original tensor fibre.  Its very ample line recovers the SAME original O(1). -/
theorem exists_original_geometric_model
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (g : X ⟶ Spec (.of R))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (d : ℕ) (j : X ⟶ NativeProjectiveScheme R d) [IsClosedImmersion j]
    (hj : j ≫ nativeStructureMap = g) :
    ∃ (C : Subalgebra ℤ k), Algebra.FiniteType ℤ C ∧
      ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D),
        Algebra.FinitePresentation C D ∧ Nonempty (k ⊗[C] D ≃ₐ[k] R) ∧
        ∃ (Y : Scheme.{u}) (a : X ⟶ Y) (fC : Y ⟶ Spec (.of C))
          (gD : Y ⟶ Spec (.of D)) (T : Y.Modules),
          IsPullback a f fC (Spec.map (CommRingCat.ofHom (algebraMap C k))) ∧
          SmoothOfRelativeDimension n fC ∧ IsSeparated fC ∧
          QuasiCompact fC ∧
          gD ≫ Spec.map (CommRingCat.ofHom (algebraMap C D)) = fC ∧
          SchemeLineAmpleness.IsVeryAmple gD T ∧
          Nonempty ((Scheme.Modules.pullback a).obj T ≅
            (Scheme.Modules.pullback j).obj
              (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1)) := by
  obtain ⟨A, _, hFTA, B, hB, hAB, hFPB, e, l, h, m, ι,
      hm, hn, hι, hbase, horiginal⟩ :=
    RelativeArithmeticOriginalProjectiveModel.exists_original_projective_stage
      f g hg n d j hj
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Algebra.FinitePresentation A B := hFPB
  let : Algebra.FiniteType ℤ A := hFTA
  exact geometric_of_stage A f n d j e h m ι hm hn hι hbase horiginal

end EnvelopeProperty.Vanishing.RelativeArithmeticGeometricModel
