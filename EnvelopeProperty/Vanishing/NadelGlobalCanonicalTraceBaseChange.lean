import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSmooth
import EnvelopeProperty.AlgGeom.Canonical.ExteriorPullbackSections
import EnvelopeProperty.Vanishing.NadelMixedKummerDimensionGeometry
import EnvelopeProperty.Vanishing.NadelCanonicalMixedPurification

/-! # Actual canonical sections on the same whole mixed unit cover

The original mixed source need not have a global differential basis.  The
already proved entire smooth-etale canonical differential and genuine affine
pullback-sections comparison provide the required whole canonical comparison.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite
open CanonicalGeometry
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Affine
variable {k : Type u} [Field k] {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (f : X ⟶ Spec (.of k)) (g : Z ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Etale g]

/-- Actual canonical affine base change, without any original global cotangent frame. -/
def sectionsIso :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (ModuleCat.extendScalars g.appTop.hom).obj
        ((exteriorCotangentSheaf f n).val.obj (op ⊤)) ≅
      (exteriorCotangentSheaf (g ≫ f) n).val.obj (op ⊤) := by
  letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  letI : IsIso (exteriorCotangentSheafPullbackMap f g n) :=
    NadelBlowupCanonicalEtaleSmooth.etale_isIso f n g
  let E := SheafOfModules.evaluation Z.ringCatSheaf (op (⊤ : Z.Opens))
  exact Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n) ≪≫
    E.mapIso (asIso (exteriorCotangentSheafPullbackMap f g n))

/-- The entire map is the SAME actual affine pullback comparison followed by
 the SAME original canonical differential. -/
theorem sectionsIso_hom :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (sectionsIso f g n).hom =
      (Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom ≫
        (exteriorCotangentSheafPullbackMap f g n).val.app (op ⊤) := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  rfl

/-- The original section unit followed by the native canonical differential
 is its SAME original adjoint; every section is retained. -/
theorem sectionsIso_one_tmul (w : Γ(exteriorCotangentSheaf f n, ⊤)) :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (sectionsIso f g n).hom ((1 : Γ(Z, ⊤)) ⊗ₜ[Γ(X, ⊤)] w) =
      (exteriorCotangentSheafMorphism f g n).val.app (op ⊤) w := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  rw [sectionsIso_hom]
  change (exteriorCotangentSheafPullbackMap f g n).val.app (op ⊤)
    ((Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom
      ((1 : Γ(Z, ⊤)) ⊗ₜ[Γ(X, ⊤)] w)) = _
  rw [Scheme.Modules.affinePullbackΓIso_hom_one_tmul]
  have hu : Scheme.Modules.affinePullbackUnitTop g (exteriorCotangentSheaf f n) w =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (exteriorCotangentSheaf f n)).val.app (op ⊤) w := by
    change ((Scheme.Modules.pullback g).obj (exteriorCotangentSheaf f n)).presheaf.map
      (𝟙 (op (⊤ : Z.Opens))) _ = _
    exact congr($(((Scheme.Modules.pullback g).obj
      (exteriorCotangentSheaf f n)).presheaf.map_id (op ⊤)).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (exteriorCotangentSheaf f n)).val.app (op ⊤) w))
  rw [hu]
  exact congr($(exteriorCotangentSheafPullbackMap_unit f g n).val.app (op ⊤) |>.hom w)

/-- Every actual original pure tensor retains the true differential, not a
 separately matched basis map. -/
theorem sectionsIso_tmul (s : Γ(Z, ⊤)) (w : Γ(exteriorCotangentSheaf f n, ⊤)) :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (sectionsIso f g n).hom (s ⊗ₜ[Γ(X, ⊤)] w) =
      s • (show Γ(exteriorCotangentSheaf (g ≫ f) n, ⊤) from
        (exteriorCotangentSheafMorphism f g n).val.app (op ⊤) w) := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : Algebra Γ(X, ⊤) Γ(Z, ⊤) := (g.appTop.hom).toAlgebra
  rw [show s ⊗ₜ[Γ(X, ⊤)] w = s • ((1 : Γ(Z, ⊤)) ⊗ₜ[Γ(X, ⊤)] w) from
    TensorProduct.tmul_eq_smul_one_tmul s w, map_smul, sectionsIso_one_tmul]

end Affine
section Mixed
open NadelMixedKummer NadelCanonicalMixed
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A)
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (u : Fin q → Aˣ)
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The SAME entire original mixed root algebra, retaining all factors. -/
abbrev mixedRing := NadelMixedKummer.Ring N (mixedCoefficient x I σ u)

/-- The actual native tensor algebra on the original whole unit-root cover. -/
abbrev extendedMixedRing := UnitCover N u ⊗[A] mixedRing x N I σ u

/-- The actual original mixed structural morphism over the original field. -/
abbrev mixedStructure : Spec (.of (mixedRing x N I σ u)) ⟶ Spec (.of k) :=
  NadelMixedKummer.Dimension.SmoothSourceDimension.structureMap (k := k) N
    (mixedCoefficient x I σ u)

/-- The SAME original tensor right inclusion, as the actual spectrum map. -/
def mixedUnitProjection : Spec (.of (extendedMixedRing x N I σ u)) ⟶
    Spec (.of (mixedRing x N I σ u)) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := UnitCover N u)
      (B := mixedRing x N I σ u)).toRingHom)

/-- Original etale coordinates derive actual smoothness of the ENTIRE mixed
source; no original source smoothness or differential-frame certificate is input. -/
theorem mixedStructure_smooth
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    SmoothOfRelativeDimension n (mixedStructure (k := k) x N I σ u) :=
  NadelMixedKummer.Dimension.SmoothSourceDimension.smoothOfRelativeDimension
    x hx N (mixedCoefficient x I σ u) I σ u (fun _ => rfl) hN htame

/-- The SAME full unit extension is actually etale on the mixed source, from
original positive tame degrees and the actual unit-cover producer. -/
theorem mixedUnitProjection_etale
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    Etale (mixedUnitProjection x N I σ u) := by
  let S := UnitCover N u
  let B := mixedRing x N I σ u
  let : Algebra.Etale A S := unitCover_etale N u hN htame
  let : Algebra.Etale B (B ⊗[A] S) := inferInstance
  let : Algebra.Etale B (S ⊗[A] B) :=
    Algebra.Etale.of_equiv (R := B) (A := B ⊗[A] S) (B := S ⊗[A] B)
      (Algebra.TensorProduct.commRight A B S)
  rw [mixedUnitProjection, HasRingHomProperty.Spec_iff (P := @Etale)]
  change (algebraMap B (S ⊗[A] B)).Etale
  rw [RingHom.etale_algebraMap]
  infer_instance

/-- Original mixed-coordinate data constructs actual whole canonical-section
base change for B→UnitCover⊗B, without a global cotangent basis on B. -/
def mixedSectionsIso
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    letI := mixedStructure_smooth x N I σ u hx hN htame
    letI := mixedUnitProjection_etale x N I σ u hN htame
    letI : (exteriorCotangentSheaf (mixedStructure (k := k) x N I σ u) n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible (mixedStructure (k := k) x N I σ u) n).isQuasicoherent
    (ModuleCat.extendScalars (mixedUnitProjection x N I σ u).appTop.hom).obj
      ((exteriorCotangentSheaf (mixedStructure (k := k) x N I σ u) n).val.obj (op ⊤)) ≅
      (exteriorCotangentSheaf
        (mixedUnitProjection x N I σ u ≫ mixedStructure (k := k) x N I σ u) n).val.obj (op ⊤) := by
  letI := mixedStructure_smooth x N I σ u hx hN htame
  letI := mixedUnitProjection_etale x N I σ u hN htame
  letI : (exteriorCotangentSheaf (mixedStructure (k := k) x N I σ u) n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible (mixedStructure (k := k) x N I σ u) n).isQuasicoherent
  exact sectionsIso (mixedStructure (k := k) x N I σ u) (mixedUnitProjection x N I σ u) n

end Mixed

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
