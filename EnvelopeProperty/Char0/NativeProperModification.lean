import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeProperProduct
import EnvelopeProperty.Projective.NativeBaseChange
import EnvelopeProperty.AlgGeom.ProjectiveBlowupSequence
import EnvelopeProperty.Alterations.Geometry.ProjectiveIdentity

/-!
# Actual analytic properness of the original projective morphism

The actual polynomial coefficient-base-change isomorphism and the native
analytic product homeomorphism reduce the original relative projective
projection to projection with a compact projective factor. The actual original
closed immersion then proves properness of every original projective
factorization and, in particular, the SAME finite blowup succession.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeProperModification

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexSchemes HolomorphicGerms
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem closedImmersionPointMap_isProper {X Y : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (g : Y ⟶ Spec (.of ℂ))
    (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ g = f) :
    @IsProperMap (SchemeComplexPoint f) (SchemeComplexPoint g)
      (schemeAnalyticPointTopology f) (schemeAnalyticPointTopology g)
      (schemeComplexPointMap f g i hi) := by
  subst f
  let := schemeAnalyticPointTopology (i ≫ g)
  let := schemeAnalyticPointTopology g
  exact (closedImmersionComplexPointMap_isClosedEmbedding g i).isProperMap

variable {R : Type} [CommRing R]

/-- The original projective coefficient projection is analytically proper over every complex ring map. -/
theorem projectiveProjection_isProper (φ : ℂ →+* R) (n : ℕ) :
    let q := ProjBerk.nativeStructureMap (R := R) (n := n)
    let b := Spec.map (CommRingCat.ofHom φ)
    @IsProperMap (SchemeComplexPoint (q ≫ b)) (SchemeComplexPoint b)
      (schemeAnalyticPointTopology (q ≫ b)) (schemeAnalyticPointTopology b)
      (schemeComplexPointMap (q ≫ b) b q rfl) := by
  let q := ProjBerk.nativeStructureMap (R := ℂ) (n := n)
  let qR := ProjBerk.nativeStructureMap (R := R) (n := n)
  let b := Spec.map (CommRingCat.ofHom φ)
  let E := ProjBerk.nativeCoefficientBaseChangeIso (n := n) φ
  let t := pullback.fst q b ≫ q
  let := schemeAnalyticPointTopology q
  let := schemeAnalyticPointTopology b
  let := schemeAnalyticPointTopology t
  let := schemeAnalyticPointTopology (qR ≫ b)
  let : CompactSpace (SchemeComplexPoint q) := by
    change @CompactSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ n))
      (schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n))
    exact polynomialProjComplexPoint_compactSpace n
  have hp : @IsProperMap (SchemeComplexPoint t) (SchemeComplexPoint b)
      (schemeAnalyticPointTopology t) (schemeAnalyticPointTopology b)
      (schemeComplexPointMap t b (pullback.snd q b) pullback.condition.symm) := by
    exact isProperMap_snd_of_compactSpace.comp (schemeNativeProductHomeomorph q b).isProperMap
  have hE : E.hom ≫ t = qR ≫ b := by
    dsimp only [t]
    rw [pullback.condition, ← Category.assoc,
      ProjBerk.nativeCoefficientBaseChangeIso_hom_snd]
  have hc := hp.comp (closedImmersionPointMap_isProper (qR ≫ b) t E.hom hE)
  convert hc using 1
  funext p
  apply Subtype.ext
  change p.val ≫ qR = (p.val ≫ E.hom) ≫ pullback.snd q b
  rw [Category.assoc, ProjBerk.nativeCoefficientBaseChangeIso_hom_snd]

/-- The same projection is proper for the literal original complex structural morphism. -/
theorem projectiveProjection_isProper_of_structure
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) :
    let q := ProjBerk.nativeStructureMap (R := R) (n := n)
    @IsProperMap (SchemeComplexPoint (q ≫ f)) (SchemeComplexPoint f)
      (schemeAnalyticPointTopology (q ≫ f)) (schemeAnalyticPointTopology f)
      (schemeComplexPointMap (q ≫ f) f q rfl) := by
  have hf : Spec.map (CommRingCat.ofHom (Spec.preimage f).hom) = f := Spec.map_preimage f
  let P := fun b : Spec (.of R) ⟶ Spec (.of ℂ) =>
    let q := ProjBerk.nativeStructureMap (R := R) (n := n)
    @IsProperMap (SchemeComplexPoint (q ≫ b)) (SchemeComplexPoint b)
      (schemeAnalyticPointTopology (q ≫ b)) (schemeAnalyticPointTopology b)
      (schemeComplexPointMap (q ≫ b) b q rfl)
  exact Eq.mp (congrArg P hf) (projectiveProjection_isProper (Spec.preimage f).hom n)

/-- An actual original finite projective factorization derives actual analytic properness. -/
theorem projectiveMorphism_isProper {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R))
    (hπ : IsProjectiveFactorization π) :
    @IsProperMap (SchemeComplexPoint (π ≫ f)) (SchemeComplexPoint f)
      (schemeAnalyticPointTopology (π ≫ f)) (schemeAnalyticPointTopology f)
      (schemeComplexPointMap (π ≫ f) f π rfl) := by
  obtain ⟨n, i, hi, hif⟩ := hπ
  let q := ProjBerk.nativeStructureMap (R := R) (n := n)
  have hiq : i ≫ q = π := hif
  let : IsClosedImmersion i := hi
  let := schemeAnalyticPointTopology (q ≫ f)
  let := schemeAnalyticPointTopology f
  let := schemeAnalyticPointTopology (π ≫ f)
  have hio : i ≫ (q ≫ f) = π ≫ f := by rw [← Category.assoc, hiq]
  have hc := (projectiveProjection_isProper_of_structure f n).comp
    (closedImmersionPointMap_isProper (π ≫ f) (q ≫ f) i hio)
  convert hc using 1
  funext p
  apply Subtype.ext
  change p.val ≫ π = (p.val ≫ i) ≫ q
  rw [Category.assoc, hiq]

/-- Properness is derived for the SAME actual original finite blowup succession. -/
theorem blowupSequence_isProper [IsNoetherianRing R]
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (S : (Spec (.of R)).BlowUpSequence) :
    @IsProperMap (SchemeComplexPoint (S.composite ≫ f)) (SchemeComplexPoint f)
      (schemeAnalyticPointTopology (S.composite ≫ f)) (schemeAnalyticPointTopology f)
      (schemeComplexPointMap (S.composite ≫ f) f S.composite rfl) := by
  have hid : IsProjectiveFactorization (𝟙 (Spec (.of R))) :=
    (ProjectiveBlowupSequence.isProjectiveOver_iff _).mp
      (Alterations.Geometry.ProjectiveIdentity.isProjectiveOver_id_spec R)
  have hS := ProjectiveBlowupSequence.composite_isProjectiveFactorization S (𝟙 _) hid
  apply projectiveMorphism_isProper f S.composite
  simpa only [Category.comp_id] using hS

end EnvelopeProperty.Char0.NativeProperModification
