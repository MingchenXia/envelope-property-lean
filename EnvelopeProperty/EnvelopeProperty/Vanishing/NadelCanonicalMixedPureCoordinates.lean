import EnvelopeProperty.Vanishing.NadelCanonicalMixedPureTowerTrace
import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniquenessCoordinate

/-! # Genuine etale coordinates on the entire original pure quotient -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerTraceBaseChangeUniqueness
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] [Nontrivial R]
    {n q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
    (htame : ∀ i, IsUnit (N i : R))
attribute [local instance] Classical.propDecidable
local notation "x" => originalCoordinates a
local notation "h" => pureCoefficient x I σ
local notation "A₀" => ActiveRing N I h
local notation "B₀" => SplitRing N I h
local notation "P₀" => NadelMixedKummer.Ring N h

/-- The genuine whole pure/split algebra comparison over the SAME original small coefficient ring. -/
def wholePureSmallAlgEquiv : P₀ ≃ₐ[k] B₀ :=
  (wholeAlgEquiv N I h (fun i hi => by simp only [pureCoefficient, dif_neg hi])).restrictScalars k

/-- The entire inactive unit layer retains the SAME actual active coordinate evaluations. -/
def splitCoordinateEvaluation : MvPolynomial (Fin n) k →ₐ[k] B₀ :=
  (IsScalarTower.toAlgHom k A₀ B₀).comp (coordinateEvaluation N I σ a)

/-- The WHOLE original pure quotient has its internally constructed actual polynomial coordinate morphism. -/
def pureCoordinateEvaluation : MvPolynomial (Fin n) k →ₐ[k] P₀ :=
  (wholePureSmallAlgEquiv N I σ a).symm.toAlgHom.comp (splitCoordinateEvaluation N I σ a)

private theorem pureCoordinate_formallyEtale_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) : f.FormallyEtale := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.Etale A B := RingHom.Etale.of_bijective hf
  change Algebra.FormallyEtale A B
  infer_instance

omit [Nontrivial k] [Nontrivial R] in
include hN ha htame in
/-- The SAME actual split-coordinate morphism is formally etale on the complete inactive root layer. -/
theorem splitCoordinateEvaluation_formallyEtale : (splitCoordinateEvaluation N I σ a).toRingHom.FormallyEtale := by
  let : Algebra.Etale A₀ B₀ := unitCover_etale (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
    (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
  have he : (algebraMap A₀ B₀).FormallyEtale := RingHom.formallyEtale_algebraMap.mpr inferInstance
  exact (coordinateEvaluation_formallyEtale N I σ hN a ha).comp he

omit [Nontrivial k] [Nontrivial R] in
include hN ha htame in
/-- Original true geometric data give a genuinely formally-etale polynomial chart on the WHOLE original pure quotient. -/
theorem pureCoordinateEvaluation_formallyEtale : (pureCoordinateEvaluation N I σ a).toRingHom.FormallyEtale := by
  have he := pureCoordinate_formallyEtale_of_bijective _ (wholePureSmallAlgEquiv N I σ a).symm.bijective
  exact (splitCoordinateEvaluation_formallyEtale N I σ hN a ha htame).comp he

/-- The actual original pure quotient receives its genuine native differential frame internally, without an Omega-model premise. -/
def pureDifferentialBasis : Module.Basis (Fin n) P₀ (KaehlerDifferential k P₀) :=
  NadelCanonicalUnitRoot.chartDifferentialBasis k P₀ (pureCoordinateEvaluation N I σ a)
    (pureCoordinateEvaluation_formallyEtale N I σ hN a ha htame)

omit [Nontrivial k] [Nontrivial R] in
/-- The real entire pure/split comparison retains the actual original coordinate maps on every polynomial. -/
theorem wholePure_coordinateEvaluation (p : MvPolynomial (Fin n) k) :
    wholePureSmallAlgEquiv N I σ a (pureCoordinateEvaluation N I σ a p) =
      splitCoordinateEvaluation N I σ a p :=
  (wholePureSmallAlgEquiv N I σ a).apply_symm_apply _

omit [Nontrivial k] [Nontrivial R] in
/-- Every actual split-frame vector is the differential of the same genuine whole coordinate polynomial. -/
theorem splitDifferentialBasis_apply (j : Fin n) :
    splitDifferentialBasis N I σ hN a ha htame j =
      KaehlerDifferential.D k B₀ (splitCoordinateEvaluation N I σ a (MvPolynomial.X j)) := by
  let : Algebra.Etale A₀ B₀ := unitCover_etale (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
    (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
  change affineDifferentialBasisOfFormallyEtale (B := B₀) (activeDifferentialBasis N I σ hN a ha) j = _
  rw [affineDifferentialBasisOfFormallyEtale_apply, activeDifferentialBasis_apply,
    KaehlerDifferential.map_D]
  congr 1
  simp only [splitCoordinateEvaluation, AlgHom.comp_apply, coordinateEvaluation, MvPolynomial.aeval_X,
    IsScalarTower.toAlgHom_apply]

omit [Nontrivial k] [Nontrivial R] in
/-- Every original pure-frame vector is the native differential of its internally produced actual coordinate. -/
theorem pureDifferentialBasis_apply (j : Fin n) :
    pureDifferentialBasis N I σ hN a ha htame j =
      KaehlerDifferential.D k P₀ (pureCoordinateEvaluation N I σ a (MvPolynomial.X j)) :=
  NadelCanonicalUnitRoot.chartDifferentialBasis_apply k P₀ (pureCoordinateEvaluation N I σ a)
    (pureCoordinateEvaluation_formallyEtale N I σ hN a ha htame) j

/-- The genuine whole-algebra exterior differential map, with its actual original coefficient action. -/
def pureToSplitExterior : affineCanonicalModule k P₀ n →ₛₗ[(wholePureSmallAlgEquiv N I σ a).toRingEquiv.toRingHom]
    affineCanonicalModule k B₀ n := algebraExteriorMap (wholePureSmallAlgEquiv N I σ a).toAlgHom n

omit [Nontrivial k] [Nontrivial R] in
/-- The actual whole differential map carries the genuine original pure generator to the genuine whole split generator. -/
theorem pureToSplitExterior_generator :
    pureToSplitExterior N I σ a (affineCanonicalGenerator (pureDifferentialBasis N I σ hN a ha htame)) =
      affineCanonicalGenerator (splitDifferentialBasis N I σ hN a ha htame) := by
  have hp : affineCanonicalGenerator (pureDifferentialBasis N I σ hN a ha htame) =
      exteriorPower.ιMulti P₀ n
        (fun j => KaehlerDifferential.D k P₀ (pureCoordinateEvaluation N I σ a (MvPolynomial.X j))) := by
    rw [affineCanonicalGenerator_eq_wedge]
    congr 1
    exact funext (pureDifferentialBasis_apply N I σ hN a ha htame)
  have hs : exteriorPower.ιMulti B₀ n
      (fun j => KaehlerDifferential.D k B₀
        (wholePureSmallAlgEquiv N I σ a (pureCoordinateEvaluation N I σ a (MvPolynomial.X j)))) =
        affineCanonicalGenerator (splitDifferentialBasis N I σ hN a ha htame) := by
    rw [affineCanonicalGenerator_eq_wedge]
    congr 1
    funext j
    exact (congrArg (KaehlerDifferential.D k B₀) (wholePure_coordinateEvaluation N I σ a (MvPolynomial.X j))).trans
      (splitDifferentialBasis_apply N I σ hN a ha htame j).symm
  calc
    _ = pureToSplitExterior N I σ a
        (exteriorPower.ιMulti P₀ n
          (fun j => KaehlerDifferential.D k P₀ (pureCoordinateEvaluation N I σ a (MvPolynomial.X j)))) :=
      congrArg (pureToSplitExterior N I σ a) hp
    _ = exteriorPower.ιMulti B₀ n
        (fun j => KaehlerDifferential.D k B₀
          (wholePureSmallAlgEquiv N I σ a (pureCoordinateEvaluation N I σ a (MvPolynomial.X j)))) :=
      algebraExteriorMap_differential_wedge (wholePureSmallAlgEquiv N I σ a).toAlgHom n _
    _ = _ := hs

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
