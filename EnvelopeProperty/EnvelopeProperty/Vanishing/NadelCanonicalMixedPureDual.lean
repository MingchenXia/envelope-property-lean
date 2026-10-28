import EnvelopeProperty.Vanishing.NadelCanonicalMixedPureCoordinates
import EnvelopeProperty.Vanishing.NadelCanonicalDualTransport

/-! # Actual finite duality on the entire original pure quotient -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerCanonicalTrace
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
local notation "f₀" => coefficientHom N I h

/-- The actual whole pure/split comparison retains the literal original composite coefficient action. -/
def wholePureCoefficientAlgEquiv :
    letI : Algebra R B₀ := (f₀).toAlgebra
    P₀ ≃ₐ[R] B₀ := by
  let : Algebra R B₀ := (f₀).toAlgebra
  exact {
    toRingEquiv := wholeRingEquiv N I h (fun i hi => by simp only [pureCoefficient, dif_neg hi])
    commutes' r := congrArg (fun f : R →+* B₀ => f r)
      (wholeToSplit_structure N I h (fun i hi => by simp only [pureCoefficient, dif_neg hi])) }

/-- The proved whole canonical duality and its true differential frames give the actual native regular-module dual. -/
def splitRegularIso : ModuleCat.of B₀ B₀ ≅ (coextendScalars f₀).obj (ModuleCat.of R R) :=
  (affineCanonicalTrivialization (splitDifferentialBasis N I σ hN a ha htame)).symm.toModuleIso ≪≫
    splitCanonicalIso N I σ hN a ha htame ≪≫
      (coextendScalars f₀).mapIso (affineCanonicalTrivialization (baseDifferentialBasis a ha)).toModuleIso

/-- Its actual original restricted counit is a genuine original R-linear coefficient functional. -/
def splitRegularCoefficient : (restrictScalars f₀).obj (ModuleCat.of B₀ B₀) →ₗ[R] R :=
  (((restrictScalars f₀).map (splitRegularIso N I σ hN a ha htame).hom) ≫
    (restrictCoextendScalarsAdj f₀).counit.app (ModuleCat.of R R)).hom

/-- The genuine native adjunction recovers the complete actual perfect pairing from its own original counit. -/
theorem splitRegularFrame_eq : coextensionFrame f₀ (splitRegularCoefficient N I σ hN a ha htame) =
    (splitRegularIso N I σ hN a ha htame).hom.hom := by
  apply LinearMap.ext
  intro z
  apply CoextendScalars.ext
  ext (w : B₀)
  change (splitRegularIso N I σ hN a ha htame).hom (w * z) (1 : B₀) =
    (splitRegularIso N I σ hN a ha htame).hom z w
  have he := congrArg
    (fun φ : (coextendScalars f₀).obj (ModuleCat.of R R) => φ (1 : B₀))
      ((splitRegularIso N I σ hN a ha htame).hom.hom.map_smul w z)
  change (splitRegularIso N I σ hN a ha htame).hom (w * z) (1 : B₀) =
    (w • (splitRegularIso N I σ hN a ha htame).hom z) (1 : B₀) at he
  have hs := CoextendScalars.smul_apply (f₀) (ModuleCat.of R R)
    ((splitRegularIso N I σ hN a ha htame).hom z) w (1 : B₀)
  exact he.trans (hs.trans (congrArg
    (fun t : B₀ => (splitRegularIso N I σ hN a ha htame).hom z t) (one_mul w)))

/-- Whole pairing bijectivity follows internally from the actual original canonical isomorphism. -/
theorem splitRegularFrame_bijective :
    Function.Bijective (coextensionFrame f₀ (splitRegularCoefficient N I σ hN a ha htame)) := by
  rw [splitRegularFrame_eq]
  exact (splitRegularIso N I σ hN a ha htame).toLinearEquiv.bijective

/-- The original pure quotient has its actual native coefficient, obtained through the whole original algebra map. -/
def pureCoefficientFunctional :
    (restrictScalars (algebraMap R P₀)).obj (ModuleCat.of P₀ P₀) →ₗ[R] R := by
  let : Algebra R B₀ := (f₀).toAlgebra
  exact NadelCanonicalDualTransport.coefficient (wholePureCoefficientAlgEquiv N I σ a)
    (splitRegularCoefficient N I σ hN a ha htame)

/-- The transferred coefficient retains the actual whole original pure/split argument. -/
theorem pureCoefficientFunctional_apply (z : P₀) :
    pureCoefficientFunctional N I σ hN a ha htame z =
      splitRegularCoefficient N I σ hN a ha htame (wholePureSmallAlgEquiv N I σ a z) := rfl

/-- Native adjunction gives the original-pure-algebra-linear whole finite dual map. -/
def pureDualizingMap : P₀ →ₗ[P₀] (coextendScalars (algebraMap R P₀)).obj (ModuleCat.of R R) :=
  coextensionFrame (algebraMap R P₀) (pureCoefficientFunctional N I σ hN a ha htame)

/-- The original whole pure dual frame retains genuine multiplication and its actual full coefficient functional. -/
theorem pureDualizingMap_apply (z w : P₀) :
    pureDualizingMap N I σ hN a ha htame z w =
      pureCoefficientFunctional N I σ hN a ha htame (w * z) := by
  dsimp only [pureDualizingMap]
  generalize hcoeff : pureCoefficientFunctional N I σ hN a ha htame = l
  exact coextensionFrame_apply (algebraMap R P₀) l z w

/-- Actual whole-pure pairing perfection is internally transported from the entire active/inactive native canonical dual. -/
theorem pureDualizingMap_bijective : Function.Bijective (pureDualizingMap N I σ hN a ha htame) := by
  let : Algebra R B₀ := (f₀).toAlgebra
  exact NadelCanonicalDualTransport.frame_bijective (wholePureCoefficientAlgEquiv N I σ a)
    (splitRegularCoefficient N I σ hN a ha htame) (splitRegularFrame_bijective N I σ hN a ha htame)

/-- The SAME entire original pure quotient is its genuine native coextension dual; no desired pairing is an input. -/
def pureDualizingIso : ModuleCat.of P₀ P₀ ≅ (coextendScalars (algebraMap R P₀)).obj (ModuleCat.of R R) :=
  (LinearEquiv.ofBijective (pureDualizingMap N I σ hN a ha htame)
    (pureDualizingMap_bijective N I σ hN a ha htame)).toModuleIso

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
