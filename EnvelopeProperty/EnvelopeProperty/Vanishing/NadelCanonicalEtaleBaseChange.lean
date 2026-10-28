import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeDifferentials

/-! # Genuine exterior Kähler base change on the actual formally étale algebra

The equivalence is native differential base change followed by actual
exterior base change.  No desired Omega or canonical comparison is an input.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelCanonicalBaseChange

open CategoryTheory CanonicalGeometry NadelKummerCanonicalBaseChange
open scoped TensorProduct

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The genuine original exterior Kähler pullback, independent of any differential frame. -/
def topPullback (n : ℕ) :
    affineCanonicalModule R A n →ₛₗ[algebraMap A B] affineCanonicalModule R B n :=
  exteriorSemilinearMap (algebraMap A B) (kaehlerSemilinear (K := R) (A := A) (B := B)) n

/-- Actual formally étale Kähler base change on the whole original top exterior modules. -/
def etaleTopEquiv [Algebra.FormallyEtale A B] {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A)) :
    B ⊗[A] affineCanonicalModule R A n ≃ₗ[B] affineCanonicalModule R B n :=
  exteriorBasisBaseChangeEquiv b n ≪≫ₗ
    exteriorLinearEquiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B) n

/-- The actual étale top comparison sends every original differential wedge to its true native images. -/
theorem etaleTopEquiv_wedge [Algebra.FormallyEtale A B] {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (w : Fin n → KaehlerDifferential R A) :
    etaleTopEquiv b (1 ⊗ₜ[A] exteriorPower.ιMulti A n w) =
      exteriorPower.ιMulti B n (fun j => KaehlerDifferential.map R R A B (w j)) := by
  rw [etaleTopEquiv, LinearEquiv.trans_apply, exteriorBasisBaseChangeEquiv_wedge,
    exteriorLinearEquiv_ιMulti]
  congr 1
  funext j
  exact (KaehlerDifferential.mapBaseChange_tmul R A B 1 (w j)).trans (one_smul _ _)

/-- Genuine differential pullback preserves every original ordered wedge. -/
theorem topPullback_wedge (n : ℕ) (w : Fin n → KaehlerDifferential R A) :
    topPullback (R := R) (A := A) (B := B) n (exteriorPower.ιMulti A n w) =
      exteriorPower.ιMulti B n (fun j => KaehlerDifferential.map R R A B (w j)) := by
  rw [topPullback, exteriorSemilinearMap_ιMulti]
  rfl

/-- The actual transported native differential basis has the genuine pulled top frame. -/
theorem topPullback_generator [Algebra.FormallyEtale A B] {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A)) :
    topPullback (R := R) (A := A) (B := B) n (affineCanonicalGenerator b) =
      affineCanonicalGenerator (affineDifferentialBasisOfFormallyEtale (B := B) b) := by
  rw [affineCanonicalGenerator_eq_wedge, topPullback_wedge, affineCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  exact (affineDifferentialBasisOfFormallyEtale_apply b j).symm

/-- The actual whole tensor comparison carries the original top frame to the genuine transported one. -/
theorem etaleTopEquiv_generator [Algebra.FormallyEtale A B] {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A)) :
    etaleTopEquiv b (1 ⊗ₜ[A] affineCanonicalGenerator b) =
      affineCanonicalGenerator (affineDifferentialBasisOfFormallyEtale (B := B) b) := by
  rw [affineCanonicalGenerator_eq_wedge, etaleTopEquiv_wedge, affineCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  exact (affineDifferentialBasisOfFormallyEtale_apply b j).symm

end EnvelopeProperty.Vanishing.NadelCanonicalBaseChange
