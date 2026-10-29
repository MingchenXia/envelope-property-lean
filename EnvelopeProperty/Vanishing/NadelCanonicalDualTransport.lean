import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeCore

/-! # Actual original coefficient-preserving transport of native multiplication dual frames -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalDualTransport

open CategoryTheory ModuleCat NadelKummerCanonicalTrace
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C)

/-- The genuine whole algebra equivalence preserves both original restricted coefficient actions. -/
def restrictionEquiv :
    (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A]
      (restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) where
  toFun x := e x
  invFun x := e.symm x
  left_inv x := e.left_inv x
  right_inv x := e.right_inv x
  map_add' x y := e.map_add x y
  map_smul' a x := by
    change e (algebraMap A B a * (show B from x)) = algebraMap A C a * e x
    rw [map_mul, e.commutes]

/-- Native functional transport is original precomposition through the true entire inverse algebra map. -/
def functionalEquiv :
    (coextendScalars (algebraMap A B)).obj (ModuleCat.of A A) ≃
      (coextendScalars (algebraMap A C)).obj (ModuleCat.of A A) :=
  (CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A A)).toEquiv |>.trans
    (((restrictionEquiv e).arrowCongr (LinearEquiv.refl A A)).toEquiv.trans
      (CoextendScalars.equiv (algebraMap A C) (ModuleCat.of A A)).symm.toEquiv)

/-- Every actual functional value retains its true original inverse-map argument. -/
theorem functionalEquiv_apply
    (φ : (coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)) (c : C) :
    functionalEquiv e φ c = φ (e.symm c) := rfl

/-- Actual precomposition transfers the native original coefficient functional. -/
def coefficient (l : (restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) →ₗ[A] A) :
    (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) →ₗ[A] A :=
  l.comp (restrictionEquiv e).toLinearMap

/-- The transported original multiplication frame is an actual B-linear native dual map. -/
def frame (l : (restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) →ₗ[A] A) :
    B →ₗ[B] (coextendScalars (algebraMap A B)).obj (ModuleCat.of A A) :=
  coextensionFrame (algebraMap A B) (coefficient e l)

/-- Whole native functional compatibility is proved from actual multiplication and inverse identities. -/
theorem functionalEquiv_frame
    (l : (restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) →ₗ[A] A) (x : B) :
    functionalEquiv e (frame e l x) = coextensionFrame (algebraMap A C) l (e x) := by
  apply CoextendScalars.ext
  ext (y : C)
  rw [functionalEquiv_apply, frame, coextensionFrame_apply, coextensionFrame_apply]
  change l (e (e.symm y * x)) = l (y * e x)
  rw [map_mul, e.apply_symm_apply]

/-- Bijectivity of the actual whole original pairing is preserved under the genuine coefficient-preserving algebra equivalence. -/
theorem frame_bijective
    (l : (restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) →ₗ[A] A)
    (hl : Function.Bijective (coextensionFrame (algebraMap A C) l)) :
    Function.Bijective (frame e l) := by
  let E := e.toEquiv.trans
    ((LinearEquiv.ofBijective (coextensionFrame (algebraMap A C) l) hl).toEquiv.trans
      (functionalEquiv e).symm)
  have hE : (frame e l : B → (coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)) = E := by
    funext x
    apply (functionalEquiv e).injective
    rw [functionalEquiv_frame]
    exact ((functionalEquiv e).apply_symm_apply _).symm
  rw [hE]
  exact E.bijective

/-- The genuine whole transported pairing gives an actual original-B-linear module isomorphism. -/
def frameIso
    (l : (restrictScalars (algebraMap A C)).obj (ModuleCat.of C C) →ₗ[A] A)
    (hl : Function.Bijective (coextensionFrame (algebraMap A C) l)) :
    ModuleCat.of B B ≅ (coextendScalars (algebraMap A B)).obj (ModuleCat.of A A) :=
  (LinearEquiv.ofBijective (frame e l) (frame_bijective e l hl)).toModuleIso

end EnvelopeProperty.Vanishing.NadelCanonicalDualTransport
