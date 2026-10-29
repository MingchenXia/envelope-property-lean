/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumQuotient

/-!
# Change of prescribed base seminorm and tensor scalar extension

Compatible real-valued seminorms on arbitrary commutative coefficient rings give
actual restriction maps. Scalar extension uses the genuine tensor algebra and
its right inclusion, preserving evaluations of every original algebra element
and every polynomial. Algebra maps and compatible scalar maps induce continuous,
functorial tensor pullbacks. No extension existence or surjectivity is assumed.
-/

open scoped NNReal Topology TensorProduct

noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

section RestrictScalars

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}

/-- Restrict prescribed coefficients through a compatible scalar tower, retaining the whole point. -/
def restrictScalars (hwv : ∀ r, w (algebraMap R S r) = v r)
    (x : RelativeSpectrum w A) : RelativeSpectrum v A :=
  ⟨x.1, fun r => by rw [IsScalarTower.algebraMap_apply R S A, x.2, hwv]⟩

@[simp]
theorem restrictScalars_val_apply (hwv : ∀ r, w (algebraMap R S r) = v r)
    (x : RelativeSpectrum w A) (a : A) : (restrictScalars hwv x).1.val a = x.1.val a := rfl

@[fun_prop]
theorem continuous_restrictScalars (hwv : ∀ r, w (algebraMap R S r) = v r) :
    Continuous (restrictScalars (A := A) hwv) :=
  continuous_subtype_val.subtype_mk _

variable {B : Type*} [CommRing B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]

/-- Coefficient restriction commutes with full algebra-map pullback. -/
theorem restrictScalars_comap (hwv : ∀ r, w (algebraMap R S r) = v r)
    (φ : A →ₐ[S] B) (y : RelativeSpectrum w B) :
    restrictScalars hwv (comap φ y) = comap (φ.restrictScalars R) (restrictScalars hwv y) := rfl

end RestrictScalars

section BaseChange

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]
  {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}

/-- Restriction from the genuine scalar extension along `a ↦ 1 ⊗ a`. -/
def baseChangeRestriction (hwv : ∀ r, w (algebraMap R S r) = v r)
    (x : RelativeSpectrum w (S ⊗[R] A)) : RelativeSpectrum v A :=
  comap Algebra.TensorProduct.includeRight (restrictScalars hwv x)

/-- Every original algebra element has its tensor-inclusion value. -/
@[simp]
theorem baseChangeRestriction_val_apply (hwv : ∀ r, w (algebraMap R S r) = v r)
    (x : RelativeSpectrum w (S ⊗[R] A)) (a : A) :
    (baseChangeRestriction hwv x).1.val a = x.1.val (1 ⊗ₜ[R] a) := rfl

@[fun_prop]
theorem continuous_baseChangeRestriction (hwv : ∀ r, w (algebraMap R S r) = v r) :
    Continuous (baseChangeRestriction (A := A) hwv) :=
  (continuous_comap (v := v)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)).comp
      (continuous_restrictScalars (A := S ⊗[R] A) hwv)

/-- The prescribed coefficient values determine the first factor of every pure tensor. -/
theorem baseChange_val_tmul (hwv : ∀ r, w (algebraMap R S r) = v r)
    (x : RelativeSpectrum w (S ⊗[R] A)) (s : S) (a : A) :
    x.1.val (s ⊗ₜ[R] a) = w s * (baseChangeRestriction hwv x).1.val a := by
  have ht : s ⊗ₜ[R] a =
      algebraMap S (S ⊗[R] A) s * (1 ⊗ₜ[R] a) := by
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [ht, map_mul, x.2]
  rfl

/-- The full multivariate polynomial evaluation commutes with tensor scalar extension. -/
theorem baseChangeRestriction_val_aeval (hwv : ∀ r, w (algebraMap R S r) = v r)
    (x : RelativeSpectrum w (S ⊗[R] A)) {ι : Type*} (z : ι → A) (p : MvPolynomial ι R) :
    (baseChangeRestriction hwv x).1.val (MvPolynomial.aeval z p) =
      x.1.val (MvPolynomial.aeval (fun i => (1 : S) ⊗ₜ[R] z i) p) := by
  change x.1.val (Algebra.TensorProduct.includeRight (MvPolynomial.aeval z p)) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The actual tensor extension of an algebra homomorphism, preserving all new coefficients. -/
def baseChangeMap (φ : A →ₐ[R] B) : S ⊗[R] A →ₐ[S] S ⊗[R] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) φ

@[simp]
theorem baseChangeMap_tmul (φ : A →ₐ[R] B) (s : S) (a : A) :
    baseChangeMap (S := S) φ (s ⊗ₜ[R] a) = s ⊗ₜ[R] φ a := rfl

/-- Tensor pullback and restriction commute as equality of whole relative spectrum points. -/
theorem baseChangeRestriction_comap (hwv : ∀ r, w (algebraMap R S r) = v r)
    (φ : A →ₐ[R] B) (y : RelativeSpectrum w (S ⊗[R] B)) :
    baseChangeRestriction hwv (comap (baseChangeMap φ) y) =
      comap φ (baseChangeRestriction hwv y) := by
  apply Subtype.ext
  exact Spectrum.ext_val fun a => rfl

/-- Tensor extension respects identity algebra maps. -/
@[simp]
theorem baseChangeMap_id : baseChangeMap (R := R) (S := S) (AlgHom.id R A) = AlgHom.id S _ :=
  Algebra.TensorProduct.map_id

variable {C : Type*} [CommRing C] [Algebra R C]

/-- Tensor extension respects the composition of algebra maps. -/
theorem baseChangeMap_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    baseChangeMap (S := S) (ψ.comp φ) = (baseChangeMap ψ).comp (baseChangeMap φ) :=
  Algebra.TensorProduct.map_id_comp ψ φ

end BaseChange

section ScalarMaps

variable {R S T A : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R T] [Algebra R A]
  {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0} {u : Valuation T ℝ≥0}

/-- Change the new scalar ring by a genuine compatible scalar algebra homomorphism. -/
def scalarChangeComap (τ : S →ₐ[R] T) (huw : ∀ s, u (τ s) = w s)
    (x : RelativeSpectrum u (T ⊗[R] A)) : RelativeSpectrum w (S ⊗[R] A) :=
  ⟨Spectrum.comap (Algebra.TensorProduct.map τ (AlgHom.id R A)).toRingHom x.1,
    fun s => by
      change x.1.val (Algebra.TensorProduct.map τ (AlgHom.id R A)
        (algebraMap S (S ⊗[R] A) s)) = w s
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change x.1.val (algebraMap T (T ⊗[R] A) (τ s)) = w s
      rw [x.2, huw]⟩

/-- Scalar-map pullback evaluates the actual full tensor homomorphism. -/
@[simp]
theorem scalarChangeComap_val_apply (τ : S →ₐ[R] T) (huw : ∀ s, u (τ s) = w s)
    (x : RelativeSpectrum u (T ⊗[R] A)) (q : S ⊗[R] A) :
    (scalarChangeComap τ huw x).1.val q =
      x.1.val (Algebra.TensorProduct.map τ (AlgHom.id R A) q) := rfl

@[fun_prop]
theorem continuous_scalarChangeComap (τ : S →ₐ[R] T) (huw : ∀ s, u (τ s) = w s) :
    Continuous (scalarChangeComap (A := A) τ huw) :=
  ((Spectrum.continuous_comap (Algebra.TensorProduct.map τ (AlgHom.id R A)).toRingHom).comp
    continuous_subtype_val).subtype_mk _

/-- Compatibility of the new scalar seminorms implies compatibility with the original base. -/
theorem scalarCompatibility_trans (hwv : ∀ r, w (algebraMap R S r) = v r)
    (τ : S →ₐ[R] T) (huw : ∀ s, u (τ s) = w s) :
    ∀ r, u (algebraMap R T r) = v r := fun r => by
  rw [← τ.commutes r, huw, hwv]

/-- Compatible scalar-map pullback commutes with restriction to every original algebra element. -/
theorem baseChangeRestriction_scalarChangeComap (hwv : ∀ r, w (algebraMap R S r) = v r)
    (τ : S →ₐ[R] T) (huw : ∀ s, u (τ s) = w s)
    (x : RelativeSpectrum u (T ⊗[R] A)) :
    baseChangeRestriction hwv (scalarChangeComap τ huw x) =
      baseChangeRestriction (scalarCompatibility_trans hwv τ huw) x := by
  apply Subtype.ext
  refine Spectrum.ext_val fun a => ?_
  simp only [baseChangeRestriction_val_apply, scalarChangeComap_val_apply,
    Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

/-- Pullback along the identity scalar homomorphism is the identity point map. -/
@[simp]
theorem scalarChangeComap_id (x : RelativeSpectrum w (S ⊗[R] A)) :
    scalarChangeComap (AlgHom.id R S) (fun _ => rfl) x = x := by
  apply Subtype.ext
  refine Spectrum.ext_val fun q => ?_
  change x.1.val (Algebra.TensorProduct.map (AlgHom.id R S) (AlgHom.id R A) q) = x.1.val q
  rw [Algebra.TensorProduct.map_id, AlgHom.id_apply]

variable {U : Type*} [CommRing U] [Algebra R U] {t : Valuation U ℝ≥0}

/-- Compatible scalar-map pullback reverses composition on every tensor, hence on whole points. -/
theorem scalarChangeComap_comp (τ : S →ₐ[R] T) (σ : T →ₐ[R] U)
    (huw : ∀ s, u (τ s) = w s) (htu : ∀ z, t (σ z) = u z)
    (x : RelativeSpectrum t (U ⊗[R] A)) :
    scalarChangeComap τ huw (scalarChangeComap σ htu x) =
      scalarChangeComap (σ.comp τ) (fun s => (htu (τ s)).trans (huw s)) x := by
  apply Subtype.ext
  refine Spectrum.ext_val fun q => ?_
  change x.1.val (Algebra.TensorProduct.map σ (AlgHom.id R A)
      (Algebra.TensorProduct.map τ (AlgHom.id R A) q)) =
    x.1.val (Algebra.TensorProduct.map (σ.comp τ) (AlgHom.id R A) q)
  have h := Algebra.TensorProduct.map_comp σ τ (AlgHom.id R A) (AlgHom.id R A)
  simp only [AlgHom.id_comp] at h
  exact congrArg (fun f : S ⊗[R] A →ₐ[R] U ⊗[R] A => x.1.val (f q)) h.symm

end ScalarMaps

section IteratedBaseChange

variable {R S T A : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R A]
  {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0} {u : Valuation T ℝ≥0}

/-- Compatible scalar seminorms compose through an actual scalar tower. -/
theorem scalarCompatibility_tower (hwv : ∀ r, w (algebraMap R S r) = v r)
    (huw : ∀ s, u (algebraMap S T s) = w s) : ∀ r, u (algebraMap R T r) = v r :=
  fun r => by rw [IsScalarTower.algebraMap_apply R S T, huw, hwv]

/-- The genuine tensor cancellation equivalence compares direct and iterated scalar extension. -/
def iteratedBaseChangeHomeomorph (u : Valuation T ℝ≥0) :
    RelativeSpectrum u (T ⊗[S] (S ⊗[R] A)) ≃ₜ RelativeSpectrum u (T ⊗[R] A) :=
  (algEquivHomeomorph u (Algebra.TensorProduct.cancelBaseChange R S T T A)).symm

/-- Direct pure-tensor values are evaluated on their actual iterated tensor representatives. -/
@[simp]
theorem iteratedBaseChangeHomeomorph_val_tmul (x : RelativeSpectrum u (T ⊗[S] (S ⊗[R] A)))
    (t : T) (a : A) :
    (iteratedBaseChangeHomeomorph u x).1.val (t ⊗ₜ[R] a) =
      x.1.val (t ⊗ₜ[S] ((1 : S) ⊗ₜ[R] a)) := by
  change x.1.val ((Algebra.TensorProduct.cancelBaseChange R S T T A).symm (t ⊗ₜ[R] a)) = _
  rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]

/-- The inverse comparison evaluates every nested pure tensor by its canonical scalar product. -/
@[simp]
theorem iteratedBaseChangeHomeomorph_symm_val_tmul (y : RelativeSpectrum u (T ⊗[R] A))
    (t : T) (s : S) (a : A) :
    ((iteratedBaseChangeHomeomorph u).symm y).1.val (t ⊗ₜ[S] (s ⊗ₜ[R] a)) =
      y.1.val ((s • t) ⊗ₜ[R] a) := by
  change y.1.val (Algebra.TensorProduct.cancelBaseChange R S T T A
    (t ⊗ₜ[S] (s ⊗ₜ[R] a))) = _
  rw [Algebra.TensorProduct.cancelBaseChange_tmul]

/-- Direct restriction agrees with successive restrictions on every original algebra element. -/
theorem baseChangeRestriction_iterated (hwv : ∀ r, w (algebraMap R S r) = v r)
    (huw : ∀ s, u (algebraMap S T s) = w s)
    (x : RelativeSpectrum u (T ⊗[S] (S ⊗[R] A))) :
    baseChangeRestriction hwv (baseChangeRestriction huw x) =
      baseChangeRestriction (scalarCompatibility_tower hwv huw) (iteratedBaseChangeHomeomorph u x) := by
  apply Subtype.ext
  refine Spectrum.ext_val fun a => ?_
  simp only [baseChangeRestriction_val_apply, iteratedBaseChangeHomeomorph_val_tmul]

end IteratedBaseChange

end EnvelopeProperty.Berkovich.RelativeSpectrum
