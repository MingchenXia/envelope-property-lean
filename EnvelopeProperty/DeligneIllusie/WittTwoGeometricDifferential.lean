import EnvelopeProperty.DeligneIllusie.WittTwoSheafFormComparison
import EnvelopeProperty.Cartier.SmoothSchemeDeRham

/-! # Actual original global differential under SAME whole residue-form comparison -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoGeometricDifferential
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local instance] KaehlerAlgebraEquivalence.inversePair
private instance inversePairReverse {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] (e : A ≃ₐ[R] C) :
    RingHomInvPair e.symm.toRingHom e.toRingHom where
  comp_eq := by ext c; exact e.apply_symm_apply c
  comp_eq₂ := by ext a; exact e.symm_apply_apply a

private theorem nativeEquiv_canonical {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] (e : A ≃ₐ[R] C) (q : ℕ) (w : ⋀[A]^q (KaehlerDifferential R A)) :
    letI := e.toRingHom.toAlgebra
    letI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
    CanonicalGeometry.exteriorSemilinearMap e.toRingHom (KaehlerAlgebraEquivalence.equiv e).toLinearMap q w =
      Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := C) q w := by
  let := e.toRingHom.toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  have hw : w ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := KaehlerDifferential R A))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t,rfl⟩ := hw
    rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti,Char0.canonicalDifferentialLinearMap_wedge]
    rfl
  | zero => simp only [map_zero]
  | add z w _ _ hz hw => rw [map_add,map_add,hz,hw]
  | smul a w _ hw =>
    rw [LinearMap.map_smulₛₗ,map_smul,hw]
    exact IsScalarTower.algebraMap_smul C a _

private theorem nativeCoordinates_etale {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] (e : A ≃ₐ[R] C) {n : ℕ} (v : Fin n → C)
    (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale) :
    (MvPolynomial.aeval (R := R) (fun j => e.symm (v j))).toRingHom.Etale := by
  let := e.symm.toRingHom.toAlgebra
  let : IsScalarTower R C A := IsScalarTower.of_algebraMap_eq fun a => (e.symm.commutes a).symm
  exact Char0.etale_aeval_algebraMap v hv (RingHom.Etale.of_bijective e.symm.bijective)

private theorem nativeDifferentialNaturality {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C] {m n : ℕ}
    (a : Fin m → A) (ha : (MvPolynomial.aeval (R := R) a).toRingHom.Etale)
    (v : Fin n → C) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (q : ℕ) (w : ⋀[A]^q (KaehlerDifferential R A)) :
    Cartier.EtaleDeRham.differential v hv q
        (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := C) q w) =
      Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := C) (q+1)
        (Cartier.EtaleDeRham.differential a ha q w) := by
  exact Cartier.EtaleDifferentialNaturality.differential_canonicalMap
    (R := R) (A := A) (B := C) a ha v hv q w


private theorem nativeRawDifferential {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C] {m n : ℕ}
    (a : Fin m → A) (ha : (MvPolynomial.aeval (R := R) a).toRingHom.Etale)
    (v : Fin n → C) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (q : ℕ) (f₀ : (⋀[A]^q (KaehlerDifferential R A)) → (⋀[C]^q (KaehlerDifferential R C)))
    (f₁ : (⋀[A]^(q+1) (KaehlerDifferential R A)) → (⋀[C]^(q+1) (KaehlerDifferential R C)))
    (h₀ : ∀ w, f₀ w = Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := C) q w)
    (h₁ : ∀ w, f₁ w = Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := C) (q+1) w)
    (w : ⋀[A]^q (KaehlerDifferential R A)) :
    Cartier.EtaleDeRham.differential v hv q (f₀ w) = f₁ (Cartier.EtaleDeRham.differential a ha q w) := by
  rw [h₀,h₁]
  exact nativeDifferentialNaturality a ha v hv q w

private theorem nativeOriginalRawTransfer {K A : Type u} [Field K] [CommRing A]
    [Algebra K A] {Z : Scheme.{u}} (h : Z ⟶ Spec (CommRingCat.of K))
    {V : Z.Opens} {m n : ℕ} (a : Fin m → A)
    (ha : (MvPolynomial.aeval (R := K) a).toRingHom.Etale)
    (v : Fin n → Γ(Z,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra h V;
      (MvPolynomial.aeval (R := K) v).toRingHom.Etale)
    (q : ℕ)
    (t₀ : (⋀[A]^q (KaehlerDifferential K A)) → (CanonicalGeometry.exteriorCotangentPresheaf h q).obj (op V))
    (t₁ : (⋀[A]^(q+1) (KaehlerDifferential K A)) → (CanonicalGeometry.exteriorCotangentPresheaf h (q+1)).obj (op V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra h V
    ∀ [Algebra A Γ(Z,V)] [IsScalarTower K A Γ(Z,V)],
    (∀ w, t₀ w = Char0.canonicalDifferentialLinearMap (k := K) (R := A) (A := Γ(Z,V)) q w) →
    (∀ w, t₁ w = Char0.canonicalDifferentialLinearMap (k := K) (R := A) (A := Γ(Z,V)) (q+1) w) →
    ∀ w, Cartier.EtaleAffineSectionDifferential.rawDifferential h v hv q (t₀ w) =
      t₁ (Cartier.EtaleDeRham.differential a ha q w) := by
  let := CanonicalGeometry.cotangentOpenAlgebra h V
  intro _ _ h₀ h₁ w
  exact nativeRawDifferential a ha v hv q t₀ t₁ h₀ h₁ w

private theorem nativeGlobalTransfer {K : Type u} [Field K] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (CommRingCat.of K)) (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) [SmoothOfRelativeDimension n h] {V : Z.Opens} (hV : IsAffineOpen V)
    (v : Fin n → Γ(Z,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra h V;
      (MvPolynomial.aeval (R := K) v).toRingHom.Etale)
    (q : ℕ) {A₀ A₁ : Type u} (d : A₀ → A₁)
    (t₀ : A₀ → (CanonicalGeometry.exteriorCotangentPresheaf h q).obj (op V))
    (t₁ : A₁ → (CanonicalGeometry.exteriorCotangentPresheaf h (q+1)).obj (op V))
    (hr : letI := CanonicalGeometry.cotangentOpenAlgebra h V;
      ∀ w, Cartier.EtaleAffineSectionDifferential.rawDifferential h v hv q (t₀ w) = t₁ (d w)) (w : A₀) :
    (Cartier.SmoothSchemeDeRham.differential h p n q).val.app (op V)
      ((CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf h) q).app (op V) (t₀ w)) =
    (CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf h) (q+1)).app (op V) (t₁ (d w)) := by
  have hd := Cartier.SmoothSchemeDeRham.differential_unit h p n hV v hv q (t₀ w)
  exact hd.trans (congrArg ((CanonicalGeometry.exteriorSheafificationMap
    (CanonicalGeometry.cotangentPresheaf h) (q+1)).app (op V)) (hr w))

private theorem nativeGlobalCanonicalTransfer {K A : Type u} [Field K] [CommRing A]
    [Algebra K A] {Z : Scheme.{u}} (h : Z ⟶ Spec (CommRingCat.of K))
    (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) [SmoothOfRelativeDimension n h]
    {V : Z.Opens} (hV : IsAffineOpen V) {m : ℕ} (a : Fin m → A)
    (ha : (MvPolynomial.aeval (R := K) a).toRingHom.Etale)
    (v : Fin n → Γ(Z,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra h V;
      (MvPolynomial.aeval (R := K) v).toRingHom.Etale)
    (q : ℕ)
    (t₀ : (⋀[A]^q (KaehlerDifferential K A)) → (CanonicalGeometry.exteriorCotangentPresheaf h q).obj (op V))
    (t₁ : (⋀[A]^(q+1) (KaehlerDifferential K A)) → (CanonicalGeometry.exteriorCotangentPresheaf h (q+1)).obj (op V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra h V
    ∀ [Algebra A Γ(Z,V)] [IsScalarTower K A Γ(Z,V)],
    (∀ w, t₀ w = Char0.canonicalDifferentialLinearMap (k := K) (R := A) (A := Γ(Z,V)) q w) →
    (∀ w, t₁ w = Char0.canonicalDifferentialLinearMap (k := K) (R := A) (A := Γ(Z,V)) (q+1) w) →
    ∀ w, (Cartier.SmoothSchemeDeRham.differential h p n q).val.app (op V)
      ((CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf h) q).app (op V) (t₀ w)) =
    (CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf h) (q+1)).app (op V)
      (t₁ (Cartier.EtaleDeRham.differential a ha q w)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra h V
  intro _ _ h₀ h₁ w
  exact nativeGlobalTransfer h p n hV v hv q (Cartier.EtaleDeRham.differential a ha q) t₀ t₁
    (nativeOriginalRawTransfer h a ha v hv q t₀ t₁ h₀ h₁) w

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
attribute [local instance] WittTwoResidue.reductionAlgebra
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
private abbrev X := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev g : X p k f ⟶ Spec (CommRingCat.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev U₀ (U : Y.Opens) := WittTwoSpecialFibreOpens.residueOpen p k f U
private abbrev B (U : Y.Opens) :=
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)
@[instance_reducible] private def rawModule (U : Y.Opens) (q : ℕ) :
    Module Γ(X p k f,U₀ p k f U)
      ((CanonicalGeometry.exteriorCotangentPresheaf (g p k f) q).obj (op (U₀ p k f U))) :=
  ((CanonicalGeometry.exteriorCotangentPresheaf (g p k f) q).obj (op (U₀ p k f U))).isModule
attribute [local instance] rawModule

/-- The SAME entire original ring equivalence retains the EXACT native cotangent-presheaf structural action. -/
def sectionEquiv {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
    B p k f U ≃ₐ[k] Γ(X p k f,U₀ p k f U) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  let e := WittTwoSpecialFibreOpens.residueOpenSections p k f hU
  refine { e.toRingEquiv with commutes' := ?_ }
  intro a
  exact (e.commutes a).trans (congrArg (fun ab : Algebra k Γ(X p k f,U₀ p k f U) =>
    @algebraMap k Γ(X p k f,U₀ p k f U) _ _ ab a)
      (WittTwoOriginalFormPresheaf.sectionAlgebra_eq (g p k f) (U₀ p k f U)))

/-- EVERY original residue element keeps its SAME actual old geometric section value. -/
theorem sectionEquiv_value {U : Y.Opens} (hU : IsAffineOpen U) (b : B p k f U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
    sectionEquiv p k f hU b = WittTwoSpecialFibreOpens.residueOpenSections p k f hU b := by
  rfl

/-- ACTUAL native residue coordinates are the original geometric coordinates under the SAME section equivalence. -/
def coordinates {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ} (v : Fin n → Γ(X p k f,U₀ p k f U)) :
    Fin n → B p k f U := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  exact fun j => (sectionEquiv p k f hU).symm (v j)

/-- Genuine original etale coordinates give genuine native etale residue coordinates, with no matching input. -/
theorem coordinates_etale {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (v : Fin n → Γ(X p k f,U₀ p k f U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U);
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (MvPolynomial.aeval (R := k) (coordinates p k f hU v)).toRingHom.Etale := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  exact nativeCoordinates_etale (sectionEquiv p k f hU) v hv

/-- EVERY original raw form has the SAME native canonical differential-map value. -/
theorem rawFormsEquiv_canonicalMap {U : Y.Opens} (hU : IsAffineOpen U) (q : ℕ)
    (w : ⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
    letI := (sectionEquiv p k f hU).toRingHom.toAlgebra
    letI : IsScalarTower k (B p k f U) Γ(X p k f,U₀ p k f U) :=
      IsScalarTower.of_algebraMap_eq fun a => ((sectionEquiv p k f hU).commutes a).symm
    (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU q).toLinearMap w =
      Char0.canonicalDifferentialLinearMap (k := k) (R := B p k f U)
        (A := Γ(X p k f,U₀ p k f U)) q w := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  let := (sectionEquiv p k f hU).toRingHom.toAlgebra
  let : IsScalarTower k (B p k f U) Γ(X p k f,U₀ p k f U) :=
    IsScalarTower.of_algebraMap_eq fun a => ((sectionEquiv p k f hU).commutes a).symm
  exact nativeEquiv_canonical (sectionEquiv p k f hU) q w

/-- The SAME actual raw form equivalence commutes with genuine native etale differentials on EVERY form. -/
theorem rawFormsEquiv_differential {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (v : Fin n → Γ(X p k f,U₀ p k f U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U);
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (q : ℕ) (w : ⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
    Cartier.EtaleAffineSectionDifferential.rawDifferential (g p k f) v hv q
      ((WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU q).toLinearMap w) =
    (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU (q+1)).toLinearMap
      (Cartier.EtaleDeRham.differential (coordinates p k f hU v)
        (coordinates_etale p k f hU v hv) q w) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  let := (sectionEquiv p k f hU).toRingHom.toAlgebra
  let : IsScalarTower k (B p k f U) Γ(X p k f,U₀ p k f U) :=
    IsScalarTower.of_algebraMap_eq fun a => ((sectionEquiv p k f hU).commutes a).symm
  exact nativeOriginalRawTransfer (g p k f) (coordinates p k f hU v) (coordinates_etale p k f hU v hv) v hv q
    (fun z => (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU q).toLinearMap z)
    (fun z => (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU (q+1)).toLinearMap z)
    (rawFormsEquiv_canonicalMap p k f hU q) (rawFormsEquiv_canonicalMap p k f hU (q+1)) w

variable [CharP k p] (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The SAME original GLOBAL native differential commutes with the actual whole residue-form sheaf comparison. -/
theorem differential_sheafFormsMap {U : Y.Opens} (hU : IsAffineOpen U)
    (v : Fin n → Γ(X p k f,U₀ p k f U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U);
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (q : ℕ) (w : ⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
    (Cartier.SmoothSchemeDeRham.differential (g p k f) p n q).val.app (op (U₀ p k f U))
        (WittTwoSheafFormComparison.sheafFormsMap p k f hU q w) =
      WittTwoSheafFormComparison.sheafFormsMap p k f hU (q+1)
        (Cartier.EtaleDeRham.differential (coordinates p k f hU v)
          (coordinates_etale p k f hU v hv) q w) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p k f n
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  rw [WittTwoSheafFormComparison.sheafFormsMap_value,WittTwoSheafFormComparison.sheafFormsMap_value]
  let := (sectionEquiv p k f hU).toRingHom.toAlgebra
  let : IsScalarTower k (B p k f U) Γ(X p k f,U₀ p k f U) :=
    IsScalarTower.of_algebraMap_eq fun a => ((sectionEquiv p k f hU).commutes a).symm
  exact nativeGlobalCanonicalTransfer (g p k f) p n
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU)
    (coordinates p k f hU v) (coordinates_etale p k f hU v hv) v hv q
    (fun z => (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU q).toLinearMap z)
    (fun z => (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU (q+1)).toLinearMap z)
    (rawFormsEquiv_canonicalMap p k f hU q) (rawFormsEquiv_canonicalMap p k f hU (q+1)) w

end EnvelopeProperty.DeligneIllusie.WittTwoGeometricDifferential
