import EnvelopeProperty.AlgGeom.MonogenicBirationalPresentation
import EnvelopeProperty.AlgGeom.BirationalCurveClosures

/-!
# Actual rational fibres on the common monogenic open

The actual rational fibre of the ORIGINAL finite algebra is identified with the
roots of the monogenic relation on the constructed good base locus. Whole
rational homomorphisms are extended through the genuine common-open isomorphism.
-/

open scoped Polynomial Classical
noncomputable section

namespace EnvelopeProperty.FcCommonOpenFibres

open FcCurveFibres FcCurveClosures

variable {F R C A : Type*} [Field F] [CommRing R] [CommRing C] [CommRing A]
variable [Algebra F R] [Algebra F C] [Algebra F A]

/-- A divisor of a base element cannot vanish at an actual rational point over
a base homomorphism nonzero on that element. -/
theorem apply_ne_zero_of_dvd_base (β : R →ₐ[F] C) (w : R →ₐ[F] F)
    (χ : C →ₐ[F] F) (hbase : χ.comp β = w) (h : C) (g : R)
    (hdiv : h ∣ β g) (hg : w g ≠ 0) : χ h ≠ 0 := by
  intro hz
  obtain ⟨q, hq⟩ := hdiv
  have he := congrArg (fun f : R →ₐ[F] F => f g) hbase
  change χ (β g) = w g at he
  apply hg
  rw [← he, hq, map_mul, hz, zero_mul]

/-- The actual rational homomorphism of the original algebra constructed from
a rational point of the monogenic algebra on their genuine common open. -/
def commonOpenRationalExtension (δ : C →ₐ[F] A) (h : C)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (χ : C →ₐ[F] F) (hχ : χ h ≠ 0) : A →ₐ[F] F :=
  ((IsLocalization.Away.liftAlgHom h (f := χ) (isUnit_iff_ne_zero.mpr hχ)).comp
    e.symm.toAlgHom).comp (IsScalarTower.toAlgHom F A (Localization.Away (δ h)))

/-- The extension retains the entire prescribed rational homomorphism of the
monogenic subalgebra, rather than only its selected generator value. -/
theorem commonOpenRationalExtension_comp (δ : C →ₐ[F] A) (h : C)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : C, e (algebraMap C (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (χ : C →ₐ[F] F) (hχ : χ h ≠ 0) :
    (commonOpenRationalExtension δ h e χ hχ).comp δ = χ := by
  apply AlgHom.ext
  intro c
  change IsLocalization.Away.liftAlgHom h (f := χ) (isUnit_iff_ne_zero.mpr hχ)
    (e.symm (algebraMap A (Localization.Away (δ h)) (δ c))) = χ c
  rw [← he c, e.symm_apply_apply]
  exact IsLocalization.Away.lift_eq h (g := χ.toRingHom) (isUnit_iff_ne_zero.mpr hχ) c

/-- On the constructed common-open base locus, the ACTUAL rational fibre of the
original algebra is in bijection with the roots of the specialized monogenic
polynomial. Both original point construction and whole-map uniqueness are proved. -/
def rationalFibreEquivRoots_of_commonOpen
    (P : R[X]) (δ : AdjoinRoot P →ₐ[F] A) (φ : R →ₐ[F] A)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : R)
    (hdiv : h ∣ algebraMap R (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (w : R →ₐ[F] F) (hw : w g ≠ 0) :
    {χ : A →ₐ[F] F // χ ∈ rationalFibre φ w} ≃
      {z : F // (P.map w.toRingHom).IsRoot z} := by
  let β := AdjoinRoot.ofAlgHom F P
  have hbase (χ : {χ : A →ₐ[F] F // χ ∈ rationalFibre φ w}) :
      (χ.1.comp δ).comp β = w := by
    rw [AlgHom.comp_assoc, hδ]
    exact χ.2
  let f : {χ : A →ₐ[F] F // χ ∈ rationalFibre φ w} →
      {z : F // (P.map w.toRingHom).IsRoot z} := fun χ =>
    FcMonogenicFibres.rationalFibreEquivRoots P w ⟨χ.1.comp δ, hbase χ⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro χ ψ hz
    have hroot := congrArg Subtype.val hz
    change (χ.1.comp δ) (AdjoinRoot.root P) = (ψ.1.comp δ) (AdjoinRoot.root P) at hroot
    have hrestrict : χ.1.comp δ = ψ.1.comp δ :=
      AdjoinRoot.algHom_ext' ((hbase χ).trans (hbase ψ).symm) hroot
    have hχh : χ.1 (δ h) ≠ 0 := apply_ne_zero_of_dvd_base β w
      (χ.1.comp δ) (hbase χ) h g hdiv hw
    apply Subtype.ext
    exact commonOpen_rationalHom_ext δ h e he χ.1 ψ.1 hχh hrestrict
  · intro z
    let χC := (FcMonogenicFibres.rationalFibreEquivRoots P w).symm z
    have hχC : χC.1 h ≠ 0 := apply_ne_zero_of_dvd_base β w χC.1 χC.2 h g hdiv hw
    let χ := commonOpenRationalExtension δ h e χC.1 hχC
    have hrestrict : χ.comp δ = χC.1 := commonOpenRationalExtension_comp δ h e he χC.1 hχC
    have hχbase : χ.comp φ = w := by
      calc
        χ.comp φ = (χ.comp δ).comp β := by rw [AlgHom.comp_assoc, hδ]
        _ = χC.1.comp β := by rw [hrestrict]
        _ = w := χC.2
    refine ⟨⟨χ, hχbase⟩, ?_⟩
    apply Subtype.ext
    change χ (δ (AdjoinRoot.root P)) = z.1
    have hr := congrArg (fun f : AdjoinRoot P →ₐ[F] F => f (AdjoinRoot.root P)) hrestrict
    have hz := congrArg Subtype.val
      ((FcMonogenicFibres.rationalFibreEquivRoots P w).apply_symm_apply z)
    exact hr.trans hz

theorem root_injective_on_rationalFibre_of_commonOpen
    (P : R[X]) (δ : AdjoinRoot P →ₐ[F] A) (φ : R →ₐ[F] A)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : R)
    (hdiv : h ∣ algebraMap R (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (w : R →ₐ[F] F) (hw : w g ≠ 0) :
    Set.InjOn (fun χ : A →ₐ[F] F => χ (δ (AdjoinRoot.root P))) (rationalFibre φ w) := by
  let ef := rationalFibreEquivRoots_of_commonOpen P δ φ hδ h g hdiv e he w hw
  intro χ hχ ψ hψ hz
  have heq : ef ⟨χ, hχ⟩ = ef ⟨ψ, hψ⟩ := Subtype.ext hz
  exact congrArg Subtype.val (ef.injective heq)

/-- The image of the actual original fibre under the actual primitive element
is the entire root set of the specialized polynomial, with both directions proved. -/
theorem image_root_rationalFibreFinset_of_commonOpen
    (P : R[X]) (hP : P.Monic) (δ : AdjoinRoot P →ₐ[F] A)
    (φ : R →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : R)
    (hdiv : h ∣ algebraMap R (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (w : R →ₐ[F] F) (hw : w g ≠ 0) :
    (rationalFibreFinset φ hφ w).image (fun χ => χ (δ (AdjoinRoot.root P))) =
      (P.map w.toRingHom).roots.toFinset := by
  let ef := rationalFibreEquivRoots_of_commonOpen P δ φ hδ h g hdiv e he w hw
  ext z
  rw [Finset.mem_image, Multiset.mem_toFinset,
    Polynomial.mem_roots (hP.map w.toRingHom).ne_zero]
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    exact (ef ⟨χ, (mem_rationalFibreFinset _ _ _ _).mp hχ⟩).2
  · intro hz
    obtain ⟨χ, hχ⟩ := ef.surjective ⟨z, hz⟩
    refine ⟨χ.1, (mem_rationalFibreFinset _ _ _ _).mpr χ.2, ?_⟩
    exact congrArg Subtype.val hχ

/-- On a separable good fibre the defining polynomial is the product over the
ACTUAL rational points of the original algebra, with each point occurring once. -/
theorem prod_rationalFibre_eq_map_of_commonOpen [IsAlgClosed F]
    (P : R[X]) (hP : P.Monic) (δ : AdjoinRoot P →ₐ[F] A)
    (φ : R →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : R)
    (hdiv : h ∣ algebraMap R (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (w : R →ₐ[F] F) (hw : w g ≠ 0) (hsep : (P.map w.toRingHom).Separable) :
    (∏ χ ∈ rationalFibreFinset φ hφ w,
      (Polynomial.X - Polynomial.C (χ (δ (AdjoinRoot.root P))))) = P.map w.toRingHom := by
  have hinj : Set.InjOn (fun χ : A →ₐ[F] F => χ (δ (AdjoinRoot.root P)))
      (↑(rationalFibreFinset φ hφ w)) := by
    intro χ hχ ψ hψ hz
    exact root_injective_on_rationalFibre_of_commonOpen P δ φ hδ h g hdiv e he w hw
      ((mem_rationalFibreFinset _ _ _ _).mp hχ) ((mem_rationalFibreFinset _ _ _ _).mp hψ) hz
  rw [← Finset.prod_image (f := fun z : F => Polynomial.X - Polynomial.C z) hinj,
    image_root_rationalFibreFinset_of_commonOpen P hP δ φ hφ hδ h g hdiv e he w hw]
  have hv : (P.map w.toRingHom).roots.toFinset.val = (P.map w.toRingHom).roots := by
    rw [Multiset.toFinset_val, (Polynomial.nodup_roots hsep).dedup]
  change ((P.map w.toRingHom).roots.toFinset.val.map
    (fun z => Polynomial.X - Polynomial.C z)).prod = _
  rw [hv]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
    IsAlgClosed.card_roots_eq_natDegree

/-- The complementary actual original-spectrum class factors recover the
specialized polynomial. No fibre identification or factorization is an input. -/
theorem fibreClassFactor_mul_compl_eq_map_of_commonOpen [IsAlgClosed F]
    (P : R[X]) (hP : P.Monic) (δ : AdjoinRoot P →ₐ[F] A)
    (φ : R →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : R)
    (hdiv : h ∣ algebraMap R (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (S : Set (PrimeSpectrum A)) (w : R →ₐ[F] F) (hw : w g ≠ 0)
    (hsep : (P.map w.toRingHom).Separable) :
    fibreClassFactor φ hφ S (δ (AdjoinRoot.root P)) w *
      fibreClassFactor φ hφ Sᶜ (δ (AdjoinRoot.root P)) w = P.map w.toRingHom := by
  change classFactor _ S _ * classFactor _ Sᶜ _ = _
  rw [classFactor_mul_compl]
  exact prod_rationalFibre_eq_map_of_commonOpen P hP δ φ hφ hδ h g hdiv e he w hw hsep

theorem fibreClassFactor_dvd_map_of_commonOpen [IsAlgClosed F]
    (P : R[X]) (hP : P.Monic) (δ : AdjoinRoot P →ₐ[F] A)
    (φ : R →ₐ[F] A) (hφ : φ.toRingHom.Finite)
    (hδ : δ.comp (AdjoinRoot.ofAlgHom F P) = φ) (h : AdjoinRoot P) (g : R)
    (hdiv : h ∣ algebraMap R (AdjoinRoot P) g)
    (e : Localization.Away h ≃ₐ[F] Localization.Away (δ h))
    (he : ∀ c : AdjoinRoot P, e (algebraMap _ (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c))
    (S : Set (PrimeSpectrum A)) (w : R →ₐ[F] F) (hw : w g ≠ 0)
    (hsep : (P.map w.toRingHom).Separable) :
    fibreClassFactor φ hφ S (δ (AdjoinRoot.root P)) w ∣ P.map w.toRingHom :=
  ⟨_, (fibreClassFactor_mul_compl_eq_map_of_commonOpen P hP δ φ hφ hδ h g hdiv e he S w hw hsep).symm⟩

end EnvelopeProperty.FcCommonOpenFibres
