import EnvelopeProperty.Char0.RoundedCanonicalOpenFactorization

/-! # SAME whole original rounded quotient detected on actual original open covers -/

open CategoryTheory AlgebraicGeometry
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Original smoothness internally derives monicity of the SAME whole
original absolute rounded canonical inclusion. -/
theorem mono_absoluteRoundedInclusion (f : Y ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (J : Y.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : Mono (absoluteRoundedInclusion f n J hJ q) := by
  let : Mono (idealModuleInclusion J hJ q) := mono_idealModuleInclusion J hJ q
  have : Mono (SchemeTensorObjMorphisms.tensorObjMap
      (𝟙 (CanonicalGeometry.canonicalLineSheaf f n)) (idealModuleInclusion J hJ q)) :=
    SchemeTensorObjMorphisms.mono_tensorObjMap_left (CanonicalGeometry.canonicalLineSheaf f n)
      (CanonicalGeometry.canonicalLineSheaf_isInvertible f n) _
  change Mono (SchemeTensorObjMorphisms.tensorObjMap
      (𝟙 (CanonicalGeometry.canonicalLineSheaf f n)) (idealModuleInclusion J hJ q) ≫
    (Scheme.Modules.tensorObjUnitIso (CanonicalGeometry.canonicalLineSheaf f n)).hom)
  infer_instance

/-- The SAME whole original quotient kills EVERY actual original function
iff EVERY genuine original covering open composite's ENTIRE original scalar
differential factors through the SAME actual absolute rounded canonical inclusion. -/
theorem quotientDifferentialSection_apply_eq_zero_iff_open_cover_factorization [CharZero k]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : Γ(Y, ⊤))
    {ι : Type v} (Z : ι → Scheme.{u}) (j : (i : ι) → Z i ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ y : Y, ∃ (i : ι) (z : Z i), j i z = y) :
    letI : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
    (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) a = 0 ↔
      ∀ i, ∃ θ : (Scheme.Modules.pullback (j i ≫ g)).obj
            (CanonicalGeometry.canonicalLineSheaf f n) ⟶
          absolute ((j i ≫ g) ≫ f) n (J.comap (j i))
            (hJ.comap_of_smooth (g ≫ f) (j i)) q,
        θ ≫ absoluteRoundedInclusion ((j i ≫ g) ≫ f) n (J.comap (j i))
            (hJ.comap_of_smooth (g ≫ f) (j i)) q =
          SchemeUnitScalarAction.globalScalarAction _ ((j i).appTop a) ≫
            CanonicalGeometry.exteriorCotangentSheafPullbackMap f (j i ≫ g) n := by
  let : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
  let inc := absoluteRoundedInclusion (g ≫ f) n J hJ q
  let : Mono inc := mono_absoluteRoundedInclusion (g ≫ f) n J hJ q
  have hc := SchemeModuleOpenCoverDetection.factorization_iff Z j hcover inc
    (SchemeUnitScalarAction.globalScalarAction _ a ≫
      CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)
  have hq := quotientDifferentialSection_apply_eq_zero_iff_factorization f g n J hJ q a
  refine hq.trans (hc.trans ?_)
  exact forall_congr' fun i => openScalarFactorization_iff f g (j i) n J hJ q a

private theorem originalOpenSmoothDimension (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n (g ≫ f)] {Z : Scheme.{u}} (h : Z ⟶ Y)
    [IsOpenImmersion h] : SmoothOfRelativeDimension n ((h ≫ g) ≫ f) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := h) (n := 0) (m := n) (g ≫ f))

/-- SAME whole original quotient zero is detected by EVERY SAME original
covering-chart quotient zero, deriving ALL original chart smooth dimensions. -/
theorem quotientDifferentialSection_apply_eq_zero_iff_open_cover [CharZero k]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : Γ(Y, ⊤))
    {ι : Type v} (Z : ι → Scheme.{u}) (j : (i : ι) → Z i ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ y : Y, ∃ (i : ι) (z : Z i), j i z = y) :
    letI : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
    letI : ∀ i, SmoothOfRelativeDimension n ((j i ≫ g) ≫ f) :=
      fun i => originalOpenSmoothDimension f g n (j i)
    (quotientDifferentialSection f g n J hJ q).val.app (.op ⊤) a = 0 ↔
      ∀ i, (quotientDifferentialSection f (j i ≫ g) n (J.comap (j i))
        (hJ.comap_of_smooth (g ≫ f) (j i)) q).val.app (.op ⊤) ((j i).appTop a) = 0 := by
  let : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
  let : ∀ i, SmoothOfRelativeDimension n ((j i ≫ g) ≫ f) :=
    fun i => originalOpenSmoothDimension f g n (j i)
  have hc := quotientDifferentialSection_apply_eq_zero_iff_open_cover_factorization
    f g n J hJ q a Z j hcover
  refine hc.trans (forall_congr' fun i => ?_)
  exact (quotientDifferentialSection_apply_eq_zero_iff_factorization f (j i ≫ g) n
    (J.comap (j i)) (hJ.comap_of_smooth (g ≫ f) (j i)) q ((j i).appTop a)).symm

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
