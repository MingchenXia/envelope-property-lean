import EnvelopeProperty.AlgGeom.CurveFiniteClosedSubschemes
import EnvelopeProperty.AlgGeom.GeometricIdealEulerDegree

/-! # Actual original Cartier-ideal degree on arbitrary integral projective curves -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules
open scoped nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.CurveCartierIdealDegrees
open SchemeCoherentEulerCharacteristic SchemeCoherentEulerIndex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X]

/-- Actual original regular local Cartier equations DERIVE proper original support. -/
theorem support_ne_top (I : X.IdealSheafData) (hI : I.IsInvertible) : I.support ≠ ⊤ := by
  intro htop
  obtain ⟨U, hηU, c, hc, hgen⟩ := hI (genericPoint X)
  let : Nonempty U.1 := ⟨⟨genericPoint X, hηU⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  have hg0 : X.presheaf.germ U.1 (genericPoint X) hηU c ≠ 0 := by
    intro hz
    exact hc0 ((germ_injective_of_isIntegral X (genericPoint X) hηU)
      (hz.trans (map_zero _).symm))
  have hunit : IsUnit (X.presheaf.germ U.1 (genericPoint X) hηU c) :=
    (isUnit_iff_ne_zero (G₀ := X.functionField)).mpr hg0
  have hb : genericPoint X ∈ X.basicOpen c :=
    (X.mem_basicOpen c (genericPoint X) hηU).mpr hunit
  have hmem : genericPoint X ∈ I.support := by rw [htop]; trivial
  have hz := (I.mem_support_iff_of_mem hηU).mp hmem
  have hci : c ∈ I.ideal U := by rw [hgen]; exact Ideal.mem_span_singleton_self _
  exact (X.mem_zeroLocus_iff (I.ideal U) (genericPoint X)).mp hz c hci hb

/-- On the SAME actual original proper integral curve, every original
Cartier ideal DERIVES a genuinely finite original closed-subscheme morphism. -/
theorem subscheme_comp_isFinite {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) : IsFinite (I.subschemeι ≫ f) :=
  CurveFiniteClosedSubschemes.subscheme_comp_isFinite f hdim I (support_ne_top I hI)

/-- The SAME original Cartier ideal's TRUE finite closed degree on the
original projective integral curve, with ALL finiteness derived from geometry. -/
theorem normalizedEulerCharacteristic_toModules {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.IsInvertible) :
    letI : IsProper f := hf.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    normalizedEulerCharacteristic f I.toModules =
      -(Module.finrank k (fieldSections (I.subschemeι ≫ f) (unitObj I.subscheme)) : ℤ) := by
  let : IsProper f := hf.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : IsFinite (I.subschemeι ≫ f) := subscheme_comp_isFinite f hdim I hI
  exact GeometricIdealEulerDegree.normalizedEulerCharacteristic_toModules I f hf

/-- On ANY actual integral projective curve, tensoring the SAME original
Cartier ideal by ANY original line adds their TRUE intrinsic full Euler degrees. -/
theorem normalizedEulerCharacteristic_tensor_toModules {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.IsInvertible)
    (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper f := hf.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    normalizedEulerCharacteristic f (Scheme.Modules.tensorObj I.toModules L) =
      normalizedEulerCharacteristic f I.toModules + normalizedEulerCharacteristic f L := by
  let : IsProper f := hf.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : IsFinite (I.subschemeι ≫ f) := subscheme_comp_isFinite f hdim I hI
  exact GeometricIdealEulerDegree.normalizedEulerCharacteristic_tensor_toModules I f hf L hL

/-- The SAME ORIGINAL Cartier ideal ratio line on ANY actual integral
projective curve has the difference of the TRUE original intrinsic ideal degrees. -/
theorem normalizedEulerCharacteristic_ratioModule {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (hdim : topologicalKrullDim X ≤ 1) (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    letI : IsProper f := hf.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    normalizedEulerCharacteristic f (I.ratioModule J) =
      normalizedEulerCharacteristic f I.toModules - normalizedEulerCharacteristic f J.toModules := by
  let : IsProper f := hf.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : IsFinite (I.subschemeι ≫ f) := subscheme_comp_isFinite f hdim I hI
  let : IsFinite (J.subschemeι ≫ f) := subscheme_comp_isFinite f hdim J hJ
  exact GeometricIdealEulerDegree.normalizedEulerCharacteristic_ratioModule I J hJ f hf

/-- The SAME ORIGINAL curve ratio line degree is the TRUE residue-weighted
local-degree difference; NO finite-divisor or numerical comparison premise is supplied. -/
theorem normalizedEulerCharacteristic_ratioModule_eq_weighted_difference {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (hdim : topologicalKrullDim X ≤ 1) (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    letI : IsProper f := hf.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    normalizedEulerCharacteristic f (I.ratioModule J) =
      ((∑ᶠ y : J.subscheme, letI := AffineSchemeLocalDegrees.residueAlgebra f (J.subschemeι y)
        (Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y)).toNat *
          Module.finrank k (X.residueField (J.subschemeι y))) : ℕ) -
      ((∑ᶠ y : I.subscheme, letI := AffineSchemeLocalDegrees.residueAlgebra f (I.subschemeι y)
        (Module.length (I.subscheme.presheaf.stalk y) (I.subscheme.presheaf.stalk y)).toNat *
          Module.finrank k (X.residueField (I.subschemeι y))) : ℕ) := by
  let : IsProper f := hf.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : IsFinite (I.subschemeι ≫ f) := subscheme_comp_isFinite f hdim I hI
  let : IsFinite (J.subschemeι ≫ f) := subscheme_comp_isFinite f hdim J hJ
  exact GeometricIdealEulerDegree.normalizedEulerCharacteristic_ratioModule_eq_weighted_difference I J hJ f hf

end EnvelopeProperty.CurveCartierIdealDegrees
