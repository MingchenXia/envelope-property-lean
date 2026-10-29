import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeTensorSectionCoefficients
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeCoordinateGenerators

/-!
# Every original saturated tensor degree is actual native H0

True inverse tensor frames, literal intrinsic ratios and genuine sheaf
gluing produce the full original R_(m·1)/native H0 comparison for EVERY
natural m, including zero. The k-action is the actual structural base
action, with no assumed section, scalar, gluing or saturation matching.
Route: owned `native-tensor-global-sections-route.tex`.
-/
open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModularCurves
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

private theorem originalNonzeroTensorCoordinateCover (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) :
    (⊤ : X.nativeRankOneScheme.Opens) ≤
      ⨆ i : {i : X.ChartIndex // ∀ c, X.coord c (i c) ≠ 0},
        X.nativeRankOneCoordinateOpen (i.val 0) := by
  intro y _
  obtain ⟨i, hi, hy, _⟩ := X.nativeRankOne_existsCoordinateGlobalGenerator j hj y
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hy⟩

/-- Actual sheafgluing produces a genuine native GLOBAL section from every
ORIGINAL fully saturated nonnegative tensor-degree coefficient, with every exact original
coordinate restriction. No gluing/matching premise is supplied. -/
theorem nativeRankOne_existsTensorGlobalSectionOfOriginal (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    ∃ s : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤), ∀ (i : X.ChartIndex)
      (hi : ∀ c, X.coord c (i c) ≠ 0),
      (bundleTensorPower (X.nativeRankOneCoordinateLine j) m).presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op s =
        X.nativeRankOneTensorLocalSectionOfOriginal i hi j hj m f := by
  let M := bundleTensorPower (X.nativeRankOneCoordinateLine j) m
  let V := {i : X.ChartIndex // ∀ c, X.coord c (i c) ≠ 0}
  let U : V → X.nativeRankOneScheme.Opens := fun i => X.nativeRankOneCoordinateOpen (i.val 0)
  let s (i : V) := X.nativeRankOneTensorLocalSectionOfOriginal i.val i.property j hj m f
  have hcpt : ∀ i l : V,
      M.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U l)).op (s i) =
        M.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U l)).op (s l) := by
    intro i l
    have : Nonempty (U i) := X.nativeRankOneCoordinateOpen_nonempty i.val i.property
    have : Nonempty (U l) := X.nativeRankOneCoordinateOpen_nonempty l.val l.property
    have : Nonempty (U i ⊓ U l : X.nativeRankOneScheme.Opens) := ⟨⟨genericPoint X.nativeRankOneScheme,
      X.nativeRankOneGenericPoint_mem_coordinateOpen i.val i.property,
      X.nativeRankOneGenericPoint_mem_coordinateOpen l.val l.property⟩⟩
    apply sectionRatio_injective M (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
      (X.nativeRankOneCoordinatePoleTensorPower j m) (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m)
      (U i ⊓ U l)
    have hleft : TopologicalSpace.Opens.infLELeft (U i) (U l) =
        homOfLE (inf_le_left : U i ⊓ U l ≤ U i) := Subsingleton.elim _ _
    have hright : TopologicalSpace.Opens.infLERight (U i) (U l) =
        homOfLE (inf_le_right : U i ⊓ U l ≤ U l) := Subsingleton.elim _ _
    rw [hleft, hright, sectionRatio_restrict, sectionRatio_restrict,
      X.nativeRankOneTensorLocalSectionOfOriginal_ratio i.val i.property j hj m f,
      X.nativeRankOneTensorLocalSectionOfOriginal_ratio l.val l.property j hj m f,
      X.nativeRankOneFunctionFieldEquiv_independent i.val l.val i.property l.property]
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) (originalNonzeroTensorCoordinateCover X j hj) s hcpt
  exact ⟨t, fun i hi => ht ⟨i, hi⟩⟩

/-- The genuine native global section constructed by actual sheaf gluing. -/
def nativeRankOneTensorGlobalSectionOfOriginal (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤) :=
  (X.nativeRankOne_existsTensorGlobalSectionOfOriginal j hj m f).choose

/-- Every whole original coordinate restriction of the actual glued section
is precisely the actual inverse-frame section of f/c_i^m. -/
theorem nativeRankOneTensorGlobalSectionOfOriginal_restrict (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    (bundleTensorPower (X.nativeRankOneCoordinateLine j) m).presheaf.map
      (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
      (X.nativeRankOneTensorGlobalSectionOfOriginal j hj m f) =
      X.nativeRankOneTensorLocalSectionOfOriginal i hi j hj m f :=
  (X.nativeRankOne_existsTensorGlobalSectionOfOriginal j hj m f).choose_spec i hi

/-- The true global coefficient of the actual glued native section is the
SAME ORIGINAL saturated coefficient. -/
theorem nativeRankOneTensorGlobalSectionOfOriginal_coefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m
      (X.nativeRankOneTensorGlobalSectionOfOriginal j hj m f) = (f : K) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  have hq := sectionRatio_restrict (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
    (X.nativeRankOneCoordinatePoleTensorPower j m) (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m)
    (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)
    (X.nativeRankOneTensorGlobalSectionOfOriginal j hj m f)
  rw [X.nativeRankOneTensorGlobalSectionOfOriginal_restrict i hi j hj m f,
    X.nativeRankOneTensorLocalSectionOfOriginal_ratio i hi j hj m f] at hq
  unfold nativeRankOneTensorGlobalSectionCoefficient
  rw [← hq, RingEquiv.symm_apply_apply]
  exact (mul_comm _ _).trans (div_mul_cancel₀ _ (pow_ne_zero m hj))

/-- Actual tensor H0 uses its genuine structural base scalar action. -/
abbrev nativeRankOneTensorH0BaseModule (j : Fin (X.M 0 + 1)) (m : ℕ) :
    Module k Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤) :=
  Module.compHom Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤)
    X.nativeRankOneBaseConstants

/-- The ORIGINAL full saturated R_(m·1) is ACTUAL native tensor H0,
linearly over the SAME actual original structural base action. -/
def nativeRankOneTensorH0OriginalSectionsLinearEquiv (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) :
    letI := X.nativeRankOneTensorH0BaseModule j m
    Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤) ≃ₗ[k]
      X.sections (m • (1 : Fin 1 → ℤ)) := by
  letI := X.nativeRankOneTensorH0BaseModule j m
  let F : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤) →ₗ[k]
      X.sections (m • (1 : Fin 1 → ℤ)) := {
    toFun s := ⟨X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m s,
      X.nativeRankOneTensorGlobalSectionCoefficient_mem_sections i hi j hj m s⟩
    map_add' s t := by
      apply Subtype.ext
      exact X.nativeRankOneTensorGlobalSectionCoefficient_add i hi j hj m s t
    map_smul' a s := by
      apply Subtype.ext
      change X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m
        (X.nativeRankOneBaseConstants a • s) =
        a • X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m s
      rw [Algebra.smul_def]
      exact X.nativeRankOneTensorGlobalSectionCoefficient_base_smul i hi j hj m a s }
  exact LinearEquiv.ofBijective F
    ⟨fun _ _ h => X.nativeRankOneTensorGlobalSectionCoefficient_injective i hi j hj m
      (congrArg Subtype.val h), fun f =>
      ⟨X.nativeRankOneTensorGlobalSectionOfOriginal j hj m f,
        Subtype.ext (X.nativeRankOneTensorGlobalSectionOfOriginal_coefficient i hi j hj m f)⟩⟩

/-- The actual k-linear equivalence is the SAME literal original coefficient. -/
theorem nativeRankOneTensorH0OriginalSectionsLinearEquiv_apply (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (s : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤)) :
    letI := X.nativeRankOneTensorH0BaseModule j m
    (X.nativeRankOneTensorH0OriginalSectionsLinearEquiv i hi j hj m s : K) =
      X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m s := rfl

/-- Its inverse is the SAME actual section produced by genuine sheaf gluing. -/
theorem nativeRankOneTensorH0OriginalSectionsLinearEquiv_symm (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    letI := X.nativeRankOneTensorH0BaseModule j m
    (X.nativeRankOneTensorH0OriginalSectionsLinearEquiv i hi j hj m).symm f =
      X.nativeRankOneTensorGlobalSectionOfOriginal j hj m f := by
  have := X.nativeRankOneTensorH0BaseModule j m
  apply (X.nativeRankOneTensorH0OriginalSectionsLinearEquiv i hi j hj m).injective
  apply Subtype.ext
  exact (congrArg Subtype.val
    ((X.nativeRankOneTensorH0OriginalSectionsLinearEquiv i hi j hj m).apply_symm_apply f)).trans
      (X.nativeRankOneTensorGlobalSectionOfOriginal_coefficient i hi j hj m f).symm

end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.MultiModel.nativeRankOne_existsTensorGlobalSectionOfOriginal
#print axioms EnvelopeProperty.MultiModel.nativeRankOne_existsTensorGlobalSectionOfOriginal
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionOfOriginal
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionOfOriginal
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionOfOriginal_restrict
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionOfOriginal_restrict
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionOfOriginal_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionOfOriginal_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorH0BaseModule
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorH0BaseModule
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorH0OriginalSectionsLinearEquiv
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorH0OriginalSectionsLinearEquiv
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorH0OriginalSectionsLinearEquiv_apply
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorH0OriginalSectionsLinearEquiv_apply
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorH0OriginalSectionsLinearEquiv_symm
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorH0OriginalSectionsLinearEquiv_symm
