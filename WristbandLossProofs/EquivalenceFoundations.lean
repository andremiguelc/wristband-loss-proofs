import WristbandLossProofs.EquivalenceImportedFacts

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-! # Equivalence Foundations

Derivations from the three Muirhead axioms in `EquivalenceImportedFacts`.
The four Gaussian-specific facts consumed by `Equivalence.lean`
(`gaussianNZ`, `gaussianPolar_direction_uniform`, `gaussianPolar_radius_chiSq`,
`gaussianPolar_independent`) are proved here. -/

/-! ## Gaussian on `Vec d` — null set at the origin -/

theorem gaussianFull_singletonZeroMeasure (d : ℕ) (hDim : 1 ≤ d) :
    (gaussianFull d).val {0} = 0 := by
  haveI : Nontrivial (Vec d) := vec_nontrivial_of_one_le d hDim
  rw [gaussianFull_density d (measurableSet_singleton 0)]
  exact setLIntegral_measure_zero _ _ (measure_singleton _)

/-! ## Restriction to nonzero vectors -/

/-- `Subtype.val : VecNZ d → Vec d` is a measurable embedding (the underlying
    set `{z ≠ 0}` is the complement of a singleton, hence measurable). -/
lemma measurableEmbedding_vecNZ_val (d : ℕ) :
    MeasurableEmbedding (Subtype.val : VecNZ d → Vec d) := by
  have hSet : ({z : Vec d | z ≠ 0}) = ({(0 : Vec d)}ᶜ) := by ext z; simp
  have hMeas : MeasurableSet ({z : Vec d | z ≠ 0}) := by
    rw [hSet]; exact (measurableSet_singleton 0).compl
  exact MeasurableEmbedding.subtype_coe hMeas

/-- The standard isotropic Gaussian restricted to nonzero vectors. -/
def gaussianNZ (d : ℕ) (hDim : 1 ≤ d) : Distribution (VecNZ d) := by
  haveI hProb : IsProbabilityMeasure (gaussianFull d).val := (gaussianFull d).property
  refine ⟨(gaussianFull d).val.comap Subtype.val, ⟨?_⟩⟩
  have hCompl : (gaussianFull d).val ({(0 : Vec d)}ᶜ) = 1 := by
    rw [prob_compl_eq_one_sub (measurableSet_singleton _),
        gaussianFull_singletonZeroMeasure d hDim]; simp
  have hImg : (Subtype.val : VecNZ d → Vec d) '' Set.univ = ({(0 : Vec d)}ᶜ) := by
    rw [Set.image_univ, Subtype.range_val]; rfl
  calc (Measure.comap (Subtype.val : VecNZ d → Vec d) (gaussianFull d).val) Set.univ
      = (gaussianFull d).val ((Subtype.val : VecNZ d → Vec d) '' Set.univ) :=
        (measurableEmbedding_vecNZ_val d).comap_apply _ _
    _ = (gaussianFull d).val ({(0 : Vec d)}ᶜ) := by rw [hImg]
    _ = 1 := hCompl

/-! ## Rotation invariance -/

/-- Standard isotropic Gaussian is invariant under linear isometries.
    Proof: density depends on `‖x‖²` only, and isometries preserve norms. -/
theorem gaussianFull_rotationInvariant (d : ℕ) (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    Measure.map (fun x : Vec d => O x) (gaussianFull d).val = (gaussianFull d).val := by
  set ρ : Vec d → ENNReal :=
    fun x => ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
  have hO : Measurable (fun x : Vec d => O x) := O.continuous.measurable
  have hOMeasPres : MeasurePreserving (fun x : Vec d => O x)
      (volume : Measure (Vec d)) volume := O.measurePreserving
  have hρInv : ∀ x : Vec d, ρ (O x) = ρ x := by
    intro x; simp [ρ, O.norm_map]
  have hρMeas : Measurable ρ := by
    refine Measurable.ennreal_ofReal ?_
    exact measurable_const.mul (Real.measurable_exp.comp
      ((measurable_norm.pow_const 2).neg.div_const 2))
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hO hs, gaussianFull_density d (hO hs), gaussianFull_density d hs]
  change ∫⁻ x in (fun x => O x) ⁻¹' s, ρ x ∂(volume : Measure (Vec d))
       = ∫⁻ x in s, ρ x ∂(volume : Measure (Vec d))
  rw [← lintegral_indicator (hO hs), ← lintegral_indicator hs]
  -- Pointwise: indicator of preimage agrees with indicator composed with O,
  -- because the density is rotation-invariant.
  have hPointwise :
      ((fun x : Vec d => O x) ⁻¹' s).indicator ρ
        = (s.indicator ρ) ∘ (fun x : Vec d => O x) := by
    funext x
    by_cases hx : O x ∈ s
    · have hx' : x ∈ (fun x : Vec d => O x) ⁻¹' s := hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx', hρInv x]
    · have hx' : x ∉ (fun x : Vec d => O x) ⁻¹' s := hx
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  rw [hPointwise]
  exact hOMeasPres.lintegral_comp (hρMeas.indicator hs)

/-- Restriction of the standard Gaussian to nonzero vectors is rotation invariant.
    Transports `gaussianFull_rotationInvariant` through the
    `Subtype.val ∘ rotateVecNZ = O ∘ Subtype.val` commuting square. -/
theorem gaussianNZ_rotationInvariant (d : ℕ) (hDim : 1 ≤ d)
    (O : (Vec d) ≃ₗᵢ[ℝ] Vec d) :
    pushforward (rotateVecNZ O) (gaussianNZ d hDim) (measurable_rotateVecNZ O)
      = gaussianNZ d hDim := by
  apply Subtype.ext
  change Measure.map (rotateVecNZ O) (gaussianNZ d hDim).val = (gaussianNZ d hDim).val
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_rotateVecNZ O) hs]
  change (Measure.comap Subtype.val (gaussianFull d).val) ((rotateVecNZ O) ⁻¹' s)
       = (Measure.comap Subtype.val (gaussianFull d).val) s
  rw [(measurableEmbedding_vecNZ_val d).comap_apply _ ((rotateVecNZ O) ⁻¹' s),
      (measurableEmbedding_vecNZ_val d).comap_apply _ s]
  -- Subtype.val '' (rotateVecNZ O ⁻¹' s) = O ⁻¹' (Subtype.val '' s) — commutation of the
  -- restriction-to-nonzero square. After this, gaussianFull_rotationInvariant closes the goal.
  have hSet : (Subtype.val : VecNZ d → Vec d) '' ((rotateVecNZ O) ⁻¹' s)
              = (fun x : Vec d => O x) ⁻¹' ((Subtype.val : VecNZ d → Vec d) '' s) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨rotateVecNZ O z, hz, rfl⟩
    · rintro ⟨w, hw, hOyw⟩
      have hyne : y ≠ 0 := by
        intro h
        apply w.2
        rw [hOyw]; change O y = 0
        rw [h]; exact map_zero O
      refine ⟨⟨y, hyne⟩, ?_, rfl⟩
      have hEq : rotateVecNZ O ⟨y, hyne⟩ = w :=
        Subtype.ext (by change O y = w.1; exact hOyw.symm)
      change rotateVecNZ O ⟨y, hyne⟩ ∈ s
      rw [hEq]; exact hw
  rw [hSet]
  have hImgMeas : MeasurableSet ((Subtype.val : VecNZ d → Vec d) '' s) :=
    (measurableEmbedding_vecNZ_val d).measurableSet_image' hs
  rw [← Measure.map_apply O.continuous.measurable hImgMeas,
      gaussianFull_rotationInvariant d O]

/-! ## Polar decomposition for `gaussianNZ`

The three `gaussianPolar_*` theorems below match the signatures of the four old
axioms (now removed), so every downstream call site in `Equivalence.lean`
keeps compiling. -/

/-- `direction#gaussianNZ = sphereUniform` — Thm 1.5.6 applied to `gaussianNZ`. -/
theorem gaussianPolar_direction_uniform (d : ℕ) (hDim : 1 ≤ d) :
    pushforward (direction (d := d)) (gaussianNZ d hDim) (measurable_direction d) =
      sphereUniform d hDim :=
  (spherical_polar_decomposition d hDim (gaussianNZ d hDim)
    (gaussianNZ_rotationInvariant d hDim)).1

/-- `direction ⊥ radiusSq` under `gaussianNZ` — Thm 1.5.6 applied to `gaussianNZ`. -/
theorem gaussianPolar_independent (d : ℕ) (hDim : 1 ≤ d) :
    IndepLaw (gaussianNZ d hDim) (direction (d := d)) (radiusSq (d := d))
      (measurable_direction d) (measurable_radiusSq d) :=
  (spherical_polar_decomposition d hDim (gaussianNZ d hDim)
    (gaussianNZ_rotationInvariant d hDim)).2

/-- `radiusSq#gaussianNZ = chiSqRadiusLaw` — derived from
    `gaussianFull_normSq_chiSq` (Thm 1.4.1(a)) by transporting the chi-squared
    statement from `gaussianFull` (where the axiom lives) down to `gaussianNZ`,
    using that the origin is a null set. -/
theorem gaussianPolar_radius_chiSq (d : ℕ) (hDim : 1 ≤ d) :
    pushforward (radiusSq (d := d)) (gaussianNZ d hDim) (measurable_radiusSq d)
      = chiSqRadiusLaw d := by
  apply Subtype.ext
  change Measure.map (radiusSq (d := d)) (gaussianNZ d hDim).val = (chiSqRadiusLaw d).val
  -- radiusSq = radiusSqVec ∘ Subtype.val on VecNZ d
  have hCompose : (radiusSq (d := d)) = (radiusSqVec (d := d)) ∘ Subtype.val := by
    funext z; exact (radiusSqVec_subtype_val z).symm
  rw [hCompose,
      ← Measure.map_map (measurable_radiusSqVec d) measurable_subtype_coe]
  change Measure.map (radiusSqVec (d := d))
      (Measure.map Subtype.val (Measure.comap Subtype.val (gaussianFull d).val))
    = (chiSqRadiusLaw d).val
  rw [(measurableEmbedding_vecNZ_val d).map_comap]
  -- Goal: Measure.map radiusSqVec (gaussianFull.restrict (range Subtype.val)) = chiSqRadiusLaw
  have hRange : Set.range (Subtype.val : VecNZ d → Vec d) = {z : Vec d | z ≠ 0} := by
    ext z; simp
  rw [hRange]
  haveI hProb : IsProbabilityMeasure (gaussianFull d).val := (gaussianFull d).property
  have hRestrict : (gaussianFull d).val.restrict {z : Vec d | z ≠ 0} = (gaussianFull d).val := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have h0 : {x : Vec d | ¬ x ∈ {z : Vec d | z ≠ 0}} = {0} := by ext x; simp
    rw [h0]
    exact gaussianFull_singletonZeroMeasure d hDim
  rw [hRestrict]
  exact congrArg Subtype.val (gaussianFull_normSq_chiSq d hDim)

end WristbandLossProofs
