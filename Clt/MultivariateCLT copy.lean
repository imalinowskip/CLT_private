import Clt.CLT
import Clt.CramerWold2

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex RealInnerProductSpace
open scoped Topology

noncomputable
abbrev stdGaussian_Multivariate (n : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
  {
    val := Measure.pi (fun _ : Fin n => (stdGaussian : Measure ℝ))
    property := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => (stdGaussian : Measure ℝ))))
  }

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {tΩ : TopologicalSpace Ω} {d : ℕ+} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

abbrev invSqrtMulSum_Multivariate {Ω} (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  (√n)⁻¹ • ∑ i : Fin n, X i ω

lemma map_invSqrtMulSum_Multivariate (μ : Measure Ω) {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)} (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    μ.map (invSqrtMulSum_Multivariate X n)
      = ((μ.map (fun ω (i : Fin n) ↦ X i ω)).map (fun x ↦ ∑ i, x i)).map ((√n)⁻¹ • ·) := by
  rw [Measure.map_map, Measure.map_map]
  · rfl
  all_goals { fun_prop }

lemma measurable_invSqrtMulSum_Multivariate (n) (hX : ∀ n, Measurable (X n)) :
    Measurable (invSqrtMulSum_Multivariate X n) := by fun_prop

lemma aemeasurable_invSqrtMulSum_Multivariate {μ : Measure Ω} (n) (hX : ∀ n, Measurable (X n)) :
    AEMeasurable (invSqrtMulSum_Multivariate X n) μ := by fun_prop

--instance : inner (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) := inferInstance

theorem central_limit_multivariate
  (hX : ∀ n, Measurable (X n))
  {P : ProbabilityMeasure Ω}
  (h0 : P[X 0] = 0)
  (h1 : ∀ i j, P[(fun ω ↦ (X 0 ω i) * (X 0 ω j))] = if i = j then 1 else 0)
  (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P)
 : Tendsto (fun n : ℕ => P.map (aemeasurable_invSqrtMulSum_Multivariate n hX))
    atTop (𝓝 (stdGaussian_Multivariate d)) := by
  let μ  := stdGaussian_Multivariate d
  let μn := fun n => P.map (aemeasurable_invSqrtMulSum_Multivariate n hX)

  -- step 1: take care of the map_id trick you already have
  have hf : AEMeasurable (id : EuclideanSpace ℝ (Fin d) → _) (μ : Measure _) := aemeasurable_id
  have map_id : μ.map hf = μ := by
    apply ProbabilityMeasure.ext_of_charFun
    dsimp [stdGaussian_Multivariate, ProbabilityMeasure.map]
    simpa using @Measure.map_id _ _ (id : EuclideanSpace ℝ (Fin d) → _) (μ : Measure _)

  -- step 2: rewrite the goal to use μn and μ
  change Tendsto μn atTop (𝓝 μ)
  rw [← map_id]
  apply cramerWold

  · intro t
    let c := ‖t‖
    let t' := c⁻¹ • t
    let Y : ℕ → Ω → ℝ := fun i ω => inner (X i ω) (t')

    have hY_meas : ∀ i, Measurable (Y i) := by
      intro i
      exact measurable_dotProduct' (hX i) t'

    -- g : EuclideanSpace ℝ (Fin d) → ℝ
    let g := fun x => ⟪x, t'⟫

    -- g is measurable since inner is continuous
    have hg : Measurable g := Measurable.inner measurable_id measurable_const

    -- independence of the Yᵢ follows by composing Xᵢ with g
    have hindep_Y : iIndepFun Y P := hindep.comp (fun _ => g) (fun _ => hg)

    -- 3. identical distribution
    have hident_Y : ∀ i, IdentDistrib (Y i) (Y 0) P P := by
      intro i; sorry

    -- 4. mean zero
    have h0_Y : P[Y 0] = 0 := by
      dsimp [Y]; sorry

    -- 5. unit variance
    have h1_Y : P[(Y 0) ^ 2] = 1 := by
      dsimp [Y]; sorry

    -- now apply the univariate CLT
    have h_clt : Tendsto (fun n => P.map (aemeasurable_invSqrtMulSum n hY_meas))
                          atTop (𝓝 stdGaussian) :=
      central_limit hY_meas h0_Y h1_Y hindep_Y hident_Y

    -- 6. check that projecting invSqrtMulSum_Multivariate along t
    have proj_sum : ∀ n ω, ⟪invSqrtMulSum_Multivariate X n ω, t⟫ = c * invSqrtMulSum Y n ω := by
      intro n ω
      calc
        ⟪invSqrtMulSum_Multivariate X n ω, t⟫
            = ⟪(√n)⁻¹ • ∑ i : Fin n, X i ω, t⟫              := rfl
        _   = (√n)⁻¹ * ⟪∑ i : Fin n, X i ω, t⟫              := by
          rw [inner_smul_left]
          simp
        _   = (√n)⁻¹ * ∑ i : Fin n, ⟪X i ω, t⟫              := by
          rw [sum_inner (Finset.univ : Finset (Fin n)) (fun i => X i ω) t]
        _   = (√n)⁻¹ * ∑ i : Fin n, (c * ⟪X i ω, t'⟫)         := by
          simp only [t', inner_smul_right]
          simp only [←mul_assoc]
          have : Invertible c := sorry
          simp [mul_inv_cancel_of_invertible]
        /-_   = c * invSqrtMulSum Y n ω              := by dsimp [invSqrtMulSum, Y]; ring-/

    /-intro t

    let Y : ℕ → Ω → ℝ := fun i ω => inner t (X i ω)
    have hY_meas : ∀ i, Measurable (Y i) := by
      intro i
      apply Measurable.inner measurable_const _
      exact hX i

    -- show that projecting the multivariate normalized sum is the same as the normalized sum of Y
    have proj_sum : ∀ n ω, inner t (invSqrtMulSum_Multivariate X n ω)
        = invSqrtMulSum (Y) n ω := by
      intro n ω
      calc
        inner t (invSqrtMulSum_Multivariate X n ω)
            = inner t ((√n)⁻¹ • ∑ i : Fin n, X i ω) := rfl
        _   = (√n)⁻¹ * inner t (∑ i : Fin n, X i ω)   := inner_smul_right _ _ _
        _   = (√n)⁻¹ * ∑ i : Fin n, inner t (X i ω)   := by
                rw [inner_sum (Finset.univ : Finset (Fin n)) (fun i => X i ω) t]
        _   = invSqrtMulSum Y n ω            := by dsimp [invSqrtMulSum, Y]

    /- 3) Mean zero of Y₀ -/
    have hY0 : P[Y 0] = 0 := by
      sorry

    /- 4) Variance of Y₀ is ∥t∥² -/
    have hY2 : P[(fun ω => (Y 0 ω)^2)] = ‖t‖^2 := by
      sorry

    /- 5) Define the normalized scalars Zᵢ = Yᵢ / ‖t‖ -/
    let Z : ℕ → Ω → ℝ := fun i ω => Y i ω / ‖t‖

    /- 6) Measurability of Zᵢ -/
    have hZ_meas : ∀ i, Measurable (Z i) := by
      sorry

    /- 7) Mean zero of Z₀ -/
    have hZ0 : P[Z 0] = 0 := by
      sorry

    /- 8) Variance of Z₀ is 1 -/
    have hZ2 : P[(fun ω => (Z 0 ω)^2)] = 1 := by
      sorry

    /- 9) Independence / IdentDist for Z -/
    have hindepZ : iIndepFun Z P := by
      sorry
    have hidentZ : ∀ i, IdentDistrib (Z i) (Z 0) P P := by
      sorry

    /- 10) Apply the 1-d CLT to Z -/
    have scalar_clt :
      Tendsto (fun n => P.map (aemeasurable_invSqrtMulSum n hZ_meas))
        atTop (𝓝 stdGaussian) := by
      exact central_limit hZ_meas hZ0 hZ2 hindepZ hidentZ

    /- 11) Relate P.map (aemeasurable_invSqrtMulSum Z) to P.map (aemeasurable_invSqrtMulSum Y) -/
    have mDiv : Measurable (fun x => x / ‖t‖) :=
      Measurable.div_const measurable_id ‖t‖
    have map_Z :
      ∀ n, P.map (aemeasurable_invSqrtMulSum n hZ_meas)
        = (P.map (aemeasurable_invSqrtMulSum n hY_meas)).map mDiv.aemeasurable := by
      sorry

    /- 12) Undo normalization, get CLT for Y -/
    have clt_Y : Tendsto
        (fun n => (P.map (aemeasurable_invSqrtMulSum n hY_meas)).map mDiv.aemeasurable)
        atTop (𝓝 stdGaussian) := by
      sorry

    /- 13) Multiply back by ‖t‖ to get projection of multivariate sum -/
    have clt_proj :
      Tendsto (fun n => (P.map (aemeasurable_invSqrtMulSum n hY_meas)).map mDiv.aemeasurable)
        atTop (𝓝 (stdGaussian.map mDiv.aemeasurable)) := by
      sorry-/

  · exact measurable_id
  · let h_invSqrtMulSum : ∀ (n : ℕ), Measurable (invSqrtMulSum_Multivariate X n) := by
      intros n
      apply measurable_invSqrtMulSum_Multivariate
      exact hX
    exact h_invSqrtMulSum

#min_imports
