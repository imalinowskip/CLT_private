import Clt.CLT
import Clt.CramerWold

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

noncomputable
abbrev stdGaussian_Multivariate (n : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
  {
    val := Measure.pi (fun _ : Fin n => (stdGaussian : Measure ℝ))
    property := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => (stdGaussian : Measure ℝ))))
  }

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ+} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

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

theorem central_limit_multivariate
  (hX : ∀ n, Measurable (X n))
  {P : ProbabilityMeasure Ω}
  (h0 : P[X 0] = 0)
  (h1 : ∀ i j, P[(fun ω ↦ (X 0 ω i) * (X 0 ω j))] = if i = j then 1 else 0)
  (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P)
 : Tendsto (fun n : ℕ => P.map (aemeasurable_invSqrtMulSum_Multivariate n hX))
    atTop (𝓝 (stdGaussian_Multivariate d)) := by sorry

  /-let μ  := stdGaussian_Multivariate d
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

  -- step 3: build the projection hypothesis
  let hAe_id := @aemeasurable_id (EuclideanSpace ℝ (Fin d)) _ μ
  have hAe_sum (n : ℕ) : AEMeasurable (invSqrtMulSum_Multivariate X n) (P : Measure Ω) :=
    aemeasurable_invSqrtMulSum_Multivariate n hX

  let hMeas_sum : ∀ n, Measurable (invSqrtMulSum_Multivariate X n) :=
    fun n => measurable_invSqrtMulSum_Multivariate n hX
  let hAe_sum   : ∀ n, AEMeasurable (invSqrtMulSum_Multivariate X n) P :=
    fun n => aemeasurable_invSqrtMulSum_Multivariate _ hX

  have h_proj : ∀ t, Tendsto
      (fun n => P.map (aemeasurable_dotProduct (hMeas_sum n) t))
      atTop
      (𝓝 ((stdGaussian_Multivariate d).map (aemeasurable_dotProduct measurable_id t)))
    := sorry

  apply cramerWold (measurable_id) (fun n => (h_meas_sum n).measurable) h_proj-/


#min_imports
