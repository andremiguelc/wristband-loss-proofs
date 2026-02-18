import WristbandLossProofs.CoreEngine.Geometry

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory

/-- A concrete CDF-on-`NNReal` associated to a measure `μ` on `NNReal`. -/
noncomputable def cdfNNReal (μ : Distribution NNReal) (x : NNReal) : ℝ :=
  (μ (Set.Iic x)).toReal

/-- `F` is the CDF of `μ` and is continuous. -/
def IsContinuousCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ Continuous (fun x => (F x : ℝ))

/-- `F` is the CDF of `μ` and is strictly increasing. -/
def IsStrictlyIncreasingCDFFor (μ : Distribution NNReal) (F : NNReal → UnitInterval) : Prop :=
  (∀ x, (F x : ℝ) = cdfNNReal μ x) ∧ StrictMono (fun x => (F x : ℝ))

end WristbandLossProofs
