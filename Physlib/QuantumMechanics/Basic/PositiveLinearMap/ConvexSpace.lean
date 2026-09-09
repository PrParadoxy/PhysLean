import Physlib.QuantumMechanics.Basic.PositiveLinearMap.Unital

open Convexity

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [AddCommMonoid E₂]
  [PartialOrder E₁] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]
  [IsOrderedAddMonoid E₂]
  [SMulCommClass R R E₂] [PartialOrder R]
  [IsStrictOrderedRing R] [PosSMulMono R E₂]

instance : ConvexSpace R (E₁ →ₚ[R] E₂) where
  sConvexComb w := PositiveLinearMap.mk (w.weights.sum fun m r ↦ r • m.toLinearMap) <| by
    refine monotone_iff_forall_lt.mpr fun a b h ↦ ?_
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.finsupp_sum_apply,
      LinearMap.smul_apply, PositiveLinearMap.coe_toLinearMap]
    exact Finsupp.sum_le_sum fun f hf ↦
      smul_le_smul_of_nonneg_left (f.monotone h.le) (w.nonneg f)
  sConvexComb_single := by simp
  assoc _ := by
    simp [Finsupp.sum_mapDomain_index, add_smul, Finsupp.sum_sum_index,
    Finsupp.sum_smul_index, mul_smul, Finsupp.smul_sum]

-- Mathlib worthy?
lemma Finsupp.sum_smul_const
    {R E α : Type*}
    [Semiring R] [AddCommMonoid E] [Module R E]
    (f : α →₀ R) (e : E) :
    f.sum (fun _ d => d • e) = (f.sum fun _ d => d) • e := by
  simpa using
    (map_finsuppSum
      (LinearMap.smulRight (LinearMap.id (R := R)) e) f (fun _ d => d)).symm

noncomputable instance [One E₁] [One E₂] : ConvexSpace R (E₁ →ₚ₁[R] E₂) where
  sConvexComb w := UnitalPositiveLinearMap.mk
    (sConvexComb (w.map (fun f ↦ f.toPositiveLinearMap))) <| by
    simp [sConvexComb, Finsupp.sum_mapDomain_index, add_smul, Finsupp.sum_smul_const]
  sConvexComb_single := by simp
  assoc _ := by
    simp [sConvexComb, Finsupp.sum_mapDomain_index, add_smul,
      Finsupp.sum_sum_index, Finsupp.smul_sum, Finsupp.sum_smul_index', smul_smul]
