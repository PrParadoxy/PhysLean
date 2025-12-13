import Mathlib.Geometry.Manifold.Algebra.LieGroup
import PhysLean.Relativity.MinkowskiMatrix

open minkowskiMatrix
open Matrix

variable (d)

def LorentzGroup : Subgroup (GL (Fin 1 ⊕ Fin d) ℝ) where
  carrier := {Λ | (dual Λ.val) * Λ = 1}
  one_mem' := by simp
  mul_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_mul, dual_mul]
    grind
  inv_mem' := by
    intro a h
    apply Matrix.inv_inj
    . replace h := congr_arg (· * a.val⁻¹) h
      simp only [mul_inv_cancel_right_of_invertible, one_mul] at h
      simp only [coe_units_inv, Matrix.mul_inv_rev, inv_inv_of_invertible, inv_one]
      rw [←h, dual_dual]
      simp
    . simp [Matrix.GeneralLinearGroup.det_ne_zero a]

#synth (TopologicalSpace (LorentzGroup d))
#synth (IsTopologicalGroup (LorentzGroup d))
#synth (∀ (a : LorentzGroup d), Invertible a.val.val)
#synth (Group (LorentzGroup d))
