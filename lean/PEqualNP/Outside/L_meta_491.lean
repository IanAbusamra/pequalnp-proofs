import Mathlib

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k → 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  let n := 3 * (E + 1)
  have hv' : v < n := hv
  have hu' : u + 1 ≤ n := by omega
  have hpair : u * n + v < n * n := calc
    u * n + v < (u + 1) * n := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ n * n := Nat.mul_le_mul_right n hu'
  have hindex : 2 * k * (u * n + v) + p < 2 * k * (n * n) := calc
    2 * k * (u * n + v) + p < 2 * k * ((u * n + v) + 1) := by
      rw [Nat.mul_succ]; omega
    _ ≤ 2 * k * (n * n) := Nat.mul_le_mul_left _ hpair
  have eq : 2 * k * (n * n) = 18 * k * (E + 1) ^ 2 := by dsimp [n]; ring
  constructor
  · rw [← eq]
    change n + 2 * k * (u * n + v) + p < n + 2 * k * (n * n)
    omega
  · ring
