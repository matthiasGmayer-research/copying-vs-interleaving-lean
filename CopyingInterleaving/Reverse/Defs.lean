import CopyingInterleaving.Setting

namespace CopyingInterleaving.Reverse

/-- The binary word `x_m` of the manuscript's section "PROVED: an explicit binary construction":
for `B = 2^m` it has length `n = m·B` and `x_m[jB+i] = bit_j(i)` for `0 ≤ j < m`, `0 ≤ i < B`,
with bit `0` the least significant bit (`false` = 0, `true` = 1).
Position `k` is read as `j = k / B`, `i = k % B`. No deviation. -/
def xm (m : ℕ) : List Bool :=
  (List.range (m * 2 ^ m)).map fun k => (k % 2 ^ m).testBit (k / 2 ^ m)

end CopyingInterleaving.Reverse
