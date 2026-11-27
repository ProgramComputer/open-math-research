import TruncatedRows

namespace OpenMathResearch.LongCycleExcedances.TruncatedRows

/-- Specification of the rounded recurrence. The lag is zero below the cutoff. -/
def lowerRows (b k : ℕ) (hk : 0 < k) (a : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  if n < k then fun _ => 0
  else if n = k then fun i => chop b (a i)
  else fun i => chop b (positiveStep k (n-1) a (lowerRows b k hk a (n-1))
        (lowerRows b k hk a (n-k)) i)
termination_by n
decreasing_by all_goals omega

theorem lowerRows_short {k n : ℕ} (hk : 0 < k) (hs : n < k) (b : ℕ) (a : ℕ → ℕ) (i : ℕ) :
    lowerRows b k hk a n i = 0 := by rw [lowerRows, if_pos hs]

theorem lowerRows_seed {k : ℕ} (hk : 0 < k) (b : ℕ) (a : ℕ → ℕ) (i : ℕ) :
    lowerRows b k hk a k i = chop b (a i) := by
  rw [lowerRows, if_neg (lt_irrefl k), if_pos rfl]

theorem lowerRows_succ {k n : ℕ} (hk : 0 < k) (hs : k ≤ n) (b : ℕ) (a : ℕ → ℕ) (i : ℕ) :
    lowerRows b k hk a (n+1) i = chop b (positiveStep k n a (lowerRows b k hk a n)
      (lowerRows b k hk a (n+1-k)) i) := by
  rw [lowerRows, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]

/-- Encode a significand and a binary shift in one natural suitable for UInt64
transport. Keeping them as unbounded naturals makes the overflow test explicit. -/
def encode (b x : ℕ) : ℕ :=
  let shift := x.log2+1-b
  shift*2^b + x/(2^shift)

def decode (b word : ℕ) : ℕ := word % (2^b) * 2^(word / 2^b)

theorem significand_lt (b x : ℕ) :
    x/(2^(x.log2+1-b)) < 2^b := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  rw [← pow_add]
  rcases x with _ | x
  · positivity
  · refine lt_of_lt_of_le (Nat.lt_log2_self (n:=x+1)) ?_
    apply Nat.pow_le_pow_right (by decide)
    omega

theorem decode_encode (b x : ℕ) :
    decode b (encode b x) = chop b x := by
  have small := significand_lt b x
  let s := x.log2+1-b
  let a := x/2^s
  have ha : a < 2^b := small
  have hq : (s*2^b+a)/2^b = s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]
  have hr : (s*2^b+a)%2^b = a := by simp [Nat.add_mod, Nat.mod_eq_of_lt ha]
  change (s*2^b+a)%2^b * 2^((s*2^b+a)/2^b) = a*2^s
  rw [hr,hq]

theorem encode_fits {x : ℕ} (h : x.log2+1-48 < 2^16) : encode 48 x < 2^64 := by
  have hs := significand_lt 48 x
  unfold encode
  dsimp only
  omega

/-- The actual archive needs far fewer than the 16 available shift bits. -/
theorem word_fits_envelope {n i x : ℕ} (hn : n ≤ 1001) (hi : i < 60)
    (bound : x ≤ (i+1)^n) : encode 48 x < 2^64 := by
  have h64 : i+1 ≤ 2^6 := by omega
  have hu : x ≤ 2^(6*n) := by
    rw [pow_mul]
    exact bound.trans (Nat.pow_le_pow_left h64 _)
  apply encode_fits
  by_cases hz : x = 0
  · simp [hz]
  · have hl := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((Nat.log2_self_le hz).trans hu)
    omega

#print axioms word_fits_envelope
#print axioms lowerRows_succ
#print axioms decode_encode
#print axioms encode_fits
end OpenMathResearch.LongCycleExcedances.TruncatedRows
