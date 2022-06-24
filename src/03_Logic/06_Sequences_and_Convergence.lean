import data.real.basic
import algebra

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
by { ext, ring }

example (a b : ℝ) : abs a = abs (a - b + b) :=
by  { congr, ring }

example {a : ℝ} (h : 1 < a) : a < a * a :=
begin
  convert (mul_lt_mul_right _).2 h,
  { rw [one_mul] },
  exact lt_trans zero_lt_one h
end

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, dsimp,
  rw [sub_self, abs_zero],
  apply εpos
end

theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε εpos, dsimp,
  have ε2pos : 0 < ε / 2,
  { linarith },
  cases cs (ε / 2) ε2pos with Ns hs,
  cases ct (ε / 2) ε2pos with Nt ht,
  use max Ns Nt,
  intros n' hnge,
  have hn'geNs: n' >= Ns := by finish,
  have hs' := hs n' hn'geNs,
  have hn'geNt: n' >= Nt := by finish,
  have ht' := ht n' hn'geNt,
  have hsum:  |s n' + t n' - (a +b)| <= |s n' - a| + |t n' - b| := by
    begin
       convert abs_add (s n' - a) (t n' - b),
       linarith,

    end,
  calc |s n' + t n' - (a + b)| <= |s n' - a| + |t n' - b| : by apply hsum
  ... < ε /2 + ε / 2 : by 
    begin
      apply add_lt_add hs' ht',
    end
  ... = ε : by norm_num,
end

lemma lt_mul_pos {a b c: ℝ} : (0 < c) -> (b < a) -> b * c < a * c :=
begin
  intros hc1 blta,
  nlinarith,
end

theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos.mpr h,
  intros ε εpos,
  have εcpos: 0 < ε/(abs c) := 
    begin
      have hε: 0 < 1 / abs c := by apply one_div_pos.mpr acpos,
      have : 0 < ε * (1 / abs c) := by apply mul_pos εpos hε,
      calc 0 < ε * (1 / abs c) : this
      ... = ε / abs c : by ring
    end,
  dsimp,
  cases cs (ε/abs c) εcpos with Ns hs,
  use Ns,
  intros n' hn'geNs,
  have hs' : |s n' - a| < ε/abs c := hs n' hn'geNs,
  have : |s n' - a| * abs c < (ε/abs c) * (abs c) := by apply lt_mul_pos (acpos) hs',
  simp [*] at this,
  rw [←abs_mul, mul_comm, mul_sub] at this,
  apply this,
end

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n' hNlen,
  have : |s n' - a| < 1 := h n' hNlen,
  have : |s n' - a| + |a| < 1 + |a| := by apply add_lt_add_right this,
  have := calc 
    1 + |a| > |s n' - a| + |a| : this
        ... >=  |s n' - a + a| : by apply abs_add 
        ... = |s n'| : by norm_num,
  finish,
end

lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
begin
  intros ε εpos, dsimp,
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
  have Bpos : 0 < B,
    from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
  have pos₀ : ε / B > 0,
    from div_pos εpos Bpos,
  cases ct _ pos₀ with N₁ h₁,
  let Nₘ := max N₀ N₁,
  use Nₘ,
  intros n' hNn',
  simp,
  simp at h₁,
  have nm0 : n' >= N₀ := by finish,
  have nm1 : n' >= N₁ := by finish,
  have hct := h₁ n' nm1,
  have hlecs: |s n'| <= B := by apply le_of_lt (h₀ n' nm0),
  have hltct: |t n'| < ε / B := h₁ n' nm1,
  have := mul_lt_mul' (hlecs) hltct (abs_nonneg _) Bpos,
  have εsimp: B * (ε / B) = ε := begin 
      rw [← mul_div_assoc B ε B],
        have Bneq0 : B ≠ 0 := by nlinarith,
      calc 
        B * ε / B = ε * B / B : by ring
              ... = ε : by rw mul_div_cancel ε Bneq0,
  end,
  rw [←abs_mul, εsimp] at this,
  exact this,
end

theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
  { apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring },
  convert (converges_to_add h₁ (converges_to_mul_const b cs)),
  { ext, ring },
  ring
end

theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
begin
  by_contradiction abne,
  have : abs (a - b) > 0,
  { sorry },
  let ε := abs (a - b) / 2,
  have εpos : ε > 0,
  { change abs (a - b) / 2 > 0, linarith },
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (s N - a) < ε,
  { sorry },
  have absb : abs (s N - b) < ε,
  { sorry },
  have : abs (a - b) < abs (a - b),
  { sorry },
  exact lt_irrefl _ this
end

section
variables {α : Type*} [linear_order α]

def converges_to' (s : α → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

end

