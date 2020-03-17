-- theta.lean

namespace theta --————————————————————————————————————————————————————————————————--
universes 𝒰r 𝒰i

section domain --—————————————————————————————————————————————————————————————————--

/--
`Domain`
The domain of discourse for this document.
-/
structure Domain (R : Type 𝒰r)
    := (zero      : R)
       (diff      : R → R → R)
       (plus      : R → R → R)
       (less_than : R → R → Type 𝒰i)
       (leq       : R → R → Type 𝒰i)
       (abs       : R → R)
       (zleqz     : leq zero zero)
       (plus_mono : Π w x y z, leq w x → leq y z → leq (plus w y) (plus x z))
       (abs_of_pos: Π n, leq zero n → (abs n = n))
       (trans_leq : Π a b c, leq a b -> leq b c -> leq a c) 

variables {R : Type 𝒰r} (𝓡 : Domain R)

-- local notation ℓ `+` r := 𝓡.plus ℓ r
local notation ℓ `-` r := 𝓡.diff ℓ r
local notation ℓ `<` r := 𝓡.less_than ℓ r
local notation ℓ `≤` r := 𝓡.leq ℓ r
local notation `|` p `|` := 𝓡.abs p

definition nonnegative (s : ℕ → R) := Π n, 𝓡.zero ≤ s n


/--
-/
definition Cauchy (s : ℕ → R)
    := Π ε, (𝓡.zero < ε) → Σ N, Π n m, n > N → m > n → | s m - s n | ≤ ε

/--
`ConvergentSequence`
Type of proofs that the given sequence is a convergent sequence.
-/
class ConvergentSequence (s : ℕ → R)
    := (limit       : R)
       (convergence : Π ε, (𝓡.zero < ε) → Σ N, Π n, n > N → | limit - s n | ≤ ε)

/--
-/
definition completeness
    := Π s, Cauchy 𝓡 s → ConvergentSequence 𝓡 s

/--
`Limit`
The limit of a convergent sequence.
-/
definition Limit (s : ℕ → R) [convergent_sequence : ConvergentSequence 𝓡 s]
    := convergent_sequence.limit





/--
`partial_sum`
The next partial sum is the sum of the current term and the current partial sum.
-/
definition partial_sum (s : ℕ → R) : ℕ → R
| (nat.zero  ) := 𝓡.zero
| (nat.succ n) := 𝓡.plus (s n) (partial_sum n)


lemma subtraction (m n : ℕ) (p : m > n) : Σ' k, k + n = m
:=
begin
induction m,
cases p,




end


definition translate (s : ℕ → R) (n : ℕ) : ℕ → R := λ m, s (m + n)

lemma translates (s : ℕ → R) (m n : ℕ) (mn : m > n) : (partial_sum 𝓡 s) m - (partial_sum 𝓡 s) n = (partial_sum 𝓡 (translate s n)) (subtraction m n mn).1
:= begin
induction m,
repeat {rw partial_sum},
repeat {rw partial_sum},
cases mn,
end


definition leq_for_sequences (s1 s2 : ℕ → R) := Π n, s1 n ≤ s2 n

/--
To show a partial sum is monotonic
-/
theorem partial_sum_is_monotonic (s1: ℕ → R) (s2: ℕ → R) (p: leq_for_sequences 𝓡 s1 s2) : 
(leq_for_sequences 𝓡 (partial_sum 𝓡 s1) (partial_sum 𝓡 s2)) :=
begin
intros n,
induction n,
-- case n=0
rw partial_sum,
rw partial_sum,
exact 𝓡.zleqz,
--case n>0
rw partial_sum,
rw partial_sum,
exact 𝓡.plus_mono (s1 n_n) (s2 n_n) (partial_sum 𝓡 s1 n_n) (partial_sum 𝓡 s2 n_n) (p n_n) (n_ih), 
end

theorem translation_monotonic (s1 s2: ℕ → R) (n : ℕ) (p: leq_for_sequences 𝓡 s1 s2) : 
(leq_for_sequences 𝓡 (translate s1 n) (translate s2 n)) :=
begin
induction n,
rw translate,
rw translate,
simp,
exact p,

rw translate,
rw translate,
rw leq_for_sequences,
intros n,
rw nat.add_succ,
exact p (nat.succ(n+n_n)),
end

/--
`ConvergentSequence`
To show that a series converges, we need to show that its sequence of partial sums converges.
-/
class ConvergentSeries (s : ℕ → R) extends ConvergentSequence 𝓡 (partial_sum 𝓡 s)

/--
`Sum`
The sum of a series is the limit of the partial sums.
-/
definition Sum (s : ℕ → R) [convergent_series : ConvergentSeries 𝓡 s]
    := convergent_series.limit


theorem mono_preserves_convergence
    (complete : completeness 𝓡)
    (s1 s2 : ℕ → R) 
    [nonneg : nonnegative 𝓡 s1]
    [pwl : leq_for_sequences 𝓡 s1 s2]
    [cs2 : Cauchy 𝓡 (partial_sum 𝓡 s2)]
: Cauchy 𝓡 (partial_sum 𝓡 s1) := 
begin
rw Cauchy,
intros ε e0,
let N := cs2 ε e0,
let N_1 := N.1,
existsi N_1,
intros n m nN mN,
let N_2 := N.2 n m nN mN,
let tr := translates 𝓡 s1 m n mN,
rw tr,
let mono := partial_sum_is_monotonic 𝓡 (translate s1 n) (translate s2 n) (translation_monotonic 𝓡 s1 s2 n pwl),
let tr2 := translates 𝓡 s2 m n mN,
sorry,

end




end domain --—————————————————————————————————————————————————————————————————————--



section theta_function --—————————————————————————————————————————————————————————--

/--
`ExtendedDomain`
An extension of the domain of discourse to define the theta function.
-/
structure ExtendedDomain (R : Type 𝒰r) extends Domain R
    := (mult : R → R → R)
       (inc  : ℕ → R)
       (exp  : R → R)

variables {R : Type 𝒰r} (𝓡 : ExtendedDomain R)

local notation ℓ `-` r := 𝓡.diff ℓ r
local notation ℓ `⬝` r := 𝓡.mult ℓ r
local notation ℓ `<` r := 𝓡.less_than ℓ r

/--
`theta_sequence`
The underlying sequence for the theta function.
-/
definition theta_sequence (x : R)
    := λ n, 𝓡.exp (𝓡.zero - ((𝓡.inc (n * n)) ⬝ x))



/--
`theta_converges_for_positive_values`
A lemma which proves that the theta function converges for all positive values.
-/
lemma theta_converges_for_positive_values (x : R) (pos : 𝓡.zero < x)
    : ConvergentSeries 𝓡.to_Domain (theta_sequence 𝓡 x)
    := sorry

/--
`theta`
The theta function.
-/
definition theta (x : R) (pos : 𝓡.zero < x)
    := @Sum R 𝓡.to_Domain (theta_sequence 𝓡 x) (theta_converges_for_positive_values 𝓡 x pos)

end theta_function --—————————————————————————————————————————————————————————————--

end theta --——————————————————————————————————————————————————————————————————————--
