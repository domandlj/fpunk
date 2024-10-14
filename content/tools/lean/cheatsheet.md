---
title: "Lean cheat sheet2"
date: 2024-10-12
draft: false
---
# Mathlib4 & Lean4 Cheatsheet.



# 1. Members of `Prop`
## Tactis for rules of inference

| Symbol | In Goal                                   | In Hypothesis                                      |
|--------|-------------------------------------------|---------------------------------------------------|
| ∃      | `use expr`                                | `obtain ⟨new_name, new_name⟩ := expr`              |
| ∀      | `intro new_name`                          | `specialize name expr`                             |
| ¬      | `intro`                             | `apply expr`                                      |
| →      | `apply expr`                              | `specialize name expr`                             |
| ↔      | `constructor`                             | `rw [expr]` or `rw [⟨expr⟩]`                      |
| ∧      | `constructor`                             | `obtain ⟨new_name, new_name⟩ := expr`              |
| ∨      | `left` or `right`                         | `cases expr with \| inl new_name => ...\| inr new_name =>` |




### Truth values (True, False)

```
inductive True : Prop where
  | intro

inductive False : Prop
```

### Or (${\vee}$)
```lean
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
```
```lean
example {P Q : Prop}  : (P → ¬ P) ∨ (P ∧ Q → Q) :=
  Or.inr (And.right)
```
* **Hypothesis:** `cases ...`
* **Goals:** `left`, `right`

```lean
example {P Q : Prop}  : (P → ¬ P) ∨ (P ∧ Q → Q) := by
  right
  intro ⟨_, q⟩
  exact q
```

### And ($\wedge$)

```lean
structure And (a b : Prop) : Prop where
  intro ::
    left : a
    right : b

-- And.intro : a → b → a ∧ b
```
**Inhabitant**
```lean
example {P Q : Prop} : (P → P) ∧ (P ∧ Q → Q) :=
  ⟨ λ x => x  , And.right⟩
```
* **Hypothesis:** `obtain ⟨p , q⟩ := h`
* **Goals:** `constructor`

```lean
example {P Q : Prop} : (P → P) ∧ (P ∧ Q → Q) := by
  constructor
  intro p
  exact p

  intro pq
  obtain ⟨p , q⟩ := pq
  exact q
```


### Implies ($\rightarrow$)

```lean
example {P: Prop}  : P → P := λ x ↦ x
```
* **Goal**: `intro`
```lean
example {P: Prop}  : P → P := by
  intro p
  exact p
```

### Iff ($\iff$)

```lean
structure Iff (a b : Prop) : Prop where
  intro ::
    mp : a → b
    mpr : b → a
```

```lean
example {P: Prop}  : P ↔ P :=
  let id := λ p ↦ p
  Iff.intro id id
```

```lean
example {P: Prop}  : P ↔ P := by
  constructor
  repeat (intro p; exact p)
```

### Neg ($\neg$)
Note that $\neg P := P \rightarrow \bot $

```lean
def Not (a : Prop) : Prop := a → False
```

```lean
example : ¬ (1 = 2) := by
  intro one_eq_two
  contradiction
```




### Forall ($\forall$)
`built-in`
```lean
example : ∀ (n : ℕ) , n < n + 1 := Nat.lt_succ_self
```
* **Hypothesis**: `apply h`
* **Goals**: `intro`
```lean
example : ∀ (n : ℕ) , n < n + 1 := by
  intros n
  apply Nat.lt_succ_self
```
### Exists ($\exists$)


```lean
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
```

```lean
example : ∃ (n : ℕ) , n < n + 1 :=
  let witness := 1
  let proof := Nat.lt_succ_self witness
  -- lt_succ_self (n : ℕ) : n < n+1

  Exists.intro witness proof
```
* **Hypothesis**: `obtain ⟨witness, proof⟩ := h`
* **Goals**: `use witness`, `exists`

```lean
example : ∃ (n : ℕ) , n < n + 1 := by
  use 1
  decide
```

### Equality type $(=$)

```lean
inductive Eq {α : Type} (a : α) : α → Prop where
  | refl : Eq a a
```
```lean
example {α} : ∀ x:α, x = x := refl
```

* **Hypothesis**: `rw [(←)h]`
* **Goals**: `rw [(←)h]`, `rfl`

```lean
example {α} : ∀ x:α, x = x := by
  intro
  rfl
```

# 2. Members of `Type`

### Product type (×)
```lean
structure Prod (α : Type u) (β : Type v) where
  mk ::

  fst : α
  snd : β
```
**Inhabitants**
```lean
example : ℕ × Bool := (1, true)
```

### Sum type (⊕)
```lean
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
```

**Inhabitants**
```lean
example : ℕ ⊕ Bool := inr 1
```

### Pi type ($\Pi$)
`built-in`
**Inhabitants**

```lean
example : Π (x : ℕ) , EqT x x := λ x  => refl
```

### Sigma type ($\Sigma$)

```lean
structure Sigma {α : Type u} (β : α → Type v) where
  mk ::

  fst : α
  snd : β fst
```

**Inhabitants**
```lean
example : Σ (x : ℕ) , EqT x x :=
  ⟨1, refl⟩ --notation for mk 1 refl
```
### Unit and Empty types
```lean
abbrev Unit : Type := PUnit

-- PUnit is universe polymorphc
inductive PUnit : Sort u where
  | unit : PUnit
```

```lean
inductive Empty : Sort u where
```

### Equality type
Isn't in the stdlib, but is analog to the `Prop` version.

```lean
inductive EqT {α : Type} (a : α) : α → Type where
  | refl : EqT a a
```
## 3. Predicates
Predicates are modelled as being of the type
```lean
α → Prop
```
For example,
```lean
def notZero (n Nat) : Prop :=
  match n with
  | zero => False
  | _ => True
```
For example quantifiers are also predicates,
```lean
#check Exists
-- Exists.{u} {α : Sort u} (p : α → Prop) : Prop
```

## 4. Relations
In mathematics binary relations over two sets are defined as $R \subseteq \alpha \times \beta$. Note that the charcateristic function of the set $R$ would be $\_ \in \_ : \alpha\times \beta  \rightarrow Prop $ which is isomorphic to $\alpha \rightarrow \beta  \rightarrow Prop $. Following this idea we define in Lean (or in type theory) a binary realtion over two types as being of the type:

```
α → β → Prop
```

Relations can be defined in differnt ways, such as being inductivily over the types.
## 5. Sets
A set over a a unvirse is modelled as the predicate of it's characteristic function.

```lean
def Set α := α → Prop

-- α would is the universe
```
For example the set $\{10,5,4\}$ can be defines as

```lean
example : Set ℕ := λ n =>
    match n with
    | 10 => True
    | 5 => True
    | 4 => True
    | _ => False
```
Or using sintactic sugar
```lean
example : Set ℕ := {10, 4 , 5}
```



### Membership
$x \in X$ is just sugar for $X \ x$

The realtion of membership ( $\_ \in \_ : \alpha \rightarrow Set \ \alpha \rightarrow Prop $) is defined as

```lean
def Mem (s : Set α) (x : α) : Prop :=
  s x
```




## 6. Natural numbers (ℕ)

### Construction
```lean
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat
```



## Operations

**Add `+`**
```lean
def add (n m : ℕ ) : ℕ :=
  match m with
  | zero   => n
  | succ k => succ (add n k)
```

**Mul `*`**

```lean
def mul (n m : ℕ ) : ℕ :=
  match m with
  | zero   => zero
  | succ k => add (mul n k) n
```

**Sub `-`**

```lean
def pred (n: ℕ ) : ℕ :=
  match n with
  | zero   => zero
  | succ m => m

def sub (n m : ℕ ) : ℕ :=
  match m with
  | zero => n
  | succ k => pred (sub n k)
```

**Pow `^`**

```lean
def pow (m : ℕ) : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (pow m n) * m
```
**Properties**

| Name        | Property                       |
|-------------|--------------------------------|
| `add_zero`  | `n + 0 = n`                    |
| `mul_one`   | `n * 1 = n`                    |
| `refl`      | `n * 0 = 0`                    |
| `add_comm`  | `n + m = m + n`                |
| `mul_comm`  | `n * m = m * n`                |
| `add_assoc` | `(n + m) + k = n + (m + k)`    |
| `mul_assoc` | `(n * m) * k = n * (m * k)`    |
| `mul_add`   | `n * (m + k) = n * m + n * k`  |
| `add_mul`   | `(n + m) * k = n * k + m * k`  |
| `mul_sub`   | `n * (m - k) = n * m - n * k`  |
| `sub_mul`   | `(n - m) * k = n * k - m * k`  |

### Order relation (≤)

```lean
inductive le (n :  ℕ) : Nat → Prop
  | refl     : le n n                          -- n ≤ n
  | step {m} : le n m → le n (succ m)          -- n ≤ m → n ≤ m + 1
```




### Order relation (<)
```lean
def lt (n m : ℕ) : Prop := n + 1 ≤ m
```



| Name                       | Property                                            |
|----------------------------|----------------------------------------------------|
| `not_succ_le_zero`          | `¬  n + 1 ≤ 0 `                                   |
| `not_lt_zero`               | `¬  n < 0`                                   |
| `zero_le`                   | `0 ≤ n`                                           |
| `succ_le_succ`              | `n ≤ m`  ⊢ `(n + 1) ≤ (m + 1)`                       |
| `zero_lt_succ`              | `0 < (n + 1)`                                     |
| `le_step`                   | `n ≤ m` ⊢ `n ≤ (m + 1)`                             |
| `le_trans`                  | `n ≤ m` , `m ≤ k` ⊢ `n ≤ k`                           |
| `lt_trans`                  | `n < m `, `m < k` ⊢ `n < k`                          |
| `le_succ`                   | `n ≤ n + 1`                                       |
| `le_succ_of_le`             | `n ≤ m` ⊢ `n ≤ (m + 1)`                             |
| `le_refl`                   | `n ≤ n`                                           |
| `succ_pos`                  | `0 < (n + 1)`                                     |

### Div operation (/)
```lean
def div (x y : ℕ) : ℕ :=
  if 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
```

| Name                     | Property                                                               |
|--------------------------|-----------------------------------------------------------------------|
| `div_le_self`           | `n / k ≤ n`                                                          |
| `div_lt_self`           | `0 < n, 1 < k ⊢ n / k < n`                                          |
| `div_eq`                | `x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0`             |


### Modulo operation (%)




| Name                     | Property                                                |
|--------------------------|--------------------------------------------------------|
| `modCore`               | `x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x`                 |
| `mod_eq_sub_mod`        | `a ≥ b ⊢ a % b = (a - b) % b`                          |
| `mod_eq`                | `x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x`   |
| `mod_zero`              | `a % 0 = a`                                           |
| `mod_eq_of_lt`          | `a < b ⊢ a % b = a`                                  |
| `mod_lt`                | `y > 0 ⊢ x % y < y`                                  |
| `mod_le`                | `x % y ≤ x`                                          |
| `zero_mod`              | `0 % b = 0`                                          |
| `mod_self`              | `n % n = 0`                                          |
| `mod_one`               | `x % 1 = 0`                                          |
| `div_add_mod`           | `n * (m / n) + m % n = m`                            |
| `div_eq_sub_div`        | `0 < b, b ≤ a ⊢ a / b = (a - b) / b + 1`            |
| `mod_add_div`           | `m % k + k * (m / k) = m`                            |
| `mod_def`               | `m % k = m - k * (m / k)`                           |
| `div_one`               | `n / 1 = n`                                          |
| `div_zero`              | `n / 0 = 0`                                          |
| `zero_div`              | `0 / b = 0`                                          |
| `le_div_iff_mul_le`     | `x ≤ y / k ↔ x * k ≤ y`                             |
| `div_div_eq_div_mul`    | `m / n / k = m / (n * k)`                           |
| `div_mul_le_self`       | `m / n * n ≤ m`                                     |
| `div_lt_iff_lt_mul`     | `x / k < y ↔ x < y * k`                             |
| `add_div_right`         | `(x + z) / z = (x / z) + 1`                         |
| `add_div_left`          | `(z + x) / z = (x / z) + 1`                         |
| `add_mul_div_left`      | `(x + y * z) / y = x / y + z`                       |
| `add_mul_div_right`     | `(x + y * z) / z = x / z + y`                       |
| `add_mod_right`         | `(x + z) % z = x % z`                               |
| `add_mod_left`          | `(x + z) % x = z % x`                               |
| `add_mul_mod_self_left` | `(x + y * z) % y = x % y`                           |
| `add_mul_mod_self_right`| `(x + y * z) % z = x % z`                           |
| `mul_mod_right`         | `(m * n) % m = 0`                                   |
| `mul_mod_left`          | `(m * n) % n = 0`                                   |
| `div_eq_of_lt_le`       | `k * n ≤ m, m < (k + 1) * n ⊢ m / n = k`            |
| `sub_mul_div`           | `n * p ≤ x ⊢ (x - n * p) / n = x / n - p`           |
| `mul_sub_div`           | `x < n * p ⊢ (n * p - (x + 1)) / n = p - ((x / n) + 1)` |
| `mul_mod_mul_left`      | `(z * x) % (z * y) = z * (x % y)`                   |
| `div_eq_of_lt`          | `a < b ⊢ a / b = 0`                                 |

### Relation divs (|)
```lean
def dvd (d n: ℕ) : Prop := ∃ k , n = d * k
```


```lean
example : ∀ n, n ∣ 2*n := by
  intro n
  use 2
  apply Nat.mul_comm 2 n
```
**Properties of |**
| Name                           | Property                                                |
|---------------------------------|---------------------------------------------------------|
| `dvd_refl`                      | `a` ⊢ `a ∣ a`                                           |
| `dvd_zero`                      | `a` ⊢ `a ∣ 0`                                           |
| `dvd_mul_left`                  | `a`, `b` ⊢ `a ∣ b * a`                                  |
| `dvd_mul_right`                 | `a`, `b` ⊢ `a ∣ a * b`                                  |
| `dvd_trans`                     | `a ∣ b`, `b ∣ c` ⊢ `a ∣ c`                              |
| `eq_zero_of_zero_dvd`           | `0 ∣ a` ⊢ `a = 0`                                       |
| `zero_dvd`                      | `0 ∣ n` ⊢ `n = 0`                                       |
| `dvd_add`                       | `a ∣ b`, `a ∣ c` ⊢ `a ∣ b + c`                          |
| `dvd_add_iff_right`             | `k ∣ m` ⊢ `k ∣ n ↔ k ∣ m + n`                           |
| `dvd_add_iff_left`              | `k ∣ n` ⊢ `k ∣ m ↔ k ∣ m + n`                           |
| `dvd_mod_iff`                   | `k ∣ n` ⊢ `k ∣ m % n ↔ k ∣ m`                           |
| `le_of_dvd`                     | `m ∣ n`, `0 < n` ⊢ `m ≤ n`                              |
| `dvd_antisymm`                  | `m ∣ n`, `n ∣ m` ⊢ `m = n`                              |
| `pos_of_dvd_of_pos`             | `m ∣ n`, `0 < n` ⊢ `0 < m`                              |
| `one_dvd`                       | `1 ∣ n`                                                 |
| `eq_one_of_dvd_one`             | `n ∣ 1` ⊢ `n = 1`                                       |
| `mod_eq_zero_of_dvd`            | `m ∣ n` ⊢ `n % m = 0`                                   |
| `dvd_of_mod_eq_zero`            | `n % m = 0` ⊢ `m ∣ n`                                   |
| `dvd_iff_mod_eq_zero`           | `m ∣ n ↔ n % m = 0`                                     |
| `emod_pos_of_not_dvd`           | `¬ a ∣ b` ⊢ `0 < b % a`                                 |
| `mul_div_cancel'`               | `n ∣ m` ⊢ `n * (m / n) = m`                             |
| `div_mul_cancel`                | `n ∣ m` ⊢ `m / n * n = m`                               |
| `mod_mod_of_dvd`                | `c ∣ b` ⊢ `a % b % c = a % c`                           |
| `dvd_of_mul_dvd_mul_left`       | `k * m ∣ k * n`, `0 < k` ⊢ `m ∣ n`                      |
| `dvd_of_mul_dvd_mul_right`      | `m * k ∣ n * k`, `0 < k` ⊢ `m ∣ n`                      |
| `dvd_sub`                       | `k ∣ m`, `k ∣ n`, `n ≤ m` ⊢ `k ∣ m - n`                 |
| `mul_dvd_mul`                   | `a ∣ b`, `c ∣ d` ⊢ `a * c ∣ b * d`                      |
| `mul_dvd_mul_left`              | `b ∣ c` ⊢ `a * b ∣ a * c`                               |
| `mul_dvd_mul_right`             | `a ∣ b` ⊢ `a * c ∣ b * c`                               |
| `dvd_one`                       | `n ∣ 1 ↔ n = 1`                                         |
| `mul_div_assoc`                 | `k ∣ n` ⊢ `m * n / k = m * (n / k)`                     |

### Gdc (`gcd`)

```lean
def gcd (m n : ℕ) : ℕ :=
  if m = 0 then
    n
  else
    gcd (n % m) m
```

### Lcm (`lcm`)

```lean
def lcm (m n : Nat) : Nat := m * n / gcd m n
```

### Coprimes relation
```lean
def Coprime (m n : Nat) : Prop := gcd m n = 1
```

### Prime number
The number $p$ is a prime number, that is, a natural number that is
at least 2 whose only divisors are $p$ and $1$. Is constructed as
```lean
def Prime (p : ℕ) :=
  Irreducible p

structure Irreducible [Monoid α] (p : α) : Prop where
  not_unit : ¬IsUnit p
  isUnit_or_isUnit' : ∀ a b, p = a * b → IsUnit a ∨ IsUnit b
```
This is a more general definition, but can be characterized by:


|Name |Property|
|---------|---------|
|`eq_one_or_self_of_dvd`| `Prime p`, `m ∣ p` ⊢  `m = 1 ∨ m = p` |
|`prime_def_lt`  | `Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1`|

Some useful properties


|Name |Property|
|---------|---------|
|`dvd_of_dvd_pow`| `Prime p`, `p ∣ m ^ n` ⊢  `p ∣ m ` |



## Type classes (and structures)

### Algebraic structures
| Structure (1 set, 1 op)                | Associativity | Id Element | Inverse Element | Commutative |
|-----------------------------------------|---------------|------------|------------------|-------------|
| Magma                                   | no            | no         | no               | no          |
| Semi Group                              | yes           | no         | no               | no          |
| Monoid                                  | yes           | yes        | no               | no          |
| Group                                   | yes           | yes        | yes              | no          |
| Commutative Group (abelian)            | yes           | yes        | yes              | yes         |



| Structure                               | Associativity ( + , * ) | Id Element ( + , * ) | Inverse Element ( + , * ) | Commutative ( + , * ) | Dist ( * , + ) |
|-----------------------------------------|--------------------------|----------------------|---------------------------|-----------------------|-----------------|
| Semiring ( + abelian monoid, * monoid) | yes, yes                 | yes, yes             | yes, no                  | yes, no               | yes             |
| Ring ( + abelian group, * monoid)      | yes, yes                 | yes, yes             | yes, no                  | yes, no               | yes             |


```lean
/-- A `Group` is a `Monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.

Use `Group.ofLeftAxioms` or `Group.ofRightAxioms` to define a group structure
on a type with the minimum proof obligations.
-/
class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
```

```lean
/-- A `Ring` is a `Semiring` with negation making it an additive group. -/
class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

/-- A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is
commutative and associative, multiplication is associative and left and right distributive over
addition, and `0` and `1` are additive and multiplicative identities. -/
class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

```

#### Order strucures
| Structure          | Reflexive | Symmetric | Antisymmetric | Transitive | Totality |
|--------------------|-----------|-----------|---------------|------------|----------|
| Equivalence Relation| Yes       | Yes       | No            | Yes        | No       |
| Poset               | Yes       | No        | Yes           | Yes        | No       |
| Complete Order      | Yes       | No        | Yes           | Yes        | Yes      |
