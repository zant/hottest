open import introduction
is-even : ℕ → Type
is-even zero = 𝟙
is-even (suc zero) = 𝟘
is-even (suc (suc x)) = is-even x

record Σ {A : Type} (B : A → Type) : Type where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁

-- product is a special case where B is not dependent on A
_×_ : Type → Type → Type
A × B = Σ {A} (λ _ → B)

Σ-elim : {A : Type} {B : A → Type} {C : (Σ B) → Type}
      → ((x : A) → (y : B x) → C (x , y))
      → ((z : Σ B) → C z)
Σ-elim f (x , y) = f x y

2-is-even : is-even 2
2-is-even = ⋆
exists-an-even-number : Σ is-even
exists-an-even-number = (2 , ⋆)