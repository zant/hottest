
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module worksheet1 where

open import prelude hiding (not-is-involution)

_&&'_ : Bool → Bool → Bool
true &&' true = true
true &&' false = false
false &&' true = false
false &&' false = false


_xor_ : Bool → Bool → Bool
true xor true = false
true xor false = true
false xor true = true
false xor false = false


_^_ : ℕ → ℕ → ℕ
n ^ zero = suc zero
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example = refl 81

_! : ℕ → ℕ 
zero ! = suc zero
suc n ! = suc n * (n !)

!-example : 4 ! ≡ 24
!-example = refl 24

max : ℕ → ℕ → ℕ 
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

min : ℕ → ℕ → ℕ 
min zero m = zero
min (suc n) zero = zero
min (suc n) (suc m) = suc (min n m)

min-example : min 5 3 ≡ 3
min-example = refl 3

-- fmap : a → b → f a → f b
map : {X Y : Type} → (X → Y) → List X → List Y
map f [] = []
map f (x :: xs) = f x :: map f xs


map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl _



