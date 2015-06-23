module pervasives where

data _≡_ {i} {A : Set i} (M : A) : A → Set i where
  refl : M ≡ M

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

transport : {A : Set} {M N : A} {P : A → Set} (Q : M ≡ N) → P M → P N
transport refl x = x

sym : {A : Set} {M N : A} (Q : M ≡ N) → N ≡ M
sym refl = refl

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

infixr 8 _×_

open Σ public
infixr 7 _,_

data Void : Set where
record Unit : Set where
  constructor tt

