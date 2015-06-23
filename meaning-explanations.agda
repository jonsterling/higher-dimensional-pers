{-# OPTIONS --copatterns #-}

module meaning-explanations where

open import pervasives
open import tower
open import terms
open import big-step

noncanonical-tower : tower val → tower exp
points (noncanonical-tower T) M N = Σ val λ M′ → Σ val λ N′ → (M ⇒ M′) × (N ⇒ N′) × points T M′ N′
paths (noncanonical-tower T) α β α-wf β-wf = FIXME
  where
    postulate FIXME : _

record _type (A : exp) : Set₁ where
  field
    {type-val} : val
    type-evals : A ⇒ type-val
    values : tower val

  expressions : tower exp
  expressions = noncanonical-tower values

record _≡_∈_ (M N A : exp) {{A-type : A type}} : Set where
  module A-type = _type A-type
  field
    membership : points A-type.expressions M N

record _∈_ (M A : exp) {{A-type : A type}} : Set where
  module A-type = _type A-type
  field
    membership : points A-type.expressions M M

  value : val
  value with membership
  value | M , _ = M

  wf : points A-type.values value value
  wf with membership
  wf | X , Y , M⇒X , M⇒Y , p rewrite confluence M⇒X M⇒Y = p

