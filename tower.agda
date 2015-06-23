module tower where

record tower (E : Set) : Set₁ where
  coinductive
  field
    points : E → E → Set
    points-sym : ∀ {M N} → points M N → points N M
    points-trans : ∀ {M N O} → points M N → points N O → points M O
    paths : (M N : E) (M-wf : points M M) (N-wf : points N N) → tower E
open tower public

