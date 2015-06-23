module tower where

record tower (E : Set) : Set₁ where
  coinductive
  field
    points : E → E → Set
    paths : (M N : E) (M-wf : points M M) (N-wf : points N N) → tower E
open tower public

