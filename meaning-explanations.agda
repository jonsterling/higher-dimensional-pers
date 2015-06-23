{-# OPTIONS --copatterns #-}

module meaning-explanations where

open import pervasives
open import infinity-per
open import terms
open import big-step

record is-point (T : ∞-per val) (M N : exp) : Set where
  field
    {val1} : val
    {val2} : val
    {{eval1}} : M ⇒ val1
    {{eval2}} : N ⇒ val2
    {{wf}} : points T val1 val2

  wf-val1 : points T val1 val1
  wf-val1 = points-trans T wf (points-sym T wf)

  wf-val2 : points T val2 val2
  wf-val2 = points-trans T (points-sym T wf) wf

is-point-sym : {T : ∞-per val} {M N : exp} → is-point T M N → is-point T N M
is-point-sym {T = T} X =
  record { eval1 = eval2 ; eval2 = eval1 ; wf = points-sym T wf }
  where
    open is-point X

is-point-trans : {T : ∞-per val} {M N O : exp} → is-point T M N → is-point T N O → is-point T M O
is-point-trans {T = T} X Y =
  record { eval1 = X.eval1 ; eval2 = Y.eval2 ; wf = points-trans T X.wf (transport (sym (confluence X.eval2 Y.eval1)) Y.wf) }
  where
    module X = is-point X
    module Y = is-point Y


noncanonical-tower : ∞-per val → ∞-per exp
points (noncanonical-tower T) = is-point T
points-sym (noncanonical-tower T) = is-point-sym
points-trans (noncanonical-tower T) = is-point-trans
paths (noncanonical-tower T) α β P Q =
  noncanonical-tower (paths T P.val1 Q.val2 P.wf-val1 Q.wf-val2)
  where
    module P = is-point P ; module Q = is-point Q

record _type (A : exp) : Set₁ where
  field
    {type-val} : val
    type-evals : A ⇒ type-val
    values : ∞-per val

  expressions : ∞-per exp
  expressions = noncanonical-tower values

record _≡_∈_ (M N A : exp) {{A-type : A type}} : Set where
  module A-type = _type A-type
  field
    membership : points A-type.expressions M N

record _∈_ (M A : exp) {{A-type : A type}} : Set where
  module A-type = _type A-type
  field
    membership : points A-type.expressions M M

  module membership = is-point membership
