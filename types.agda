{-# OPTIONS --copatterns #-}

module types where

open import pervasives
open import terms
open import big-step
open import infinity-per
open import meaning-explanations

data unit-tower-points : val → val → Set where
  <> : unit-tower-points <> <>

data unit-tower-paths : val → val → Set where
  idpath : unit-tower-paths idpath idpath

instance
  -- The judgement «unit type» is made evident by exhibiting its (mostly trivial) ∞-per:
  unit-type : (` unit) type
  unit-type = record { type-evals = val⇒ ; values = unit-tower }
    where
      unit-paths-tower : ∞-per val
      points unit-paths-tower = unit-tower-paths
      points-sym unit-paths-tower idpath = idpath
      points-trans unit-paths-tower idpath idpath = idpath
      paths unit-paths-tower _ _ _ _ = unit-paths-tower

      unit-tower : ∞-per val
      points unit-tower = unit-tower-points
      points-sym unit-tower <> = <>
      points-trans unit-tower <> <> = <>
      paths unit-tower M N M-wf N-wf = unit-paths-tower

instance
  -- The judgement «paths A M N type (A type, M ∈ A, N ∈ A)» is evident, since the path space of a type is given by pushing taking the tail of its ∞-per.
  paths-type : ∀ {A M N} {{A-type : A type}} {{M∈A : _∈_ M A {{A-type}}}} {{N∈A : _∈_ N A {{A-type}}}} → (` Paths A M N) type
  paths-type {A} {M} {N} {{A-type}} {{M∈A}} {{N∈A}} = record { type-evals = val⇒ ; values = paths A-type.values M∈A.membership.val1 N∈A.membership.val1 M∈A.membership.wf-val1 N∈A.membership.wf-val1}
    where
      module A-type = _type A-type
      module M∈A = _∈_ M∈A
      module N∈A = _∈_ N∈A


-- some examples
instance
  <>-∈-unit : ` <> ∈ ` unit
  <>-∈-unit = record { membership = record {} }
  paths-unit-<>-<> = ` Paths (` unit) (` <>) (` <>)

  idpath-∈-paths[unit,<>,<>] : ` idpath ∈ paths-unit-<>-<>
  idpath-∈-paths[unit,<>,<>] = record { membership = record {} }

  ex2 : ` idpath ∈ ` Paths paths-unit-<>-<> (` idpath) (` idpath)
  ex2 = record { membership = record {} }
