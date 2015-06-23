{-# OPTIONS --copatterns #-}

module types where

open import pervasives
open import terms
open import big-step
open import infinity-per
open import meaning-explanations

trivial-tower : ∞-per val
points trivial-tower M N = Unit
points-sym trivial-tower _ = tt
points-trans trivial-tower _ _ = tt
paths trivial-tower M N _ _ = trivial-tower

empty-tower : ∞-per val
points empty-tower _ _ = Void
points-sym empty-tower ()
points-trans empty-tower () _
paths empty-tower M N () _

data idpath-tower-points : val → val → Set where
  idpath : idpath-tower-points idpath idpath

idpath-tower : ∞-per val
points idpath-tower = idpath-tower-points
points-sym idpath-tower idpath = idpath
points-trans idpath-tower idpath idpath = idpath
paths idpath-tower M N M-wf N-wf = idpath-tower

data unit-tower-points : val → val → Set where
  <> : unit-tower-points <> <>

instance
  unit-type : (` unit) type
  unit-type = record { type-evals = val⇒ ; values = unit-tower }
    where
      unit-tower : ∞-per val
      points unit-tower = unit-tower-points
      points-sym unit-tower <> = <>
      points-trans unit-tower <> <> = <>
      paths unit-tower M N M-wf N-wf = idpath-tower

instance
  paths-type : ∀ {A M N} {{A-type : A type}} {{M∈A : _∈_ M A {{A-type}}}} {{N∈A : _∈_ N A {{A-type}}}} → (` Paths A M N) type
  paths-type {A} {M} {N} {{A-type}} {{M∈A}} {{N∈A}} = record { type-evals = val⇒ ; values = paths A-type.values M∈A.membership.val1 N∈A.membership.val1 M∈A.membership.wf-val1 N∈A.membership.wf-val1}
    where
      module A-type = _type A-type
      module M∈A = _∈_ M∈A
      module N∈A = _∈_ N∈A

instance
  <>-∈-unit : ` <> ∈ ` unit
  <>-∈-unit = record { membership = record {} }
  paths-unit-<>-<> = ` Paths (` unit) (` <>) (` <>)

  idpath-∈-paths[unit,<>,<>] : ` idpath ∈ paths-unit-<>-<>
  idpath-∈-paths[unit,<>,<>] = record { membership = record {} }

  ex2 : ` idpath ∈ ` Paths paths-unit-<>-<> (` idpath) (` idpath)
  ex2 = record { membership = record {} }
