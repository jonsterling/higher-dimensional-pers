{-# OPTIONS --copatterns #-}

module types where

open import pervasives
open import terms
open import big-step
open import tower
open import meaning-explanations

trivial-tower : tower val
points trivial-tower M N = Unit
points-sym trivial-tower _ = tt
points-trans trivial-tower _ _ = tt
paths trivial-tower M N _ _ = trivial-tower

empty-tower : tower val
points empty-tower _ _ = Void
points-sym empty-tower ()
points-trans empty-tower () _
paths empty-tower M N () _

data idpath-tower-points : val → val → Set where
  idpath : idpath-tower-points idpath idpath

idpath-tower : tower val
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
      unit-tower : tower val
      points unit-tower = unit-tower-points
      points-sym unit-tower <> = <>
      points-trans unit-tower <> <> = <>
      paths unit-tower M N M-wf N-wf = idpath-tower

instance
  paths-type : ∀ {A M N} {{A-type : A type}} {{M∈A : _∈_ M A {{A-type}}}} {{N∈A : _∈_ N A {{A-type}}}} → (` Paths A M N) type
  paths-type {A} {M} {N} {{A-type}} {{M∈A}} {{N∈A}} = record { type-evals = val⇒ ; values = Paths-tower A-type.values M∈A.membership.wf-val1 N∈A.membership.wf-val1}
    where
      module A-type = _type A-type
      module M∈A = _∈_ M∈A
      module N∈A = _∈_ N∈A

      Paths-tower : {M N : val} (A : tower val) → points A M M → points A N N → tower val
      points (Paths-tower {M} {N} A M∈A N∈A) α β = points (paths A M N M∈A N∈A) α β
      points-sym (Paths-tower {M} {N} A M∈A N∈A) = points-sym (paths A M N M∈A N∈A)
      points-trans (Paths-tower {M} {N} A M∈A N∈A) = points-trans (paths A M N M∈A N∈A)
      paths (Paths-tower A M∈A N∈A) α β α-wf β-wf = Paths-tower (paths A _ _ M∈A N∈A) α-wf β-wf

instance
  <>-∈-unit : ` <> ∈ ` unit
  <>-∈-unit = record { membership = record {} }
  paths-unit-<>-<> = ` Paths (` unit) (` <>) (` <>)

  idpath-∈-paths[unit,<>,<>] : ` idpath ∈ paths-unit-<>-<>
  idpath-∈-paths[unit,<>,<>] = record { membership = record {} }

  ex2 : ` idpath ∈ ` Paths paths-unit-<>-<> (` idpath) (` idpath)
  ex2 = record { membership = record {} }
