{-# OPTIONS --copatterns #-}

module types where

open import pervasives
open import terms
open import big-step
open import tower
open import meaning-explanations

trivial-tower : tower val
points trivial-tower M N = Unit
paths trivial-tower M N _ _ = trivial-tower

empty-tower : tower val
points empty-tower _ _ = Void
paths empty-tower M N () _

instance
  unit-type : (` unit) type
  unit-type = record { type-evals = val⇒ ; values = unit-tower }
    where
      unit-tower : tower val
      points unit-tower <> <> = Unit
      points unit-tower M N = Void
      paths unit-tower _ _ _ _ = empty-tower

instance
  interval-type : (` Interval) type
  interval-type = record { type-evals = val⇒ ; values = Interval-tower }
    where
      Interval-tower : tower val
      points Interval-tower I0 I0 = Unit
      points Interval-tower I1 I1 = Unit
      points Interval-tower _ _ = Void
      paths Interval-tower I0 I1 _ _ = seg-tower
        where
          seg-tower : tower val
          points seg-tower seg seg = Unit
          points seg-tower _ _ = Void
          paths seg-tower _ _ _ _ = trivial-tower
      paths Interval-tower _ _ _ _ = empty-tower


instance
  paths-type : ∀ {A M N} {{A-type : A type}} {{_ : _∈_ M A {{A-type}}}} {{_ : _∈_ N A {{A-type}}}} → (` Paths A M N) type
  paths-type {A} {M} {N} {{A-type}} {{M∈A}} {{N∈A}} = record { type-evals = val⇒ ; values = Paths-tower}

    where
      module A-type = _type A-type
      module M∈A = _∈_ M∈A
      module N∈A = _∈_ N∈A

      Paths-tower : tower val
      points Paths-tower idpath idpath = points A-type.values M∈A.value N∈A.value
      points Paths-tower α β = points (paths A-type.values M∈A.value N∈A.value M∈A.wf N∈A.wf) α β
      paths Paths-tower α β α-wf β-wf = FIXME -- Paths-tower (paths A M N M-wf N-wf) α β α-wf β-wf
        where postulate FIXME : _


  <>-∈-unit : ` <> ∈ ` unit
  <>-∈-unit = record { membership = <> , <> , val⇒ , val⇒ , tt }

idpath-∈-paths[unit,<>,<>] : ` idpath ∈ (` Paths (` unit) (` <>) (` <>))
idpath-∈-paths[unit,<>,<>] = record { membership = idpath , (idpath , (val⇒ , (val⇒ , tt))) }

instance
  welp : (` Paths (` Interval) (` I0) (` I1)) type
  welp = paths-type {{interval-type}} {{record { membership = I0 , I0 , (val⇒ , (val⇒ , tt)) }}} {{record { membership = I1 , (I1 , (val⇒ , (val⇒ , tt))) }}}

seg-∈-paths[I,0,1] : ` seg ∈ (` Paths (` Interval) (` I0) (` I1))
seg-∈-paths[I,0,1] = record { membership = seg , (seg , (val⇒ , (val⇒ , tt))) }

