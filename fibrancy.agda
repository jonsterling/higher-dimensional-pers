{-# OPTIONS --copatterns #-}

module fibrancy where

data _≡_ {i} {A : Set i} (M : A) : A → Set i where
  refl : M ≡ M

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

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

mutual
  data val : Set where
    unit void : val
    <> : val
    ze : val
    su : exp → val
    idpath : val
    Paths : exp → exp → exp → val
    Interval I0 I1 seg : val

  data exp : Set where
    `_ : val → exp
    sympath : exp → exp
    _,_ : exp → exp → exp

data _⇒_ : exp → val → Set where
  val⇒ : ∀ {M} → ` M ⇒ M
  sym-id : sympath (` idpath) ⇒ idpath
  seqpath-id : ∀ {α β} → α ⇒ β → (α , ` idpath) ⇒ β
  id-seqpath : ∀ {α β} → α ⇒ β → (` idpath , α) ⇒ β

confluence : ∀ {E M N} → E ⇒ M → E ⇒ N → M ≡ N
confluence val⇒ val⇒ = refl
confluence sym-id sym-id = refl
confluence (seqpath-id D) (seqpath-id E) = confluence D E
confluence (seqpath-id D) (id-seqpath E) = confluence D E
confluence (id-seqpath D) (seqpath-id E) = confluence D E
confluence (id-seqpath D) (id-seqpath E) = confluence D E

record tower (E : Set) : Set₁ where
  coinductive
  field
    points : E → E → Set
    paths : (M N : E) .(M-wf : points M M) .(N-wf : points N N) → tower E
open tower

trivial-tower : tower val
points trivial-tower M N = Unit
paths trivial-tower M N _ _ = trivial-tower

empty-tower : tower val
points empty-tower _ _ = Void
paths empty-tower M N () _

Paths-tower : (A : tower val) → (M N : val) .(M-wf : points A M M) .(N-wf : points A N N) → tower val
points (Paths-tower A M N M-wf N-wf) idpath idpath = points A M N
points (Paths-tower A M N M-wf N-wf) α β = points (paths A M N M-wf N-wf) α β
paths (Paths-tower A M N M-wf N-wf) α β α-wf β-wf = {!!} -- Paths-tower (paths A M N M-wf N-wf) α β α-wf β-wf

enriched-tower : tower val → tower exp
points (enriched-tower T) M N = Σ val λ M′ → Σ val λ N′ → (M ⇒ M′) × (N ⇒ N′) × points T M′ N′
paths (enriched-tower T) α β α-wf β-wf = {!!}

record _type (A : exp) : Set₁ where
  field
    {type-val} : val
    type-evals : A ⇒ type-val
    canonical-type : tower val

record _≡_∈_ (M N A : exp) {{A-type : A type}} : Set where
  module A-type = _type A-type
  field
    membership : points (enriched-tower A-type.canonical-type) M N

record _∈_ (M A : exp) {{A-type : A type}} : Set where
  module A-type = _type A-type
  field
    membership : points (enriched-tower A-type.canonical-type) M M

  value : val
  value with membership
  value | M , _ = M

  wf : points A-type.canonical-type value value
  wf with membership
  wf | X , Y , M⇒X , M⇒Y , p rewrite confluence M⇒X M⇒Y = p

instance
  unit-type : (` unit) type
  unit-type = record { type-evals = val⇒ ; canonical-type = unit-tower }
    where
      unit-tower : tower val
      points unit-tower <> <> = Unit
      points unit-tower M N = Void
      paths unit-tower _ _ _ _ = empty-tower

instance
  interval-type : (` Interval) type
  interval-type = record { type-evals = val⇒ ; canonical-type = Interval-tower }
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
  paths-type {A} {M} {N} {{A-type}} {{M∈A}} {{N∈A}} =
    record
      { type-evals = val⇒
      ; canonical-type = Paths-tower A-type.canonical-type M∈A.value N∈A.value M∈A.wf N∈A.wf
      }

    where
      module A-type = _type A-type
      module M∈A = _∈_ M∈A
      module N∈A = _∈_ N∈A

  <>-∈-unit : ` <> ∈ ` unit
  <>-∈-unit = record { membership = <> , <> , val⇒ , val⇒ , tt }

idpath-∈-paths[unit,<>,<>] : ` idpath ∈ (` Paths (` unit) (` <>) (` <>))
idpath-∈-paths[unit,<>,<>] = record { membership = idpath , (idpath , (val⇒ , (val⇒ , tt))) }

instance
  welp : (` Paths (` Interval) (` I0) (` I1)) type
  welp = paths-type {{interval-type}} {{record { membership = I0 , I0 , (val⇒ , (val⇒ , tt)) }}} {{record { membership = I1 , (I1 , (val⇒ , (val⇒ , tt))) }}}

seg-∈-paths[I,0,1] : ` seg ∈ (` Paths (` Interval) (` I0) (` I1))
seg-∈-paths[I,0,1] = record { membership = seg , (seg , (val⇒ , (val⇒ , tt))) }

