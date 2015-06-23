module big-step where

open import terms
open import pervasives

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

