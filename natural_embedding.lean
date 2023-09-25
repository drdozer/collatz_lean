import Mathlib.Tactic

/--!
A natural embedding of some type α into β.

The intuition is that if one type is embedded into another, that typeclasses defined for both types
should behave consistently between the two. This means that the `embed` operation should distribute over
the typeclass operations. More concretely, for a unary operation:

```
forwards: (f a).embed  → f a.embed
backwards: b.embedded → f b → f (embed⁻¹ b)
```

and for some binary operation,

```
forwards: (f a1 a2).embed  → f (a1.embed a2.embed)
backwards: b1.embedded ∧ b2.embed → f b1 b2 → f (embed⁻¹ b1) (embed⁻¹ b2)
```

and soforth.

-/
class NaturalEmbedding (α β : Type*) where
    -- The embedding from α into β
    embed : α → β   

    -- Identify all β that are the result of an (unknown) embedded α
    embedded : β -> Prop

    embedding_of (b : β) : (embedded b) -> α
    -- Given a β that is an embedded value, recover the α that was embedded
    lawful (a : α): embedded (embed a)

    -- We require that `embedding_of ∘ embed` is the identity 
    left_inverse (a : α) : embedding_of (embed a) (lawful a) = a

    -- We require that `embed ∘ embedding_of` is the identity 
    right_inverse (b : β) (eb: embedded b): embed (embedding_of b eb) = b

namespace NaturalEmbedding

class NE_LT (α β : Type*) [ne : NaturalEmbedding α β] [ltα : LT α] [ltβ : LT β] where
    embeds_lt(a1 a2: α) : ltα.lt a1 a2 = ltβ.lt (ne.embed a1) (ne.embed a2)

class NE_Zero (α β : Type*) [ne : NaturalEmbedding α β] [zα : Zero α] [zβ : Zero β] where
    embeds_zero : ne.embed zα.zero = zβ.zero

class NE_Add (α β : Type*) [ne : NaturalEmbedding α β] [addα : Add α] [addβ : Add β] where
    embeds_add(a1 a2: α) : ne.embed (addα.add a1 a2) = addβ.add (ne.embed a1) (ne.embed a2)


instance : NaturalEmbedding ℕ ℤ where
    embed := Int.ofNat
    -- fixme: not sure this is the ideal predicate, as it carries a nat rather than looking at the Int itself
    embedded := Int.NonNeg
    embedding_of (b : ℤ) := λ _ ↦ Int.toNat b
    lawful (a : ℕ) := by use a
    left_inverse (a: ℕ) := by rfl
    right_inverse (b : ℤ) := by
        simp only
        rintro ⟨ a ⟩
        simp only [Int.toNat]
        
        

instance : NE_LT ℕ ℤ where
    embeds_lt(a1 a2: ℕ) := by simp [embed]

instance : NE_Zero ℕ ℤ where
    embeds_zero := by simp only [embed]

instance : NE_Add ℕ ℤ where
    embeds_add := by
        intros a1 a2
        simp only [embed]
        rfl



end NaturalEmbedding
