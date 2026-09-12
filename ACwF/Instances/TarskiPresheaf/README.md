Let C a category.

# Π-types

Let Γ a context, A : Ty Γ, B : Ty (Γ ▹ A). The standard Kripke definition of Π A
B is

```agda
(Π A B) (I, ρ) = { w : (J : C) (f : J → I) (a : A (J , Γ f ρ)) → B (I , (Γ f ρ , a))
                 | (J K : C) (f : J → I) (g : K → J) (a : A (J , Γ f ρ)) → B g (w f a) ≡ w (f ⋆ g) (A g a)
                 }
```

There are a few different ways to formalize this in Agda.

## Straightforward way

We can literally define it as above. Unfortunately, this poses a problem:
naturality mentions the action of A and B on morphisms. These must be morphisms
not in C, but in ∫Γ. So, to express naturality, we must pick a choice of a proof
of equality. While these are equalities in a set, we still end up forced to
correct these witnesses everywhere in the proofs. In conclusion, this definition
is correct, but would probably require a lot of effort.

## Using ∫Γ directly

We could try to make this generic in the ∫Γ witness, defining Π A B as so:

``` agda
(Π A B) (x : ∫ Γ) = { w : (y : ∫Γ) (f : ∫Γ[x, y]) (a : A y) → B (fst y, (snd y, a))
                    | (y z : ∫Γ) (m : ∫Γ[x, y]) (n : ∫Γ[y, z]) (a : A y) 
                      → B n (w m a) ≡ w (m ⋆ n) (A n a)
                    }
```

This makes showing functoriality very easy. Unfortunately, this definition is
incorrect. Making Γ appear in the definition causes naturality (ΠTyNat) to fail.

## Using slices of the index category

The idea is to decouple the shape of elements of Π A B from Γ, A and B
themselves, by noticing that what matters for Π is slices of C. We can define Π
for functors defined on slice categories, then create these functors from A and
B.

Concretely, we define 

``` agda
indexed-Πdata : {Γ : Ctx} (I : C) (P : Presheaf (Fib I)) (Q : Functor (∫ P) Universe) → Type _
indexed-Πdata I P Q = (s : Fib I) (a : P s) → Q (s, a)
indexed-Πnat : {Γ : Ctx} (I : C) (P : Presheaf (Fib I)) (Q : Functor (∫ P) Universe) → indexed-Πdata → Type _
indexed-Πnat I P Q w = (s t : Fib I) (m : (Fib I)[t, s]) (a : P ob s) → Q m (w s a) ≡  w t (P m a)
indexed-Π = Σ indexed-Πdata indexed-Πnat

Πtype : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ▹ A)) → ∫U Γ .ob → Type _
Πtype {Γ} A B Iρ = indexed-Π {Γ} (Iρ .fst) (A ∘ (κ Γ) ∘ (ι Iρ)) (B ∘ (κ▹ Γ A) ∘ (∫ι Iρ (A ∘ κ Γ)))
```

where Fib I is the slice category over I, and κ, ι, and their extended variants
(κ▹ and ∫ι) are functors that pick a certain slice category. Unfolding the
definitions, we get back the standard Kripke definition.

Restriction (for functoriality) is just precomposition by slice reindexing, but
we do need to transport over associativity. However, the machinery to build this
is reused for naturality. The witness correction problem we had in the first
approach is solved in one place by the Fib/Idx machinery.
