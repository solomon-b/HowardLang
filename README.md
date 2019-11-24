# Howard Lang

A pure interpreted lambda calculus with Algebraic and Recursive Types.

### features:
 - [x] Sum and Product types
 - [x] Recursive Types
 - [x] Ascriptions
 - [x] Let bindings
 - [x] Nat and Bool base types
 - [x] A REPL
 - [ ] Type Aliases
 - [ ] Data Type Binding
 - [ ] Polymorphism (System F)
 - [ ] Type Inference
 - [ ] Type Operators (Omega)
 - [ ] Ocaml style module system

### Example Usage:
#### Base types:
```ml
λ> True
True

λ> :t True
Bool

λ> 1
1

λ> :t 1
Nat

λ> Unit
Unit

λ> :t Unit
Unit
```
#### Sums and Products:
```ml
λ> (1, True, Unit)
(S Z , True , Unit)

λ> :t (1, True, Unit)
(Nat, Bool, Unit)

λ> {foo=True, bar= 7}
{foo=True, bar=7}

λ> :t {foo=True, bar= 7}
{Bool, Nat}

λ> tag Left True as (Left Bool | Right Nat)
Left True

λ> :t tag Left True as (Left Bool | Right Nat)
Left Bool | Right Nat

λ> tag Nothing as (Nothing | Just Nat)
Nothing

λ> :t tag Nothing as (Nothing | Just Nat)
Nothing | Just Nat
```

#### Recursive Types:
```ml
λ> (tag Cons (1, tag Cons (2, tag Cons (3, tag Nil))) as mu.NatList: Nil | Cons (Nat, NatList))
Cons (1, Cons (2, Cons (3, Nil)))

λ> :t (tag Cons (1, tag Cons (2, tag Cons (3, tag Nil))) as mu.NatList: Nil | Cons (Nat, NatList))
Mu. NatList = Unit | (Nat, NatList)

λ> tag Branch (tag Leaf, 0, tag Branch (tag Leaf, 1, tag Leaf)) as mu.NatTree: Leaf | Branch (NatTree, Nat, NatTree)
Branch (Leaf, 0, Branch (Leaf, 1, Leaf))

λ> :t tag Branch (tag Leaf, 0, tag Branch (tag Leaf, 1, tag Leaf)) as mu.NatTree: Leaf | Branch (NatTree, Nat, NatTree)
Mu. NatTree = Unit | (NatTree, Nat, NatTree)
```

#### Functions:
```ml
λ> (\n:Nat.n)
(λ n : Nat. n)

λ> :t (\n:Nat.n)
Nat -> Nat

λ> (\n:Nat.n) 1
S Z

λ> :t (\p:Bool.\n:Nat.n)
Bool -> (Nat -> Nat)

λ> let f (n : Nat) = S n in f
(λ n : Nat. S n)

λ> :t let f (n : Nat) = S n in f
Nat -> Nat

λ> let f (n : Nat) = S n in f 2
S (S (S Z))

λ> let f (n : Nat) (p : Bool) = S n in f
(λ n : Nat. (λ p : Bool. S n))
```

#### Recursive Functions
```ml
λ> let isZero (n : Nat) = case n of Z => True | (S m) => False 
   in let pred (n : Nat) = case n of Z => Z | (S m) => m 
   in letrec isEven(rec : Nat -> Bool) (n : Nat) = if: isZero n then: True else: if: isZero (pred n) then: False else: rec (pred (pred n)) 
   in isEven 4
True
λ> let isZero (n : Nat) = case n of Z => True | (S m) => False 
   in let pred (n : Nat) = case n of Z => Z | (S m) => m 
   in letrec isEven (rec : Nat -> Bool) (n : Nat) = if: isZero n then: True else: if: isZero (pred n) then: False else: rec (pred (pred n)) 
   in isEven 3
False
```

#### Pattern Matching:
```ml
λ> :t (\x:(Nothing | Just Nat).variantCase x of Nothing => 0 | Just=y => y)
Nothing | Just Nat -> Nat

λ> (\x:(Nothing | Just Nat).variantCase x of Nothing => 0 | Just=y => y) (tag Nothing as (Nothing | Just Nat))
0

λ> (\x:(Nothing | Just Nat).variantCase x of Nothing => 0 | Just=y => y) (tag Just 2 as (Nothing | Just Nat))
2
```
