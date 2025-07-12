# polymorphic-state-monad

In Haskell, there's so-called `State` monad.

``` haskell
newtype State s a = State { runState :: s -> (s, a) }

instance Functor (State s) where
  fmap f ma = State $ \s0 ->
    let ~(s1, a) = runState ma s0
    in (s1, f a)

pureDefault :: a -> State s a
pureDefault a = State (\s -> (s, a))

joinDefault :: State s (State s a) -> State s a
joinDefault mma = State $ \s0 ->
  let (s1, ma) = runState ma s0
  in runState ma s1 

instance Monad (State s) where
  return :: a -> State s a
  return = pureDefault

  (>>=) :: (a -> State s b) -> State s a -> State s b
  f >>= ma = joinDefault (fmap f ma)
```

This project aims to give a formal proof that
any lawful `Monad` instance with exactly the same type
as this instance
(starts with `instance Monad (State s) where ...` verbatim)
must be equivalent to this standard instance.

In short, **there's only one `State` monad with
∀-ed state type `s`**.

There's [my blog post](https://viercc.github.io/blog/posts/2024-12-10-unique-state-monad.html) (Japanese) too.

# Proof outline:

Utilize [parametricity]() in the Haskell language to reduce
the question about `Monad` to question about plain algebraic data type.

Firstly, from parametricity, `fmap` and `return` is uniquely determined as the above instance. Also from parametricity,
there's isomorphism between `BindTy` (the type of `(>>=)`) and `JoinTy` (the type of `join`).

``` haskell
{- LANGUAGE RankNTypes -}
type BindTy = forall s a b. (a -> State s b) -> State s a -> State s b
type JoinTy = forall s a. State s (State s a) -> State s a
```

Therefore, we only need to care how many `join :: JoinTy`
are there which give rise to lawful `Monad` with the unique
`fmap` and `return`. The `Monad` laws written in terms of `join`
is below.

``` haskell
-- Monad laws
-- Left unit
join . return = id
  :: (forall s a. State s a -> State s a)

-- Right unit
join . fmap return = id
  :: (forall s a. State s a -> State s a)

-- Associativity
join . join = join . fmap join
  :: (forall s a. State s (State s (State s a)) -> State s a)
```

Furthermore, by manipulating isomorphisms, one can show `JoinTy`
can be isomorphically encoded as the 3-tuple `(T,T,T)`
of a plain data type `T` defined below.

``` haskell
data T = F T | G T T | X

run² :: (T,T,T) -> JoinTy
reify² :: JoinTy -> (T,T,T)
```

Similarly, the type of left and right side of the monad laws
can be encoded as plain data type.

``` haskell
type UnitLawTy = forall s a. State s a -> State s a

data Nat = Zero | Suc Nat

run¹ :: (Nat,Nat) -> UnitLawTy
reify¹ :: UnitLawTy -> (Nat,Nat)
```

```
type AssocLawTy = forall s a. State s (State s (State s a)) -> State s a

data S = A S | B S S | C S S S | Leaf

run³ :: (S,S,S,S) -> AssocLawTy
reify³ :: AssocLawTy -> (S,S,S,S)
```

By using these encodings, the problem is now reduced to solving
the equations for `def :: (T,T,T)` and finding that
the unique solution is the encoded version of the usual `State` monad.

``` haskell
-- leftUnitLaw
reify¹ (run² def . return) = reify¹ id
-- rightUnitLaw
reify¹ (run² def . fmap return) = reify¹ id
-- assoc
reify³ (run² def . run² def) = reify³ (run² def . fmap (run² def))
```

# Files:

- `Definitions.agda`

  - Define the above `State` type in Agda,
    `Monad` laws,
    and encodings.
  
  - **Work in progrss** and the correctness of
    the encodings (these `run` and `reify` are inverses each other) is not completed

- `Uniqueness.agda`

  - Solves the equations and confirms the uniquemess of solution.

  - Completed, I think.

- `PolymorphicState.hs`

  - Basically just a note to sketch the proof
    (comments in Japanese)