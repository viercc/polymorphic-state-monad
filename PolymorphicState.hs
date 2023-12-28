{-# LANGUAGE RankNTypes #-}
module PolymorphicState where
import Control.Monad (ap)

{-

-- https://twitter.com/Kory__3/status/1737757423673413635

> forall s, a. Monad (a =>> s -> (s, a)) の値って一意なのでしょうか

-}

type State s a = s -> (s, a)
data StateMonad s = SM
  {
    pureState :: forall a. a -> State s a,
    joinState :: forall a. State s (State s a) -> State s a
  }

fmapState :: (a -> b) -> State s a -> State s b
fmapState f sa s = f <$> sa s

-- Q. Monad則を満たす (sm :: forall s. StateMonad s) はいくつある？

-- `s` について量化された pureState はユニーク

type PureStateTy = forall s a. a -> State s a
thePureState :: PureStateTy
thePureState a s = (s, a)

-- `s` について量化された joinState はユニークではないが、
-- 適当なそれはMonad則を満たさないかもしれない

type JoinStateTy = forall s a. State s (State s a) -> State s a
joinStateUsual :: JoinStateTy
joinStateUsual ssa s0 =
  let (s1, sa) = ssa s0
  in sa s1

joinStateStranger :: JoinStateTy
joinStateStranger ssa s0 =
  let (s1, _) = ssa s0
      (s2, _) = ssa s1
      (s3, sa) = ssa s2
      (_,  a) = sa s3
  in (s1, a)

-- JoinStateTyは、以下のように型の計算をしていけば、ある再帰的なデータ型と同型になる。

{-

JoinStateTy
 ~ forall s a. (s -> (s, s -> (s, a))) -> (s -> (s, a))
        -- (A -> (B,C)) ~ (A -> B, A -> C)
 ~ forall s a. (s -> s, s -> s -> s, s -> s -> a) -> (s -> s, s -> a)
        --     ^^^^^^^^^^^^^^^^^^^^
        -- ここを F(s) とおく
 ~ forall s a. ((F s, s -> s -> a) -> s -> s, (F s, s -> s -> a) -> s -> a)
        -- forall a. (E1(a), E2(a)) ~ (forall a. E1(a), forall a. E2(a))
 ~ forall s. (forall a. (F s, s -> s -> a) -> s -> s,
              forall a. (F s, s -> s -> a) -> s -> a)
        -- タプルの1番目のforall a. でくくられた a は、negativeな位置にしか
        -- 登場しないので、 () に置き換えられる。
        -- すると、
        {
            forall a. (F s, s -> s -> a) -> s -> s
          ~ (F s, s -> s -> ()) -> s -> s
          ~ F s -> s -> s
        }
        -- なので

 ~ forall s. (F s -> s -> s,
              forall a. (F s, s -> s -> a) -> s -> a)
        -- タプルの2番目に注目する。
        {
          forall a. (F s, s -> s -> a) -> s -> a)
            -- カリー化とアンカリー化
          ~ forall a. F s -> ((s, s) -> a) -> s -> a
            -- forall と -> はスコープの問題がなければ交換する
          ~ F s -> forall a. ((s, s) -> a) -> s -> a
            -- 米田の補題
          ~ F s -> s -> (s, s)
          ~ (F s -> s -> s, F s -> s -> s)
        }
        -- なので
  ~ forall s. (F s -> s -> s, (F s -> s -> s, F s -> s -> s))
    -- ここで forall s. (F s -> s -> s) = T とおけば
  ~ (T, (T, T))

また、

T = forall s. (F s -> s -> s)
  = forall s. (s -> s, s -> s -> s) -> s -> s
  ~ forall s. (s -> s) -> (s -> s -> s) -> s -> s

は、Boehm-Berarducciエンコーディングより次のデータ型に同型になっている。
-}

data T = F T | G T T | X
  deriving (Show, Eq)

foldT :: (s -> s) -> (s -> s -> s) -> s -> T -> s
foldT f g x = go
  where
    go (F t) = f (go t)
    go (G t1 t2) = g (go t1) (go t2)
    go X = x

-- 同型により、*任意の* JoinStateTy は、Tの３つ組である。

type JoinStateTy' = (T, T, T)

joinFromT :: (T, T, T) -> JoinStateTy
joinFromT (t, l, r) ssa s = (foldT f g s t, ret (foldT f g s l) (foldT f g s r))
  where
    f s1 = fst (ssa s1)
    g s1 s2 = fst (snd (ssa s1) s2)
    ret s1 s2 = snd (snd (ssa s1) s2)

joinToT :: JoinStateTy -> (T, T, T)
joinToT join = case join (\t -> (F t, \t' -> (G t t', (t, t')))) X of
  (t, (ta1, ta2)) -> (t, ta1, ta2)

usualDef :: (T, T, T)
usualDef = joinToT joinStateUsual

-- ある(s, aに関して自然な)等式が任意の (sa :: State s a) に対して成立することは、
-- 以下のNat型を用いて...

data Nat = Zero | Succ Nat
  deriving (Show, Eq)

-- 次の (ma :: State Nat Nat) に対して成立することと同値になります。

ma :: State Nat Nat
ma = \n -> (Succ n, n)

-- これを使って、モナド則の単位律を純代数的に書くことができます。

propLeftUnit :: (T, T, T) -> Bool
propLeftUnit joinDef = joinFromT joinDef (thePureState ma) Zero == ma Zero

propRightUnit :: (T, T, T) -> Bool
propRightUnit joinDef = joinFromT joinDef (fmapState thePureState ma) Zero == ma Zero

{-

pure a s = (s, a)

join ssa s = (foldT f g s t, ret (foldT f g s l) (foldT f g s r))
  where
    f s1 = fst (ssa s1)
    g s1 s2 = fst (snd (ssa s1) s2)
    ret s1 s2 = snd (snd (ssa s1) s2)

-}

{-

[Left Unit]

  (LHS)
  = join (pure ma) Zero
  = (foldT f g s t, ret (foldT f g s l) (foldT f g s r))
    where
      s = Zero
      f s1 = fst (pure ma s1) = s1
      g s1 s2 = fst (snd (pure ma s1) s2)
        = fst (ma s2) = Succ s2
      ret s1 s2 = snd (snd (pure ma s1) s2) = snd (ma s2) = s2
  = (foldT id (const Succ) Zero t, foldT id (const Succ) Zero r)
  = (countG t, countG r)
    where
      countG = foldT id (const Succ) Zero

      countG X = Zero
      countG (F r) = countG r
      countG (G _ r) = Succ (countG r)
  (RHS)
  = (Succ Zero, Zero)

  (1) countG t = Succ Zero
  (2) countG r = Zero

[Right Unit]

  mpa = fmap pure ma = \n -> (Succ n, pure n)

  (LHS)
  = join mpa Zero
  = (foldT f g s t, ret (foldT f g s l) (foldT f g s r))
    where
      s = Zero
      f s1 = fst (mpa s1) = Succ s1
      g s1 s2 = fst (snd (mpa s1) s2)
        = fst (pure s1 s2) = s2
      ret s1 s2 = snd (snd (mpa s1) s2) = snd (pure s1 s2) = s1
  = (foldT Succ (const id) Zero t, foldT Succ (const id) Zero l)
  = (countF t, countF l)
    where
      countF = foldT Succ (const id) Zero

      countF X = Zero
      countF (F r) = Succ (countF r)
      countF (G _ r) = countF r
   (RHS)
    = (Succ Zero, Zero)
   
   (3) countF t = Succ Zero
   (4) countF l = Zero

(1)式から、tは

  t = F $ F $ ... $ G _ $ F $ F $ ... $ X

という形をしていなければならず、また(3)式から

  t = G _ $ G _ $ ... $ F $ G _ $ ... $ X

でもなければならない。これらを同時に満たすためには、

  (1+3)    t = G t' (F X) | F (G t' X)     (for some t')

である必要がある。

-}

-- 同様にして、ある(s, aに関して自然な)等式が任意の (sssa :: State s (State s (State s a)))
-- に対して成立することは、以下の型Sを用いて...

data S = Init | A S | B S S | C S S S
  deriving (Show, Eq)

-- 次の sss に対して成立することと同値です。

sss :: State S (State S (State S (S,S,S)))
sss = \s1 -> (A s1, \s2 -> (B s1 s2, \s3 -> (C s1 s2 s3, (s1, s2, s3))))

-- これを使って、結合律も純粋に代数的に書くことができます。

propAssocJoin :: (T, T, T) -> Bool
propAssocJoin joinDef = join' (join' sss) Init == join' (fmapState join' sss) Init
  where
    join' = joinFromT joinDef

{-

join (join sss) Init = join (fmap join sss) Init

join sss
= \s -> (foldT f g s t, ret (foldT f g s l, foldT f g s r))
  where
    f = A
    g = B
    ret s1 s2 = \s3 -> (C s1 s2 s3, (s1, s2, s3))
= \s -> (foldT A B s t, \s3 -> (C (foldT A B s l) (foldT A B s r) s3, (foldT A B s l, foldT A B s r, s3))

join (join sss) Init
 = (foldT f g Init t, ret (foldT f g Init l, foldT f g Init r))
   where
    f s1 = fst (join sss s1) = foldT A B s1 t
    g s1 s2 = fst (snd (join sss s1) s2)
     = C (foldT A B s1 l) (foldT A B s1 r) s2
    ret s1 s2 = snd (snd (join sss s1) s2)
     = (foldT A B s1 l, foldT A B s1 r, s2)

fmap join sss
 = \s1 -> (A s1, join (\s2 -> (B s1 s2, \s3 -> (C s1 s2 s3, (s1, s2, s3)))))
 = \s1 -> (A s1, \s23 -> (foldT f g s23 t, ret (foldT f g s23 l) (foldT f g s23 r)))
   where
    f = B s1
    g = C s1
    ret = (,,) s1
= \s1 -> (A s1, \s23 -> (foldT (B s1) (C s1) s23 t, (s1, foldT (B s1) (C s1) s23 l, foldT (B s1) (C s1) s23 r)))

join (fmap join sss) Init
 = (foldT f' g' Init t, ret' (foldT f' g' Init l) (foldT f' g' Init r))
   where
     f' s1 = fst (join (fmap join sss) s1) = A s1
     g' s1 s2 = fst (snd (join (fmap join sss) s1) s2)
      = foldT (B s1) (C s1) s2 t
     ret' s1 s2
      = (s1, foldT (B s1) (C s1) s2 l, foldT (B s1) (C s1) s2 r)
 = (foldT A g' Init t, ret' (foldT A g' Init l) (foldT A g' Init r))
   where
     g' s1 s2 = fst (snd (join (fmap join sss) s1) s2)
      = foldT (B s1) (C s1) s2 t
     ret' s1 s2
      = (s1, foldT (B s1) (C s1) s2 l, foldT (B s1) (C s1) s2 r)

両辺の比較から4つの等式が得られる。

(5) foldT f g Init t = foldT A g' Init t
(6) foldT A B (foldT f g Init l) l = l'
(7) foldT A B (foldT f g Init l) r = foldT (B l') (C l') r' l
(8) foldT f g Init r = foldT (B l') (C l') r' r

  where
    f s1 = foldT A B s1 t
    g s1 s2 = C (foldT A B s1 l) (foldT A B s1 r) s2
    g' s1 s2 = foldT (B s1) (C s1) s2 t

    l' = foldT A g' Init l
    r' = foldT A g' Init r

(1+3) 式を再掲する。 t は

  (1+3)    t = G t' (F X) | F (G t' X)     (for some t')

という形に限られるのであった。 t = G t' (F X)の場合を「GF型のケース」、
t = F (G t' X)の場合を「FG型のケース」と呼ぶことにする。

まず(8)式から検討する。 (2)式から r = X | F X | F (F X) | ... =  FⁿX であるので、

  r' = foldT A g' Init r = Aⁿ Init

  (8左辺)
   = foldT f g Init r
   = fⁿ Init
   = (\x -> foldT A B x t)ⁿ Init
  (8右辺)
   = foldT (B l') (C l') (Aⁿ Init) (Fⁿ X)
   = (B l')ⁿ (Aⁿ Init)

ここで、データ型Sを(A,B,C)を頂点ラベルとして持つ木と見たときに、
根から最右辺をたどるパスをとる関数を

  rightmostPath :: S -> [ {A, B, C} ]
  rightmostPath Init = []
  rightmostPath (A s) = A : rightmostPath s
  rightmostPath (B _ s) = B : rightmostPath s
  rightmostPath (C _ _ s) = C : rightmostPath s

とすると、

  rightmostPath (8左辺) = (rightmostPath (foldT A B Init t))ⁿ
  rightmostPath (8右辺) = [B]ⁿ ++ [A]ⁿ

を得る。n >= 2 のときにこれは常に偽なので、 n <= 1 である。
更に、「FG型のケース」の場合、n == 0 の場合しか成り立たない。

続いて、(6)式に注目する。(4)式から l = X | G _ X | G _ (G _ X) | ... である。
これを(非正確ながら) l = (G _)^m X と表記する。

  l' = foldT A g' Init l
     = (g' (foldT A g' Init _))^m Init
  
  (6左辺)
   = foldT A B (foldT f g Init ((G _)^m X)) ((G _)^m X)
   = (B _)^m ((\x -> g _ x)^m Init)
   = (B _)^m ((\x -> C (foldT A B _ l) (foldT A B _ r) x)^m Init)
  (6右辺)
   = l'
   = foldT A g' Init ((G _)^ X)
   = (\x -> g' _ x)^m Init
   = (\x -> foldT (B _) (C _) x t)^m Init

である。再びrightmostPath関数を両辺に適用して比較すると、

  rightmostPath (6左辺) = [B]^m ++ [C]^m
  rightmostPath (6右辺) = (rightmostPath (foldT (B _) (C _) Init t))^m

となる。n >= 2 のときにこれは常に偽なので、tの選択によらず m <= 1であり、
かつ「GF型のケース」ではm == 0に限られる。

+-------+---------------+-------------+
|   t   | l = (G _)^m X | r = F^n X   |
+-------+---------------+-------------+
| GF型  | m == 0        | n <= 1      |
+-------+---------------+-------------+
| FG型  | m <= 1        | n == 0      |
+-------+---------------+-------------+

こんどは(7)式に注目する。場合分けをすると、

  ## 「GF型のケース」

    l = X
    l' = Init

    (7左辺)
    = foldT A B (foldT f g Init X) r
    = foldT A B Init r
    (7右辺)
    = foldT (B l') (C l') r' X
    = r'
    = foldT A g' Init r
    
  となる。これは n によらず成り立つ。

  ## 「FG型のケース」

    r = X
    r' = Init

    (7左辺)
    = foldT A B (foldT f g Init l) r
    = foldT f g Init l
    (7右辺)
    = foldT (B l') (C l') Init l
    
  となる。l = X のときこれは成立する。
  
  l = G k X にはならないことを背理法で示す。l = G k Xと仮定すると、

    (7左辺)
    = foldT f g Init (G k X)
    = g (foldT f g Init k) Init
    = g fk Init
        where
          fk = foldT f g Init k
    = C (foldT A B fk (G k X)) (foldT A B fk X) Init
    = C (B (foldT A B fk k) fk) fk Init
    (7右辺)
    = foldT (B l') (C l') Init (G k X)
    = C l' (foldT (B l') (C l') Init k) Init
  
  したがって
    
    (7.FG.1) l' = B (foldT A B fk k) fk
    (7.FG.2) foldT (B l') (C l') Init k = fk
  
  である。ここで、 k ≠ Xである。実際、 k = X と仮定すると

    fk = foldT f g Init X = Init

    (7.FG.1-LHS) l'
       = foldT A g' Init l
       = foldT A g' Init (G X X)
       = g' Init Init
       = foldT (B Init) (C Init) Init (F (G t' X))
       = B Init (C Init (...) Init)
    ((7.FG.1-RHS)
       = B (foldT A B Init X) Init
       = B Init Init
  
  となり矛盾する。

  だが、k = F _ | G _ _としても矛盾する。
  ここで、根から最左辺をたどるパスをとる関数を

    leftmostPath :: S -> [ {A, B, C} ]
    leftmostPath Init = []
    leftmostPath (A s) = A : leftmostPath s
    leftmostPath (B s _) = B : leftmostPath s
    leftmostPath (C s _ _) = C : leftmostPath s

  と定義すると、

    (7.FG.1') leftmostPath l'
                   = B : leftmostPath (foldT A B fk k)
                   = B : (leftmostPath (foldT A B Init k) ++ leftmostPath fk)
   
  となる。このとき

    ### k = F _ の場合

      (7.FG.1') leftmostPath l' = B : A : leftmostPath (...) ++ leftmostPath fk
      (7.FG.2') B : leftmostPath l' = leftmostPath fk
      
      すなわち
       
      leftmostPath fk = [B, B, A] ++ leftmostPath (...) + leftmostPath fk
      
      だがこれでは無限長になってしまい不可能。
    
    ### k = G _ _ の場合

      (7.FG.1') leftmostPath l' = B : B : leftmostPath (...) ++ leftmostPath fk
      (7.FG.2') C : leftmostPath l' = leftmostPath fk

     　であり、同様に無限長になってしまい不可能。
  
  すなわち、l = G k Xを充足するkは存在せず、l = Xがいえる。

まとめると、以下のようになる。


+-------+---------------+-------------+
|   t   | l = (G _)^m X | r = F^n X   |
+-------+---------------+-------------+
| GF型  | m == 0        | n <= 1      |
+-------+---------------+-------------+
| FG型  | m == 0        | n == 0      |
+-------+---------------+-------------+

最後に、(5)式に着目する。

## 「GF型のケース」
 
  t = G u (F X) であるとき、

    (5LHS) foldT f g Init (G u (F X))
      = g (foldT f g Init u) (f Init)
      = g (foldT f g Init u) (foldT A B Init t)
      = g (foldT f g Init u) (B (foldT A B Init u) (A Init))
           ^^^^^^^^^^^^^^^^^ = fu
      = C (foldT A B fu l) (foldT A B fu r) (B (foldT A B Init u) (A Init))
      = C fu (foldT A B fu r) (B fu (A Init))
    (5RHS) foldT A g' Init (G u (F X))
      = g' (foldT A g' Init u) (A Init)
            ^^^^^^^^^^^^^^^^^ fu'
      = foldT (B fu') (C fu') (A Init) t
      = C fu' (foldT (B fu') (C fu') (A Init) u) (B fu' (A Init))
  
  より、

    (5.GF.1) fu = fu'
    (5.GF.2) foldT A B fu r = foldT (B fu') (C fu') (A Init) u

   である。いま、r = X または r = F X であるが、 r = X と仮定すると

    (5.GF.2') foldT A B fu X = fu = foldT (B fu') (C fu') (A Init) u

    すなわち
    
      foldT (B fu') (C fu') (A Init) u = fu'
    
    となる。ここで u = X 以外であると fu'の木の深さが無限になってしまうが、
    u = X ととると

      fu = foldT f g Init X = Init
      fu' = foldT (B fu') (C fu') (A Init) X = A Init
    
    となり矛盾。したがって、r ≠ X である。

    r = F X を 代入すると、

    (5.GF.2'') foldT A B fu (F X)
      = A fu = foldT (B fu') (C fu') (A Init) u

    これが成り立つのは u = X, fu = Init の場合のみである。
    したがって、

      t = G u (F X) = G X (F X)
      l = X
      r = F X
    
    のみが、GF型のケースでMonad則を満たす。

## 「FG型のケース」

  t = F (G u X) の場合である。
  ここまでの議論から、l = r = Xであり、
  
  (5.FG-LHS) = foldT f g Init (F (G u X))
    = f (g (foldT f g Init u) Init)
            ^^^^^^^^^^^^^^^^ = fu
    = foldT A B (g fu Init) (F (G u X))
    = A (B (foldT A B (g fu Init) u) (g fu Init))

  (5.FG-RHS) = foldT A g' Init (F (G u X))
    = A (g' (foldT A g' Init u) Init)
             ^^^^^^^^^^^^^^^^^ = fu'
    = A $ foldT (B fu') (C fu') Init (F (G u X))
    = A $ B fu' (C fu' (foldT (B fu') (C fu') Init u) Init)

  (5.FG.1) foldT A B (g fu Init) u = fu'
  (5.FG.2) g fu Init = C fu' (foldT (B fu') (C fu') Init u) Init

  いま、g の定義を展開すると、
    g s1 s2
      = C (foldT A B s1 l) (foldT A B s1 r) s2
      = C s1 s1 s2
  なので、
  
  (5.FG.2) C fu fu Init = C fu' (foldT (B fu') (C fu') Init u) Init

  (5.FG.2.1) fu = fu'
  (5.FG.2.2) fu = foldT (B fu') (C fu') Init u

  である。いま、u ≠ X であれば fu' の木の深さが無限になってしまうが、u = X としても
  
  (5.FG.1''') g Init Init = C Init Init Init = Init

  より矛盾する。したがってどんな u も t = F (G u X) としたときに
  モナド則を充足しない。

これによって全てのケースが検討された。Monad則を満たす (t, l, r) は

  t = G X (F X)
  l = X
  r = F X

すなわち通常のStateモナドを定義する3つ組に限る。

-}

-- ちなみに、Reverse state monadというものが一応あるが、これには
-- 「無限の深さのT」が対応する。

--   https://hackage.haskell.org/package/tardis
--   https://hackage.haskell.org/package/rev-state

newtype RevState s a = RevState { runRevState :: s -> (a, s) }
  deriving Functor

instance Applicative (RevState s) where
  pure a = RevState (\s -> (a, s))

  (<*>) = ap

instance Monad (RevState s) where
  ma >>= f = RevState $ \s ->
    let ~(a, s'') = runRevState ma s'
        ~(b, s')  = runRevState (f a) s
    in (b, s'')

-- このインスタンスには、以下の無限の深さをもつ T が対応する。
-- こういった、有限でないTに対しては、foldTが全域関数とはならない。
-- 
-- 実際、RevStateの(>>=)は、全域関数でない(m :: s -> (a, s))を返しうる。
-- 言い換えれば、(>>=)を3引数の関数
--
--   (RevState s a, a -> RevState s b, s) -> (b, s)
--
-- と見たとき、全域関数になっていない。
-- このような全域関数でないものは、今回はLawfulなMonadとして認めていない。

revStateDef :: (T, T, T)
revStateDef = (F t', t', X)
  where t' = G t' X
