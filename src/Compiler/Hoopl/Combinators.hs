{-# LANGUAGE GADTs, RankNTypes, LiberalTypeSynonyms, ScopedTypeVariables #-}

module Compiler.Hoopl.Combinators
  ( SimpleFwdRewrite, SimpleFwdRewrite3, noFwdRewrite, thenFwdRw
  , shallowFwdRw3, shallowFwdRw, deepFwdRw3, deepFwdRw, iterFwdRw
  , SimpleBwdRewrite, SimpleBwdRewrite3, noBwdRewrite, thenBwdRw
  , shallowBwdRw3, shallowBwdRw, deepBwdRw3, deepBwdRw, iterBwdRw
  , pairFwd, pairBwd, pairLattice
  )

where

import Control.Monad
import Data.Maybe

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Graph (Graph, C, O)
import Compiler.Hoopl.Label


----------------------------------------------------------------
-- Using the Shape typeclass, we can discover the shape of a graph node.

class Shape n where
  shape :: n e x -> ShapeT e x

data ShapeT e x where
  First  :: ShapeT C O
  Middle :: ShapeT O O
  Last   :: ShapeT O C

----------------------------------------------------------------
type FRW  m n f e x = n e x -> f -> m (FwdRes m n f e x)
type SFRW m n f e x = n e x -> f -> m (Maybe (Graph n e x))
type SimpleFwdRewrite3 m n f = ExTriple (SFRW m n f)
type ExTriple a = (a C O, a O O, a O C) -- ^ entry/exit triple
type SimpleFwdRewrite m n f = forall e x . SFRW m n f e x

----------------------------------------------------------------
-- Some combinators cannot be written without distinguishing
-- between first, middle, and last nodes.
-- See

-- Most of the combinators are easier to write using polymorphic
-- analyze or rewrite functions.

-- 
-- Same code, different types. Not sure how to improve it...
polySFR :: Shape n => SimpleFwdRewrite3 m n f -> SimpleFwdRewrite m n f
polySFR (f, m, l) = \ n -> case shape n of First  -> f n
                                           Middle -> m n
                                           Last   -> l n

polySBR :: Shape n => SimpleBwdRewrite3 m n f -> SimpleBwdRewrite m n f
polySBR (f, m, l) = \ n -> case shape n of First  -> f n
                                           Middle -> m n
                                           Last   -> l n

getFRewrite :: forall m n f e x . Shape n
            => FwdRewrite m n f -> (n e x -> f -> m (FwdRes m n f e x))
getFRewrite = poly . getFRewrite3
  where poly :: ExTriple (FRW m n f) -> forall e x . FRW m n f e x
        poly (f, m, l) = \ n -> case shape n of First  -> f n
                                                Middle -> m n
                                                Last   -> l n

getBRewrite :: forall m n f e x . Shape n
            => BwdRewrite m n f -> (n e x -> Fact x f -> m (BwdRes m n f e x))
getBRewrite = poly . getBRewrite3
  where poly :: ExTriple (BRW m n f) -> forall e x . BRW m n f e x
        poly (f, m, l) = \ n -> case shape n of First  -> f n
                                                Middle -> m n
                                                Last   -> l n



----------------------------------------------------------------


shallowFwdRw :: Monad m => SimpleFwdRewrite m n f -> FwdRewrite m n f
shallowFwdRw rw = mkFRewrite $ lift rw
  where lift rw n f = liftM withoutRewrite (rw n f) 
        withoutRewrite Nothing = NoFwdRes
        withoutRewrite (Just g) = FwdRes g noFwdRewrite

shallowFwdRw3 :: forall m n f . (Monad m, Shape n) => SimpleFwdRewrite3 m n f -> FwdRewrite m n f
shallowFwdRw3 rw3 = shallowFwdRw $ polySFR rw3

deepFwdRw3    :: (Monad m, Shape n) => SimpleFwdRewrite3 m n f -> FwdRewrite m n f
deepFwdRw     :: (Monad m, Shape n) => SimpleFwdRewrite  m n f -> FwdRewrite m n f
deepFwdRw3 r = iterFwdRw  (shallowFwdRw3 r)
deepFwdRw  r = iterFwdRw  (shallowFwdRw  r)

-- N.B. rw3, rw3', and rw3a are triples of functions.
-- But rw and rw' are single functions.
-- @ start comb1.tex
thenFwdRw :: (Monad m, Shape n)
          => FwdRewrite m n f 
          -> FwdRewrite m n f 
          -> FwdRewrite m n f
thenFwdRw rw3 rw3' = mkFRewrite thenrw
 where
  thenrw n f = getFRewrite rw3 n f >>= fwdRes
     where fwdRes NoFwdRes = getFRewrite rw3' n f
           fwdRes (FwdRes g rw3a)
            = return $ FwdRes g (rw3a `thenFwdRw` rw3')

noFwdRewrite :: Monad m => FwdRewrite m n f
noFwdRewrite = mkFRewrite $ \ _ _ -> return NoFwdRes
-- @ end comb1.tex

-- @ start iterf.tex
iterFwdRw :: (Monad m, Shape n)
          => FwdRewrite m n f 
          -> FwdRewrite m n f
iterFwdRw rw3 = mkFRewrite iter
 where
    iter n f = getFRewrite rw3 n f >>= fwdRes
    fwdRes NoFwdRes = return NoFwdRes
    fwdRes (FwdRes g rw3a)
      = return $ FwdRes g (rw3a `thenFwdRw` iterFwdRw rw3)
-- @ end iterf.tex


----------------------------------------------------------------

type BRW  m n f e x = n e x -> Fact x f -> m (BwdRes m n f e x)
type SBRW m n f e x = n e x -> Fact x f -> m (Maybe (Graph n e x))
type SimpleBwdRewrite3 m n f = ExTriple ( SBRW m n f)
type SimpleBwdRewrite m n f = forall e x . SBRW m n f e x

----------------------------------------------------------------

noBwdRewrite :: Monad m => BwdRewrite m n f
noBwdRewrite = mkBRewrite $ \ _ _ -> return NoBwdRes

shallowBwdRw :: Monad m => SimpleBwdRewrite m n f -> BwdRewrite m n f
shallowBwdRw rw = mkBRewrite $ lift rw
  where lift rw n f = liftM withoutRewrite (rw n f)
        withoutRewrite Nothing = NoBwdRes
        withoutRewrite (Just g) = BwdRes g noBwdRewrite

shallowBwdRw3 :: (Monad m, Shape n) => SimpleBwdRewrite3 m n f -> BwdRewrite m n f
shallowBwdRw3 rw = shallowBwdRw $ polySBR rw

deepBwdRw3 :: (Monad m, Shape n) => SimpleBwdRewrite3 m n f -> BwdRewrite m n f
deepBwdRw  :: (Monad m, Shape n) => SimpleBwdRewrite  m n f -> BwdRewrite m n f
deepBwdRw3 r = iterBwdRw (shallowBwdRw3 r)
deepBwdRw  r = iterBwdRw (shallowBwdRw  r)


thenBwdRw :: (Monad m, Shape n) => BwdRewrite m n f -> BwdRewrite m n f -> BwdRewrite m n f
thenBwdRw rw3 rw3' = mkBRewrite thenrw
  where
   thenrw n f = getBRewrite rw3 n f >>= bwdRes
      where bwdRes NoBwdRes = getBRewrite rw3' n f
            bwdRes (BwdRes g rw3a)
             = return $ BwdRes g (rw3a `thenBwdRw` rw3')

iterBwdRw :: (Monad m, Shape n) => BwdRewrite m n f -> BwdRewrite m n f
iterBwdRw rw3 = mkBRewrite iter
  where 
    iter n f = getBRewrite rw3 n f >>= bwdRes
    bwdRes NoBwdRes = return NoBwdRes
    bwdRes (BwdRes g rw3a)
      = return $ BwdRes g (rw3a `thenBwdRw` iterBwdRw rw3)

pairFwd :: forall m n f f' . (Monad m, Shape n) => FwdPass m n f -> FwdPass m n f' -> FwdPass m n (f, f')
pairFwd pass1 pass2 = FwdPass lattice transfer rewrite
  where
    lattice = pairLattice (fp_lattice pass1) (fp_lattice pass2)
    transfer = mkFTransfer3 (tf tf1 tf2) (tf tm1 tm2) (tfb tl1 tl2)
      where
        tf  t1 t2 n (f1, f2) = (t1 n f1, t2 n f2)
        tfb t1 t2 n (f1, f2) = mapMapWithKey withfb2 fb1
          where fb1 = t1 n f1
                fb2 = t2 n f2
                withfb2 l f = (f, fromMaybe bot2 $ lookupFact l fb2)
                bot2 = fact_bot (fp_lattice pass2)
        (tf1, tm1, tl1) = getFTransfer3 (fp_transfer pass1)
        (tf2, tm2, tl2) = getFTransfer3 (fp_transfer pass2)
    rewrite = liftRW (fp_rewrite pass1) fst `thenFwdRw` liftRW (fp_rewrite pass2) snd
      where
        liftRW rws proj = mkFRewrite3 (lift f) (lift m) (lift l)
          where lift rw n f = liftM projRewrite $ rw n (proj f)
                projRewrite NoFwdRes = NoFwdRes
                projRewrite (FwdRes g rws') = FwdRes g $ liftRW rws' proj
                (f, m, l) = getFRewrite3 rws

pairBwd :: forall m n f f' . (Monad m, Shape n) => BwdPass m n f -> BwdPass m n f' -> BwdPass m n (f, f')
pairBwd pass1 pass2 = BwdPass lattice transfer rewrite
  where
    lattice = pairLattice (bp_lattice pass1) (bp_lattice pass2)
    transfer = mkBTransfer3 (tf tf1 tf2) (tf tm1 tm2) (tfb tl1 tl2)
      where
        tf  t1 t2 n (f1, f2) = (t1 n f1, t2 n f2)
        tfb t1 t2 n fb = (t1 n $ mapMap fst fb, t2 n $ mapMap snd fb)
        (tf1, tm1, tl1) = getBTransfer3 (bp_transfer pass1)
        (tf2, tm2, tl2) = getBTransfer3 (bp_transfer pass2)
    rewrite = liftRW (bp_rewrite pass1) fst `thenBwdRw` liftRW (bp_rewrite pass2) snd
      where
        liftRW :: forall f1 . BwdRewrite m n f1 -> ((f, f') -> f1) -> BwdRewrite m n (f, f')
        liftRW rws proj = mkBRewrite3 (lift proj f) (lift proj m) (lift (mapMap proj) l)
          where lift proj' rw n f = liftM projRewrite $ rw n (proj' f)
                projRewrite NoBwdRes = NoBwdRes
                projRewrite (BwdRes g rws') = BwdRes g $ liftRW rws' proj
                (f, m, l) = getBRewrite3 rws

pairLattice :: forall f f' . DataflowLattice f -> DataflowLattice f' -> DataflowLattice (f, f')
pairLattice l1 l2 =
  DataflowLattice
    { fact_name       = fact_name l1 ++ " x " ++ fact_name l2
    , fact_bot        = (fact_bot l1, fact_bot l2)
    , fact_extend     = extend'
    , fact_do_logging = fact_do_logging l1 || fact_do_logging l2
    }
  where
    extend' lbl (OldFact (o1, o2)) (NewFact (n1, n2)) = (c', (f1, f2))
      where (c1, f1) = fact_extend l1 lbl (OldFact o1) (NewFact n1)
            (c2, f2) = fact_extend l2 lbl (OldFact o2) (NewFact n2)
            c' = case (c1, c2) of
                   (NoChange, NoChange) -> NoChange
                   _                    -> SomeChange
