{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif

-- N.B. addBasicBlocks won't work on OO without a Node (branch/label) constraint

module Compiler.Hoopl.GraphUtil
  ( splice, gSplice , cat , bodyGraph, bodyUnion
  , frontBiasBlock, backBiasBlock
  )

where

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label

bodyGraph :: Body n -> Graph n C C
bodyGraph b = GMany NothingO b NothingO

splice :: forall block n e a x . NonLocal (block n) =>
          (forall e x . block n e O -> block n O x -> block n e x)
       -> (Graph' block n e a -> Graph' block n a x -> Graph' block n e x)
splice bcat = sp
  where sp :: forall e a x .
              Graph' block n e a -> Graph' block n a x -> Graph' block n e x

        sp GNil g2 = g2
        sp g1 GNil = g1

        sp (GUnit b1) (GUnit b2) = {-# SCC "sp1" #-} GUnit $! b1 `bcat` b2

        sp (GUnit b) (GMany (JustO e) bs x) = {-# SCC "sp2" #-} GMany (JustO (b `bcat` e)) bs x

        sp (GMany e bs (JustO x)) (GUnit b2) = {-# SCC "sp3" #-} GMany e bs (JustO (x `bcat` b2))

        sp (GMany e1 bs1 (JustO x1)) (GMany (JustO e2) b2 x2)
          = {-# SCC "sp4" #-} GMany e1 (b1 `bodyUnion` b2) x2
          where b1 = addBlock (x1 `bcat` e2) bs1

        sp (GMany e1 b1 NothingO) (GMany NothingO b2 x2)
          = {-# SCC "sp5" #-} GMany e1 (b1 `bodyUnion` b2) x2

        sp _ _ = error "bogus GADT match failure"

bodyUnion :: forall a . LabelMap a -> LabelMap a -> LabelMap a
bodyUnion = mapUnionWithKey nodups
  where nodups l _ _ = error $ "duplicate blocks with label " ++ show l

gSplice :: NonLocal n => Graph n e a -> Graph n a x -> Graph n e x
gSplice = splice cat

cat :: Block n e O -> Block n O x -> Block n e x
cat x y = case x of
  BNil -> y

  BlockCO l b1 -> case y of
                   BlockOC b2 n -> BlockCC l (b1 `cat` b2) n
                   BNil         -> x
                   BMiddle n    -> BlockCO l (b1 `BHead` n)
                   BCat{}       -> BlockCO l (b1 `BCat` y)
                   BHead{}      -> BlockCO l (b1 `BCat` y)
                   BTail{}      -> BlockCO l (b1 `BCat` y)

  BMiddle n -> case y of
                   BlockOC b2 n2 -> BlockOC (n `BTail` b2) n2
                   BNil          -> x
                   BMiddle{}     -> BTail n y
                   BCat{}        -> BTail n y
                   BHead{}       -> BTail n y
                   BTail{}       -> BTail n y

  BCat{} -> case y of
                   BlockOC b3 n2 -> BlockOC (x `cat` b3) n2
                   BNil          -> x
                   BMiddle n     -> BHead x n
                   BCat{}        -> BCat x y
                   BHead{}       -> BCat x y
                   BTail{}       -> BCat x y

  BHead{} -> case y of
                   BlockOC b2 n2 -> BlockOC (x `cat` b2) n2
                   BNil          -> x
                   BMiddle n     -> BHead x n
                   BCat{}        -> BCat x y
                   BHead{}       -> BCat x y
                   BTail{}       -> BCat x y


  BTail{} -> case y of
                   BlockOC b2 n2 -> BlockOC (x `BCat` b2) n2
                   BNil          -> x
                   BMiddle n     -> BHead x n
                   BCat{}        -> BCat x y
                   BHead{}       -> BCat x y
                   BTail{}       -> BCat x y

----------------------------------------------------------------

-- | A block is "front biased" if the left child of every
-- concatenation operation is a node, not a general block; a
-- front-biased block is analogous to an ordinary list.  If a block is
-- front-biased, then its nodes can be traversed from front to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be front-biased; a closed/open block is inherently back-biased.

frontBiasBlock :: Block n e x -> Block n e x
frontBiasBlock blk = case blk of
   BlockCO f b   -> BlockCO f (fb b BNil)
   BlockOC   b n -> BlockOC   (fb b BNil) n
   BlockCC f b n -> BlockCC f (fb b BNil) n
   b@BNil{}      -> fb b BNil
   b@BMiddle{}   -> fb b BNil
   b@BCat{}      -> fb b BNil
   b@BHead{}     -> fb b BNil
   b@BTail{}     -> fb b BNil
 where
   fb :: Block n O O -> Block n O O -> Block n O O
   fb BNil        rest = rest
   fb (BMiddle n) rest = BTail n rest
   fb (BCat l r)  rest = fb l (fb r rest)
   fb (BTail n b) rest = BTail n (fb b rest)
   fb (BHead b n) rest = fb b (BTail n rest)

-- | A block is "back biased" if the right child of every
-- concatenation operation is a node, not a general block; a
-- back-biased block is analogous to a snoc-list.  If a block is
-- back-biased, then its nodes can be traversed from back to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be back-biased; an open/closed block is inherently front-biased.

backBiasBlock :: Block n e x -> Block n e x
backBiasBlock blk = case blk of
   BlockCO f b   -> BlockCO f (bb BNil b)
   BlockOC   b n -> BlockOC   (bb BNil b) n
   BlockCC f b n -> BlockCC f (bb BNil b) n
   b@BNil{}      -> bb BNil b
   b@BMiddle{}   -> bb BNil b
   b@BCat{}      -> bb BNil b
   b@BHead{}     -> bb BNil b
   b@BTail{}     -> bb BNil b
 where
   bb :: Block n O O -> Block n O O -> Block n O O
   bb rest BNil = rest
   bb rest (BMiddle n) = BHead rest n
   bb rest (BCat l r) = bb (bb rest l) r
   bb rest (BTail n b) = bb (BHead rest n) b
   bb rest (BHead b n) = BHead (bb rest b) n
