-- DO NOT MODIFY THIS FILE. DO NOT SUBMIT THIS FILE.

module PriorityQueue(PriorityQueue, PriorityQueue.empty, is_empty, PriorityQueue.insert, least) where

import BinomialHeap

--------------------------------------------------------------------------------
-- interface
--------------------------------------------------------------------------------

-- the empty priority queue
empty :: PriorityQueue a

{- is_empty q
   RETURNS: True if and only if q is empty
 -}
is_empty :: PriorityQueue a -> Bool

{- insert q (x,p)
   RETURNS: the queue q with element x inserted at priority p
 -}
insert :: PriorityQueue a -> (a, Int) -> PriorityQueue a

{- least q
   PRE:  q is not empty
   RETURNS: ((x,p), q’), where x is an element of minimum priority in q, p is the
         priority of x, and q’ is q without x
 -}
least :: PriorityQueue a -> ((a, Int), PriorityQueue a)

--------------------------------------------------------------------------------
-- implementation
--------------------------------------------------------------------------------

-- the type of priority queues with elements of type a (and priorities
-- of type Int)
type PriorityQueue = BinomialHeap.BinoHeap

empty = BinomialHeap.empty

is_empty = BinomialHeap.isEmpty

insert q (x,p) = BinomialHeap.insert q p x

least = BinomialHeap.extractMin
