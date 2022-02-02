-- Binomial heaps with Int keys

module BinomialHeap(BinoHeap, empty, isEmpty, insert, extractMin) where

{- in the binomial tree Node r v ts,
   the first integer, r, is the rank of the tree;
   the second integer, v, is the key at its root;
   ts is the list of sub-trees under its root.

   INVARIANT: the list ts has r elements (sub-trees), ordered by decreasing ranks r-1, r-2, ..., 1, 0.
 -}
data BinoTree a = Node Int Int a [BinoTree a]
                deriving (Show)

{- A binomial heap consisting of trees t1, ..., tn is given by BinoHeap [t1, ..., tn].

   INVARIANT:
   - in each binomial tree, the key of each non-root node is at least the key
     of its parent (min-heap property)
   - the trees t1,...,tn have increasing ranks.
-}
data BinoHeap a = BinoHeap [BinoTree a]
                deriving (Show)

-- Some selectors

{- rank t
   RETURNS: the rank of t
 -}
rank :: BinoTree a -> Int
rank (Node r _ _ _) = r

{- root t
   RETURNS: the key of the root of t
 -}
root :: BinoTree a -> Int
root (Node _ k _ _) = k

{- link t1 t2
   PRE:  rank t1 == rank t2
   RETURNS: a binomial tree containing the union of the elements of t1 and t2; if
         t1 and t2 satisfy the min-heap property, then the result also
         satisfies the min-heap property
 -}
link :: BinoTree a -> BinoTree a-> BinoTree a
link t1@(Node r1 k1 v1 ts1) t2@(Node _ k2 v2 ts2) =
    if k1 < k2 then
        Node (r1+1) k1 v1 (t2 : ts1)
    else
        Node (r1+1) k2 v2 (t1 : ts2)

-- the empty binomial heap
empty :: BinoHeap a
empty = BinoHeap []

{- isEmpty t
   RETURNS: True if and only if t is empty
 -}
isEmpty :: BinoHeap a-> Bool
isEmpty (BinoHeap []) = True
isEmpty _             = False

{- insTree h t
   PRE:  t satisfies the min-heap property
   RETURNS: a binomial heap containing the union of the elements of h and t
 -}
insTree :: BinoHeap a -> BinoTree a -> BinoHeap a
insTree (BinoHeap []) t = BinoHeap [t]
insTree (BinoHeap (t':h')) t =
        if rank t < rank t' then
            BinoHeap (t:t':h')
        else
            insTree (BinoHeap h') (link t t')

{- insert h k
   RETURNS: h with element k inserted
 -}
insert :: BinoHeap a -> Int -> a -> BinoHeap a
insert h k v = insTree h (Node 0 k v [])

{- merge h1 h2
   RETURNS: the union of h1 and h2
 -}
merge :: BinoHeap a-> BinoHeap a-> BinoHeap a
merge h1 (BinoHeap []) = h1
merge (BinoHeap []) h2 = h2
merge h1@(BinoHeap (t1:h1')) h2@(BinoHeap (t2:h2'))
        | rank t1 < rank t2 =
            let BinoHeap h = merge (BinoHeap h1') h2
            in
                BinoHeap (t1 : h)
        | rank t2 < rank t1 =
            let BinoHeap h = merge h1 (BinoHeap h2')
            in
                BinoHeap (t2 : h)
        | otherwise =
            insTree (merge (BinoHeap h1') (BinoHeap h2')) (link t1 t2)

extractMinTree :: BinoHeap a -> (BinoTree a, BinoHeap a)
extractMinTree (BinoHeap [t]) = (t, BinoHeap [])
extractMinTree (BinoHeap (t:h)) =
    let (t', BinoHeap h') = extractMinTree (BinoHeap h)
    in
      if root t < root t' then (t, BinoHeap h) else (t', BinoHeap (t:h'))

{- extractMin h
   PRE:  h is not empty
   RETURNS: (k, h-k), where k is the minimum key of h, and h-k is h without an
         element of key k
 -}
extractMin :: BinoHeap a -> ((a, Int), BinoHeap a)
extractMin h =
    let (Node _ k v ts, h') = extractMinTree h
    in
        ((v, k), merge (BinoHeap (reverse ts)) h')  -- Why reverse?
