-- DO NOT MODIFY THIS FILE. DO NOT SUBMIT THIS FILE.

{- A key-value store: each key corresponds to at most one data item. -}

module Table(Table, empty, insert, exists, lookup, delete, iterate, keys, values) where

import Prelude hiding (lookup, iterate)

--------------------------------------------------------------------------------
-- interface
--------------------------------------------------------------------------------

-- the empty table with keys of type k and values of type v
empty :: Table k v

{- insert t k v
   RETURNS: the table t with value v inserted with key k.
   If key k already exists in the table, its old value is first forgotten.
 -}
insert :: Eq k => Table k v -> k -> v -> Table k v

{- exists t k
   RETURNS: true iff key k already exists in the table t
 -}
exists :: Eq k => Table k v -> k -> Bool

{- lookup t k
   RETURNS: Just the value associated with key k in the table t, or None if the key is absent
 -}
lookup :: Eq k => Table k v -> k -> Maybe v

{- delete t k
   RETURNS: The table t minus the key k and its associated value.
 -}
delete :: Eq k => Table k v -> k -> Table k v

{- iterate t f acc
   RETURNS: The result of calling f on all key-value pairs of t in some order, 
                  with an accumulator that is initially acc.
 -}
iterate :: Table k v -> (b -> (k, v) -> b) -> b -> b

{- keys t f acc
   RETURNS: The result of calling f on all keys of t in some order, 
                  with an accumulator that is initially acc.
 -}
keys :: Table k v -> (b -> k -> b) -> b -> b

{- values t f acc
   RETURNS: The result of calling f on all values of t in some order, 
                  with an accumulator that is initially acc.
 -}
values :: Table k v -> (b -> v -> b) -> b -> b

--------------------------------------------------------------------------------
-- implementation
--------------------------------------------------------------------------------

newtype Table k v = T [(k, v)] deriving (Show)

empty = T []

insert (T t) k v = T $ insert' t k v
  where
    insert' [] k v = [(k,v)]
    insert' ((k', v'):as) k v
            | k == k'    = (k,v) : as
            | otherwise = (k',v') : insert' as k v

exists (T t) k = exists' t k
  where
    exists' [] k = False
    exists' ((k', _):as) k = if k == k' then True else exists' as k

lookup (T t) k = lookup' t k
  where
    lookup' [] k = Nothing
    lookup' ((k', v):as) k = if k == k' then Just v else lookup' as k

delete (T t) k = T $ delete' t k
  where
    delete' [] _ = []
    delete' ((k', v'):as) k = if k == k' then as else (k',v') : delete' as k

iterate (T t) f d = foldl f d t

keys (T t) f d = foldl f d (map fst t)

values (T t) f d = foldl f d (map snd t)
