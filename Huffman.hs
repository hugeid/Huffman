-- DO NOT MODIFY THE FOLLOWING LINES
module Huffman(HuffmanTree, characterCounts, huffmanTree, codeTable, encode, compress, decompress) where

import Table
import PriorityQueue

import Test.HUnit
{- a bit code (of a character or string) is represented by a list of Booleans
   INVARIANT:
     the bit code is a concatenation of (0 or more) valid code words for some Huffman tree
 -}
type BitCode = [Bool]

-- END OF DO NOT MODIFY ZONE
--Hugo Eidmann & Viktor Kangasniemi grupp 22
--------------------------------------------------------------------------------

{- characterCounts s
   creates a table with the character counts of s
   RETURNS: a table that maps each character that occurs in s to the number of
         times the character occurs in s
   EXAMPLES:
   characterCounts "Example text" == T [('E',1),('x',2),('a',1),('m',1),('p',1),('l',1),('e',2),(' ',1),('t',2)]
      characterCounts "hello" == T [('h',1),('e',1),('l',2),('o',1)]
      characterCounts "" == T []
 -}
characterCounts :: String -> Table Char Int
characterCounts = characterCounts' Table.empty

{- characterCounts' acc s
  helper function for characterCounts that uses an accumulator to save the intermediate results in a table.
-}
characterCounts' :: (Num v, Eq k) => Table k v -> [k] -> Table k v
characterCounts' acc [] = acc
characterCounts' acc (x:xs)
  | Table.exists acc x = let Just c = Table.lookup acc x 
    in characterCounts' (Table.insert acc x (c+1)) xs

  | otherwise = characterCounts' (Table.insert acc x 1) xs


-- modify and add comments as needed
{- a Huffman tree
  Empty is an empty tree.
  Leaf c x is a leaf with the character c and x is the number of times c occurs in the string that is represented in the tree
  Node l x r is a node with left child l, value x, and right child r.
  in Node l x r, x is the sum of all a, b, in (Leaf c a), (Node l2 b r2), where (Leaf c a) and (Node l2 b r2) are sub-trees of (Node l x r) 
  INVARIANT: sub-trees with larger character counts do not occur at a lower level of the tree than
sub-trees with smaller character counts
-}
data HuffmanTree = Empty | Leaf Char Int | Node HuffmanTree Int HuffmanTree deriving Show

{- huffmanTree t
  iterates over all (key, value) pairs in z t and adds them as HuffmanTrees into a PriorityQueue,
  merges the trees in the PriorityQueue in increasing order of priority into a single HuffmanTree.
  PRE:  t maps each key to a positive value
  RETURNS: a Huffman tree based on the character counts in t
  EXAMPLES: 
    huffmanTree (T [('E',1),('x',2),('a',1),('m',1),('p',1),('l',1),('e',2),(' ',1),('t',2)]) ==
      Node (Node (Leaf 't' 2) 4 (Node (Leaf 'E' 1) 2 (Leaf 'p' 1))) 12 (Node (Node (Node (Leaf 'a' 1) 2 (Leaf ' ' 1)) 4 (Leaf 'e' 2)) 8 (Node (Leaf 'x' 2) 4 (Node (Leaf 'l' 1) 2 (Leaf 'm' 1))))
    huffmanTree (T []) == Empty
    huffmanTree (T [('a', 1)]) == Leaf 'a' 1
 -}
huffmanTree :: Table Char Int -> HuffmanTree 
huffmanTree t
  | null (toList t) = Empty
  | otherwise = hqmerge $ Table.iterate t hqinsert PriorityQueue.empty

{- toList t
  Export a table t as a list of key-value tuples. 
  The order of the elements in t are reversed.
  
  RETURNS: a list of all key-value pairs in t
  EXAMPLES: 
    tolist (T [('h',1),('e',1),('l',2),('o',1)]) == [('o',1),('l',2),('e',1),('h',1)]
    toList (T []) == []
-}
toList :: Table k v -> [(k, v)]
toList t = Table.iterate t (\a b -> b:a) []

{- hqinsert q (x, c)
  inserts a HuffmanTree that consists just of a leaf labeled with x and c into the priority queue, with priority c
  
  RETURNS: q but with the (Leaf x c, c) inserted 
  EXAMPLES: hqinsert (BinoHeap []) ('a', 2) ==  BinoHeap [Node 0 2 (Leaf 'a' 2) []]
    hqinsert (BinoHeap [Node 0 2 (Leaf 'a' 2) []]) ('b', 4) == BinoHeap [Node 1 2 (Leaf 'a' 2) [Node 0 4 (Leaf 'b' 4) []]]
    hqinsert (BinoHeap [Node 1 2 (Leaf 'a' 2) [Node 0 4 (Leaf 'b' 4) []]]) ('c', 1) == BinoHeap [Node 0 1 (Leaf 'c' 1) [],Node 1 2 (Leaf 'a' 2) [Node 0 4 (Leaf 'b' 4) []]]
-}
hqinsert :: PriorityQueue HuffmanTree -> (Char, Int) -> PriorityQueue HuffmanTree
hqinsert q (x,c) = PriorityQueue.insert q (Leaf x c, c)

{-hqmerge q
  Merges the HuffmanTrees in q into one tree, in increasing order of priority
  If there is only one tree in q, that tree is returned, otherwise it merges the trees until there is only one.
  RETURNS: A merged tree consisting of all the trees in q
  PRE: q is not empty
  EXAMPLES: 
    hqmerge (BinoHeap [Node 1 1 (Leaf 'a' 1) [Node 0 4 (Leaf 'b' 4) []]]) == Node (Leaf 'a' 1) 5 (Leaf 'b' 4)
    hqmerge (BinoHeap [Node 0 1 (Leaf 'a' 1) []]) == Leaf 'a' 1
-}

hqmerge :: PriorityQueue HuffmanTree -> HuffmanTree
-- VARIANT: (number of elements in q)
hqmerge q 
  | PriorityQueue.is_empty $ snd $ least q = fst $ fst $ least q
  | otherwise = hqmerge $ hqmerge' q


{-hqmerge' q
  Helper function for hqmerge.
  Merges the two trees with least priority in q
  PRE: q contains at least two elements
  RETURNS: q but with the two trees with least priority merged into one tree.
  EXAMPLES: 
    hqmerge' (BinoHeap [Node 1 1 (Leaf 'a' 1) [Node 0 4 (Leaf 'b' 4) []]]) == BinoHeap [Node 0 5 (Node (Leaf 'a' 1) 5 (Leaf 'b' 4)) []]
-}
hqmerge' :: PriorityQueue HuffmanTree -> PriorityQueue HuffmanTree
hqmerge' q =
  let ((t1, p1), rest1) = least q 
  in 
    let ((t2, p2), rest2) = least rest1 
      in PriorityQueue.insert rest2 (Node t1 (p1+p2) t2, p1+p2)


{- codeTable h
   Creates a table that maps each character from the input tree to its respective Huffman code
   RETURNS: a table that maps each character in h to its Huffman code
   EXAMPLES: codeTable (Node (Node (Leaf 'b' 1) 2 (Leaf 'a' 1)) 5 (Leaf 'c' 3)) ==
                          T [('b',[False,False]),('a',[False,True]),('c',[True])]
    codeTable (Leaf 'a' 1) == T [('a',[])]
    codeTable Empty = T []
    codeTable $ huffmanTree $ characterCounts "abba" == T [('a',[False]),('b',[True])]
 -}
codeTable :: HuffmanTree -> Table Char BitCode
codeTable Empty = Table.empty
codeTable hTree = fromList (codeLst hTree [])

{- codeLst hTree bitcode
  Goes through the given HuffmanTree and maps each leafs char to its respective Huffman code
  PRE: input tree is not Empty
  RETURNS: a list of all pairs (c, bc) where c is the character and bc is its respective Huffman code from htree
  EXAMPLES: codeLst (Node (Node (Leaf 'b' 1) 2 (Leaf 'a' 1)) 5 (Leaf 'c' 3)) ==
                         [('b',[False,False]),('a',[False,True]),('c',[True])]
-}
codeLst :: HuffmanTree -> BitCode -> [(Char, BitCode)]
-- VARIANT: (The amount of Nodes/Leaf in htree)
codeLst (Leaf c n) lst = [(c, lst)]
codeLst (Node l a r) lst = codeLst l (lst ++ [False]) ++ codeLst r (lst ++ [True])

{- fromList xs
  Given a list of (key,value)-tuples, it inserts all these values into a table.

  If there are multiple values for a given key in the list,
  the LAST value in the list is kept.
  RETURNS: a table with all key-value pairs of xs
  EXAMPLE: fromList [(1,1),(1,2)] == T [(1,2)]
-}
fromList :: Eq k => [(k,v)] -> Table k v
fromList = foldl (\t (k,v) -> Table.insert t k v) Table.empty

{- encode h s
   encodes a huffmanTree from the given string
   PRE: All characters in s appear in h
   RETURNS: the concatenation of the characters of s encoded using the Huffman code table of h.

   EXAMPLES: encode (Node (Leaf 'a' 2) 4 (Leaf 'b' 2)) "abba" == [False,True,True,False]
             encode (Leaf 'a' 2) "aa" == []
             encode Empty "" == []
 -}
encode :: HuffmanTree -> String -> BitCode
-- VARIANT: length s
encode hTree ""  = []
encode hTree (x:xs) = (getBitCode hTree x) ++ encode hTree xs


{- getBitCode hTree chr
  gets the input characters corresponding Huffman code
  PRE: chr must be in hTree, hTree cant be Empty
  RETURNS : the Huffman code of chr in htree
  EXAMPLES:
    getBitCode (Node (Node (Leaf 'b' 1) 2 (Leaf 'a' 1)) 5 (Leaf 'c' 3)) 'c' == [True]
    getBitCode (Node (Node (Leaf 'b' 1) 2 (Leaf 'a' 1)) 5 (Leaf 'c' 3)) 'b' == [False, False]
    getBitCode (Node (Node (Leaf 'b' 1) 2 (Leaf 'a' 1)) 5 (Leaf 'c' 3)) 'a' == [False, True]
-}
getBitCode :: HuffmanTree -> Char -> BitCode
getBitCode hTree chr = let Just x = Table.lookup (codeTable hTree) chr in x



{- compress s
   Compresses the given string
   RETURNS: (a Huffman tree based on s, the Huffman coding of s under this tree)

   EXAMPLES: compress "abba" == (Node (Leaf 'a' 2) 4 (Leaf 'b' 2), [False,True,True,False])
             compress "aaa" == (Leaf 'a' 3, [])
             compress "" == (Empty, [])
 -}
compress :: String -> (HuffmanTree, BitCode)
compress str = (hTree, encode hTree str)
  where hTree = huffmanTree ( characterCounts str)


{- decompress h bits
   decompresses the compressed string
   PRE:  bits is a concatenation of valid Huffman code words for h
   RETURNS: the decoding of bits under h

   EXAMPLES: decompress (huffmanTree (characterCounts "abba")) [False,True,True,False] = "abba"
             decompress Empty [] = ""
             decompress (Leaf 'a' 3) [] = "aaa" 
 -}
decompress :: HuffmanTree -> BitCode -> String
-- VARIANT: variant for decompress (Leaf c n) is length n 
decompress (Leaf c 0) [] = ""
decompress (Leaf c n) [] = c : decompress (Leaf c (n-1)) [] 
decompress hTree bc = decompressAux hTree hTree bc

{- decompressAux t1 t2 bitcode
   Goes through the huffmanTree according to the BitCode
   and creates a string of all chars in correct order
   PRE: The given BitCode must be correlated with the given hTree
   RETURNS: The String that was compressed within the given hTree & BitCode

   EXAMPLES: decompressAux (Node (Leaf 'a' 2) 4 (Leaf 'b' 2)) (Node (Leaf 'a' 2) 4 (Leaf 'b' 2)) [False,True,True,False] = "abba"
             decompressAux Empty Empty [] = ""
-}
decompressAux :: HuffmanTree -> HuffmanTree -> BitCode -> String
-- VARIANT: length bitcode
decompressAux _ (Leaf c n) [] = [c]
decompressAux _ _ [] = ""
decompressAux hTree (Leaf c n) xs = c : decompressAux hTree hTree xs
decompressAux hTree (Node l a r) (False:xs) = decompressAux hTree l xs
decompressAux hTree (Node l a r) (True:xs) = decompressAux hTree r xs



--------------------------------------------------------------------------------
-- Test Cases
-- You may add your own test cases here:
-- Follow the pattern and/or read about HUnit on the interwebs.
--------------------------------------------------------------------------------

-- characterCounts
test1 = TestCase $ assertEqual "characterCounts"
            (Just 7) (Table.lookup (characterCounts "this is an example of a huffman tree") ' ')

-- codeTable
-- while the precise code for ' ' may vary, its length (for the given example string) should always be 3 bits
test2 = TestCase $ assertEqual "codeTable"
            3 (maybe (-1) length (Table.lookup (codeTable (huffmanTree (characterCounts "this is an example of a huffman tree"))) ' '))

-- compress
-- while the precise code for the given example string may vary, its length should always be 135 bits
test3 = TestCase $ assertEqual "compress"
            135 (length (snd (compress "this is an example of a huffman tree")))

-- decompress
test4 =
    let s = "this is an example of a huffman tree"
    in
      TestCase $ assertEqual ("decompress \"" ++ s ++ "\"")
        s (let (h, bits) = compress s in decompress h bits)

test5 =
    let s = "xxx"
    in
      TestCase $ assertEqual ("decompress \"" ++ s ++ "\"")
        s (let (h, bits) = compress s in decompress h bits)

test6 =
    let s = ""
    in
      TestCase $ assertEqual ("decompress \"" ++ s ++ "\"")
        s (let (h, bits) = compress s in decompress h bits)

-- for running all the tests
runtests = runTestTT $ TestList [test1, test2, test3, test4, test5, test6]