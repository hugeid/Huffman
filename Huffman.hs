-- DO NOT MODIFY THE FOLLOWING LINES

module Huffman(HuffmanTree, characterCounts, huffmanTree, codeTable, encode, compress, decompress) where

import Table
import PriorityQueue

import Test.HUnit
import Debug.Trace

{- a bit code (of a character or string) is represented by a list of Booleans
   INVARIANT:
     the bit code is a concatenation of (0 or more) valid code words for some Huffman tree
 -}
type BitCode = [Bool]

-- END OF DO NOT MODIFY ZONE

--------------------------------------------------------------------------------

{- characterCounts s
   RETURNS: a table that maps each character that occurs in s to the number of
         times the character occurs in s
   EXAMPLES:
 -}
characterCounts :: String -> Table Char Int
characterCounts = characterCounts' Table.empty

characterCounts' acc [] = acc
characterCounts' acc (x:xs)
  | Table.exists acc x = let Just c = Table.lookup acc x 
    in characterCounts' (Table.insert acc x (c+1)) xs

  | otherwise = characterCounts' (Table.insert acc x 1) xs


-- modify and add comments as needed
{- 
  INVARIANT: sub-trees with larger character counts do not occur at a lower level of the tree than
sub-trees with smaller character counts
-}
data HuffmanTree = Empty | Leaf Char Int | Node (HuffmanTree) Int (HuffmanTree) deriving Show
s = "this is an example of a huffman tree"
tree1 = (Node (Node (Leaf 'b' 1) 2 (Leaf 'a' 1)) 5 (Leaf 'c' 3)) -- [True, False, False, True, True]
tree2 = Node (Leaf 'b' 1) 3 (Node (Leaf 'a' 1) 2 (Leaf 'c' 1))

{- huffmanTree t
  iterates over all (key, value) pairs in t and adds them as HuffmanTrees into a PriorityQueue,
  merges the trees in the PriorityQueue in increasing order of priority into a single HuffmanTree.
   PRE:  t maps each key to a positive value
   RETURNS: a Huffman tree based on the character counts in t
   EXAMPLES: 
 -}
huffmanTree :: Table Char Int -> HuffmanTree 
huffmanTree t
  | null (toList t) = Empty
  | otherwise = hqmerge $ Table.iterate t hqinsert PriorityQueue.empty

{- hqinsert q (x, c)
  inserts a HuffmanTree that consists just of a leaf labeled with x and c into the priority queue, with priority c

  RETURNS: q but with the (Leaf x c, c) inserted 
-}
hqinsert :: PriorityQueue HuffmanTree -> (Char, Int) -> PriorityQueue HuffmanTree
hqinsert q (x,c) = PriorityQueue.insert q (Leaf x c, c)

{-hqmerge q
  Merges the HuffmanTrees in q into one tree, in increasing order of priority
  If there is only one tree in q, that tree is returned, otherwise it merges the trees until there is only one.
  RETURNS: A merged tree consisting of all the trees in q

-}
hqmerge :: PriorityQueue HuffmanTree -> HuffmanTree
hqmerge q 
  | PriorityQueue.is_empty $ snd $ least q = fst $ fst $ least q
  | otherwise = hqmerge $ hqmerge' q


{-hqmerge' q
  Helper function for hqmerge.
  Merges the two trees with least priority in q

  RETURNS: q but with the two trees with least priority merged into one tree.

-}
hqmerge' :: PriorityQueue HuffmanTree -> PriorityQueue HuffmanTree
hqmerge' q =
  let ((l1, p1), rest1) = least q 
  in 
    let ((l2, p2), rest2) = least rest1 
      in PriorityQueue.insert rest2 (Node l1 (p1+p2) l2, p1+p2)


{- codeTable h
   RETURNS: a table that maps each character in h to its Huffman code
   EXAMPLES:
 -}
codeTable :: HuffmanTree -> Table Char BitCode
codeTable Empty = Table.empty
codeTable hTree = fromList (codeLst hTree [])

--PRE: input tree is non empty
codeLst :: HuffmanTree -> BitCode -> [(Char, BitCode)]
codeLst (Leaf c n) lst = [(c, lst)]
codeLst (Node l a r) lst = codeLst l (lst ++ [False]) ++ codeLst r (lst ++ [True])

fromList :: Eq k => [(k,v)] -> Table k v
fromList = foldl (\t (k,v) -> Table.insert t k v) Table.empty

toList :: Table k v -> [(k, v)]
toList t = Table.iterate t (\a b -> b:a) []
{- encode h s
   PRE: All characters in s appear in h
   RETURNS: the concatenation of the characters of s encoded using the Huffman code table of h.
   EXAMPLES:
 -}
encode :: HuffmanTree -> String -> BitCode
--encode = undefined
encode hTree ""  = []
encode hTree (x:xs) = (getBitCode hTree x) ++ encode hTree xs

-- PRE: chr is in tree, tree is not Empty
getBitCode :: HuffmanTree -> Char -> BitCode
getBitCode hTree chr = let Just x = Table.lookup (codeTable hTree) chr in x




{- compress s
   RETURNS: (a Huffman tree based on s, the Huffman coding of s under this tree)
   EXAMPLES:
 -}
compress :: String -> (HuffmanTree, BitCode)
compress str = (hTree, encode hTree str)
  where hTree = huffmanTree ( characterCounts str)


{- decompress h bits
   PRE:  bits is a concatenation of valid Huffman code words for h
   RETURNS: the decoding of bits under h
   EXAMPLES:
 -}
decompress :: HuffmanTree -> BitCode -> String
decompress (Leaf c 0) [] = ""
decompress (Leaf c n) [] = c : decompress (Leaf c (n-1)) [] 
decompress hTree bc = decompressAux hTree hTree bc


decompressAux :: HuffmanTree -> HuffmanTree -> BitCode -> String
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


