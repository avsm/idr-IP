-- Some proofs about primitive operations - we just have to trust these.

-- Not that this is actually true if x+y overflows! Whole thing works
-- under the assumption that it doesn't.

ltAdd : (y:Int) -> (so (y>0)) -> so (x+y >= x);
ltAdd y = __Prove_Anything;

addSub : (x:Int) -> (y:Int) -> (x = ((y + x) - y));
addSub = __Prove_Anything;
