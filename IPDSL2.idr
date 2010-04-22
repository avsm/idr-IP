-- Title: IP DSL
-- Author: Edwin Brady

-- IGNORE
-- FIXME: put this is nat.idr and compile the int version

power : Nat -> Nat -> Nat;
power n O = S O;
power n (S k) = mult n (power n k);
--START

-- IGNORE
-- namespace IP {
-- START

-- Section: Bits

{-- "Chunk" gives the types of data which can appear in our packet format.
    "bit" is a number of bits, and "prop" is some arbitrary predicate,
    which in practice would be a predicate on some other data appearing
    in the packet. 
--}

  data Chunk : Nat -> Set where
      bit : (width: Nat) -> Chunk width
    | prop : (P:Set) -> Chunk O;

{-- We'll want to convert Chunks to Idris types. "Fin" is a bounded number,
    so we get some guarantee that any data we have fits.
--}
 
  chunkTy : Chunk n -> Set;
  chunkTy (bit w) = Fin (power (S (S O)) w);
  chunkTy (prop P) = P;

{-- "PacketLang" is parameterised over the type of the last thing in it.
    This means we can use do notation to pull out the values which will
    appear in actual data, and construct predicates on those values. 
    The "Nat" give the /total/ length in bits of a packet. --}

-- Section: The DSL

  data PacketLang : Nat -> Set -> Set where
      CHUNK : (c:Chunk w) -> PacketLang w (chunkTy c)
    | BINDC : (c:Chunk w) -> (chunkTy c -> PacketLang w' V) ->
              PacketLang (plus w w') V;

{-- If we really want "do" notation, better make "BINDC" more general.
    This just flattens nested blocks. --}

  BIND : PacketLang x T -> (T -> PacketLang y V) -> PacketLang (plus x y) V;
  BIND (CHUNK c) k = BINDC c k;
  BIND (BINDC {w} {w'} c k) k' ?= BINDC c (\cv => BIND (k cv) k'); [bindp]

{-- And, so that we don't need to write down too many types, let's hide
    it. --}

  data PacketFormat : Set where
     Packet : (PacketLang w T) -> PacketFormat;

{-- We'll want to convert our description of types into concrete types.
--}

  mkTy' : PacketLang w T -> Set;
  mkTy' (CHUNK c) = chunkTy c;
  mkTy' (BINDC c k) = (x:chunkTy c ** mkTy' (k x));

  mkTy : PacketFormat -> Set;
  mkTy (Packet p) = mkTy' p;

-- IGNORE
-- }
-- START

{-- A few bits and pieces to help notation... --}

bits = \n => CHUNK (bit (intToNat n));
syntax fact n = CHUNK (prop n);

fNat : Fin n -> Nat;
fNat fO = O;
fNat (fS k) = S (fNat k);

fInt : Fin n -> Int;
fInt k = natToInt (fNat k);

{-- Just a simple predicate --}

data LT : Nat -> Nat -> Set where
    ltO : LT O (S k)
  | ltS : LT n m -> LT (S n) (S m);

-- Section: Example

do using (BIND, CHUNK) {

{-- And a test: In this simple format, the first four bits specify the
    number of bits (x) for the next number. The next x bits give a number,
    which must be >2, then we have one more bit. --}

   simpleFormat : PacketFormat;
   simpleFormat = Packet do { x <- bits 4;
                              y <- bits (fInt x);
                              fact (LT (S (S O)) (fNat y)); 
                              bits 1; };
}

{-- Converting this to an Idris type, we get: --}

{->
Idris> mkTy simpleFormat
Sigma (Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))) (\ x : Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))) => Sigma (Fin (power (S (S O)) (in' (natToInt (fNat x)<=0) O (natToInt (fNat x))))) (\ x0 : Fin (power (S (S O)) (in' (natToInt (fNat x)<=0) O (natToInt (fNat x)))) => Sigma (LT (S (S O)) (fNat x0)) (\ x1 : LT (S (S O)) (fNat x0) => Fin (S (S O))))) : Set
>-}


{-- ...which is not very readable. If the ugly printer was a  pretty 
printer which knew about syntactic sugar, it would say something like: --}

{->
(x:Fin 16 ** (y:Fin (power 2 x) ** (2<y ** Fin 2)))
>-}

{-- Next step, which is probably much harder: generating functions which 
    can manipulate this type from the DSL! --}
