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
    in the packet. "len" tells us how many bits we've got so far.
--}

  data Chunk : Set where
      bit : (width: Nat) -> Chunk
    | len : Chunk
    | prop : (P:Set) -> Chunk
    | end : Chunk;

{-- We'll want to convert Chunks to Idris types. "Fin" is a bounded number,
    so we get some guarantee that any data we have fits.
--}
 
  chunkTy : Chunk -> Set;
  chunkTy (bit w) = Fin (power (S (S O)) w);
  chunkTy len = Nat;
  chunkTy (prop P) = P;
  chunkTy end = ();

{-- "PacketLang" is parameterised over the type of the last thing in it.
    This means we can use do notation to pull out the values which will
    appear in actual data, and construct predicates on those values. --}

-- Section: The DSL

  data PacketLang : Set -> Set where
      CHUNK : (c:Chunk) -> PacketLang (chunkTy c)
    | BINDC : (c:Chunk) -> (chunkTy c -> PacketLang V) ->
              PacketLang V;

{-- If we really want "do" notation, better make "BINDC" more general.
    This just flattens nested blocks. --}

  BIND : PacketLang T -> (T -> PacketLang V) -> PacketLang V;
  BIND (CHUNK c) k = BINDC c k;
  BIND (BINDC c k) k' = BINDC c (\cv => BIND (k cv) k');

{-- And, so that we don't need to write down too many types, let's hide
    it. --}

  data PacketFormat : Set where
     Packet : (PacketLang T) -> PacketFormat;

{-- We'll want to convert our description of types into concrete types.
--}

  mkTy' : PacketLang T -> Set;
  mkTy' (CHUNK c) = chunkTy c;
  mkTy' (BINDC c k) = (x ** mkTy' (k x));

  mkTy : PacketFormat -> Set;
  mkTy (Packet p) = mkTy' p;

-- IGNORE
-- }
-- START

{-- A few bits and pieces to help notation... --}

syntax bits n = CHUNK (bit (intToNat n));
syntax fact n = CHUNK (prop n);
syntax offset = CHUNK len;

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
    which must be >2. We then ask for an offset and verify that we're
    where we think we are. Finally,  we have one more bit. --}

   simpleFormat : PacketFormat;
   simpleFormat = Packet
   		  do { x <- bits 4;
                       y <- bits (fInt x);
                       fact (LT (S (S O)) (fNat y)); 
		       bits 1;
                       t <- offset;
                       fact (t = (plus (S (S (S (S (S O))))) (fNat x)));
                       CHUNK end;
                     };
}

{-- Converting this to an Idris type, we get: --}

{->
Idris> mkTy simpleFormat
Sigma (Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))) (\ x : Fin (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))) => Sigma (Fin (power (S (S O)) (in' (natToInt (fNat x)<=0) O (natToInt (fNat x))))) (\ x0 : Fin (power (S (S O)) (in' (natToInt (fNat x)<=0) O (natToInt (fNat x)))) => Sigma (LT (S (S O)) (fNat x0)) (\ x1 : LT (S (S O)) (fNat x0) => Sigma Nat (\ x2 : Nat => Sigma (Fin (S (S O))) (\ x3 : Fin (S (S O)) => Sigma (x2=S (S (S (S (fNat x))))) (\ x4 : x2=S (S (S (S (fNat x)))) => Fin (S (S O)))))))) : Set

>-}


{-- ...which is not very readable. If the ugly printer was a  pretty 
printer which knew about syntactic sugar, it would say something like: --}

{->
(x:Fin 16 ** (y:Fin (power 2 x) ** (2<y ** (t:Nat ** (t==4+x) ** Fin 2))))
>-}

{-- Next step, which is probably much harder: generating functions which 
    can manipulate this type from the DSL! --}


bar : Sigma Nat (\n => Sigma Nat (Vect (Vect Int n)));
bar = Exists 
      (S O)
      (Exists
       O
       (VNil {A=Vect Int (S O)}));

foo : mkTy simpleFormat;
foo = Exists (fS (fS fO)) (
      Exists (fS (fS (fS fO))) (
      Exists (ltS (ltS ltO)) (
      Exists (fS fO) (
      Exists (S (S (S (S (S (S (S O))))))) (
      Exists (refl _) II)))));

-- foo = Exists (fS (fS fO)) ?; -- (ex (fS fO) ?);

{-      << fS (fS (fS fO)), 
      << ltS (ltS ltO),
      << (S (S (S (S (S (S O)))))), 
      << refl (S (S (S (S (S (S O)))))), 
         fO >> >> >> >> >>;
-}
