-- Title: IP DSL
-- Author: Edwin Brady

include "bittwiddle.idr";
include "so_what.idr";

-- IGNORE
-- namespace IP {
-- START

-- Section Propositions

{-- We'll allow numbers within a packet to satisfy simple properties. 
    Less than, equal, and combinations of properties for now. --}

{-- The less than predicate: --}

  data LT : Nat -> Nat -> Set where
      ltO : LT O (S k)
    | ltS : LT n m -> LT (S n) (S m);

{-- A language of propositions: --}

  data Prop : Set where
      p_lt   : Nat -> Nat -> Prop
    | p_eq   : Nat -> Nat -> Prop
    | p_bool : Bool -> Prop
    | p_and  : Prop -> Prop -> Prop
    | p_or   : Prop -> Prop -> Prop;

{-- We can convert this language to propositions in Idris. We'll have
    less than and equality on natural numbers, and arbitrary booleans
    (which might arise from simple dynamic checks). --}

  propTy : Prop -> Set;
  propTy (p_lt x y) = LT x y;
  propTy (p_eq x y) = x=y;
  propTy (p_bool b) = so b;
  propTy (p_and s t) = (propTy s & propTy t); 
  propTy (p_or s t) = Either (propTy s) (propTy t);

{-- And we can test whether or not a proposition is true, and return a 
    proof of it, if it is true. --}

  mkLT : (x:Nat) -> (y:Nat) -> Maybe (LT x y);
  mkLT O (S k) = Just ltO;
  mkLT (S n) (S m) with mkLT n m {
     | Just p = Just (ltS p);
     | Nothing = Nothing;
  }
  mkLT _ _ = Nothing;

  mkEQ : (x:Nat) -> (y:Nat) -> Maybe (x = y);
  mkEQ O O = Just (refl _);
  mkEQ (S n) (S m) with mkEQ n m {
    mkEQ (S k) (S k) | Just (refl _) = Just (refl _);
                     | Nothing = Nothing;
  }
  mkEQ _ _ = Nothing;

  testProp : (p:Prop) -> Maybe (propTy p);
  testProp (p_lt x y) = mkLT x y;
  testProp (p_eq x y) = mkEQ x y;
  testProp (p_bool True) = Just oh;
  testProp (p_bool False) = Nothing;
  testProp (p_and s t) with testProp s {
      | Just sp with testProp t {
          | Just tp = Just (sp, tp);
          | Nothing = Nothing;
        }
      | Nothing = Nothing;
  }
  testProp (p_or s t) with testProp s {
      | Just sp = Just (Left sp);
      | Nothing with testProp t {
          | Just tp = Just (Right tp);
      }
  }

-- Section: Bits

{-- "Chunk" gives the types of data which can appear in our packet format.
    "bit" is a number of bits, and "prop" is some arbitrary predicate,
    which in practice would be a predicate on some other data appearing
    in the packet. "len" tells us how many bits we've got so far.
--}

  data Chunk : Set where
      bit : (width: Int) -> Chunk
    | len : Chunk
    | prop : (P:Prop) -> Chunk
    | end : Chunk;

{-- We'll want to convert Chunks to Idris types. "Fin" is a bounded number,
    so we get some guarantee that any data we have fits.
--}

  chunkTy : Chunk -> Set;
  chunkTy (bit w) = Bounded (1 << w);
  chunkTy len = Nat;
  chunkTy (prop P) = propTy P;
  chunkTy end = ();

{-- Calculate number of bits needed in the packet data for a chunk: --}

  chunkLength : Chunk -> Int;
  chunkLength (bit w) = w;
  chunkLength len = 0;
  chunkLength (prop p) = 0;
  chunkLength end = 0;

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

{-- Calculate the number of bits required to store the data in a packet. --}

  bitLength' : {p:PacketLang T} -> mkTy' p -> Int;
  bitLength' {p=CHUNK c} _ = chunkLength c;
  bitLength' {p=BINDC c k} <| x, p |> = chunkLength c + bitLength' p;

  bitLength : mkTy pf -> Nat;
  bitLength {pf=Packet p} d = bitLength' d;

-- IGNORE
-- }
-- START

data Bit = _O_ | _I_;

-- Parse a chunk. On success, return the result, and the rest of the
-- stream of bits.

unmarshalChunk : (c:Chunk) -> List Bit -> Maybe (chunkTy c & List Bit);

boundFin' : Bounded (1 << (y+(natToInt x)-y)) -> Fin (power (S (S O)) (S x));

unmarshal' : (p:PacketLang T) -> Int -> RawPacket -> Maybe (mkTy' p);
unmarshal' (CHUNK (bit (S l))) pos pkt = 
    let field = getField pkt pos (pos+(natToInt l)) (ltAdd _) in
        Just (boundFin' field);

{-- A few bits and pieces to help notation... --}

syntax bits n = CHUNK (bit (intToNat n));
syntax fact n = CHUNK (prop n);
syntax offset = CHUNK len;

fNat : Fin n -> Nat;
fNat fO = O;
fNat (fS k) = S (fNat k);

fInt : Fin n -> Int;
fInt k = natToInt (fNat k);

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
                       fact (p_lt (S (S O)) (fNat y)); 
		       bits 1;
                       t <- offset;
                       fact (p_eq t (plus (S (S (S (S (S O))))) (fNat x)));
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
