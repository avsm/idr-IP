-- Title: IP DSL
-- Author: Edwin Brady

include "bittwiddle.idr";

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

  -- Slightly odd to do it this way, but keeping x dynamic at the top
  -- means that partially evaluating testProp with a known expression
  -- can make the Prop structure go away.

  testProp (p_bool x) with x {
    testProp (p_bool True) | True = Just oh;
    testProp (p_bool False) | False = Nothing;
  }
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
      bit : (width: Int) -> (so (width>0)) -> Chunk
    | Cstring : Chunk
    | len : Chunk
    | prop : (P:Prop) -> Chunk
    | end : Chunk;

{-- We'll want to convert Chunks to Idris types. "Fin" is a bounded number,
    so we get some guarantee that any data we have fits.
--}

  chunkTy : Chunk -> Set;
  chunkTy (bit w p) = Bounded (1 << w);
  chunkTy Cstring = String;
  chunkTy len = Int;
  chunkTy (prop P) = propTy P;
  chunkTy end = ();

{-- Calculate number of bits needed in the packet data for a chunk: --}

  chunkLength : (t:Chunk) -> chunkTy t -> Int;
  chunkLength (bit w p) _ = w;
  chunkLength Cstring p = 8 * (strLen p + 1); -- Null terminated
  chunkLength len _ = 0;
  chunkLength (prop p) _ = 0;
  chunkLength end _ = 0;

{-- Helps with PE. We can do something depending on a conditional, statically,
    even if its value isn't known. But we need to fix up the types. The idea
    is that any evaluation that needs doing gets done *before* reaching 
    'depIfV'. --}

  depIfV : {P:Bool->Set} -> (x:Bool) -> 
       	  (value:P x) ->
	  |(t:P True -> T) -> |(e:P False -> T) -> T;
  depIfV True v t e = t v;
  depIfV False v t e = e v;

  depIf : {P:Bool->Set} -> (x:Bool) -> |(t:P True) -> |(e:P False) -> P x;
  depIf True t e = t;
  depIf False t e = e;

{-- "PacketLang" is parameterised over the type of the last thing in it.
    This means we can use do notation to pull out the values which will
    appear in actual data, and construct predicates on those values. --}

-- Section: The DSL

  infixl 5 // ;

  -- IF makes a choice based on some known data, and corresponds to a
  -- concrete type computed from that data.
  -- // makes a choice based on what parses, and corresponds to an
  -- 'Either' type. (i.e. it's alternation in ABNF)

  data PacketLang : Set -> Set where
      CHUNK : (c:Chunk) -> PacketLang (chunkTy c)
    | IF : Bool -> PacketLang T -> PacketLang T -> PacketLang T
    | (//) : PacketLang T -> PacketLang T -> PacketLang T
    | BINDC : (c:Chunk) -> (chunkTy c -> PacketLang V) ->
              PacketLang V;

{-- If we really want "do" notation, better make "BINDC" more general.
    This just flattens nested blocks. --}

  BIND : PacketLang T -> (T -> PacketLang V) -> PacketLang V;
  BIND (CHUNK c) k = BINDC c k;
  BIND (IF x t e) k = IF x (BIND t k) (BIND e k);
  BIND (l // r) k = (BIND l k) // (BIND r k) ;
  BIND (BINDC c k) k' = BINDC c (\cv => BIND (k cv) k');

{-- And, so that we don't need to write down too many types, let's hide
    it. --}

  data PacketFormat : Set where
     Packet : (PacketLang T) -> PacketFormat;

{-- We'll want to convert our description of types into concrete types.
--}

  mkTy' : PacketLang T -> Set;
  mkTy' (CHUNK c) = chunkTy c;
  mkTy' (IF x t e) = if x then (mkTy' t) else (mkTy' e);
  mkTy' (l // r) = Either (mkTy' l) (mkTy' r);
  mkTy' (BINDC c k) = (x ** mkTy' (k x));

  mkTy : PacketFormat -> Set;
  mkTy (Packet p) = mkTy' p;

{-- Calculate the number of bits required to store the data in a packet. --}

  bitLength' : {p:PacketLang T} -> mkTy' p -> Int;
  
  bitLength' {p=CHUNK c} d = chunkLength c d;
  bitLength' {p=IF x t e} d 
    = depIfV {P=\x => mkTy' (IF x t e)} x d
                   (\pt => bitLength' d)
		   (\pe => bitLength' d);
  bitLength' {p = l // r} d
    = either d (\l => bitLength' l) (\r => bitLength' r);
  bitLength' {p=BINDC c k} d = chunkLength c (getSigIdx d) + bitLength' (getSigVal d);

  bitLength : mkTy pf -> Int;
  bitLength {pf=Packet p} d = bitLength' d;

-- IGNORE
-- }
-- START

unmarshalChunk : (c:Chunk) -> Int -> RawPacket -> Maybe (chunkTy c);
unmarshalChunk (bit w p) pos pkt ?= 
      getField pkt pos (pos + w) (ltAdd w p);  [rewriteField]
unmarshalChunk Cstring pos pkt = getString pkt pos;
unmarshalChunk len pos pkt = Just pos;
unmarshalChunk (prop p) pos pkt = testProp p;
unmarshalChunk end pos pkt = Just II;

unmarshal' : (p:PacketLang T) -> Int -> RawPacket -> Maybe (mkTy' p);
unmarshal' (CHUNK c) pos pkt = unmarshalChunk c pos pkt;
unmarshal' (IF x t e) pos pkt 
    = depIf {P = \x => Maybe (mkTy' (IF x t e))} x
            (unmarshal' t pos pkt)
            (unmarshal' e pos pkt);
unmarshal' (l // r) pos pkt 
   = maybe (unmarshal' l pos pkt)
       (maybe (unmarshal' r pos pkt)
              Nothing
	      (\y => Just (Right y)))
       (\x => Just (Left x));
unmarshal' (BINDC c k) pos pkt 
   = maybe (unmarshalChunk c pos pkt) Nothing 
        (\v => maybe (unmarshal' (k v) (pos + chunkLength c v) pkt)
	             Nothing
		     (\kv => Just <| v, kv |>));
unmarshal : (p:PacketFormat) -> RawPacket -> Maybe (mkTy p);
unmarshal (Packet p) pkt = unmarshal' p 0 pkt;

marshalChunk : (c:Chunk) -> chunkTy c -> Int -> RawPacket -> IO Int;
marshalChunk (bit w p) v pos pkt 
   = let v' : Bounded (1 << ((pos+w)-pos)) = ? in
     do { setField pkt pos (pos + w) v';
     	  putStrLn ((showInt pos) ++ ", " ++ (showInt (pos+w)) ++ ": " ++ showInt (value v'));
     	  return (pos+w); 
        };
marshalChunk Cstring v pos pkt
   = do { setString pkt pos v;
     	  return (pos+(strLen v * 8));
        };
marshalChunk len v pos pkt = return pos;
marshalChunk (prop p) v pos pkt = return pos;
marshalChunk end v pos pkt = return pos;

marshal' : {p:PacketLang T} -> mkTy' p -> Int -> RawPacket -> IO Int;
marshal' {p=CHUNK c} v pos pkt = marshalChunk c v pos pkt;
marshal' {p=IF x t e} v pos pkt 
     = depIfV {P=\x => mkTy' (IF x t e)} x v 
              (\vt => marshal' {p=t} vt pos pkt)
              (\ve => marshal' {p=e} ve pos pkt);
marshal' {p = l // r} v pos pkt
    = either v (\lv => marshal' lv pos pkt) 
               (\rv => marshal' rv pos pkt);
marshal' {p=BINDC c k} p pos pkt 
    = do { pos' <- marshalChunk c (getSigIdx p) pos pkt;
      	   marshal' (getSigVal p) pos' pkt; 
         };

marshal : {pf:PacketFormat} -> mkTy pf -> RawPacket;
marshal {pf = Packet p} v = unsafePerformIO
	    do { pkt <- newPacket (bitLength v);
	       	 putStrLn (showInt (bitLength v));
	      	 marshal' v 0 pkt; 
		 return pkt; 
               };

{-- A few bits and pieces to help notation... --}

syntax bits n = CHUNK (bit n oh);
syntax bitsp n = CHUNK (bit (value n) ?);
syntax fact n = CHUNK (prop n);
syntax offset = CHUNK len;
syntax CString = CHUNK Cstring;

infixr 5 ## ;
syntax (##) x y = <| x, y |>;

do using (BIND, CHUNK) {
  testPacket : PacketFormat;
  testPacket = Packet do {
  	       	 ver <- bits 2; 
		 x <- bits 4;
		 fact (p_bool (value x > 0));
		 y <- bitsp x;
		 fact (p_bool (value ver == 1));
		 CHUNK end;
               };
}

rewriteField proof {
	%intro;
	%rewrite <- addSub w pos;
	%refine value;
	%qed;
};

testPacket_1 proof {
	%intro;
	%trivial;
	%qed;
};

marshalChunk_1 proof {
	%intro pkt, pos, w, p;
	%rewrite <- addSub w pos;
	%intro;
	%rewrite addSub w pos;
	%fill v;
	%qed;
};
