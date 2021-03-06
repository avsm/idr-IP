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

    'Cstring' is a null-terminated C string. 'Lstring' is a string
    with an explicit length.
--}

  infixl 5 :+:;

  data Chunk : Set where
      bit : (width: Int) -> (so (width>0)) -> Chunk
    | options : (width: Int) -> (so (width>0)) -> List Int -> Chunk
    | Cstring : Chunk
    | Lstring : Int -> Chunk
    | len : Chunk
    | prop : (P:Prop) -> Chunk
    | (:+:) : Chunk -> Chunk -> Chunk
    | seq : Chunk -> Chunk
    | end : Chunk;

{-- We'll want to convert Chunks to Idris types. "Fin" is a bounded number,
    so we get some guarantee that any data we have fits.
--}

  chunkTy : Chunk -> Set;
  chunkTy (bit w p) = Bounded (1 << w);
  chunkTy (options w p xs) = Option (1 << w) xs;
  chunkTy Cstring = String;
  chunkTy (Lstring i) = String; -- maybe a length proof too?
  chunkTy len = Int;
  chunkTy (prop P) = propTy P;
  chunkTy (a :+: b) = (chunkTy a & chunkTy b);
  chunkTy (seq c) = List (chunkTy c);
  chunkTy end = ();

{-- Calculate number of bits needed in the packet data for a chunk: --}

  chunkLength : (t:Chunk) -> chunkTy t -> Int;
  chunkLength (bit w p) _ = w;
  chunkLength (options w p _) _ = w;
  chunkLength Cstring p = 8 * (strLen p + 1); -- Null terminated
  chunkLength (Lstring i) _ = 8 * i; -- Not null terminated
  chunkLength len _ = 0;
  chunkLength (prop p) _ = 0;
  chunkLength (a :+: b) x = chunkLength a (fst x) + chunkLength b (snd x);
  chunkLength (seq c) Nil = 0;
  chunkLength (seq c) (Cons y ys) 
      = chunkLength c y + chunkLength (seq c) ys;
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

  -- GROUP allows sub-sections of a packet format to be grouped together.

  data PacketLang : Set -> Set where
      CHUNK : (c:Chunk) -> PacketLang (chunkTy c)
    | IF : Bool -> PacketLang T -> PacketLang T -> PacketLang T
    | (//) : PacketLang T -> PacketLang T -> PacketLang T
    | GROUP : PacketLang () -> PacketLang ()
    | LIST : PacketLang () -> PacketLang ()
    | LISTN : Nat -> PacketLang () -> PacketLang ()
    | SEQ : PacketLang () -> PacketLang V -> PacketLang V
    | BINDC : (c:Chunk) -> (chunkTy c -> PacketLang V) ->
              PacketLang V;

{-- If we really want "do" notation, better make "BINDC" more general.
    This just flattens nested blocks. --}

  BIND : PacketLang T -> (T -> PacketLang V) -> PacketLang V;
  BIND (CHUNK c) k = BINDC c k;
  BIND (IF x t e) k = IF x (BIND t k) (BIND e k);
  BIND (l // r) k = (BIND l k) // (BIND r k);
  BIND (GROUP g) k = SEQ (GROUP g) (k II);
  BIND (LIST g) k = SEQ (LIST g) (k II);
  BIND (LISTN i g) k = SEQ (LISTN i g) (k II);
  BIND (SEQ c kf) k = SEQ c (BIND kf k);
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
  mkTy' (GROUP t) = mkTy' t;
  mkTy' (l // r) = Either (mkTy' l) (mkTy' r);
  mkTy' (LIST x) = List (mkTy' x);
  mkTy' (LISTN i x) = Vect (mkTy' x) i;
  mkTy' (SEQ v k) = (x : mkTy' v ** mkTy' k);
  mkTy' (BINDC c k) = (x ** mkTy' (k x));

  mkTy : PacketFormat -> Set;
  mkTy (Packet p) = mkTy' p;

{-- Calculate the number of bits required to store the data in a packet. --}

  bitLength' : {p:PacketLang T} -> mkTy' p -> Int;
  
  bitLength' {p=CHUNK c} d = chunkLength c d;
  bitLength' {p=IF True t e} d = bitLength' {p=t} d;
  bitLength' {p=IF False t e} d = bitLength' {p=e} d;
{-  bitLength' {p=IF x t e} d 
    = depIfV {P=\x => mkTy' (IF x t e)} x d
                   (\pt => bitLength' {p=IF True t e} d)
		   (\pe => bitLength' {p=IF False t e} d); -}
  bitLength' {p = GROUP g} d = bitLength' {p=g} d;
  bitLength' {p = l // r} d
    = either d (\l => bitLength' l) (\r => bitLength' r);
  bitLength' {p = LIST x} Nil = 0;
  bitLength' {p = LIST x} (Cons y ys) 
      = (bitLength' {p=x} y) + (bitLength' {p=LIST x} ys);
  bitLength' {p = LISTN _ x} VNil = 0;
  bitLength' {p = LISTN _ x} (y :: ys) 
      = (bitLength' {p=x} y) + (bitLength' {p=LISTN _ x} ys);
  bitLength' {p = SEQ v k} d
    = bitLength' (getSigIdx d) + bitLength' (getSigVal d);
  bitLength' {p=BINDC c k} d 
    = chunkLength c (getSigIdx d) + bitLength' (getSigVal d);

  bitLength : mkTy pf -> Int;
  bitLength {pf=Packet p} d = bitLength' d;

-- IGNORE
-- }
-- START

unmarshalChunk : (c:Chunk) -> Int -> RawPacket -> Maybe (chunkTy c);
unmarshalChunk (bit w p) pos pkt ?= 
      getField pkt pos (pos + w) (ltAdd w p);  [rewriteField]
unmarshalChunk (options w p xs) pos pkt 
      with unmarshalChunk (bit w p) pos pkt {
       | Nothing = Nothing;
       | Just jv = either (choose (validOption (value jv) xs))
                        (\lp => Nothing)
	                (\rp => Just (Opt jv rp)); 
}
unmarshalChunk Cstring pos pkt = getString pkt pos;
unmarshalChunk (Lstring i) pos pkt = getStringn pkt pos i;
unmarshalChunk len pos pkt = Just pos;
unmarshalChunk (prop p) pos pkt = testProp p;
unmarshalChunk (a :+: b) pos pkt 
     with unmarshalChunk a pos pkt {
         | Nothing = Nothing;
         | Just av with unmarshalChunk b (pos + chunkLength a av) pkt {
              | Nothing = Nothing;
	      | Just bv = Just (av, bv);
         }
}
unmarshalChunk (seq a) pos pkt
     with unmarshalChunk a pos pkt {
         | Nothing = Just Nil;
	 | Just v with unmarshalChunk (seq a) (pos + chunkLength a v) pkt {
              | Nothing = Nothing;
	      | Just vs = Just (Cons v vs);
         }        
}
unmarshalChunk end pos pkt = Just II;

unmarshal' : (p:PacketLang T) -> Int -> RawPacket -> Maybe (mkTy' p);
unmarshal' (CHUNK c) pos pkt = unmarshalChunk c pos pkt;
unmarshal' (IF True t e) pos pkt = unmarshal' t pos pkt;
unmarshal' (IF False t e) pos pkt = unmarshal' e pos pkt;
{-
    = depIf {P = \x => Maybe (mkTy' (IF x t e))} x
            (unmarshal' t pos pkt)
            (unmarshal' e pos pkt);
-}
unmarshal' (GROUP g) pos pkt = unmarshal' g pos pkt;
unmarshal' (l // r) pos pkt 
   = maybe (unmarshal' l pos pkt)
       (maybe (unmarshal' r pos pkt)
              Nothing
	      (\y => Just (Right y)))
       (\x => Just (Left x));
unmarshal' (LIST x) pos pkt
   = maybe (unmarshal' x pos pkt)
       (Just Nil)
       (\v => maybe (unmarshal' (LIST x) (pos + (bitLength' {pf=x} v)) pkt)
                (Just Nil)
		(\vs => Just (Cons v vs)));
unmarshal' (LISTN O x) pos pkt = Just VNil;
unmarshal' (LISTN (S k) x) pos pkt
   = maybe (unmarshal' x pos pkt)
       Nothing
       (\v => maybe (unmarshal' (LISTN k x) (pos + (bitLength' {pf=x} v)) pkt)
                Nothing
		(\vs => Just (v :: vs)));
unmarshal' (SEQ c k) pos pkt
   = maybe (unmarshal' c pos pkt) Nothing 
        (\v => maybe (unmarshal' k (pos + (bitLength' {pf=c} v)) pkt)
	             Nothing
		     (\kv => Just <| v, kv |>));
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
     	  -- putStrLn ((showInt pos) ++ ", " ++ (showInt (pos+w)) ++ ": " ++ showInt (value v'));
     	  return (pos+w); 
        };
marshalChunk (options w p xs) v pos pkt 
    = marshalChunk (bit w p) (bvalue v) pos pkt;
marshalChunk Cstring v pos pkt
   = do { setString pkt pos v;
     	  return (pos+((1 + strLen v) * 8));
        };
marshalChunk (Lstring i) v pos pkt
   = do { setStringn pkt pos v i;
     	  return (pos+(i * 8));
        };
marshalChunk len v pos pkt = return pos;
marshalChunk (prop p) v pos pkt = return pos;
marshalChunk (a :+: b) v pos pkt 
   = do { pos' <- marshalChunk a (fst v) pos pkt;
     	  marshalChunk b (snd v) pos pkt; };
marshalChunk (seq a) Nil pos pkt = return pos;
marshalChunk (seq a) (Cons x xs) pos pkt
   = do { pos' <- marshalChunk a x pos pkt;
     	  marshalChunk (seq a) xs pos' pkt; };
marshalChunk end v pos pkt = return pos;

marshal' : {p:PacketLang T} -> mkTy' p -> Int -> RawPacket -> IO Int;
marshal' {p=CHUNK c} v pos pkt = marshalChunk c v pos pkt;
marshal' {p=IF True t e} v pos pkt = marshal' {p=t} v pos pkt;
marshal' {p=IF False t e} v pos pkt = marshal' {p=e} v pos pkt;
{-
marshal' {p=IF x t e} v pos pkt 
     = depIfV {P=\x => mkTy' (IF x t e)} x v 
              (\vt => marshal' {p=t} vt pos pkt)
              (\ve => marshal' {p=e} ve pos pkt);
-}
marshal' {p=GROUP g} v pos pkt
     = marshal' {p=g} v pos pkt;
marshal' {p = l // r} v pos pkt
    = either v (\lv => marshal' lv pos pkt) 
               (\rv => marshal' rv pos pkt);
marshal' {p = LIST x} Nil pos pkt
    = return pos;
marshal' {p = LIST x} (Cons y ys) pos pkt
    = do { pos' <- marshal' {p=x} y pos pkt; 
      	   marshal' {p=LIST x} ys pos' pkt; };
marshal' {p = LISTN _ x} VNil pos pkt
    = return pos;
marshal' {p = LISTN _ x} (y :: ys) pos pkt
    = do { pos' <- marshal' {p=x} y pos pkt; 
      	   marshal' {p=LISTN _ x} ys pos' pkt; };
marshal' {p=SEQ c k} p pos pkt 
    = do { pos' <- marshal' {p=c} (getSigIdx p) pos pkt;
      	   marshal' {p=k} (getSigVal p) pos' pkt; 
         };
marshal' {p=BINDC c k} p pos pkt 
    = do { pos' <- marshalChunk c (getSigIdx p) pos pkt;
      	   marshal' (getSigVal p) pos' pkt; 
         };

marshal : {pf:PacketFormat} -> mkTy pf -> RawPacket;
marshal {pf = Packet p} v = unsafePerformIO
	    do { pkt <- newPacket (bitLength v);
	       	 -- putStrLn (showInt (bitLength v));
	      	 marshal' v 0 pkt; 
		 return pkt; 
               };

{-- A few bits and pieces to help notation... --}

syntax bits n = CHUNK (bit n oh);
syntax bitsp n = CHUNK (bit (value n) ?);
syntax fact n = CHUNK (prop n);
syntax offset = CHUNK len;
syntax CString = CHUNK Cstring;
syntax LString i = CHUNK (Lstring i);
syntax Options n xs = CHUNK (options n oh xs);

syntax Option x = Opt (BInt x oh) oh;

infixr 5 ## ;
syntax (##) x y = <| x, y |>;

{-- Note: Instead of the syntax stuff above, it would perhaps be
    better if Idris had a reflection mechanism which converted data
    declarations (which do look a bit like ABNF, as observed by
    Saleem) into a PacketFormat and generated the associated
    machinery. --}

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
