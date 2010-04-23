include "so_what.idr";

%include "bittwiddle.h"
%lib "bittwiddle.o"

-- First, the primitive versions using unsafe C call evilness.

-- A 32 bit integer.
data Int32 = I32 Ptr;

data RawPacket = RPkt Ptr Int;

f_mkInt32 = mkForeign (FFun "mkInt32"
	              (Cons FInt Nil) FPtr); [%eval]

f_getInt = mkForeign (FFun "getInt"
	   	     (Cons FPtr Nil) FInt); [%eval]

f_getBits = mkForeign (FFun "getBits"
	    	      (Cons FPtr (Cons FInt (Cons FInt Nil))) FPtr); [%eval]

f_setBits = mkForeign (FFun "setBits"
	    	      (Cons FPtr (Cons FInt (Cons FInt (Cons FInt Nil)))) 
		      FPtr); [%eval]

f_newPacket = mkForeign (FFun "newPacket"
                        (Cons FInt Nil) FPtr); [%eval]
f_dumpPacket = mkForeign (FFun "dumpPacket"
                         (Cons FPtr (Cons FInt Nil)) FUnit); [%eval]
f_setPacketBits = mkForeign (FFun "setPacketBits"
                            (Cons FPtr (Cons FInt (Cons FInt (Cons FInt Nil))))
			    FUnit); [%eval]
f_getPacketBits = mkForeign (FFun "getPacketBits"
                            (Cons FPtr (Cons FInt (Cons FInt Nil)))
			    FInt); [%eval]

f_setPacketString = mkForeign (FFun "setPacketString"
                            (Cons FPtr (Cons FInt (Cons FStr Nil)))
			    FUnit); [%eval]

newPacket : Int -> IO RawPacket;
newPacket l = do { p <- f_newPacket l;
	      	   return (RPkt p l); };

dumpPacket : RawPacket -> IO ();
dumpPacket (RPkt p l) = f_dumpPacket p l;

setPacketBits : RawPacket -> Int -> Int -> Int -> IO ();
setPacketBits (RPkt p l) s e dat = f_setPacketBits p s e dat;

getPacketBits : RawPacket -> Int -> Int -> IO Int;
getPacketBits (RPkt p l) s e = f_getPacketBits p s e;

mkInt32 : Int -> Int32;
mkInt32 x = I32 (unsafePerformIO (f_mkInt32 x));

getInt32 : Int32 -> Int;
getInt32 (I32 x) = unsafePerformIO (f_getInt x);

getBits' : Int32 -> Int -> Int -> Int32;
getBits' (I32 x) start end 
          = I32 (unsafePerformIO (f_getBits x start end));

setBits' : Int32 -> Int -> Int -> Int -> Int32;
setBits' (I32 x) start end new 
	  = I32 (unsafePerformIO (f_setBits x start end new));

-- Now the versions with nice types we actually want to use and export.

-- a 32 bit integer with an upper bound. (Bounded32 i gives an integer < i)

data Bounded32 : Int -> Set where
     B32 : (x:Int32) -> (so (getInt32 x < i)) -> Bounded32 i;

getBInt32 : Bounded32 i -> Int;
getBInt32 (B32 x p) = getInt32 x;

bound32Proof : (b:Bounded32 x) -> so ((getBInt32 b) < x);
bound32Proof (B32 x p) = p;

-- Yes, it's just 'elem'. Need type classes...

validOption : Int -> List Int -> Bool;
validOption x Nil = False;
validOption x (Cons y ys) = if x==y then True else (validOption x ys);

data Bounded : Int -> Set where
     BInt : (x:Int) -> (so (x<i)) -> Bounded i;

value : Bounded i -> Int;
value (BInt v _) = v;

data Option : Int -> List Int -> Set where
     Opt : (x:Bounded w) -> (so (validOption (value x) xs)) -> Option w xs;

ovalue : Option i xs -> Int;
ovalue (Opt (BInt v _) _) = v;

bvalue : Option i xs -> Bounded i;
bvalue (Opt b _) = b;

boundProof : (b:Bounded i) -> so ((value b) < i);
boundProof (BInt _ p) = p;

getField : RawPacket -> (start:Int) -> (end:Int) -> so (end>=start) -> 
	   Maybe (Bounded (1 << (end-start)));
getField (RPkt pkt len) start end _
   = if ((start<=len) && (end<=len)) then
       (Just 
         (BInt (unsafePerformIO (getPacketBits (RPkt pkt len) start (end-1))) 
           ?so_it_is))
       else Nothing;

-- These really need proofs that there is space in the packet rep. It's okay
-- if we go through the DSL interface though.

setField : RawPacket -> (start:Int) -> (end:Int) -> 
	   Bounded (1 << (end-start)) -> IO ();
setField pkt start end (BInt v _) = setPacketBits pkt start (end-1) v;

setString : RawPacket -> (start:Int) -> String -> IO ();
setString (RPkt pkt len) start v = f_setPacketString pkt start v;

-- Maybe better as a primitive in C?

getString' : RawPacket -> Int -> String -> Maybe String;
getString' pkt pos acc with getField pkt pos (pos+8) (ltAdd 8 oh) {
   | Just vin = let v = value vin in
     	        if (v==0) then (Just (strRev acc)) else
     	           (getString' pkt (pos+8) (strCons (__intToChar v) acc));
   | Nothing = Nothing;
}

getString : RawPacket -> Int -> Maybe String;
getString pkt pos = getString' pkt pos "";

boundFin : Bounded (1 << (natToInt x)) -> Fin (power (S (S O)) (S x));
	               
-- This arises from some C, which we can't prove anything about...
-- so we'll just have to trust it.

so_it_is proof {
	%intro;
	%refine __Prove_Anything;
	%qed;
};


-- Some networking glue

f_clientSocket = mkForeign (FFun "net_UDP_clientSocket"
	                 (Cons FStr (Cons FInt Nil)) FPtr); [%eval]
f_serverSocket = mkForeign (FFun "net_UDP_serverSocket"
	                 (Cons FInt Nil) FPtr); [%eval]
f_tcpSocket = mkForeign (FFun "net_TCP_socket"
	                 (Cons FStr (Cons FInt Nil)) FPtr); [%eval]
f_tcpListen = mkForeign (FFun "net_TCP_listen"
	                 (Cons FInt (Cons FInt Nil)) FPtr); [%eval]
f_tcpAccept = mkForeign (FFun "net_TCP_accept"
	                 (Cons FPtr Nil) FPtr); [%eval]
f_closeSocket = mkForeign (FFun "net_closeSocket"
	                  (Cons FPtr Nil) FUnit); [%eval]


f_sendUDP = mkForeign (FFun "net_sendUDP"
     (Cons FPtr (Cons FStr (Cons FInt (Cons (FAny RawPacket) Nil)))) 
     FInt); [%eval]
f_recvUDP = mkForeign (FFun "net_recvUDP"
		   (Cons FPtr Nil) FPtr); [%eval]

f_sendTCP = mkForeign (FFun "net_sendTCP"
     (Cons FPtr (Cons (FAny RawPacket) Nil))
     FInt); [%eval]
f_recvTCP = mkForeign (FFun "net_recvTCP"
		   (Cons FPtr Nil) FPtr); [%eval]

f_recvBuf = mkForeign (FFun "get_recvBuf"
		   (Cons FPtr Nil) (FAny RawPacket)); [%eval]
f_recvServer = mkForeign (FFun "get_recvServer"
		   (Cons FPtr Nil) FStr); [%eval]
f_recvPort = mkForeign (FFun "get_recvPort"
		   (Cons FPtr Nil) FInt); [%eval]

f_nullPtr = mkForeign (FFun "nullPtr" (Cons FPtr Nil) FInt); [%eval]

nullPtr : Ptr -> Bool;
nullPtr ptr = unsafePerformIO (
	      do { p <- f_nullPtr ptr;
		   return (if_then_else (p==1) True False);
                 });

data Socket = mkCon Ptr | noCon;

data Recv = mkRecv RawPacket String Int;

-- FIXME: Opening a socket might fail! Will return a null pointer if so.

clientSocket : String -> Int -> IO Socket;
clientSocket server port = do {
	     sock <- f_clientSocket server port;
	     if (nullPtr sock) then (return noCon) else
	                            (return (mkCon sock)); };

serverSocket : Int -> IO Socket;
serverSocket port = do {
	     sock <- f_serverSocket port;
	     if (nullPtr sock) then (return noCon) else 
                                    (return (mkCon sock)); };

TCPConnect : String -> Int -> IO Socket;
TCPConnect server port = do {
	     sock <- f_tcpSocket server port;
	     if (nullPtr sock) then (return noCon) else 
                                    (return (mkCon sock)); };

TCPListen : Int -> Int -> IO Socket;
TCPListen port maxcon = do {
	     sock <- f_tcpListen port maxcon;
	     if (nullPtr sock) then (return noCon) else 
	                            (return (mkCon sock)); };

TCPAccept : Socket -> IO Socket;
TCPAccept noCon = return noCon;
TCPAccept (mkCon s) = do {
	     sock <- f_tcpAccept s;
	     if (nullPtr sock) then (return noCon) else 
	                            (return (mkCon sock)); };

closeSocket : Socket -> IO ();
closeSocket noCon = return II;
closeSocket (mkCon s) = f_closeSocket s;

sendTo : Socket -> String -> Int -> RawPacket -> IO ();
sendTo noCon _ _ _ = return II;
sendTo (mkCon c) server port dat 
       = do { v <- f_sendUDP c server port dat;
	      return II; };

doMkRecv : Bool -> Ptr -> IO (Maybe Recv);
doMkRecv True _ = return Nothing;
doMkRecv False rcv = do {
	 buf <- f_recvBuf rcv;
	 server <- f_recvServer rcv;
	 port <- f_recvPort rcv;
	 return (Just (mkRecv buf server port));
};

recvFrom : Socket -> IO (Maybe Recv);
recvFrom noCon = return Nothing;
recvFrom (mkCon c) = do {
	 rcv <- f_recvUDP c;
	 doMkRecv (nullPtr rcv) rcv;
};

send : Socket -> RawPacket -> IO ();
send noCon dat = return II;
send (mkCon c) dat = do { v <- f_sendTCP c dat;
     	       	     	  return II; };

recv : Socket -> IO (Maybe Recv);
recv noCon = return Nothing;
recv (mkCon c) = do {
	 rcv <- f_recvTCP c;
	 doMkRecv (nullPtr rcv) rcv;
};

{-
x = 20;
y = 64;

main : IO ();
main = do { putStrLn (showInt (x << 2));
       	    putStrLn (showInt (y >> 3));
          };
-}

{-

-- Fin version, abandonded...

Word = \n => Fin (power (S (S O)) n);
Word32 = Word (intToNat 32);

-- Given an n+m+p bit number, pull out the m bits in the middle.
-- (i.e. call getBits' with n and m-1). We know that getBits' returns
-- a number with the right bounds, but it's external so we'll have to
-- cheat with the type!

getBits : (n:Nat) -> (m:Nat) ->
	  Word (plus (plus n m) p) -> 
	  Word m;
getBits n m num with getBits' (mkInt32 (finToInt num))
	                               (natToInt n) ((natToInt m)-1) {
   | x ?= intToFin (getInt32 x); [getBitsHack]
}

setBits : (n:Nat) -> (m:Nat) ->
	  Word (plus (plus n m) p) -> 
	  Word m ->
	  Word (plus (plus n m) p);
setBits n m num newnum with setBits' (mkInt32 (finToInt num))
	                             (natToInt n) ((natToInt m)-1)
				     (finToInt newnum) {
   | x ?= intToFin (getInt32 x); [setBitsHack]
}

-- We can do this as long as the external C code is correct. (Uh oh...)
getBitsHack proof {
  %intro; %believe value; %qed;
};

setBitsHack proof {
  %intro; %believe value; %qed;
};

-}
