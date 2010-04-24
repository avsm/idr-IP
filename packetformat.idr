include "IPDSL.idr";

cheese = 0;
biscuits = 1;
tea = 2;
coffee = 3;

-- Simple packet format - a 2 bit version number which must be 1, then
-- a null-terminated string (which is going to be inconveniently
-- aligned, but we'll deal with that...) which must be shorter than 16
-- characters. 

do using (BIND, CHUNK) {

  IPAddress = do { bits 8; bits 8; bits 8; bits 8; };

  syntax V x = BInt x oh;
  	      	  
  simplePacket : PacketFormat;
  simplePacket = Packet do {
      ver <- bits 2;
      fact (p_bool (value ver == 1));
      len <- bits 4;
      str <- LString (value len);
      Options 2 [cheese, biscuits, tea];
      IPAddress;
      CHUNK end;
  };
}

-- mkTy gives an Idris type for 'simplePacket' above, the ## separates
-- fields. 'oh' is a proof that some boolean test is done
-- statically. Obviously below we need to check that the given string
-- fits in 16 characters - 'choose' does that test and remembers the
-- result in a form that's usable as a proof.

-- choose : (x:Bool) -> Either (so (not x)) (so x);

-- a ## b ## c ... etc, is the unmarshalled form. 'sendData' and
-- 'getData' convert this from and to a type we might actually want to
-- work with.

sendData : String -> mkTy simplePacket;
sendData x with choose (strLen x < 16) {
   | Right p = BInt 1 oh ## oh ## BInt (strLen x) p ## x ## Option tea ## 
      	      	 V 129 ## V 234 ## V 200 ## V 100 ## II;

   -- truncate the string
   | Left p = BInt 1 oh ## oh ## BInt 15 oh ## x ## Option tea ## 
      	      	 V 129 ## V 234 ## V 200 ## V 100 ## II;
}

getData : mkTy simplePacket -> (String & Int);
getData (_ ## _ ## _ ## x ## teatime ## _ ## _ ## _ ## _ ## _) 
      = (x, ovalue teatime);

getIP : mkTy simplePacket -> (Int & Int & Int & Int);
getIP (_ ## _ ## _ ## _ ## _ ## a ## b ## c ## d ## _) 
    = (value a, value b, value c, value d);
