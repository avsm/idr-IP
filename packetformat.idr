include "IPDSL.idr";

-- Simple packet format - a 2 bit version number which must be 1, then
-- a null-terminated string (which is going to be inconveniently
-- aligned, but we'll deal with that...) which must be shorter than 16
-- characters. 

do using (BIND, CHUNK) {
  simplePacket : PacketFormat;
  simplePacket = Packet do {
      ver <- bits 2;
      fact (p_bool (value ver == 1));
      str <- CString;
      fact (p_bool (strLen str < 16));
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
sendData x with (choose (strLen x < 16)) {
    | Right p =  BInt 1 oh ## oh ## x ## p ## II;
    | Left  p = BInt 1 oh ## oh ## "String too long" ## oh ## II;
}

getData : mkTy simplePacket -> String;
getData (_ ## _ ## x ## _ ## _) = x;
