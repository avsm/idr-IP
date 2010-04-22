include "bittwiddle.idr";

syntax Bound x = BInt x oh;

fromJust : Maybe a -> a;
fromJust (Just x) = x;

main = do { p <- newPacket 13;
       	    setField p 0 2 (Bound 1);
       	    setField p 2 6 (Bound 7);
       	    setField p 6 13 (Bound 127);
	    dumpPacket p; 
	    conn <- TCPConnect "127.0.0.1" 3456;
	    send conn p;
	    closeSocket conn;

	    let v0 = value (fromJust (getField p 0 2 oh));
	    let v1 = value (fromJust (getField p 2 6 oh));
	    let v2 = value (fromJust (getField p 6 13 oh));

	    putStrLn (showInt v0 ++ ", " ++ showInt v1 ++ ", " ++ showInt v2);
	  };
