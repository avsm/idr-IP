include "bittwiddle.idr";

syntax Bound x = BInt x oh;

getPkt : Maybe Recv -> IO RawPacket;
getPkt Nothing = do { putStrLn "No reply!"; 
                      pkt <- newPacket 13;
                      return pkt;
};
getPkt (Just (mkRecv buf host port)) = do {
    putStrLn ("Ping from " ++ host ++ ":" ++ showInt port);
    return buf;
};

fromJust : Maybe a -> a;
fromJust (Just x) = x;

main = do { p <- newPacket 13;
       	    setField p 0 2 (Bound 1);
       	    setField p 2 6 (Bound 7);
       	    setField p 6 13 (Bound 127);
	    dumpPacket p; 
	    conn <- TCPConnect "localhost" 3456;
	    send conn p;
	    echop' <- recv conn;
	    echop <- getPkt echop';
	    closeSocket conn;

	    let v0 = value (fromJust (getField echop 0 2 oh));
	    let v1 = value (fromJust (getField echop 2 6 oh));
	    let v2 = value (fromJust (getField echop 6 13 oh));

	    putStrLn (showInt v0 ++ ", " ++ showInt v1 ++ ", " ++ showInt v2);
	  };
