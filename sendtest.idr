include "packetformat.idr";

syntax Bound x = BInt x oh;

getPkt : Maybe Recv -> IO RawPacket;
getPkt Nothing = do { 
    putStrLn "No reply!"; 
    pkt <- newPacket 13;
    return pkt; };
getPkt (Just (mkRecv buf host port)) = do {
    putStrLn ("Ping from " ++ host ++ ":" ++ showInt port);
    return buf; };

fromJust : Maybe a -> a;
fromJust (Just x) = x;

main = do { let p = sendData "Hello there";
       	    let pkt = marshal p;
	    dumpPacket pkt; 
	    conn <- TCPConnect "localhost" 3456;
	    send conn pkt;
	    echop' <- recv conn;
	    echop <- getPkt echop';
	    closeSocket conn;

	    putStrLn (fst (getData (fromJust (unmarshal simplePacket echop))));
	  };
