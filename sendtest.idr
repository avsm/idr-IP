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

fromJust : Maybe a -> IO a;
fromJust (Just x) = return x;
fromJust Nothing = do { putStrLn "FAIL";
	 	      	__Prove_Anything; };


main = do { let p = sendData ["Hello world", "Sossidges"];
       	    let pkt = marshal p;
	    dumpPacket pkt; 
	    dat <- (fromJust (unmarshal simplePacket pkt));
	    dumpData dat;
	    conn <- TCPConnect "localhost" 3456;
	    send conn pkt;
	    echop' <- recv conn;
	    echop <- getPkt echop';
	    closeSocket conn;
	  };
