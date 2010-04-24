include "packetformat.idr";

fromJust : Maybe a -> a;
fromJust (Just x) = x;

showIP : (Int & Int & Int & Int) -> String;
showIP (a,b,c,d) = showInt a ++ "." ++ showInt b ++ "." ++ 
       		   showInt c ++ "." ++ showInt d;

processPacket : Socket -> Maybe Recv -> IO ();
processPacket acc Nothing = putStrLn "Nothing received";
processPacket acc (Just (mkRecv buf host port)) = do {
      dumpPacket buf;
      let dat = (fromJust (unmarshal simplePacket buf));
      let strd = getData dat;
      let ip = getIP dat;
      putStrLn ("Received " ++ fst strd ++ ", " ++ showInt (snd strd)
                ++ " from " ++ host ++ ":" ++ showInt port);
      putStrLn ("Received " ++ showIP ip);
      send acc buf;
};

recvLoop : Socket -> IO ();
recvLoop conn = do {
	 acc <- TCPAccept conn;
	 fork ( do { d <- recv acc;
              	     processPacket acc d;
		     putStrLn "Gratuitous testing pause...";
		     sleep 10;
		     putStrLn "Pause done...";
	             closeSocket acc;
                   }
              );
         recvLoop conn;
};

runReceiver : (port:Int) -> IO ();
runReceiver port = do {
            conn <- TCPListen port 5;
            recvLoop conn;
};

main : IO ();
main = runReceiver 3456;
