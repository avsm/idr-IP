include "bittwiddle.idr";

processPacket : Socket -> Maybe Recv -> IO ();
processPacket acc Nothing = putStrLn "Nothing received";
processPacket acc (Just (mkRecv buf host port)) = do {
      dumpPacket buf;
      putStrLn ("Received from " ++ host ++ ":" ++ showInt port);
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
