include "bittwiddle.idr";

processPacket : Maybe Recv -> IO ();
processPacket Nothing = putStrLn "Nothing received";
processPacket (Just (mkRecv buf host port)) = do {
      dumpPacket buf;
      putStrLn ("Received from " ++ host ++ ":" ++ showInt port);
};

recvLoop : Socket -> IO ();
recvLoop conn = do {
	 acc <- TCPAccept conn;
         d <- recv acc;
         processPacket d;
	 closeSocket acc;
         recvLoop conn;
};

runReceiver : (port:Int) -> IO ();
runReceiver port = do {
            conn <- TCPListen port 5;
            recvLoop conn;
};

main : IO ();
main = runReceiver 3456;
