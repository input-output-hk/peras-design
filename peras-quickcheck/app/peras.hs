import Peras.Abstract.Protocol.Network (runNetwork)
import Peras.Abstract.Protocol.Trace (perasTracer)

main :: IO ()
main =
  runNetwork perasTracer >>= print
