import Peras.Abstract.Protocol.Environment (mkSimpleScenario)
import Peras.Abstract.Protocol.Network (runNetwork)
import Peras.Abstract.Protocol.Trace (perasTracer)

main :: IO ()
main = do
  mkSimpleScenario >>= runNetwork perasTracer >>= print
