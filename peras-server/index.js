document.addEventListener('DOMContentLoaded', () => {
  const node = document.getElementById('chain');
  const slot = document.getElementById('slot');
  const roundNumber = document.getElementById('roundNumber');

  // retrieve simulation data from server
  const wsPath = window.location.pathname.split('/').slice(0, -1).join('/');
  const ws = new WebSocket("ws://" + window.location.hostname + ":" + window.location.port + wsPath);

  const nodes = [];
  const edges = [];
  const data = { nodes, edges };

  const network = new vis.Network(node, data, {
    nodes: {
      shape: 'dot',
      size: 20,
      font: {
        size: 20,
        color: '#000000',
      },
    },
    edges: {
      width: 2,
      color: '#000000',
    },
    layout: {
      hierarchical: {
        direction: 'LR',
      },
    },
  });


  // handle incoming traces from the server
  // | Protocol {parameters :: PerasParams}
  // | Tick {slot :: SlotNumber, roundNumber :: RoundNumber}
  // | NewChainAndVotes {partyId :: PartyId, newChains :: Set Chain, newVotes :: Set Vote}
  // | NewChainPref {partyId :: PartyId, newChainPref :: Chain}
  // | NewCertificatesReceived {partyId :: PartyId, newCertificates :: [(Certificate, SlotNumber)]}
  // | NewCertificatesFromQuorum {partyId :: PartyId, newQuorums :: [Certificate]}
  // | NewCertPrime {partyId :: PartyId, newCertPrime :: Certificate}
  // | NewCertStar {partyId :: PartyId, newCertStar :: Certificate}
  // | CastVote {partyId :: PartyId, vote :: Vote}
  // | PreagreementBlock {partyId :: PartyId, block :: Block, weight :: VotingWeight}
  // | PreagreementNone {partyId :: PartyId}
  // | ForgingLogic {partyId :: PartyId, bc1a :: Bool, bc1b :: Bool, bc1c :: Bool}
  // | VotingLogic {partyId :: PartyId, vr1a :: Bool, vr1b :: Bool, vr2a :: Bool, vr2b :: Bool}
  // | DiffuseChain {partyId :: PartyId, chain :: Chain}
  // | DiffuseVote {partyId :: PartyId, vote :: Vote}
  function handleMessage(msg) {
    switch (msg.tag) {
      case "Protocol":
        console.log("Protocol", msg.parameters);
        break;
      case "Tick":
        slot.textContent = '' + msg.slot;
        roundNumber.textContent = '' + msg.roundNumber;
        break;
      case "NewChainAndVotes":
        if (msg.newChains.length > 0) {
          msg.newChains.forEach(chain => {
            const blockId = chain[0].signature;
            const parentId = chain[0].parentBlock;
            network.body.data.nodes.add({ id: blockId, label: blockId });
            network.body.data.edges.add({ from: blockId, to: parentId });
          });
          network.redraw();
        }
        break;
      case "NewChainPref":
        console.log("NewChainPref", msg.partyId, msg.newChainPref);
        break;
      case "NewCertificatesReceived":
        console.log("NewCertificatesReceived", msg.partyId, msg.newCertificates);
        break;
      case "NewCertificatesFromQuorum":
        console.log("NewCertificatesFromQuorum", msg.partyId, msg.newQuorums);
        break;
      case "NewCertPrime":
        console.log("NewCertPrime", msg.partyId, msg.newCertPrime);
        break;
      case "NewCertStar":
        console.log("NewCertStar", msg.partyId, msg.newCertStar);
        break;
      case "CastVote":
        console.log("CastVote", msg.partyId, msg.vote);
        break;
      case "PreagreementBlock":
        console.log("PreagreementBlock", msg.partyId, msg.block, msg.weight);
        break;
      case "PreagreementNone":
        console.log("PreagreementNone", msg.partyId);
        break;
      case "ForgingLogic":
        console.log("ForgingLogic", msg.partyId, msg.bc1a, msg.bc1b, msg.bc1c);
        break;
      case "VotingLogic":
        console.log("VotingLogic", msg.partyId, msg.vr1a, msg.vr1b, msg.vr2a, msg.vr2b);
        break;
      case "DiffuseChain":
        console.log("DiffuseChain", msg.partyId, msg.chain);
        break;
      case "DiffuseVote":
        console.log("DiffuseVote", msg.partyId, msg.vote);
        break;
      default:
        console.log("Unknown message", msg);
    }
  }

  ws.onopen = function() {
    console.log('connected');
  };

  ws.onmessage = function(message) {
    if (message.data) {
      const eb = JSON.parse(message.data);
      handleMessage(eb);
    }
  };

  window.onbeforeunload = _ => {
    ws.close();
  };

  ws.onclose = function() {
    console.log('disconnected');
  };

});

async function postJSON(url, data) {
  try {
    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify(data),
    });

    const result = await response.json();
    console.log("Success:", result);
  } catch (error) {
    console.error("Error:", error);
  }
}
