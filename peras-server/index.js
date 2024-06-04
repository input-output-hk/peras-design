document.addEventListener('DOMContentLoaded', () => {
  const node = document.getElementById('chain');
  const slot = document.getElementById('slot');
  const roundNumber = document.getElementById('roundNumber');

  const simulate = document.getElementById('uiSimulate');
  simulate.addEventListener('click', () => {
    postJSON("/simulate", {
      duration: parseInt(document.getElementById('uiDuration').value)
      , parties: parseInt(document.getElementById('uiParties').value)
      , u: parseInt(document.getElementById('uiU').value)
      , a: parseInt(document.getElementById('uiA').value)
      , r: parseInt(document.getElementById('uiR').value)
      , k: parseInt(document.getElementById('uiK').value)
      , l: parseInt(document.getElementById('uiL').value)
      , tau: parseInt(document.getElementById('uiTau').value)
      , b: parseInt(document.getElementById('uiB').value)
      , delta: parseInt(document.getElementById('uiDelta').value)
      , activeSlots: parseFloat(document.getElementById('uiAlpha').value)
    })
  });

  const stop = document.getElementById('uiStop');
  stop.addEventListener('click', () => {
    req("/stop", "DELETE");
  });

  const pause = document.getElementById('uiPause');
  pause.addEventListener('click', () => {
    req("/pause", "PATCH");
  });

  const resume = document.getElementById('uiResume');
  resume.addEventListener('click', () => {
    req("/resume", "PATCH");
  });

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
      arrows:
        { to: { enabled: true, scaleFactor: 1, type: 'arrow' } },
    },
    layout: {
      hierarchical: {
        direction: 'LR',
      },
    },
  });

  function createBlock(block) {
    const blockId = block.signature;
    if (network.body.data.nodes.get(blockId) === null) {
      const parentId = block.parentBlock;
      const label = `<b>${blockId.substr(0, 8)}</b>\nslot: <i>${block.slotNumber}</i>\ncreator: <i>${block.creatorId}</i>`;
      network.body.data.nodes.add({ font: { multi: 'html' }, id: blockId, level : nextLevel() , shape: 'box', label });
      network.body.data.edges.add({ from: blockId, to: parentId });
    }
  }

  let currentLevel = 0;
  let currentSlot = 0;
  let currentRound = 0;
  let lastSlot = 0;
  let lastRound = 0;

  function nextLevel() {
    if (currentSlot != lastSlot) {
      currentLevel += 1;
      lastSlot = currentSlot;
      lastRound = currentRound;
    }
    return currentLevel;
  }

  function refresh() {
    network.fit();
  }

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
  // | ForgingLogic {partyId :: PartyId, bc1a :: Bool, bc1b :: Bool, bc1c :: Bool, block :: Block}
  // | VotingLogic {partyId :: PartyId, vr1a :: Bool, vr1b :: Bool, vr2a :: Bool, vr2b :: Bool}
  // | DiffuseChain {partyId :: PartyId, chain :: Chain}
  // | DiffuseVote {partyId :: PartyId, vote :: Vote}
  function handleMessage(msg) {
    switch (msg.tag) {
      case "Protocol":
        console.log("Protocol", msg.parameters);
        network.body.data.nodes.add({ font: { multi: 'html' }, id: "0000000000000000" , level: nextLevel() , shape: 'box', label : "<b>Genesis</b>" });
        break;
      case "Tick":
	currentSlot = msg.slot;
	currentRound = msg.roundNumber;
        slot.textContent = '' + msg.slot;
        roundNumber.textContent = '' + msg.roundNumber;
        break;
      case "NewChainAndVotes":
        if (msg.newChains.length > 0) {
          msg.newChains.forEach(chain => createBlock(chain[0]));
          refresh();
        }
        break;
      case "NewChainPref":
        if (network.body.data.nodes.get(msg.partyId) === null) {
          const label = `<b>Tip</b>\nnode: <i>${msg.partyId}</i>`;
          network.body.data.nodes.add({ font: { multi: 'html', color: 'white' , size: 12}, id: msg.partyId, level: currentLevel , shape: 'circle', color: 'tomato', label });
	} else {
          const label = `<b>Tip</b>\n<i>node: ${msg.partyId}</i>`;
          network.body.data.nodes.update({ font: { multi: 'html', color: 'white' , size: 12}, id: msg.partyId, level: currentLevel , shape: 'circle', color: 'tomato', label });
        }
        // we want a single edge from the party to the block which is their preferred chain
        network.body.data.edges.update({ id: msg.partyId, from: msg.partyId, to: msg.newChainPref[0].signature, color: 'tomato', dashes: true });
        break;
      case "NewCertificatesReceived":
        console.log("NewCertificatesReceived", msg.partyId, msg.newCertificates);
        break;
      case "NewCertificatesFromQuorum":
        console.log("NewCertificatesFromQuorum", msg.partyId, msg.newQuorums);
        break;
      case "NewCertPrime":
        const certPrimeId = `prime:${msg.partyId}`;
        const certPrimeLabel = `round: <i>${msg.newCertPrime.round}</i>\nparty: <i>${msg.partyId}</i>`;
        network.body.data.nodes.update({ font: { multi: 'html' }, id: certPrimeId, level: nextLevel() , shape: 'box', color: '#8cc474', label: certPrimeLabel });
        network.body.data.edges.update({ id: certPrimeId, from: certPrimeId, to: msg.newCertPrime.blockRef });
        break;
      case "NewCertStar":
        const certStarId = `star:${msg.partyId}`;
        const certStarLabel = `round: <i>${msg.newCertStar.round}</i>\nparty: <i>${msg.partyId}</i>`;
        network.body.data.nodes.update({ font: { multi: 'html' }, id: certStarId, level: nextLevel() , shape: 'box', color: '#b59543', label: certStarLabel });
        network.body.data.edges.update({ id: certStarId, from: certStarId, to: msg.newCertStar.blockRef });
        break;
      case "CastVote":
        const blockId = msg.vote.blockHash;
        const label = `Vote\nround: <i>${msg.vote.votingRound}</i>\ncreator: <i>${msg.vote.creatorId}</i>`;
        network.body.data.nodes.add({ font: { multi: 'html' , size: 12}, id: msg.vote.signature, level: nextLevel() , shape: 'circle', color: "lightgray", label });
        network.body.data.edges.add({ from: msg.vote.signature, to: blockId , dashes: true , color: "lightgray" });
        refresh();
        break;
      case "PreagreementBlock":
        console.log("PreagreementBlock", msg.partyId, msg.block, msg.weight);
        break;
      case "PreagreementNone":
        console.log("PreagreementNone", msg.partyId);
        break;
      case "ForgingLogic":
        if (network.body.data.nodes.get(msg.partyId) === null) {
          const label = `${msg.partyId}`;
          network.body.data.nodes.add({ font: { multi: 'html', color: 'red' }, id: msg.partyId, level: nextLevel() , shape: 'ellipse', label });
        }
        createBlock(msg.block);
        // we want a single edge from the party to the block which is their preferred chain
        network.body.data.edges.update({ id: msg.partyId, from: msg.partyId, to: msg.block.signature });
        refresh();
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

async function req(url, method) {
  try {
    const response = await fetch(url, {
      method: method
    });
    const result = await response.json();
    console.log("Success:", result);
  } catch (error) {
    console.error("Error:", error);
  }
}
