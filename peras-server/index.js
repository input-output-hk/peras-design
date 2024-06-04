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
    const blockId = mkBlockId(block);
    if (network.body.data.nodes.get(blockId) === null) {
      const parentId = mkBlockHashId(block.parentBlock);
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

  function mkPartyId(party) {
    return `party:${party}`;
  }

  function mkBlockId(block) {
    return `block:${block.signature}`;
  }

  function mkBlockHashId(hash) {
    return `block:${hash}`;
  }

  function mkCertId(party, round) {
    return `cert:${party}:${round}`;
  }

  function mkCertPrimeId(party) {
    return `certPrime:${party}`;
  }

  function mkCertStarId(party) {
    return `certStar:${party}`;
  }

  const genesisBlockId = "block:0000000000000000";

  const genesisCertId = "cert:0:0";

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
        {
          console.log("Protocol", msg.parameters);
          network.body.data.nodes.add({ font: { multi: 'html' }, id: genesisBlockId , level: nextLevel() , shape: 'box', label : "<b>Genesis</b>" });
          network.body.data.nodes.add({ font: { multi: 'html', size: 12 }, id: genesisCertId, level: nextLevel() , shape: 'box', color: 'lightgray', label: "Genesis\ncertificate" });
          network.body.data.edges.add({ id: genesisCertId, from: genesisCertId, to: genesisBlockId, hidden: true });
          const nParties = parseInt(document.getElementById('uiParties').value)
          for (let party = 1; party <= nParties; party++) {
            const id = mkPartyId(party);
            const certPrimeId = mkCertPrimeId(party);
            const certStarId = mkCertStarId(party);
            const label = `Node: <i>${party}</i>`;
            network.body.data.nodes.update({ font: { multi: 'html', color: 'white' , size: 12}, id, level: currentLevel , shape: 'circle', color: 'tomato', label })
            network.body.data.edges.update({ id, from: id, to: genesisBlockId, color: 'tomato', dashes: true });
            network.body.data.edges.update({ font: {color: 'tomato'}, id: certPrimeId, from: id, to: genesisCertId, color: 'hotpink' , dashes: true, label: "cert′"});
            network.body.data.edges.update({ font: {color: 'tomato'}, id: certStarId, from: id, to: genesisCertId, color: 'deeppink' , dashes: true, label: "cert*"});
          }
        }
        break;
      case "Tick":
	currentSlot = msg.slot;
	currentRound = msg.roundNumber;
        slot.textContent = '' + msg.slot;
        roundNumber.textContent = '' + msg.roundNumber;
        break;
      case "NewChainAndVotes":
        console.log("NewChainAndVotes", msg.parameters);
        // No drawing required.
        break;
      case "NewChainPref":
        {
          const id = mkPartyId(msg.partyId);
          const label = `Node: <i>${msg.partyId}</i>`;
          network.body.data.nodes.update({ font: { multi: 'html', color: 'white' , size: 12}, id, level: currentLevel , shape: 'circle', color: 'tomato', label });
          network.body.data.edges.update({ font: { color: "tomato"}, id, from: id, to: mkBlockId(msg.newChainPref[0]), color: 'tomato', dashes: true, label: "tip" });
        }
        break;
      case "NewCertificatesReceived":
        console.log("NewCertificatesReceived", msg.partyId, msg.newCertificates);
        // No drawing required.
        break;
      case "NewCertificatesFromQuorum":
        msg.newQuorums.forEach(function (cert) {
          const id = mkCertId(msg.partyId, cert.round);
          const label = `Certificate\nround: <i>${cert.round}</i>\nnode: <i>${msg.partyId}</i>`;
          network.body.data.nodes.update({ font: { multi: 'html', size: 12 }, id, level: nextLevel() , shape: 'box', color: 'lightgray', label });
          network.body.data.edges.update({ id, from: id, to: mkBlockHashId(cert.blockRef), color: 'lightgray' , dashes: true });
        });
        break;
      case "NewCertPrime":
        {
          const certPrimeId = mkCertPrimeId(msg.partyId);
          const certId = mkCertId(msg.partyId, msg.newCertPrime.round);
          const partyId = mkPartyId(msg.partyId);
          const label = "cert′";
          network.body.data.edges.update({ font: {color: 'tomato'}, id: certPrimeId, from: partyId, to: certId, color: 'hotpink' , dashes: true, label });
          refresh();
        }
        break;
      case "NewCertStar":
        {
          const certStarId = mkCertStarId(msg.partyId);
          const certId = mkCertId(msg.partyId, msg.newCertStar.round);
          const partyId = mkPartyId(msg.partyId);
          const label = "cert*";
          network.body.data.edges.update({ font: {color: 'tomato'}, id: certStarId, from: partyId, to: certId, color: 'deeppink' , dashes: true, label });
          refresh();
        }
        break;
      case "CastVote":
        const blockId = mkBlockHashId(msg.vote.blockHash);
        const label = `Vote\nround: <i>${msg.vote.votingRound}</i>\ncreator: <i>${msg.vote.creatorId}</i>`;
        network.body.data.nodes.add({ font: { multi: 'html' , size: 12}, id: msg.vote.signature, level: nextLevel() , shape: 'circle', color: "skyblue", label });
        network.body.data.edges.add({ from: msg.vote.signature, to: blockId , dashes: true , color: "skyblue" });
        refresh();
        break;
      case "PreagreementBlock":
        console.log("PreagreementBlock", msg.partyId, msg.block, msg.weight);
        break;
      case "PreagreementNone":
        console.log("PreagreementNone", msg.partyId);
        break;
      case "ForgingLogic":
        {
          const id = mkPartyId(msg.partyId);
          const label = `${msg.partyId}`;
          createBlock(msg.block);
          network.body.data.edges.update({ id, from: id, to: mkBlockId(msg.block), color: 'tomato', dashes: true });
          refresh();
        }
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
