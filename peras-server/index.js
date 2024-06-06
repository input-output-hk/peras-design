document.addEventListener('DOMContentLoaded', () => {
  const setInputValue = (inputId, paramName, defaultValue = "error") => {
    const urlParams = new URLSearchParams(window.location.search);
    const value = urlParams.get(paramName) || defaultValue;
    document.getElementById(inputId).value = value;
  };

  const paramToInputMap = {
    duration: "uiDuration",
    parties: "uiParties",
    u: "uiU",
    a: "uiA",
    r: "uiR",
    k: "uiK",
    l: "uiL",
    b: "uiB",
    tau: "uiTau",
    n: "uiCommittee", 
    delta: "uiDelta",
    alpha: "uiAlpha",
    delayMicroseconds: "uiDelay",
    rngSeed: "uiSeed",
  };

  for (const paramName in paramToInputMap) {
    const inputId = paramToInputMap[paramName];
    const defaultValue = paramName != "rngSeed" ? document.getElementById(inputId).value : Math.round(Math.random() * 1000000000); 
    setInputValue(inputId, paramName, defaultValue); 
  }

  // This is needed to stop any prior simulations when refreshing the browser.
  req("/stop", "DELETE");

  const node = document.getElementById('chain');
  const slot = document.getElementById('slot');
  const roundNumber = document.getElementById('roundNumber');

  const simulate = document.getElementById('uiSimulate');
  simulate.addEventListener('click', () => {
    network.body.data.nodes.clear();
    network.body.data.edges.clear();
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
      , committee: parseInt(document.getElementById('uiCommittee').value)
      , delta: parseInt(document.getElementById('uiDelta').value)
      , activeSlots: parseFloat(document.getElementById('uiAlpha').value)
      , delayMicroseconds: Math.round(parseFloat(document.getElementById('uiDelay').value) * 1000000)
      , rngSeed: parseInt(document.getElementById('uiSeed').value)
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
    physics: {
      enabled: false,
    },
  });

  function createBlock(block) {
    const blockId = mkBlockId(block);
    if (network.body.data.nodes.get(blockId) === null) {
      const parentId = mkBlockHashId(block.parentBlock);
      const label = `<b>${block.signature.substr(0, 8)}</b>\nslot: <i>${block.slotNumber}</i>\ncreator: <i>${block.creatorId}</i>\n${cache["bl"]}`;
      const color = block.certificate ? "dodgerblue" : "skyblue";
      network.body.data.nodes.add({ font: { multi: 'html' }, id: blockId, level: nextLevel(), shape: 'box', color, label });
      network.body.data.edges.add({ from: blockId, to: parentId });
      if (block.certificate != null) {
        network.body.data.edges.add({ from: blockId, to: mkCertId(1, block.certificate.round), color });
      }
    }
  }

  function setStatus(message) {
    document.getElementById('uiMessage').innerText = message;
  }

  let currentLevel = 0;
  let currentSlot = 0;
  let currentRound = 0;
  let lastSlot = 0;
  let preagreementBlock = null;

  function nextLevel() {
    if (currentSlot != lastSlot) {
      currentLevel += 1;
      lastSlot = currentSlot;
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

  // FIXME: Consider the pros and cons.
  const collapseCerts = true;

  function mkCertId(party, round) {
    return collapseCerts ? `cert:1:${round}` : `cert:${party}:${round}`;
  }

  function mkCertPrimeId(party) {
    return `certPrime:${party}`;
  }

  function mkCertStarId(party) {
    return `certStar:${party}`;
  }

  function mkVoteId(vote) {
    return `vote:${vote.signature}`;
  }

  function mkCooldownId(party, round) {
    return `cool:${party}:${round}`;
  }

  const genesisBlockId = "block:0000000000000000";

  const genesisCertId = "cert:0:0";

  function logic(x) {
    return x ? "⊤" : "⊥";
  }

  const cache = {};

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
    console.debug(msg);
    setStatus(msg.tag);
    switch (msg.tag) {
      case "Protocol":
        {
          network.body.data.nodes.add({ font: { multi: 'html' }, id: genesisBlockId, level: nextLevel(), shape: 'box', color: "dodgerblue", label: "<b>Genesis</b>" });
          network.body.data.nodes.add({ font: { multi: 'html', size: 12 }, id: genesisCertId, level: nextLevel(), shape: 'box', color: 'turquoise', label: "Genesis\ncertificate" });
          network.body.data.edges.add({ id: genesisCertId, from: genesisCertId, to: genesisBlockId, color: "dodgerblue" });
          const nParties = parseInt(document.getElementById('uiParties').value);
          for (let party = 1; party <= nParties; party++) {
            const id = mkPartyId(party);
            const certPrimeId = mkCertPrimeId(party);
            const certStarId = mkCertStarId(party);
            const label = `Node: <i>${party}</i>`;
            network.body.data.nodes.update({ font: { multi: 'html', color: 'white', size: 12 }, id, level: currentLevel, shape: 'circle', color: 'tomato', label });
            network.body.data.edges.update({ id, from: id, to: genesisBlockId, color: 'tomato', dashes: true });
            network.body.data.edges.update({ font: { color: 'tomato' }, id: certPrimeId, from: id, to: genesisCertId, color: 'hotpink', dashes: true, label: "cert′" });
            network.body.data.edges.update({ font: { color: 'tomato' }, id: certStarId, from: id, to: genesisCertId, color: 'deeppink', dashes: true, label: "cert*" });
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
        // No drawing required.
        break;
      case "NewChainPref":
        {
          const id = mkPartyId(msg.partyId);
          const label = `Node: <i>${msg.partyId}</i>`;
          network.body.data.nodes.update({ font: { multi: 'html', color: 'white', size: 12 }, id, level: currentLevel, shape: 'circle', color: 'tomato', label });
          network.body.data.edges.update({ font: { color: "tomato" }, id, from: id, to: mkBlockId(msg.newChainPref[0]), color: 'tomato', dashes: true, label: "tip" });
        }
        break;
      case "NewCertificatesReceived":
        // No drawing required.
        break;
      case "NewCertificatesFromQuorum":
        msg.newQuorums.forEach(function(cert) {
          const id = mkCertId(msg.partyId, cert.round);
          const label = collapseCerts ? `Certificate\nround: <i>${cert.round}</i>` : `Certificate\nround: <i>${cert.round}</i>\nnode: <i>${msg.partyId}</i>`;
          network.body.data.nodes.update({ font: { multi: 'html', size: 12 }, id, level: nextLevel() , shape: 'box', color: 'turquoise', label });
          network.body.data.edges.update({ id, from: id, to: mkBlockHashId(cert.blockRef), color: 'turquoise' , dashes: true });
        });
        break;
      case "NewCertPrime":
        {
          const certPrimeId = mkCertPrimeId(msg.partyId);
          const certId = mkCertId(msg.partyId, msg.newCertPrime.round);
          const partyId = mkPartyId(msg.partyId);
          const label = "cert′";
          network.body.data.nodes.update({ font: { multi: 'html', color: 'white', size: 12 }, id: partyId, level: currentLevel, shape: 'circle', color: 'tomato', label: `Node: <i>${msg.partyId}</i>` });
          network.body.data.edges.update({ font: { color: 'tomato' }, id: certPrimeId, from: partyId, to: certId, color: 'hotpink', dashes: true, label });
          refresh();
        }
        break;
      case "NewCertStar":
        {
          const certStarId = mkCertStarId(msg.partyId);
          const certId = mkCertId(msg.partyId, msg.newCertStar.round);
          const partyId = mkPartyId(msg.partyId);
          const label = "cert*";
          network.body.data.nodes.update({ font: { multi: 'html', color: 'white', size: 12 }, id: partyId, level: currentLevel, shape: 'circle', color: 'tomato', label: `Node: <i>${msg.partyId}</i>` });
          network.body.data.edges.update({ font: { color: 'tomato' }, id: certStarId, from: partyId, to: certId, color: 'deeppink', dashes: true, label });
          refresh();
        }
        break;
      case "CastVote":
        {
          const blockId = mkBlockHashId(msg.vote.blockHash);
          const label = `Vote\nround: <i>${msg.vote.votingRound}</i>\ncreator: <i>${msg.vote.creatorId}</i>\n${cache["vl"]}`;
          network.body.data.nodes.add({ font: { multi: 'html', size: 12 }, id: mkVoteId(msg.vote), level: nextLevel(), shape: 'circle', color: "sandybrown", label });
          network.body.data.edges.add({ from: mkVoteId(msg.vote), to: blockId, dashes: true, color: "sandybrown" });
          refresh();
        }
        break;
      case "PreagreementBlock":
        preagreementBlock = msg.block;
        // Nothing to draw.
        break;
      case "PreagreementNone":
        // Nothing to draw.
        break;
      case "ForgingLogic":
        {
	  cache["bl"] = `${logic(msg.bc1a)}${logic(msg.bc1b)}${logic(msg.bc1c)}`;
          const id = mkPartyId(msg.partyId);
          createBlock(msg.block);
          network.body.data.edges.update({ id, from: id, to: mkBlockId(msg.block), color: 'tomato', dashes: true });
          refresh();
        }
        break;
      case "VotingLogic":
	cache["vl"] = `${logic(msg.vr1a)}${logic(msg.vr1b)}${logic(msg.vr2a)}${logic(msg.vr2b)}`;
        if (!(msg.vr1a && msg.vr1b || msg.vr2a && msg.vr2b)) {
          const blockId = mkBlockId(preagreementBlock);
          const cooldownId = mkCooldownId(msg.partyId, currentRound);
          const label = `Cooldown\nround: <i>${currentRound}</i>\nparty: <i>${msg.partyId}</i>\n${cache["vl"]}`;
          network.body.data.nodes.add({ font: { multi: 'html', color: 'white', size: 12 }, id: cooldownId, level: nextLevel(), shape: 'ellipse', color: "darkkhaki", label });
          network.body.data.edges.add({ from: cooldownId, to: blockId, dashes: true, color: "darkkhaki" });
          refresh();
        }
        break;
      case "DiffuseChain":
        // Nothing to draw.
        break;
      case "DiffuseVote":
        // Nothing to draw.
        break;
      default:
        console.warn("Unknown message", msg);
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

  // Randomize button
  const randomizeButton = document.getElementById("randomizeButton");

  randomizeButton.addEventListener("click", () => {

      const parameterValues = {
          uiDuration: { input: document.getElementById("uiDuration"), },
          uiParties: { input: document.getElementById("uiParties") },
          uiU: { input: document.getElementById("uiU") },
          uiA: { input: document.getElementById("uiA")},
          uiR: { input: document.getElementById("uiR") },
          uiK: { input: document.getElementById("uiK")},
          uiL: { input: document.getElementById("uiL")},
          uiB: { input: document.getElementById("uiB")},
          uiTau: { input: document.getElementById("uiTau")},
          uiCommittee: { input: document.getElementById("uiCommittee")},
          uiDelta: { input: document.getElementById("uiDelta") },
          uiAlpha: { input: document.getElementById("uiAlpha") },
          uiSeed: { input: document.getElementById("uiSeed") },
      };
      const getRandomInt = (min, max) => Math.floor(Math.random() * (max - min + 1)) + min;
      const getRandomFloat = (min, max, step) => {
        const numSteps = Math.floor((max - min) / step) + 1;
        const randomStep = Math.floor(Math.random() * numSteps);
        return min + randomStep * step;
      };
  
      for (const param in parameterValues) {
          const { input } = parameterValues[param];
  
          if (input.type === 'number') {
              const min = parseFloat(input.min) || 0;  
              const max = parseFloat(input.max) || 100;
              const step = parseFloat(input.step) || 1; 
  
              if (step === 1) {
                input.value = getRandomInt(min, max); 
              } else {
                input.value = getRandomFloat(min, max, step).toFixed(2); 
              }
          }
      }

  });

  // Share link generation
  const shareButton = document.getElementById("shareButton");
  const shareLinkContainer = document.getElementById("shareLink");

  shareButton.addEventListener("click", () => {
      const baseUrl = `${self.location.origin}${self.location.pathname}`;
      const params = [];

      params.push(`duration=${document.getElementById("uiDuration").value}`);
      params.push(`parties=${document.getElementById("uiParties").value}`);
      params.push(`u=${document.getElementById("uiU").value}`);
      params.push(`a=${document.getElementById("uiA").value}`);
      params.push(`r=${document.getElementById("uiR").value}`);
      params.push(`k=${document.getElementById("uiK").value}`);
      params.push(`l=${document.getElementById("uiL").value}`);
      params.push(`b=${document.getElementById("uiB").value}`);
      params.push(`tau=${document.getElementById("uiTau").value}`);
      params.push(`n=${document.getElementById("uiCommittee").value}`);
      params.push(`delta=${document.getElementById("uiDelta").value}`);
      params.push(`alpha=${document.getElementById("uiAlpha").value}`);
      params.push(`delayMicroseconds=${document.getElementById("uiDelay").value}`);
      params.push(`rngSeed=${document.getElementById("uiSeed").value}`);

      const shareUrl = `${baseUrl}?${params.join("&")}`;

      shareLinkContainer.innerHTML = `<a href="${shareUrl}">${shareUrl}</a>`;
  });

  // Toggle parameters field
  const toggleChevron = document.getElementById("toggleParams");
  const parameterFields = document.getElementById("parameterFields");
  parameterFields.style.display = "grid";

  toggleChevron.addEventListener("click", () => {
    if (parameterFields.style.display === "grid") { 
      parameterFields.style.display = "none";
      toggleChevron.classList.remove("up");
      toggleChevron.classList.add("down");
  } else {
      parameterFields.style.display = "grid";
      toggleChevron.classList.remove("down");
      toggleChevron.classList.add("up");
  }
  });
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
    console.error("Error: %o", error);
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
    console.error("Error: %o", error);
  }
}
