
'use strict'


import * as d3  from "d3"
import {jStat} from "jstat"

let resultData = []

function pNoHonestQuorum(tau, committeeSize, totalStake, adversaryStakeFraction) {
  const quorum = tau * committeeSize
  const beta = committeeSize / totalStake
  const honestStake = (1 - adversaryStakeFraction) * totalStake
  return jStat.binomial.cdf(quorum, honestStake, beta)
}

function pEvolve(n, p, q, s0, k) {
  function adv(s) {
    const s1 = new Array(n + 2).fill(0)
    for (let k = 0; k < n + 2; ++k) {
      if (k == 0) {
        s1[0] = (1 - p) * q * s[1] + s[0]
      } else {
        let x = ((1 - p) * (1 - q) + p * q) * s[k]
        if (k > 1)
            x += p * (1 - q) * s[k-1]
        if (k < n + 1)
            x += (1 - p) * q * s[k+1]
        s1[k] = x
      }
    }
    return s1
  }
  let s = s0.slice()
  for (let i = 0; i < k; ++ i)
    s = adv(s)
  return s
}

function pPreRollback (adversaryStakeFraction, activeSlotCoefficient, U, L) {
  const n = U + L
  const p = 1 - (1 - activeSlotCoefficient)**(1 - adversaryStakeFraction)
  const q = 1 - (1 - activeSlotCoefficient)**adversaryStakeFraction
  let s = new Array(n + 2).fill(0)
  s[1] = 1
  return pEvolve(n, p, q, s, n)
}

function pPostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L, B) {
  const n = U + L
  const p = 1 - (1 - activeSlotCoefficient)**(1 - adversaryStakeFraction)
  const q = 1 - (1 - activeSlotCoefficient)**adversaryStakeFraction
  let s = new Array(n + 2).fill(0)
  s[1] = 1
  s = pEvolve(n, p, q, s, n)
  let s2 = new Array(n + 2).fill(0)
  for (let k = B + 1; k < n + 2; ++k)
    s2[k] = s[k-B]
  const sum = s2.reduce((acc, x) => acc + x, 0)
  s = s2.map(x => x / sum)
  return pEvolve(n, p, q, s, 1000)
}

function pPostRollbackNet(tau, committeeSize, totalStake, adversaryStakeFraction, activeSlotCoefficient, U, L, B) {
    const p0 = pPreRollback(adversaryStakeFraction, activeSlotCoefficient, U, L)
    const pB = pPostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L, B)
    const pNQ = pNoHonestQuorum(tau, committeeSize, totalStake, adversaryStakeFraction)
    return p0[0] * pNQ + pB[0] * (1 - pNQ)
}

function appendTable(data) {
  const tr = d3.select("#uiResultTable").append("tr")
  for (let i = 0; i < data.length; ++i) {
    const td = tr.append("td")
    const x = data[i]
    td.html(() => i > 6 ? x.toExponential(4) : x.toString())
  }
}

export function reset() {
  resultData = []
  d3.select("#uiResultTable").selectAll("tr").remove()
}

export function calculate() {
  const tau = parseFloat(uiTau.value)
  const committeeSize = parseInt(uiCommittee.value)
  const totalStake = 1000000
  const adversaryStakeFraction = parseFloat(uiAdversary.value)
  const activeSlotCoefficient = parseFloat(uiAlpha.value)
  const U = parseInt(uiU.value)
  const L = parseInt(uiL.value)
  const B = parseInt(uiB.value)
  const pPostBoost = pPostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L, B)[0]
  const pPre = pPreRollback(adversaryStakeFraction, activeSlotCoefficient, U, L)[0]
  const pPost = pPostRollbackNet(tau, committeeSize, totalStake, adversaryStakeFraction, activeSlotCoefficient, U, L, B)
  const pNoQuorum = pNoHonestQuorum(tau, committeeSize, totalStake, adversaryStakeFraction)
  uiPostBoost.innerText = pPostBoost.toExponential(4)
  uiPre.innerText = pPre.toExponential(4)
  uiPost.innerText = pPost.toExponential(4)
  uiNoQuorum.innerText = pNoQuorum.toExponential(4)
  const x = [
      B
    , U
    , L
    , committeeSize
    , tau
    , activeSlotCoefficient
    , adversaryStakeFraction
    , pPostBoost
    , pPre
    , pPost
    , pNoQuorum
  ]
  resultData.push(x)
  appendTable(x)
}

export async function initialize() {
  calculate()
}
