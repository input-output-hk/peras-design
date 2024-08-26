
'use strict'


import {jStat} from "jstat"

export const jstat = jStat

export function pNoHonestQuorum(tau, committeeSize, totalStake, adversaryStakeFraction) {
  const quorum = tau * committeeSize
  const beta = committeeSize / totalStake
  const honestStake = (1 - adversaryStakeFraction) * totalStake
  return jStat.binomial.cdf(quorum, honestStake, beta)
}

export function pEvolve(n, p, q, s0, k) {
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

export function pPreBoostRollback (adversaryStakeFraction, activeSlotCoefficient, U, L) {
  const n = U + L
  const p = 1 - (1 - activeSlotCoefficient)**(1 - adversaryStakeFraction)
  const q = 1 - (1 - activeSlotCoefficient)**adversaryStakeFraction
  let s = new Array(n + 2).fill(0)
  s[1] = 1
  return pEvolve(n, p, q, s, n)
}

export function pPostBoostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L, B) {
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

export function pPostRollback(tau, committeeSize, totalStake, adversaryStakeFraction, activeSlotCoefficient, U, L, B) {
    const p0 = pPostBoostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L, 0)
    const pB = pPostBoostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L, B)
    const pNQ = pNoHonestQuorum(tau, committeeSize, totalStake, adversaryStakeFraction)
    return p0[0] * pNQ + pB[0] * (1 - pNQ)
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
  uiNoQuorum.innerText = pNoHonestQuorum(tau, committeeSize, totalStake, adversaryStakeFraction)
  uiPreBoost.innerText = pPreBoostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L)[0]
  uiPost.innerText = pPostRollback(tau, committeeSize, totalStake, adversaryStakeFraction, activeSlotCoefficient, U, L, B)
  uiPostBoost.innerText = pPostBoostRollback(adversaryStakeFraction, activeSlotCoefficient, U, L, B)[0]
}

export async function initialize() {
  calculate()
}
