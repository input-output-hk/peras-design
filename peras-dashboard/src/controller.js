
'use strict'


import * as d3  from "d3"
import {jStat} from "jstat"

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

let resultData = []

function appendTable(data) {
  const tr = d3.select("#uiResultTable").insert("tr", ":first-child")
  for (let i = 0; i < data.length; ++i) {
    const td = tr.append("td")
    const x = data[i]
    td.html(() => i > 6 ? x.toExponential(4) : x.toString())
  }
}

function highlightData(d) {
  let j = resultData.length - 1
  d3.select("#uiResultTable")
    .selectAll("tr")
    .each(function(r) {
      let found = true
      for (let i = 0; i < 7; ++i)
        found = found && d[i] == resultData[j][i]
      if (found)
        d3.select(this).style("color", "steelblue")
                       .style("background-color", "aliceblue")
      j = j - 1
    })
}

function clearHightlights() {
  d3.select("#uiResultTable")
    .selectAll("tr")
    .style("color", "black")
    .style("background-color", "white")
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
  plotData("#uiPlot1", 8, 9)
  plotData("#uiPlot2", 7, 10)
}

const plots = {
  "#uiPlot1" : null
, "#uiPlot2" : null
}

function setupPlot(el, xlab, ylab) {

  const margin = {top: 20, right: 30, bottom: 50, left: 60}
  const width = (uiRightPanel.clientWidth - 20) / 2 - margin.left - margin.right
  const height = uiTopPanel.clientHeight - margin.top - margin.bottom

  d3.select(el).selectAll("*").remove()
 
  const svg = d3.select(el)
                .attr("width", width + margin.left + margin.right)
                .attr("height", height + margin.top + margin.bottom)
                .append("g")
                .attr("transform", `translate(${margin.left},${margin.top})`)
  
  const xScale = d3.scaleLog().domain([1e-5, 1]).range([0, width])
  const yScale = d3.scaleLog().domain([1e-5, 1]).range([height, 0])
  const xAxis = d3.axisBottom(xScale).ticks(8, ".0e")
  const yAxis = d3.axisLeft(yScale).ticks(8, ".0e")

  const xAxisGroup = svg.append("g").attr("transform", `translate(0,${height})`)
  const yAxisGroup = svg.append("g")
  xAxisGroup.call(xAxis)
  yAxisGroup.call(yAxis)

  svg.append("text")
     .attr("class", "x axis-label")
     .attr("text-anchor", "middle")
     .attr("x", width / 2)
     .attr("y", height + margin.bottom - 10)
     .text(xlab)
  svg.append("text")
     .attr("class", "y axis-label")
     .attr("text-anchor", "middle")
     .attr("x", - height / 2)
     .attr("y", - margin.left + 15)
     .attr("transform", "rotate(-90)")
     .text(ylab)

  plots[el] = {
    svg : svg
  , xScale : xScale
  , yScale : yScale
  , xAxisGroup : xAxisGroup
  , yAxisGroup : yAxisGroup
  }
}

function plotData(el, i, j) {
  const svg = plots[el].svg
  const xScale = plots[el].xScale
  const yScale = plots[el].yScale
  const xAxisGroup = plots[el].xAxisGroup
  const yAxisGroup = plots[el].yAxisGroup

  function setScale(k) {
    const mn = d3.min(resultData, d => d[k])
    const mx = d3.max(resultData, d => d[k])
    if (false)
      return [
        10**Math.floor(Math.log10(mn))
      , 10**Math.ceil(Math.log10(mx))
      ]
    else
      return [mn / 2, mx * 2]
  }
  xScale.domain(setScale(i))
  yScale.domain(setScale(j))

  xAxisGroup.transition().duration(500).call(d3.axisBottom(xScale).ticks(8, ".0e"))
  yAxisGroup.transition().duration(500).call(d3.axisLeft(yScale).ticks(8, ".0e"))

  const previous = svg.selectAll("circle").data(resultData)
  previous.enter().append("circle")
          .attr("cx", d => xScale(d[i]))
          .attr("cy", d => yScale(d[j]))
          .attr("r", 3)
          .attr("fill", "steelblue")
          .on("mouseenter", (evt, d) => highlightData(d))
          .on("mouseout", () => clearHightlights())
          .merge(previous)
          .transition()
          .duration(500)
          .attr("cx", d => xScale(d[i]))
          .attr("cy", d => yScale(d[j]))
  previous.exit().remove()
}

export function reset() {
  resultData = []
  d3.select("#uiResultTable").selectAll("tr").remove()
  setupPlot("#uiPlot1", "Probability of a rollback in first U+L slots", "Probability of a rollback after surviving U+L slots")
  setupPlot("#uiPlot2", "Probability of a rollback after one boosting", "Probability of a round not reaching quorum")
}

export function updateParameters() {
  const B = parseFloat(uiB.value)
  const U = parseFloat(uiU.value)
  const activeSlotCoefficient = parseFloat(uiAlpha.value)
  const k = 2160 + 90 * B
  uiSecurity.value = Math.round(k)
  const A = 90 * B / activeSlotCoefficient
  uiA.value = Math.round(A)
  uiR.value = Math.round(A / U)
  uiK.value = Math.round(k / activeSlotCoefficient / U)
}

export async function initialize() {
  updateParameters()
  reset()
  calculate()
}
