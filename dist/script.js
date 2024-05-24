"use strict";

let canv, ctx; // canvas and context
let maxx, maxy; // canvas dimensions

let radius; // hexagons radius (and side length)
let grid; // array of hexagons
let nbx, nby; // grid size (in elements, not pixels)
let orgx, orgy;
let perx, pery, pergrid;
let colorMode = 0;
let globalHue;

// for animation
let messages;

// shortcuts for Math.
const mrandom = Math.random;
const mfloor = Math.floor;
const mround = Math.round;
const mceil = Math.ceil;
const mabs = Math.abs;
const mmin = Math.min;
const mmax = Math.max;

const mPI = Math.PI;
const mPIS2 = Math.PI / 2;
const mPIS3 = Math.PI / 3;
const m2PI = Math.PI * 2;
const m2PIS3 = (Math.PI * 2) / 3;
const msin = Math.sin;
const mcos = Math.cos;
const matan2 = Math.atan2;

const mhypot = Math.hypot;
const msqrt = Math.sqrt;

const rac3 = msqrt(3);
const rac3s2 = rac3 / 2;

//------------------------------------------------------------------------

function alea(mini, maxi) {
  // random number in given range

  if (typeof maxi == "undefined") return mini * mrandom(); // range 0..mini

  return mini + mrandom() * (maxi - mini); // range mini..maxi
}
// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
function intAlea(mini, maxi) {
  // random integer in given range (mini..maxi - 1 or 0..mini - 1)
  //
  if (typeof maxi == "undefined") return mfloor(mini * mrandom()); // range 0..mini - 1
  return mini + mfloor(mrandom() * (maxi - mini)); // range mini .. maxi - 1
}

function lerp(p0, p1, alpha) {
  return {
    x: p0.x * (1 - alpha) + p1.x * alpha,
    y: p0.y * (1 - alpha) + p1.y * alpha
  };
}
//------------------------------------------------------------------------

class ExtremeFilter {
  /* tracks extreme points to build a linear gradient in direction given by constructor
      let D the oriented straight line passing by (0,0) in direction D
      makes projection of filtered points on D
      keeps track of points whose projection has min and max abscissa on D
      */

  constructor(angle = 0) {
    this.min = Infinity;
    this.max = -Infinity;
    this.c = Math.cos(angle);
    this.s = Math.sin(angle);
  }

  filter(p) {
    let absc = p.x * this.c + p.y * this.s;
    if (absc < this.min) {
      this.min = absc;
      this.pmin = p;
    }
    if (absc > this.max) {
      this.max = absc;
      this.pmax = p;
    }
  } // filter

  filterArc(xc, yc, radius, starta, enda, ccw) {
    /* uses same signature as CanvasRenderingContext2D.arc
        does not accurately find extreme values, but filters a few points along the arc.
        Inaccuracy does not matter that much for a gradient
        */
    let x, y, a;
    // make angles increasing along arc
    if (ccw) [starta, enda] = [enda, starta];
    while (enda < starta) enda += m2PI;
    while (enda > starta + m2PI) enda -= m2PI;
    const ndiv = mceil((enda - starta) / 0.4); // vill divide arc in angles < 0.4 rad (0.4 : arbitrary value)
    if (ndiv == 0) ndiv = 1; // will do some extra work, but who cares ?
    for (let k = 0; k <= ndiv; ++k) {
      a = starta + (k * (enda - starta)) / ndiv;
      this.filter({ x: xc + radius * mcos(a), y: yc + radius * msin(a) });
    }
  } // filterArc

  getLinearGradient() {
    /* creates a gradient without filling the stop points */
    let delta = this.max - this.min;
    return ctx.createLinearGradient(
      this.pmin.x,
      this.pmin.y,
      this.pmin.x + delta * this.c,
      this.pmin.y + delta * this.s
    );
  }
} // ExtremeFilter

//------------------------------------------------------------------------
/* angles useful for the arcs */
const deltaAng0 = Math.acos(msqrt(2 / 3));
//    const deltaAng1 = mPIS3 - deltaAng0;

class Hexagon {
  constructor(kx, ky) {
    this.kx = kx;
    this.ky = ky;
    //        this.rot = intAlea(6); // random orientation
    this.rot = pergrid[ky % pery][kx % perx].rot;
    this.arcTypes = [];
    this.exits = [];
    this.turn = [];
    for (let k = 0; k < 6; ++k) {
      this.exits[(k + this.rot) % 6] = ([5, 4, 1, 2, 3, 0][k] + this.rot) % 6;
      this.turn[(k + this.rot) % 6] = [2, 0, 2, 2, 2, -2][k]; // in 1/6th of turn
      this.arcTypes[(k + this.rot) % 6] = ["l", "b", "b", "b", "b", "l"][k];
      /* encoding for arcTypes l/b = little/big */
    }

    this.size();
    this.lines = [];
  } // Hexagon.constructor

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  size() {
    // coordinates of centre
    this.xc = orgx + this.kx * 1.5 * radius;
    this.yc = orgy + this.ky * radius * rac3;
    if (this.kx & 1) this.yc -= radius * rac3s2; // odd columns, centre is a bit higher

    this.vertices = new Array(6).fill(0).map((v, k) => ({
      x: this.xc + radius * mcos(((k - 2) * mPI) / 3),
      y: this.yc + radius * msin(((k - 2) * mPI) / 3)
    }));
    this.vertices[6] = this.vertices[0]; // makes things easier by avoiding many "% 6" in calculating other calculations

    this.middle = new Array(6)
      .fill(0)
      .map((p, k) => lerp(this.vertices[k], this.vertices[k + 1], 0.5));

    this.extCenters = new Array(6).fill(0).map((v, k) => ({
      x: this.xc + rac3 * radius * mcos((k * mPI) / 3 - mPIS2),
      y: this.yc + rac3 * radius * msin((k * mPI) / 3 - mPIS2)
    }));
  } // Hexagon.prototype.size

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  drawLittleArc(kCenter) {
    ctx.beginPath();
    ctx.arc(
      this.vertices[kCenter].x,
      this.vertices[kCenter].y,
      radius / 2,
      (kCenter * mPI) / 3,
      (kCenter + 2) * mPIS3
    );
    ctx.stroke();
  }
  drawBigArc(kCenter) {
    ctx.beginPath();
    ctx.arc(
      this.extCenters[kCenter].x,
      this.extCenters[kCenter].y,
      1.5 * radius,
      ((kCenter + 1) * mPI) / 3,
      (kCenter + 2) * mPIS3
    );
    ctx.stroke();
  }
  // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  drawArcs() {
    let c, radius, a0, a1, ccw;
    ctx.lineWidth = 2;
    ctx.strokeStyle = "#fff";

    for (let k = 0; k < 6; ++k) {
      if ((k - this.rot + 6) % 6 == 5) continue;
      ({ c, radius, a0, a1, ccw } = this.getArcElements(k));
      ctx.beginPath();
      ctx.arc(c.x, c.y, radius, a0, a1, ccw);
      ctx.stroke();
    }
  } //Hexagon.prototype.drawArcs

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  getArcElements(kEntry) {
    // arcs are defined starting from kEntry

    // returns (center, radius, a0,a1, ccw)
    switch ((kEntry + 6 - this.rot) % 6) {
      case 0:
        return {
          c: this.vertices[this.rot],
          radius: 0.5 * radius,
          a0: this.rot * mPIS3,
          a1: (this.rot + 2) * mPIS3,
          ccw: false
        };

      case 1:
        return {
          c: this.extCenters[(this.rot + 2) % 6],
          radius: 1.5 * radius,
          a0: ((this.rot + 4) % 6) * mPIS3,
          a1: ((this.rot + 4) % 6) * mPIS3 - deltaAng0,
          ccw: true
        };

      case 2:
        return {
          c: this.extCenters[(this.rot + 3) % 6],
          radius: 1.5 * radius,
          a0: ((this.rot + 5) % 6) * mPIS3,
          a1: ((this.rot + 4) % 6) * mPIS3 + deltaAng0,
          ccw: true
        };

      case 3:
        return {
          c: this.extCenters[(this.rot + 2) % 6],
          radius: 1.5 * radius,
          a0: ((this.rot + 3) % 6) * mPIS3,
          a1: ((this.rot + 4) % 6) * mPIS3 - deltaAng0,
          ccw: false
        };

      case 4:
        return {
          c: this.extCenters[(this.rot + 3) % 6],
          radius: 1.5 * radius,
          a0: ((this.rot + 4) % 6) * mPIS3,
          a1: ((this.rot + 4) % 6) * mPIS3 + deltaAng0,
          ccw: false
        };

      case 5:
        return {
          c: this.vertices[this.rot],
          radius: 0.5 * radius,
          a0: (this.rot + 2) * mPIS3,
          a1: this.rot * mPIS3,
          ccw: true
        };
    }
  }

  getReverseArcElements(kExit) {
    const el = this.getArcElements(kExit);
    return { c: el.c, radius: el.radius, a0: el.a1, a1: el.a0, ccw: !el.ccw };
  } // getReverseArcElements

  getCrossingElements(kEntry, kExit) {
    /* returns array of 1 or 2 arcElements, suitably oriented */
    if (this.arcTypes[kEntry] == "l")
      // little arc: only one
      return [this.getArcElements(kEntry)];
    return [this.getArcElements(kEntry), this.getReverseArcElements(kExit)];
  } // getCrossingElements

  drawHexagon() {
    ctx.beginPath();
    this.vertices.forEach((p, k) => {
      if (k == 0) ctx.moveTo(p.x, p.y);
      else ctx.lineTo(p.x, p.y);
    });
    ctx.lineWidth = 0.25;
    ctx.strokeStyle = "#fff";
    ctx.stroke();
  } // Hexagon.prototype.drawHexagon

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  getNeighbor(edge) {
    const kx = this.kx + [0, 1, 1, 0, -1, -1][edge];
    const ky =
      this.ky +
      [
        [-1, 0, 1, 1, 1, 0],
        [-1, -1, 0, 1, 0, -1]
      ][this.kx & 1][edge];
    if (kx < 0 || kx >= nbx || ky < 0 || ky >= nby) return false;
    return grid[ky][kx];
  }
} //class Hexagon
//-----------------------------------------------------------------------------
class Hierarchy {
  constructor(item) {
    this.item = item;
    this.children = [];
  }
  isDeeper(other) {
    // "other" is deeper than "this" ?
    /* "deeper" means "inside" in the context of nesting loops */
    /* to build hierarchy : returns true if other must be in this's chidren (or grandchildren)
         returning false DOES NOT imply that other.isDeeper(this) returns true : they may be siblings or not directly related
        */
    if (!this.item) return true; // "this" is top of hierarchy, all others are lower
    return ctx.isPointInPath(
      this.item.path,
      other.item.refP.x,
      other.item.refP.y
    );
  }

  insert(other) {
    /* must be called only if isDeeper(other) returns true (actually checked, or this is top) */
    for (let k = 0; k < this.children.length; ++k) {
      if (this.children[k].isDeeper(other)) {
        // belongs to a child
        this.children[k].insert(other);
        return;
      }
    }
    // see if other is any of my children's ancestor
    for (let k = this.children.length - 1; k >= 0; --k) {
      if (other.isDeeper(this.children[k]))
        other.insert(this.children.splice(k, 1)[0]);
    }
    this.children.push(other);
  }

  inDepth(func) {
    if (this.item) func(this.item);
    this.children.forEach((child) => child.inDepth(func));
  }
} // class hierarchy
//-----------------------------------------------------------------------------
function createHierarchy(lines) {
  /* relies on the path2D an refP created when loop was created - assumes getPath2D(loop,alpha) was not called since then */
  let top = new Hierarchy(null);
  lines.forEach((line) => top.insert(new Hierarchy(line)));
  return top;
}
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
function makeLine(cell, kEntry) {
  /* lines are determined when hexagons are created. This function just "follows" a line
   */
  let nCell, kExit;
  const cellInit = cell;
  const kEntryInit = kEntry;
  const line = { arcs: [], turn: 0 };
  let arc;
  while (true) {
    kExit = cell.exits[kEntry];
    arc = { kind: "n", cell, kEntry, kExit }; // "normal" arc
    //  arc.crossingElements = cell.getCrossingElements(kEntry);
    line.arcs.push(arc);
    line.turn += cell.turn[kEntry];
    cell.lines[kEntry] = line;
    nCell = cell.getNeighbor(kExit);
    if (nCell === false) {
      // on the edge of the grid, add straightline to next cell entry
      nCell = cell.getNeighbor((kExit + 1) % 6); // next side of same hexagon
      if (nCell === false) {
        kEntry = (kExit + 1) % 6;
        line.arcs.push({
          kind: "l",
          cell0: cell,
          k0: kExit,
          cell1: cell,
          k1: kEntry
        }); // line
        line.turn += 4;
      } else {
        kEntry = (kExit + 5) % 6;
        line.arcs.push({
          kind: "l",
          cell0: cell,
          k0: kExit,
          cell1: nCell,
          k1: kEntry
        }); // line
        cell = nCell;
        line.turn += 2;
      }
    } else {
      cell = nCell;
      kEntry = (kExit + 3) % 6;
    }
    if (cell == cellInit && kEntry == kEntryInit) {
      if (line.turn < 0) {
        // reverse line to have a potitive turn
        line.arcs.reverse();
        line.arcs.forEach((arc) => {
          switch (arc.kind) {
            case "n":
              [arc.kEntry, arc.kExit] = [arc.kExit, arc.kEntry];
              break;
            case "l":
              [arc.cell0, arc.cell1] = [arc.cell1, arc.cell0];
              [arc.k0, arc.k1] = [arc.k1, arc.k0];
              break;
          }
        });
        if (line.arcs[0].kind == "l") {
          // want all lines to begin by a "n"
          line.arcs.push(line.arcs.unshift());
        }
        line.turn = -line.turn;
      }
      return line;
    }
  } // while true
} // makeLine

//-----------------------------------------------------------------------------
function makeLines() {
  const lines = [];

  grid.forEach((row) =>
    row.forEach((cell) => {
      for (let kEntry = 0; kEntry < 6; ++kEntry) {
        if (cell.lines[kEntry]) continue; // already belong to another line
        lines.push(makeLine(cell, kEntry));
      } // for kEntry
    })
  );
  // "clean" lines by removing curves which were unduly created when some curves are not connected to rest of the shape
  forkl0: for (let kl0 = lines.length - 2; kl0 >= 0; --kl0) {
    let line0 = lines[kl0];
    for (let ka0 = 0; ka0 < line0.arcs.length; ++ka0) {
      let arc0 = line0.arcs[ka0];
      if (arc0.kind == "l") continue;
      for (let kl1 = kl0 + 1; kl1 < lines.length; ++kl1) {
        let line1 = lines[kl1];
        for (let ka1 = 0; ka1 < line1.arcs.length; ++ka1) {
          let arc1 = line1.arcs[ka1];
          if (arc1.kind == "l") continue;
          if (arc0.cell != arc1.cell || arc0.kEntry != arc1.kEntry) continue;
          // remove line0 or line1, whichever is the longest
          if (line0.arcs.length >= line1.arcs.length) {
            lines.splice(kl0, 1);
          } else {
            lines.splice(kl1, 1);
          }
          continue forkl0;
        } // for ka1
      } // for kl1
    } // for ka0
  } // for kl0
  return lines;
} // makeLines

//-----------------------------------------------------------------------------
function setParity(lines) {
  let arc;

  lines.forEach((line) => {
    arc = line.arcs[0];
    line.parity = !((arc.kEntry + (line.turn > 0 ? 0 : 1)) & 1);
  });
} // setParity
//-----------------------------------------------------------------------------
function makePaths(lines) {
  // adds lines paths for drawing and linear gradient

  let gr, hue, sat;
  lines.forEach((line) => {
    line.ef = new ExtremeFilter(-mPI / 4);
    line.path = new Path2D();
    let p;

    line.arcs.forEach((arc) => {
      if (arc.kind == "l") {
        p = arc.cell1.middle[arc.k1];
        line.path.lineTo(p.x, p.y);
      } else {
        arc.crossingElements = arc.cell.getCrossingElements(
          arc.kEntry,
          arc.kExit
        );
        arc.crossingElements.forEach((aa) => {
          line.ef.filterArc(aa.c.x, aa.c.y, aa.radius, aa.a0, aa.a1, aa.ccw);
          line.path.arc(aa.c.x, aa.c.y, aa.radius, aa.a0, aa.a1, aa.ccw);
        });
      }
    });
    // create refP
    let arc = line.arcs[0];
    let crossArc = arc.crossingElements[0];
    // must refP be inside or outside of arc ?
    let inout = [-1, 1, 1, -1, -1, 1][(arc.kEntry + 6 - arc.cell.rot) % 6];
    inout = 1 + 0.1 * inout;
    let ang = crossArc.a0 + 0.2 * (crossArc.ccw ? -1 : +1);
    line.refP = {
      x: crossArc.c.x + crossArc.radius * inout * mcos(ang),
      y: crossArc.c.y + crossArc.radius * inout * msin(ang)
    };
    // create color (gradient)
    line.gr = line.ef.getLinearGradient();
    switch (colorMode) {
      case 0:
        hue = intAlea(360);
        break;
      case 1:
        hue = globalHue;
        break;
      case 2:
        hue = line.parity ? globalHue : globalHue + 180;
    }
    line.hue = hue;
    sat = 100;
    let lum0 = 20,
      lum1 = 80;
    if (line.parity) {
      [lum0, lum1] = [lum1, lum0];
      sat = 60;
    }
    line.gr.addColorStop(0, `hsl(${hue} ${sat}% ${lum0}%)`);
    line.gr.addColorStop(0.5, `hsl(${hue} ${sat}% 50%)`);
    line.gr.addColorStop(1, `hsl(${hue} ${sat}% ${lum1}%)`);
  }); // lines.forEach
}
//-----------------------------------------------------------------------------

function createGrid() {
  let line;

  perx = intAlea(1, 6);
  pery = intAlea(1, 5);
  if (alea(1) > 0.7) {
    perx = nbx;
    pery = nby;
  }

  pergrid = [];
  for (let ky = 0; ky < pery; ++ky) {
    pergrid[ky] = line = []; // new line
    for (let kx = 0; kx < perx; ++kx) {
      line[kx] = { rot: intAlea(6) };
    } // for let kx
  } // for ky

  grid = [];
  for (let ky = 0; ky < nby; ++ky) {
    grid[ky] = line = []; // new line
    for (let kx = 0; kx < nbx; ++kx) {
      line[kx] = new Hexagon(kx, ky);
    } // for let kx
  } // for ky
} // createGrid
//-----------------------------------------------------------------------------

let animate;

{
  // scope for animate

  let animState = 0;

  animate = function (tStamp) {
    let message;

    message = messages.shift();
    if (message && message.message == "reset") animState = 0;
    if (message && message.message == "click") animState = 0;
    window.requestAnimationFrame(animate);

    switch (animState) {
      case 0:
        if (startOver()) {
          ++animState;
        }
        break;

      case 1:
        colorMode = (colorMode + 1) % 3;
        ++animState;
        break;

      case 2:
        break;
    } // switch
  }; // animate
} // scope for animate

//------------------------------------------------------------------------
//------------------------------------------------------------------------

function startOver() {
  // canvas dimensions

  maxx = window.innerWidth;
  maxy = window.innerHeight;

  canv.width = maxx;
  canv.height = maxy;
  ctx.lineJoin = "round";
  ctx.lineCap = "round";

  ctx.fillStyle = "#000";
  ctx.fillRect(0, 0, maxx, maxy);

  globalHue = intAlea(360);

  radius = msqrt(maxx * maxy) / intAlea(10, 20);

  // all hexagons fully visible
  nbx = mfloor((maxx / radius - 0.5) / 1.5);
  nby = mfloor(maxy / radius / rac3 - 0.5);
  // all screen covered with hexagons
  nbx = mceil(maxx / radius / 1.5 + 1);
  nby = mceil(maxy / radius / rac3 + 0.5);

  if (nbx < 1 || nby < 1) return false; // nothing to draw

  orgx = (maxx - radius * (1.5 * nbx + 0.5)) / 2 + radius; // obvious, insn't it ?
  orgy = (maxy - radius * rac3 * (nby + 0.5)) / 2 + radius * rac3; // yet more obvious

  createGrid();
  /*
            grid.forEach(line => line.forEach(cell => {
              cell.drawHexagon();
              cell.drawArcs();
            }));
      */
  let lines = makeLines();
  setParity(lines);
  makePaths(lines);

  const top = createHierarchy(lines);

  let levels = [[top]];
  for (let level = 1; level < 100; ++level) {
    let newLevel = [];
    levels[level - 1].forEach(
      (hier) => (newLevel = newLevel.concat(hier.children))
    );
    if (newLevel.length == 0) break; // done
    levels.push(newLevel);
  }

  for (let k = 1; k < levels.length; ++k) {
    let level = levels[k];
    level.forEach((hier) => {
      let line = hier.item;
      if (!line.parity) return;
      ctx.strokeStyle = line.gr;
      ctx.stroke(line.path);
      ctx.fillStyle = line.gr;
      ctx.fill(line.path);
    });
    ctx.shadowBlur = 5;
    ctx.shadowOffsetX = -5;
    ctx.shadowOffsetY = 5;
    level.forEach((hier) => {
      let line = hier.item;
      ctx.shadowColor = `hsl(${line.hue} 100% 10% / 0.4)`;
      if (line.parity) return;
      ctx.fillStyle = line.gr;
      ctx.fill(line.path);
    });
    ctx.shadowBlur = 0;
    ctx.shadowOffsetX = 0;
    ctx.shadowOffsetY = 0;
  }

  return true;
} // startOver

//------------------------------------------------------------------------

function mouseClick(event) {
  messages.push({ message: "click" });
} // mouseClick

//------------------------------------------------------------------------
//------------------------------------------------------------------------
// beginning of execution

{
  canv = document.createElement("canvas");
  canv.style.position = "absolute";
  document.body.appendChild(canv);
  ctx = canv.getContext("2d");
  //      canv.setAttribute('title', 'click me');
} // création CANVAS

canv.addEventListener("click", mouseClick);
messages = [{ message: "reset" }];
requestAnimationFrame(animate);