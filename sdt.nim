# Plain CAD tool using Nim, GTK and Cairo
#
# Basic drawing area behaviour like zooming, scrolling and panning is based on gintro/examples/gtk3/drawingarea.nim
# which again is based on an earlier Ruby implementation
#
# Main goal of this tool is to make fun using it.
#
# (c) S. Salewski 2020, 2021
# License MIT
# v0.1 2021-MAR-15

import times
import gintro/[gtk4, gdk4, glib, gobject, gio, cairo]
from math import round, floor, `^`, `mod`
import rtree

const
  ZoomFactorMouseWheel = 1.1
  ZoomFactorSelectMax = 10 # ignore zooming in tiny selection
  ZoomNearMousepointer = true # mouse wheel zooming -- to mouse-pointer or center
  SelectRectCol = [0.0, 0, 1, 0.5] # blue with transparency

const
  GrabDist = 3 # mm
  DefaultLineWidth = 0.2 # mm

type
  RGBA = tuple[r, g, b, a: float]

proc newRGBA(r, g, b: float; a: float = 1): RGBA =
  (r, g, b, a)

type
  Style = object
    lineWidth: float
    color: RGBA # gdk4.RGBA ?

var styles: array[3, Style]
styles[0] = Style(lineWidth: 1.0, color: newRGBA(0, 0, 1))
styles[0] = Style(lineWidth: 1.0, color: (0.0, 0.0, 1.0, 1.0))
styles[1] = Style(lineWidth: 0.5, color: (1.0, 0.0, 0.0, 1.0))
styles[2] = Style(lineWidth: 1.5, color: (0.0, 1.0, 0.0, 1.0))

type
  Shapes {.pure.} = enum
    line, rect, circ

type
  Styles {.pure.} = enum
    medium, thin, thick, none

type
  V2 = tuple[x, y: float]

type CColor =
  array[4, float]

# copy from the cdt module
func distanceLinePointSqr(x1, y1, x2, y2, x3, y3: float): (float, float, float, float, float) =
  assert(x2 != x1 or y2 != y1) # division by zero 
  let
    u = ((x3 - x1) * (x2 - x1) + (y3 - y1) * (y2 - y1)) / ((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1))
    x = x1 + u * (x2 - x1)
    y = y1 + u * (y2 - y1)
    d2 = (x - x3) * (x - x3) + (y - y3) * (y - y3) # squared distance to infinite line through p1-p2
  var v2: float # squared distance to line segment defined by p1-p2
  if u < 0:
    v2 = (x3 - x1) * (x3 - x1) + (y3 - y1) * (y3 - y1)
  elif u > 1:
    v2 = (x3 - x2) * (x3 - x2) + (y3 - y2) * (y3 - y2)
  else:
    v2 = d2
  return (d2, v2, u, x, y)

discard """
Zooming, scrolling, panning...

|-------------------------|
|<-------- A ------------>|
|                         |
|  |---------------|      |
|  | <---- a ----->|      |
|  |    visible    |      |
|  |---------------|      |
|                         |
|                         |
|-------------------------|

a is the visible, zoomed in area == darea.allocatedWidth
A is the total data range
A/a == userZoom >= 1
For horizontal adjustment we use
hadjustment.setUpper(darea.allocatedWidth * userZoom) == A
hadjustment.setPageSize(darea.allocatedWidth) == a
So hadjustment.value == left side of visible area

Initially, we set userZoom = 1, scale our data to fit into darea.allocatedWidth
and translate the origin of our data to (0, 0)

Zooming: Mouse wheel or selecting a rectangle with left mouse button pressed
Scrolling: Scrollbars
Panning: Moving mouse while middle mouse button pressed
"""

# drawing area and scroll bars in 2x2 grid (PDA == Plain Drawing Area)

type
  PosAdj = ref object of Adjustment
    handlerID: uint64

proc newPosAdj: PosAdj =
  newAdjustment(PosAdj, 0, 0, 1, 1, 10, 1)

# we have basic geometric elements like lines, and we can group them together.
# groups can contain basic elements and subgroups

proc sort(a, b: float): rtree.Ext[float] =
  if a <= b : (a, b) else: (b, a)

type
  Element = ref object of RootRef
    style: Styles
    x1, y1, x2, y2: float
    width: float
    color: CColor
    hover: bool
    selected: bool

type
  Line = ref object of Element

type
  Rect = ref object of Element

type
  Circ = ref object of Element


### Line procedures

# constructor
proc newLine(p1, p2: V2; width: float; color: CColor): Line =
  Line(x1: p1.x, y1: p1.y, x2: p2.x, y2: p2.y, width: width, color: color)

proc newRect(p1, p2: V2; width: float; color: CColor): Rect =
  var p1 = p1
  var p2 = p2
  if p1.x > p2.x: swap(p1.x, p2.x)
  if p1.y > p2.y: swap(p1.y, p2.y)
  Rect(x1: p1.x, y1: p1.y, x2: p2.x, y2: p2.y, width: width, color: color)
 
proc newCirc(p1, p2: V2; width: float; color: CColor): Circ =
  Circ(x1: p1.x, y1: p1.y, x2: p2.x, y2: p2.y, width: width, color: color)

# distance to line segment
proc sqrDistanceLine(l: Line; x, y: float): float =
  distanceLinePointSqr(x1 = l.x1, y1 = l.y1, x2 = l.x2, y2 = l.y2, x3 = x, y3 = y)[1]

proc sqrDistanceRect(r: Rect; x, y: float): float =
  let (x1, y1, x2, y2) = (r.x1, r.y1, r.x2, r.y2)
  var min: float = Inf
  for p in [(x1, y1, x1, y2), (x1, y1, x2, y1), (x2, y2, x1, y2), (x2, y2, x2, y1)]:
    let d = distanceLinePointSqr(p[0], p[1], p[2], p[3], x, y)[1]
    if d < min:
      min = d
  result = min

proc sqrDistanceCirc(c: Circ; x, y: float): float =
  max(math.hypot(c.x1 - x, c.y1 - y) - math.hypot(c.x1 - c.x2, c.y1 - c.y2), 0) ^ 2
  #if result < 0:
  #  return 0
  #return result ^ 2

type
  UserAction {.pure.} = enum
    none,
    lmbdv, # left mouse button pressed over void area
    lmbdo, # left mouse button pressed over object
    zooming,
    selecting,
    dragging

iterator allElements(tree: RStarTree[8, 2, float, Element]; x: Element): Element =
  for el in tree.elements:
    yield el
  if x != nil:
    yield x

type
  PDA = ref object of Grid
    cbtStyle: ComboBoxText
    activeShape: Shapes
    tree: RStarTree[8, 2, float, Element]
    points: seq[V2]
    activeObj: Element
    movingObj: Element
    activeState: int 
    hover, lastHover: Element
    fcolor: CColor
    bcolor: CColor
    majorGridColor: CColor
    minorGridColor: CColor
    guideColor: CColor
    majorGrid: float
    minorGrid: float
    activeGrid: float
    zoomNearMousepointer: bool
    selecting: bool
    uact: UserAction
    lineWidth: float
    userZoom: float
    grid: array[2, float]
    surf: cairo.Surface
    pattern: Pattern
    cr: cairo.Context
    darea: DrawingArea
    hadjustment: PosAdj
    vadjustment: PosAdj
    hscrollbar: Scrollbar
    vscrollbar: Scrollbar
    hPaintable: Paintable
    vPaintable: Paintable
    headerbar: Headerbar
    topbox: gtk4.Box
    botbox: gtk4.Box
    fullScale: float
    dataX: float
    dataY: float
    dataWidth: float
    dataHeight: float
    lastButtonDownPosX: float
    lastButtonDownPosY: float
    lastButtonDownPosXUser: float
    lastButtonDownPosYUser: float
    lastMousePosX: float
    lastMousePosY: float
    zoomRectX1: float
    zoomRectY1: float
    oldSizeX: int
    oldSizeY: int
    legEvX, legEvY: float

proc initCData(result: var PDA) =
  result.tree = newRStarTree[8, 2, float, Element]()
  result.fcolor = [float 0, 0, 1, 0.7]
  result.bcolor= [float 1, 1, 1, 1]
  result.majorGridColor= [float 0, 0, 0, 1]
  result.minorGridColor= [float 0, 0, 0, 0.6]
  result.guideColor= [float 1, 0, 0, 0.7]
  result.majorGrid = 100
  result.minorGrid = 10
  result.activeGrid = 10
  result.activeShape = Shapes.line

# convert abs distance x in mm into distance value for GtkDrawingArea
# when drawing with cairo and cairo_scale == 1
proc absToScr(pda: PDA; x: float): float =
  var scale {.global.}: float
  if scale == 0:
    let d = gdk4.getDefaultDisplay()
    #let m = gdk4.getMonitor(d, 0)
    let glm = gdk4.getMonitors(d)
    #let m = gdk4.Monitor(glm.getItem(0))
    let m = gdk4.getMonitorAtSurface(d, getSurface(getNative(pda.darea)))
    var r: gdk4.Rectangle
    gdk4.getGeometry(m, r)
    let s = gdk4.getScaleFactor(m)
    #let s = 1
    #let mm: int  = gdk4.getWidth_mm(m) # this is for exact size
    let mm = 500
    # a 27 inch screen is our basis configuration -- larger screens are used with more distance, so we may scale then up with
    # const mm = 600.0 
    # scale = float(s) * float(r.width) / float(mm)
    scale = float(s) * float(1) / float(mm)
  #let fullScale = min(r.width.float / this.dataWidth,
  #    r.height.float / this.dataHeight)
  let h = min(pda.darea.allocatedWidth.float, pda.darea.allocatedHeight.float)
  return x * scale * h / pda.fullscale # * customDetailScale # compensate monitor distance, viewing angle

proc setLineWidthAbs(pda: PDA; w: float) =
  pda.cr.setLineWidth(pda.absToScr(w))

proc setHairLineWidth(pda: PDA) =
  pda.cr.setLineWidth(pda.absToScr(0.2))

proc setThinHairLineWidth(pda: PDA) =
  pda.cr.setLineWidth(pda.absToScr(0.15))

proc drawGrabX(pda: PDA; x, y: float) =
  let d = pda.absToScr(math.sin(math.Pi * 0.25) * GrabDist)
  pda.cr.moveTo(x - d, y - d)
  pda.cr.lineTo(x + d, y + d)
  pda.cr.stroke
  pda.cr.moveTo(x - d, y + d)
  pda.cr.lineTo(x + d, y - d)
  pda.cr.stroke

proc drawGrabCirc(pda: PDA; x, y: float) =
  pda.setHairLineWidth
  pda.cr.newPath
  pda.cr.arc(x, y, pda.absToScr(GrabDist), 0, math.Tau)
  pda.drawGrabX(x, y)
  pda.cr.stroke

# event coordinates to user space
proc getUserCoordinates(this: PDA; eventX, eventY: float): tuple[x, y: float] =
  ((eventX - this.hadjustment.upper * 0.5 + this.hadjustment.value) / (
      this.fullScale * this.userZoom) + this.dataX + this.dataWidth * 0.5,
   (eventY - this.vadjustment.upper * 0.5 + this.vadjustment.value) / (
       this.fullScale * this.userZoom) + this.dataY + this.dataHeight * 0.5)

proc getUserCoordinates(this: PDA; v: V2): V2 =
  ((v.x - this.hadjustment.upper * 0.5 + this.hadjustment.value) / (
      this.fullScale * this.userZoom) + this.dataX + this.dataWidth * 0.5,
   (v.y - this.vadjustment.upper * 0.5 + this.vadjustment.value) / (
       this.fullScale * this.userZoom) + this.dataY + this.dataHeight * 0.5)

proc roundToMultiple(x, m: float): float =
  result = ((x / m) + 0.5).floor * m

proc roundToGrid(x, y: float): tuple[x, y: float] =
  (roundToMultiple(x, 10), roundToMultiple(y, 10))

proc roundToGrid(pda: PDA; v: V2): V2 =
  (roundToMultiple(v.x, pda.activeGrid), roundToMultiple(v.y, pda.activeGrid))

proc cairoDevRound(w: float): float =
  if w < 1.5:
    0.5
  else:
    floor((w + 0.5) mod 2) / 2

proc move(pda: PDA): bool =
  let (a, b) = (pda.lastButtonDownPosXUser, pda.lastButtonDownPosYUser)
  let (x, y) = pda.getUserCoordinates((pda.lastMousePosX, pda.lastMousePosY))
  let (dx, dy) = pda.roundToGrid((x - pda.lastButtonDownPosXUser, y - pda.lastButtonDownPosYUser))
  if (a - pda.movingObj.x1) ^ 2 + (b - pda.movingObj.y1) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
    pda.movingObj.x1 += dx
    pda.movingObj.y1 += dy
  elif (a - pda.movingObj.x2) ^ 2 + (b - pda.movingObj.y2) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
    pda.movingObj.x2 += dx
    pda.movingObj.y2 += dy
  else:
    pda.movingObj.x1 += dx
    pda.movingObj.y1 += dy
    pda.movingObj.x2 += dx
    pda.movingObj.y2 += dy
  pda.lastButtonDownPosXUser += dx
  pda.lastButtonDownPosYUser += dy
  return true

proc drawGrid(pda: PDA) =
  pda.cr.setOperator(Operator.over)
  var w = getLineWidth(pda.cr)
  w = deviceToUserDistance(pda.cr, w, 0)[0] # hypot?
  let rw = cairoDevRound(w)
  var (x1, y1) = getUserCoordinates(pda, 0, 0)
  var (x2, y2) = getUserCoordinates(pda, pda.darea.allocatedWidth.float, pda.darea.allocatedHeight.float)
  pda.setThinHairLineWidth
  pda.cr.setSource(pda.minorGridColor)
  var x = x1.roundToMultiple(pda.grid[1])
  while x < x2:
    if (x mod pda.grid[0]).abs > 0.1:
      var h = userToDevice(pda.cr, x, 0.0)[0].round + rw
      h = deviceToUser(pda.cr, h, 0.0)[0]
      pda.cr.moveTo(h, y1)
      pda.cr.lineTo(h, y2)
    x += pda.grid[1]
  pda.cr.stroke
  var y = y1.roundToMultiple(pda.grid[1])
  while y < y2:
    if (y mod pda.grid[0]).abs > 0.1:
      var h = userToDevice(pda.cr, 0.0, y)[1].round + rw
      h = deviceToUser(pda.cr, 0.0, h)[1]
      pda.cr.moveTo(x1, h)
      pda.cr.lineTo(x2, h)
    y += pda.grid[1]
  pda.cr.stroke
  #
  pda.setHairLineWidth
  pda.cr.setSource(pda.majorGridColor)
  x = x1.roundToMultiple(pda.grid[0])
  while x < x2:
    var h = userToDevice(pda.cr, x, 0.0)[0].round + rw
    h = deviceToUser(pda.cr, h, 0.0)[0]
    pda.cr.moveTo(h, y1)
    pda.cr.lineTo(h, y2)
    x += pda.grid[0]
  pda.cr.stroke
  y = y1.roundToMultiple(pda.grid[0])
  while y < y2:
    var h = userToDevice(pda.cr, 0.0, y)[1].round + rw
    h = deviceToUser(pda.cr, 0.0, h)[1]
    pda.cr.moveTo(x1, h)
    pda.cr.lineTo(x2, h)
    y += pda.grid[0]
  pda.cr.stroke

# we have 4 visible states:
# type VState = enum plain, selected, hover, selectedHover
# We draw the objects only once.
# First we use a grey, translated copy of the objects for the shadow.
# Then we draw all plain elements. After that we draw the
#  hover, selectedHover objects to get brigher colors.
# we call this proc twice -- with plain group and with selected group

# bounding box

proc boxLine(l: Line; pda: PDA): rtree.Box[2, float] =
  result[0] = sort(l.x1, l.x2)
  result[1] = sort(l.y1, l.y2)

proc boxRect(l: Rect; pda: PDA): rtree.Box[2, float] =
  result[0] = sort(l.x1, l.x2)
  result[1] = sort(l.y1, l.y2)

proc boxCirc(c: Circ; pda: PDA): rtree.Box[2, float] =
  let r = math.hypot(c.x1 - c.x2, c.y1 - c.y2)
  result[0] = (c.x1 - r, c.x1 + r)
  result[1] = (c.y1 - r, c.y1 + r)

proc drawLine(l: Line; pda: PDA) =
  pda.cr.moveTo(l.x1, l.y1)
  pda.cr.lineTo(l.x2, l.y2)

proc drawRect(r: Rect; pda: PDA) =
  let (x1, y1, x2, y2) = (r.x1, r.y1, r.x2, r.y2)
  pda.cr.moveTo(x1, y2)
  for p in [(x1, y1), (x2, y1), (x2, y2), (x1, y2)]:
    pda.cr.lineTo(p[0], p[1])

proc drawCirc(c: Circ; pda: PDA) =
  let r = math.hypot(c.x1 - c.x2,  c.y1 - c.y2)
  pda.cr.arc(c.x1, c.y1, r, 0, math.Tau)

proc initDrawGrab(pda: PDA) =
  pda.cr.setSource(1, 0, 0)
  pda.setHairLineWidth

proc drawLineGrab(l: Line; pda: PDA) =
  initDrawGrab(pda)
  #pda.cr.setSource(1, 0, 0)
  pda.drawGrabCirc(l.x1, l.y1)
  pda.drawGrabCirc(l.x2, l.y2)
  #pda.setHairLineWidth
  let dx = pda.absToScr((l.y2 - l.y1) / math.hypot(l.x2 - l.x1, l.y2 - l.y1) * GrabDist)
  let dy = pda.absToScr(-(l.x2 - l.x1) / math.hypot(l.x2 - l.x1, l.y2 - l.y1) * GrabDist)
  pda.cr.moveTo(l.x1 + dx, l.y1 + dy)
  pda.cr.lineTo(l.x2 + dx, l.y2 + dy)
  pda.cr.stroke
  pda.cr.moveTo(l.x1 - dx, l.y1 - dy)
  pda.cr.lineTo(l.x2 - dx, l.y2 - dy)
  pda.cr.stroke

proc drawRectGrab(r: Rect; pda: PDA) =
  initDrawGrab(pda)
  let d = pda.absToScr(GrabDist * 0.5)
  var x = r.x1 - d
  var y = r.y1 - d
  pda.cr.moveTo(x, y)
  x = r.x2 + d
  pda.cr.lineTo(x, y)
  y = r.y2 + d
  pda.cr.lineTo(x, y)
  x = r.x1 - d
  pda.cr.lineTo(x, y)
  y = r.y1 - d
  pda.cr.lineTo(x, y)

  y = r.y1 + d
  pda.cr.moveTo(x, y)
  x = r.x2 + d
  pda.cr.lineTo(x, y)
  y = r.y2 - d
  pda.cr.moveTo(x, y)
  x = r.x1 - d
  pda.cr.lineTo(x, y)

  x = r.x1 + d
  y = r.y1 - d
  pda.cr.moveTo(x, y)
  y = r.y2 + d
  pda.cr.lineTo(x, y)
  x = r.x2 - d
  pda.cr.moveTo(x, y)
  y = r.y1 - d
  pda.cr.lineTo(x, y)
  pda.cr.stroke
  
proc sqrDistance(el: Element; x, y: float): float =
  if el of Line:
    result = sqrDistanceLine(Line(el), x, y)
  elif el of Rect:
    result = sqrDistanceRect(Rect(el), x, y)
  elif el of Circ:
    result = sqrDistanceCirc(Circ(el), x, y)

# squared distance from query point to
proc dist(qo: BoxCenter[2, float]; el: L[2, float, Element]): float =
  if el.l of Line:
    let l = Line(el.l)
    let x = qo[0]
    let y = qo[1]
    result = distanceLinePointSqr(x1 = l.x1, y1 = l.y1, x2 = l.x2, y2 = l.y2, x3 = x, y3 = y)[1]
  elif el.l of Rect:
    let l = Rect(el.l)
    let x = qo[0]
    let y = qo[1]
    result = distanceLinePointSqr(l.x1, l.y1, l.x2, l.y2, x,  y)[1]
  elif el.l of Circ:
    let l = Circ(el.l)
    let x = qo[0]
    let y = qo[1]
    result = distanceLinePointSqr(l.x1, l.y1, l.x2, l.y2, x,  y)[1]

# squared distance from query point to
#proc dist(qo: BoxCenter[2, float]; l: L[2, float, Element]): float =
#  if el of Line:
#    result = distLine(qo, Line(el), pda)

proc boxEl(el: Element; pda: PDA): rtree.Box[2, float] =
  if el of Line:
    result = boxLine(Line(el), pda)
  elif el of Rect:
    result = boxRect(Rect(el), pda)
  elif el of Circ:
    result = boxCirc(Circ(el), pda)

proc drawEl(el: Element; pda: PDA) =
  if el of Line:
    drawLine(Line(el), pda)
  elif el of Rect:
    drawRect(Rect(el), pda)
  elif el of Circ:
    drawCirc(Circ(el), pda)
  
proc drawElGrab(el: Element; pda: PDA) =
  if el of Line:
    drawLineGrab(Line(el), pda)
  elif el of Rect:
    drawrectGrab(Rect(el), pda)

proc drawSelected(pda: PDA; selected: bool) =
  pda.cr.setOperator(Operator.over)
  for hov in [false, true]:
    pda.cr.pushGroup
    for l in pda.tree.allElements(pda.movingObj):
      if l.selected != selected: continue
      if hov != (l == pda.hover): continue
      drawEl(l, pda)
      pda.cr.setSource(styles[l.style.ord].color)
      pda.setLineWidthAbs(styles[l.style.ord].lineWidth * (1.0 + 0.6 * (selected.int + (l == pda.hover).int).float))
      pda.cr.stroke
    if not selected and not hov: # the plain ones
      let tmp0 = pda.cr.popGroup
      let dd = pda.absToScr(0.2) # tiny offset, or better zero?
      pda.cr.translate(dd, dd)
      pda.cr.setSource(0, 0, 0, 0.7)
      pda.cr.mask(tmp0) # grey bottom shadow
      pda.cr.translate(-dd, -dd)
      pda.cr.setSource(tmp0)
      pda.cr.paintWithAlpha(0.7) # color pain
      patternDestroy(tmp0)
      continue

    let tmp0 = pda.cr.popGroup
    pda.cr.setSource(0, 0, 0, 0.7)
    pda.cr.mask(tmp0) # fat shadow -- should we do a offset translation?
    patternDestroy(tmp0)
    pda.cr.pushGroup
    for l in pda.tree.allElements(pda.movingObj):
      if l.selected != selected: continue
      if hov != (l == pda.hover): continue
      drawEl(l, pda)
      pda.cr.setSource(styles[l.style.ord].color)
      pda.setLineWidthAbs(styles[l.style.ord].lineWidth * (1.0 + 0.3 * (selected.int + (l == pda.hover).int).float))
      pda.cr.stroke
      if l == pda.hover: # draw the hover grab markers
        drawElGrab(l, pda)
    let tmp1 = pda.cr.popGroup
    pda.cr.setSource(1, 1, 1, 0.3) # lighter than plain objects
    pda.cr.mask(tmp1)
    pda.cr.setSource(tmp1)
    pda.cr.paintWithAlpha(0.7)
    pda.cr.paintWithAlpha(1.0)#0.7)
    patternDestroy(tmp1)

proc draw(pda: PDA) =
  pda.cr.setSource(1, 1, 1)
  pda.cr.paint
  pda.cr.setLineWidth(1)
  pda.cr.setSource(0, 0, 0)
  pda.drawGrid
  pda.drawSelected(false)
  pda.drawSelected(true)

proc drawingAreaDrawCb(darea: DrawingArea; cr: Context; width, height: int; this: PDA) =
  if this.pattern.isNil: return
  var t0 = cpuTime()
  cr.setSource(this.pattern)
  cr.paint
  #echo "CPU time [s] ", cpuTime() - t0
  if this.selecting:
    cr.rectangle(this.lastButtonDownPosX, this.lastButtonDownPosY,
      this.zoomRectX1 - this.lastButtonDownPosX, this.zoomRectY1 - this.lastButtonDownPosY)
    cr.setSource(SelectRectCol)
    cr.fillPreserve
    cr.setSource(0, 0, 0)
    cr.setLineWidth(2)
    cr.stroke

# clamp to correct values, 0 <= value <= (adj.upper - adj.pageSize), block calling onAdjustmentEvent()
proc updateVal(adj: PosAdj; d: float) =
  adj.signalHandlerBlock(adj.handlerID)
  adj.setValue(max(0.0, min(adj.value + d, adj.upper - adj.pageSize)))
  adj.signalHandlerUnblock(adj.handlerID)

proc updateAdjustments(this: PDA; dx, dy: float) =
  this.hadjustment.setUpper(this.darea.allocatedWidth.float * this.userZoom)
  this.vadjustment.setUpper(this.darea.allocatedHeight.float * this.userZoom)
  this.hadjustment.setPageSize(this.darea.allocatedWidth.float)
  this.vadjustment.setPageSize(this.darea.allocatedHeight.float)
  updateVal(this.hadjustment, dx)
  updateVal(this.vadjustment, dy)

proc paint(this: PDA) =
  this.cr.save
  this.cr.translate(this.hadjustment.upper * 0.5 - this.hadjustment.value, # our origin is the center
    this.vadjustment.upper * 0.5 - this.vadjustment.value)
  this.cr.scale(this.fullScale * this.userZoom, this.fullScale * this.userZoom)
  this.cr.translate(-this.dataX - this.dataWidth * 0.5, -this.dataY - this.dataHeight * 0.5)
  draw(this)
  this.cr.restore

proc dareaConfigureCallback(darea: DrawingArea; width, height: int; this: PDA) =
  (this.dataX, this.dataY, this.dataWidth,
    this.dataHeight) = (100.0, 150.0, 400.0, 300.0)#this.extents() # query user defined size
  this.fullScale = min(this.darea.allocatedWidth.float / this.dataWidth,
      this.darea.allocatedHeight.float / this.dataHeight)
  if this.surf != nil:
    destroy(this.surf) # manually destroy surface -- GC would do it for us, but GC is slow...
  let s = darea.getNative.getSurface
  this.surf = createSimilarSurface(s, Content.color,
      this.darea.allocatedWidth, this.darea.allocatedHeight)
  if this.pattern != nil:
    patternDestroy(this.pattern)
  if this.cr != nil:
    destroy(this.cr)
  this.pattern = patternCreateForSurface(this.surf) # pattern now owns the surface!
  this.cr = newContext(this.surf) # this function references target!
  this.paint

proc hscrollbarSizeAllocateCallback(p: Paintable; pda: PDA) =
  let w = p.getIntrinsicWidth
  pda.hadjustment.setUpper(w.float * pda.userZoom)
  pda.hadjustment.setPageSize(w.float)
  if pda.oldSizeX != 0: # this fix is not exact, as fullScale can ...
    updateVal(pda.hadjustment, (w - pda.oldSizeX).float * 0.5)
  pda.oldSizeX = w
  
proc vscrollbarSizeAllocateCallback(p: Paintable; pda: PDA) =
  let h = p.getIntrinsicHeight
  pda.vadjustment.setUpper(h.float * pda.userZoom)
  pda.vadjustment.setPageSize(h.float)
  if pda.oldSizeY != 0: # this fix is not exact, as fullScale can ...
    updateVal(pda.vadjustment, (h - pda.oldSizeY).float * 0.5)
  pda.oldSizeY = h

proc updateAdjustmentsAndPaint(this: PDA; dx, dy: float) =
  this.updateAdjustments(dx, dy)
  this.paint
  this.darea.queueDraw#Area(0, 0, this.darea.allocatedWidth, this.darea.allocatedHeight)

proc onMotion(c: EventControllerLegacy; e: Event; this: PDA): bool =
  let x = this.legEvX
  let y = this.legEvY
  let (a, b) = this.getUserCoordinates(x, y)

  if this.uact == dragging and this.movingObj != nil:
    this.lastMousePosX = x
    this.lastMousePosY = y
    discard this.move
    paint(this)
    this.darea.queueDraw

  if math.hypot(x - this.lastButtonDownPosX, y - this.lastButtonDownPosY) > 2:
    if this.uact == lmbdv:
      this.uact = zooming
    elif this.uact == lmbdo:
      this.uact = dragging#selecting
      assert this.movingObj != nil
      var el: L[2, float, Element]
      var l = this.movingObj
      el = (boxEl(l, this), l)
      this.tree.delete(el)

  var el: Element = this.tree.findNearest(BoxCenter[2, float]([a, b]), dist)[1]
  if el != nil:
    if sqrDistance(el, a, b) < (this.absToScr(GrabDist)) ^ 2:
      this.hover = el
      el.hover = true
    else:
      this.hover = nil

  if this.uact == selecting:#state.contains(button1): # selecting
    this.selecting = true
    this.zoomRectX1 = x
    this.zoomRectY1 = y
    this.darea.queueDraw#Area(0, 0, this.darea.allocatedWidth, this.darea.allocatedHeight)
  elif false:#button2 in state: # panning
    this.updateAdjustmentsAndPaint(this.lastMousePosX - x, this.lastMousePosY - y)
  this.lastMousePosX = x
  this.lastMousePosY = y
  if this.points.len > 0 or this.hover != this.lastHover:
    if this.points.len == 1:
      let p = roundToGrid(a, b)
      this.movingObj.x2 = p[0]
      this.movingObj.y2 = p[1]
    paint(this)
    this.darea.queueDraw
    this.lastHover = this.hover
  return gdk4.EVENT_STOP

# zooming with mouse wheel -- data near mouse pointer should not move if possible!
# hadjustment.value + event.x is the position in our zoomed_in world, (userZoom / z0 - 1)
# is the relative movement caused by zooming
# In other words, this is the delta-move d of a point at position P from zooming:
# d = newPos - P = P * scale - P = P * (z/z0) - P = P * (z/z0 - 1). We have to compensate for this d.

proc scrollEvent(c: EventControllerLegacy; event: ScrollEvent; this: PDA): bool =
  assert  event.getEventType == EventType.scroll
  let z0 = this.userZoom
  case getDirection(event)
  of ScrollDirection.up:
    this.userZoom *= ZoomFactorMouseWheel
  of ScrollDirection.down:
    this.userZoom /= ZoomFactorMouseWheel
    if this.userZoom < 1:
      this.userZoom = 1
  else:
    return gdk4.EVENT_PROPAGATE
  if this.zoomNearMousepointer:
    let x = this.legEvX
    let y = this.legEvY
    this.updateAdjustmentsAndPaint((this.hadjustment.value + x) * (this.userZoom / z0 - 1),
      (this.vadjustment.value + y) * (this.userZoom / z0 - 1))
  else: # zoom to center
    this.updateAdjustmentsAndPaint((this.hadjustment.value +
        this.darea.allocatedWidth.float * 0.5) * (this.userZoom / z0 - 1),
        (this.vadjustment.value + this.darea.allocatedHeight.float * 0.5) * (this.userZoom / z0 - 1))
  return gdk4.EVENT_STOP

proc buttonPressEvent(c: EventControllerLegacy; e: Event; this: PDA): bool =
  let x = this.legEvX
  let y = this.legEvY
  this.lastMousePosX = x
  this.lastMousePosY = y
  this.lastButtonDownPosX = x
  this.lastButtonDownPosY = y
  (this.lastButtonDownPosXUser, this.lastButtonDownPosYUser) = this.getUserCoordinates((x, y))
  if this.hover.isNil:
    this.uact = lmbdv
  else:
    this.uact = lmbdo
    this.movingObj = this.hover
  return gdk4.EVENT_STOP

# zoom into selected rectangle and center it
# math: we first center the selection rectangle, and then compensate for translation due to scale

proc buttonReleaseEvent(c: EventControllerLegacy; event: ButtonEvent; this: PDA): bool =
  let x = this.legEvX
  let y = this.legEvY
  let xy = [x, y]

  if this.uact == UserAction.lmbdv and this.hover == nil:# and this.selected.lines.len > 0:
    var h = false
    for el in this.tree.allElements(nil):#pda.movingObj):
      if el.selected: h = true
      el.selected = false
    if h:
      paint(this)
      this.darea.queueDraw
      this.uact = UserAction.none
      return
    
  if this.uact == UserAction.lmbdo and this.hover != nil:
    this.uact = UserAction.none

    for l in this.tree.allElements(nil):
      if l == this.hover:
        l.selected = true

    return
  if this.movingObj != nil and this.uact == dragging:
    var el: L[2, float, Element]
    var l = this.movingObj
    el = (boxEl(l, this), l)
    this.tree.insert(el)
    this.uact = UserAction.none
    return
  if this.hover != nil:
    return
  #var uc = this.getUserCoordinates(xy) # does not compile
  let uc = this.getUserCoordinates((xy[0], xy[1]))
  let ucr = roundToGrid(this, uc)
  if this.uact == dragging:
    this.uact = UserAction.none
  if this.uact in {lmbdo, lmbdv}:
    this.points.add(ucr)
  if this.points.len == 1:
    var l: Element
    if this.activeShape == Shapes.line:
      l = newLine(this.points[0], this.points[0], this.lineWidth, this.fcolor)
    elif this.activeShape == Shapes.rect:
      l = newRect(this.points[0], this.points[0], this.lineWidth, this.fcolor)
    elif this.activeShape == Shapes.circ:
      l = newCirc(this.points[0], this.points[0], this.lineWidth, this.fcolor)

    l.style = Styles(this.cbtStyle.getActive)
    this.movingObj = l

  if this.points.len == 2:
    let l = this.movingObj
    this.movingObj = nil
    var el: L[2, float, Element]
    el = (boxEl(l, this), l)
    this.tree.insert(el)
    this.points.setLen(0)
  return gdk4.EVENT_PROPAGATE
 
proc distributeLegacyEvent(c: EventControllerLegacy; e: Event; this: PDA): bool =
  let et = e.getEventType
  case et
  of EventType.buttonPress, buttonRelease, motionNotify:
    var nx, ny: float
    let widget = this.darea
    var (x, y) = e.getPosition
    var native: gtk4.Native
    native = widget.getNative
    native.getSurfaceTransform(nx, ny)  
    let toplevel = widget.getRootWidget
    discard translateCoordinates(toplevel, widget, x - nx, y - ny, x, y) # TODO add getRootWindow()
    this.legEvX = x
    this.legEvY = y
  else: discard

  case e.getEventType
  of EventType.buttonPress:
    return buttonPressEvent(c, e, this)
  of EventType.buttonRelease:
    return buttonReleaseEvent(c, cast[ButtonEvent](e), this)
  of EventType.scroll:
    return scrollEvent(c, cast[ScrollEvent](e), this)
  of EventType.motionNotify:
    return onMotion(c, e, this)
  else:
    discard

proc shapeChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeShape = Shapes(cbt.getActive)

proc styleChanged(cbt: ComboBoxText) =
  echo cbt.getActiveText

proc onAdjustmentEvent(this: PosAdj; pda: PDA) =
  pda.paint
  pda.darea.queueDraw

proc onSetLineWidth(this: SpinButton; pda: PDA) =
  pda.lineWidth = this.value

proc newPDA: PDA =
  result = newGrid(PDA)
  initCData(result)
  let da = newDrawingArea()

  let legacy = newEventControllerLegacy()
  da.addController(legacy)
  legacy.connect("event", distributeLegacyEvent, result)

  result.lineWidth = DefaultLineWidth
  result.darea = da
  da.setHExpand
  da.setVExpand
  #da.connect("draw", drawingAreaDrawCb, result)
  da.setDrawFunc(drawingAreaDrawCb, result)
  da.connect("resize", dareaConfigureCallback, result)
  #da.addEvents({EventFlag.buttonPress, EventFlag.buttonRelease, pointerMotion,
  #    EventFlag.scroll, button1Motion, button2Motion, pointerMotionHint})
  #da.connect("motion-notify-event", onMotion, result)
  #da.connect("scroll_event", scrollEvent, result)
  #da.connect("button_press_event", buttonPressEvent, result)
  #da.connect("button_release_event", buttonReleaseEvent, result)

  #drag.setButton(BUTTON_PRIMARY)
  #da.addController(drag)
  #drag.connect("drag-begin", buttonPressEvent, result)
  #drag.connect("drag-update", onMotion, result)
  #drag.connect("drag-end", dragEnd, da)

  result.zoomNearMousepointer = ZoomNearMousepointer # mouse wheel zooming
  result.userZoom = 2.0#1.0
  result.grid = [100.0, 10]
  result.hadjustment = newPosAdj()
  result.hadjustment.handlerID = result.hadjustment.connect("value-changed", onAdjustmentEvent, result)
  result.vadjustment = newPosAdj()
  result.vadjustment.handlerID = result.vadjustment.connect("value-changed", onAdjustmentEvent, result)
  result.hscrollbar = newScrollbar(Orientation.horizontal, result.hadjustment)
  result.vscrollbar = newScrollbar(Orientation.vertical, result.vadjustment)
  result.hPaintable = cast[Paintable](newWidgetPaintable(result.hscrollbar))
  result.vPaintable = cast[Paintable](newWidgetPaintable(result.vscrollbar))
  result.hscrollbar.setHExpand
  result.vscrollbar.setVExpand
  result.hPaintable.connect("invalidate-size", hscrollbarSizeAllocateCallback, result)
  result.vPaintable.connect("invalidate-size", vscrollbarSizeAllocateCallback, result)
  result.attach(result.darea, 0, 0, 1, 1)
  result.attach(result.vscrollbar, 1, 0, 1, 1)
  result.attach(result.hscrollbar, 0, 1, 1, 1)
  result.headerbar = newHeaderBar()

  result.topbox = newBox(Orientation.horizontal, 0)
  result.topbox.append(newLabel("test0"))
  let adj = newAdjustment(0.2, 0, 1, 0.1, 0.1, 0) # value, min, max...
  let sb = newSpinButton(adj, 1, 3)
  sb.connect("value-changed", onSetLineWidth, result)
  result.topbox.append(sb)

  let cbtShape = newComboboxText()
  for el in Shapes:
    cbtShape.append(nil, $el)
  cbtShape.setActive(0)
  cbtShape.connect("changed", shapeChanged, result)
  result.topbox.append(cbtShape)

  let cbtStyle = newComboboxText()
  result.cbtStyle = cbtStyle
  for el in Styles:
    cbtStyle.append(nil, $el)
  cbtStyle.setActive(0)
  cbtStyle.connect("changed", styleChanged)
  result.topbox.append(cbtStyle)

  result.attach(result.topbox, 0, -1, 2, 1)
  result.botbox = newBox(Orientation.horizontal, 0)
  result.botbox.append(newLabel("test"))
  result.attach(result.botbox, 0, 2, 2, 1)

proc appStartup(app: Application) =
  echo "appStartup"

proc appActivate(app: Application) =
  let window = newApplicationWindow(app)
  window.title = "Drawing example"
  window.defaultSize = (2400, 1800)
  let pda = newPDA()
  window.setChild(pda)
  window.setTitlebar(pda.headerbar) # before window.show()
  show(window)

proc newDisplay*() =
  let app = newApplication("org.gtk.example")
  connect(app, "startup", appStartup)
  connect(app, "activate", appActivate)
  discard run(app)

when isMainModule:
  newDisplay() # 968 lines CPU drawSelected movingObj seq tree echo newLine hypot
