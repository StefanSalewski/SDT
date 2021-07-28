# Plain CAD tool using Nim, GTK and Cairo
#
# Basic drawing area behaviour like zooming, scrolling and panning is based on gintro/examples/gtk3/drawingarea.nim
# which again is based on an earlier Ruby implementation
#
# Main goal of this tool is to make fun using it.
#
# (c) S. Salewski 2020, 2021
# License MIT
# v0.1 2021-JUL-28

import std/[times, parseutils, strutils, strformat]
from std/math import round, floor, `^`, `mod`
from std/sequtils import mapIt
import gintro/[gtk4, gdk4, glib, gobject, gio, cairo, pango, pangocairo]
import rtree
import salewski, minmax #xpairs

const
  ZoomFactorMouseWheel = 1.1
  ZoomFactorSelectMax = 10 # ignore zooming in tiny selection
  ZoomNearMousepointer = true # mouse wheel zooming -- to mouse-pointer or center
  SelectRectCol = [0.0, 0, 1, 0.5] # blue with transparency

const
  DefaultWorldRange = [0.0, 0, 100, 100]
  DefaultGrid = [100.0 , 10, 100, 10]

const
  GrabDist = 3 # mm
  DefaultLineWidth = 0.2 # mm

const menuData = """
  <interface>
    <menu id="menuModel">
      <section>
        <item>
          <attribute name="label">Normal Menu Item</attribute>
          <attribute name="action">win.normal-menu-item</attribute>
        </item>
        <item>
          <attribute name="label">Group Selection</attribute>
          <attribute name="action">win.group-selection</attribute>
        </item>
        <submenu>
          <attribute name="label">Submenu</attribute>
          <item>
            <attribute name="label">Submenu Item</attribute>
            <attribute name="action">win.submenu-item</attribute>
          </item>
        </submenu>
        <item>
          <attribute name="label">Toggle Menu Item</attribute>
          <attribute name="action">win.toggle-menu-item</attribute>
        </item>
      </section>
      <section>
        <item>
          <attribute name="label">Radio 1</attribute>
          <attribute name="action">win.radio</attribute>
          <attribute name="target">1</attribute>
        </item>
        <item>
          <attribute name="label">Radio 2</attribute>
          <attribute name="action">win.radio</attribute>
          <attribute name="target">2</attribute>
        </item>
        <item>
          <attribute name="label">Radio 3</attribute>
          <attribute name="action">win.radio</attribute>
          <attribute name="target">3</attribute>
        </item>
      </section>
    </menu>
  </interface>"""

type
  RGBA = tuple[r, g, b, a: float]

type
  Style = object
    lineWidth: float
    lineCap: LineCap
    lineJoin: LineJoin
    color: RGBA # gdk4.RGBA ?

var styles: array[4, Style]
styles[0] = Style(lineWidth: 1.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0))
styles[1] = Style(lineWidth: 0.5, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (1.0, 0.0, 0.0, 1.0))
styles[2] = Style(lineWidth: 1.5, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 1.0, 0.0, 1.0))
styles[3] = Style(lineWidth: 4.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (1.0, 0.0, 0.0, 1.0))

type
  Shapes {.pure.} = enum
    line, rect, circ, text, trace, path

type
  Styles {.pure.} = enum
    medium, thin, thick, fat, none

type
  V2 = tuple[x, y: float]

type
  Grid = array[4, float] # major x, minor x, major y, minor y

proc `+=`(a: var V2; b: V2) =
  a.x += b.x
  a.y += b.y

proc `+`(a, b: V2): V2 =
  (a.x + b.x, a.y + b.y)

proc `-`(a, b: V2): V2 =
  (a.x - b.x, a.y - b.y)

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

proc sortedTuple(a, b: float): rtree.Ext[float] =
  if a <= b: (a, b) else: (b, a)

type
  Element = ref object of RootRef
    style: Styles
    p: seq[V2]
    width: float
    height: float
    hover: bool
    selected: bool
    text: string
    gx, gy: int # text grab
    grabPos: array[9, tuple[x, y: float]]
    isNew: bool

template x1(e: Element):float = e.p[0].x
template y1(e: Element):float  = e.p[0].y
template x2(e: Element):float  = e.p[1].x
template y2(e: Element):float  = e.p[1].y

template `x1=`(e: Element; v: float) = e.p[0].x = v
template `y1=`(e: Element; v: float) = e.p[0].y = v
template `x2=`(e: Element; v: float) = e.p[1].x = v
template `y2=`(e: Element; v: float) = e.p[1].y = v

type
  Line = ref object of Element

type
  Trace = ref object of Element

type
  Rect = ref object of Element

type
  Circ = ref object of Element

type
  Text = ref object of Element

type
  Path = ref object of Element

type
  Group = ref object of Element
    lines: seq[Line]
    circs: seq[Circ]

proc move(el: Element; v: V2) =
  for p in mitems(el.p):
    p += v

# constructors
proc newLine(p1, p2: V2): Line =
  Line(p: @[p1, p2])

proc newPath(p1, p2: V2): Path =
  Path(p: @[p1, p2])

proc newTrace(p1, p2: V2): Trace =
  Trace(p: @[p1, p2])

proc sortedPair(p1, p2: V2): tuple[a, b: V2] =
  (result[0].x, result[1].x) = sortedTuple(p1.x, p2.x)
  (result[0].y, result[1].y) = sortedTuple(p1.y, p2.y)

proc newRect(p1, p2: V2): Rect =
  let h = sortedPair(p1, p2)
  Rect(p: @[h[0], h[1]])
 
proc newCirc(p1, p2: V2): Circ =
  Circ(p: @[p1, p2])

proc newText(p1, p2: V2; text: string): Text =
  Text(p: @[p1, p2], text: text)

# distances
proc sqrDistanceLine(l: Line; x, y: float): float =
  distanceLinePointSqr(x1 = l.p[0].x, l.p[0].y, l.p[1].x, l.p[1].y, x, y)[1]

proc sqrDistancePath(l: Path; x, y: float): float =
  result = float.high
  for l in l.p.xpairs:
    let h = distanceLinePointSqr(l[0].x, l[0].y, l[1].x, l[1].y, x, y)[1]
    if h < result:
      result = h

proc sqrDistanceTrace(t: Trace; x, y: float): float =
  distanceLinePointSqr(x1 = t.p[0].x, t.p[0].y, t.p[1].x, t.p[1].y, x, y)[1]

proc sqrDistanceRB(x1, y1, x2, y2, x, y: float): float = # distance to rectangle border
  [(x1, y1, x1, y2), (x1, y1, x2, y1), (x2, y2, x1, y2), (x2, y2, x2, y1)].mapIt(distanceLinePointSqr(it[0], it[1], it[2], it[3], x, y)[1]).min

proc sqrDistanceR(x1, y1, x2, y2, x, y: float): float =
  if (x > x1 and x < x2) and (y > y1 and y < y2): # in rectangle
    return 0
  sqrDistanceRB(x1, y1, x2, y2, x, y) # distance to boarder

proc sqrDistanceRect(r: Rect; x, y: float): float =
  sqrDistanceR(r.x1, r.y1, r.x2, r.y2, x, y)
 
proc sqrDistanceCirc(c: Circ; x, y: float): float =
  max(math.hypot(c.x1 - x, c.y1 - y) - math.hypot(c.x1 - c.x2, c.y1 - c.y2), 0) ^ 2

proc sqrDistanceText(t: Text; x, y: float): float =
  var (x, y) = (x, y)
  x += t.width * (t.gx mod 3).float * 0.5
  y += t.height * (t.gy mod 3).float * 0.5
  sqrDistanceR(t.x1, t.y1, t.x2, t.y2, x, y)

proc sqrDistanceGroup(g: Group; x, y: float): float =
  sqrDistanceR(g.x1, g.y1, g.x2, g.y2, x, y)

type
  UserAction {.pure.} = enum
    none,
    lmbdv, # left mouse button pressed over void area
    lmbdo, # left mouse button pressed over object
    zooming,
    selecting,
    dragging

type
  Tree = RStarTree[8, 2, float, Element]

iterator allElements(tree: Tree; x: Element): Element =
  for el in tree.elements:
    yield el
  if x != nil:
    yield x

type
  PDA = ref object of gtk4.Grid
    entry: Entry
    world: Entry
    gridw: Entry
    cbtStyle: ComboBoxText
    activeShape: Shapes
    tree: Tree
    points: seq[V2]
    activeObj: Element
    movingObj: Element
    activeState: int 
    hover, lastHover: Element
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
    grid: Grid
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
    lastButtonDownPos: V2
    lastButtonDownPosUser: V2
    lastMousePos: V2
    zoomRect: V2
    oldSizeX: int
    oldSizeY: int
    legEvX, legEvY: float

### The gaction menu procs

proc changeLabelButton(action: gio.SimpleAction; parameter: glib.Variant; label: Label) =
  label.setLabel("Text set from button")

proc normalMenuItem(action: gio.SimpleAction; parameter: glib.Variant; label: Label) =
  label.setLabel("Text set from normal menu item")

proc toggleMenuItem(action: gio.SimpleAction; parameter: glib.Variant; label: Label) =
  let newState = newVariantBoolean(not action.getState.getBoolean)
  action.changeState(newState)
  label.setLabel("Text set from toggle menu item. Toggle state: " & $newState.getBoolean)

proc submenuItem(action: gio.SimpleAction; parameter: glib.Variant; label: Label) =
  label.setlabel("Text set from submenu item")

proc radio(action: gio.SimpleAction; parameter: glib.Variant; label: Label) =
  var l: uint64
  let newState: glib.Variant = newVariantString(parameter.getString(l))
  action.changeState(parameter)
  let str: string = "From Radio menu item " & getString(newState, l)
  label.setLabel(str)

###

proc initCData(result: var PDA) =
  result.tree = newRStarTree[8, 2, float, Element]()
  result.bcolor= [float 1, 1, 1, 1]
  result.majorGridColor= [float 0, 0, 0, 1]
  result.minorGridColor= [float 0, 0, 0, 0.4]
  result.guideColor= [float 1, 0, 0, 0.7]
  result.majorGrid = 100
  result.minorGrid = 10
  result.activeGrid = 10
  result.activeShape = Shapes.line

# we will fix this proc later, it's good enough for now
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
  pda.cr.setLineWidth(pda.absToScr(0.4))

proc setThinHairLineWidth(pda: PDA) =
  pda.cr.setLineWidth(pda.absToScr(0.15))

proc drawGrabX(pda: PDA; x, y: float) =
  let d = pda.absToScr(math.sin(math.Pi * 0.25) * GrabDist)
  pda.cr.moveTo(x - d, y - d)
  pda.cr.lineTo(x + d, y + d)
  pda.cr.moveTo(x - d, y + d)
  pda.cr.lineTo(x + d, y - d)
  pda.cr.stroke

proc drawGrabCirc(pda: PDA; x, y: float) =
  pda.cr.newPath
  pda.cr.arc(x, y, pda.absToScr(GrabDist), 0, math.Tau)
  pda.drawGrabX(x, y)
  pda.cr.stroke

# event coordinates to user space
proc getUserCoordinates(this: PDA; v: V2): V2 =
  ((v.x - this.hadjustment.upper * 0.5 + this.hadjustment.value) / (this.fullScale * this.userZoom) + this.dataX + this.dataWidth * 0.5,
   (v.y - this.vadjustment.upper * 0.5 + this.vadjustment.value) / (this.fullScale * this.userZoom) + this.dataY + this.dataHeight * 0.5)

proc roundToMultiple(x, m: float): float =
  ((x / m) + 0.5).floor * m

proc roundToGrid(pda: PDA; v: V2): V2 =
  (roundToMultiple(v.x, pda.activeGrid), roundToMultiple(v.y, pda.activeGrid))

proc cairoDevRound(w: float): float =
  if w < 1.5:
    0.5
  else:
    floor((w + 0.5) mod 2) / 2

proc move(pda: PDA): bool =
  let (a, b) = (pda.lastButtonDownPosUser)#.x, pda.lastButtonDownPosUser.y)
  let dxdy = pda.roundToGrid(pda.getUserCoordinates(pda.lastMousePos) - pda.lastButtonDownPosUser)
  let (x1, y1, x2, y2) = (pda.movingObj.x1, pda.movingObj.y1, pda.movingObj.x2, pda.movingObj.y2)

  if pda.movingObj of Path:
    let l = pda.movingObj
    let i = minIndexByIt(l.p, math.hypot(a - it.x, b - it.y))
    let p = l.p[i]
    if (a - p.x) ^ 2 + (b - p.y) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
      l.p[i] += dxdy
    else:
      move(pda.movingObj, dxdy)
  elif pda.movingObj of Rect:
    let d = pda.absToScr(GrabDist)
    if a > x1 - d and a < x2 + d and b > y1 - d and b < y2 + d:
      if a > x1 + d and a < x2 - d and b > y1 + d and b < y2 - d:
        pda.movingObj.p[0] += dxdy
        pda.movingObj.p[1] += dxdy
        pda.lastButtonDownPosUser += dxdy
        return true
      if a > x1 - d and a <  x1 + d:
        pda.movingObj.x1 += dxdy[0]
      elif a > x2 - d and a <  x2 + d:
        pda.movingObj.x2 += dxdy[0]
      if b > y1 - d and b <  y1 + d:
        pda.movingObj.y1 += dxdy[1]
      elif b > y2 - d and b <  y2 + d:
        pda.movingObj.y2 += dxdy[1]
  elif pda.movingObj of Group:
    move(pda.movingObj, dxdy)
    for el in Group(pda.movingObj).lines:
      move(el, dxdy)
    for el in Group(pda.movingObj).circs:
      move(el, dxdy)
  elif (a - pda.movingObj.x1) ^ 2 + (b - pda.movingObj.y1) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
    pda.movingObj.p[0] += dxdy
  elif (a - pda.movingObj.x2) ^ 2 + (b - pda.movingObj.y2) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
    pda.movingObj.p[1] += dxdy
  else:
    pda.movingObj.p[0] += dxdy
    pda.movingObj.p[1] += dxdy
  pda.lastButtonDownPosUser += dxdy
  return true

proc drawGrid(pda: PDA) =
  pda.cr.setOperator(Operator.over)
  var w = getLineWidth(pda.cr)
  w = deviceToUserDistance(pda.cr, w, 0)[0] # hypot?
  let rw = cairoDevRound(w)
  var (x1, y1) = getUserCoordinates(pda, (0.0, 0.0))
  var (x2, y2) = getUserCoordinates(pda, (pda.darea.allocatedWidth.float, pda.darea.allocatedHeight.float))
  pda.setThinHairLineWidth
  pda.cr.setSource(pda.minorGridColor)
  var x = x1.roundToMultiple(pda.grid[1]) # minor x
  while x < x2:
    if (x mod pda.grid[0]).abs > 0.1:
      var h = userToDevice(pda.cr, x, 0.0)[0].round + rw
      h = deviceToUser(pda.cr, h, 0.0)[0]
      pda.cr.moveTo(h, y1)
      pda.cr.lineTo(h, y2)
    x += pda.grid[1]
  pda.cr.stroke
  var y = y1.roundToMultiple(pda.grid[3]) # minor y
  while y < y2:
    if (y mod pda.grid[2]).abs > 0.1:
      var h = userToDevice(pda.cr, 0.0, y)[1].round + rw
      h = deviceToUser(pda.cr, 0.0, h)[1]
      pda.cr.moveTo(x1, h)
      pda.cr.lineTo(x2, h)
    y += pda.grid[3]
  pda.cr.stroke
  #
  pda.setHairLineWidth
  pda.cr.setSource(pda.majorGridColor)
  x = x1.roundToMultiple(pda.grid[0]) # major x
  while x < x2:
    var h = userToDevice(pda.cr, x, 0.0)[0].round + rw
    h = deviceToUser(pda.cr, h, 0.0)[0]
    pda.cr.moveTo(h, y1)
    pda.cr.lineTo(h, y2)
    x += pda.grid[0]
  pda.cr.stroke
  y = y1.roundToMultiple(pda.grid[2]) # major y
  while y < y2:
    var h = userToDevice(pda.cr, 0.0, y)[1].round + rw
    h = deviceToUser(pda.cr, 0.0, h)[1]
    pda.cr.moveTo(x1, h)
    pda.cr.lineTo(x2, h)
    y += pda.grid[2]
  pda.cr.stroke

# we have 4 visible states:
# type VState = enum plain, selected, hover, selectedHover
# We draw the objects only once.
# First we use a grey, translated copy of the objects for the shadow.
# Then we draw all plain elements. After that we draw the
#  hover, selectedHover objects to get brigher colors.
# we call this proc twice -- with plain group and with selected group

# bounding box

proc boxGrow(b: var rtree.Box[2, float]; c: rtree.Box[2, float]) =
  for i in 0 .. 1:
    if b[i].a > c[i].a:
      b[i].a = c[i].a
    if b[i].b < c[i].b:
      b[i].b = c[i].b

proc box(l: Element; pda: PDA): rtree.Box[2, float] =
  [sortedTuple(l.x1, l.x2), sortedTuple(l.y1, l.y2)]

proc boxCirc(c: Circ; pda: PDA): rtree.Box[2, float] =
  let r = math.hypot(c.x1 - c.x2, c.y1 - c.y2)
  [(c.x1 - r, c.x1 + r), (c.y1 - r, c.y1 + r)]

proc boxText(t: Text; pda: PDA): rtree.Box[2, float] =
  let dx = -t.width * (t.gx mod 3).float * 0.5
  let dy = -t.height * (t.gy mod 3).float * 0.5
  [(t.x1 + dx, t.x2 + dx), (t.y1 + dy, t.y2 + dy)]

proc boxPath(l: Path; pda: PDA): rtree.Box[2, float] =
  var (xa, xb, ya, yb) = (l.p[0].x, l.p[0].x, l.p[0].y, l.p[0].y)
  for el in l.p:
    if el.x < xa:
      xa = el.x
    if el.x > xb:
      xb = el.x
    if el.y < ya:
      ya = el.y
    if el.y > yb:
      yb = el.y
  [(xa, xb), (ya, yb)]

proc boxEl(el: Element; pda: PDA): rtree.Box[2, float] =
  if el of Line or el of Trace or el of Rect or el of Group:
    result = box(el, pda)
  elif el of Circ:
    result = boxCirc(Circ(el), pda)
  elif el of Text:
    result = boxText(Text(el), pda)
  elif el of Path:
    result = boxPath(Path(el), pda)

proc groupSelection(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  var collector: seq[Element]
  var box: rtree.Box[2, float]
  for el in pda.tree.allElements(nil):
    if el.selected:
      collector.add(el)
  box = boxEl(collector[0], pda)
  for el in collector:
    box.boxGrow(boxEl(el, pda))
    var eb: L[2, float, Element]
    eb = (boxEl(el, pda), el)
    discard pda.tree.delete(eb)
  var g = Group(p: @[(box[0].a, box[1].a), (box[0].b, box[1].b)])
  for el in collector:
    if el of Line:
      g.lines.add(Line(el))
    elif el of Circ:
      g.circs.add(Circ(el))
  var gb: L[2, float, Element]
  gb = (box, g)
  pda.tree.insert(gb)

proc drawLine(l: Line; pda: PDA) =
  pda.cr.moveTo(l.x1, l.y1)
  pda.cr.lineTo(l.x2, l.y2)

proc drawPath(l: Path; pda: PDA) =
  pda.cr.newPath
  for p in l.p:
    pda.cr.lineTo(p.x, p.y)

proc drawTrace(l: Trace; pda: PDA) =
  pda.cr.moveTo(l.x1, l.y1)
  pda.cr.lineTo(l.x2, l.y2)

proc drawRect(r: Rect; pda: PDA) = # rectangle
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)

proc drawText(t: Text; pda: PDA) =
  const Font = "Serif 8px"
  var context = pda.darea.createPangoContext
  var layout = pango.newLayout(context)
  var desc = pango.newFontDescription(Font)
  pda.cr.moveTo(t.x1, t.y1)
  layout.setText(t.text)
  layout.setFontDescription(desc)
  var w, h : int
  layout.getSize(w, h)
  t.width = w.float / pango.Scale.float
  t.height = h.float / pango.Scale.float
  t.p[1] = t.p[0] + (t.width, t.height)
  let dx = -t.width * (t.gx mod 3).float * 0.5
  let dy = -t.height * (t.gy mod 3).float * 0.5
  pda.cr.moveTo(t.x1 + dx, t.y1 + dy)
  pda.cr.updateLayout(layout)
  pangocairo.showLayout(pda.cr, layout)
  if t.isNew:
    var el: L[2, float, Element] = (boxEl(t, pda), t)
    pda.tree.insert(el)
    t.isNew = false
    pda.movingObj = nil
  for i in 0 .. 8:
    let x = t.x1 + t.width * (i mod 3).float * 0.5
    let y = t.y1 + t.height * (i div 3).float * 0.5
    t.grabPos[i] = (x + dx, y + dy)

proc drawCirc(c: Circ; pda: PDA) =
  let r = math.hypot(c.x1 - c.x2,  c.y1 - c.y2)
  pda.cr.newPath
  pda.cr.arc(c.x1, c.y1, r, 0, math.Tau)

proc drawGroup(g: Group; pda: PDA) =
  for l in g.lines:
    pda.cr.setSource(styles[l.style.ord].color)
    pda.setLineWidthAbs(styles[l.style.ord].lineWidth) # extend is still missing
    drawLine(l, pda)
    pda.cr.stroke
  for l in g.circs:
    pda.setLineWidthAbs(styles[l.style.ord].lineWidth)
    pda.cr.setSource(styles[l.style.ord].color)
    drawCirc(l, pda)
    pda.cr.stroke

proc initDrawGrab(pda: PDA) =
  pda.cr.setSource(1, 0, 0)
  pda.setHairLineWidth

proc drawTextGrab(t: Text; pda: PDA) =
  initDrawGrab(pda)
  let dx = -t.width * (t.gx mod 3).float * 0.5
  let dy = -t.height * (t.gy mod 3).float * 0.5
  pda.cr.rectangle(t.x1 + dx, t.y1 + dy, t.width, t.height)
  pda.cr.stroke
  for i in 0 .. 8:
      pda.drawGrabCirc(t.grabPos[i].x, t.grabPos[i].y)
  
proc drawLineGrab(l: Line; pda: PDA) =
  initDrawGrab(pda)
  pda.drawGrabCirc(l.x1, l.y1)
  pda.drawGrabCirc(l.x2, l.y2)
  let dx = pda.absToScr((l.y2 - l.y1) / math.hypot(l.x2 - l.x1, l.y2 - l.y1) * GrabDist)
  let dy = pda.absToScr(-(l.x2 - l.x1) / math.hypot(l.x2 - l.x1, l.y2 - l.y1) * GrabDist)
  pda.cr.moveTo(l.x1 + dx, l.y1 + dy)
  pda.cr.lineTo(l.x2 + dx, l.y2 + dy)
  pda.cr.moveTo(l.x1 - dx, l.y1 - dy)
  pda.cr.lineTo(l.x2 - dx, l.y2 - dy)
  pda.cr.stroke

proc drawPathGrab(l: Path; pda: PDA) =
  initDrawGrab(pda)
  for p in l.p.pairwise:
    var a: V2 = p[0]
    var b: V2 = p[1]
    let h = math.hypot(b.x - a.x, b.y - a.y)
    let dx = pda.absToScr((b.y - a.y) / h * GrabDist)
    let dy = pda.absToScr(-(b.x - a.x) / h * GrabDist)
    pda.cr.moveTo(a.x + dx, a.y + dy)
    pda.cr.lineTo(b.x + dx, b.y + dy)
    pda.cr.moveTo(a.x - dx, a.y - dy)
    pda.cr.lineTo(b.x - dx, b.y - dy)
  pda.cr.stroke
  for p in l.p:
    pda.drawGrabCirc(p.x, p.y)

proc drawTraceGrab(l: Trace; pda: PDA) =
  initDrawGrab(pda)
  pda.drawGrabCirc(l.x1, l.y1)
  pda.drawGrabCirc(l.x2, l.y2)
  let dx = pda.absToScr((l.y2 - l.y1) / math.hypot(l.x2 - l.x1, l.y2 - l.y1) * GrabDist)
  let dy = pda.absToScr(-(l.x2 - l.x1) / math.hypot(l.x2 - l.x1, l.y2 - l.y1) * GrabDist)
  pda.cr.moveTo(l.x1 + dx, l.y1 + dy)
  pda.cr.lineTo(l.x2 + dx, l.y2 + dy)
  pda.cr.moveTo(l.x1 - dx, l.y1 - dy)
  pda.cr.lineTo(l.x2 - dx, l.y2 - dy)
  pda.cr.stroke

proc drawCircGrab(c: Circ; pda: PDA) =
  initDrawGrab(pda)
  pda.drawGrabCirc(c.x1, c.y1)
  let d = pda.absToScr(GrabDist)
  let r = math.hypot(c.x1 - c.x2,  c.y1 - c.y2)
  pda.cr.newPath
  pda.cr.arc(c.x1, c.y1, r + d, 0, math.Tau)
  pda.cr.stroke
  pda.cr.newPath
  pda.cr.arc(c.x1, c.y1, r - d, 0, math.Tau)
  pda.cr.stroke
  pda.drawGrabCirc(c.x2, c.y2)

proc drawRectGrab(r: Rect; pda: PDA) =
  initDrawGrab(pda)
  let d = pda.absToScr(GrabDist)
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

proc drawGroupGrab(r: Group; pda: PDA) =
  pda.cr.setSource(0, 0, 1, 0.1)
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)
  pda.cr.fill

proc sqrDistance(el: Element; x, y: float): float =
  if el of Line:
    result = sqrDistanceLine(Line(el), x, y)
  elif el of Path:
    result = sqrDistancePath(Path(el), x, y)
  elif el of Trace:
    result = sqrDistanceTrace(Trace(el), x, y)
  elif el of Rect:
    result = sqrDistanceRect(Rect(el), x, y)
  elif el of Circ:
    result = sqrDistanceCirc(Circ(el), x, y)
  elif el of Text:
    result = sqrDistanceText(Text(el), x, y)
  elif el of Group:
    result = sqrDistanceGroup(Group(el), x, y)

# squared distance from query point to
proc dist(qo: BoxCenter[2, float]; el: L[2, float, Element]): float =
  sqrDistance(el.l, qo[0], qo[1])

proc drawEl(el: RootRef; pda: PDA) =
  if el of Line:
    drawLine(Line(el), pda)
  elif el of Path:
    drawPath(Path(el), pda)
  elif el of Trace:
    pda.cr.setLineCap(LineCap.round)
    drawTrace(Trace(el), pda)
  elif el of Rect:
    drawRect(Rect(el), pda)
  elif el of Circ:
    drawCirc(Circ(el), pda)
  elif el of Text:
    drawText(Text(el), pda)
  elif el of Group:
    drawGroup(Group(el), pda)

proc drawElGrab(el: Element; pda: PDA) =
  if el of Line:
    drawLineGrab(Line(el), pda)
  elif el of Path:
    drawPathGrab(Path(el), pda)

  elif el of Trace:
    if styles[el.style.ord].lineWidth < 0.8 * GrabDist:
      drawTraceGrab(Trace(el), pda)

  elif el of Rect:
    drawRectGrab(Rect(el), pda)
  elif el of Circ:
    drawCircGrab(Circ(el), pda)
  elif el of Text:
    drawTextGrab(Text(el), pda)
  elif el of Group:
    drawGroupGrab(Group(el), pda)

proc draw(pda: PDA) =
  pda.cr.setSource(1, 1, 1)
  pda.cr.paint
  pda.cr.setLineWidth(1)
  pda.cr.setSource(0, 0, 0)
  pda.drawGrid
  pda.cr.setOperator(Operator.over)
  for selected in [false, true]:
    for hov in [false, true]:
      pda.cr.pushGroup
      for l in pda.tree.allElements(pda.movingObj):
        if l.selected != selected: continue
        if hov != (l == pda.hover): continue
        pda.cr.setSource(styles[l.style.ord].color) # for text, set color before calling the draw procs
        drawEl(l, pda)
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
        pda.cr.setSource(styles[l.style.ord].color) # for text, set color before calling the draw procs
        drawEl(l, pda)
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

proc drawingAreaDrawCb(darea: DrawingArea; cr: cairo.Context; width, height: int; this: PDA) =
  if this.pattern.isNil: return
  var t0 = cpuTime()
  cr.setSource(this.pattern)
  cr.paint
  #echo "CPU time [s] ", cpuTime() - t0
  if this.selecting:
    cr.rectangle(this.lastButtonDownPos.x, this.lastButtonDownPos.y, this.zoomRect.x - this.lastButtonDownPos.x, this.zoomRect.y - this.lastButtonDownPos.y)
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

proc paint(this: PDA; queueDraw = true) =
  this.cr.save
  this.cr.translate(this.hadjustment.upper * 0.5 - this.hadjustment.value, # our origin is the center
    this.vadjustment.upper * 0.5 - this.vadjustment.value)
  this.cr.scale(this.fullScale * this.userZoom, this.fullScale * this.userZoom)
  this.cr.translate(-this.dataX - this.dataWidth * 0.5, -this.dataY - this.dataHeight * 0.5)
  draw(this)
  this.cr.restore
  if queueDraw:
    this.darea.queueDraw

proc dareaConfigureCallback(darea: DrawingArea; width, height: int; this: PDA) =
  this.fullScale = min(this.darea.allocatedWidth.float / this.dataWidth, this.darea.allocatedHeight.float / this.dataHeight)
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
  updateAdjustments(this, 0, 0)
  this.paint(false)

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

proc onMotion(c: EventControllerLegacy; e: Event; this: PDA): bool =
  let x = this.legEvX
  let y = this.legEvY
  let (a, b) = this.getUserCoordinates((x, y))
  #echo "::: ", a, " ", b

  if this.uact == dragging and this.movingObj != nil:
    this.lastMousePos = (x, y)
    discard this.move
    paint(this)

  if math.hypot(x - this.lastButtonDownPos.x, y - this.lastButtonDownPos.y) > 2:
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
    if el of Circ:
      echo "Circ"
    elif el of Line:
      echo "Line"
    if sqrDistance(el, a, b) < (this.absToScr(GrabDist)) ^ 2:
      this.hover = el
      el.hover = true
    else:
      this.hover = nil

  if this.uact == selecting:#state.contains(button1): # selecting
    this.selecting = true
    this.zoomRect = (x, y)
    this.darea.queueDraw#Area(0, 0, this.darea.allocatedWidth, this.darea.allocatedHeight)
  elif false:#button2 in state: # panning
    this.updateAdjustmentsAndPaint(this.lastMousePos.x - x, this.lastMousePos.y - y)
  this.lastMousePos = (x, y)
  if this.points.len > 0 or this.hover != this.lastHover:
    if this.points.len == 1:
      let p = this.roundToGrid((a, b))
      if this.movingObj of Path:
        this.movingObj.p[^1] = p
      else:
        this.movingObj.p[1] = p
    paint(this)
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
  this.lastMousePos = (x, y)
  this.lastButtonDownPos = (x, y)
  (this.lastButtonDownPosUser.x, this.lastButtonDownPosUser.y) = this.getUserCoordinates((x, y))
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
      this.uact = UserAction.none
      return
  if this.uact == UserAction.lmbdo and this.hover != nil:
    this.movingObj = nil
    this.uact = UserAction.none
    if this.hover of Text:
      let olddx = -this.hover.width * (this.hover.gx mod 3).float * 0.5
      let olddy = -this.hover.height * (this.hover.gy mod 3).float * 0.5
      for i in 0 .. 8:
        let (x, y) = this.getUserCoordinates((x, y))
        if (x - this.hover.grabPos[i].x) ^ 2 + (y - this.hover.grabPos[i].y) ^ 2 < this.absToScr(GrabDist) ^ 2:
          var el: L[2, float, Element]
          el = (boxEl(this.hover, this), this.hover)
          discard this.tree.delete(el)
          this.hover.gx = i mod 3
          this.hover.gy = i div 3
          var dx = -this.hover.width * (this.hover.gx mod 3).float * 0.5
          var dy = -this.hover.height * (this.hover.gy mod 3).float * 0.5
          var dxdy = this.roundToGrid((olddx - dx, olddy - dy))
          this.hover.p[0] += dxdy
          this.hover.p[1] += dxdy
          this.movingObj = this.hover
          this.hover.isNew = true
          paint(this)
          break
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
  let ucr = this.roundToGrid(uc)
  if this.uact == dragging:
    this.uact = UserAction.none
  if this.uact in {lmbdo, lmbdv}:
    this.points.add(ucr)
  var needsRefresh = false
  if this.points.len == 1:
    var l: Element
    if this.activeShape == Shapes.line:
      l = newLine(this.points[0], this.points[0])
    elif this.activeShape == Shapes.path:
      l = newPath(this.points[0], this.points[0])
      echo "newpath"
    elif this.activeShape == Shapes.trace:
      #echo "newtrace"
      l = newTrace(this.points[0], this.points[0])
    elif this.activeShape == Shapes.rect:
      l = newRect(this.points[0], this.points[0])
    elif this.activeShape == Shapes.circ:
      l = newCirc(this.points[0], this.points[0])
    elif this.activeShape == Shapes.text:
      l = newText(this.points[0], this.points[0], "|")
      this.entry.setText("")
      this.entry.setPlaceholderText("New Text")
      discard this.entry.grabFocus
      this.points.setLen(0)
      needsRefresh = true
    l.style = Styles(this.cbtStyle.getActive)
    this.movingObj = l
  if this.points.len == 2:
    let l = this.movingObj
    if l of Path:
      if this.points[0] == this.points[1]:
        l.p.setLen(l.p.len - 1)
        this.movingObj = nil
        var el: L[2, float, Element] = (boxEl(l, this), l)
        this.tree.insert(el)
        this.points.setLen(0)
      else:
        l.p.add(this.points[0])
        this.points[0] = this.points[1]
        this.points.setLen(1)
    else:
      this.movingObj = nil
      var el: L[2, float, Element] = (boxEl(l, this), l)
      this.tree.insert(el)
      this.points.setLen(0)
  if needsRefresh:
    paint(this)
  return gdk4.EVENT_PROPAGATE
 
proc distributeLegacyEvent(c: EventControllerLegacy; e: Event; this: PDA): bool =
  let et = e.getEventType
  case et
  of EventType.buttonPress, buttonRelease, motionNotify:
    var nx, ny: float
    let widget = this.darea
    var (x, y) = e.getPosition
    var native: gtk4.Native = widget.getNative
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

proc entryNotify(entry: Entry; paramSpec: ParamSpec; pda: PDA) =
  if pda.movingObj of Text:
    Text(pda.movingObj).text = entry.text
    let c = entry.getPosition
    Text(pda.movingObj).text.insert("|", c)
    pda.paint

proc entryActivate(entry: Entry; pda: PDA) =
  if pda.movingObj != nil:
    Text(pda.movingObj).text = entry.text
    Text(pda.movingObj).isNew = true
    pda.paint

proc worldActivate(entry: Entry; pda: PDA) =
  var
    d: array[4, float] = [NaN, NaN, NaN, NaN]
    s: array[4, bool]
    t = entry.text
    i, j, k: int
    f: float
  i = 1
  entry.setIconFromIconName(EntryIconPosition.secondary, nil)
  for c in mitems(t):
    if c in {';', ','}:
      inc(i)
      c = ' '
    if c in {'0' .. '9'}:
      i = 0
    if i > 1:
      entry.setIconFromIconName(EntryIconPosition.secondary, "dialog-error")
      return
  while k < d.len:
    i = t.skipWhitespace(j)
    j += i
    if j == t.len:
      break
    s[k] = t[j] == '+'
    i = t.parseFloat(f, j)
    j += i
    if i > 0:
      d[k] = f
    inc(k)
  if k == 1:
    d[1] = d[0]
  elif k == 3:
    d[3] = d[2]
    s[3] = s[2]
  case k
  of 0:
    d = DefaultWorldRange
  of 1, 2:
    d[3] = d[1]
    d[2] = d[0]
    d[0] = 0
    d[1] = 0
  of 3, 4:
    if not s[2]:
      d[2] -= d[0]
    if not s[3]:
      d[3] -= d[1]
  else:
    discard
  t.setLen(0)
  for f in d:
    t.add(fmt("{f:g}, "))
  t.setlen(t.len - 2)
  entry.setText(t)
  (pda.dataX, pda.dataY, pda.dataWidth, pda.dataHeight) = d # (d[0], d[1], d[2], d[3])
  pda.fullScale = min(pda.darea.allocatedWidth.float / pda.dataWidth, pda.darea.allocatedHeight.float / pda.dataHeight)
  updateAdjustments(pda, 0, 0)
  pda.paint

proc gridActivate(entry: Entry; pda: PDA) =
  var
    d: array[4, float] = [NaN, NaN, NaN, NaN]
    t = entry.text
    i, j, k: int
    f: float
  i = 1
  entry.setIconFromIconName(EntryIconPosition.secondary, nil)
  for c in mitems(t):
    if c in {';', ','}:
      inc(i)
      c = ' '
    if c in {'0' .. '9'}:
      i = 0
    if i > 1:
      entry.setIconFromIconName(EntryIconPosition.secondary, "dialog-error")
      return
  while k < d.len:
    i = t.skipWhitespace(j)
    j += i
    if j == t.len:
      break
    i = t.parseFloat(f, j)
    j += i
    if i > 0:
      d[k] = f
    inc(k)
  if k == 1:
    d[1] = d[0] / 10
  elif k == 3:
    d[3] = d[2]
  case k
  of 0:
    d = DefaultGrid
  of 1, 2:
    d[3] = d[1]
    d[2] = d[0]
  else:
    discard
  t.setLen(0)
  for f in d:
    t.add(fmt("{f:g}, "))
  t.setlen(t.len - 2)
  entry.setText(t)
  # TODO check d for NaN, positive, useful value
  pda.grid = d
  pda.paint

proc entryChanged(entry: Entry; pda: PDA) =
  if pda.movingObj of Text:
    Text(pda.movingObj).text = entry.text
    pda.paint

proc shapeChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeShape = Shapes(cbt.getActive)

proc styleChanged(cbt: ComboBoxText) =
  echo cbt.getActiveText

proc onAdjustmentEvent(this: PosAdj; pda: PDA) =
  pda.paint

proc onSetLineWidth(this: SpinButton; pda: PDA) =
  pda.lineWidth = this.value

proc newPDA(window: ApplicationWindow): PDA =
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
  da.setDrawFunc(drawingAreaDrawCb, result)
  da.connect("resize", dareaConfigureCallback, result)
  result.zoomNearMousepointer = ZoomNearMousepointer # mouse wheel zooming
  result.userZoom = 1.0
  result.grid = DefaultGrid
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

  let entry = newEntry()
  entry.connect("activate", entryActivate, result)
  entry.connect("changed", entryChanged, result)
  entry.connect("notify::cursor-position", entryNotify, result)
  result.entry = entry
  result.topbox.append(entry)

  let world = newEntry()
  world.setPlaceholderText("0, 0, 100, 100")
  world.setWidthChars(16)
  world.connect("activate", worldActivate, result)
  let worldLabel = newLabel()
  let worldImage = newImageFromIconName("video-display")
  worldImage.setIconSize(IconSize.large)
  #worldLabel.setUseMarkup(true)
  worldLabel.setMarkup("<big>\u{265A}</big>")
  result.topbox.append(worldImage)
  #result.topbox.append(worldLabel)
  result.topbox.append(world)
  result.world = world

  ### grid entry
  let grid = newEntry()
  grid.setPlaceholderText("100, 100, 10, 10")
  grid.setWidthChars(16)
  grid.connect("activate", gridActivate, result)
  let gridLabel = newLabel()
  gridLabel.setMarkup("<big>\u{25A6}</big>")
  result.topbox.append(gridLabel)
  result.topbox.append(grid)
  result.gridw = grid

  ### gaction menu
  var label = newLabel("test")

  let menubutton = newMenuButton()
  let actionGroup: gio.SimpleActionGroup = newSimpleActionGroup()

  var action: SimpleAction
  action = newSimpleAction("change-label-button")
  discard action.connect("activate", changeLabelButton, label)
  actionGroup.addAction(action)

  action = newSimpleAction("normal-menu-item")
  discard action.connect("activate", normalMenuItem, label)
  actionGroup.addAction(action)

  action = newSimpleAction("group-selection")
  discard action.connect("activate", groupSelection, result)
  actionGroup.addAction(action)

  var v = newVariantBoolean(true)
  action = newSimpleActionStateful("toggle-menu-item", nil, v)
  discard action.connect("activate", toggleMenuItem, label)
  actionGroup.addAction(action)

  action = newSimpleAction("submenu-item")
  discard action.connect("activate", submenuItem, label)
  actionGroup.addAction(action)

  v = newVariantString("1")
  let vt = newVariantType("s")
  action = newSimpleActionStateful("radio", vt, v)
  discard action.connect("activate", radio, label)
  actionGroup.addAction(action)
  window.insertActionGroup("win", actionGroup)

  var builder = newBuilderFromString(menuData)
  var menuModel: gio.MenuModel = builder.getMenuModel("menuModel")
  var menu = newPopoverMenuFromModel(menuModel)
  menuButton.setPopover(menu)
  result.topbox.append(menubutton)

  ###
  result.attach(result.topbox, 0, -1, 2, 1)
  result.botbox = newBox(Orientation.horizontal, 0)
  result.botbox.append(label)
  result.attach(result.botbox, 0, 2, 2, 1)

proc appStartup(app: Application) =
  echo "appStartup"

proc appActivate(app: Application) =
  let window = newApplicationWindow(app)
  window.title = "Drawing example"
  window.defaultSize = (2400, 1800)
  let pda = newPDA(window)
  (pda.dataX, pda.dataY, pda.dataWidth, pda.dataHeight) = DefaultWorldRange
  window.setChild(pda)
  window.setTitlebar(pda.headerbar) # before window.show()
  show(window)

proc newDisplay*() =
  let app = newApplication("org.gtk.example")
  connect(app, "startup", appStartup)
  connect(app, "activate", appActivate)
  discard run(app)

when isMainModule: # 1497 lines
  newDisplay()
