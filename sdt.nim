{.warning[CStringConv]: off.}

# Plain CAD tool using Nim, GTK and Cairo
#
# Basic drawing area behaviour like zooming, scrolling and panning is based on gintro/examples/gtk3/drawingarea.nim
# which again is based on an earlier Ruby implementation
#
# Main goal of this tool is to make fun using it.
#
# (c) S. Salewski 2020, 2021
# License MIT
# v0.1 2021-OCT-25

import std/[times, parseutils, strutils, strformat, strscans, json, macros]#, json, jsonutils]
#import yaml/serialization, streams

from std/math import round, floor, `^`, `mod`
from std/sugar import `=>`
from std/sequtils import mapIt, applyIt, filter
import gintro/[gtk4, gdk4, glib, gobject, gio, cairo, pango, pangocairo]
import rtree
import salewski, minmax #xpairs

const # make config option later
  HoleDia = 10
  HoleDrill = 6

const
  ### SchematicGrid = 10 # base unit in schematic mode, pin length should be 20 or 30
  PinHotEnd = 2.5

const
  ZoomFactorMouseWheel = 1.1
  ### ZoomFactorSelectMax = 10         # ignore zooming in tiny selection
  ZoomNearMousepointer = true      # mouse wheel zooming -- to mouse-pointer or center
  SelectRectCol = [0.0, 0, 1, 0.5] # blue with transparency

const
  DefaultWindowSize = (2400, 1800)
  DefaultWorldRange = [0.0, 0, 600, 400]
  DefaultGrid = [100.0, 10, 100, 10]
  HairLineWidth = 0.2 # mm
  ThinHairLineWidth = 0.1 # mm

const
  GrabDist = 1.5 # mm
  DefaultLineWidth = 0.2 # mm

const useNewDelMenuData = """
  <interface>
    <menu id="menuModel2">
      <section>
        <item>
          <attribute name="label">Use</attribute>
          <attribute name="action">win.use-line-width</attribute>
        </item>
        <item>
          <attribute name="label">New</attribute>
          <attribute name="action">win.new-line-width</attribute>
        </item>
        <item>
          <attribute name="label">Del</attribute>
          <attribute name="action">win.del-line-width</attribute>
        </item>
      </section>
    </menu>
  </interface>"""

const menuData = """
  <interface>
    <menu id="menuModel">
      <section>
        <item>
          <attribute name="label">Create Group</attribute>
          <attribute name="action">win.group-selection</attribute>
        </item>
        <item>
          <attribute name="label">Break up Group</attribute>
          <attribute name="action">win.break-up-group</attribute>
        </item>

        <item>
          <attribute name="label">Save Group</attribute>
          <attribute name="action">win.save-group</attribute>
        </item>
        <item>
          <attribute name="label">Load Group</attribute>
          <attribute name="action">win.load-group</attribute>
        </item>
        <item>
          <attribute name="label">Detach Text</attribute>
          <attribute name="action">win.detach-text</attribute>
        </item>
        <item>
          <attribute name="label">Attach Text</attribute>
          <attribute name="action">win.attach-text</attribute>
        </item>
        <item>
          <attribute name="label">Edit Text</attribute>
          <attribute name="action">win.edit-text</attribute>
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
        <item>
          <attribute name="label">Show Pad Numbers</attribute>
          <attribute name="action">win.toggle-show-pad-numbers</attribute>
        </item>
        <item>
          <attribute name="label">Show Pad Names</attribute>
          <attribute name="action">win.toggle-show-pad-names</attribute>
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
    textSize: float
    relSize: bool
    lineCap: LineCap
    lineJoin: LineJoin
    color: RGBA
    xcolor: RGBA # second color: fill, text background, pin hot end and such

type
  Fonts {.pure.} = enum
    Sans, Serif

type
  Modes {.pure.} = enum
    cad, sch, pcb

type
  Shapes {.pure.} = enum
    line, rect, pad, hole, circ, text, trace, path, pin, attr

type
  LineCaps {.pure.} = enum
    butt, round, square

type
  LineJoins {.pure.} = enum
    miter, round, bevel

type
  Styles {.pure.} = enum
    medium, thin, thick, fat, pin, sym, pad, hole, none

type
  LineWidths {.pure.} = enum
    default, thin, thick

type
  Colors {.pure.} = enum
    red, gree, blue

type
  Sizes {.pure.} = enum
    pinNumber, pinLabel, junction, shadow

const
  CvRed = [1.0, 0, 0, 0.8]
  #CvGreen = [0.0, 1, 0, 0.8]
  CvBlue = [0.0, 0, 1, 1]
  CvWhite = [1.0, 1, 1, 1]
  CvBlack = [0.0, 0, 0, 0.8]
  CvGray = [0.5, 0.5, 0.5, 0.8]

type
  XColors {.pure.} = enum
    bigGrid, smallGrid, background, shadow, alert, junction, pinNumber, pinName, grab

const
  XColorValues = [CVGray, CvGray, CvWhite, CvBlack, CvRed, CvBlue, CvBlue, CvBlue, CvRed]

# we could use the enums as indices directly, but later we do user extent the style set...
var styles: array[8, Style]
#for s in mitems(styles):
#  s.textSize = 16
styles[Styles.medium.ord] = Style(lineWidth: 1.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0), textSize: 16)
styles[Styles.thin.ord] = Style(lineWidth: 0.5, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (1.0, 0.0, 0.0, 1.0))
styles[Styles.thick.ord] = Style(lineWidth: 1.5, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 1.0, 0.0, 1.0))
styles[Styles.fat.ord] = Style(lineWidth: 4.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (1.0, 0.0, 0.0, 1.0))
styles[Styles.pin.ord] = Style(lineWidth: 1.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0), xcolor: (1.0, 0.0, 0.0, 1.0), relSize: true, textSize: 8)
styles[Styles.sym.ord] = Style(lineWidth: 1.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0), xcolor: (1.0, 0.0, 0.0, 1.0), relSize: true)
styles[Styles.pad.ord] = Style(lineWidth: 0.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0), xcolor: (1.0, 1.0, 1.0, 1.0))
styles[Styles.hole.ord] = Style(lineWidth: 0.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0), xcolor: (1.0, 1.0, 1.0, 1.0))
#for s in mitems(styles):
#  s.textSize = 16

type
  V2 = array[2, float]

type
  Grid = array[4, float] # major x, minor x, major y, minor y

#proc sort(a, b: var float) =

proc `+=`(a: var V2; b: V2) =
  a[0] += b[0]
  a[1] += b[1]

proc `+`(a, b: V2): V2 =
  [a[0] + b[0], a[1] + b[1]]

proc `-`(a, b: V2): V2 =
  [a[0] - b[0], a[1] - b[1]]

proc jecho(x: varargs[string, `$`]) =
  for el in x:
    stdout.write(el & " ")
  stdout.write('\n')
  stdout.flushfile

### helper procs for strscan module

proc sep(input: string; start: int; seps: set[char] = {' ',',',';'}): int =
  while start + result < input.len and input[start + result] in {' ','\t'}:
    inc(result)
  if start + result < input.len and input[start + result] in {';',','}:
    inc(result)
  while start + result < input.len and input[start + result] in {' ','\t'}:
    inc(result)

proc skipName(input: string; start: int; seps: set[char] = strutils.Letters): int =
  while start + result < input.len and input[start + result] in seps:
    inc(result)

proc plus(input: string; plusVal: var int; start: int; n: int): int =
  result = sep(input, start)
  if start + result < input.len and input[start + result] == '+':
    plusVal = 1 # bool
    result += 1

proc minus(input: string; minusVal: var int; start: int; n: int): int =
  result = sep(input, start)
  if start + result < input.len and input[start + result] == '-':
    minusVal = 1 # bool
    result += 1

proc optName(input: string; nameVal: var string; start: int; n: int): int =
  result = sep(input, start)
  result += parseutils.parseIdent(input, nameVal, start + result)

proc optFloat(input: string; floatVal: var float; start: int; n: int): int =
  result = sep(input, start)
  result += parseutils.parseFloat(input, floatVal, start + result)

###

# copy from the cdt module
proc distanceLinePointSqr(p1, p2, p: V2): (float, float, float, float, float) =
  let (x1, y1, x2, y2, x3, y3) = (p1[0], p1[1], p2[0], p2[1], p[0], p[1])
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

const
  PadNumberPos = 0 # TODO rename to Index
  PadNamePos = 1
  HoleNumberPos = 0
  HoleNamePos = 1
  PinNumberPos = 0
  PinNamePos = 1

type
  Element = ref object of RootRef
    style: Styles
    p: seq[V2]
    at: seq[Text] # attached text
    hover: bool
    selected: bool
    gx, gy: int # text grab
    #grabPos: array[9, tuple[x, y: float]] # we can reuse instead  p: seq[V2]
    isNew: bool

# type
  Text = ref object of Element
    text: string
    parent: Element # new, for easy reattaching, and maybe a graphical parent indication (arrow)
    detached: bool # maybe with new parent field this boolean is redundant. 
    sizeInPixel: bool

proc grabPos(e: Element; i: int): var V2 =
  e.p[i + 2]

template x1(e: Element): float = e.p[0][0]
template y1(e: Element): float = e.p[0][1]
template x2(e: Element): float = e.p[1][0]
template y2(e: Element): float = e.p[1][1]

#template `x1=`(e: Element; v: float) = e.p[0].x = v
#template `y1=`(e: Element; v: float) = e.p[0].y = v
#template `x2=`(e: Element; v: float) = e.p[1].x = v
#template `y2=`(e: Element; v: float) = e.p[1].y = v

type
  PathLike = ref object of Element

type
  Line = ref object of PathLike # Element

type
  Trace = ref object of PathLike # Element

type
  Rect = ref object of Element

type
  Circ = ref object of Element

type
  Pad = ref object of Element
    cornerRadius: float

type
  Path = ref object of PathLike # Element

type
  Pin = ref object of PathLike # Element

type
  Hole = ref object of Element
    drill: float
    dia: float
    #copper: float
    xext, yext: bool

type
  Group = ref object of Element
    lines: seq[Line]
    circs: seq[Circ]
    texts: seq[Text]
    rects: seq[Rect]
    pads: seq[Pad]
    holes: seq[Hole]
    paths: seq[Path]
    pins: seq[Pin]
    traces: seq[Trace]

type
  UserAction {.pure.} = enum
    none,
    lmbdv, # left mouse button pressed over void area
    lmbdo, # left mouse button pressed over object
    zooming,
    selecting,
    dragging,
    constructing

type
  Tree = rtree.RStarTree[8, 2, float, Element]
  TreeEl = rtree.L[2, float, Element]
  TreeBox = rtree.Box[2, float]

iterator filter(t: Tree; pred: proc(x: Element): bool {.closure.}): Element =
  for x in t.elements:
    if pred(x):
      yield x

type
  PDA = ref object of gtk4.Grid
    applicationWindow: ApplicationWindow
    textDataBuffer: TextBuffer
    textData: string
    entry: Entry
    commandEntry: Entry
    world: Entry
    gridw: Entry
    cbtStyle: ComboBoxText
    activeShape: Shapes
    activeStyle: Styles
    activeMode: Modes
    activeLineWidth: LineWidths
    activeFont: Fonts
    activeColor: Colors
    activeFillColor: Colors
    tree: Tree
    points: seq[V2]
    activeObj: Element
    movingObj: Element
    activeState: int
    hover, lastHover: Element
    majorGridColor: RGBA
    minorGridColor: RGBA
    activeGrid: V2
    activeG: int
    zoomNearMousepointer: bool
    selecting: bool
    uact: UserAction
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
    topbox2: gtk4.Box
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
    legEvXY: V2
    showPadNumbers: bool
    showPadNames: bool

macro addItFields(fields: openArray[string]; o: untyped): untyped =
  expectKind(o, nnkIteratorDef)
  let objName = o.params[1][0]
  for f in fields:
    let node =
      nnkStmtList.newTree(nnkForStmt.newTree(newIdentNode("el"),
          nnkDotExpr.newTree(newIdentNode($objName), newIdentNode($f)),
          nnkStmtList.newTree(nnkYieldStmt.newTree(newIdentNode("el")))))
    insert(body(o), body(o).len, node)
  result = o

iterator items(g: Group): Element {.addItFields(["lines", "rects", "circs"]).} =
  discard

proc move(el: Element; v: V2) 

proc moveAttachedText(el: Element; v: V2) =
  for t in filter(el.at, t => t != nil and not t.detached): # maybe padName, pinNumber and such can be nil? We will see.
    # move(t, v) # maybe applyIt(it + v) will do
    t.p.applyIt(it + v) # can attached text have again attached text?

proc move(el: Element; v: V2) =
  el.p.applyIt(it + v)
  moveAttachedText(el, v)

# constructors
proc newLine(p1, p2: V2): Line =
  Line(p: @[p1, p2])

proc newPath(p1, p2: V2): Path =
  Path(p: @[p1, p2])

proc newTrace(p1, p2: V2): Trace =
  Trace(p: @[p1, p2])

proc sortedPair(p1, p2: V2): tuple[a, b: V2] =
  (result[0][0], result[1][0]) = sortedTuple(p1[0], p2[0])
  (result[0][1], result[1][1]) = sortedTuple(p1[1], p2[1])

proc newRect(p1, p2: V2): Rect =
  let h = sortedPair(p1, p2)
  Rect(p: @[h[0], h[1]])

proc newText(p1, p2: V2; text: string): Text =
  result = Text(text: text)
  result.p = newSeq[V2](2 + 9)
  #result.style = Styles.hole # ?????????????????????
  result.p[0] = p1
  result.p[1] = p2

proc newPad(p1, p2: V2): Pad =
  let h = sortedPair(p1, p2)
  result = Pad(p: @[h[0], h[1]])
  result.style = Styles.pad
  result.at = @[Text(nil), Text(nil)] # number and name

proc newHole(p1, p2: V2): Hole =
  result = Hole(p: @[p1, p2])
  result.style = Styles.hole
  result.at = @[Text(nil), Text(nil)] # number and name

proc newCirc(p1, p2: V2): Circ =
  Circ(p: @[p1, p2])

# we do not yet support rotated text, so this proc may change later
proc putPinText(pin: Pin) =
  var x1, y1, x2, y2, d: float
  var gx, gy: int
  (x1, y1) =  pin.p[0]
  (x2, y2) =  pin.p[1]
  if y1 == y2: # horizontal, x1 is the "hot" end
    if x1 < x2:
      gx = 0
      d = 2
    else:
      gx = 2
      d = -2
    if not pin.at[PinNamePos].detached:
      pin.at[PinNamePos].p[0] = [x2 + d, y2]
      pin.at[PinNamePos].p[1] = [x2 + d, y2]
      pin.at[PinNamePos].gx = gx
      pin.at[PinNamePos].gy = 1
    if not pin.at[PinNumberPos].detached:
      pin.at[PinNumberPos].p[0] = [x2 - d, y2 - 1]
      pin.at[PinNumberPos].p[1] = [x2 - d, y2 - 1]
      pin.at[PinNumberPos].gx = (gx + 2) and 2
      pin.at[PinNumberPos].gy = 2
  if x1 == x2: # vertical
    if y1 < y2:
      gy = 0
      d = 2
    else:
      gy = 2
      d = -2
    if not pin.at[PinNamePos].detached:
      pin.at[PinNamePos].p[0] = [x2, y2 + d]
      pin.at[PinNamePos].p[1] = [x2, y2 + d]
      pin.at[PinNamePos].gx = 1
      pin.at[PinNamePos].gy = gy
    if not pin.at[PinNumberPos].detached:
      pin.at[PinNumberPos].p[0] = [x2 + 1, y2 - d]
      pin.at[PinNumberPos].p[1] = [x2 + 1, y2 - d]
      pin.at[PinNumberPos].gx = 0
      pin.at[PinNumberPos].gy = (gy + 2) and 2

proc newPin(p1, p2: V2): Pin =
  result = Pin(p: @[p1, p2], style: Styles.pin)
  assert PinNamePos == 1
  result.at.add(newText(p1, p2, "7?"))
  result.at.add(newText(p1, p2, "Name"))
  result.at[PinNamePos].sizeInPixel = true
  result.at[PinNumberPos].sizeInPixel = true
  result.at[PinNamePos].style = Styles.pin
  result.at[PinNumberPos].style = Styles.pin
  result.putPinText

# distances
proc sqrDistanceLineLike(l: Element; xy: V2): float =
  distanceLinePointSqr(l.p[0], l.p[1], xy)[1]

proc sqrDistanceRB(x1, y1, x2, y2: float; xy: V2): float = # distance to rectangle border
  [(x1, y1, x1, y2), (x1, y1, x2, y1), (x2, y2, x1, y2), (x2, y2, x2, y1)].mapIt(distanceLinePointSqr([it[0], it[1]], [it[2], it[3]], xy)[1]).min

proc sqrDistanceR(x1, y1, x2, y2: float; xy: V2): float =
  # if (xy[0] > x1 and xy[0] < x2) and (xy[1] > y1 and xy[1] < y2): # in rectangle
  if xy[0] in x1 .. x2 and xy[1] in y1 .. y2:
    return 0
  sqrDistanceRB(x1, y1, x2, y2, xy) # distance to boarder

proc sqrDistanceRectLike(r: Element; xy: V2): float =
  sqrDistanceR(r.x1, r.y1, r.x2, r.y2, xy)

proc sqrDistancePath(l: Path; xy: V2): float =
  result = float.high
  for l in l.p.xpairs:
    result = min(result, distanceLinePointSqr(l[0], l[1], xy)[1])

proc sqrDistanceCirc(c: Circ; xy: V2): float =
  max(math.hypot(c.x1 - xy[0], c.y1 - xy[1]) - math.hypot(c.x1 - c.x2, c.y1 - c.y2), 0) ^ 2

proc sqrDistanceHole(c: Hole; xy: V2): float =
  max(math.hypot(c.x1 - xy[0], c.y1 - xy[1]) - c.dia, 0) ^ 2

proc sqrDistanceText(t: Text; xy: V2): float =
  var (x, y) = (xy[0], xy[1])
  x += (t.p[1][0] - t.p[0][0]) * (t.gx mod 3).float * 0.5
  y += (t.p[1][1] - t.p[0][1]) * (t.gy mod 3).float * 0.5
  sqrDistanceR(t.x1, t.y1, t.x2, t.y2, [x, y]) # caution, this is not xy!

iterator allElements(tree: Tree; x: Element): Element =
  for el in tree.elements:
    yield el
  if x != nil:
    yield x

proc elAndText(tree: Tree): (Element, Text) =
  for el in tree.filter(el => el.selected):
    if el of Text:
      result[1] = Text(el)
    else:
      result[0] = el
    if result[0] != nil and result[1] != nil:
      return result

proc selectedText(tree: Tree): Text =
  for el in tree.filter(el => el of Text and el.selected):
    return Text(el)

proc selectedGroup(tree: Tree): Group =
  for el in tree.filter(el => el of Group and el.selected):
    return Group(el)

proc paint(pda: PDA; queueDraw = true)

### The gaction menu procs

proc toggleShowPadNumbers(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let newState = newVariantBoolean(not action.getState.getBoolean)
  action.changeState(newState)
  pda.showPadNumbers = not pda.showPadNumbers
  pda.paint

proc toggleShowPadNames(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let newState = newVariantBoolean(not action.getState.getBoolean)
  action.changeState(newState)
  pda.showPadNames = not pda.showPadNames
  pda.paint

### unused
proc submenuItem(action: gio.SimpleAction; parameter: glib.Variant; label: Label) =
  label.setlabel("Text set from submenu item")

proc radio(action: gio.SimpleAction; parameter: glib.Variant; label: Label) =
  var l: uint64
  let newState: glib.Variant = newVariantString(parameter.getString(l))
  action.changeState(parameter)
  let str: string = "From Radio menu item " & getString(newState, l)
  label.setLabel(str)

###

# grow the extend of the hair lines slower than ordinary graphics when zooming in 
proc smartScale(x: float): float = math.sqrt(x)

# convert abs distance x in mm into distance value for GtkDrawingArea
# when drawing with cairo and cairo_scale == 1
proc absToScr(pda: PDA; x: float; smartScale: bool = false): float =
  var scale {.global.}: float
  if scale == 0:
    let surface: gdk4.Surface = pda.applicationWindow.getSurface
    let display: gdk4.Display = surface.getDisplay
    let monitor: gdk4.Monitor = display.getMonitorAtSurface(surface)
    let geometry: gdk4.Rectangle = monitor.getGeometry
    scale = geometry.width.float / monitor.getWidthmm.float # inv. pixel size
  result = x * scale / pda.fullscale # * customDetailScale # compensate monitor distance, viewing angle
  if smartScale:
    result /= smartScale(pda.userZoom)

proc setLineWidthAbs(pda: PDA; w: float) =
  pda.cr.setLineWidth(pda.absToScr(w))

proc setHairLineWidth(pda: PDA) =
  pda.cr.setLineWidth(pda.absToScr(HairLineWidth))

proc setThinHairLineWidth(pda: PDA) =
  pda.cr.setLineWidth(pda.absToScr(ThinHairLineWidth))

proc drawGrabX(pda: PDA; x, y: float) =
  let d = pda.absToScr(math.sin(math.Pi * 0.25) * GrabDist, true)
  pda.cr.moveTo(x - d, y - d)
  pda.cr.lineTo(x + d, y + d)
  pda.cr.moveTo(x - d, y + d)
  pda.cr.lineTo(x + d, y - d)
  pda.cr.stroke

proc drawGrabCirc(pda: PDA; xy: V2) =
  pda.cr.newPath
  pda.cr.arc(xy[0], xy[1], pda.absToScr(GrabDist, true), 0, math.Tau)
  pda.drawGrabX(xy[0], xy[1])
  pda.cr.stroke

# event coordinates to user space
proc getUserCoordinates(pda: PDA; v: V2): V2 =
  [(v[0] - pda.hadjustment.upper * 0.5 + pda.hadjustment.value) / (pda.fullScale * pda.userZoom) + pda.dataX + pda.dataWidth * 0.5,
   (v[1] - pda.vadjustment.upper * 0.5 + pda.vadjustment.value) / (pda.fullScale * pda.userZoom) + pda.dataY + pda.dataHeight * 0.5]

proc roundToMultiple(x, m: float): float =
  ((x / m) + 0.5).floor * m # round(x / m) * m ?

proc roundToGrid(pda: PDA; v: V2): V2 =
  [roundToMultiple(v[0], pda.activeGrid[0]), roundToMultiple(v[1], pda.activeGrid[1])]

proc cairoDevRound(w: float): float =
  if w < 1.5:
    0.5
  else:
    floor((w + 0.5) mod 2) / 2 # if odd(round(w)): 0.5 else: 0

macro genGroupMove(g: static[string]; fields: varargs[untyped]): untyped =
  var s: string
  for f in fields:
    s.add("for el in " & g & "." & f.repr & ":\n")
    s.add("  move(el, dxdy)\n")
  result = parseStmt(s)

# we may use the items() iterator instead
proc move(g: Group; dxdy: V2) =
  move(Element(g), dxdy)
  genGroupMove("g", lines, rects, circs, pads, holes, pins, texts, traces, paths)

proc move(pda: PDA) =
  let (a, b) = (pda.lastButtonDownPosUser[0], pda.lastButtonDownPosUser[1])
  let dxdy = pda.roundToGrid(pda.getUserCoordinates(pda.lastMousePos) - pda.lastButtonDownPosUser)
  let (x1, y1, x2, y2) = (pda.movingObj.x1, pda.movingObj.y1, pda.movingObj.x2, pda.movingObj.y2)
  if pda.movingObj of Rect:
    let d = pda.absToScr(GrabDist)
    if a > x1 - d and a < x2 + d and b > y1 - d and b < y2 + d:
      if a > x1 + d and a < x2 - d and b > y1 + d and b < y2 - d:
        pda.movingObj.p[0] += dxdy
        pda.movingObj.p[1] += dxdy
      else:
        if a > x1 - d and a < x1 + d:
          pda.movingObj.x1 += dxdy[0]
        elif a > x2 - d and a < x2 + d:
          pda.movingObj.x2 += dxdy[0]
        if b > y1 - d and b < y1 + d:
          pda.movingObj.y1 += dxdy[1]
        elif b > y2 - d and b < y2 + d:
          pda.movingObj.y2 += dxdy[1]
  elif pda.movingObj of Group:
    Group(pda.movingObj).move(dxdy)
  elif pda.movingObj of Pad or pda.movingObj of Hole:
    move(pda.movingObj, dxdy)
  else: # Path, Line, Pin...
    let l = pda.movingObj
    let i = minIndexByIt(l.p, math.hypot(a - it[0], b - it[1]))
    let p = l.p[i]
    if (a - p[0]) ^ 2 + (b - p[1]) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
      l.p[i] += dxdy
    else:
      move(pda.movingObj, dxdy)
  pda.lastButtonDownPosUser += dxdy
  if pda.movingObj of Pin:
    putPinText(Pin(pda.movingObj))

# https://www.cairographics.org/FAQ/#sharp_lines
proc drawGrid(pda: PDA) =
  pda.cr.setOperator(Operator.over)
  pda.setThinHairLineWidth
  var w = getLineWidth(pda.cr)
  w = deviceToUserDistance(pda.cr, w, 0)[0]
  var rw = cairoDevRound(w) # the offset to rounded dev coordinates -- 0 or 0.5
  var h = getUserCoordinates(pda, [0.0, 0.0])
  var (x1, y1) = (h[0], h[1])
  h = getUserCoordinates(pda, [pda.darea.allocatedWidth.float, pda.darea.allocatedHeight.float]) # - 1 ?
  var (x2, y2) = (h[0], h[1])
  pda.cr.setSource(pda.minorGridColor)
  if pda.grid[1] * 1e3 > pda.grid[0]: # ignore tiny minor grid
    var x = x1.roundToMultiple(pda.grid[1]) # minor x
    while x < x2:
      if (x mod pda.grid[0]).abs > 0.1 * pda.grid[1]: # skip major grid positions
        var h = userToDevice(pda.cr, x, 0.0)[0].round + rw
        h = deviceToUser(pda.cr, h, 0.0)[0]
        pda.cr.moveTo(h, y1)
        pda.cr.lineTo(h, y2)
      x += pda.grid[1]
    pda.cr.stroke
  if pda.grid[3] * 1e3 > pda.grid[2]: # ignore tiny minor grid
    var y = y1.roundToMultiple(pda.grid[3]) # minor y
    while y < y2:
      if (y mod pda.grid[2]).abs > 0.1 * pda.grid[3]:
        var h = userToDevice(pda.cr, 0.0, y)[1].round + rw
        h = deviceToUser(pda.cr, 0.0, h)[1]
        pda.cr.moveTo(x1, h)
        pda.cr.lineTo(x2, h)
      y += pda.grid[3]
    pda.cr.stroke
  #
  pda.setHairLineWidth
  w = getLineWidth(pda.cr)
  w = deviceToUserDistance(pda.cr, w, 0)[0]
  rw = cairoDevRound(w) # the offset to rounded dev coordinates -- 0 or 0.5
  pda.cr.setSource(pda.majorGridColor)
  var x = x1.roundToMultiple(pda.grid[0]) # major x
  while x < x2:
    var h = userToDevice(pda.cr, x, 0.0)[0].round + rw
    h = deviceToUser(pda.cr, h, 0.0)[0]
    pda.cr.moveTo(h, y1)
    pda.cr.lineTo(h, y2)
    x += pda.grid[0]
  pda.cr.stroke
  var y = y1.roundToMultiple(pda.grid[2]) # major y
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

proc boxGrow(b: var TreeBox; c: TreeBox) =
  for i in 0 .. 1:
    if b[i].a > c[i].a:
      b[i].a = c[i].a
    if b[i].b < c[i].b:
      b[i].b = c[i].b

proc box(l: Element; pda: PDA): TreeBox =
  [sortedTuple(l.x1, l.x2), sortedTuple(l.y1, l.y2)]

proc boxCirc(c: Circ; pda: PDA): TreeBox =
  let r = math.hypot(c.x1 - c.x2, c.y1 - c.y2)
  [(c.x1 - r, c.x1 + r), (c.y1 - r, c.y1 + r)]

proc boxHole(c: Hole; pda: PDA): TreeBox =
  let r = c.dia * 0.5
  [(c.x1 - r, c.x1 + r), (c.y1 - r, c.y1 + r)]

proc boxText(t: Text; pda: PDA): TreeBox =
  let dx = -(t.p[1][0] - t.p[0][0]) * (t.gx mod 3).float * 0.5
  let dy = -(t.p[1][1] - t.p[0][1]) * (t.gy mod 3).float * 0.5
  [(t.x1 + dx, t.x2 + dx), (t.y1 + dy, t.y2 + dy)]

proc boxPath(l: Path; pda: PDA): TreeBox =
  var (xa, xb, ya, yb) = (l.p[0][0], l.p[0][0], l.p[0][1], l.p[0][1])
  for el in l.p:
    xa = min(xa, el[0])
    xb = max(xb, el[0])
    ya = min(ya, el[1])
    yb = max(yb, el[1])
  [(xa, xb), (ya, yb)]

proc boxEl(el: Element; pda: PDA): TreeBox =
  if el of Circ:
    result = boxCirc(Circ(el), pda)
  elif el of Hole:
    result = boxHole(Hole(el), pda)
  elif el of Text:
    result = boxText(Text(el), pda)
  elif el of Path:
    result = boxPath(Path(el), pda)
  else: #if el of Line or el of Pin or el of Trace or el of Rect or el of Group or el of Pad:
    result = box(el, pda)

proc editText(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let t = selectedText(pda.tree)
  if t != nil:
    var el: TreeEl = (boxEl(t, pda), t)
    assert pda.tree.delete(el)
    pda.entry.setText(t.text)
    pda.movingObj = t
  discard pda.entry.grabFocus

# attach "free" text, or attach detached text again
proc attachText(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let (l, t) = pda.tree.elAndText
  if l == nil:
    return
  # re-attach one only
  if t != nil and t.detached and t notin l.at:
    echo "text belongs to different object"
    return
  if l != nil and t != nil and t.detached and t in l.at:
    t.detached = false
    var el: TreeEl = (boxEl(t, pda), t)
    pda.tree.delete(el)
    return
  # try re-attach all
  if l != nil and t == nil:
    var succ: bool
    for t in l.at:
      if t.detached:
        succ = true
        t.detached = false
        var el: TreeEl = (boxEl(t, pda), t)
        pda.tree.delete(el)
    if not succ:
      echo "no detached text found"
  # we can always add new "free" text attributes 
  if l != nil and t != nil and not t.detached:
    t.detached = false
    l.at.add(t)
    var el: TreeEl = (boxEl(t, pda), t)
    pda.tree.delete(el)

proc detachText(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  var collector: seq[Element]
  for el in pda.tree.elements:
    if el.selected:
      collector.add(el)
  for el in collector:
    for text in el.at:
      if text.text == "":
        text.text  = "_?_"
      var t: TreeEl = (boxEl(text, pda), text)
      text.detached = true
      pda.tree.insert(t)

proc fileChooserSaveResponseCb(d: FileChooserDialog; id: int; str: string) =
  if ResponseType(id) == ResponseType.accept:
    var f: File = open(d.file.getPath, fmWrite)
    f.writeLine(str)
    f.close
  d.destroy

proc saveGroup(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let g = pda.tree.selectedGroup()
  if g != nil:
    let str = pretty(%* g)
    let dialog = newFileChooserDialog("Open File", pda.applicationWindow, FileChooserAction.save)
    discard dialog.addButton("Save", ResponseType.accept.ord)
    discard dialog.addButton("Cancel", ResponseType.cancel.ord)
    dialog.connect("response", fileChooserSaveResponseCb, str)
    dialog.show
 
proc draw(pda: PDA)

proc paint(pda: PDA; queueDraw = true) =
  pda.cr.save
  pda.cr.translate(pda.hadjustment.upper * 0.5 - pda.hadjustment.value, # our origin is the center
    pda.vadjustment.upper * 0.5 - pda.vadjustment.value)
  pda.cr.scale(pda.fullScale * pda.userZoom, pda.fullScale * pda.userZoom)
  pda.cr.translate(-pda.dataX - pda.dataWidth * 0.5, -pda.dataY - pda.dataHeight * 0.5)
  draw(pda)
  pda.cr.restore
  if queueDraw:
    pda.darea.queueDraw

proc fileChooserLoadResponseCb(d: FileChooserDialog; id: int; pda: PDA) =
  if ResponseType(id) == ResponseType.accept:
    let str = readFile(d.file.getPath)
    let g = to(parseJson(str), Group)
    let cx = pda.dataX + pda.dataWidth * 0.5
    let cy = pda.dataY + pda.dataHeight * 0.5
    var n = (cx - g.p[0][0]) / pda.grid[0]
    let dx = roundToMultiple(n.int.float * pda.grid[0], pda.grid[0])
    n = (cy - g.p[0][1]) / pda.grid[2]
    let dy = roundToMultiple(n.int.float * pda.grid[2], pda.grid[2])
    g.move([dx, dy])
    var  box: TreeBox = [(g.p[0][0], g.p[1][0]), (g.p[0][1], g.p[1][1])]
    var gb: TreeEl = (box, g)
    pda.tree.insert(gb)
    pda.paint
  d.destroy

proc loadGroup(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let dialog = newFileChooserDialog("Load Group", pda.applicationWindow, FileChooserAction.open)
  discard dialog.addButton("Load", ResponseType.accept.ord)
  discard dialog.addButton("Cancel", ResponseType.cancel.ord)
  dialog.connect("response", fileChooserLoadResponseCb, pda)
  dialog.show

proc breakUpGroup(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  var g: Group
  for el in pda.tree.filter(el => el.selected and el of Group):
    g = Group(el)
  if g == nil: return
  var box: TreeBox
  var gb: TreeEl
  for el in items(g):
    box = boxEl(el, pda)
    gb = (box, el)
    pda.tree.insert(gb)
  gb = (boxEl(g, pda), g)
  discard pda.tree.delete(gb)
  pda.paint # not necessary?

proc groupSelection(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  var collector: seq[Element]
  for el in pda.tree.filter(el => el.selected):
    collector.add(el)
  var box: TreeBox = boxEl(collector[0], pda)
  for el in collector:
    box.boxGrow(boxEl(el, pda))
    var eb: TreeEl = (boxEl(el, pda), el)
    discard pda.tree.delete(eb)
  var g = Group(p: @[[box[0].a, box[1].a], [box[0].b, box[1].b]])
  for el in collector:
    if el of Line:
      g.lines.add(Line(el))
    elif el of Circ:
      g.circs.add(Circ(el))
    elif el of Hole:
      g.holes.add(Hole(el))
    elif el of Pad:
      g.pads.add(Pad(el))
    elif el of Pin:
      g.pins.add(Pin(el))
    elif el of Rect:
      g.rects.add(Rect(el))
    elif el of Text:
      g.texts.add(Text(el))
    elif el of Path:
      g.paths.add(Path(el))
    elif el of Trace:
      g.traces.add(Trace(el))
  var gb: TreeEl = (box, g)
  pda.tree.insert(gb)

proc drawPath(l: Path; pda: PDA) =
  pda.cr.newPath
  for p in l.p:
    pda.cr.lineTo(p[0], p[1])

proc drawTrace(l: Trace; pda: PDA) =
  pda.cr.moveTo(l.x1, l.y1)
  pda.cr.lineTo(l.x2, l.y2)

proc drawRect(r: Rect; pda: PDA) =
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)

proc drawText(t: Text; pda: PDA; size: float = 0) =
  if t == nil:
    return
  const Font = "Serif 8px" # later we take that from style
  var context = pda.darea.createPangoContext
  var layout = pango.newLayout(context)
  var desc = pango.newFontDescription(Font)
  var ts = styles[t.style.ord].textSize
  if size != 0:
    ts = size
  if t.sizeInPixel:
    desc.setAbsoluteSize((pango.SCALE.float * ts))
  else:
    desc.setSize((pango.SCALE.float * ts / pda.fullScale).int) # works, text size does not change! Size in points.
  #pda.cr.moveTo(t.x1, t.y1)
  layout.setText(t.text)
  layout.setFontDescription(desc)
  var w, h: int
  layout.getSize(w, h)
  let width = w.float / pango.Scale.float
  let height = h.float / pango.Scale.float
  if (height) * pda.userZoom < pda.absToScr(5): return
  t.p[1] = t.p[0] + [width, height]
  let dx = -width * (t.gx mod 3).float * 0.5
  let dy = -height * (t.gy mod 3).float * 0.5
  pda.cr.moveTo(t.x1 + dx, t.y1 + dy)
  pda.cr.updateLayout(layout)
  pangocairo.showLayout(pda.cr, layout)
  if t.isNew:
    if t.text.len > 0:
      var el: TreeEl = (boxEl(t, pda), t)
      pda.tree.insert(el)
    t.isNew = false
    pda.movingObj = nil
  for i in 0 .. 8:
    let x = t.x1 + width * (i mod 3).float * 0.5
    let y = t.y1 + height * (i div 3).float * 0.5
    t.grabPos(i) = [x + dx, y + dy]

proc drawLine(l: Line; pda: PDA) =
  pda.cr.moveTo(l.x1, l.y1)
  pda.cr.lineTo(l.x2, l.y2)
  for el in l.at:
    el.drawText(pda)

proc drawPad(r: Pad; pda: PDA) =
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)
  pda.cr.setLineWidth(0)
  pda.cr.fill
  pda.cr.setSource(styles[r.style.ord].xcolor)
  # pda.cr.setSource(styles[Styles.pad.ord].xcolor) # maybe we should use a fixed style?
  let ts = min(r.x2 - r.x1, r.y2 - r.y1)
  if pda.showPadNumbers and pda.showPadNames:
    if r.at[PadNumberPos] != nil and r.at[PadNamePos] != nil:
      r.at[PadNumberPos].gx = 2
      r.at[PadNumberPos].gy = 1
      r.at[PadNamePos].gx = 0
      r.at[PadNamePos].gy = 1
      #let ts = min(r.x2 - r.x1, r.y2 - r.y1)
      drawText(r.at[PadNumberPos], pda, ts)
      drawText(r.at[PadNamePos], pda, ts)
  elif pda.showPadNumbers or pda.showPadNames:
    let i = pda.showPadNames.int
    if r.at[i] != nil: 
      r.at[i].gx = 1
      r.at[i].gy = 1
      drawText(r.at[i], pda, ts)

proc drawPin(l: Pin; pda: PDA) =
  var h = math.hypot(l.x2 - l.x1, l.y2 - l.y1)
  if h == 0: # to fix
    h = 1
  let x = l.x1 + (l.x2 - l.x1) / h * PinHotEnd
  let y = l.y1 + (l.y2 - l.y1) / h * PinHotEnd
  pda.cr.moveTo(l.x2, l.y2)
  pda.cr.lineTo(x, y)
  pda.cr.stroke
  pda.cr.moveTo(x, y)
  pda.cr.setSource(styles[l.style.ord].xcolor)
  pda.cr.lineTo(l.x1, l.y1)
  pda.cr.stroke
  pda.cr.setSource(XColorValues[XColors.pinName.ord]) # use XColor, as style color is needed for pin itself
  drawText(l.at[PinNamePos], pda)
  pda.cr.setSource(XColorValues[XColors.pinNumber.ord])
  drawText(l.at[PinNumberPos], pda)

proc drawCirc(c: Circ; pda: PDA) =
  let r = math.hypot(c.x1 - c.x2, c.y1 - c.y2)
  pda.cr.newPath
  pda.cr.arc(c.x1, c.y1, r, 0, math.Tau)

proc drawHole(r: Hole; pda: PDA) =
  if r.x1 == r.x2 and r.y1 == r.y2: # round holes
    pda.cr.arc(r.x1, r.y1, r.dia * 0.5, 0, math.Tau)
    pda.cr.fill
    pda.cr.setSource(styles[r.style.ord].xcolor)
    pda.cr.arc(r.x1, r.y1, r.drill * 0.5, 0, math.Tau)
    pda.cr.fill
  else: # the ( O ) shapes for DIP packages
    pda.cr.setLineWidth(r.dia)
    pda.cr.moveTo(r.x1, r.y1)
    pda.cr.lineTo(r.x2, r.y2)
    pda.cr.stroke
    pda.cr.setSource(styles[r.style.ord].xcolor)
    pda.cr.arc((r.x1 + r.x2) * 0.5, (r.y1 + r.y2) * 0.5, r.drill * 0.5, 0, math.Tau)
    pda.cr.fill
  pda.cr.setSource(styles[r.style.ord].xcolor)
  if pda.showPadNumbers and pda.showPadNames:
    if r.at[PadNumberPos] != nil and r.at[PadNamePos] != nil:
      r.at[PadNumberPos].gx = 2
      r.at[PadNumberPos].gy = 1
      r.at[PadNamePos].gx = 0
      r.at[PadNamePos].gy = 1
      drawText(r.at[PadNumberPos], pda, r.dia)
      drawText(r.at[PadNamePos], pda, r.dia)
  elif pda.showPadNumbers or pda.showPadNames:
    let i = pda.showPadNames.int
    if r.at[i] != nil: 
      r.at[i].gx = 1
      r.at[i].gy = 1
      drawText(r.at[i], pda, r.dia)

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
  for l in g.texts:
    pda.cr.setSource(styles[l.style.ord].color)
    drawText(l, pda)
    #pda.cr.stroke
  for l in g.rects:
    pda.setLineWidthAbs(styles[l.style.ord].lineWidth)
    pda.cr.setSource(styles[l.style.ord].color)
    drawRect(l, pda)
    pda.cr.stroke
  for l in g.paths:
    pda.setLineWidthAbs(styles[l.style.ord].lineWidth)
    pda.cr.setSource(styles[l.style.ord].color)
    drawPath(l, pda)
    pda.cr.stroke
  for l in g.pins: # note: all pins should have the same style?
    pda.setLineWidthAbs(styles[l.style.ord].lineWidth)
    pda.cr.setSource(styles[l.style.ord].color)
    drawPin(l, pda)
    pda.cr.stroke
  for l in g.pads: # all same style?
    pda.setLineWidthAbs(styles[l.style.ord].lineWidth)
    pda.cr.setSource(styles[l.style.ord].color)
    drawPad(l, pda)
    pda.cr.stroke
  for l in g.traces:
    pda.setLineWidthAbs(styles[l.style.ord].lineWidth)
    pda.cr.setSource(styles[l.style.ord].color)
    drawTrace(l, pda)
    pda.cr.stroke

proc initDrawGrab(pda: PDA) =
  pda.cr.setSource(XColorValues[XColors.grab.ord])
  pda.setHairLineWidth

proc drawTextGrab(t: Text; pda: PDA) =
  initDrawGrab(pda)
  let width = t.p[1][0] - t.p[0][0]
  let height = t.p[1][1] - t.p[0][1]
  let dx = -width * (t.gx mod 3).float * 0.5
  let dy = -height * (t.gy mod 3).float * 0.5
  pda.cr.rectangle(t.x1 + dx, t.y1 + dy, width, height)
  pda.cr.stroke
  for i in 0 .. 8:
    pda.drawGrabCirc(t.grabPos(i))

proc drawPathGrab(l: PathLike; pda: PDA) =
  initDrawGrab(pda)
  for p in l.p.pairwise:
    var a: V2 = p[0]
    var b: V2 = p[1]
    let h = math.hypot(b[0] - a[0], b[1] - a[1])
    let dx = pda.absToScr((b[1] - a[1]) / h * GrabDist, true)
    let dy = pda.absToScr(-(b[0] - a[0]) / h * GrabDist, true)
    pda.cr.moveTo(a[0] + dx, a[1] + dy)
    pda.cr.lineTo(b[0] + dx, b[1] + dy)
    pda.cr.moveTo(a[0] - dx, a[1] - dy)
    pda.cr.lineTo(b[0] - dx, b[1] - dy)
  pda.cr.stroke
  for p in l.p:
    pda.drawGrabCirc(p)

proc drawCircGrab(c: Circ; pda: PDA) =
  initDrawGrab(pda)
  let d = pda.absToScr(GrabDist)
  let r = math.hypot(c.x1 - c.x2, c.y1 - c.y2)
  for i in 0 .. 1:
    pda.cr.newPath
    pda.cr.arc(c.x1, c.y1, r + d * (i * 2 - 1).float, 0, math.Tau)
    pda.cr.stroke
    pda.drawGrabCirc(c.p[i])

proc drawPadGrab(r: Pad; pda: PDA) =
  discard

proc drawHoleGrab(r: Hole; pda: PDA) =
  discard

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
  pda.cr.setSource(0, 0, 1, 0.1) # fix later
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)
  pda.cr.fill

proc sqrDistance(el: Element; xy: V2): float =
  if el of Line or el of Pin or el of Trace:
    sqrDistanceLineLike(el, xy)
  elif el of Path:
    sqrDistancePath(Path(el), xy)
  elif el of Rect or el of Pad or el of Group:
    sqrDistanceRectLike(el, xy)
  elif el of Hole:
    sqrDistanceHole(Hole(el), xy)
  elif el of Circ:
    sqrDistanceCirc(Circ(el), xy)
  elif el of Text:
    sqrDistanceText(Text(el), xy)
  else:
    assert false
    0 # discard

# squared distance from query point to
proc dist(qo: BoxCenter[2, float]; el: TreeEl): float =
  sqrDistance(el.l, [qo[0], qo[1]])

proc drawEl(el: RootRef; pda: PDA) =
  if el of Line:
    drawLine(Line(el), pda)
  elif el of Pin:
    drawPin(Pin(el), pda)
  elif el of Path:
    drawPath(Path(el), pda)
  elif el of Trace:
    pda.cr.setLineCap(LineCap.round)
    drawTrace(Trace(el), pda)
  elif el of Rect:
    drawRect(Rect(el), pda)
  elif el of Pad:
    drawPad(Pad(el), pda)
  elif el of Hole:
    pda.cr.setLineCap(LineCap.round)
    drawHole(Hole(el), pda)
  elif el of Circ:
    drawCirc(Circ(el), pda)
  elif el of Text:
    drawText(Text(el), pda)
  elif el of Group:
    drawGroup(Group(el), pda)

proc drawElGrab(el: Element; pda: PDA) =
  #if true: return
  if el of Line or el of Pin or el of Path or el of Trace:
    if not (el of Trace and styles[el.style.ord].lineWidth < 0.8 * GrabDist):
      drawPathGrab(PathLike(el), pda)
  elif el of Hole:
    drawHoleGrab(Hole(el), pda)
  elif el of Rect:
    drawRectGrab(Rect(el), pda)
  elif el of Pad:
    drawPadGrab(Pad(el), pda)
  elif el of Circ:
    drawCircGrab(Circ(el), pda)
  elif el of Text:
    drawTextGrab(Text(el), pda)
  elif el of Group:
    drawGroupGrab(Group(el), pda)

# We draw the elements with 4 different states -- plain, selected, hover and hoverSelected.
# 1. Draw plain elements, blit its shadow and blit the drawing
# 2. Draw all remaining elements with shadow extend and blit the shadow
# 3. Draw all the non plain elements and blit the drawing with brighter color
proc draw(pda: PDA) =
  pda.cr.setSource(XColorValues[XColors.background.ord])
  pda.cr.paint
  pda.drawGrid
  pda.cr.setOperator(Operator.over)
  for selected in [false, true]: # try all
    for hov in [false, true]: # four different states
      pda.cr.pushGroup
      for l in pda.tree.allElements(pda.movingObj):
        if l.selected == selected and hov == (l == pda.hover): # if loop state is state of el
          pda.cr.setSource(styles[l.style.ord].color) # for text, set color before calling the draw procs
          if styles[l.style.ord].relSize:
            pda.cr.setLineWidth(styles[l.style.ord].lineWidth * (1.0 + 0.3 * (selected.int + (l == pda.hover).int).float) + (1.0 * (selected.int + (l == pda.hover).int).float))
          else:
            pda.setLineWidthAbs(styles[l.style.ord].lineWidth * (1.0 + 0.3 * (selected.int + (l == pda.hover).int).float) +  (1.0 * (selected.int + (l == pda.hover).int).float))
          drawEl(l, pda) # draw with lineWidth matching state
          pda.cr.stroke
      let tmp0 = pda.cr.popGroup
      let dd = pda.absToScr(0.2) # tiny offset
      pda.cr.translate(dd, dd)
      pda.cr.setSource(0, 0, 0, 0.7)
      pda.cr.mask(tmp0) # grey bottom shadow
      pda.cr.translate(-dd, -dd)
      if not selected and not hov: # the plain ones -- shadow size matches line width
        pda.cr.setSource(tmp0)
        pda.cr.paintWithAlpha(0.7)
        patternDestroy(tmp0)
      else:
        patternDestroy(tmp0)
        pda.cr.pushGroup
        for l in pda.tree.allElements(pda.movingObj): # the "highlighted" ones, for which shadow is larger than line width -- we have to draw them again
          if l.selected == selected and hov == (l == pda.hover): # if loop state is state of el
            pda.cr.setSource(styles[l.style.ord].color) # for text, set color before calling the draw procs
            if styles[l.style.ord].relSize:
              pda.cr.setLineWidth(styles[l.style.ord].lineWidth * (1.0 + 0.3 * (selected.int + (l == pda.hover).int).float))
            else:
              pda.setLineWidthAbs(styles[l.style.ord].lineWidth * (1.0 + 0.3 * (selected.int + (l == pda.hover).int).float))
            drawEl(l, pda)
            pda.cr.stroke
            if l == pda.hover: # draw the hover grab markers
              drawElGrab(l, pda)
        let tmp1 = pda.cr.popGroup
        pda.cr.setSource(1, 1, 1, 0.3) # lighter than plain objects
        pda.cr.mask(tmp1)
        pda.cr.setSource(tmp1)
        pda.cr.paintWithAlpha(0.7)
        pda.cr.paintWithAlpha(1.0) #0.7)
        patternDestroy(tmp1)

proc drawingAreaDrawCb(darea: DrawingArea; cr: cairo.Context; width, height: int; pda: PDA) =
  if pda.pattern.isNil: return
  ### var t0 = cpuTime()
  cr.setSource(pda.pattern)
  cr.paint
  #echo "CPU time [s] ", cpuTime() - t0
  if pda.selecting:
    cr.rectangle(pda.lastButtonDownPos[0], pda.lastButtonDownPos[1], pda.zoomRect[0] - pda.lastButtonDownPos[0], pda.zoomRect[1] -
        pda.lastButtonDownPos[1])
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

proc updateAdjustments(pda: PDA; dx, dy: float) =
  pda.hadjustment.setUpper(pda.darea.allocatedWidth.float * pda.userZoom)
  pda.vadjustment.setUpper(pda.darea.allocatedHeight.float * pda.userZoom)
  pda.hadjustment.setPageSize(pda.darea.allocatedWidth.float)
  pda.vadjustment.setPageSize(pda.darea.allocatedHeight.float)
  updateVal(pda.hadjustment, dx)
  updateVal(pda.vadjustment, dy)

proc dareaConfigureCallback(darea: DrawingArea; width, height: int; pda: PDA) =
  pda.fullScale = min(pda.darea.allocatedWidth.float / pda.dataWidth, pda.darea.allocatedHeight.float / pda.dataHeight)
  #if pda.surf != nil:
  #  destroy(pda.surf) # manually destroy surface -- GC would do it for us, but GC is slow...
  let s = darea.getNative.getSurface
  pda.surf = createSimilarSurface(s, Content.color, pda.darea.allocatedWidth, pda.darea.allocatedHeight)
  #if pda.pattern != nil:
  #  patternDestroy(pda.pattern)
  #if pda.cr != nil:
  #  destroy(pda.cr)
  pda.pattern = patternCreateForSurface(pda.surf) # pattern now owns the surface!
  pda.cr = newContext(pda.surf) # pda function references target!
  updateAdjustments(pda, 0, 0)
  pda.paint(false)

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

proc updateAdjustmentsAndPaint(pda: PDA; dx, dy: float) =
  pda.updateAdjustments(dx, dy)
  pda.paint

proc onMotion(c: EventControllerLegacy; e: Event; pda: PDA): bool =
  let x = pda.legEvXY[0]
  let y = pda.legEvXY[1]
  let h = pda.getUserCoordinates(pda.legEvXY)
  let (a, b) = (h[0], h[1])
  var el: Element = pda.tree.findNearest(BoxCenter[2, float]([a, b]), dist)[1]
  if el != nil:
    if sqrDistance(el, [a, b]) < (pda.absToScr(GrabDist)) ^ 2:
      pda.hover = el
      el.hover = true
    else:
      pda.hover = nil
  if pda.uact == dragging and pda.movingObj != nil:
    pda.move
    paint(pda)
  elif math.hypot(x - pda.lastButtonDownPos[0], y - pda.lastButtonDownPos[1]) > 2:
    if pda.uact == lmbdv:
      pda.uact = zooming
    elif pda.uact == lmbdo:
      pda.uact = dragging #selecting
      pda.movingObj = pda.hover
      assert pda.movingObj != nil
      var l = pda.movingObj
      var el: TreeEl = (boxEl(l, pda), l)
      pda.tree.delete(el)
  elif pda.uact == selecting: #state.contains(button1): # selecting
    pda.selecting = true
    pda.zoomRect = [x, y]
    pda.darea.queueDraw #Area(0, 0, pda.darea.allocatedWidth, pda.darea.allocatedHeight)
  elif false: #button2 in state: # panning
    pda.updateAdjustmentsAndPaint(pda.lastMousePos[0] - x, pda.lastMousePos[1] - y)
  if pda.points.len > 0 or pda.hover != pda.lastHover:
    if pda.points.len == 1:
      let p = pda.roundToGrid([a, b])
      if pda.movingObj of Path:
        pda.movingObj.p[^1] = p
      else:
        pda.movingObj.p[1] = p
        if pda.movingObj of Pin:
          let n = Pin(pda.movingObj).at[PinNamePos]
          Pin(pda.movingObj).putPinText
    paint(pda)
    pda.lastHover = pda.hover
  pda.lastMousePos = pda.legEvXY
  return gdk4.EVENT_STOP

# zooming with mouse wheel -- data near mouse pointer should not move if possible!
# hadjustment.value + event.x is the position in our zoomed_in world, (userZoom / z0 - 1)
# is the relative movement caused by zooming
# In other words, this is the delta-move d of a point at position P from zooming:
# d = newPos - P = P * scale - P = P * (z/z0) - P = P * (z/z0 - 1). We have to compensate for this d.

proc scrollEvent(c: EventControllerLegacy; event: ScrollEvent; pda: PDA): bool =
  assert event.getEventType == EventType.scroll
  let z0 = pda.userZoom
  case getDirection(event)
  of ScrollDirection.up:
    pda.userZoom *= ZoomFactorMouseWheel
  of ScrollDirection.down:
    pda.userZoom /= ZoomFactorMouseWheel
    if pda.userZoom < 1:
      pda.userZoom = 1
  else:
    return gdk4.EVENT_PROPAGATE
  if pda.zoomNearMousepointer:
    let x = pda.legEvXY[0]
    let y = pda.legEvXY[1]
    pda.updateAdjustmentsAndPaint((pda.hadjustment.value + x) * (pda.userZoom / z0 - 1),
      (pda.vadjustment.value + y) * (pda.userZoom / z0 - 1))
  else: # zoom to center
    pda.updateAdjustmentsAndPaint((pda.hadjustment.value +
        pda.darea.allocatedWidth.float * 0.5) * (pda.userZoom / z0 - 1),
        (pda.vadjustment.value + pda.darea.allocatedHeight.float * 0.5) * (pda.userZoom / z0 - 1))
  return gdk4.EVENT_STOP

proc buttonPressEvent(c: EventControllerLegacy; e: Event; pda: PDA): bool =
  pda.lastMousePos = pda.legEvXY
  pda.lastButtonDownPos = pda.legEvXY
  (pda.lastButtonDownPosUser[0], pda.lastButtonDownPosUser[1]) = pda.getUserCoordinates(pda.legEvXY)
  if pda.uact == constructing:
    discard
  elif pda.hover.isNil:
    pda.uact = lmbdv
  else:
    pda.uact = lmbdo
  return gdk4.EVENT_STOP

# zoom into selected rectangle and center it
# math: we first center the selection rectangle, and then compensate for translation due to scale

proc buttonReleaseEvent(c: EventControllerLegacy; event: ButtonEvent; pda: PDA): bool =
  let x = pda.legEvXY[0]
  let y = pda.legEvXY[1]
  if pda.uact == UserAction.lmbdv and pda.hover == nil: # and pda.selected.lines.len > 0:
    var h = false
    for el in pda.tree.elements: #pda.movingObj):
      if el.selected: h = true
      el.selected = false
    if h:
      paint(pda)
      pda.uact = UserAction.none
      return
  if pda.uact == UserAction.lmbdo and pda.hover != nil:
    pda.movingObj = nil
    if pda.hover of Text:
      let width = pda.hover.p[1][0] - pda.hover.p[0][0]
      let height = pda.hover.p[1][1] - pda.hover.p[0][1]
      let olddx = -width * (pda.hover.gx mod 3).float * 0.5
      let olddy = -height * (pda.hover.gy mod 3).float * 0.5
      for i in 0 .. 8:
        let h = pda.getUserCoordinates([x, y])
        let (x, y) = (h[0], h[1])
        if (x - pda.hover.grabPos(i)[0]) ^ 2 + (y - pda.hover.grabPos(i)[1]) ^ 2 < pda.absToScr(GrabDist) ^ 2:
          var el: TreeEl = (boxEl(pda.hover, pda), pda.hover)
          discard pda.tree.delete(el)
          pda.hover.gx = i mod 3
          pda.hover.gy = i div 3
          var dx = -width * (pda.hover.gx mod 3).float * 0.5
          var dy = -height * (pda.hover.gy mod 3).float * 0.5
          var dxdy = pda.roundToGrid([olddx - dx, olddy - dy])
          pda.hover.p[0] += dxdy
          pda.hover.p[1] += dxdy
          pda.movingObj = pda.hover
          pda.hover.isNew = true
          paint(pda)
          break
    var ret = false
    for l in pda.tree.elements:
      if l == pda.hover:
        if not l.selected: ret = true
        l.selected = true
    if ret:
      pda.uact = UserAction.none
      return
  if pda.movingObj != nil and pda.uact == dragging:
    var l = pda.movingObj
    pda.movingObj = nil
    pda.points.setLen(0)
    var el: TreeEl = (boxEl(l, pda), l)
    pda.tree.insert(el)
    pda.uact = UserAction.none
  let uc = pda.getUserCoordinates(pda.legEvXY)
  let ucr = pda.roundToGrid(uc)
  if pda.uact == dragging:
    pda.uact = UserAction.none
  if pda.uact in {lmbdo, lmbdv, constructing}:
    pda.points.add(ucr)
  var needsRefresh = false
  if pda.points.len == 1:
    var l: Element
    if pda.activeShape == Shapes.line:
      l = newLine(pda.points[0], pda.points[0])
    elif pda.activeShape == Shapes.pin:
      l = newPin(pda.points[0], pda.points[0])
    elif pda.activeShape == Shapes.path:
      l = newPath(pda.points[0], pda.points[0])
    elif pda.activeShape == Shapes.trace:
      l = newTrace(pda.points[0], pda.points[0])
    elif pda.activeShape == Shapes.rect:
      l = newRect(pda.points[0], pda.points[0])
    elif pda.activeShape == Shapes.pad:
      l = newPad(pda.points[0], pda.points[0])
    elif pda.activeShape == Shapes.circ:
      l = newCirc(pda.points[0], pda.points[0])
    elif pda.activeShape == Shapes.hole:
      l = newHole(pda.points[0], pda.points[0])
      pda.points.add([0.0, 0])
      Hole(l).dia = HoleDia
      Hole(l).drill = HoleDrill
    elif pda.activeShape == Shapes.text:
      l = newText(pda.points[0], pda.points[0], "|")
      pda.entry.setText("")
      pda.entry.setPlaceholderText("New Text")
      discard pda.entry.grabFocus
      pda.points.setLen(0)
      needsRefresh = true
    elif pda.activeShape == Shapes.attr:
      l = newText(pda.points[0], pda.points[0], "|")
      pda.entry.setText("")
      pda.entry.setPlaceholderText("New Text")
      discard pda.entry.grabFocus
      pda.points.setLen(0)
      needsRefresh = true
    if not (l of Pin or l of Hole or l of Pad):
      l.style = Styles(pda.cbtStyle.getActive)
    pda.movingObj = l
    if pda.points.len == 1:
      pda.uact = constructing
  if pda.points.len == 2:
    let l = pda.movingObj
    if l of Path:
      if pda.points[0] == pda.points[1]:
        l.p.setLen(l.p.len - 1)
        pda.movingObj = nil
        var el: TreeEl = (boxEl(l, pda), l)
        pda.tree.insert(el)
        pda.points.setLen(0)
        pda.uact = UserAction.none
      else:
        l.p.add(pda.points[0])
        pda.points[0] = pda.points[1]
        pda.points.setLen(1)
        pda.uact = constructing
    else:
      pda.movingObj = nil
      var el: TreeEl = (boxEl(l, pda), l)
      pda.tree.insert(el)
      pda.points.setLen(0)
      pda.uact = UserAction.none
    if l of Pad or l of Hole:
      let (x1, y1, x2, y2) = (l.p[0][0], l.p[0][1], l.p[1][0], l.p[1][1])
      l.at[PadNamePos] = newText([(x1 + x2) * 0.5, (y1 + y2) * 0.5], [x2, y2], "Name")
      l.at[PadNamePos].sizeInPixel = true
      l.at[PadNumberPos] = newText([(x1 + x2) * 0.5, (y1 + y2) * 0.5], [x2, y2], "Num")
      l.at[PadNumberPos].sizeInPixel = true
  if needsRefresh:
    paint(pda)
  return gdk4.EVENT_PROPAGATE

proc distributeLegacyEvent(c: EventControllerLegacy; e: Event; pda: PDA): bool =
  let et = e.getEventType
  case et
  of EventType.buttonPress, buttonRelease, motionNotify:
    var nx, ny: float
    let widget = pda.darea
    var (x, y) = e.getPosition
    var native: gtk4.Native = widget.getNative
    native.getSurfaceTransform(nx, ny)
    let toplevel = widget.getRootWidget
    discard translateCoordinates(toplevel, widget, x - nx, y - ny, x, y) # TODO add getRootWindow()
    pda.legEvXY = [x, y]
  else: discard
  case et
  of EventType.buttonPress:
    return buttonPressEvent(c, e, pda)
  of EventType.buttonRelease:
    return buttonReleaseEvent(c, cast[ButtonEvent](e), pda)
    #return buttonReleaseEvent(c, ButtonEvent(e), pda) # runtime issue
  of EventType.scroll:
    return scrollEvent(c, cast[ScrollEvent](e), pda)
  of EventType.motionNotify:
    return onMotion(c, e, pda)
  else:
    discard

proc entryNotify(entry: Entry; paramSpec: ParamSpec; pda: PDA) =
  if pda.movingObj of Text:
    Text(pda.movingObj).text = entry.text
    let c = entry.getPosition
    #Text(pda.movingObj).text.insert("|", c)
    pda.paint

# Caution: remember that (x == NaN) is alway false, so we do the test with x != x
# This works currently for pads only -- later we will be able to create other objects as well
proc padCommand(input: string; pda: PDA) =
  var x1, y1, x2, y2, r, dx, dy: float
  var n, px2, py2, mnum, num: int
  var id, name: string
  (x1, y1, x2, y2, r, num, name, dx, dy, n) = (NaN, NaN, NaN, NaN, 0.0, 0, "", NaN, NaN, 1) # defaults
  var res: bool
  # using the plus matcher, so the '+' is optional
  res = scanf(input, "$[skipName]$[sep]$f$[sep]$f${plus(0)}$f${plus(0)}$f${optFloat(0)}${minus(0)}$i${optName(0)}$[sep]$f$[sep]$f$[sep]$i", x1, y1, px2, x2, py2, y2, r, mnum, num, name, dx, dy, n)
  if y2 != y2:
    return
  x2 += x1 * px2.float
  y2 += y1 * py2.float
  for i in 1 .. n:
    let pad = newPad([x1, y1], [x2, y2])
    pad.at[PadNamePos] = newText([(x1 + x2) * 0.5, (y1 + y2) * 0.5], [x2, y2], name)
    pad.at[PadNumberPos] = newText([(x1 + x2) * 0.5, (y1 + y2) * 0.5], [x2, y2], $num)
    pad.at[PadNamePos].sizeInPixel = true
    pad.at[PadNumberPos].sizeInPixel = true
    var el: TreeEl = (boxEl(pad, pda), pad)
    pda.tree.insert(el)
    if dy != dy:
      break
    num += 1 - mnum * 2
    x1 += dx
    y1 += dy
    x2 += dx
    y2 += dy
  pda.paint

proc holeCommand(input: string; pda: PDA) =
  var x, y, dia, drill, dx, dy: float
  var n, mnum, num, px, py: int
  var name: string
  (x, y, dia, drill, num, name, dx, dy, n) = (NaN, NaN, NaN, 0.0, 0, "Name", NaN, NaN, 1) # defaults: x y dia drill  id name dx dy n
  var res: bool
  # using the plus matcher, so the '+' is optional
  echo input
  # we have a problem currently: plus() needs at least one character to process, so input has to start with "hole ", " " or "+".
  res = scanf(input, "$[skipName]${plus(0)}$f${plus(0)}$f$[sep]$f$[sep]$f${minus(0)}$i${optName(0)}$[sep]$f$[sep]$f$[sep]$i", px, x, py, y, dia, drill, mnum, num, name, dx, dy, n)
  echo res
  jecho px, x, py, y, dia, drill, mnum, num, name, dx, dy, n
  if dia != dia:
    return
  let ddx = px.float * dia * 0.5
  let ddy = py.float * dia * 0.5
  for i in 1 .. n:
    let pad = newHole([x - ddx, y - ddy], [x + ddx, y + ddy])#, [x, y])
    pad.dia = dia
    pad.drill = drill
    pad.at[HoleNamePos] = newText([x, y], [x, y], name)
    pad.at[HoleNumberPos] = newText([x, y], [x, y], $num)
    pad.at[HoleNamePos].sizeInPixel = true
    pad.at[HoleNumberPos].sizeInPixel = true
    var el: TreeEl = (boxEl(pad, pda), pad)
    pda.tree.insert(el)
    if dy != dy:
      break
    num += 1 - mnum * 2
    x += dx
    y += dy
  pda.paint

proc pinCommand(input: string; pda: PDA) =
  var x1, y1, x2, y2, dx, dy: float
  var n, px2, py2, mnum, num: int
  var name: string
  (x1, y1, x2, y2, num, name, dx, dy, n) = (NaN, NaN, NaN, NaN, 0, "", NaN, NaN, 1) # defaults
  var res: bool
  # using the plus matcher, so the '+' is optional
  res = scanf(input, "$[skipName]$[sep]$f$[sep]$f${plus(0)}$f${plus(0)}$f${minus(0)}$i${optName(0)}$[sep]$f$[sep]$f$[sep]$i", x1, y1, px2, x2, py2, y2, mnum, num, name, dx, dy, n)
  if y2 != y2:
    return
  x2 += x1 * px2.float
  y2 += y1 * py2.float
  var h = pda.textData.split
  for i in 0 ..< n:
    let pad = newPin([x1, y1], [x2, y2])
    pad.at[PinNumberPos].text = $num
    if name == "_" and i < h.len:
      pad.at[PinNamePos].text = h[i]
    var el: TreeEl = (boxEl(pad, pda), pad)
    pda.tree.insert(el)
    if dy != dy:
      break
    num += 1 - mnum * 2
    x1 += dx
    y1 += dy
    x2 += dx
    y2 += dy
  pda.paint

proc commandEntryActivate(entry: Entry; pda: PDA) =
  let com = entry.text
  var act = $pda.activeShape
  var sha: string
  let i = parseWhile(com, sha, {'a' .. 'z'}, 0)
  if sha in ["pin", "pad", "hole"]: # overwrite pda.activeShape
    act = sha
  if act notin ["pin", "pad", "hole"]:
    echo "Shape has no command support"
    return
  case act
  of "pin": pinCommand(com, pda)
  of "pad":  padCommand(com, pda)
  of "hole":  holeCommand(com, pda)
  else: discard

proc entryActivate(entry: Entry; pda: PDA) =
  if pda.movingObj != nil:
    Text(pda.movingObj).text = entry.text
    Text(pda.movingObj).isNew = entry.text.len > 0
    #pda.movingObj = nil
    pda.paint

proc lineWidthEntryActivate(entry: Entry) =
  echo "lineWidthEntryActivate"

proc colorEntryActivate(entry: Entry) =
  echo "lineWidthEntryActivate"

proc fontEntryActivate(entry: Entry) =
  echo "lineWidthEntryActivate"

proc gridToggled(b: ToggleButton; pda: PDA) =
  let i = b.getActive.int
  pda.activeG = i
  pda.activeGrid = [pda.grid[i], pda.grid[i + 2]]

# Caution: remember that (x == NaN) is alway false, so we do the test with x != x

proc worldActivate(entry: Entry; pda: PDA) =
  var x1, y1, x2, y2: float
  var px2, py2: int # bool
  (x1, y1, px2, x2, py2, y2) = (NaN, NaN, 0, NaN, 0, NaN) # defaults
  var res: bool
  var input = entry.text
  # using the plus matcher, so the '+' is optional
  res = scanf(input, "$f$[sep]$f${plus(0)}$f${plus(0)}$f", x1, y1, px2, x2, py2, y2)
  if not res and x1 != x1: # NaN
    return # or maybe set all to defaults?
  if not res and x1 == x1: # not NaN
    if y1 != y1: # NaN
      y1 = x1
    if y2 != y2: # NaN
      y2 = x2
      py2 = px2
    if x2 != x2: # NaN
      (x2, y2) = (x1, y1)
      (x1, y1) = (0.0, 0.0)
    else:
      if px2 == 1:
        x2 = x1 + x2
      if py2 == 1:
        y2 = y1 + y2
  if x2 <= x1 or y2 <= y1:
    return
  input.setLen(0)
  for f in [x1, y1, x2, y2]:
    input.add(fmt("{f:g}, "))
  input.setlen(input.len - 2)
  entry.setText(input)
  (pda.dataX, pda.dataY, pda.dataWidth, pda.dataHeight) = (x1, y1, x2, y2)
  pda.fullScale = min(pda.darea.allocatedWidth.float / pda.dataWidth, pda.darea.allocatedHeight.float / pda.dataHeight)
  updateAdjustments(pda, 0, 0)
  pda.paint

# caution, we have to set activeGrid too
# what can we do with zero or negative values? Zero may indicate no grid?
proc gridActivate(entry: Entry; pda: PDA) =
  var d: array[4, float] = [NaN, NaN, NaN, NaN] # majorX, minorX, majorY, minorY
  var input = entry.text
  entry.setIconFromIconName(EntryIconPosition.secondary, "dialog-error")
  var res: bool = scanf(input, "$f$[sep]$f$[sep]$f$[sep]$f", d[0], d[1], d[2], d[3])
  if d[0] != d[0]: # NaN
    return # or maybe set all to defaults?
  #if not res and d[0] == d[0]: # not NaN
  if d[1] != d[1]: # NaN
    d[1] = d[0]
  if d[2] != d[2]: # NaN
    d[2] = d[0]
  if d[3] != d[3]: # NaN
    d[3] = d[1]
  if d[0] < d[1]: swap(d[0], d[1])
  if d[2] < d[3]: swap(d[2], d[3])
  pda.activeGrid = [d[pda.activeG], d[pda.activeG + 2]]
  pda.grid = d
  input = d[0 .. ((d[0] != d[2] or d[1] != d[3]).int + 1) * 2 - 1].mapIt(fmt("{it:g}")).join(", ")
  entry.setText(input)
  entry.setIconFromIconName(EntryIconPosition.secondary, nil)
  pda.paint

proc entryChanged(entry: Entry; pda: PDA) =
  if pda.movingObj of Text:
    Text(pda.movingObj).text = entry.text
    pda.paint

proc lineWidthChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeLineWidth = LineWidths(cbt.getActive)

proc lineCapChanged(cbt: ComboBoxText; pda: PDA) =
  #pda.activeLineWidth = LineWidths(cbt.getActive)
  echo "lineCapChanged"

proc lineJoinChanged(cbt: ComboBoxText; pda: PDA) =
  #pda.activeLineWidth = LineWidths(cbt.getActive)
  echo "lineJoinChanged"

proc colorChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeColor = Colors(cbt.getActive)

proc fillColorChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeColor = Colors(cbt.getActive)

proc fontChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeFont = Fonts(cbt.getActive)

proc shapeChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeShape = Shapes(cbt.getActive)

proc dataDialogResponseCb(d: Dialog; id: int; pda: PDA) =
  #echo "response: ", ResponseType(id)
  if ResponseType(id) == ResponseType.ok:
    ### var buffer: TextBuffer = TextView(d.getContentArea.getFirstChild.getFirstChild).getBuffer # that would work too
    pda.textData = pda.textDataBuffer.getText(pda.textDataBuffer.getStartIter, pda.textDataBuffer.getEndIter, true)
    #echo pda.textData
    #discard
  d.destroy

proc openDataDialog(b: Button; pda: PDA) =
  #echo "openDataDialog"
  let dialog = newDialog()
  dialog.setMargin(10)
  dialog.title = "Dialog"
  dialog.setTransientFor(pda.applicationWindow)
  # dialog.setDestroyWithParent(true) # not useful for modal dialogs
  dialog.setModal(true)
  let contentArea = dialog.getContentArea
  let msg = newLabel("Data input")
  let scrolledWindow = newScrolledWindow()
  if pda.textDataBuffer == nil:
    pda.textDataBuffer = newTextBuffer()
  let view = newTextViewWithBuffer(pda.textDataBuffer)
  scrolledWindow.setChild(view)
  scrolledWindow.setSizeRequest(300, 300)
  scrolledWindow.setHExpand
  contentArea.append(scrolledWindow)
  discard dialog.addButton("OK", ResponseType.ok.ord)
  discard dialog.addButton("Cancel", ResponseType.cancel.ord)
  dialog.connect("response", dataDialogResponseCb, pda)
  dialog.show

proc modeChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeMode = Modes(cbt.getActive)

proc sizeChanged(cbt: ComboBoxText; pda: PDA) =
  #pda.activeMode = Modes(cbt.getActive)
  echo "sizeChanged"

proc xcolorChanged(cbt: ComboBoxText; pda: PDA) =
  #pda.activeMode = Modes(cbt.getActive)
  echo "xcolorChanged"

proc styleChanged(cbt: ComboBoxText; pda: PDA) =
  #echo cbt.getActiveText
  pda.activeStyle = Styles(cbt.getActive)

proc onAdjustmentEvent(adj: PosAdj; pda: PDA) =
  pda.paint

#proc onSetLineWidth(b: SpinButton; pda: PDA) =
#  pda.lineWidth = b.value

proc sizeSpinButtonValueChanged(s: SpinButton) =
  echo "value changed: ", s.getValue, " (", s.getValueAsInt, ")"

proc xcolorSet(b: ColorButton) =
  echo "xcolorSet"

# this proc is large!
proc newPDA(window: ApplicationWindow): PDA =
  result = newGrid(PDA)
  result.applicationWindow = window
  (result.dataX, result.dataY, result.dataWidth, result.dataHeight) = DefaultWorldRange
  result.tree = newRStarTree[8, 2, float, Element]()
  result.majorGridColor = (0.0, 0.0, 0.0, 0.8) # value will come from config later
  result.minorGridColor = (0.0, 0.0, 0.0, 0.4)
  result.activeShape = Shapes.line
  let da = newDrawingArea()
  let legacy = newEventControllerLegacy()
  da.addController(legacy)
  legacy.connect("event", distributeLegacyEvent, result)
  result.darea = da
  da.setHExpand
  da.setVExpand
  da.setDrawFunc(drawingAreaDrawCb, result)
  da.connect("resize", dareaConfigureCallback, result)
  result.zoomNearMousepointer = ZoomNearMousepointer # mouse wheel zooming
  result.userZoom = 1.0
  result.grid = DefaultGrid
  result.activeGrid[0] = DefaultGrid[0]
  result.activeGrid[1] = DefaultGrid[2]
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
  let open = newButton("Open")
  result.headerbar.packStart(open)
  result.topbox = newBox(Orientation.horizontal, 0)
  result.topbox2 = newBox(Orientation.horizontal, 0)
  let cbMode = newComboboxText()
  for el in Modes:
    cbMode.append(nil, $el)
  cbMode.setActive(0)
  cbMode.connect("changed", modeChanged, result)
  result.topbox2.append(cbMode)
  let cbSize = newComboboxText()
  for el in Sizes:
    cbSize.append(nil, $el)
  cbSize.setActive(0)
  cbSize.connect("changed", sizeChanged, result)
  result.topbox2.append(cbSize)

  let adj = newAdjustment(8.0, 0.0, 16.0, 1.0, 10.0, 0.0) # value, lower, upper, stepIncrement, pageIncrement, pageSize
  let sizeSpinButton = newSpinButton(adj, 0.0, 2)
  sizeSpinButton.setWidthChars(2)
  sizeSpinButton.connect("value-changed", sizeSpinButtonValueChanged)
  result.topbox2.append(sizeSpinButton)

  let cbXColor = newComboboxText()
  for el in XColors:
    cbXColor.append(nil, $el)
  cbXColor.setActive(0)
  cbXColor.connect("changed", xcolorChanged, result)
  result.topbox2.append(cbXColor)

  let xcolorButton = newColorButton()
  xcolorButton.setUseAlpha
  xcolorButton.connect("color-set", xcolorSet)
  result.topbox2.append(xcolorButton)

  let cbtShape = newComboboxText()
  for el in Shapes:
    cbtShape.append(nil, $el)
  cbtShape.setActive(0)
  cbtShape.connect("changed", shapeChanged, result)
  result.topbox.append(cbtShape)

  let dataDialogButton = newButton("?")
  dataDialogButton.connect("clicked", openDataDialog, result)
  result.topbox.append(dataDialogButton)

  let commandEntry = newEntry()
  commandEntry.connect("activate", commandEntryActivate, result)
  result.commandEntry = commandEntry
  result.topbox.append(commandEntry)

  let cbtStyle = newComboboxText()
  result.cbtStyle = cbtStyle
  for el in Styles:
    cbtStyle.append(nil, $el)
  cbtStyle.setActive(0)
  cbtStyle.connect("changed", styleChanged, result)
  result.topbox.append(cbtStyle)

  let entry = newEntry()
  entry.connect("activate", entryActivate, result)
  entry.connect("changed", entryChanged, result)
  entry.connect("notify::cursor-position", entryNotify, result)
  result.entry = entry
  result.topbox.append(entry)

  let world = newEntry()
  world.setPlaceholderText(DefaultWorldRange.mapIt(fmt("{it:g}")).join(", "))
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
  grid.setPlaceholderText(DefaultGrid.join(", "))
  grid.setWidthChars(16)
  grid.connect("activate", gridActivate, result)
  let gridLabel = newLabel()
  gridLabel.setMarkup("<big>\u{25A6}</big>")
  let gridButton = newToggleButton()
  gridButton.connect("toggled", gridToggled, result)
  gridButton.setChild(gridLabel)
  result.topbox.append(gridButton)
  result.topbox.append(grid)
  result.gridw = grid

  ### line width widgets
  let actionGroup: gio.SimpleActionGroup = newSimpleActionGroup()
  block:
 
    proc useLineWidth(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "use-line-width"
      discard

    proc newLineWidth(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "new-line-width"
      discard

    proc delLineWidth(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "del-line-width"
      discard

    proc lineWidthSpinButtonValueChanged(s: SpinButton) =
      echo "value changed: ", s.getValue, " (", s.getValueAsInt, ")"

    var action: SimpleAction
    action = newSimpleAction("use-line-width")
    discard action.connect("activate", useLineWidth)
    actionGroup.addAction(action)
    action = newSimpleAction("new-line-width")
    discard action.connect("activate", newLineWidth)
    actionGroup.addAction(action)
    action = newSimpleAction("del-line-width")
    discard action.connect("activate", delLineWidth)
    actionGroup.addAction(action)

    var builder = newBuilderFromString(useNewDelMenuData)
    var menuModel: gio.MenuModel = builder.getMenuModel("menuModel2")
    var menu = newPopoverMenu(menuModel)
    let menuButton = newMenuButton()
    menuButton.setIconName("accessories-text-editor")

    menuButton.setPopover(menu)
    result.topbox.append(newSeparator(Orientation.horizontal))
    result.topbox.append(newLabel(" "))
    #result.headerbar.packEnd(menuButton)

    let lineWidthStack = newStack()
    let lineWidthCB = newComboboxText()
    for el in LineWidths:
      lineWidthCB.append(nil, $el)
    lineWidthCB.setActive(0)
    lineWidthCB.connect("changed", lineWidthChanged, result)
    discard lineWidthStack.addNamed(lineWidthCB, "LineWidthCB")

    ###
    let lineWidthEntry = newEntry()
    lineWidthEntry.setWidthChars(6)
    lineWidthEntry.setMaxWidthChars(6)
    lineWidthEntry.connect("activate", lineWidthEntryActivate)
    discard lineWidthStack.addNamed(lineWidthEntry, "LineWidthEntry")
    lineWidthStack.setVisibleChild(lineWidthCB)
    result.topbox.append(lineWidthStack)
    let adj = newAdjustment(50.0, 0.0, 100.0, 1.0, 10.0, 0.0) # value, lower, upper, stepIncrement, pageIncrement, pageSize
    let lineWidthSpinButton = newSpinButton(adj, 0.0, 2)
    lineWidthSpinButton.setWidthChars(3)
    lineWidthSpinButton.connect("value-changed", lineWidthSpinButtonValueChanged)
    result.topbox.append(lineWidthSpinButton)

    let cbtLineCap = newComboboxText()
    for el in LineCaps:
      cbtLineCap.append(nil, $el)
    cbtLineCap.setActive(0)
    cbtLineCap.connect("changed", lineCapChanged, result)
    result.topbox.append(cbtLineCap)

    let cbtLineJoin = newComboboxText()
    for el in LineJoins:
      cbtLineJoin.append(nil, $el)
    cbtLineJoin.setActive(0)
    cbtLineJoin.connect("changed", lineJoinChanged, result)
    result.topbox.append(cbtLineJoin)

  ### color widgets
  block:
    proc useColor(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "use-color"
      discard

    proc newColor(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "new-color"
      discard

    proc delColor(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "del-color"
      discard

    proc colorSet(b: ColorButton) =
      echo "colorSet"

    var action: SimpleAction
    action = newSimpleAction("use-color")
    discard action.connect("activate", useColor)
    actionGroup.addAction(action)
    action = newSimpleAction("new-color")
    discard action.connect("activate", newColor)
    actionGroup.addAction(action)
    action = newSimpleAction("del-color")
    discard action.connect("activate", delColor)
    actionGroup.addAction(action)

    var builder = newBuilderFromString(useNewDelMenuData)
    var menuModel: gio.MenuModel = builder.getMenuModel("menuModel2")
    var menu = newPopoverMenu(menuModel)
    let menuButton = newMenuButton()
    menuButton.setIconName("applications-graphics")

    menuButton.setPopover(menu)
    result.topbox.append(newLabel(" "))
    result.topbox.append(menuButton)

    let colorStack = newStack()
    let colorCB = newComboboxText()
    for el in Colors:
      colorCB.append(nil, $el)
    colorCB.setActive(0)
    colorCB.connect("changed", colorChanged, result)
    discard colorStack.addNamed(colorCB, "ColorCB")

    let colorEntry = newEntry()
    colorEntry.setWidthChars(6)
    colorEntry.setMaxWidthChars(6)
    colorEntry.connect("activate", colorEntryActivate)
    discard colorStack.addNamed(colorEntry, "ColorEntry")
    colorStack.setVisibleChild(colorCB)
    result.topbox.append(colorStack)
    let colorButton = newColorButton()
    colorButton.setUseAlpha
    colorButton.connect("color-set", colorSet)
    result.topbox.append(colorButton)

  ### fill color widgets
  block:
    proc useFillColor(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "use-color"
      discard

    proc newFillColor(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "new-color"
      discard

    proc delFillColor(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "del-color"
      discard

    proc fillColorSet(b: ColorButton) =
      echo "fillColorSet"

    var action: SimpleAction
    action = newSimpleAction("use-fill-color")
    discard action.connect("activate", useFillColor)
    actionGroup.addAction(action)
    action = newSimpleAction("new-fill-color")
    discard action.connect("activate", newFillColor)
    actionGroup.addAction(action)
    action = newSimpleAction("del-fill-color")
    discard action.connect("activate", delFillColor)
    actionGroup.addAction(action)

    var builder = newBuilderFromString(useNewDelMenuData)
    var menuModel: gio.MenuModel = builder.getMenuModel("menuModel2")
    var menu = newPopoverMenu(menuModel)
    let menuButton = newMenuButton()
    menuButton.setIconName("image-x-generic")

    menuButton.setPopover(menu)
    result.topbox.append(newLabel(" "))
    result.topbox.append(menuButton)

    let fillColorStack = newStack()
    let fillColorCB = newComboboxText()
    for el in Colors:
      fillColorCB.append(nil, $el)
    fillColorCB.setActive(0)
    fillColorCB.connect("changed", fillColorChanged, result)
    discard fillColorStack.addNamed(fillColorCB, "FillColorCB")

    ###
    let colorEntry = newEntry()
    colorEntry.setWidthChars(6)
    colorEntry.setMaxWidthChars(6)
    colorEntry.connect("activate", colorEntryActivate)
    discard fillColorStack.addNamed(colorEntry, "ColorEntry")
    fillColorStack.setVisibleChild(fillColorCB)
    result.topbox.append(fillColorStack)
    let colorButton = newColorButton()
    colorButton.connect("color-set", fillColorSet)
    result.topbox.append(colorButton)

  ### font chooser widgets
  block:
 
    proc useFont(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "use-line-width"
      discard

    proc newFont(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "new-line-width"
      discard

    proc delFont(action: gio.SimpleAction; parameter: glib.Variant) =
      echo "del-line-width"
      discard

    var action: SimpleAction
    action = newSimpleAction("use-font")
    discard action.connect("activate", useFont)
    actionGroup.addAction(action)
    action = newSimpleAction("new-font")
    discard action.connect("activate", newFont)
    actionGroup.addAction(action)
    action = newSimpleAction("del-font")
    discard action.connect("activate", delFont)
    actionGroup.addAction(action)

    var builder = newBuilderFromString(useNewDelMenuData)
    var menuModel: gio.MenuModel = builder.getMenuModel("menuModel2")
    var menu = newPopoverMenu(menuModel)
    let menuButton = newMenuButton()
    menuButton.setIconName("accessories-text-editor")

    menuButton.setPopover(menu)
    #result.topbox.append(newSeparator(Orientation.horizontal))
    result.topbox.append(newLabel(" "))
    result.topbox.append(menuButton)

    let fontStack = newStack()
    let fontCB = newComboboxText()
    for el in Fonts:
      fontCB.append(nil, $el)
    fontCB.setActive(0)
    fontCB.connect("changed", fontChanged, result)
    discard fontStack.addNamed(fontCB, "FontCB")

    ###
    let fontEntry = newEntry()
    fontEntry.setWidthChars(6)
    fontEntry.setMaxWidthChars(6)
    fontEntry.connect("activate", fontEntryActivate)
    discard fontStack.addNamed(fontEntry, "FontEntry")
    fontStack.setVisibleChild(fontCB)
    result.topbox.append(fontStack)
    #let adj = newAdjustment(50.0, 0.0, 100.0, 1.0, 10.0, 0.0) # value, lower, upper, stepIncrement, pageIncrement, pageSize
    #let lineWidthSpinButton = newSpinButton(adj, 0.0, 2)
    #lineWidthSpinButton.setWidthChars(3)
    #lineWidthSpinButton.connect("value-changed", lineWidthSpinButtonValueChanged)
    let fontButton = newFontButtonWithFont("Sans 10")
    result.topbox.append(fontButton)

  ### gaction menu
  var label = newLabel("test")

  let menubutton = newMenuButton()
  #let actionGroup: gio.SimpleActionGroup = newSimpleActionGroup()

  var action: SimpleAction

  action = newSimpleAction("group-selection")
  discard action.connect("activate", groupSelection, result)
  actionGroup.addAction(action)

  action = newSimpleAction("break-up-group")
  discard action.connect("activate", breakUpGroup, result)
  actionGroup.addAction(action)

  action = newSimpleAction("save-group")
  discard action.connect("activate", saveGroup, result)
  actionGroup.addAction(action)

  action = newSimpleAction("load-group")
  discard action.connect("activate", loadGroup, result)
  actionGroup.addAction(action)

  action = newSimpleAction("detach-text")
  discard action.connect("activate", detachText, result)
  actionGroup.addAction(action)

  action = newSimpleAction("attach-text")
  discard action.connect("activate", attachText, result)
  actionGroup.addAction(action)

  action = newSimpleAction("edit-text")
  discard action.connect("activate", editText, result)
  actionGroup.addAction(action)

  var v = newVariantBoolean(false)

  #v = newVariantBoolean(false) # for gintro <= v0.9.4 see https://github.com/StefanSalewski/gintro/issues/178
  action = newSimpleActionStateful("toggle-show-pad-numbers", nil, v)
  discard action.connect("activate", toggleShowPadNumbers, result)
  actionGroup.addAction(action)

  #v = newVariantBoolean(false)
  action = newSimpleActionStateful("toggle-show-pad-names", nil, v)
  discard action.connect("activate", toggleShowPadNames, result)
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
  var menu = newPopoverMenu(menuModel)
  menuButton.setPopover(menu)
  result.headerbar.packEnd(menuButton)
  let save = newButton("Save")
  result.headerbar.packEnd(save)

  ###
  result.attach(result.topbox, 0, -2, 2, 1)
  result.attach(result.topbox2, 0, -1, 2, 1)
  result.botbox = newBox(Orientation.horizontal, 0)
  result.botbox.append(label)
  result.attach(result.botbox, 0, 2, 2, 1)

proc startup(app: Application) =
  echo "appStartup"

proc activate(app: Application) =
  let window = app.newApplicationWindow
  window.title = "Simple design tool"
  window.defaultSize = DefaultWindowSize
  let pda = newPDA(window)
  window.setChild(pda)
  window.setTitlebar(pda.headerbar) # before window.show()
  window.show

proc newDisplay =
  let app = newApplication("org.gtk.example")
  app.connect("startup", startup)
  app.connect("activate", activate)
  let status = app.run
  quit(status)

when isMainModule: # 2531 lines drawLine newComboboxText 100 move newToggleButton activeGrid editText notify drawText newPin newText drawLine styles  newLine style
  newDisplay() # sqrt Group newVariantBoolean move items filter elements newPad newHole drawPath mapIt
