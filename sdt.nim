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
# v0.1 2021-AUG-30

import std/[times, parseutils, strutils, strformat, strscans]
from std/math import round, floor, `^`, `mod`
from std/sequtils import mapIt, applyIt
import gintro/[gtk4, gdk4, glib, gobject, gio, cairo, pango, pangocairo]
import rtree
import salewski, minmax #xpairs

const # make config option later
  ShowPadNumbers = true
  ShowPadNames = false

const
  ### SchematicGrid = 10 # base unit in schematic mode, pin length should be 200 or 300
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

const
  GrabDist = 3           # mm
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
          <attribute name="label">Normal Menu Item</attribute>
          <attribute name="action">win.normal-menu-item</attribute>
        </item>
        <item>
          <attribute name="label">Group Selection</attribute>
          <attribute name="action">win.group-selection</attribute>
        </item>
        <item>
          <attribute name="label">Detach Text</attribute>
          <attribute name="action">win.detach-text</attribute>
        </item>
        <item>
          <attribute name="label">Atach Text</attribute>
          <attribute name="action">win.atach-text</attribute>
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
    #textSize: float
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
    line, rect, pad, circ, text, trace, path, pin, attr

type
  LineCaps {.pure.} = enum
    butt, round, square

type
  LineJoins {.pure.} = enum
    miter, round, bevel

type
  Styles {.pure.} = enum
    medium, thin, thick, fat, pin, pad, none

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
  CvBlue = [0.0, 0, 1, 0.8]
  CvWhite = [1.0, 1, 1, 0.8]
  CvBlack = [0.0, 0, 0, 0.8]
  CvGray = [0.5, 0.5, 0.5, 0.8]

type
  XColors {.pure.} = enum
    bigGrid, smallGrid, background, shadow, alert, junction, pinNumber, pinName

const
  XColorValues = [CVGray, CvGray, CvWhite, CvBlack, CvRed, CvBlue, CvBlue, CvBlue]

# we could use the enums as indices directly, but later we do user extent the style set...
var styles: array[6, Style]
styles[Styles.medium.ord] = Style(lineWidth: 1.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0))
styles[Styles.thin.ord] = Style(lineWidth: 0.5, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (1.0, 0.0, 0.0, 1.0))
styles[Styles.thick.ord] = Style(lineWidth: 1.5, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 1.0, 0.0, 1.0))
styles[Styles.fat.ord] = Style(lineWidth: 4.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (1.0, 0.0, 0.0, 1.0))
styles[Styles.pin.ord] = Style(lineWidth: 1.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0), xcolor: (1.0, 0.0, 0.0, 1.0))
styles[Styles.pad.ord] = Style(lineWidth: 0.0, lineCap: LineCap.round, lineJoin: LineJoin.miter, color: (0.0, 0.0, 1.0, 1.0), xcolor: (1.0, 1.0, 1.0, 1.0))

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
  let (x1, y1, x2, y2, x3, y3) = (p1.x, p1.y, p2.x, p2.y, p.x, p.y)
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
  PinNumberPos = 0
  PinNamePos = 1

type
  Element = ref object of RootRef
    style: Styles
    p: seq[V2]
    at: seq[Text] # atached text
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
    absSize: bool

proc grabPos(e: Element; i: int): var V2 =
  e.p[i + 2]

template x1(e: Element): float = e.p[0].x
template y1(e: Element): float = e.p[0].y
template x2(e: Element): float = e.p[1].x
template y2(e: Element): float = e.p[1].y

#template `x1=`(e: Element; v: float) = e.p[0].x = v
#template `y1=`(e: Element; v: float) = e.p[0].y = v
#template `x2=`(e: Element; v: float) = e.p[1].x = v
#template `y2=`(e: Element; v: float) = e.p[1].y = v

type
  Line = ref object of Element

type
  Trace = ref object of Element

type
  Rect = ref object of Element

type
  Circ = ref object of Element

type
  Pad = ref object of Element
    cornerRadius: float

type
  Path = ref object of Element

type
  Pin = ref object of Element

type
  Group = ref object of Element
    lines: seq[Line]
    circs: seq[Circ]

proc move(el: Element; v: V2) =
  el.p.applyIt(it + v)

proc moveAttachedText(el: Element; v: V2) =
  for t in el.at:
    if t != nil and not t.detached:
      move(t, v)

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

proc newText(p1, p2: V2; text: string): Text =
  result = Text(text: text)
  result.p = newSeq[V2](2 + 9)
  result.p[0] = p1
  result.p[1] = p2

proc newPad(p1, p2: V2): Pad =
  let h = sortedPair(p1, p2)
  result = Pad(p: @[h[0], h[1]])
  result.style = Styles.pad
  result.at = @[Text(nil), Text(nil)] # number and name
  #let (x1, y1, x2, y2) = (p1[0], p1[1], p2[0], p2[1])
  #result.at[PadNamePos] = newText(((x1 + x2) * 0.5, (y1 + y2) * 0.5), (x2, y2), "Name")
  #result.at[PadNumberPos] = newText(((x1 + x2) * 0.5, (y1 + y2) * 0.5), (x2, y2), "Num")

proc newCirc(p1, p2: V2): Circ =
  Circ(p: @[p1, p2])

proc putPinText(pin: Pin) =
  if pin.at[PinNamePos].detached:
    discard
  else:
    pin.at[PinNamePos].p[0] = pin.p[0]
    pin.at[PinNamePos].p[1] = pin.p[1]
    var x1, y1, x2, y2, x, y: float
    var gx, gy: int
    (x1, y1) =  pin.p[0]
    (x2, y2) =  pin.p[1]
    if y1 == y2:
      y = y1
      x = x2
      gy = 1
      if x1 < x2:
        gx = 0
      else:
        gx = 2
      pin.at[PinNamePos].p[0] = (x, y)
      pin.at[PinNamePos].p[1] = (x, y)
      pin.at[PinNamePos].gx = gx
      pin.at[PinNamePos].gy = gy

      y = y1
      x = x2
      gy = 2
      if x1 < x2:
        gx = 2
      else:
        gx = 0
      pin.at[PinNumberPos].p[0] = (x, y)
      pin.at[PinNumberPos].p[1] = (x, y)
      pin.at[PinNumberPos].gx = gx
      pin.at[PinNumberPos].gy = gy

    if x1 == x2:
      y = y2
      x = x1
      gx = 1
      if y1 < y2:
        gy = 0
      else:
        gy = 2
      pin.at[PinNamePos].p[0] = (x, y)
      pin.at[PinNamePos].p[1] = (x, y)
      pin.at[PinNamePos].gx = gx
      pin.at[PinNamePos].gy = gy

      y = y2
      x = x1
      gx = 0
      if y1 < y2:
        gy = 2
      else:
        gy = 0
      pin.at[PinNumberPos].p[0] = (x, y)
      pin.at[PinNumberPos].p[1] = (x, y)
      pin.at[PinNumberPos].gx = gx
      pin.at[PinNumberPos].gy = gy

proc newPin(p1, p2: V2): Pin =
  result = Pin(p: @[p1, p2])
  assert PinNamePos == 1
  result.at.add(newText(p1, p2, "13"))
  result.at.add(newText(p1, p2, "Name"))

  result.style = Styles.pin
  result.putPinText

# distances
proc sqrDistanceLine(l: Line; xy: V2): float =
  distanceLinePointSqr(l.p[0], l.p[1], xy)[1]

proc sqrDistancePin(l: Pin; xy: V2): float =
  distanceLinePointSqr(l.p[0], l.p[1], xy)[1]

proc sqrDistancePath(l: Path; xy: V2): float =
  result = float.high
  for l in l.p.xpairs:
    result = min(result, distanceLinePointSqr(l[0], l[1], xy)[1])

proc sqrDistanceTrace(t: Trace; xy: V2): float =
  distanceLinePointSqr(t.p[0], t.p[1], xy)[1]

proc sqrDistanceRB(x1, y1, x2, y2: float; xy: V2): float = # distance to rectangle border
  [(x1, y1, x1, y2), (x1, y1, x2, y1), (x2, y2, x1, y2), (x2, y2, x2, y1)].mapIt(distanceLinePointSqr((it[0], it[1]), (it[2], it[3]), xy)[1]).min

proc sqrDistanceR(x1, y1, x2, y2: float; xy: V2): float =
  if (xy.x > x1 and xy.x < x2) and (xy.y > y1 and xy.y < y2): # in rectangle
    return 0
  sqrDistanceRB(x1, y1, x2, y2, xy) # distance to boarder

proc sqrDistanceRect(r: Rect; xy: V2): float =
  sqrDistanceR(r.x1, r.y1, r.x2, r.y2, xy)

proc sqrDistancePad(r: Pad; xy: V2): float =
  sqrDistanceR(r.x1, r.y1, r.x2, r.y2, xy)

proc sqrDistanceCirc(c: Circ; xy: V2): float =
  max(math.hypot(c.x1 - xy.x, c.y1 - xy.y) - math.hypot(c.x1 - c.x2, c.y1 - c.y2), 0) ^ 2

proc sqrDistanceText(t: Text; xy: V2): float =
  var (x, y) = xy
  x += (t.p[1].x - t.p[0].x) * (t.gx mod 3).float * 0.5
  y += (t.p[1].y - t.p[0].y) * (t.gy mod 3).float * 0.5
  sqrDistanceR(t.x1, t.y1, t.x2, t.y2, (x, y)) # caution, this is not xy!

proc sqrDistanceGroup(g: Group; xy: V2): float =
  sqrDistanceR(g.x1, g.y1, g.x2, g.y2, xy)

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
  Tree = RStarTree[8, 2, float, Element]

iterator allElements(tree: Tree; x: Element): Element =
  for el in tree.elements:
    yield el
  if x != nil:
    yield x

proc elAndText(tree: Tree): (Element, Text) =
  for el in tree.elements:
    if el.selected:
      if el of Text:
        result[1] = Text(el)
      else:
        result[0] = el
      if result[0] != nil and result[1] != nil:
        return result

proc selectedText(tree: Tree): Text =
  for el in tree.elements:
    if el of Text and el.selected:
      return Text(el)

type
  PDA = ref object of gtk4.Grid
    entry: Entry
    commandEntry: Entry
    world: Entry
    gridw: Entry
    cbtStyle: ComboBoxText
    activeShape: Shapes
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
    bcolor: RGBA
    majorGridColor: RGBA
    minorGridColor: RGBA
    guideColor: RGBA
    activeGrid: V2
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
  result.bcolor = (1.0, 1.0, 1.0, 1.0)
  result.majorGridColor = (0.0, 0.0, 0.0, 0.8)
  result.minorGridColor = (0.0, 0.0, 0.0, 0.4)
  result.guideColor = (1.0, 0.0, 0.0, 0.7)
  result.activeShape = Shapes.line

# we will fix this proc later, it's good enough for now
# convert abs distance x in mm into distance value for GtkDrawingArea
# when drawing with cairo and cairo_scale == 1
proc absToScr(pda: PDA; x: float): float =
  var scale {.global.}: float
  if scale == 0:
    let d = gdk4.getDefaultDisplay()
    #let m = gdk4.getMonitor(d, 0)
    #let glm = gdk4.getMonitors(d)
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
  #let fullScale = min(r.width.float / pda.dataWidth,
  #    r.height.float / pda.dataHeight)
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
proc getUserCoordinates(pda: PDA; v: V2): V2 =
  ((v.x - pda.hadjustment.upper * 0.5 + pda.hadjustment.value) / (pda.fullScale * pda.userZoom) + pda.dataX + pda.dataWidth * 0.5,
   (v.y - pda.vadjustment.upper * 0.5 + pda.vadjustment.value) / (pda.fullScale * pda.userZoom) + pda.dataY + pda.dataHeight * 0.5)

proc roundToMultiple(x, m: float): float =
  ((x / m) + 0.5).floor * m

proc roundToGrid(pda: PDA; v: V2): V2 =
  (roundToMultiple(v.x, pda.activeGrid.x), roundToMultiple(v.y, pda.activeGrid.y))

proc cairoDevRound(w: float): float =
  if w < 1.5:
    0.5
  else:
    floor((w + 0.5) mod 2) / 2

proc move(pda: PDA): bool =
  let (a, b) = (pda.lastButtonDownPosUser) #.x, pda.lastButtonDownPosUser.y)
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
      if a > x1 - d and a < x1 + d:
        pda.movingObj.x1 += dxdy[0]
      elif a > x2 - d and a < x2 + d:
        pda.movingObj.x2 += dxdy[0]
      if b > y1 - d and b < y1 + d:
        pda.movingObj.y1 += dxdy[1]
      elif b > y2 - d and b < y2 + d:
        pda.movingObj.y2 += dxdy[1]
  elif pda.movingObj of Group:
    move(pda.movingObj, dxdy)
    for el in Group(pda.movingObj).lines:
      let h = cast[Element](el) # silly nimsuggest issue
      move(h, dxdy)
    for el in Group(pda.movingObj).circs:
      move(el, dxdy)

  elif pda.movingObj of Pad:
    move(pda.movingObj, dxdy)

  elif (a - pda.movingObj.x1) ^ 2 + (b - pda.movingObj.y1) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
    pda.movingObj.p[0] += dxdy
  elif (a - pda.movingObj.x2) ^ 2 + (b - pda.movingObj.y2) ^ 2 < (pda.absToScr(GrabDist)) ^ 2:
    pda.movingObj.p[1] += dxdy
  else:
    pda.movingObj.p[0] += dxdy
    pda.movingObj.p[1] += dxdy
  pda.lastButtonDownPosUser += dxdy
  moveAttachedText(pda.movingObj, dxdy)
  if pda.movingObj of Pin:
    putPinText(Pin(pda.movingObj))
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
  let dx = -(t.p[1].x - t.p[0].x) * (t.gx mod 3).float * 0.5
  let dy = -(t.p[1].y - t.p[0].y) * (t.gy mod 3).float * 0.5
  [(t.x1 + dx, t.x2 + dx), (t.y1 + dy, t.y2 + dy)]

proc boxPath(l: Path; pda: PDA): rtree.Box[2, float] =
  var (xa, xb, ya, yb) = (l.p[0].x, l.p[0].x, l.p[0].y, l.p[0].y)
  for el in l.p:
    xa = min(xa, el.x)
    xb = max(xb, el.x)
    ya = min(ya, el.y)
    yb = max(yb, el.y)
  [(xa, xb), (ya, yb)]

proc boxEl(el: Element; pda: PDA): rtree.Box[2, float] =
  if el of Line or el of Pin or el of Trace or el of Rect or el of Group or el of Pad:
    result = box(el, pda)
  elif el of Circ:
    result = boxCirc(Circ(el), pda)
  elif el of Text:
    result = boxText(Text(el), pda)
  elif el of Path:
    result = boxPath(Path(el), pda)

proc editText(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let t = selectedText(pda.tree)
  if t != nil:
    var el: L[2, float, Element]
    el = (boxEl(t, pda), Element(t))
    pda.tree.delete(el)
    pda.entry.setText(t.text)
    pda.movingObj = t
  discard pda.entry.grabFocus

# attach "free" text, or attach detached text again
proc atachText(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  let (l, t) = pda.tree.elAndText
  if l == nil:
    return

  # re-attach one only
  if t != nil and t.detached and t notin l.at:
    echo "text belongs to different object"
    return
  if l != nil and t != nil and t.detached and t in l.at:
    t.detached = false
    var el: L[2, float, Element]
    el = (boxEl(t, pda), Element(t))
    pda.tree.delete(el)
    return

  # try re-attach all
  var succ: bool
  if l != nil and t == nil:
    for t in l.at:
      if t.detached:
        succ = true
        t.detached = false
        var el: L[2, float, Element]
        el = (boxEl(t, pda), Element(t))
        pda.tree.delete(el)
  if not succ:
    echo "no detached text found"
      
  # we can always add new "free" text attributes 
  if l != nil and t != nil and not t.detached:
    t.detached = false
    l.at.add(t)
    var el: L[2, float, Element]
    el = (boxEl(t, pda), Element(t))
    pda.tree.delete(el)

proc detachText(action: gio.SimpleAction; parameter: glib.Variant; pda: PDA) =
  var collector: seq[Element]
  for el in pda.tree.allElements(nil):
    if el.selected:
      collector.add(el)
  for el in collector:
    for text in el.at:
      if text.text == "":
        text.text  = "_?_"
      var t: L[2, float, Element] = (boxEl(text, pda), text)
      text.detached = true
      pda.tree.insert(t)

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

proc drawText(t: Text; pda: PDA; size: float = 8)

proc drawLine(l: Line; pda: PDA) =
  pda.cr.moveTo(l.x1, l.y1)
  pda.cr.lineTo(l.x2, l.y2)
  for el in l.at:
    el.drawText(pda)

proc drawPath(l: Path; pda: PDA) =
  pda.cr.newPath
  for p in l.p:
    pda.cr.lineTo(p.x, p.y)

proc drawTrace(l: Trace; pda: PDA) =
  pda.cr.moveTo(l.x1, l.y1)
  pda.cr.lineTo(l.x2, l.y2)

proc drawRect(r: Rect; pda: PDA) = # rectangle
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)

proc drawText(t: Text; pda: PDA; size: float = 8) =
  if t == nil:
    return
  const Font = "Serif 8px" # later we take that from style
  var context = pda.darea.createPangoContext
  var layout = pango.newLayout(context)
  var desc = pango.newFontDescription(Font)
  #desc.setAbsoluteSize(pda.absToScr(pango.SCALE.float * 10))

  #desc.setAbsoluteSize((pango.SCALE.float * size))
  desc.setSize((pango.SCALE.float * 16.0 / pda.fullScale).int) # works, text size does not change! Size in points.
  #desc.setAbsoluteSize((pango.SCALE.float * 16.0 / pda.fullScale)) # works too, text size does not change! Size in pixel.

  pda.cr.moveTo(t.x1, t.y1)
  layout.setText(t.text)
  layout.setFontDescription(desc)
  var w, h: int
  layout.getSize(w, h)
  let width = w.float / pango.Scale.float
  let height = h.float / pango.Scale.float
  if (height) * pda.userZoom < pda.absToScr(5): return
  t.p[1] = t.p[0] + (width, height)
  let dx = -width * (t.gx mod 3).float * 0.5
  let dy = -height * (t.gy mod 3).float * 0.5
  pda.cr.moveTo(t.x1 + dx, t.y1 + dy)
  pda.cr.updateLayout(layout)
  pangocairo.showLayout(pda.cr, layout)
  if t.isNew:
    var el: L[2, float, Element] = (boxEl(t, pda), t)
    pda.tree.insert(el)
    t.isNew = false
    pda.movingObj = nil
  for i in 0 .. 8:
    let x = t.x1 + width * (i mod 3).float * 0.5
    let y = t.y1 + height * (i div 3).float * 0.5
    t.grabPos(i) = (x + dx, y + dy)

proc drawPad(r: Pad; pda: PDA) =
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)
  pda.cr.setLineWidth(0)
  pda.cr.fill
  pda.cr.setSource(styles[r.style.ord].color)
  pda.cr.setSource(0, 0, 0, 1)

  if ShowPadNumbers and ShowPadNames:
    if r.at[PadNumberPos] != nil and r.at[PadNamePos] != nil:
      r.at[PadNumberPos].gx = 2
      r.at[PadNumberPos].gy = 1
      r.at[PadNamePos].gx = 0
      r.at[PadNamePos].gy = 1
      let ts = min(r.x2 - r.x1, r.y2 - r.y1)
      drawText(r.at[PadNumberPos], pda, ts)
      drawText(r.at[PadNamePos], pda, ts)
  elif ShowPadNumbers or ShowPadNames:
    let ts = min(r.x2 - r.x1, r.y2 - r.y1)
    var i = PadNumberPos
    if ShowPadNames:
      i  = PadNamePos
    if r.at[i] != nil: 
      r.at[i].gx = 1
      r.at[i].gy = 1
      drawText(r.at[i], pda, ts)

proc drawPin(l: Pin; pda: PDA) =
  var h = math.hypot(l.x2 - l.x1, l.y2 - l.y1)
  if h == 0:
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
  pda.cr.setSource(XColorValues[XColors.pinName.ord])
  drawText(l.at[PinNamePos], pda)
  pda.cr.setSource(XColorValues[XColors.pinNumber.ord])
  drawText(l.at[PinNumberPos], pda)

proc drawCirc(c: Circ; pda: PDA) =
  let r = math.hypot(c.x1 - c.x2, c.y1 - c.y2)
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
  let width = t.p[1].x - t.p[0].x
  let height = t.p[1].y - t.p[0].y
  let dx = -width * (t.gx mod 3).float * 0.5
  let dy = -height * (t.gy mod 3).float * 0.5
  pda.cr.rectangle(t.x1 + dx, t.y1 + dy, width, height)
  pda.cr.stroke
  for i in 0 .. 8:
    pda.drawGrabCirc(t.grabPos(i).x, t.grabPos(i).y)

proc drawLineGrab(l: Line; pda: PDA) = # TODO: join with drawPathGrab
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

proc drawPinGrab(l: Pin; pda: PDA) = # TODO: join with drawPathGrab
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
  let r = math.hypot(c.x1 - c.x2, c.y1 - c.y2)
  pda.cr.newPath
  pda.cr.arc(c.x1, c.y1, r + d, 0, math.Tau)
  pda.cr.stroke
  pda.cr.newPath
  pda.cr.arc(c.x1, c.y1, r - d, 0, math.Tau)
  pda.cr.stroke
  pda.drawGrabCirc(c.x2, c.y2)

proc drawPadGrab(r: Pad; pda: PDA) =
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
  pda.cr.setSource(0, 0, 1, 0.1)
  pda.cr.rectangle(r.x1, r.y1, r.x2 - r.x1, r.y2 - r.y1)
  pda.cr.fill

proc sqrDistance(el: Element; xy: V2): float =
  if el of Line:
    result = sqrDistanceLine(Line(el), xy)
  if el of Pin:
    result = sqrDistancePin(Pin(el), xy)
  elif el of Path:
    result = sqrDistancePath(Path(el), xy)
  elif el of Trace:
    result = sqrDistanceTrace(Trace(el), xy)
  elif el of Rect:
    result = sqrDistanceRect(Rect(el), xy)
  elif el of Pad:
    result = sqrDistancePad(Pad(el), xy)

  elif el of Circ:
    result = sqrDistanceCirc(Circ(el), xy)
  elif el of Text:
    result = sqrDistanceText(Text(el), xy)
  elif el of Group:
    result = sqrDistanceGroup(Group(el), xy)

# squared distance from query point to
proc dist(qo: BoxCenter[2, float]; el: L[2, float, Element]): float =
  sqrDistance(el.l, (qo[0], qo[1]))

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

  elif el of Circ:
    drawCirc(Circ(el), pda)
  elif el of Text:
    drawText(Text(el), pda)
  elif el of Group:
    drawGroup(Group(el), pda)

proc drawElGrab(el: Element; pda: PDA) =
  if el of Line:
    drawLineGrab(Line(el), pda)
  elif el of Pin:
    drawPinGrab(Pin(el), pda)

  elif el of Path:
    drawPathGrab(Path(el), pda)
  elif el of Trace:
    if styles[el.style.ord].lineWidth < 0.8 * GrabDist:
      drawTraceGrab(Trace(el), pda)
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
        pda.setLineWidthAbs(styles[l.style.ord].lineWidth * (1.0 + 0.6 * (selected.int + (l == pda.hover).int).float))
        drawEl(l, pda)
        #pda.setLineWidthAbs(styles[l.style.ord].lineWidth * (1.0 + 0.6 * (selected.int + (l == pda.hover).int).float))
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
      pda.cr.paintWithAlpha(1.0) #0.7)
      patternDestroy(tmp1)

proc drawingAreaDrawCb(darea: DrawingArea; cr: cairo.Context; width, height: int; pda: PDA) =
  if pda.pattern.isNil: return
  ### var t0 = cpuTime()
  cr.setSource(pda.pattern)
  cr.paint
  #echo "CPU time [s] ", cpuTime() - t0
  if pda.selecting:
    cr.rectangle(pda.lastButtonDownPos.x, pda.lastButtonDownPos.y, pda.zoomRect.x - pda.lastButtonDownPos.x, pda.zoomRect.y -
        pda.lastButtonDownPos.y)
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
  let x = pda.legEvXY.x
  let y = pda.legEvXY.y
  let (a, b) = pda.getUserCoordinates(pda.legEvXY)

  if pda.uact == dragging and pda.movingObj != nil:
    pda.lastMousePos = pda.legEvXY
    discard pda.move
    paint(pda)

  if math.hypot(x - pda.lastButtonDownPos.x, y - pda.lastButtonDownPos.y) > 2:
    if pda.uact == lmbdv:
      pda.uact = zooming
    elif pda.uact == lmbdo:
      pda.uact = dragging #selecting
      assert pda.movingObj != nil
      var el: L[2, float, Element]
      var l = pda.movingObj
      el = (boxEl(l, pda), l)
      pda.tree.delete(el)

  var el: Element = pda.tree.findNearest(BoxCenter[2, float]([a, b]), dist)[1]
  if el != nil:
    if sqrDistance(el, (a, b)) < (pda.absToScr(GrabDist)) ^ 2:
      pda.hover = el
      el.hover = true
    else:
      pda.hover = nil

  if pda.uact == selecting: #state.contains(button1): # selecting
    pda.selecting = true
    pda.zoomRect = (x, y)
    pda.darea.queueDraw #Area(0, 0, pda.darea.allocatedWidth, pda.darea.allocatedHeight)
  elif false: #button2 in state: # panning
    pda.updateAdjustmentsAndPaint(pda.lastMousePos.x - x, pda.lastMousePos.y - y)
  pda.lastMousePos = (x, y)
  if pda.points.len > 0 or pda.hover != pda.lastHover:
    if pda.points.len == 1:
      let p = pda.roundToGrid((a, b))
      if pda.movingObj of Path:
        pda.movingObj.p[^1] = p
      else:
        pda.movingObj.p[1] = p
        if pda.movingObj of Pin:
          let n = Pin(pda.movingObj).at[PinNamePos]
          if false:#n.detached:
            var el: L[2, float, Element]
            el = (boxEl(n, pda), Element(n))
            pda.tree.delete(el)
            n.detached = false
          Pin(pda.movingObj).putPinText
    paint(pda)
    pda.lastHover = pda.hover
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
    let x = pda.legEvXY.x
    let y = pda.legEvXY.y
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
  (pda.lastButtonDownPosUser.x, pda.lastButtonDownPosUser.y) = pda.getUserCoordinates(pda.legEvXY)
  if pda.uact == constructing:
    discard
  elif pda.hover.isNil:
    pda.uact = lmbdv
  else:
    pda.uact = lmbdo
    pda.movingObj = pda.hover
  return gdk4.EVENT_STOP

# zoom into selected rectangle and center it
# math: we first center the selection rectangle, and then compensate for translation due to scale

proc buttonReleaseEvent(c: EventControllerLegacy; event: ButtonEvent; pda: PDA): bool =
  let x = pda.legEvXY.x
  let y = pda.legEvXY.y
  let xy = [x, y]
  if pda.uact == UserAction.lmbdv and pda.hover == nil: # and pda.selected.lines.len > 0:
    var h = false
    for el in pda.tree.allElements(nil): #pda.movingObj):
      if el.selected: h = true
      el.selected = false
    if h:
      paint(pda)
      pda.uact = UserAction.none
      return
  if pda.uact == UserAction.lmbdo and pda.hover != nil:
    pda.movingObj = nil
    if pda.hover of Text:
      let width = pda.hover.p[1].x - pda.hover.p[0].x
      let height = pda.hover.p[1].y - pda.hover.p[0].y
      let olddx = -width * (pda.hover.gx mod 3).float * 0.5
      let olddy = -height * (pda.hover.gy mod 3).float * 0.5
      for i in 0 .. 8:
        let (x, y) = pda.getUserCoordinates((x, y))
        if (x - pda.hover.grabPos(i).x) ^ 2 + (y - pda.hover.grabPos(i).y) ^ 2 < pda.absToScr(GrabDist) ^ 2:
          var el: L[2, float, Element]
          el = (boxEl(pda.hover, pda), pda.hover)
          discard pda.tree.delete(el)
          pda.hover.gx = i mod 3
          pda.hover.gy = i div 3
          var dx = -width * (pda.hover.gx mod 3).float * 0.5
          var dy = -height * (pda.hover.gy mod 3).float * 0.5
          var dxdy = pda.roundToGrid((olddx - dx, olddy - dy))
          pda.hover.p[0] += dxdy
          pda.hover.p[1] += dxdy
          pda.movingObj = pda.hover
          pda.hover.isNew = true
          paint(pda)
          break
    var ret = false
    for l in pda.tree.allElements(nil):
      if l == pda.hover:
        if not l.selected: ret = true
        l.selected = true
    if ret:
      pda.uact = UserAction.none
      return
  if pda.movingObj != nil and pda.uact == dragging:
    var el: L[2, float, Element]
    var l = pda.movingObj
    el = (boxEl(l, pda), l)
    pda.tree.insert(el)
    pda.uact = UserAction.none

  #var uc = pda.getUserCoordinates(xy) # does not compile
  let uc = pda.getUserCoordinates((xy[0], xy[1]))
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
    if not (l of Pin):#l.style == Styles.none:
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
        var el: L[2, float, Element] = (boxEl(l, pda), l)
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
      var el: L[2, float, Element] = (boxEl(l, pda), l)
      pda.tree.insert(el)
      pda.points.setLen(0)
      pda.uact = UserAction.none
    if l of Pad:
      let (x1, y1, x2, y2) = (l.p[0].x, l.p[0].y, l.p[1].x, l.p[1].y)
      l.at[PadNamePos] = newText(((x1 + x2) * 0.5, (y1 + y2) * 0.5), (x2, y2), "Name")
      l.at[PadNumberPos] = newText(((x1 + x2) * 0.5, (y1 + y2) * 0.5), (x2, y2), "Num")


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
    pda.legEvXY = (x, y)
  else: discard

  case e.getEventType
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
    Text(pda.movingObj).text.insert("|", c)
    pda.paint

# Caution: remember that (x == NaN) is alway false, so we do the test with x != x
# This works currently for pads only -- later we will be able to create other objects as well
proc commandEntryActivate(entry: Entry; pda: PDA) =
  var x1, y1, x2, y2, r, dx, dy: float
  var n, px2, py2, mnum, num: int
  var id, name: string
  (x1, y1, x2, y2, r, num, name, dx, dy, n) = (NaN, NaN, NaN, NaN, 0.0, 0, "", NaN, NaN, 1) # defaults
  var res: bool
  var input = entry.text
  # using the plus matcher, so the '+' is optional
  res = scanf(input, "$[skipName]$[sep]$f$[sep]$f${plus(0)}$f${plus(0)}$f${optFloat(0)}${minus(0)}$i${optName(0)}$[sep]$f$[sep]$f$[sep]$i", x1, y1, px2, x2, py2, y2, r, mnum, num, name, dx, dy, n)
  if y2 != y2:
    return
  x2 += x1 * px2.float
  y2 += y1 * py2.float
  for i in 1 .. n:
    let pad = newPad((x1, y1), (x2, y2))
    pad.at[PadNamePos] = newText(((x1 + x2) * 0.5, (y1 + y2) * 0.5), (x2, y2), name)
    pad.at[PadNumberPos] = newText(((x1 + x2) * 0.5, (y1 + y2) * 0.5), (x2, y2), $num)
    var el: L[2, float, Element] = (boxEl(pad, pda), pad)
    pda.tree.insert(el)
    if dy != dy:
      break
    num += 1 - mnum * 2
    x1 += dx
    y1 += dy
    x2 += dx
    y2 += dy
  pda.paint

proc entryActivate(entry: Entry; pda: PDA) =
  if pda.movingObj != nil:
    Text(pda.movingObj).text = entry.text
    Text(pda.movingObj).isNew = true
    pda.paint

proc lineWidthEntryActivate(entry: Entry) =
  echo "lineWidthEntryActivate"

proc colorEntryActivate(entry: Entry) =
  echo "lineWidthEntryActivate"

proc fontEntryActivate(entry: Entry) =
  echo "lineWidthEntryActivate"

proc gridToggled(b: ToggleButton; pda: PDA) =
  let i = b.getActive.int
  pda.activeGrid = (pda.grid[i], pda.grid[i + 2])

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

proc modeChanged(cbt: ComboBoxText; pda: PDA) =
  pda.activeMode = Modes(cbt.getActive)

proc sizeChanged(cbt: ComboBoxText; pda: PDA) =
  #pda.activeMode = Modes(cbt.getActive)
  echo "sizeChanged"

proc xcolorChanged(cbt: ComboBoxText; pda: PDA) =
  #pda.activeMode = Modes(cbt.getActive)
  echo "xcolorChanged"

proc styleChanged(cbt: ComboBoxText) =
  echo cbt.getActiveText

proc onAdjustmentEvent(adj: PosAdj; pda: PDA) =
  pda.paint

#proc onSetLineWidth(b: SpinButton; pda: PDA) =
#  pda.lineWidth = b.value

proc sizeSpinButtonValueChanged(s: SpinButton) =
  echo "value changed: ", s.getValue, " (", s.getValueAsInt, ")"

proc xcolorSet(b: ColorButton) =
  echo "xcolorSet"

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
  result.activeGrid.x = DefaultGrid[0]
  result.activeGrid.y = DefaultGrid[2]
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

  let commandEntry = newEntry()
  commandEntry.connect("activate", commandEntryActivate, result)
  #entry.connect("changed", entryChanged, result)
  #entry.connect("notify::cursor-position", entryNotify, result)
  result.commandEntry = commandEntry
  result.topbox.append(commandEntry)

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
  action = newSimpleAction("change-label-button")
  discard action.connect("activate", changeLabelButton, label)
  actionGroup.addAction(action)

  action = newSimpleAction("normal-menu-item")
  discard action.connect("activate", normalMenuItem, label)
  actionGroup.addAction(action)

  action = newSimpleAction("group-selection")
  discard action.connect("activate", groupSelection, result)
  actionGroup.addAction(action)

  action = newSimpleAction("detach-text")
  discard action.connect("activate", detachText, result)
  actionGroup.addAction(action)

  action = newSimpleAction("atach-text")
  discard action.connect("activate", atachText, result)
  actionGroup.addAction(action)

  action = newSimpleAction("edit-text")
  discard action.connect("activate", editText, result)
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
  (pda.dataX, pda.dataY, pda.dataWidth, pda.dataHeight) = DefaultWorldRange
  window.setChild(pda)
  window.setTitlebar(pda.headerbar) # before window.show()
  window.show

proc newDisplay =
  let app = newApplication("org.gtk.example")
  app.connect("startup", startup)
  app.connect("activate", activate)
  let status = app.run
  quit(status)

when isMainModule: # 2300 lines newColorButton block image colorButton sizerequest destroy oha newComboboxText move hypot drawPin newPin newText drawText
  newDisplay() # newBox newButton drawText xcolorButton newSpinButton drawPin newPin newText editText buttonRelease dragging echo newText
  # atachText delete editText iterator delete drawRectGrab newText commandEntry newPad drawPad newPin xcolor drawRect newPad newLine
  # move drawText newPad newText drawText nim absToScr atach drawLine move detach newText setSize drawPad drawText moveAttachedText

#[
newAttribute:
  new text attached to selected object iterator jecho plus minus detach echo

]#
