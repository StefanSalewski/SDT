#
import gintro/[gtk4, gobject, gio, glib, cairo]
import times

var qt = "GTKLV" & $epochTime()
if g_quark_try_string(qt) != 0:
  qt = "NGIQ" & $epochTime()
let CVquark: int = quark_from_static_string(qt) # caution, do not use name Quark!

type
  XLayers {.pure.} = enum # will become user extendable
    line, rect, pad, hole, circ, text, trace, path, attr, net, pin

const
  LayerNames = ["Ground", "Power", "Signal", "Remark", "Net", "Pin"]

type
  LayerRow* = object
    name*: string
    style*: string
    group*: string
    locked*: bool
    visible*: bool

var
  layers* = newSeq[LayerRow](LayerNames.len)
  selectedLayer: int

proc initLayers =
  for i, el in mpairs(layers):
    el.name = LayerNames[i]
    el.style = "default"
    el.group = "G"
    el.visible = true
    
    
proc findLayer*(name: string): int =
  if name.len == 0:
    return selectedLayer
  result = -1
  for i, el in layers:
    if el.name == name:
      return i
      
type
  ColumnViewGObject = ref object of gobject.Object

proc onSelectionChanged(self: SelectionModel; pos: int; nItems: int) =
  selectedLayer = cast[SingleSelection](self).getSelected
  echo "onSelectionChanged"
  #echo pos, nItems
  #echo typeof(cast[SingleSelection](self).getModel)
  echo "bbb ", self.getSelection.maximum

proc onLayerNameChanged(w: Text) =
  let row = cast[int](w.getQdata(CVquark))
  layers[row].name = w.text

proc onStyleNameChanged(w: Text) =
  let row = cast[int](w.getQdata(CVquark))
  layers[row].style = w.text

proc onGroupNameChanged(w: Text) =
  let row = cast[int](w.getQdata(CVquark))
  layers[row].group = w.text

proc onLockedChanged(w: CheckButton) =
  let row = cast[int](w.getQdata(CVquark))
  layers[row].locked = w.active
  echo layers

proc onVisibilityChanged(w: CheckButton) =
  let row = cast[int](w.getQdata(CVquark))
  layers[row].visible = w.active

proc draw(d: DrawingArea; cr: cairo.Context; w, h: int) =
  echo "draw", w, " ", h
  cr.setSource(1, 0, 0)
  cr.paint

proc setup0(f: SignalListItemFactory; item: Object) =
  let l = newLabel()
  cast[ListItem](item).setChild(l)

proc setup1(f: SignalListItemFactory; item: Object) =
  let l = newText()
  l.connect("activate", onLayerNameChanged)
  cast[ListItem](item).setChild(l)

proc setup2(f: SignalListItemFactory; item: Object) =
  let l = newText()
  l.connect("activate", onStyleNameChanged)
  cast[ListItem](item).setChild(l)

proc setup3(f: SignalListItemFactory; item: Object) =
  let l = newText()
  l.connect("activate", onGroupNameChanged)
  cast[ListItem](item).setChild(l)

proc setup4(f: SignalListItemFactory; item: Object) =
  let l = newCheckButton()
  l.connect("toggled", onLockedChanged)
  cast[ListItem](item).setChild(l)

proc setup5(f: SignalListItemFactory; item: Object) =
  let l = newCheckButton()
  l.connect("toggled", onVisibilityChanged)
  cast[ListItem](item).setChild(l)

proc setup6(f: SignalListItemFactory; item: Object) =
  let l = newDrawingArea()
  l.setContentWidth(4)
  l.setContentHeight(4)
  l.setDrawFunc(draw)
  cast[ListItem](item).setChild(l)

proc bind0(f: SignalListItemFactory; item: Object) =
  let item = cast[ListItem](item)
  let l = Label(item.getChild())
  l.text = $item.getPosition

proc bind1(f: SignalListItemFactory; item: Object) =
  let item = cast[ListItem](item)
  let l = Text(item.getChild())
  l.setQdata(CVquark, cast[pointer](item.getPosition))
  l.text = layers[item.getPosition].name

proc bind2(f: SignalListItemFactory; item: Object) =
  let item = cast[ListItem](item)
  let l = Text(item.getChild())
  l.setQdata(CVquark, cast[pointer](item.getPosition))
  l.text = layers[item.getPosition].style

proc bind3(f: SignalListItemFactory; item: Object) =
  let item = cast[ListItem](item)
  let l = Text(item.getChild())
  l.setQdata(CVquark, cast[pointer](item.getPosition))
  l.text = layers[item.getPosition].group

proc bind4(f: SignalListItemFactory; item: Object) =
  let item = cast[ListItem](item)
  let l = CheckButton(item.getChild())
  l.setQdata(CVquark, cast[pointer](item.getPosition))
  l.setActive(layers[item.getPosition].locked)

proc bind5(f: SignalListItemFactory; item: Object) =
  let item = cast[ListItem](item)
  let l = CheckButton(item.getChild())
  l.setQdata(CVquark, cast[pointer](item.getPosition))
  l.setActive(layers[item.getPosition].visible)

proc bind6(f: SignalListItemFactory; item: Object) =
  let item = cast[ListItem](item)
  let l = DrawingArea(item.getChild())

# e.g. double click on item
proc onColumnViewActivate(cv: ColumnView, pos:int) =
  echo "onColumnViewActivate"

proc createLayersWidget*: ScrolledWindow =
  initLayers()
  let cv = newColumnView()
  ###cv.setHexpand
  #cv.setSingleClickActivate(false)
  cv.addCssClass("data-table") # [.column-separators][.rich-list][.navigation-sidebar][.data-table]

  let c0 = newColumnViewColumn()
  c0.title = "#"
  let f0 = newSignalListItemFactory()
  f0.connect("setup", setup0)
  f0.connect("bind", bind0)
  c0.setFactory(f0)
  cv.appendColumn(c0)

  let c1 = newColumnViewColumn()
  c1.title = "Layer   "
  let f1 = newSignalListItemFactory()
  f1.connect("setup", setup1)
  f1.connect("bind", bind1)
  c1.setFactory(f1)
  cv.appendColumn(c1)

  let c2 = newColumnViewColumn()
  c2.title = "Style   "
  ###c2.setExpand
  let f2 = newSignalListItemFactory()
  f2.connect("setup", setup2)
  f2.connect("bind", bind2)
  c2.setFactory(f2)
  cv.appendColumn(c2)

  let c3 = newColumnViewColumn()
  c3.title = "Group"
  let f3 = newSignalListItemFactory()
  f3.connect("setup", setup3)
  f3.connect("bind", bind3)
  c3.setFactory(f3)
  cv.appendColumn(c3)

  let c4 = newColumnViewColumn()
  c4.title = "L."
  let f4 = newSignalListItemFactory()
  f4.connect("setup", setup4)
  f4.connect("bind", bind4)
  c4.setFactory(f4)
  cv.appendColumn(c4)

  let c5 = newColumnViewColumn()
  c5.title = "V."
  let f5 = newSignalListItemFactory()
  f5.connect("setup", setup5)
  f5.connect("bind", bind5)
  c5.setFactory(f5)
  cv.appendColumn(c5)

  let c6 = newColumnViewColumn()
  #c6.title = "V."
  let f6 = newSignalListItemFactory()
  f6.connect("setup", setup6)
  f6.connect("bind", bind6)
  c6.setFactory(f6)
  cv.appendColumn(c6)

  cv.connect("activate", onColumnViewActivate)

  let gtype = gObjectGetType()
  var listStore = gio.newListStore(gtype)

  for i in 0 .. LayerNames.high:
    let o = newObjectv(ColumnViewGObject, gtype, 0, nil)
    #o.name = Names[i]#.sample
    #o.age = rand(18 .. 95)
    listStore.append(o)

  let model = cast[SelectionModel](newSingleSelection(cast[ListModel](listStore)))
  model.connect("selection-changed", onSelectionChanged)
  cv.setModel(model)
  result = newScrolledWindow()
  #result.setMinContentWidth(2000)
  #result.setSizeRequest(800, -1)
  result.setPolicy(PolicyType.never, PolicyType.automatic)
  result.setChild(cv)

