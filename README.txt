NDT -- Nim Drawing Tool


This app is a small tool to draw simple vector graphics.
Basic shapes like lines, rectangles, circles and some more
are supported.

The tool is the foundation to more specialized variants like a
app for drawing schematiocs of electronic circuits.

The main goals of the tool are

- easy to use
- nice look

Currently we use GTK4 with cairo for the GUI. The program is written in the Nim language,
offering clean python like code and high performance. Cairo is not the fastest 2D drawing
lib, but it is directly supported by GTK and offers varioous backends including SVG and PDF.
RTree based logic will restict the redraw to changed entities, so performance should be acceptable
even for 4k and 8 k screens and low performance CPUs.

User interface

Various basic shapes like line, rectangle, circle or text can be selected.

For each shape named styles can be selected from lists, for example styles named
"Default", "Thin", "Thick", "Large font". When styles are modified later, all entities
using that style are updated automatically. Additional entities can avoid use of styles
but can use individual properties like linewidth or color. In these case the properties are
bound to the entities.

The GUI tries to be modeless whenever possible. For example while we are drawing new
lines we can at the same time move or resize existing elements. There is no need to select a 
different mode for the most used operations. Most operations work with the left mouse button (LMB).
For example to draw a line we click with the LMB on the starting point, move the mouse pointer to
its end point, and click again. Click meand press and release of the mouse button. Moving
of objects works by grag gestures: To move a line end point, we move the mouse pointer
to one end of the line, press and hold the LMB and move the mouse. When we release the mouse
button the line end point has changed.

Grid

Hover

Elements under the mouse pointer are drawn in a special way, currently with a more saturated color
and a shadow.

Selections

Objects can be selected with a mouse click. Clicking on a void area unselects all selected elements.
When multiple elements are selected, and we move one of them, then all other selected
elements move in the same way. Selected elements are also drawn in a more saturated color
and with shadow, giving the indication of lifting bthem from the paper surface.

Groups

Elements can be grouped. Grouped elements behave like a single entity. Groups can contain other
groups.
