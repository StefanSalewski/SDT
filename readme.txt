Styles and Attributes:

To all elements like lines, circles or text styles and optional attributes
are assigned. A typical simple style consists of two attributes:
color and linewidth. We may call this style "default". When we
draw lines and that style is active then the lines get this style.
At the same time the actual attributes linewidth and color are
displayed in widgets. The user can select another style, create new styles
or temporqary modify single attributes of the cuurent style. Modifying an existing style
temporary should be done only in rare cases. When new elements are created after an
style has been temporary modified, then that modified attribute is additional attached
to the new elements. It is always possible to modify a style permanently, in that case
the modification is applied to all existing elememnts.

We may have various style classes like line styles for geometric shapes, and a fillstyle
and a textstyle.

User interaction:

We try to make the user interface as modeless as possible. The user should not have
to changes modes often. Example drawing lines: Double click of left mouse botton starts
a line, user moves mouse pointer to endpoint of line and next double click terminates that line.
At the same time the user can move lines or other elements: Press left mouse button over
an element, move the mouse to move the element, and release the mouse button to end this action.
For lines the user can grab and move endpoints of a line, or he can grab and move the whole line when he grabs
the center of the line.  

Data structures:

We have simple elements like lines, rectangles, cirles, text and such. And compound
objects which are built from the simple elements. A set of simple elements can be
converted to an compound object, and compound objects can be split again
in simple elements. Compound elements can again contain compound elements.

We do not use an OOP design with inheritance for the elements, but multiple
lists with a single data type. That is we we have sequences of lines, circles, text and such.
And a list with compound objects. Each compound object has again list of simple
elements and optional a list of other compound objects.

