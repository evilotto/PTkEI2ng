import Tkinter
import string

# This class is a copy of the TkTextMixin class of the Anygui project
# (http://anygui.sourceforge.net).  It can be found in the source file
# backends/tkgui.py.

# Copyright (c) 2001, 2002 Magnus Lie Hetland, Thomas Heller, Alex
# Martelli, Greg Ewing, Joseph A. Knapka, Matthew Schinckel, Kalle
# Svensson, Shanky Tiwari, Laura Creighton, Dallas T. Johnston,
# Patrick K. O'Brien, Phil Cook.

class MyText(Tkinter.Text):
    """This is a replacement of the Tkinter Text widget.  It only
    supports selection and copy of text but not editing.  Simply using
    state = 'disabled' didn't work as it disabled those actions.  When the widget is uneditable """
    
    def __init__(self, *args, **kw):
        if kw.has_key('next'):
            self.next = kw['next']
            del kw['next']
        else:
            self.next = None
        apply(Tkinter.Text.__init__, (self,) + args, kw)
        self.ctl = 0
        self.alt = 0
        self.shift = 0
        self.editable = 1
        self.bind("<Key>", self.keybinding)
        #self.bind("<KeyRelease>", self.updateProxy) # Ensure all changes reach Proxy.
        self.bind("<KeyPress-Control_L>", self.ctldown)
        self.bind("<KeyRelease-Control_L>", self.ctlup)
        self.bind("<KeyPress-Alt_L>", self.altdown)
        self.bind("<KeyRelease-Alt_L>", self.altup)
        self.bind("<KeyPress-Shift_L>", self.shiftdown)
        self.bind("<KeyRelease-Shift_L>", self.shiftup)
        self.bind("<Key-Insert>", self.insertbinding)
        self.bind("<Key-Up>", self.arrowbinding)
        self.bind("<Key-Down>", self.arrowbinding)
        self.bind("<Key-Left>", self.arrowbinding)
        self.bind("<Key-Right>", self.arrowbinding)
        self.bind("<ButtonRelease>", self.insertbinding)
        self.bind("<Button-2>", self.mousebinding)

        # Easy place to put this - not _editable-related, but common
        # to all text selfs.
        #self.bind("<Leave>", self.updateProxy)

    # Track modifier key state.
    def ctldown(self, ev):
        self.ctl = 1
    def ctlup(self, ev):
        self.ctl = 0
    def altdown(self, ev):
        self.alt = 1
    def altup(self, ev):
        self.alt = 0
    def shiftdown(self, ev):
        self.shift = 1
    def shiftup(self, ev):
        self.shift = 0

    def mousebinding(self, ev):
        print 'entering mousebinding'
        if self.editable:
            return None
        else:
            if self.next:
                self.next.focus_set()
                self.next.insert('insert', self.selection_get())
            return "break"


    def keybinding(self, ev):
        """ This method binds all keys, and causes them to be
        ignored when _editable is not set. """
        if self.editable:
            return None
        else:
            # This is truly horrid. Please add appropriate
            # code for Mac platform, someone.
            if (ev.char == "\x03") or (ev.char == "c" and self.alt):
                # DON'T ignore this key: it's a copy operation.
                return None
            if self.next:
                self.next.focus_set()
                if (ev.char and ev.char in string.printable and ev.char != '\t'
                    and ev.char != '\r'):
                    self.next.insert('end', ev.char)
            return "break"
            
    def insertbinding(self, ev):
        # Overrides keybinding for the Insert key.
        if self.editable:
            return None
        if self.ctl:
            # Allow copy.
            return None
        return "break"

    def arrowbinding(self, ev):
        # This method's sole reason for existence is to allow arrows
        # to work even when self.editable is false.
        return None

    def setEditable(self, editable):
        self.editable = editable
