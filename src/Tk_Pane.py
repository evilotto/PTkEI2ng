"""Primitive interface that allows internal windows to be resized."""

#    Copyright (C) 1998-1999 Kevin O'Connor
#
#    This program is free software; you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation; either version 2 of the License, or
#    (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with this program; if not, write to the Free Software
#    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

import Tkinter

###########################################################################
#############################  Pane interface #############################
class paned:
    """Simple paned window interface."""

    def __init__(self, root, win1, win2):
        self.win1 = win1
        self.win2 = win2

        self.PFrame = Tkinter.Frame(root, name="pane")
        self.PFrame.pack(side='top', expand=1, fill='both')
        self.PFrame.lower()

        win1.place(in_=self.PFrame, relwidth=1.0)
        win2.place(in_=self.PFrame, relwidth=1.0)

        self.Grip = Tkinter.Frame(root, name="grip", height=10, width=10,
                          cursor='sb_v_double_arrow',
                          borderwidth=2, relief='raised')
        self.Grip.place(in_=self.PFrame, relx=0.8, rely=0.5, y=-5)
        self.Grip.bind('<1>', self.Press)
        self.Grip.bind('<Button1-Motion>', self.Drag)
        self.Grip.bind('<ButtonRelease-1>', self.Release)

        # Setup a callback function
        self.PFrame.after_idle(self.resize)
##	self.PFrame.bind('<Configure>', self.resize)

    def resize(self):
        self.PFrame.configure({'width':max(self.win1.winfo_reqwidth(),
                                           self.win2.winfo_reqwidth()),
                               'height':(self.win1.winfo_reqheight()
                                         + self.win2.winfo_reqheight())})
        self.ratio = (float(self.win1.winfo_reqheight())
                      / (self.win1.winfo_reqheight()
                         + self.win2.winfo_reqheight()))
        self.win1.place(relheight=self.ratio)
        self.win2.place(rely=self.ratio, relheight=1.0-self.ratio)
        self.Grip.place(rely=self.ratio)
##	self.PFrame.bind('<Configure>', None)
##	print event.height

    def Press(self, event):
        self.Grip['relief'] = 'sunken'
    def Release(self, event):
        self.Grip['relief'] = 'raised'
        self.win1.place(relheight=self.ratio)
        self.win2.place(rely=self.ratio, relheight=1.0-self.ratio)
    def Drag(self, event):
##	if event.y > 0 and event.y < 10:
##	    return
        val = (float(event.y_root-self.win1.winfo_rooty())
               / (self.win1.winfo_height()+self.win2.winfo_height()))
        if val > 1.0:
            val = 1.0
        elif val < 0.0:
            val = 0.0
        self.Grip.place(rely=val)
        self.ratio = val
