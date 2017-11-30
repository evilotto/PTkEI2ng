"""Maintains arbitrary output windows."""

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
import string
import re

import MyText
import empParse
import empQueue
import empCmd

###########################################################################
#############################  Simple window  #############################
class SimpDisp(empParse.baseDisp):
    """Display command output in its own window."""
    def __init__(self, disp, title = "Empire output", width=None):
        empParse.baseDisp.__init__(self, disp)

        # Create root window
        self.Root = Tkinter.Toplevel(class_="Output")
        self.Root.title(title)
        self.Root.iconname(title)

        title = string.lower(string.split(title, None, 1)[0])
        # Create text box and scrollbar
        scrollY = Tkinter.Scrollbar(self.Root, name="scrollY")
        scrollY.pack(side='right', fill='y')
        self.Text = MyText.MyText(self.Root, name=title, setgrid=1, 
                                  yscrollcommand=scrollY.set)
        self.Text.setEditable(0)
        self.Text.pack(side='left', expand=1, fill='both')
        scrollY['command'] = self.Text.yview

        # Forward key events to main window.
        viewer.transferKeys(self.Root)

        # Allow configurable width
        if width is not None:
            self.Text['width']=width

        self.Text.bind('<Button-3>', viewer.DoLocateSector)
        self.Root.protocol('WM_DELETE_WINDOW', self.goAway)

    def goAway(self):
        """Tk callback: Remove the window from the display."""
        self.data = empQueue.doNothing
        self.Root.destroy()

    def data(self, line):
        if self.data is empQueue.doNothing:
            # Window was closed
            return
        self.Text.setEditable(1)
        self.Text.insert('end', line+"\n")
        self.Text.setEditable(0)

class CmdWind(empCmd.baseCommand):
    description = "Output arbitrary command to its own Tk Window."

    defaultPreList = 1
    defaultBinding = (('wind', 4),)

    def invoke(self):
        args = self.commandMatch.group('args')
        self.Send(args, SimpDisp(self.out, args))

class CmdCShow(empCmd.baseCommand):
    description = "Display 'show X bui;show X sta;show X cap' in its own window."

    defaultBinding = (('cshow', 5),)

    commandUsage = "cshow {land|plane|ship} [<tech level>]"
    commandFormat = re.compile(r"^(?P<unitType>\S+)(?P<techLevel>.*)$")
    def invoke(self):
        mm = self.parameterMatch
        new = empCmd.ParseShow(SimpDisp(
            self.out, self.commandMatch.string, 140))
        if mm.group('techLevel') is None:
            tl = ""
        else:
            tl = mm.group('techLevel')
        self.Send("show "+mm.group('unitType')+" build"+tl, new)
        self.Send("show "+mm.group('unitType')+" stat"+tl, new)
        self.Send("show "+mm.group('unitType')+" cap"+tl, new)
