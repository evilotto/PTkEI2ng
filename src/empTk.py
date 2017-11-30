"""Module that interacts with Python/Tk."""

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
import Pmw
import select
import string
import types
import re
import operator
import os

import Tk_Pane
import Tk_VDB
import MapWin
import CenWin
import LoginWin
import MyText
import OutWin
import TeleWin

import empQueue
import empDb
import empParse
import empCmd
import empEval
import empPath

# Key Ideas:

# What is contained within this file:

# This file contains the main viewer class that is created by empire.py
# when a Tk connection is used.  The mainWin class defined below is
# instanciated and stored in the global variable "viewer".  viewer should
# then be accessible from all the major modules in this package.  The
# mainWin class supports all the standard callbacks that the empire queue
# (see the file empQueue.py) expects "viewer" to support.  In addition to
# these standard features, mainWin also contains the code and Tk callbacks
# for much of the main root window that is opened on the display.  It
# directly controls the sub-prompt window, the command-line window, the
# command-output window, and the root window itself.  The censor window is
# controlled by code within the CenWin.py file; the map window is
# controlled by MapWin.py, and much of the status-line is controlled by
# LoginWin.py.


# Global variables:

# viewer : For Tk clients, viewer is an instance of class mainWin.


# Relationship to the other Tk files in this package:

# The map window in the main root window is controlled by code within
# MapWin.py.  Additional map windows may be popped up using the command
# "Map" (See the method CmdMap() for more info).

# The censor window in the main root window is controlled by code from
# CenWin.py.

# An arbitrary number of output windows may be popped up at any time.  The
# command "wind" is controlled by the method CmdWind.  These output windows
# are controlled via the OutWin.py file.  Also, the output from the "cshow"
# command (see the method CmdCShow) is sent to one of these output windows.

# The login window may be opened via the command "Login" (see the CmdLogin
# method), or directly via an empQueue.py callback.  The class attribute
# viewer.loginCallback is a pointer to the loginWin class stored in the
# file LoginWin.py.  The LoginWin.py file supports the Tk interface to the
# login window, and it also supports the login callbacks needed by the
# empire queue.  In addition to login requests, the LoginWin.py file
# currently also supports code to handle the status line (see the
# QueueStatus class contained in LoginWin.py).

# There is a telegram window that may be popped up via the command "wread"
# (see CmdWRead() ).  All the functions necessary to support the telegram
# window are contained within the file TeleWin.py.

# The file Tk_Pane.py contains the low-level functionality that supports
# the paned interface in the root window.  (The drag-and-drop box that
# allows the map window and command-line to be resized.)

# The file Tk_VDB.py contains the low-levl code that currently reads in
# entries from the Tk options list and attempts to convert them to
# meaningful ptkei client data.  This is still fairly primitive.

# The file Tk_List.py supports a listbox that is more powerful than the
# standard Tk listbox.  It is not called directly from this file, but it is
# used by the telegram window and the censor window.


###########################################################################
#############################  Main window    #############################
class mainWin:
    """Tk interface"""

    def __init__(self):
        global viewer
        MapWin.viewer = CenWin.viewer = LoginWin.viewer = \
                        TeleWin.viewer = OutWin.viewer = \
                        viewer = self

        # Setup the balloon help.
        self.Balloon = Pmw.Balloon(Display)

        self.msgQueue = []
        self.stsList = []
        self.updateList = []
        self.atPrompt = 0

        self.Root = Display
        self.Root.title("Python/Tk Empire Interface")

        self.coord = Tkinter.StringVar()

        statusbar = Tkinter.Frame(self.Root, name="statusbar")
        statusbar.pack(side='bottom', anchor='s', fill='both')
        coordLabel = Tkinter.Label(self.Root, name="coord",
                                   textvariable=self.coord, width=20,
                                   relief="sunken")
        coordLabel.pack(in_=statusbar, fill='both', side='right')
        self.Balloon.bind(coordLabel, "Empire coordinates")
        self.queueStatus = LoginWin.QueueStatus(statusbar)

        self.Status = Tkinter.Entry(self.Root, name="status", relief='sunken')
        self.Status.pack(in_=statusbar, fill='both', expand=1)
        self.Status.bind('<Key-Return>', self.DoStatus)
        self.Status.insert(0, "Welcome to empire!")
        self.Status['state']='disabled'

##  	# Create a main PanedWidget with top and bottom panes.
##  	pane = Pmw.PanedWidget(self.Root, hull_width='7i', hull_height=800)
##  	pane.pack(side='right', expand=1, fill='both')

        mapframe = Tkinter.Frame(self.Root, name="mapframe", class_="Map")
##  	mapframe = Tkinter.Frame(self.Root, name="mapframe", class_="Map")
##  	mapframe.pack(in_=pane.add('top'), expand=1, fill='both')
##  	mapframe = Tkinter.Frame(pane.pane('top'), name="mapframe", class_="Map")
##  	mapframe.pack(expand=1, fill='both')
##  	mapframe = pane.add('mapframe')

        self.map = MapWin.mapSubWin(mapframe)
        self.mapList = [self.map]

        infoframe = Tkinter.Frame(self.Root, name="infoframe")
        infoframe.pack(side='left', fill='both')
        self.CmdPrompt = Tkinter.Label(self.Root, name="cmdprompt",
                                       anchor='ne')
        self.CmdPrompt.pack(in_=infoframe, side='bottom', anchor='s',
                            fill='x')
        self.CmdPrompt.bind('<Configure>',
                            (lambda e, cp=self.CmdPrompt:
                             cp.configure({'wraplength': e.width})))
        self.Balloon.bind(self.CmdPrompt, "Empire prompt")
        self.cen = CenWin.cenWin(infoframe)

        ioframe = Tkinter.Frame(self.Root, name="ioframe", class_="Censor")
##  	ioframe.pack(in_=pane.add('bottom', size=400), expand=1, fill='both')
##  	ioframe = Tkinter.Frame(pane.pane('bottom'), name="ioframe",
##  				class_="Censor")
##  	ioframe.pack(expand=1, fill='both')
##  	ioframe = pane.add('ioframe')

        self.Prompt = Tkinter.Entry(self.Root, name="prompt")
        self.Prompt.pack(in_=ioframe, side='bottom', anchor='s', fill='x')
        self.Prompt.bind('<Key-Return>', self.DoCmd)
        self.Prompt.bind('<Control-z>', self.DoCtld)
        self.Prompt.bind('<Up>', (lambda e, s=self: s.DoHistoryMove(1)))
        self.Prompt.bind('<Down>', (lambda e, s=self: s.DoHistoryMove(-1)))
        self.Prompt.focus()

        scrollY = Tkinter.Scrollbar(self.Root, name="ioscrollbar")
        scrollY.pack(in_=ioframe, side='right', anchor='e', fill='y')
        self.Output = MyText.MyText(self.Root, name="iobox",
                                    yscrollcommand=scrollY.set,
                                    next = self.Prompt)
        self.Output.setEditable(0)
        self.Output.pack(in_=ioframe, side='left', anchor='se',
                         expand=1, fill='both')
##  	scrollY = Tkinter.Scrollbar(ioframe, name="ioscrollbar")
##  	scrollY.pack(side='right', anchor='e', fill='y')
##  	self.Output = Tkinter.Text(ioframe, name="iobox", state='disabled',
##  				   yscrollcommand=scrollY.set)
##  	self.Output.pack(side='left', anchor='se',
##  			 expand=1, fill='both')
        scrollY['command'] = self.Output.yview
        self.Output.bind('<Button-3>', self.DoLocateSector)
        self.Output.bind('<Configure>', (lambda e, s=self.Output:
                                         s.see('end')))
##  	# Windows hack!
##  	bindFocus(self.Output)

        pane = Tk_Pane.paned(self.Root, mapframe, ioframe)
        self.Balloon.bind(pane.Grip, "Resize window")

        self.Root.bind('<Prior>',
                       (lambda e, s=self.Output:
                        s.yview('scroll', -1, 'page')))
        self.Root.bind('<Next>',
                       (lambda e, s=self.Output:
                        s.yview('scroll', 1, 'page')))
        self.Root.bind('<Tab>',
                       (lambda e, s=self:
                        s.insertText(s.cen.getKey()) or "break"))
        self.Root.bind('<Alt-Key>', self.DoAltHandler)

        # Establish default bindings for text prompts
        Tk_VDB.setTextOptions(self.Output,
                              ('data', 'prompt', 'command', 'flush',
                               'subcommand', 'flash', 'inverse', 'error'))
##	self.lwrite(('data', 'data'), "\n", ('prompt :', 'prompt'),
##		    ('command', 'command'), "\n",
##		    ('subprompt :', 'subprompt'),
##		    ('subcommand', 'subcommand'), "\n", ('flash', 'flash'))

        self.loginCallback = LoginWin.loginWin()
        self.telegramWindow = TeleWin.teleWin()
        self.Root.update_idletasks()
        self.Root.pack_propagate(0)
        infoframe.pack_propagate(0)
        InitFileHandler()
    #
    # Tk callbacks - Bindings for keypresses/mouse events:
    #

    def DoHistoryMove(self, offset):
        """Move up or down the command-line history list."""
        try:
            cmd = self.ioq.HistMove(offset, self.Prompt.get())
        except IndexError:
            self.Root.bell()
        else:
            self.Prompt.delete(0, 'end')
            self.Prompt.insert(0, cmd)

    def DoCmd(self, event):
        """Tk callback:  Accept the command, and send to server."""
        cmd = self.Prompt.get()
        self.Prompt.delete(0, 'end')
        try:
            self.ioq.HistSend(cmd)
        except IndexError:
            self.Root.bell()

    def DoAltHandler(self, event):
        """Tk callback:  Handle Alt+key events."""
        key = event.keysym
        if len(key) != 1 or key not in empDb.pathDirections:
            return
        # Put the key into the input window.
        self.Root.focus_lastfor().insert('insert', key)
        # Find the new location.
        range = self.cen.getSect()
        sect1 = empDb.directionToSector((range[0], range[2]), key)
        sect2 = empDb.directionToSector((range[1], range[3]), key)
        # Change the censor window.
        self.cen.SetSect((sect1[0], sect2[0], sect1[1], sect2[1]))
        # Ouch - something massive is also attached to these keys..  Must
        # "break" to prevent cpu hogging..
        return "break"

    def DoCtld(self, event):
        self.ioq.Send("ctld")

    sectorFormat = re.compile(empParse.s_sector)
    def DoLocateSector(self, event):
        """Tk callback:  Highlight a sector from its text description.

        This function will grab a sector designation (of the form x,y) from
        a text output window and highlight the sector on the map.  It works
        with any text output window; in addition to the main command-line
        window, this function is called from the telegram/output windows.
        """
        win = event.widget
        pos = "@%s,%s" % (event.x, event.y)
        start = win.search("^|[^-0-9,]", pos+" + 1 chars",
                           regexp=1, backwards=1)
        end = win.search("[^-0-9,]|$", pos, regexp=1)
        mm = self.sectorFormat.search(win.get(start, end))
        if mm:
            x, y = map(int, mm.groups())
            self.cen.SetSect((x, x, y, y))
        else:
            self.Root.bell()

    #
    # Output window functions:
    #

    def displayMsgs(self):
        """Send the internal message queue to the Tk interface."""
        self.Output.setEditable(1)
        self.msgQueue[:0] = ['end']
        apply(self.Output.insert, tuple(self.msgQueue))

        # Delete any lines in excess of 1000
        self.Output.delete('1.0', 'end - 1000 lines')

        self.Output.setEditable(0)
        self.Output.see('end')
        del self.msgQueue[:]

    def Begin(self, cmd):
        """empQueue handler: Note the beginning of a command."""
        # If there are no messages on the msgQueue, then force the display
        # to output the begin line.  This should give a little better
        # feedback to the user - if it is not done, no acknowledgement of
        # the sent command is shown until the server starts sending data.
        forceOutput = not self.msgQueue

        if self.atPrompt:
            self.msgQueue[len(self.msgQueue):] = [cmd, 'command']
            self.atPrompt = 0
        else:
            self.msgQueue[len(self.msgQueue):] = [
                "\n", '',
                empDb.GetPrompt(), 'prompt',
                cmd, 'command']
        if forceOutput:
            self.displayMsgs()

    def data(self, msg):
        """empQueue handler: Process a line of server data."""
        # Check for empire display protocols.
        ochr = map(ord, msg)
        if 7 in ochr:
            # Found bell characters
            num = ochr.count(7)
            for i in range(num):
                ochr.remove(7)
                self.Root.bell()
            # Remove bell characters from input
            msg = string.join(map(chr, ochr), '')
        l = len(ochr)
        t = map(operator.and_, [128]*l, ochr)
        if 128 in t:
            # Found inverse video characters
            ochr = map(chr, map(operator.and_, [~128]*l, ochr))
            names = (('data', 128), ('inverse', 0))
            n = 0
            cont = 1
            lst = ["\n", '']
            while cont:
                try:
                    pos = t.index(names[n][1])
                except ValueError:
                    pos = len(t)
                    cont = 0
                lst[len(lst):] = [string.join(ochr, "")[:pos], names[n][0]]
                del t[:pos], ochr[:pos]
                n = n ^ 1
            self.msgQueue[len(self.msgQueue):] = lst
        else:
            self.msgQueue[len(self.msgQueue):] = [
                "\n", '', msg, 'data']
        self.atPrompt = 0

    def flush(self, msg, hdl):
        """empQueue handler: Handle a subprompt."""
        mm = self.sectorFormat.search(msg)
        if mm:
            self.markSectors([map(int, mm.groups())], 'prompt')
        self.msgQueue[len(self.msgQueue):] = [
            "\n", '', msg, 'flush']
        if hdl is not None:
            self.bufferStatus(msg, hdl, 'subprompt',
                              # Hack! Only move to subprompt when syncing
                              not self.queueStatus.burst.get())
        self.atPrompt = 2

    def Answer(self, msg):
        """empQueue handler: Note the answer to a subprompt."""
        # Check if bufferStatus is requesting a sub-prompt
        if (self.delStatus('subprompt')
            # Hack! Only beep when syncing
            and not self.queueStatus.burst.get()):
            self.Root.bell()
## 	self.delStatus('subprompt')
        if msg is not None:
            self.msgQueue[len(self.msgQueue):] = [msg, 'subcommand']
        self.atPrompt = 0

    def End(self, cmd):
        """empQueue handler: Note the end of a command."""
        p = empDb.GetPrompt()
        self.msgQueue[len(self.msgQueue):] = [
            "\n", '', p, 'prompt']
        self.markSectors([], 'prompt')
        self.setprompt(p)
        self.atPrompt = 1

    def Process(self):
        """empQueue handler: Note a lull in socket activity."""
        # Send output to screen
        if self.msgQueue:
            self.displayMsgs()

        # Update the graphical displays.
        if filter(None, empDb.updateDB.values()):
            self.redraw()

    def inform(self):
        """empQueue handler: Process an asynchronous prompt update."""
        p = empDb.GetPrompt()
        if self.atPrompt == 1:
            self.msgQueue[len(self.msgQueue):] = [
                "\n", '', p, 'prompt']
        elif self.stsList:
            # The prompt window is in use - write prompt anyway
            self.msgQueue[len(self.msgQueue):] = [
                "\n", '',
                empDb.megaDB['prompt']['inform'], 'prompt']
        self.setprompt(p)

    def flash(self, msg):
        """empQueue handler: Process an asynchronous line of data."""
        self.msgQueue[len(self.msgQueue):] = [
            "\n", '', msg, 'flash']
        self.atPrompt = 0

    def Error(self, msg):
        """empQueue handler: Process an internal error notification."""
        self.msgQueue[len(self.msgQueue):] = [
            "\n", '', msg, 'error']
        self.atPrompt = 0
        self.displayMsgs()

    #
    # Subprompt manipulators:
    #

    def setprompt(self, prompt=None):
        """Set the prompt window to the standard empire prompt."""
        if self.stsList:
            # Dont update the prompt if the status window is in use.
            return
        if prompt is None:
            prompt = empDb.GetPrompt()
        self.CmdPrompt['text'] = prompt

    def bufferStatus(self, prompt, hdl, id=None, focus=1):
        """Place a subprompt query on a queue."""
        self.stsList.append((prompt, hdl, id))
        if len(self.stsList) == 1:
            self.CmdPrompt['anchor'] = 'nw'
            self.CmdPrompt['text'] = self.stsList[0][0]
            self.Status['state'] = 'normal'
##  	    self.Status['relief'] = 'sunken'
            self.Status.delete(0, 'end')
            if focus:
                self.Status.focus()

    def DoStatus(self, event):
        """Tk callback:  Accept a subcommand, and send to calling process."""
        cmd = self.Status.get()
        hdl = self.stsList[0][1]
        self.delStatus(self.stsList[0][2])
        hdl(cmd)

    def delStatus(self, id):
        """Find a prompt request with ID and delete it."""
        for i in range(len(self.stsList)):
            if self.stsList[i][2] != id:
                continue
            del self.stsList[i]
            self.Status.delete(0, 'end')
            if self.stsList:
                self.CmdPrompt['text'] = self.stsList[0][0]
            else:
                self.Status['state'] = 'disabled'
##  		self.Status['relief'] = 'flat'
                self.CmdPrompt['anchor'] = 'ne'
                self.CmdPrompt['text'] = ""
                self.Prompt.focus()
            return 1
        return 0

    def queryCommand(self, msg, cmd, post=None, pre=None):
        """Query the user for a value; don't buffer if prompt is in-use."""
        if self.stsList:
            # Dont buffer additional commands.
            self.Root.bell()
            return
        def f(msg, self=self, cmd=cmd, pre=pre, post=post):
            """Function to be called when status window finishes."""
            if not msg:
                return
            if pre:
                self.ioq.Send(pre)
            self.ioq.Send(cmd % ((msg,)*string.count(cmd, '%s')))
            if post:
                self.ioq.Send(post)
        self.bufferStatus(msg, f)

    #
    # Login callbacks:
    #

    def startConn(self):
        """Login callback:  Establish the socket connection."""
        viewer.Root.createfilehandler(self.ioq,
                                      Tkinter.tkinter.READABLE,
                                      self.HandleSock)

    def stopConn(self):
        """Login callback:  Disengage the socket connection."""
        viewer.Root.deletefilehandler(self.ioq)

    #
    # Misc. utilities:
    #

    def transferKeys(self, win):
        """Set the window WIN to redirect keystrokes to the root window."""
        win.bind('<Key>', (lambda e:
                           (not e.char or
                            e.widget.focus_get().__class__ in (
                                MyText.MyText, Tkinter.Entry))
                           or viewer.Root.focus_lastfor().focus()
                           or viewer.Root.event_generate('<Key>',
                                                         state=e.state,
                                                         keysym=e.keysym,
                                                         keycode=e.keycode)))

    def insertText(self, txt):
        """Insert TXT into the current position in the command-line."""
        inpbox = self.Root.focus_lastfor()
        cmd = inpbox.get()
        idx = inpbox.index('insert')
        end = inpbox.index('end')
        if idx > 1 and cmd[idx-1] != ' ':
            txt = " " + txt
        if idx == end or cmd[idx] != ' ':
            txt = txt + " "
        inpbox.insert('insert', txt)

    def redraw(self, total=0):
        """DB handler: Database has changed - update the displays."""
        # Inform all subwindows of the update.
        for i in self.updateList:
            i.redraw(total)
        # Clear the update database.
        for i in filter(None, empDb.updateDB.values()):
            i.clear()

    def markSectors(self, *args):
        """Send markSectors request to all maps."""
        for i in self.mapList:
            apply(i.markSectors, args)

    def HandleSock(self, file, mask):
        """Tk file callback:  Process pending socket data."""
        self.ioq.HandleInput()

    #
    # empire.py callbacks:
    #

    def main(self):
        """empire.py callback: Start the main input/output loop."""
        # Register the Tk commands.
        self.ioq.registerCmds(OutWin.CmdWind, LoginWin.CmdLogin
                              , TeleWin.CmdWRead, MapWin.CmdMap
                              , OutWin.CmdCShow, CmdDisp, CmdSect
                              , MapWin.CmdBestpath)

        # Hack! Start the queue checking timer.
        self.queueStatus.checkQueue()

        # Enter Tk mainloop.
        self.Root.mainloop()

## 	while 1:
## 	    pending = select.select([self.ioq], [], [], .1)[0]
## 	    self.root.update()
## 	    if pending:
## 		self.HandleSock()

# # The following commands are callback functions for the EmpCmd
# # interface.  They define client-side synthetic commands that are
# # dependent on the Tk interface.

class CmdDisp(empCmd.baseCommand):
    description = "Gradually highlight specified sectors on main map."

    sendRefresh = "e"
    defaultBinding = (('Disp', 4),)

    commandUsage = ("Disp [<commodity> <sectors>"
                    " [min <min value>] [max <max value>]]")
    commandFormat = re.compile(
	r"^(?P<comm>\S+)\s+(?P<sectors>\S+)(?:\s+\?(?P<selectors>\S+))?(\s+min\s+(?P<vmin>\d+))?(\s+max\s+(?P<vmax>\d+))?\s*$|^$")
    def receive(self):
	mm = self.parameterMatch
	if not mm.group('sectors'):
	    # Disable highlighting
	    viewer.markSectors([], "disp")
	    return
	try:
	    list = empEval.getSectors(
		"owner==-1 and " + empEval.selectToExpr('SECTOR',
		    mm.group('sectors'),
		    mm.group('selectors')),
		'SECTOR')
	except empEval.error, e:
	    viewer.Error(e)
	else:
	    for i in viewer.mapList:
	    	i.Map.delete("disp");

	    try: commodity = empEval.commodityTransform[mm.group('comm')]
	    except KeyError: commodity = mm.group('comm')

            vmin = None
            vmax = None
            
            for coord in list:
		DB = empDb.megaDB['SECTOR'][coord] 
		val = DB.get(commodity, 0)
		if vmin is None or val < vmin:
		    vmin = val
                if vmax is None or val > vmax:
		    vmax = val
#            print vmin, vmax

            try:
                uvmin = int(mm.group('vmin'))
            except:
                uvmin = vmin

            try:
                uvmax = int(mm.group('vmax'))
            except:
                uvmax = vmax

            if uvmin > vmin:
                vmin = uvmin
            if uvmax < vmax:
                vmax = uvmax
                
	    if(vmin >= vmax) :
		vmax = vmin + 1

	    vmax = vmax - vmin

            for coord in list:
		DB = empDb.megaDB['SECTOR'][coord] 
		val = DB.get(commodity, 0)
		nval = max(0, min(val - vmin, vmax))
                print nval
		scale = nval * 255 / vmax
		color = "#%02x%02x00" % ( 0x80 + scale/2, scale )
		for i in viewer.mapList:
			x, y = i.getCoord(tuple(coord))
			if(val > 0) :
			    i.drawItem(x, y, "disp", "Mark", tags="disp", fill=color, outline=color)

class CmdSect(empCmd.baseCommand):
    description = "Highlight specified sectors on main map."

    sendRefresh = "e"
    defaultBinding = (('Sect', 4),)

    commandUsage = "Sect [<sectors>]"
    commandFormat = re.compile(
        r"^(?P<sectors>\S+)(?:\s+\?(?P<selectors>\S+))?\s*$|^$")
    def receive(self):
        mm = self.parameterMatch
        if not mm.group('sectors'):
            # Disable highlighting
            viewer.markSectors([], "sect")
            return
        try:
            list = empEval.getSectors(
                "owner==-1 and " + empEval.selectToExpr('SECTOR',
                    mm.group('sectors'),
                    mm.group('selectors')),
                'SECTOR')
        except empEval.error, e:
            viewer.Error(e)
        else:
            viewer.markSectors(list, "sect")

##     def CmdBurstAll(self, ioq, match, out):
## 	"""Put the Tk interface into burst mode."""
## 	if match.args == 'on':
## 	    ioq.preFlags = ioq.postFlags = empQueue.QU_BURST
## 	elif match.args == 'off':
## 	    ioq.preFlags = ioq.postFlags = empQueue.QU_SYNC
## 	    if self.atPrompt == 2:
## 		self.delStatus('subprompt')

###########################################################################
#############################  Startup	      #############################

# Open the display
Display = Tkinter.Tk(None, None, "Ptkei")
Pmw.initialise(Display)

##  bindFocus = empQueue.doNothing

# Read in options database
Display.option_readfile(empQueue.pathPrefix('TkOption'),
                        'startupFile')

# HACK!  Platform specific initialization.

if os.name == 'posix':
    # X11 initialization
    file = empQueue.pathPrefix('TkOption.x11')
    if file:
        Display.option_readfile(file, 'startupFile')
    del file

    # Hack! Set the default font for entry/listbox to be the same as the text
    # box.
    f = Tkinter.Text()
    Display.option_add("*Entry.font", f['font'], 'widgetDefault')
    Display.option_add("*Listbox.font", f['font'], 'widgetDefault')
    f.destroy()
    del f
elif os.name == 'nt':
    # Windows initialization
    file = empQueue.pathPrefix('TkOption.w32')
    if file:
        Display.option_readfile(file, 'startupFile')
    del file

##      print "PTkEI: Using Windows text selection hack."
##      def setFocus(event):
##  	event.widget.OldFocus = event.widget.focus_lastfor()
##  	event.widget.focus()

##      def unsetFocus(event):
##  	if hasattr(event.widget, 'OldFocus'):
##  	    event.widget.OldFocus.focus()
##  	    del event.widget.OldFocus

##      def bindFocus(win):
##  	win.bind('<Button-1>', setFocus)
##  	win.bind('<ButtonRelease-1>', unsetFocus)


# Handle platforms that don't support the Tcl file handler
def InitFileHandler():
    global viewer

    if Tkinter.tkinter.createfilehandler is None:
        print "PTkEI: Using emulated file handlers."
        def bogusFileHandler(file, mask, hdlr):
            global bogusFileTimer
            def hdl(file=file, mask=mask, hdlr=hdlr):
                if (file.fileno() is not None
                    and select.select([file], [], [], 0)[0]):
                    hdlr(file, mask)
                bogusFileHandler(file, mask, hdlr)
            bogusFileTimer = viewer.Root.tk.createtimerhandler(50, hdl)

        def bogusDelFileHandler(fileno):
            bogusFileTimer.deletetimerhandler()

        viewer.Root.createfilehandler = bogusFileHandler
        viewer.Root.deletefilehandler = bogusDelFileHandler
        viewer.Root.createtimerhandler = viewer.Root.tk.createtimerhandler 
    else:
        viewer.Root.createfilehandler = viewer.Root.tk.createfilehandler
        viewer.Root.deletefilehandler = viewer.Root.tk.deletefilehandler 
        viewer.Root.createtimerhandler = viewer.Root.tk.createtimerhandler 
    
    
