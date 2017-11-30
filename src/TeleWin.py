"""Graphical telegram/announcment tool."""

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

import re
import string
import types

import Tkinter
import Pmw

import Tk_List
import MyText
import empQueue
import empDb
import empParse
import empCmd

###########################################################################
#############################  Telegrams      #############################
class teleWin:
    """Handle communications in a graphical manner."""
    def __init__(self):
        title = "Empire Correspondence"
        # Create root window
        self.Root = Tkinter.Toplevel(name="telegram")
        self.Root.withdraw()
        self.Root.title(title)
        self.Root.iconname(title)

        # Forward key events to main window.
        viewer.transferKeys(self.Root)

        # TCL variables
        self.type = Tkinter.StringVar()
        self.type.set('telegrams')

        # Create options bar
        oframe = Tkinter.Frame(self.Root, name="oframe")
        oframe.pack(side='bottom', fill='x', expand=1)
        orframe = Tkinter.Frame(oframe, name="orframe")
        orframe.pack(side='left', fill='y', expand=1)
        self.AnnoB = Tkinter.Radiobutton(
            orframe, name="anno", text="Announcements",
            anchor='w', variable=self.type,
            value='announcements',
            command=self.redraw)
        self.AnnoB.pack(fill='both', expand=1)
        self.TeleB = Tkinter.Radiobutton(
            orframe, name="tele", text="Telegrams",
            anchor='w',
            variable=self.type, value='telegrams',
            command=self.redraw)
        self.TeleB.pack(fill='both', expand=1)
        self.SendB = Tkinter.Button(
            oframe, name="send",
            text="Send", command=self.DoSend)
        self.SendB.pack(side='left', fill='y', expand=1)
        self.AbortB = Tkinter.Button(
            oframe, name="abort",
            text="Abort", command=self.DoAbort,
            state='disabled')
        self.AbortB.pack(side='left', fill='y', expand=1)
        self.ReplyB = Tkinter.Button(
            oframe, name="reply",
            text="Reply", command=self.DoReply)
        self.ReplyB.pack(side='left', fill='y', expand=1)
        self.RemoveB = Tkinter.Button(
            oframe, name="delete",
            text="Delete", command=self.DoRemove)
        self.RemoveB.pack(side='left', fill='y', expand=1)

        # Create search box
        self.SearchMsg = Tkinter.StringVar()
        self.StringRE = Tkinter.StringVar()
        self.TypeRE = Tkinter.IntVar()
        self.TypeRE.set(0)
        sframe = Tkinter.Frame(self.Root, name="sframe")
        sframe.pack(side='top', fill='both', expand=1)
        srframe = Tkinter.Frame(sframe, name="srframe")
        srframe.pack(side='right')
        hsearch = Tkinter.Radiobutton(srframe, name="headerSearch",
                                      text="Header Search", anchor='w',
                                      variable=self.TypeRE, value=0)
        hsearch.pack(fill='both', expand=1)
        viewer.Balloon.bind(hsearch, "Search only the first\n"
                            +"line of text")
        fsearch = Tkinter.Radiobutton(srframe, name="fullSearch",
                                      text="Full Search", anchor='w',
                                      variable=self.TypeRE, value=1)
        fsearch.pack(fill='both', expand=1)
        viewer.Balloon.bind(fsearch, "Search the entire message")
        listall = Tkinter.Button(sframe, name="listAll",
                                 command=self.DoListAll, text="List All")
        listall.pack(side='right')
        viewer.Balloon.bind(listall, "Undo a previous search")
        search = Tkinter.Button(sframe, name="search",
                                command=self.DoSearch, text="Search")
        search.pack(side='right')
        viewer.Balloon.bind(search, "Search for string")
        Tkinter.Label(sframe, name="slabel",
                      textvariable=self.SearchMsg,
                      anchor='sw'
                      ).pack(side='top', fill='x', expand=1)
        searchRE = Tkinter.Entry(sframe, name="regexp",
                                 textvariable=self.StringRE)
        searchRE.pack(side='top', fill='x', expand=1)
        viewer.Balloon.bind(searchRE, "Click to enter a search string")

        # Create list box
        lframe = Tkinter.Frame(self.Root, name="lframe")
        lframe.pack(side='top', fill='both', expand=1)
        scrollY = Tkinter.Scrollbar(lframe, name="scrollY")
        scrollY.pack(side='right', fill='y')
        self.List = Tk_List.MyListbox(lframe, name="list",
                                      height=8, selectmode='extended',
                                      command=self.SetMsg,
                                      yscrollcommand=scrollY.set)
        self.List.pack(side='left', fill='both', expand=1)
        scrollY['command'] = self.List.yview

        # Create text box and scrollbar
        scrollY = Tkinter.Scrollbar(self.Root, name="scrollY")
        scrollY.pack(side='right', anchor='e', fill='y')
        self.Text = MyText.MyText(self.Root, name="text",
                                  yscrollcommand=scrollY.set)
        self.Text.setEditable(0)
        self.Text.pack(side='left', anchor='w', expand=1, fill='both')
        scrollY['command'] = self.Text.yview
        self.Text.bind('<Button-3>', viewer.DoLocateSector)

        # Draw
        self.DoListAll()

        # Create a special country input box
        self.CInput = Pmw.ComboBoxDialog(viewer.Root,
                                         title = "Country Selection",
                                         buttons = ("OK", "Cancel"),
                                         defaultbutton = "OK",
                                         combobox_labelpos = 'n',
                                         label_text= "Select Country:")
        self.CInput.withdraw()

        # Register automatic updating
        viewer.updateList.append(self)
        self.Root.protocol('WM_DELETE_WINDOW', self.handleDelete)

    def handleDelete(self):
        """Tk callback: Remove the window from the display."""
        self.Root.withdraw()

    def mapWindow(self):
        """Force window to display."""
        self.Root.deiconify()
        self.Root.lift()

    def SetMsg(self, msg):
        """Tk/Listbox callback: Note a change in current message."""
        if self.Text.editable:
            return
        self.Text.setEditable(1)
        self.Text.delete('1.0', 'end')
        printTime = empDb.megaDB['time'].printTime
        getName = empDb.megaDB['countries'].getName
        for i in msg:
            if type(i[0]) == types.TupleType:
                hdr = "> %s%s  dated %s\n" % (
                    i[0][0],
                    (i[0][1] is not None
                     and " from %s"%getName(i[0][1]) or ""),
                    printTime(i[0][2]))
            else:
                hdr = i[0]+"\n"
            self.Text.insert('end', hdr)
            for j in i[1:]:
                self.Text.insert('end', str(j)+"\n")
        self.Text.setEditable(0)

    def redraw(self, total=1):
        """DB update handler:  Redraw the window."""
        if total or empDb.updateDB['time']:
            sts = self.List.getStatus()
            self.List.delete()
            db = empDb.megaDB[self.type.get()]['list']
        else:
            db = empDb.updateDB[self.type.get()].get('list', [])
        printTime = empDb.megaDB['time'].printTime
        getName = empDb.megaDB['countries'].getName
        compRE = self.compRE
        fullSearch = self.TypeRE.get()
        for i in db:
            hdr = i[0]
            if type(hdr) == types.TupleType:
                hdr = "> %-40s %s" % (
                    (hdr[1] is not None
                     and "%s from %s"%(hdr[0], getName(hdr[1]))
                     or hdr[0]),
                    printTime(hdr[2]))
            # Check if it matches the regular expression
            if compRE is not None and not compRE.search(hdr):
                if not fullSearch:
                    continue
                for j in i[1:]:
                    if compRE.search(j):
                        break
                else:
                    # Match not found
                    continue
            self.List.insert(0, (hdr, i))
        if total:
            apply(self.List.setStatus, sts)
## 	else:
## 	    self.List.see('end')

    def DoSearch(self):
        """Tk callback: Process Search button request."""
        try:
            self.compRE = re.compile(self.StringRE.get())
        except re.error, e:
            self.SearchMsg.set("Regular Expression Error: %s" % e[0])
            self.Root.bell()
        else:
            self.redraw(1)
##  	    viewer.grabFocus()
            self.Root.focus()

    def DoListAll(self):
        """Tk callback: Process ListAll button request."""
        self.compRE = None
        self.SearchMsg.set("Regular Expression Search:")
        self.redraw(1)
##  	viewer.grabFocus()
        self.Root.focus()

    teleMatch = re.compile("(?P<num>\d+)")
    def DoSend(self):
        """Tk callback: Process Send button request."""
        if self.Text.editable:
            # Sending after a reply button.
            self.Text.setEditable(0)
            self.AbortB['state'] = 'disabled'
            self.ReplyB['state'] = self.RemoveB['state'] = \
                                   self.AnnoB['state'] = \
                                   self.TeleB['state'] = 'normal'
            empCmd.sendTelegram(self.sendCmd, self.Text.get('1.0', 'end'))
##  	    viewer.ioq.Send(self.sendCmd, telegramParser(
##  		self.sendCmd, self.Text.get('1.0', 'end')))
            del self.sendCmd
##  	    viewer.grabFocus()
            self.Root.focus()
            self.SetMsg(self.List.curselection())
            return
        # Sending a new message
        if self.type.get() == 'announcements':
            self.sendCmd = "anno"
        else:
            self.CInput.component('scrolledlist').setlist(
                empDb.megaDB['countries'].getList())
            result = self.CInput.activate()
            if result != "OK":
                return
            who = self.CInput.get()
            mm = self.teleMatch.match(who)
            if mm is not None:
                who = mm.group('num')
            self.sendCmd = "tele " + who
        self.ReplyB['state'] = self.RemoveB['state'] = \
                               self.AnnoB['state'] = \
                               self.TeleB['state'] = 'disabled'
        self.Text.setEditable(1)
        self.AbortB['state'] = 'normal'
        self.Text.delete('0.0', 'end')
        self.Text.focus()

    def DoAbort(self):
        """Tk callback: Process Abort button request."""
        self.Text.setEditable(0)
        self.AbortB['state'] = 'disabled'
        self.ReplyB['state'] = self.RemoveB['state'] = \
                               self.AnnoB['state'] = \
                               self.TeleB['state'] = 'normal'
        del self.sendCmd
##  	viewer.grabFocus()
        self.Root.focus()
        self.SetMsg(self.List.curselection())

    def DoReply(self):
        """Tk callback: Process Reply button request."""
        which = self.List.curselection()
        if not which or len(which) > 1:
            self.Root.bell()
            return
        if self.type.get() == 'announcements':
            self.sendCmd = "anno"
        else:
            if (not type(which[0][0]) == types.TupleType
                or which[0][0][1] is None):
                self.Root.bell()
                return
            self.sendCmd = "tele " + str(
                empDb.megaDB['countries'].getId(which[0][0][1]))
        self.ReplyB['state'] = self.RemoveB['state'] = \
                               self.AnnoB['state'] = \
                               self.TeleB['state'] = 'disabled'
        self.Text.setEditable(1)
        self.AbortB['state'] = 'normal'
        for i in range(len(which[0])):
            self.Text.insert("%s.0"%(i+1), " >")
        self.Text.focus()
##	self.List['state'] = 'disabled'

    def DoRemove(self):
        """Tk callback: Process Delete button request."""
        which = self.List.curselection()
        self.List.delete(which)
        for i in which:
            empDb.megaDB[self.type.get()]['list'].remove(i)

class CmdWRead(empCmd.baseCommand):

    description = "Open the telegram window."

    defaultBinding = (('wread', 5),)

    def invoke(self):
        viewer.telegramWindow.mapWindow()
