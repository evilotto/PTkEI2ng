"""Get host/port and country/representative information graphically."""

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
import tkMessageBox
import tkFileDialog

import string
import sys
import os
import traceback

import empDb
import empQueue
import empCmd

###########################################################################
#############################  Login window   #############################
class loginWin:
    """Get host/port and coun/rep info in a graphical manner."""
    def __init__(self):
        # Create root window
        self.Root = Tkinter.Toplevel(name="login")
        self.Root.withdraw()
        # Windows HACK!
        if os.name == 'nt':
            self.Root.transient(viewer.Root)
        self.Root.title("Empire login")
        self.Root.iconname("Empire login")
        self.Root.bind('<Return>', self.DoPlay)
        self.Root.protocol('WM_DELETE_WINDOW', self.handleDelete)

        self.Status = Tkinter.Label(self.Root, name="status", width=40,
                                    anchor='w', text="hrmm")
        self.Status.pack(side='bottom', fill='x', expand=1)

        # Allow the database to be selected.
        dbGroup = Pmw.Group(self.Root,
                            tag_text = "Database File")
        dbGroup.pack(fill='x', expand=1)
        dbframe = dbGroup.interior()
        self.FileInfo = Tkinter.Label(dbframe, name="filename",
                                      text="File:\n "+empDb.DBIO.filename,
                                      justify='left', anchor='w')
        self.FileInfo.pack(side='top', fill='x', expand=1)
        self.ResetB = Tkinter.Button(dbframe, name="reset",
                                     text="Reset", command=self.DoReset)
        self.ResetB.pack(side='right')
        self.SaveB = Tkinter.Button(dbframe, name="save",
                                      text="Save As", command=self.DoSave)
        self.SaveB.pack(side='right')
        self.LoadB = Tkinter.Button(dbframe, name="load",
                                      text="Load", command=self.DoLoad)
        self.LoadB.pack(side='right')
        self.NewB = Tkinter.Button(dbframe, name="new",
                                   text="New", command=self.DoNew)
        self.NewB.pack(side='right')

        # Create network info section.
        netGroup = Pmw.Group(self.Root,
                             tag_text = "Server Information")
##  			     tag_pyclass=Pmw.OptionMenu,
##  			     tag_labelpos='w',
##  			     tag_labelmargin=10,
##  			     tag_label_text="Server",
##  			     tag_items=("Cheetah", "Zebra", "Changeling"))
        netGroup.pack(side='top', fill='x', expand=1)
        netFrame = netGroup.interior()
        lhost = Tkinter.Label(netFrame, name="lhost",
                              anchor='w', text="Host:")
        lhost.pack(fill='x', expand=1)
        self.Host = Tkinter.Entry(netFrame, name="host")
        self.Host.pack(fill='x', expand=1)
        lport = Tkinter.Label(netFrame, name="lport",
                              anchor='w', text="Port:")
        lport.pack(fill='x', expand=1)
        self.Port = Tkinter.Entry(netFrame, name="port")
        self.Port.pack(fill='x', expand=1)
        self.DisconnectB = Tkinter.Button(netFrame, name="disconnect",
                                          text="Disconnect", state='disabled',
                                          command=self.DoDisconnect)
        self.DisconnectB.pack(anchor='e')

        # Create player info section.
        playerGroup = Pmw.Group(self.Root,
                                tag_text = "Player Information")
        playerGroup.pack(side='top', fill='x', expand=1)
        pframe = playerGroup.interior()
        lcoun = Tkinter.Label(pframe, name="lcoun",
                              anchor='w', text="Country:")
        lcoun.pack(fill='x', expand=1)
        self.Coun = Tkinter.Entry(pframe, name="coun")
        self.Coun.pack(fill='x', expand=1)
        lrep = Tkinter.Label(pframe, name="lrep",
                             anchor='w', text="Password:")
        lrep.pack(fill='x', expand=1)
        self.Rep = Tkinter.Entry(pframe, name="rep")
        self.Rep.pack(fill='x', expand=1)
        self.killV = Tkinter.StringVar()
        killCB = Tkinter.Checkbutton(pframe, name="kill", text="Kill",
                                     variable=self.killV,
                                     command=self.DoKill)
        killCB.pack(anchor='w')
        self.PlayB = Tkinter.Button(pframe, name="play",
                                    text="Play", command=self.DoPlay)
        self.PlayB.pack(anchor='e')

        self.getDBValues()

    def setDBValues(self):
        """Set the database login values from the login window."""
        port = int(self.Port.get())
        vals = {'host':self.Host.get(), 'port':port,
                'coun':self.Coun.get(),	'repr':self.Rep.get()}
        loginDb = empDb.megaDB['login']
        if (loginDb['host'] != vals['host'] or loginDb['port'] != vals['port']
            or loginDb['coun'] != vals['coun']):
            empDb.DBIO.newDatabase = 1
        loginDb.update(vals)

    def getDBValues(self):
        """Get the database login values and set them in the login window."""
        self.login_kill = 0
        ldict = empDb.megaDB["login"]
        self.Host.delete(0, 'end')
        self.Host.insert(0, ldict['host'])
        self.Port.delete(0, 'end')
        self.Port.insert(0, ldict['port'])
        self.Coun.delete(0, 'end')
        self.Coun.insert(0, ldict['coun'])
        self.Rep.delete(0, 'end')
        self.Rep.insert(0, ldict['repr'])

    def DoPlay(self, event=None):
        """Tk callback: Process Play button request."""
        try:
            self.setDBValues()
        except ValueError:
            self.Status['text'] = "Could not convert port to an integer."
            return
        self.Status['text'] = "Attempting connection.."
        self.Root.update_idletasks()
        self.loginHandler.retry()

    def DoReset(self):
        """Tk callback: Process Reset button request."""
        if not tkMessageBox.askokcancel(
            "Reset Database?",
            "This command will reset all known information."
            "  Really continue?"):
            return
        DBIO = empDb.DBIO
        DBIO.reset()
        try: self.setDBValues()
        except ValueError:
            pass
        viewer.redraw(1)

    def DoSave(self):
        """Tk callback: Process Save button request."""
        DBIO = empDb.DBIO
        newfile = tkFileDialog.SaveAs(title="Save Database",
                                      initialfile=DBIO.filename).show()
        if not newfile:
            return
        DBIO.filename = newfile
        DBIO.needSave = 1
        self.FileInfo['text'] = "File:\n " + newfile
        try:
            DBIO.save()
        except:
            empQueue.flashException()
            return

    def DoLoad(self):
        """Tk callback: Process Load button request."""
        newfile = tkFileDialog.Open(title="Load Database").show()
        if not newfile:
            return
        DBIO = empDb.DBIO
        try:
            DBIO.save()
        except:
            empQueue.flashException()
            return
        self.FileInfo['text'] = "File:\n " + newfile
        try:
            DBIO.load(newfile)
        except:
            viewer.Error("PTkEI: Encountered error while loading database.\n"
                         "PTkEI: Perhaps this is an old database?\n")
            traceback.print_exc()
            return
        self.getDBValues()
        self.Status['text'] = "Loading Database.."
        self.Root.update_idletasks()
        viewer.redraw(1)
        self.Status['text'] = ""

    def DoNew(self):
        """Tk callback: Process New button request."""
        newfile = tkFileDialog.SaveAs(title="New Database").show()
        if not newfile:
            return
        DBIO = empDb.DBIO
        try:
            DBIO.save()
        except:
            empQueue.flashException()
            return
        DBIO.filename = newfile
        self.FileInfo['text'] = "File:\n " + newfile
        DBIO.reset()
        viewer.redraw(1)

    def DoKill(self):
        """Tk callback: Process Kill button request."""
        self.login_kill = (self.killV.get() == "1")

    def DoDisconnect(self):
        """Tk callback: Process Disconnect button request."""
        # HACK++
        viewer.ioq.sock.loginParser.Disconnect()

    def handleDelete(self):
        """Tk callback: Remove the window from the display."""
        self.Root.withdraw()

    def login_error(self, msg):
        """empQueue/login handler: Report a login error."""
        self.Status['text'] = msg
        self.Root.deiconify()
        self.Root.lift()

    def login_success(self):
        """empQueue/login handler: Note a successful login."""
        self.Root.withdraw()
        self.Coun['state'] = self.Rep['state'] = \
                             self.PlayB['state'] = \
                             self.LoadB['state'] = self.SaveB['state'] = \
                             self.NewB['state'] = self.ResetB['state'] = \
                             'disabled'
        self.login_kill = 0
        self.killV.set("0")

    def connect_success(self):
        """empQueue/login handler: Note a server connection."""
        viewer.startConn()
        self.Host['state'] = self.Port['state'] = 'disabled'
        self.DisconnectB['state'] = 'normal'

    def connect_terminate(self):
        """empQueue/login handler: Note a server disconnect."""
        self.Host['state'] = self.Port['state'] = \
                             self.Coun['state'] = self.Rep['state'] = \
                             self.PlayB['state'] = \
                             self.LoadB['state'] = self.SaveB['state'] = \
                             self.NewB['state'] = self.ResetB['state'] = \
                             'normal'
        self.DisconnectB['state'] = 'disabled'
        viewer.stopConn()

class CmdLogin(empCmd.baseCommand):
    description = "Re-open the login window."

    defaultBinding = (('Login', 5),)

    def invoke(self):
        viewer.loginCallback.login_error("")


###########################################################################
#############################  Queue Menu     #############################
class QueueStatus:
    def __init__(self, root):
        # Create the queue status menubutton
        self.queueStatus = Tkinter.StringVar()
        self.queueStatus.set("Starting")
        menubutton = Tkinter.Menubutton(viewer.Root, name="socket",
                                        textvariable=self.queueStatus,
                                        width=20,
                                        relief="sunken")
        try:
            # Tk 8.0 option
            menubutton['direction'] = 'above'
        except Tkinter.TclError:
            pass
        menubutton.pack(in_=root, fill='both', side='right')
        viewer.Balloon.bind(menubutton, "Queue status\n"
                            +"Click for Queue Menu")

        # Create the queue status menu
        menu = Tkinter.Menu(menubutton, name="queueMenu",
                            tearoffcommand=self.DoTearoff)
        menu.add_command(label='Clear Queue', command=self.DoClearQueue)
        self.paused = Tkinter.IntVar()
        self.paused.set(0)
        menu.add_checkbutton(label='Pause Queue',
                             command=self.DoSetPause,
                             variable=self.paused, onvalue=1, offvalue=0)
        menu.add_separator()
        self.raw = Tkinter.IntVar()
        self.raw.set(0)
        menu.add_checkbutton(label='Raw Mode',
                             command=self.DoSetRaw,
                             variable=self.raw, onvalue=1, offvalue=0)
        menu.add_separator()

        self.burst = Tkinter.IntVar()
        self.burst.set(0)
##  	menu.add_radiobutton(label='Burst Mode',
##  			     command=self.DoSetBurst,
##  			     variable=self.burst, value=1)
##  	menu.add_radiobutton(label='Synchronous Mode',
##  			     command=self.DoSetBurst,
##  			     variable=self.burst, value=2)
        menu.add_checkbutton(label='Burst Mode',
                             command=self.DoSetBurst,
                             variable=self.burst, onvalue=1, offvalue=0)
        menubutton['menu']=menu

        # Create the update countdown timer
        self.updateStatus = Tkinter.StringVar()
        self.updateStatus.set("--:--:--")
        updateS = Tkinter.Label(viewer.Root, name="countdown",
                                textvariable=self.updateStatus, width=10,
                                relief="sunken"
                                )
        updateS.pack(in_=root, fill='both', side='right')
        self.lasttime = (None, None, None)
        viewer.Balloon.bind(updateS, "Time until next update")

    def checkQueue(self):
        """Tk timer callback:  Show the queue status."""
        viewer.Root.createtimerhandler(500, self.checkQueue)
        newtime = empDb.megaDB['time'].getCountDown()
        if newtime != self.lasttime:
            hours, minutes, seconds = newtime
            if hours is None:
                self.lasttime = (None, None, None)
                self.updateStatus.set("--:--:--")
            else:
                lasthours, lastminutes, lastseconds = self.lasttime
                if (lasthours is None or minutes < 5 or seconds == 0
                    or minutes > lastminutes or minutes < lastminutes-1
                    or (minutes != lastminutes and lastseconds != 0)
                    or hours != lasthours):
                    self.lasttime = tuple(map(int, newtime))
                    self.updateStatus.set("%d:%02d:%02d" % newtime)

        ioq = viewer.ioq
        flags = ioq.sock.flags
        self.paused.set(flags in (empQueue.QU_PAUSED, empQueue.QU_DISCONNECT))

        status = ioq.sock.GetStatusMsg()

        raw = (ioq.raw != 0)
        self.raw.set(raw)
        if raw:
            status = "Raw "+status
        burst = (ioq.preFlag == empQueue.QU_BURST)
        self.burst.set(burst)
        if burst:
            status = "Burst "+status

        self.queueStatus.set(status)

    def DoSetRaw(self):
        viewer.ioq.raw = (self.raw.get() == 1)

    def DoSetBurst(self):
        ioq = viewer.ioq
        if self.burst.get() == 1:
            ioq.preFlag = ioq.postFlag = empQueue.QU_BURST
        else:
            ioq.preFlag = ioq.postFlag = empQueue.QU_SYNC

    def DoSetPause(self):
        viewer.ioq.sock.pauseQueue(self.paused.get() == 1)

    def DoClearQueue(self):
        viewer.ioq.sock.clearQueue()

    def DoTearoff(self, queueMenu, newWin):
        # Hrmm.  Tkinter doesn't seem to support this fully.
        viewer.Root.tk.call("wm", "title", newWin, "Queue Options")
        viewer.Root.tk.call("wm", "iconname", newWin, "Queue Options")
