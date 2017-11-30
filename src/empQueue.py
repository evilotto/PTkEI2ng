"""Code to start and maintain empire connection"""

# version 1.1.1
#    Copyright (C) 1998-1999 Kevin O'Connor
#    Copyright (C) 2013 William Fittge
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

#import readline
import sys
import socket
import errno
import select
import string
import re
import traceback

import empDb
import empParse

# Key Ideas:


# What is contained within this file:

# This file contains the underlying socket code.  Code to handle all the
# incoming data and broker all the outgoing data is contained within the
# class EmpIOQueue.  EmpIOQueue uses a number of other classes to handle
# the incoming/outgoing data.  This file also contains these other classes
# and contains the basic building block for the chained display classes.  A
# quick glance at the other files in this distribution will show that this
# is the only file that references any of the low-level empire protocols
# (EG. C_PROMPT) - all that protocol stuff is handled here.

# Note: To actually send commands, the standard method is to use the class
# empCmd.EmpParse.  Please see the documentation in empCmd for more info.


# Global variables:

# empQueue : This always points to the only instance of EmpIOQueue.  Its a
# convenience aid that probably isn't necessary..
#
# NormalHandler.msgQueue : Stores messages that the client thinks may be
# server broadcasts (EG. new telgram notifications).  It could just as
# easily be non-global - it's global for optimization/simplicity.


# The purpose of the low-level data managers:

# The "data managers" are helper classes for EmpIOQueue.  These helper
# classes essentially manage output from the server.  They strip the
# low-level empire protocol stuff from the information and transmit the
# data using a variety of classes and methods.  The classes AsyncHandler,
# LoginHandler, and NormalHandler, are these "data managers".  It is
# important to note that AsyncHandler and LoginHandler have special
# properties.  Both of these classes will normally have exactly one
# instance associated with them.  These single instances are associated
# with EmpIOQueue at its instantiation, and are stored in the variables
# defParse and loginParser.  To the contrary, the NormalHandler class will
# generally have multiple instances associated with them - one instance per
# queued command.


# The purpose of the chained display classes:

# Associated with many of the server commands will be client parsers.  (For
# example, the server command "read" will be transmitted to the class
# empDb.ParseRead.)  These classes are referred to as "chained" because
# they generally form a linked-list of parsers.  More than one parser might
# have interest in the server output of any given command, so a chain is
# formed where each low-level parser transmits the information to the next
# parser.  The chaining is performed by the individual parsers - a lower
# level parser might decide to not send information up the chain, thus
# hiding info.  (Which, BTW, is the basis for the "null" command - "null"
# just associates the given command with a parser that discards its input.)
# At the highest level of this parse chain, is generally the main viewer.
# The global variable viewer must support the same methods of an ordinary
# display class.  (In addition to its special methods - see
# AsyncHandler/LoginHandler for more info.)


# The use of the Queue Flags:

# The queue flags describe the current state of the command queue.  They
# determine if the connection is open/closed/paused/etc..  The more
# interesting flags, however, are the per-command transmission flags.
# These flags (QU_BURST, QU_SYNC, QU_FORCEBURST, and QU_FULLSYNC) determine
# how each command is transmitted to the server.  If empQueue.flags is set
# to one of these per-command flags, that means the connection is open,
# stable, and ready to send a command in accordance with these per-command
# flags.  empQueue.flags is set by bitwise or'ing a command's pre-flags
# with the previous command's post-flags.  The pre-flags are used to
# determine when a command should be transmitted.  The post-flags determine
# the command's environment (IE. should it secure its potential
# sub-prompts, does it need to prevent further commands from being executed
# while processing the current, etc.)  If there are zero or one commands on
# the queue, then empQueue.flags will always equal QU_BURST.

# With QU_BURST, the command is transmitted immediately; no checks are made
# to determine if the command will be sent to a sub-prompt or a command
# line.

# With QU_SYNC (the most interesting and complex mode), the command is
# guaranteed to be sent to a command-line, but can be sent prior to the
# completed processing of the previous command.  This is done by forcing
# the socket reader to pre-scan all the server data.  When a C_PROMPT
# protocol is detected, the socket reader will transmit the next command
# immediately.  This pre-scanning of the server data can significantly
# reduce the connection's latency.  (Certain commands can cause a Tk
# redraw, which may take several seconds - by sending the next command
# prior to trudging through the chained display classes, it is possible to
# keep the server busy while the client works on other processing.)

# QU_FORCEBURST is a modification of QU_BURST and QU_SYNC.  QU_FORCEBURST
# is a pledge that the command will not create any subprompts.  This is
# used by the rdb command to force QU_SYNC commands following a 'dump *' to
# downgrade to QU_BURST.  Since a 'dump *' will never create a subprompt,
# this squeezes a little more performance from the frequently used rdb
# commands.

# With QU_FULLSYNC, the command is not sent until the previous command is
# fully processed, completed, and dequeued.  This is used by smart commands
# that require either the output in entirety from the previous command or
# the ability to send commands to the server immediately.  (For example,
# the client-command 'foreach' would set QU_FULLSYNC to ensure that it can
# place a command on the queue right after it is completed - it would not
# be ideal to have a command following 'foreach xxx' pop in front of the
# foreach commands due to QU_SYNC's behavior.)


# Empire Protocol IDs
C_CMDOK	 = "0"
C_DATA	 = "1"
C_INIT	 = "2"
C_EXIT	 = "3"
C_FLUSH	 = "4"
C_NOECHO = "5"
C_PROMPT = "6"
C_ABORT	 = "7"
C_REDIR	 = "8"
C_PIPE	 = "9"
C_CMDERR = "a"
C_BADCMD = "b"
C_EXECUTE= "c"
C_FLASH	 = "d"
C_INFORM = "e"
C_LAST	 = "e"

C_ASYNCS = (C_INFORM, C_FLASH)

# Queue flags
QU_BURST = 0
QU_SYNC = 1
QU_FORCEBURST = 3
QU_FULLSYNC = 7

QU_CONNECTING = 32
QU_PAUSED = 40
QU_LOGIN = 48
QU_DISCONNECT = 64
QU_OFFLINE = 72

QU_BURSTS = (QU_BURST, QU_FORCEBURST)

class EmpIOQueue:
    """Broker all input and output to/from server.

    This class generally has only one instance associated with it.  It is
    used mainly as a code/data container.
    """

    def __init__(self, async, login):
        global empQueue
        empQueue = self

        # Storage area for partial socket reads.  (Reads that contain a
        # string that is not terminated by a newline.)  This info has to be
        # stored somewhere until the next read reveals the trailing
        # information.
        self.InpBuf = ""

        # Storage for the command queue.  Each command is queued by
        # associating it with a "data manager" class (eg, NormalHandler),
        # and placing it in the queue stored in FuncList.  The integers
        # FLWaitLev and FLSentLev are indexes into this queue.
        # FuncList[FLWaitLev] points to the command that is currently
        # receiving data.  FuncList[FLSentLev] points to the next command
        # that needs to be sent to the server.
        self.FuncList = []
        self.FLWaitLev = self.FLSentLev = 0

        # Special data manager classes.  defParser (which is associated
        # with the class AsyncHandler) is used for all asynchronous data -
        # data that is received when there are exactly zero commands
        # waiting on the queue.  loginParser (which is associated with the
        # class LoginHandler) is used when the queue needs to reestablish a
        # server connection.
        self.defParser = async
        self.loginParser = login

        self.flags = QU_OFFLINE

    def SendNow(self, cmd):
        """Immediately send CMD to socket."""
        # Paranoia check
        if string.find(cmd, "\n") != -1:
            # Ugh, there should be no newlines in the cmd
            viewer.Error("Send error - embedded newline: " + `cmd`)
            cmd = cmd[:string.find(cmd, "\n")]
##  	self.debug(cmd, 'send')
        try:
            self.socket.send(cmd+"\n")
        except socket.error, e:
            self.loginParser.Disconnect()
            viewer.Error("Socket write error: " + str(e))
        except UnicodeError, e:
	    viewer.Error("Socket write error: " + str(e))
            self.socket.send("\n")
    def debug(*args):
        pass
    # To enable debugging, rename this function to debug.
    def debugXX(self, msg, type=None):
        if type == 'send':
            print "## %s" % msg
        elif type == 'get':
            print "-- %s" % msg
        else:
            print "%-30s @ len:%-2d wait:%-2d sent:%-2d flags:%-2d" % (
                msg, len(self.FuncList), self.FLWaitLev,
                self.FLSentLev, self.flags)

    def doFlags(self):
        """Set the queue flags depending on the current state of the queue."""
        if self.flags >= QU_CONNECTING:
            return
        ls = self.FLSentLev
        if len(self.FuncList) == ls or ls == 0:
            self.flags = QU_BURST
        else:
            self.flags = (self.FuncList[ls-1].postFlags
                          | self.FuncList[ls].preFlags)
##  	self.debug("Leave doflags")

    def sendCommand(self):
        """Send a command to the server."""
        while 1:
            qElem = self.FuncList[self.FLSentLev]
            # Check for dynamic command-string manipulator
            if qElem.sending is not None:
                qElem.sending()
            # Send command
            cmd = qElem.command
            if cmd is None:
                self.FLWaitLev = self.FLWaitLev + 1
            else:
                self.SendNow(cmd)
            self.FLSentLev = self.FLSentLev + 1
            # HACK++
            if (cmd is not None
                and self.FuncList[0].__class__ is NormalHandler
                and self.FuncList[0].atSubPrompt):
                # This command was sent to a known sub-prompt. Checking
                # this here totally defies a good OO design!
                self.FLSentLev = self.FLSentLev - 1
                del self.FuncList[self.FLSentLev]
                self.FuncList[0].atSubPrompt = 0
                self.FuncList[0].out.Answer(cmd)
            # Update flags
            self.doFlags()
            if (self.flags not in QU_BURSTS
                or self.FLSentLev >= len(self.FuncList)):
                break

    def beginParser(self):
        while 1:
            if (self.FLSentLev == 0 and self.flags <= QU_FULLSYNC):
##  		self.debug("Planned send")
                self.sendCommand()
            # Send parser start signal
##  	    self.debug("Parser start")
            try: self.FuncList[0].start()
            except: flashException()
            if self.FuncList[0].command is not None:
                break
            # Dummy command - remove it and try again
            del self.FuncList[0]
            self.FLWaitLev = self.FLWaitLev - 1
            self.FLSentLev = self.FLSentLev - 1
            if not self.FuncList:
                break

    def offlineSendCommand(self):
        """Handle commands on queue when off-line."""
        while 1:
            qElem = self.FuncList[0]
            # Check for dynamic command-string manipulator
            if qElem.sending is not None:
                qElem.sending()
            # Send command
            cmd = qElem.command
            if cmd is not None:
                self.loginParser.Connect()
                return
            self.FLWaitLev = self.FLWaitLev + 1
            self.FLSentLev = self.FLSentLev + 1
            # Send parser start signal
            try: self.FuncList[0].start()
            except: flashException()
            # Dummy command - remove it and try again
            del self.FuncList[0]
            self.FLWaitLev = self.FLWaitLev - 1
            self.FLSentLev = self.FLSentLev - 1
            if not self.FuncList:
                # Create dummy lull signal.
                try: self.defParser.lull()
                except: flashException()
                break

    def popHandler(self, pos):
        """Forcibly remove a command from the queue."""
        if pos < self.FLSentLev:
            self.FLSentLev = self.FLSentLev - 1
##  	self.debug("force delete @ %s : '%s'"
##  		   % (pos, self.FuncList[pos].command))
        del self.FuncList[pos]
        if pos == self.FLSentLev:
            self.doFlags()
            if (self.FLSentLev < len(self.FuncList)
                and (self.flags in QU_BURSTS
                     or (self.flags == QU_SYNC
                         and self.FLWaitLev == self.FLSentLev))):
                self.sendCommand()

    def AddHandler(self, handler, pos=None):
        """Add a command to the output queue.

        Normally, this will add a command to the end of the queue.
        However, it is possible to customize the location for the command
        via the pos argument.
        """
        l = len(self.FuncList)
        FLSentLev = self.FLSentLev
        if pos is None or pos > l:
            pos = l
        elif pos < FLSentLev:
            pos = FLSentLev
        self.FuncList.insert(pos, handler)
##  	self.debug("Add '%s'" % handler.command)
        if pos == self.FLSentLev:
            self.doFlags()
            if (self.flags == QU_OFFLINE):
                self.offlineSendCommand()
            elif (self.flags in QU_BURSTS
                  or (self.flags == QU_SYNC
                      and self.FLWaitLev == self.FLSentLev)):
##  		self.debug("Force send")
                self.sendCommand()
                if not pos:
                    self.beginParser()
                    if not self.FuncList:
                        # Was a dummy command - create dummy lull signal.
                        try: self.defParser.lull()
                        except: flashException()

    def HandleInput(self):
        """Parse input from socket; send all data to function list.

        This method does all the actual reading of the socket.  It reads
        and stores the server information, and delegates complete lines of
        data to the data-managers.  It also checks for the special sequence
        C_PROMPT which always indicates the end of a command.

        This method is made significantly more complex because of the
        heterogeneous mixture of command priorities.  Tracking of
        FLWaitLev, and FLSentLev is an arduous task.
        """
        cache = []
        error = ""
        # HACK!  Obscure python optimization - make local copies of global
        # variables.
        __C_PROMPT = C_PROMPT; __QU_SYNC = QU_SYNC
        __QU_FULLSYNC = QU_FULLSYNC; __QU_DISCONNECT = QU_DISCONNECT
        __len = len; __None = None; select__select = select.select
        string__count = string.count; string__split = string.split
        self__InpBuf = self.InpBuf; self__FuncList = self.FuncList
        self__sendCommand = self.sendCommand; self__socket = self.socket
        self__socket__recv = self.socket.recv
        # Dummy exception - used for unusual flow control
        class StopRead(Exception):
            def __init__(self, value):
                self.value = value
            def __str__(self):
                return repr(self.value)
        StopReading = "Internal Break"
        while 1:
            # Make sure socket is available and readable.
            if self.flags >= __QU_DISCONNECT:
                # Socket disconnected sometime during the cycle
                # Remove all sent items from the queue
                del self__FuncList[:self.FLSentLev]
                self.FLSentLev = self.FLWaitLev = 0
                if error:
                    # It was an error - send error to login code
                    self.loginParser.Error(error)
                elif self__FuncList and self.flags == QU_OFFLINE:
                    self.offlineSendCommand()
                break
            try:
                # Begin unconventional flow control.
                # StopRead is used here to "break out" of the read if any
                # of the socket conditions are "bad".  It is possible to do
                # this more conventionally, but I find it "ugly", and less
                # intuitive.
                sts = select__select([self__socket], [], [self__socket], 0)
                if sts[2]:
                    error = "Exceptional condition on socket!"
                    self.loginParser.Disconnect()
                    raise StopRead(StopReading)
                if not sts[0]:
                    # Nothing left to read
                    if not cache:
                        # cache is empty - break from main loop and return.
                        break
                    # There is info on the cache, process it first.
                    raise StopRead(StopReading)
                # Socket is Ok to read - now read a large block.
                try:
                    tmp = self__socket__recv(4096)
                except socket.error, e:
                    error = "Socket read exception: " + str(e)
                    self.loginParser.Disconnect()
                    raise StopRead
                if not tmp:
                    # Ughh.
                    error = "Zero read on socket!"
                    self.loginParser.Disconnect()
                    raise StopRead
                # If a prompt is encountered anywhere in the buffered data,
                # send the next command immediately in QU_SYNC mode.
                cnt = string__count(tmp, "\n"+__C_PROMPT)
                if not self__InpBuf and tmp[:1] == __C_PROMPT:
                    cnt = cnt + 1
                self.FLWaitLev = self.FLWaitLev + cnt
                if (self.flags == __QU_SYNC
                    and self.FLWaitLev == self.FLSentLev):
##  		    self.debug("Pre-send")
                    self__sendCommand()
                # Convert input to line cache
                l = __len(cache)
                cache[l:] = string__split(tmp, "\n")
                cache[l] = self__InpBuf + cache[l]
                self__InpBuf = cache[-1]
                del cache[-1]
            except StopRead:
                # End of unconventional flow control.  If StopRead is
                # raised, process what is on the cache.  (If the socket was
                # closed, we are guaranteed to exit at the start of the
                # next loop, because the queue flags are checked there.)
                pass

            while cache:
                data = cache[0]
                del cache[0]
##                 self.debug(data, 'get')

                if not self__FuncList:
                    # Asynchronous line of data
                    try: self.defParser.line(data)
                    except: flashException()
                    continue
                # call the handler
                try: self__FuncList[0].line(data)
                except: flashException()
                # Check for prompt
                if data[:1] == __C_PROMPT:
                    del self__FuncList[0]
                    self.FLWaitLev = self.FLWaitLev - 1
                    self.FLSentLev = self.FLSentLev - 1
##  		    self.debug("removed")
                    if self__FuncList:
                        self.beginParser()
                # In QU_SYNC mode, the socket is checked for new data at
                # the end of every line of data processed.  This may cause
                # some overhead, but generally network response time is
                # significantly more important than cpu time.
                if self.flags == __QU_SYNC:
                    break
        # Processing has ended.	 Copy local variables back to their originals.
        self.InpBuf = self__InpBuf

        # Signal handlers of the lull in data.
        if not self__FuncList:
            # No parsers.
            try: self.defParser.lull()
            except: flashException()
        else:
            try: self__FuncList[0].lull()
            except: flashException()

    def fileno(self):
        """Return the socket descriptor."""
        if self.flags >= QU_DISCONNECT:
            return None
        return self.socket.fileno()

    def GetStatusMsg(self):
        """Return a string that describes the current queue."""
        msg = ""
        if self.flags >= QU_CONNECTING:
            msg = {QU_DISCONNECT:"Disconnected",
                   QU_OFFLINE:"Off-line",
                   QU_CONNECTING:"Connecting",
                   QU_PAUSED:"Paused",
                   QU_LOGIN:"Logging in",
                   }[self.flags]
        tot = len(self.FuncList)
        sent = self.FLSentLev
        if tot != 0: msg = msg + " " + str(tot)
        if sent != 0: msg = msg + "/" + str(sent)
        if msg == "": msg = "Idle"
        return msg

    def clearQueue(self):
        """Permanently delete all commands that have not been sent."""
        del self.FuncList[self.FLSentLev:]
        if self.flags < QU_CONNECTING:
            self.flags = QU_BURST

    def pauseQueue(self, pause):
        """Pause/unpause all further outgoing commands."""
        if pause:
            # Pause the connection
            if self.flags < QU_CONNECTING:
                self.flags = QU_PAUSED
            elif self.flags == QU_OFFLINE:
                self.flags = QU_DISCONNECT
        else:
            # Restart a paused connection
            if self.flags == QU_PAUSED:
                self.flags = QU_BURST
                self.doFlags()
                if (self.FLSentLev < len(self.FuncList)
                    and (self.flags in QU_BURSTS
                         or (self.flags == QU_SYNC
                             and self.FLWaitLev == self.FLSentLev))):
                    self.sendCommand()
                    if not self.FLSentLev:
                        self.beginParser()
            elif self.flags == QU_DISCONNECT:
                self.flags = QU_OFFLINE
                if self.FuncList:
                    self.offlineSendCommand()

    def scanQueue(self, callback, start=0, end=None):
        """Execute a callback function on each element in the queue."""
        l = len(self.FuncList)
        if end is None or end > l:
            end = l

        for i in self.FuncList[start:end]:
            ret = callback(i)
            if ret:
                return ret

class LoginHandler:
    """Aid EmpIOQueue with all login/logout requests.

    This class requires the global viewer class to contain the class
    viewer.loginHandler.  The class viewer.loginHandler must contain the
    following methods/objects:
    login_error(), login_success(), connect_success(), connect_terminate(),
    and login_kill
    """

    def __init__(self, callback, username):
        self.callback = callback
        callback.loginHandler = self
        self.firstConnect = 1
        self.srcStart = 1
        self.username = username
        self.postFlags = QU_FULLSYNC
##  	self.command = "\t\t-=-"
        self.command = ""
## 	preFlags = QU_BURST
## 	self.pos = 0

##     def start(self):
##	pass

    def Connect(self):
        """Connect to specified host/port as coun/repr."""
        ldb = empDb.megaDB['login']
        if empDb.DBIO.newDatabase and self.firstConnect:
            # On a new database, open the login window so that users may
            # enter the socket/country information.
            self.firstConnect = 0
            self.callback.login_error("Enter connect information.")
            return
        try:
            empQueue.socket = socket.socket(socket.AF_INET,
                                            socket.SOCK_STREAM)
            # Attempt to start the connection in non-blocking mode.
            # Hopefully this will allow the client to function while the
            # address is being looked up.
            empQueue.socket.setblocking(0)
            empQueue.socket.connect((ldb['host'], ldb['port']))
        except socket.error, e:
            if e[0] not in (errno.EINPROGRESS, errno.EWOULDBLOCK):
                self.callback.login_error("Connect error: " + str(e))
                return
        self.pos = 0
        empQueue.flags = QU_CONNECTING
        empQueue.FuncList[:0] = [ self ]
        empQueue.FLWaitLev = 0
        empQueue.FLSentLev = 1
        self.callback.connect_success()

    def Error(self, msg):
        """Note an error."""
        self.callback.login_error(msg)

    def Disconnect(self):
        """Break the connection with the server."""
        if empQueue.flags >= QU_DISCONNECT:
            # Already disconnected
            return
        self.callback.connect_terminate()
        empQueue.socket.close()
        del empQueue.socket
        empQueue.flags = QU_OFFLINE

    def line(self, line):
        """EmpIOQueue Handler: Process a line of data."""
        proto = line[:1]
        msg = line[1:]
        if empQueue.flags == QU_CONNECTING:
            empQueue.flags = QU_LOGIN

        # Ughh..  It appears we can get these async messages at any time..
        if proto in C_ASYNCS:
            empQueue.defParser.line(line)
            return

        ldb = empDb.megaDB['login']
        if (self.pos == 0):
            if proto != C_INIT:
                self.callback.login_error("[%s]%s" % (proto, msg))
                return
            self.pos = 1
            empQueue.SendNow("user %s" % self.username)
        elif (self.pos == 1):
            if proto != C_CMDOK:
                self.callback.login_error("[%s]%s" % (proto, msg))
                return
            self.pos = 2
            empQueue.SendNow("coun %s" % ldb['coun'])
        elif (self.pos == 2):
            if proto != C_CMDOK:
                self.callback.login_error("[%s]%s" % (proto, msg))
                return
            self.pos = 3
            empQueue.SendNow("pass %s" % ldb['repr'])
        elif (self.pos == 3):
            if proto != C_CMDOK:
                self.callback.login_error("[%s]%s" % (proto, msg))
                return
            if self.callback.login_kill:
                self.pos = 4
                empQueue.SendNow("kill")
            else:
                self.pos = 5
                empQueue.SendNow("play")
        elif (self.pos == 4):
            if proto != C_EXIT:
                self.callback.login_error("[%s]%s" % (proto, msg))
                return
            self.pos = 5
            empQueue.SendNow("play")
        elif (self.pos == 5):
            if proto != C_INIT:
                self.callback.login_error("[%s]%s" % (proto, msg))
                return
            # Login successful!
            self.pos = 99
            # Arghh - the flags must be set to FullSync, because FLWaitLev
            # may have already been encountered..
            empQueue.flags = QU_FULLSYNC
            empQueue.doFlags()
            # run the initialization script
            if empDb.DBIO.newDatabase:
                viewer.ioq.Send("exec "+pathPrefix("first.emp"))
                empDb.DBIO.newDatabase = 0
            # Note the change in the database.
            empDb.DBIO.needSave = 1
            # Start boot-up script
            if self.srcStart:
                viewer.ioq.Send("exec "+pathPrefix("start.emp"))
                self.firstConnect = 0
                self.srcStart = 0
            # Start connect script
            viewer.ioq.Send("exec "+pathPrefix("connect.emp"))
            self.callback.login_success()
            self.out = NormalHandler(self.command, viewer)
            self.out.start()
        else:
            self.out.line(line)

    def lull(self):
        viewer.Process()

    def retry(self):
        """Try to connect to the server again.

        Calling this function is the natural conclusion of a call to the
        login_error() method described above.
        """
        if empQueue.flags >= QU_DISCONNECT:
            self.Connect()
        elif empQueue.flags >= QU_CONNECTING:
## 	else:
            self.pos = 0
            self.line(C_INIT)
        else:
            viewer.Error("Unknown internal error.")

class AsyncHandler:
    """Handle asyncrounous server data.

    Data received that is not associated with a command is processed by
    this class.  The class requires the global viewer class to support the
    following methods:

    flash(), and inform()
    """
    def line(self, line):
        """EmpIOQueue Handler: Process a line of data."""
        if line[:1] == C_DATA:
            viewer.flash(line[2:])
        elif line[:1] == C_EXIT:
            viewer.Error("Server exiting (%s)." % (line[2:],))
            empQueue.loginParser.Disconnect()
##	    # HACK++
##	    if empQueue.FuncList:
##		del empQueue.FuncList[:1]
##		empQueue.FLSentLev = empQueue.FLSentLev - 1
        elif line[:1] == C_INFORM:
            empDb.megaDB['prompt']['inform'] = line[2:]
            viewer.inform()
        elif line[:1] == C_FLASH:
            viewer.flash(line[2:])
        else:
            viewer.Error('PTkEI: Bad protocol "%s"' % (line,))

    def lull(self):
        viewer.Process()

class NormalHandler:
    """Handle server data that is received during most normal operations.

    This class will invoke the chained display class associated with the
    command.  It will also detect built-in parsers from empDb.py, and bind
    those parsers with the display chain.
    """
    # The server sends telegram/annoucement/etc. messages to the client as
    # if they were normal C_DATA messages.  Store these messages
    # seperately, and send them all at once using the viewer.flash method.
    # This way, the individual parsers dont have to worry about detecting
    # these messages.
    msgqueue = []

    # empCmd.CmdRefresh expects this to be set:
    sendRefresh = None

#You have a new telegram waiting ...
#You have three new announcements waiting ...
#You lost your capital... better designate one
    msgMatch = re.compile(
        r"^You lost your capital\.\.\. better designate one$|"
        +r"^You have .* new (?:telegram|announcement)s? waiting \.\.\.$")

    def __init__(self, command, disp, pre=QU_SYNC, post=None):
        self.command = command
        self.out = disp
        self.sending = None
        self.preFlags = pre
        if post is None:
            post = pre
        self.postFlags = post
        self.atSubPrompt = 0

    def start(self):
        """EmpIOQueue Handler: Previous command completed; start this one."""
        # Check for lowlevel parsers
        lst = string.split(self.command)
        if lst:
            cmd = lst[0]
        else:
            cmd = ""
        parser = empParse.lookupParser(cmd)
        self.out = parser(self.out)
        self.out.Begin(self.command)

    def line(self, line):
        """EmpIOQueue Handler: Process a line of data."""
        proto = line[:1]
        msg = line[2:]

        if proto not in (C_DATA, C_PROMPT, C_FLUSH):
            # Can't handle the proto - send to async class.
            empQueue.defParser.line(line)
            return

        if self.atSubPrompt:
            # Ughh.  Something must have interrupted the sub-prompt.
            self.atSubPrompt = 0
            self.out.Answer(None)

        if proto == C_DATA:
            if (self.msgMatch.match(msg)):
                self.msgqueue.append(msg)
            else:
                # If there are messages on the msgqueue, then we have
                # been spoofed - send them along to the parsers normally.
                for i in self.msgqueue:
                    self.out.data(i)
                self.out.data(msg)
                del self.msgqueue[:]
        elif proto == C_PROMPT:
            # If there are messages on the msgqueue then flash them out.
            for i in self.msgqueue:
                viewer.flash(i)
            del self.msgqueue[:]
            ndb = empDb.megaDB['prompt']
            ndb['minutes'], ndb['BTU'] = map(int, string.split(msg))
            self.out.End(self.command)
##	elif msg[0] == C_REDIR:
##	    print "PE: Server Redirect requested:", msg[2:]
##	elif msg[0] == C_PIPE:
##	    print "PE: Server Pipe requested:", msg[2:]
##	elif msg[0] == C_EXECUTE:
##	    print "PE: Server Execute requested:", msg[2:]
        else:
            # Must be a C_FLUSH sub-prompt.
            eq = empQueue
            for i in range(1, eq.FLSentLev):
                if eq.FuncList[i].__class__ is NormalHandler:
                    # HACK!  It appears a Burst'd command answered a
                    # sub-prompt.  That command will have to be deleted
                    # from the queue.
                    cmd = eq.FuncList[i].command
                    eq.popHandler(i)
                    self.out.flush(msg, None)
                    self.out.Answer(cmd)
                    break
            else:
                self.atSubPrompt = 1
                self.out.flush(msg, self.handleFlush)

    def lull(self):
        self.out.Process()

    def handleFlush(self, response):
        """Chained viewer class callback: Respond to a prompt."""
        if not self.atSubPrompt:
            # Ughh.  No longer at the subprompt.
            viewer.Error("Sync error: Can not send sub-prompt.")
            return
        empQueue.SendNow(response)
        self.atSubPrompt = 0
        self.out.Answer(response)

def flashException():
    """Send an exception message directly to the display.

    This should be used in a block: try: ... except: flashException().
    """
    viewer.Error('Internal error!\nException %s with detail:\n"%s".'
                 % tuple(sys.exc_info()[:2]))
    traceback.print_exc()

def doNothing(*args, **kw):
    """Do absolutely nothing.  (Used as a dummy function.)"""
    pass

def EmpData(username):
    """Initialize EmpIOQueue with default values."""
    return EmpIOQueue(AsyncHandler(),
                      LoginHandler(viewer.loginCallback, username))

# Hack!  There is a function pathPrefix that is not defined in this module,
# but is setup for this module in empire.py.  See the line
# "empQueue.pathPrefix = pathPrefix" in the initialize function of
# empire.py.
