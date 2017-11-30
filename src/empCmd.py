"""Synthetic client side command interface."""

# version 1.0.2
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

import sys
import os
import string
import re
import bisect
import types

import empQueue
import empDb
import empParse
import empEval
import empPath
import empSector

# Key Ideas:

# What is contained within this file:

# This file holds much of the client-side synthetic command interface.  The
# main code implements a command checker that parses outgoing commands and
# determines if they are synthetic.  The main class is EmpParse; it
# performs these aliasing/redirection capabilities.  This file also
# contains a couple of high-level parse classes.  Please see the individual
# class documentation for more information.


# Sending a command to the server:

# To send an outgoing command, the standard method is to invoke
# viewer.ioq.Send().  (Because viewer.ioq points to the only instance of
# EmpParse, in many cases viewer.ioq will be replaced with self.  In
# general, "closer" references should be used in place of references to the
# global variable viewer.)  See the documentation with EmpParse.Send() for
# more info on the syntax and options available.


# Creating a new command:

# Use the following five steps to define a new command:
#
# 1 Create a new class that descends from the baseCommand class.
#
# 2 Define a class variable 'description' for the new class.  This should
# be a brief one-line description - it is printed when the user issues the
# 'define' command.
#
# 3 Set the class variable 'defaultBinding' to a list of commands to bind
# the class to.  The list must contain one or more 2-tuples that contain
# name/length pairs.  The length parameter sets the minimum length that
# must be matched for the command.  For example, if ("execute", 3) were
# used, then the command "exe" would match.  If the length is negative,
# then a command will also match if it has more characters than the total
# length of the command.  For example, if ("execute", -3) were used, then
# both the commands "exe" and "executes" would match.
#
# 4 Optionally set the class variable 'defaultPreList' to a true value.
# Setting this option causes the command-line checker to scan for this
# command before it does syntax checking.  So for example, if a new command
# called "newcommand" were bound and defaultPreList were set, then the
# command "newcommand echo 1 ; echo 2" would cause the class to be invoked
# with parameters "echo 1 ; echo 2".  However, if defaultPreList was not
# set, then the class would be invoked with parameters "echo 1" and a
# second command ("echo 2") would be buffered separately.
#
# 5 Define one or more of the following methods: invoke, receive, sending.
# There can be three different callbacks associated with a command due to
# the asynchronous nature of the command queue.  Ptkei supports
# command-buffering - that is, if a user issues a series of commands faster
# than the server can receive and respond to them, the client will
# automatically queue the commands.  One side-effect of this, is that if
# there are commands buffered when a synthetic client-side command is
# received, the client must decide whether to run the command instantly or
# to run it when the server finishes its processing.  To accomplish this,
# each command can set callbacks to be invoked under different conditions.
# Normally only one of the above callbacks is used per-command. (But the
# client is not limited to only one callback.)  Each callback has its own
# effect:
#
# invoke: This method is called the instant the user completes the command.
# (There is no synchronization performed.)  Never use this type of callback
# for commands that send data to the output window or that use the internal
# database.  This command is most useful for performing GUI events that are
# not related to the internal database or the command queue (EG. wread,
# Login).  One other noteworthy use, is for commands that only buffer
# additional commands on the queue (EG. alias, execute).  In this case it
# is acceptable to use invoke, as the synchronization will be performed by
# the newly added commands.  (These commands are only acting as
# "translators" - they don't need synchronization.)
#
# receive: Defining this method causes a special location marker to be
# inserted into the command-queue.  Once the server/client transmits all
# the commands prior to this marker, the callback is invoked.  This
# mechanism provides for synchronization in the command-queue.  This is the
# standard callback used anytime a command uses the internal database.  (If
# a user issues a command "rdb" followed by "mmove", the rdb command needs
# to be processed before calculating moves - else the moves wont utilize
# the latest database information.)  It is also the standard callback for
# commands that send date to the output window.  (If the user issues "map #
# ; define", the command listing must come only after all the map output
# has been displayed.)
#
# sending: This callback is invoked just before the command-queue would
# send the command (had it been a real command).  This is a limited use
# callback - it is currently only used by the rdb command.  The rdb command
# uses it to delay deciding on which commands to send until it is
# absolutely necessary to decide.  It uses this mechanism to gain some
# synchronization while still keeping the benefits of bursted commands.
# Chances are, this isn't the callback you want.

class EmpParse:
    """Implements a set of aliasing commands.

    This class is used as a wrapper around empQueue.EmpIOQueue.  Outgoing
    commands are sent here, and if they are not client synthetic commands,
    they are sent to the server via the empQueue module.  This class is
    more 'user-friendly' then the empQueue stuff.  The major interaction
    with this class is done via the Send() module which is passed simple
    ASCII strings that are to be transmitted.

    Note: This class generally only has one instantiation - viewer.ioq
    """

    def __init__(self, queue):
        # Pointer to the actual low-level socket manager.
        self.sock = queue

        # Copies of methods so that this class can "double" for
        # empQueue.EmpIOQueue.
        self.HandleInput = self.sock.HandleInput
        self.fileno = self.sock.fileno
        self.SendNow = self.sock.SendNow

        # Default command transmission flags:
        self.preFlag = self.postFlag = empQueue.QU_SYNC
## 	self.preFlag = self.postFlag = empQueue.QU_BURST
        self.raw = 0

        # History substitution:
        self.hisList = [""]
        self.hisPos = 0

        # Setup the syntax list:
        self.preList = []
        self.postList = []
        self.syntaxList = (
            (re.compile(
                r"^(?P<cmd>.*?)\s+"
                +r"(?P<flags>\||(?:>>?!?))"
                +r"\s*(?P<name>.*?)\s*$"),
             self.SyntaxRedirect),
            (re.compile(r"(?P<cmd1>.*)\s*;\s*(?P<cmd2>.*)"),
             self.SyntaxMulti),
            )

        # Set the default commands:
        self.registerCmds(CmdAlias, CmdNull, CmdEval, CmdForEach
                          , CmdBurst, CmdDefList, CmdRefresh, CmdExec
                          , CmdOut, CmdNova, CmdPredict, CmdMover
                          , CmdRaw, CmdOrigin, CmdMMove, CmdEMove
                          , CmdRemove, CmdDanno, CmdDtele, CmdProjection
                          , CmdDmove, CmdSetFood, CmdLTest, CmdCoords)

    def registerCmds(self, *args):
        """Register a list of commands."""
        for cmdclass in args:
            cmds = cmdclass.defaultBinding
            if cmdclass.defaultPreList:
                lst = self.preList
            else:
                lst = self.postList
            for cmd in cmds:
                bisect.insort(lst, cmd + (cmdclass,))

    commandFormat = re.compile(
        r"^\s*(?P<command>\S+)(?:\s+(?P<args>.*))?$")
    def Send(self, cmd, disp=None, prepend=0,
             preFlag=None, postFlag=None, raw=None):
        """Search command line for smart commands.

        This method is the main way of interacting with this class.  Send
        will search the given command for known smart-commands.  If one is
        found, its associated code block is run.  Otherwise, the command is
        sent unaltered to EmpIOQueue for normal server execution.  This
        method has grown to include a number of options that may be
        specified for each outgoing command.  disp = the display parser to
        associate with the outgoing command (None indicates that the
        standard viewer should be used).  Setting prepend will instruct the
        command to be prepended to the queue - this causes the command to
        be the next command sent regardless of other waiting commands.
        preFlags/postFlags = the empQueue pre & post flags that should be
        requested for the command (assuming it is not a client-command).
        Setting raw will force this method to send the command unaltered -
        thus ignoring possible client-side commands.
        """
        if disp is None:
            disp = viewer

        if raw is None:
            raw = self.raw

        # Find root word
        if not raw:
            mm = self.commandFormat.match(cmd)
            if mm:
                arg0 = mm.group('command')
                # Check pre-syntax list
                f = empParse.findCmd(self.preList, arg0)
                if f is not None:
                    f(self, mm, disp)
                    return
                # Check syntax list
                for i in self.syntaxList:
                    test = i[0].match(cmd)
                    if test is not None:
                        i[1](test, disp)
                        return
                # Check post-syntax list
                f = empParse.findCmd(self.postList, arg0)
                if f is not None:
                    f(self, mm, disp)
                    return
        # Command not aliased - send raw
        if preFlag is None:
            preFlag = self.preFlag
        if postFlag is None:
            postFlag = self.postFlag
        hdlr = empQueue.NormalHandler(cmd, disp, preFlag, postFlag)
        if prepend:
            self.sock.AddHandler(hdlr, 0)
        else:
            self.sock.AddHandler(hdlr)

    def HistSend(self, cmd):
        """Send the command with support for history substitution."""
        if cmd[:2] == "!!":
            cmd = self.hisList[1]
            del self.hisList[1]
        elif cmd[:1] == "!":
            cmd = cmd[1:]
            l = len(cmd)
            for i in range(1, len(self.hisList)):
                val = self.hisList[i]
                if val[:l] == cmd:
                    cmd = val
                    del self.hisList[i]
                    break
            else:
                raise IndexError
        else:
            if cmd[:1] == "^":
                pos = string.find(cmd, "^", 1)
                if pos == -1:
                    raise IndexError
                cmd = string.replace(self.hisList[1], cmd[1:pos],
                                     cmd[pos+1:], 1)
                if cmd == self.hisList[1]:
                    raise IndexError

            # Remove duplicate commands from the history list
            del self.hisList[0]
            try: self.hisList.remove(cmd)
            except ValueError: pass

        # Add the command to the history list
        self.hisList[:0] = ["", cmd]
        self.hisPos = 0
        del self.hisList[100:]

        self.Send(cmd)

    def HistMove(self, offset, cmd):
        """Note an up/down arrow command-line request; returns new cmdline."""
        if ((offset == 1 and self.hisPos >= len(self.hisList)-1)
            or (offset == -1 and self.hisPos <= 0)):
            raise IndexError
        if (offset == 1 and self.hisPos == 0):
            self.hisList[0] = cmd
        self.hisPos = self.hisPos + offset
        return self.hisList[self.hisPos]

    def SyntaxMulti(self, match, out):
        """Multi-Command line."""
        self.Send(match.group('cmd1'), out)
        self.Send(match.group('cmd2'), out)

    def SyntaxRedirect(self, match, out):
        """Redirect output to a file."""
##  	print "redirect"
        flags = match.group('flags')
        if flags == "|":
            type = "pipe"
        elif flags[:2] == ">>":
            type = "append"
        elif flags[-1] == "!":
            type = "force"
        else:
            type = ""
        self.Send(match.group('cmd'),
                  RedirectOutput(out, match.group('name'), type))



class baseCommand:
    """Base class for synthetic commands. (Does little by itself.)

    This class is used as a base-class for creating new synthetic commands
    in the client.  To define a new client-side command create a class that
    descends from this class, and then pass the new class to
    EmpParse.registerCmds().

    The following class values are supported:

    description - a short text description that is printed when 'define' is
                called.
    commandFormat - if defined, it must be a regular expression that
                specifies the parameters for the command.
    commandUsage - a text string to print should the above regular
                expression fail to match.

    The following class attributes are not used by this base-class, but are
    used by EmpParse when the command is 'registered':

    defaultPreList - Sets the 'parse ordering' of the command.
    defaultBinding - A list of name/length pairs to bind the command to.

    The following methods are supported:

    invoke - Callback invoked the moment the user types the command.
    receive - Callback invoked when the outbound command queue reaches this
                command.
    sending - Callback invoked when the command queue is ready to send the
                command to the server.
    """

    # EmpParse (command registration) required fields:
    description = "No help available."
    defaultPreList = defaultBinding = None

    # Redefinable fields:
    sendRefresh = None
    invoke = receive = None
    commandFormat = None
    commandUsage = None

    def __init__(self, ioq, match, disp):
        # Establish defaults for all the standard command class commands.
        self.out = disp
        self.ioq = ioq
        self.Send = ioq.Send
        self.commandMatch = match
        # If commandFormat is defined check command parameters now.
        if self.commandFormat is not None:
            args = match.group('args')
            if not args:
                args = ""
            self.parameterMatch = self.commandFormat.match(args)
            if not self.parameterMatch:
                form = self.commandUsage
                if form is None:
                    form = self.commandFormat.pattern
                viewer.Error("Invalid parameters.  Form should be:\n%s"
                             % form)
                return
        # Call invoke method immediately
        if self.invoke is not None:
            self.invoke()
        # Add command to queue (if required)
        if self.receive is not None or self.sending is not None:
##  	    # Send DB update commands
##  	    if self.sendRefresh:
##  		ioq.Send("rdb"+self.sendRefresh, self.out)
            # Arrange for callback from queue code
            ioq.sock.AddHandler(self)

    # EmpQueue required fields:
    preFlags = empQueue.QU_BURST
    postFlags = empQueue.QU_FULLSYNC
    command = None
    sending = None

    def start(self):
        """EmpIOQueue Handler: Previous command completed; start this one."""
        # Ughh..
        if self.receive is not None:
            s = self.commandMatch.string
            self.out.Begin(s)
            self.receive()
            self.out.End(s)


class CmdDefList(baseCommand):

    description = "List all online commands."

    defaultBinding = (('define', 6),)

    def receive(self):
        if not self.out.data:
            return
        self.out.data('Pre-syntax:')
        for i, k, j in self.ioq.preList:
            self.out.data("%-10s - %s" % (i, j.description))
        self.out.data("")
        self.out.data("Syntax:")
        for i in self.ioq.syntaxList:
            self.out.data("%-35s - %s" % (i[0].pattern, i[1].__doc__))
        self.out.data("")
        self.out.data("Post-syntax:")
        for i, k, j in self.ioq.postList:
            self.out.data("%-10s - %s" % (i, j.description))

class CmdAlias(baseCommand):

    description = "Generate a definition for a simple alias."

    defaultPreList = 1
    defaultBinding = (('alias', 5),)

    EAliasFormat = re.compile(r"\$(\$|\*|\d+)")

    commandUsage = "alias <name> <command>"
    commandFormat = re.compile(
        r"^(?P<newName>\S+)\s+(?P<value>.*?)\s*$")
    def invoke(self):
        newcmd = self.parameterMatch.group('value')
        name = self.parameterMatch.group('newName')
        lst = self.EAliasFormat.split(newcmd)

        class dummyclass(baseCommand):
            def invoke(self):
                """Evaluate an alias for a given command."""
                sublst = self.substitutions
                args = self.commandMatch.group('args')
                if args is None:
                    args = ""
                argl = string.split(self.commandMatch.string)
                cmd = ""
                for part in range(len(sublst)):
                    val = sublst[part]
                    if part & 1:
                        # Odd value - this is a parameter substitution.
                        if val == '*':
                            cmd = cmd + args
                        elif val == '$':
                            cmd = cmd + '$'
                        else:
                            try:
                                cmd = cmd + argl[int(val)]
                            except IndexError:
                                viewer.Error("Not enough arguments for alias.")
                                return
                    else:
                        cmd = cmd + val
                self.Send(cmd, self.out, 1)

        dummyclass.description = "Aliased to "+repr(newcmd)
        dummyclass.defaultBinding = ((name, len(name)),)
        dummyclass.substitutions = lst

        self.ioq.registerCmds(dummyclass)

class CmdOrigin(baseCommand):
    description = "Block unsupported server command."

    defaultBinding = (('origin', -3),)

    def receive(self):
        viewer.Error("Sorry, the origin command is not supported.")
        viewer.Error("Please see TIPS.html for more information.")

class CmdRaw(baseCommand):
    description = "Send a command without client interpretation."

    defaultPreList = 1
    defaultBinding = (('raw', 3),)

    def invoke(self):
        self.ioq.Send(self.commandMatch.group('args'), raw=1)

class CmdBurst(baseCommand):

    description = "Send a multi-command line without syncing server output."

    defaultPreList = 1
    defaultBinding = (('burst', 5),)

    def invoke(self):
        args = self.commandMatch.group('args')
        if not args:
            return
        pre, post = self.ioq.preFlag, self.ioq.postFlag
## 	self.preFlag = empQueue.QU_SYNC
## 	self.postFlag = empQueue.QU_FORCEBURST
        self.ioq.preFlag = self.ioq.postFlag = empQueue.QU_BURST
## 	self.Send(args, out, preFlag=pre, postFlag=post)
        self.Send(args, self.out)
        self.ioq.preFlag, self.ioq.postFlag = pre, post

class CmdExec(baseCommand):

    description = "Run commands from a file."

    defaultBinding = (('execute', -3), ('runfeed', 7))

    def invoke(self):
        args = self.commandMatch.group('args')
        if not args:
            return
        try:
            if self.commandMatch.group('command')[:1] == 'r':
                # Runfeed command
                file = os.popen(args, 'r')
            else:
                # Execute command
                file = open(args)
        except IOError:
            viewer.Error("Unable to open file [%s]." % args)
            return
        lst = file.readlines()
        file.close()
        for i in lst:
            i = string.strip(i)
            if not i or i[0] == '#':
                continue
            self.Send(i, self.out)

##     class ReallySilentDisp(empParse.baseDisp):
## 	"""Display class that discards all input."""
## 	Begin = data = Answer = End = empQueue.doNothing

##     class QuietDisp(empParse.baseDisp):
## 	"""Display class that discards some input."""
## 	data = empQueue.doNothing

class SilentDisp(empParse.baseDisp):
    """Display class that discards most input."""
    def __init__(self, disp, name):
        empParse.baseDisp.__init__(self, disp)
        self.name = name
    def __del__(self):
        if self.End is empQueue.doNothing:
            self.out.End(self.name)
    def Begin(self, cmd):
        if self.Begin is not empQueue.doNothing:
            self.out.Begin(self.name)
            self.Begin = empQueue.doNothing
    def End(self, cmd):
        self.End = empQueue.doNothing
    data = empQueue.doNothing

class CmdNull(baseCommand):

    description = "Run command with no output."

    defaultPreList = 1
    defaultBinding = (('null', 4),)

    def invoke(self):
        self.Send(self.commandMatch.group('args')
                  , SilentDisp(self.out, self.commandMatch.string))


class CmdPredict(baseCommand):

    description = "Get predictions for a sector."

    sendRefresh = "e"
    defaultBinding = (('Predict', 7),)

    def receive(self):
        try:
            coord = empParse.str2Coords(self.commandMatch.group('args'))
        except ValueError:
            viewer.Error("Invalid coordinates.")
            return
        DB = empDb.megaDB['SECTOR'][coord]
        for i in string.split(empSector.sectorPredictions(DB), "\n"):
            self.out.data(i)

class CmdMover(baseCommand):

    description = "Issue a multi-stage move."

    sendRefresh = "e"
    defaultBinding = (('Mover', 5),)

    commandUsage = "Mover <commodity> <quantity> <sector> <sector> [<sector> ...]"
    commandFormat = re.compile(
        r"^(?P<comd>\S+)\s+(?P<val>[+-@]?\d+)\s+(?P<sectors>.*)$")
    def receive(self):
        mm = self.parameterMatch
        try:
            sectors = map(empParse.str2Coords,
                          string.split(mm.group('sectors')))
            if len(sectors) < 2:
                raise ValueError
            commodity = empEval.commodityTransform[mm.group('comd')]
            quantity = getMoveQuantity(mm.group('val'), commodity, sectors)
        except (ValueError, KeyError):
            viewer.Error("Move invalid input failure.")

        if quantity < 0:
            quantity = -quantity
            sectors.reverse()

        for i in range(len(sectors)-1, 0, -1):
            last = sectors[i-1]
            cur = sectors[i]
            self.Send("move %s %d,%d %d %d,%d" % (
                commodity, last[0], last[1], quantity, cur[0], cur[1]),
                      self.out, 1)

class CmdRefresh(baseCommand):

    description = "Refresh client databases."

    defaultBinding = (('rdb', -3), ('rerdb', -5))

    syncFormat = re.compile(
        r"^(?P<total>re)?rdb(?P<pre>P)?(?P<flags>[eslpno]*)$")

    postFlags = empQueue.QU_BURST

    commandFlags = [('e', 'SECTOR', 'dump'),
                    ('l', 'LAND UNITS', 'ldump'),
                    ('s', 'SHIPS', 'sdump'),
                    ('p', 'PLANES', 'pdump'),
                    ('n', 'NUKES', 'ndump'),
                    ('o', 'LOST ITEMS', 'lost')]

    def invoke(self):
        match = self.syncFormat.match(self.commandMatch.group('command'))
        if not match:
            viewer.Error("refresh regex failure.")
            return

        # Set the display class class to the null-parser
        self.out = SilentDisp(self.out, match.string)

##  	self.dumpList = match.group('flags') or "elspno"
        self.dumpList = match.group('flags') or "elspo"
        self.persistent = (match.group('pre') != None)
        self.totalDump = (match.group('total') != None)
        self.neededDump = ""

    def checkPending(self, qElem):
        """empQueue scan callback: Don't send redundant commands."""
        if qElem.sendRefresh is not None:
            for i in qElem.sendRefresh:
                if i not in self.neededDump:
                    self.neededDump = self.neededDump + i
            return 0
        if qElem.__class__ is self.__class__:
            # Found a refresh command pending - don't send any repeated dumps
            for i in qElem.dumpList:
                pos = string.find(self.dumpList, i)
                if pos != -1 and string.find(self.neededDump, i) == -1:
                    self.dumpList = self.dumpList[:pos] + self.dumpList[pos+1:]
                    if not self.dumpList:
                        # No dump commands left - end scan
                        return 1
        return 0

    def sending(self):
        # Ughh.
        qPos = self.ioq.sock.FLSentLev
        # Check if parts of this dump can be picked up by a pending dump.
        if not self.persistent:
            self.ioq.sock.scanQueue(self.checkPending, start=qPos+1)

        for dumpInfo in self.commandFlags:
            # Check if this kind of dump is requested.
            if not dumpInfo[0] in self.dumpList:
                continue

            # Set the timestamp.
            ts = ""
            if (not self.totalDump
                # HACK!  Always do a full dump of the nuke database
                and dumpInfo[0] != 'n'):
                time = empDb.megaDB[dumpInfo[1]].unofficial_timestamp
                if time != 0:
                    ts = " ?timestamp>%s" % time

            # Generate the command.
            qPos = qPos + 1
            self.ioq.sock.AddHandler(empQueue.NormalHandler(
                dumpInfo[2] + " *" + ts, self.out, pre=empQueue.QU_SYNC
                , post=empQueue.QU_FORCEBURST)
                                     , pos=qPos)

        if (not self.totalDump and
            'MOB_ACCESS' in empDb.megaDB['version']['enabledOptions']):
            self.ioq.sock.AddHandler(empQueue.NormalHandler(
                "dump * mob", self.out, pre=empQueue.QU_SYNC,
                post=empQueue.QU_FORCEBURST)
                                     , pos=qPos)

s_var = r"(?P<var>\w+)"
s_val = r"(?P<val>\w+)"
s_command = r"(?P<command>.*)"

class CmdEval(baseCommand):

    description = "Evaluate an expression for a sector/database."

    sendRefresh = "e"
    defaultPreList = 1
    defaultBinding = (('eval', 4),)

    commandUsage = "eval {<sector>|'nation'|'version'} <command>"
    commandFormat = re.compile(
        r"^(?P<type>"+empParse.s_sector+"|nation|version)\s+"+s_command+"$")
    def receive(self):
        mm = self.parameterMatch
        type = mm.group('type')
        if type == 'nation' or type == 'version':
            db = empDb.megaDB[type]
        else:
            type = 'SECTOR'
            key = tuple(map(int, mm.group('sectorX', 'sectorY')))
            try:
                db = empDb.megaDB['SECTOR'][key]
            except KeyError:
                viewer.Error("Could not find sector.")
                return
        try:
            self.Send(empEval.evalString(
                empEval.estrToExpr(mm.group('command')),
                type, db),
                      self.out, 1)
        except empEval.error, e:
            viewer.Error(e)

class CmdForEach(baseCommand):

    description = "Run given command on specified sectors."

    sendRefresh = "e"
    defaultPreList = 1
    defaultBinding = (('foreach', 7),)

    commandUsage = "foreach <sectors> [?<selectors>] <command>"
    commandFormat = re.compile(
        r"^(?P<sectors>\S+)\s+(?:\?(?P<selectors>\S+)\s+)?"
        +s_command+"$")
    def receive(self):
        mm = self.parameterMatch
        try:
            list = empEval.foreach(
                "owner==-1 and "+empEval.selectToExpr('SECTOR', mm.group('sectors'),
                                                      mm.group('selectors')),
                empEval.estrToExpr(mm.group('command')),
                'SECTOR')
        except empEval.error, e:
            viewer.Error(e)
        else:
            for i in list:
                self.Send(i, self.out, 1)

class CmdOut(baseCommand):

    description = "Debugging tool - dumps database."

    sendRefresh = "espnlo"
    defaultBinding = (('out', 3),)

##      outFormat = re.compile(r"\s+(\S+)\s*$")
    def receive(self):
        self.out.data(str(empDb.megaDB))
##	cmds = [('e', 'SECTOR', 'dump'),
##		('l', 'LAND UNITS', 'ldump'),
##		('s', 'SHIPS', 'sdump'),
##		('p', 'PLANES', 'pdump'),
## #		('n', 'NUKES', 'ndump'),
##		('o', 'LOST ITEMS', 'lost')]
##	c = match.group(1)
##	if not c:
##	    c = 'elspno'

##	mm = self.match_out.search(match.string)

##	if not mm:
##	    val = '*'
##	else:
##	    val = mm.group(1)

##	for dbt in cmds:
##	    if not dbt[0] in c:
##		continue

##	    out.data(dbt[1]+":" + `self.getSectors(val, "", dbt[1])`)

class CmdMMove(baseCommand):

    description = "Ulf Larsson's multi-move tool."

    sendRefresh = "e"
    defaultBinding = (('mmove', 5),)

    commandUsage = ("mmove <commodity> <src sectors> <min level>"
                    " <min mob> <dst sectors> <max level>")
    commandFormat = re.compile(
        "^"+empParse.s_comm+"\s+"
        r"(?P<sectors>\S+)(?:\s+\?(?P<selectors>\S+))?\s+"
        r"(?P<level1>\S+)\s+(?P<mob>\S+)\s+"
        r"(?P<sectors2>\S+)(?:\s+\?(?P<selectors2>\S+))?\s+"
        r"(?P<level2>\S+)\s*$")
    def receive(self):
        mm = self.parameterMatch
        commodity, slevel, mob, dlevel = mm.group(
            'comm', 'level1', 'mob', 'level2')
        try: commodity = empEval.commodityTransform[commodity]
        except KeyError:
            viewer.Error("Unknown commodity.")
            return

        # Call the empEval.foreach function.  empEval.foreach tests every
        # sector in the database to see if arg1 tests true.  If it does, then
        # arg2 is evaluated and inserted into the list.
        try:
            # Return a list for source sectors that contains tuples of the
            # form: ((x, y), sectDB, amount, mobility)
            slist = empEval.foreach(
                ("owner==-1 and "+empEval.selectToExpr('SECTOR',
                    mm.group('sectors'), mm.group('selectors'))),
                ("(xloc+0,yloc+0), __db[1], int("+commodity+"-("+slevel
                 +")), int(mob-("+mob+"))"),
                'SECTOR')
            # Return a list for destination sectors that contains tuples of the
            # form: ((x, y), sectDB, amount)
            dlist = empEval.foreach(
                ("owner==-1 and "+empEval.selectToExpr('SECTOR',
                    mm.group('sectors2'), mm.group('selectors2'))),
                "(xloc+0,yloc+0), __db[1], int(("+dlevel+")-"+commodity+")",
                'SECTOR')
        except empEval.error, e:
            viewer.Error(e)
            return
        
        # Create usable dictionaries from the returned list.
        ddict = {}
        for coord, db, amount in dlist:
            if amount > 0 and empSector.is_movable_into(db, commodity):
                ddict[coord] = amount
        sdict = {}
        for coord, db, amount, mobility in slist:
            if (amount > 0 and mobility > 0
                and not ddict.has_key(coord)
                and empSector.is_movable_from(db, commodity)):
                sdict[coord] = (amount, mobility,
                                empSector.move_weight(db, commodity))
##        print "sdict: %s\nddict: %s" % (sdict, ddict)  # lfm

        # Send the dictionaries to the move generator
        mmove = empPath.MoveGenerator(commodity, sdict, ddict)

        # Extract the moves and pass to the command queue.
        while not mmove.empty() :
            comm, path, amount = mmove.move()
            self.Send("move %s %d,%d %s %d,%d" % (
                comm, path.start[0], path.start[1], amount,
                path.end[0], path.end[1]),
                      self.out, 1)
            mmove.next()

class CmdEMove(baseCommand):

    description = "Ulf Larsson's multi-move explore tool."

    sendRefresh = "e"
    defaultBinding = (('emove', 5),)

    commandUsage = ("emove {civ|mil} <source sectors> <min level>"
                    " <min mobility> <dest sectors>")
    commandFormat = re.compile(
        "^"+empParse.s_comm+"\s+"
        r"(?P<sectors>\S+)(?:\s+\?(?P<selectors>\S+))?\s+"
        r"(?P<level1>\S+)\s+(?P<mob>\S+)\s+"
        r"(?P<sectors2>\S+)(?:\s+\?(?P<selectors2>\S+))?\s*$")
    def receive(self):
        mm = self.parameterMatch
        commodity, slevel, mob = mm.group(
            'comm', 'level1', 'mob')
        try: commodity = empEval.commodityTransform[commodity]
        except KeyError:
            viewer.Error("Unknown commodity.")
            return

        # Call the empEval.foreach function.  empEval.foreach tests every
        # sector in the database to see if arg1 tests true.  If it does, then
        # arg2 is evaluated and inserted into the list.
        try:
            # Return a list for source sectors that contains tuples of the
            # form: ((x, y), sectDB, amount, mobility)
            slist = empEval.foreach(
                ("owner==-1 and "+commodity+">0 and "+empEval.selectToExpr('SECTOR',
                    mm.group('sectors'), mm.group('selectors'))),
                ("(xloc+0,yloc+0), __db[1], int("+commodity+"-("+slevel
                 +")), int(mob-("+mob+"))"),
                'SECTOR')

            # Return a list for destination sectors that contains tuples of the
            # form: ((x, y), sectDB)
            dlist = empEval.foreach(
                (empEval.selectToExpr('SECTOR',
                    mm.group('sectors2'), mm.group('selectors2'))),
                "(xloc+0,yloc+0), __db[1]",
                'SECTOR')

        except empEval.error, e:
            viewer.Error(e)
            return

        # Create usable dictionaries from the returned list.
        ddict = {}
        for coord, db in dlist:
            if empSector.is_explorable_into(db):
                ddict[coord] = 1
        sdict = {}
        for coord, db, amount, mobility in slist:
            if (amount > 0 and mobility > 0
                and not ddict.has_key(coord)
                and empSector.is_movable_from(db, commodity)):
                sdict[coord] = (amount, mobility, 1.0)
##  	print "%s\n%s" % (sdict, ddict)

        # Send the dictionaries to the move generator
        mmove = empPath.MoveGenerator(commodity, sdict, ddict,
                                      empPath.ExplMobCost())

        # Extract the moves and pass to the command queue.
        while not mmove.empty() :
            comm, path, amount = mmove.move()
            self.Send("explore %s %d,%d %s %sh" % (
                comm, path.start[0], path.start[1], amount, path.directions),
                      self.out, 1)
            mmove.next()

class CmdNova(baseCommand):

    description = "Auto-explore sectors."

    sendRefresh = "e"
    defaultBinding = (('nova', 4),)

    commandUsage = "nova {civ|mil} <from sector> [<to sector>]"
    commandFormat = re.compile(
        "^"+empParse.s_comm+"\s+"+empParse.s_sector
        +"\s*(?:"+empParse.s_sector2+")?\s*$")
    def receive(self):
        mm = self.parameterMatch
        start = map(int, mm.group('sectorX', 'sectorY'))
        if mm.group('sector2X'):
            dest = map(int, mm.group('sector2X', 'sector2Y'))
        else:
            dest = start
        if dest == start:
            estr = "%s,%s 1" % tuple(start)
        else:
            estr = "%s,%s 1 %s,%s" % tuple(start+dest)
        db = empDb.megaDB['SECTOR']
        # Check if there are wilderness sectors around destination.
        CN_UNOWNED = empDb.CN_UNOWNED
        for newcoord in empDb.sectorNeighbors(dest):
            sect = db.get(newcoord, {})
            des = sect.get('des')
            own = sect.get('owner')
            if ((own == 0 or own is None or own == CN_UNOWNED)
                and des is not None and des not in ".?s\\"):
## 		print "exploring to %s,%s a (%s) owned by (%s)" % (
## 		    newcoord+(sect.get('des'), sect.get('owner')))
                break
        else:
            # No sectors to explore
            return
        self.Send("explore " + mm.group('comm') + " " + estr,
                  HandleNova(self.out, self.ioq, mm.group('comm'), start, dest),
                  1, empQueue.QU_SYNC, empQueue.QU_FULLSYNC)
        self.Send("des * ?newdes=-&mob<1 +", self.out,
##  		  preFlag=empQueue.QU_SYNC,
                  postFlag=empQueue.QU_FORCEBURST)
##	self.Send("esync")

class HandleNova(empParse.baseDisp):
    """Parse class for nova handled explores.

    This class receives output after the empParse.ParseMove class.
    Basically, it automatically generates moves based on the information
    contained in the prompts.
    """

    def __init__(self, disp, slf, comd, start, dest):
        empParse.baseDisp.__init__(self, disp)
        self.slf = slf
        self.comd = comd
        self.start = start
        self.dest = dest
        self.oldflush = None
        self.direc = 0
    promptFormat = empParse.ParseMove.promptFormat
    def flush(self, msg, hdl):
        mm = self.promptFormat.match(msg)
        if not mm:
            # Encountered an unknown prompt
            self.out.flush(msg, hdl)
            return
        if self.oldflush is not None and msg != self.oldflush:
            # Looks like we succeeded in moving.
            self.out.flush(msg, None)
            hdl('h')
            return
        self.oldflush = msg
        db = empDb.megaDB['SECTOR']
        CN_UNOWNED = empDb.CN_UNOWNED
        # Failed to move.
        neighbors = empDb.sectorNeighbors(self.dest)
        pathDirections = empDb.pathDirections
        while 1:
            if self.direc >= len(pathDirections):
                # No more directions left
                self.out.flush(msg, None)
                hdl('h')
                return
            newcoord = neighbors[self.direc]
            sect = db.get(newcoord, {})
            des = sect.get('des')
            own = sect.get('owner')
            if (((own == 0 or own is None) and des is not None
                 and des not in ".\\")
                or (own == CN_UNOWNED and des not in "?s")):
                self.out.flush(msg, None)
                hdl(pathDirections[self.direc])
                break
            self.direc = self.direc + 1
        self.direc = self.direc + 1
    ownSector = empParse.ParseMove.ownSector
    def data(self, msg):
        self.out.data(msg)
        mm = self.ownSector.match(msg)
        if mm:
            if self.direc < len(empDb.pathDirections):
                CmdNova(
                    self.slf,
                    EmpParse.commandFormat.match(
                        "nova %s %s,%s %s,%s" % (
                            self.comd, self.start[0], self.start[1],
                            self.dest[0], self.dest[1])),
                    self.out)
            self.slf.Send(
                "nova %s %s,%s %s,%s" % (
                    (self.comd, self.start[0], self.start[1],
                    mm.group('sectorX'), mm.group('sectorY'))),
                self.out)

##  class HandleFlush(empParse.baseDisp):
##      """Class to handle programable sub-prompts."""
##      def __init__(self, disp, prompts):
##  	empParse.baseDisp.__init__(self, disp)
##  	self.prompts = list(prompts)
##      def flush(self, msg):
##  	for i in range(prompts):
##  	    val = prompts[i]
##  	    if type(val) == types.tuple:
##  		match, val = val
##  		mm = match.match(msg)
##  		if mm:
##  		    if callable(val):
##  			viewer.SendNow(val(mm))
##  		    else:
##  			viewer.SendNow(val)
##  		    break
##  	    elif callable(val):
##  		viewer.SendNow(val(msg))
##  		del self.prompts[i]
##  		break
##  	    else:
##  		viewer.SendNow(val)
##  		del self.prompts[i]
##  		break
##  	else:
##  	    self.out.flush(msg)

class ParseShow(empParse.baseDisp):
    """Rearrange output from multiple commands into a set of columns.

    This is a hack!  - It is really only usefull for show XXX YYY.
    Now this hack got hacked by Bernhard to let capability listings
        not grow to big. So it is special for cshow. :-)
        It is important that "cap" are the last char of the last command
        which this class is called with.

    Kevin has arranged a list Body. The last element is printed first,
    so that commands with more overhead lines can append to the list.
    """

    def __init__(self, disp):
        empParse.baseDisp.__init__(self, disp)

        self.CBody = []
        self.Body = []
        self.first = 1
        self.foundheader = 0

    def __del__(self):
        # do the output
        for i in range(1, len(self.Body)+1):
            self.out.data(self.Body[-i])

    def End(self, cmd):
        self.out.End(cmd)
        # stuff to do at the end of each block, put CBody in Body

        if self.Body:
            mx = max(map(len, self.Body))
        else:
            mx = 0

        # next lines just to test that i have understood this --Bernhard
## 	sys.stdout.write('cmd=' + cmd + "\n")
        if  cmd[-3:] == "cap" :
## 	    sys.stdout.write('found cap cmd\n')
## 	    sys.stdout.flush()
            mfc=140-mx-1  # max width for cap output (should be determined dynmc)

        al=0 	# added lines, only >0 when formatting cap output
        for i in range(len(self.CBody)):
            if cmd[-3:] == "cap":
                while len(self.CBody[i])>mfc:
                    # insert enough additional lines in Body and truncate CBody
                    # a better approach would be to find a word to split
                    ll= len(self.CBody[i])
                    if (ll/mfc)*mfc==ll:
                        ii=(ll/mfc - 1)*mfc
                    else:
                        ii=(ll/mfc)*mfc
                    self.Body.insert(i+al,' '*mx + ' ' + self.CBody[i][ii:])
                    self.CBody[i]= self.CBody[i][:ii]
                    al=al+1

            if i+1 > len(self.Body):
                self.Body.append(' '*mx + self.CBody[i])
            else:
                self.Body[i+al] =  ( self.Body[i+al]
                                        + ' '*(mx-len(self.Body[i+al]))
                                        + self.CBody[i])
        self.CBody = []
        self.Bpos = -1
        self.first = 0
        self.foundheader = 0

    def data(self, msg):
        # prepend message to CBody
        if not self.foundheader:
            if string.lstrip(msg[:25]) == '':
                self.foundheader = 1
            else:
                return
        if self.first:
            self.CBody[0:0] = [ msg ]
        else:
            self.CBody[0:0] = [ msg[25:] ]

class RedirectOutput(empParse.baseDisp):
    """Redirect a command to a file or program."""
    def __init__(self, disp, name, type):
        empParse.baseDisp.__init__(self, disp)
        self.name = name
        self.type = type
    def Begin(self, cmd):
##  	print "opening"
        if self.out.Begin is empQueue.doNothing:
            # File already opened.
            return
        self.out.Begin(cmd)
        try:
            if self.type == "pipe":
                self.file = os.popen(self.name, 'w')
            else:
                if self.type == "append":
                    flags = "a"
                elif self.type != "force" and os.path.exists(self.name):
                    raise IOError, "File %s already exists." % self.name
                else:
                    flags = "w"
                self.file = open(self.name, flags)
        except:
            viewer.Error('Exception %s with detail:\n"%s".'
                         % tuple(sys.exc_info()[:2]))
            self.file = None
    def End(self, cmd):
##  	print 'end'
        self.out.End(cmd)
        if self.file is not None:
            self.file.close()
    def data(self, msg):
##  	print 'data'
        if self.file is not None:
            self.file.write(msg+"\n")
        else:
            self.out.data(msg)

def getMoveQuantity(txt, commodity, sectors):
    var = string.lstrip(txt)
    flag = 0
    if var and var[0] in '-+@':
        if var[0] == '@':
            flag = 1
            var = var[1:]
        else:
            flag = 2

    val = int(var)

    # Check for reverse paths.
    if flag == 2:
        # Absolute move.
        quantity = val
    elif flag == 1:
        # Reverse "smart" move.
        db = empDb.megaDB['SECTOR'][sectors[-1]]
        quantity = val - db.get(commodity, 0)
    else:
        # Normal "smart" move.
        db = empDb.megaDB['SECTOR'][sectors[0]]
        quantity = db.get(commodity, 0) - val

    return quantity

##  class telegramParser(empParse.baseDisp):
##      def __init__(self, cmd, msg):
##  	empParse.baseDisp.__init__(self, viewer)
##  	self.cmd = cmd
##  	self.msg = string.split(string.rstrip(msg), '\n')
##      prompt = empParse.ParseTele.prompt
##      def flush(self, msg, hdl):
##  	# Get the characters remaining in this message
##  	mm = self.prompt.match(msg)
##  	if not mm:
##  	    self.out.flush(msg, hdl)
##  	else:
##  	    response = ""
##  	    left = int(mm.group('left'))
##  	    if len(self.msg) == 0:
##  		response = "."
##  	    elif len(self.msg[0]) > left:
##  		if len(self.msg[0]) > 1024:
##  		    # Force out a partial string
##  		    response = self.msg[0][:left]
##  		    self.msg[0] = self.msg[0][left:]
##  		else:
##  		    # Finish this message
##  		    viewer.ioq.Send(self.cmd, self, 1)
##  		    response = "."
##  	    else:
##  		response = self.msg[0]
##  		del self.msg[0]
##  	    self.out.flush(msg, None)
##  	    hdl(response)

def sendTelegram(cmd, msg):
    """Send a telegram to the server.

    This function takes a telegram/announcement command stored in cmd, and
    a multi-line string stored in msg and then bursts the telegram command
    and the body of the message to the server.  The results of this command
    are not synchronized or checked in any way.  Assumptions are made about
    the form and acceptable content of a telegram, and then all the info is
    bursted out.  The advantage of bursting telegrams, is that it makes the
    transmission extremely fast.
    """
    msg = string.split(string.rstrip(msg), '\n')
    if not msg:
        return
    tot = 0
    QU_BURST = empQueue.QU_BURST
    Send = viewer.ioq.Send
    # Start the tele command
    Send(cmd, postFlag=QU_BURST)
    while msg:
        val = msg[0]
        del msg[0]
        # Alter any suspicious lines so the server doesn't choke on them.
        if val in ("~u", "~p", "~q", "."):
            val = val+" "
        l = len(val)
        # Assume the total bytes in a telegram is 1024.
        if l > 1024:
            l = 1024-l
            msg[:0].insert(val[l:], 0)
            val = val[:l]
        elif tot + l > 1024:
            # Continue message on another tele command
            Send(".", preFlag=QU_BURST, postFlag=QU_BURST, raw=1)
            Send(cmd, preFlag=QU_BURST, postFlag=QU_BURST)
            tot = 0
        Send(val, preFlag=QU_BURST, postFlag=QU_BURST, raw=1)
        tot = tot + l + 1
    Send(".", preFlag=QU_BURST, raw=1)

class CmdRemove(baseCommand):

    description = "Remove a unit (ship, land, plane) from the database"

    defaultPreList = 1
    defaultBinding = (("remove", -3),)

    commandUsage = "remove {s|l|p} <sectors> [<selectors>]"
    commandFormat = re.compile(
        r"^(?P<type>[slp])\s+(?P<sectors>\S+)(?:\s+\?(?P<selectors>\S+))?\s*$|^$")
    
    def receive(self):
        mm = self.parameterMatch
        type, sectors, selectors = mm.group('type', 'sectors', 'selectors')
        if type is None:
            viewer.Error("Wrong unit type")
            return
        if sectors is None:
            viewer.Error("You must provide a range")
            return
        
        if mm.group('type') == 's':
            db = 'SHIPS'
        elif mm.group('type') == 'l':
            db = 'LAND UNITS'
        elif mm.group('type') == 'p':
            db = 'PLANES'

        try:
            list = empEval.getSectors(
                "owner!=-1 and " + empEval.selectToExpr('SECTOR',
                    mm.group('sectors'),
                    mm.group('selectors')),
                db)
        except empEval.error, e:
            viewer.Error(e)
        else:
            for unit in list:
                id = unit[0]
                empDb.megaDB[db].updates([
                    {'id': id, 'owner': empDb.CN_UNOWNED}])

class CmdDanno(baseCommand):
    description = "Dump all annoucements to the screen or a file"

    defaultPrelist = 1
    defaultBinding = (("danno", 2),)

    def receive(self):
        printTime = empDb.megaDB['time'].printTime
        getName = empDb.megaDB['countries'].getName
        for m in empDb.megaDB['announcements']['list']:
            if type(m[0]) == types.TupleType:
                hdr = "> %s%s  dated %s" % (
                    m[0][0], (m[0][1] is not None
                              and " from %s"%getName(m[0][1]) or ""),
                    printTime(m[0][2]))
            else:
                hdr = m[0]
            self.out.data(hdr)
            for l in m[1:]:
                self.out.data(l)
            self.out.data('\n')

class CmdDtele(baseCommand):
    description = "Dump all telegrams to the screen or a file"

    defaultPrelist = 1
    defaultBinding = (("dtele", 2),)

    def receive(self):
        printTime = empDb.megaDB['time'].printTime
        getName = empDb.megaDB['countries'].getName
        for m in empDb.megaDB['telegrams']['list']:
            if type(m[0]) == types.TupleType:
                hdr = "> %s%s  dated %s" % (
                    m[0][0], (m[0][1] is not None
                              and " from %s"%getName(m[0][1]) or ""),
                    printTime(m[0][2]))
            else:
                hdr = m[0]
            self.out.data(hdr)
            for l in m[1:]:
                self.out.data(l)
            self.out.data('\n')

class CmdProjection(baseCommand):
    description = "Computes the new efficiency of all units"

    sendRefresh = "espnlo"
    defaultPrelist = 1
    defaultBinding = (("projection", 4),)

    def receive(self):
        conversion = [
            ('PLANES', 'planetype', '*',    ('lcm', 'hcm', 'mil', 'avail')),
            ('SHIPS', 'shiptype', 'h',      ('lcm', 'hcm', 'avail')),
            ('LAND UNITS', 'landtype', '!', ('lcm', 'hcm', 'gun', 'avail'))
            ]

        self.out.data("Building Projections")
        self.out.data("====================")

        for typ in conversion:
            db = db = empDb.megaDB[typ[0]]
            needed_com = {}

            lst = db.keys()
            lst.sort()
            for id in lst:
                unit = db[id]
                if unit['owner'] != empDb.CN_OWNED:
                    continue
                # if we issue the 'projection' command just after a
                # 'build', we don't know the efficiency of the unit
                # built (maybe empParse.ParseBuild should be updated).
                # So we assume 20% for ships and 10% for planes and land units.
                try:
                    e = unit['eff']
                except KeyError:
                    if typ[0] == 'SHIPS':
                        e = 20
                    else:
                        e = 10

                if e == 100:
                    continue

                coord = (unit['x'],unit['y'])
                try:
                    sect = empDb.megaDB['SECTOR'][coord]
                except KeyError:
                    continue
                if sect['des'] != typ[2]:
                    continue
                for c in typ[3]:
                    if not needed_com.has_key(coord):
                        needed_com[coord] = {}
                    if not needed_com[coord].has_key(c):
                        needed_com[coord][c] = 0.
                    if empDb.megaDB[typ[1]].has_key(unit['type']):
                        needed = empDb.megaDB[typ[1]][unit['type']][c]
                    else:
                        needed = 0
                        viewer.Error("You should issue a 'show "
                        +typ[1][0:-4]+" build' command to update the "
                        "database")
                        return
                    needed_com[coord][c] = needed_com[coord][c] + \
                                           (100.0 - e) * needed / 100.0

            for s in needed_com.keys():
                ok = 1
                for c in typ[3]:
                    stock = 0
                    owner = empDb.megaDB['SECTOR'][s]['owner']
                    if owner == -1 :
                        stock = empDb.megaDB['SECTOR'][s][c]
                    if needed_com[s][c] > stock:
                        if owner == -1 :
                            self.out.data("Sector %d,%d needs %.0f more %s" % (s[0], s[1], needed_com[s][c] - stock, c))
                        else:
                            self.out.data("Sector %d,%d needs %.0f %s  owned by (#%d)" % (s[0], s[1], needed_com[s][c] - stock, c, owner))
                        ok = 0
                if ok == 1:
                    self.out.data("Sector %d,%d is ok." % (s[0], s[1]))
#                print empSector.eff_work_new(empDb.megaDB['SECTOR'][s],
#                                             empDb.megaDB['SECTOR'][s]['avail'])

class CmdDmove(baseCommand):

    sendRefresh = "e"
    defaultBinding = (('dmove', 5),)

    commandUsage = ("dmove <commodity> <src sectors> <min mob> "
                    "[zero] [<dst sectors>]")
    commandFormat = re.compile(
        "^"+empParse.s_comm+"\s+"
        r"(?P<sectors>\S+)(?:\s+\?(?P<selectors>\S+))?\s+"
        r"(?P<mob>\S+)"
        r"(?:\s+(?P<zero>z|ze|zer|zero))?"
        r"(?:\s+(?P<sectors2>\S+)(?:\s+\?(?P<selectors2>\S+))?)?"
        r"\s*$")

    def receive(self):
        mm = self.parameterMatch
        commodity, mob, = mm.group('comm', 'mob')
        
        try: commodity = empEval.commodityTransform[commodity]
        except KeyError:
            viewer.Error("Unknown commodity.")
            return

        if mm.group('zero'):
            minCom = "-1"
        else:
            minCom = "0"
        sectors2 = mm.group('sectors2')
        selectors2 = mm.group('selectors2')
        if sectors2 is None:
            sectors2 = mm.group('sectors')
            selectors2 = mm.group('selectors')
            
        # Call the empEval.foreach function.  empEval.foreach tests every
        # sector in the database to see if arg1 tests true.  If it does, then
        # arg2 is evaluated and inserted into the list.
        try:
            # Return a list for source sectors that contains tuples of the
            # form: ((x, y), sectDB, amount, mobility)
            slist = empEval.foreach(
                ("owner==-1 and "+commodity+">"+commodity[0]+"_dist and "
                 +commodity[0]+"_dist>"+minCom+" and "+empEval.selectToExpr('SECTOR',
                mm.group('sectors'), mm.group('selectors'))),
                ("(xloc+0,yloc+0), __db[1], int("+commodity+"-("+commodity[0]
                 +"_dist)), int(mob-("+mob+"))"),
                'SECTOR')
            # Return a list for destination sectors that contains tuples of the
            # form: ((x, y), sectDB, amount)
            dlist = empEval.foreach(
                ("owner==-1 and "+empEval.selectToExpr('SECTOR',
                    sectors2, selectors2)),
                "(xloc+0,yloc+0), __db[1], int(("+commodity[0]+"_dist)-"+commodity+")",
                'SECTOR')
        except empEval.error, e:
            viewer.Error(e)
            return

        # Create usable dictionaries from the returned list.
        ddict = {}
        for coord, db, amount in dlist:
            if amount > 0 and empSector.is_movable_into(db, commodity):
                ddict[coord] = amount
        sdict = {}
        for coord, db, amount, mobility in slist:
            if (amount > 0 and mobility > 0
                and not ddict.has_key(coord)
                and empSector.is_movable_from(db, commodity)):
                sdict[coord] = (amount, mobility,
                                empSector.move_weight(db, commodity))
##        print "sdict: %s\nddict: %s" % (sdict, ddict)  

        # Send the dictionaries to the move generator
        mmove = empPath.MoveGenerator(commodity, sdict, ddict)

        # Extract the moves and pass to the command queue.
        while not mmove.empty() :
            comm, path, amount = mmove.move()
            self.Send("move %s %d,%d %s %d,%d" % (
                comm, path.start[0], path.start[1], amount,
                path.end[0], path.end[1]),
                      self.out, 1)
            mmove.next()

class CmdSetFood(baseCommand):
    description = "Set food thresholds for maximum population growth"""

    sendRefresh = "e"
    defaultPrelist = 1
    defaultBinding = (("setfood", 4),)

    commandUsage = "setfood <sectors> [no] [force]"
    commandFormat = re.compile(
        "(?P<sectors>\S+)(?:\s+\?(?P<selectors>\S+))?"
        +r"(?:\s+(?P<local>no))?"
        +r"(?:\s+(?P<force>force))?"
        +r"\s*$")

    def receive(self):
        mm = self.parameterMatch
        try:
            list = empEval.getSectors(
                "owner==-1 and " + empEval.selectToExpr('SECTOR',
                mm.group('sectors'),
                mm.group('selectors')),
                'SECTOR')
        except empEval.error, e:
            viewer.Error(e)
            return

        if mm.group('local'):
            local = 1
        else:
            local = 0
        if mm.group('force'):
            force = 1
        else:
            force = 0

        for xy in list:
            sect = empDb.megaDB['SECTOR'][xy]
            new_food = int(empSector.food_needed_for_breed(sect))
            if force == 1:
                new_thr = new_food
            else:
                if new_food > sect['f_dist']:
                    new_thr = new_food
                else:
                    new_thr = sect['f_dist']
            if local == 1:
                sect['f_dist'] = new_thr
            elif new_thr != sect['f_dist']:
                cmd = 'threshold food %d,%d %d' % (xy[0], xy[1], new_thr)
                self.Send(cmd, self.out, 1)

class CmdLTest(baseCommand):
    description = """Compute the amount of mobility a land unit would
    use to reach a given sector."""

    sendRefresh = "el"
    defaultPreList = 1
    defaultBinding = (("ltest", 5),)

    commandUsage = "ltest <land id> <sector>"
    commandFormat = re.compile("(?P<landId>\d+)\s+"+
                               r"(?P<xLoc>-?\d+),(?P<yLoc>-?\d+)")

    def receive(self):
        mm = self.parameterMatch
        if mm is None:
            return
        landId = int(mm.group('landId'))
        try:
            unit = empDb.megaDB['LAND UNITS'][(landId,)]
        except KeyError:
            viewer.Error("Land unit %d doesn't exist." % (landId))
            return
        fromLoc = (unit['x'], unit['y'])
        toLoc = (int(mm.group('xLoc')), int(mm.group('yLoc')))
        if fromLoc == toLoc:
            self.out.data("Using best path 'h', movement cost 0.000")
            self.out.data("Total movement cost cost: 0")
            return
        self.out.data("Looking for best path to %d,%d" % toLoc)
        path = empPath.best_path(fromLoc, toLoc)
        if path is None:
            viewer.Error("Path could not be completed.")
            return
        s = ""
        for i in path.directions:
            s = s + i
        self.out.data("Using best path '%s', movement cost %.3f" % (s,
                                                                    path.cost))
        mcost = path.cost * 5.0 * 480.0 / (unit['spd'] + unit['spd'] *
                                           (50.0 + unit['tech']) /
                                           (200.0 + unit['tech']))
        last_step = empSector.mob_cost(empDb.megaDB['SECTOR'][toLoc])
        last_step = last_step * 5.0 * 480.0 / (unit['spd'] + unit['spd'] *
                                               (50.0 + unit['tech']) /
                                               (200.0 + unit['tech']))
        
        if mcost - last_step > unit['mob']:
            self.out.data("Not enough mobility to go all the way.")
        else:
            newmob = int(unit['mob'] - mcost)
            self.out.data("Total movement cost: %d, new mob: %d" %
                          (unit['mob'] - newmob, newmob))

class CmdCoords(baseCommand):
    description = "Translate coordinates or set translation coordinate"

    sendRefresh = "e"
    defaultPreList = 1
    defaultBinding = (('coordinate', 5),)

    commandUsage = "coordinate <country number> <your x,y> [<their x,y>]"
    commandFormat = re.compile(
        r"^(?P<cnumber>\S+)\s+(?P<yourcoord>\S+)(?:\s+(?P<theircoord>\S+))?$")

    def receive(self):
        mm = self.parameterMatch
        cnumber = mm.group('cnumber')
        coord1 = mm.group('yourcoord')
        coord2 = mm.group('theircoord')
        coordtype = 0
        reverse = 0
        sectors = ''
 
        if int(cnumber) <0:
            cnumber = str(int(cnumber) * -1)
            reverse = 1

        if coord2 is not None:
            coordtype = 1
            x,y = coord1.split(',')
            x = int(x)
            y = int(y)
            tx,ty = coord2.split(',')
            tx = int(tx)
            ty = int(ty)
            deltax = x - tx
            deltay = y - ty
            empDb.megaDB['coordtable'][cnumber] = { 'deltax': deltax, 'deltay': deltay }
            self.out.data("  Country: (#%s) set" % cnumber)
        else:
            deltax = empDb.megaDB['coordtable'][cnumber]['deltax']
            deltay = empDb.megaDB['coordtable'][cnumber]['deltay']
            x,y = coord1.split(',')
            x = int(x)
            y = int(y)
            if not reverse :
                newx = x - deltax
                newy = y - deltay
            else:
                newx = x + deltax
                newy = y + deltay
            newcoord = empDb.sectorWrap((newx,newy))
            self.out.data("  Country: #%s coordinate: %s" % ( cnumber, newcoord))
#               self.out.data("  country number (#%s)  coord1 (%s) " % ( cnumber, coord1))

