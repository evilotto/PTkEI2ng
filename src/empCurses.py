"""Curses support."""

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

import curses
import termios
 
import select
import sys

import empDb
import empQueue
import empCmd

###########################################################################
#############################  Curses support #############################
class Curses:
    """Simple Curses based interface."""

    def __init__(self):
        self.loginCallback = self
        self.login_kill = 0
        self.stayOnline = 0
        self.atPrompt = 0

        self.origState = termios.tcgetattr(sys.stdin.fileno())
        self.stdscr=curses.initscr()
        y, x = self.stdscr.getmaxyx()
        self.outwin = curses.newwin(y-1, x, 0, 0)
        self.outwin.scrollok(1)
        self.promptwin = curses.newwin(1, x, y-1, 0)

    def setprompt(self, prompt):
        """Set the prompt window to the standard empire prompt."""
        self.promptwin.clear()
        self.promptwin.addstr(0, 0, prompt)
        self.promptwin.refresh()
#	pass

    def Begin(self, cmd):
        """empQueue handler: Note the beginning of a command."""
        if self.atPrompt:
            self.outwin.addstr(cmd)
        else:
            self.outwin.addstr("\n"+empDb.GetPrompt()+cmd)
            self.atPrompt = 0

    def data(self, msg):
        """empQueue handler: Process a line of server data."""
        self.outwin.addstr("\n"+msg)
        self.atPrompt = 0

##      def flush(self, msg, hdl):
##  	"""empQueue handler: Handle a subprompt."""
##  	if hdl is None:
##  	    print msg
##  	    return
##  	try:
##  	    cmd = raw_input(msg)
##  	except KeyboardInterrupt:
##  	    cmd = "ctlc"
##  	    print
##  	hdl(cmd)
##  	self.atPrompt = 0

    def End(self, cmd):
        """empQueue handler: Note the end of a command."""
        p = empDb.GetPrompt()
        self.outwin.addstr("\n" + p)
        self.setprompt(p)
        self.atPrompt = 1

    flush = Answer = updateDB = empQueue.doNothing

    def inform(self):
        """empQueue handler: Process an asynchronous prompt update."""
        p = empDb.GetPrompt()
        if self.atPrompt == 1:
            self.outwin.addstr("\n" + p)
        self.setprompt(p)

    def flash(self, msg):
        """empQueue handler: Process an asynchronous line of data."""
        self.outwin.addstr("\n" + msg)
        self.atPrompt = 0

    Error = flash

    def login_error(self, msg):
        """empQueue/login handler: Report a login error."""
        print msg
        # HACK! See if we are online..
        if self.ioq.sock.flags >= empQueue.QU_DISCONNECT:
            ldb = empDb.megaDB['login']
            t = raw_input("host[%s]: " % ldb['host'])
            if t:
                ldb['host'] = t
            while 1:
                t = raw_input("port[%s]: " % ldb['port'])
                if t:
                    try: t = int(t)
                    except ValueError:
                        continue
                    ldb['port'] = t
                break
        # Hack! Check if we need to kill
        if msg[:22] == "[3] country in use by ":
            t = raw_input("Try to issue a kill? [n] ")
            if t[:1] == 'y' or t[:1] == 'Y':
                self.login_kill = 1
                self.loginHandler.retry()
                return
            self.login_kill = 0
        ldb = empDb.megaDB['login']
        t = raw_input("Country? [%s] " % ldb['coun'])
        if t:
            ldb['coun'] = t
        t = raw_input("Representative? [%s] " % ldb['repr'])
        if t:
            ldb['repr'] = t
        self.loginHandler.retry()

    def login_success(self):
        """empQueue/login handler: Note a successful login."""
        pass

    def connect_success(self):
        """empQueue/login handler: Note a server connection."""
        self.stayOnline = 1

    def connect_terminate(self):
        """empQueue/login handler: Note a server disconnect."""
        self.stayOnline = 0

    def Process(self):
        """empQueue handler: Note a lull in socket activity."""
        pass

    def main(self):
        """empire.py callback: Start the main input/output loop."""
        try:
            # Start curses
#	    self.promptwin.nodelay(1)
#	    curses.intrflush(1)
            curses.noecho()
            curses.cbreak()
            self.promptwin.keypad(1)

            self.cmd = ""
            while self.stayOnline:
                pending = select.select([self.ioq, sys.stdin], [], [])[0]
                if pending and pending[0] == self.ioq:
                    self.ioq.HandleInput()
                    del pending[0]
#		    self.outwin.refresh()
                if pending and pending[0] == sys.stdin:
##  		    cmd = self.promptwin.getstr()
##  		    try:
##  			self.ioq.HistSend(cmd)
##  		    except IndexError:
##  			print "History substitution error."
##  		    self.promptwin.move(0,0)
##  		    self.promptwin.clrtoeol()
#		    buf = sys.stdin.read()
#		    map(curses.ungetch, map(ord, buf))
#		    while 1:
                    ch = self.promptwin.getch()
                    if ch < 0:
                        break
                    if ch == ord("\n"):
                        try:
                            self.ioq.HistSend(self.cmd)
                        except IndexError:
                            curses.beep()
                        self.promptwin.move(0,0)
                        self.promptwin.clrtoeol()
                        self.cmd = ""
                    elif ch > 255:
                        # Function key
                        if ch == curses.KEY_UP or ch == curses.KEY_DOWN:
                            if ch == curses.KEY_UP:
                                offset = 1
                            else:
                                offset = -1
                            try:
                                self.cmd = self.ioq.HistMove(offset, self.cmd)
                            except IndexError:
                                curses.beep()
                            else:
                                self.promptwin.clear()
                                self.promptwin.addstr(0, 0, empDb.GetPrompt()
                                                      + self.cmd)
                    else:
#			print 'got ' + chr(ch)
#			self.stdscr.addstr(0, 0, cmd)
                        self.cmd = self.cmd + chr(ch)
                        self.promptwin.addstr(chr(ch))
##  			self.promptwin.move(0,0)
##  			self.promptwin.clrtoeol()
##  			self.promptwin.addstr(0, 0, empDb.GetPrompt() + cmd)
                self.outwin.refresh()
                self.promptwin.refresh()
        finally:
#	    self.promptwin.nodelay(0)
            self.promptwin.keypad(0)
            curses.flushinp()
            curses.echo()
            curses.nocbreak()
            curses.endwin()
#	    termios.tcsetattr(sys.stdin.fileno(), TERMIOS.TCSANOW, self.origState)
#	    termios.tcflush(sys.stdin.fileno(), TERMIOS.TCIOFLUSH)
#	    termios.tcflush(sys.stdout.fileno(), TERMIOS.TCIOFLUSH)
#	    termios.tcflush(sys.stderr.fileno(), TERMIOS.TCIOFLUSH)
#	    sys.stdin.flush()
#	    sys.stdout.flush()
#	    while 1:
#		pass
