"""Text-only support."""

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

import select
import sys
import string
# Readline is not practical because there is no way to interleave terminal
# input and socket input using the current Python implementation of readline.
#import readline

import empDb
import empQueue
import empCmd

# Key Ideas:

# What is contained within this file:

# This file contains the simple text viewer interface.  The text viewer is
# a fall back for the graphical interface.  The text interface is designed
# for compatibility of the Tk interface, not vice-versa.  Please see the
# documentation of empQueue.py for information on the structure of the
# viewer class.


# Global variables:

# viewer : For Text clients, viewer is an instance of class SText.

###########################################################################
#############################  Text interface #############################
class SText:
    """Simple ASCII Text interface."""

    def __init__(self):
        self.loginCallback = self
        self.login_kill = 0
        self.stayOnline = 0
        self.atPrompt = 0

    def Begin(self, cmd):
        """empQueue handler: Note the beginning of a command."""
        if self.atPrompt:
            sys.stdout.write("")
            print "[[%s]]" % cmd
            self.atPrompt = 0

    def data(self, msg):
        """empQueue handler: Process a line of server data."""
        print msg
        self.atPrompt = 0

    def flush(self, msg, hdl):
        """empQueue handler: Handle a subprompt."""
        if hdl is None:
            print msg
            return
        try:
            cmd = raw_input(msg)
        except KeyboardInterrupt:
            cmd = "ctlc"
            print
        hdl(cmd)
        self.atPrompt = 0

    def End(self, cmd):
        """empQueue handler: Note the end of a command."""
        if self.atPrompt:
            print
        print empDb.GetPrompt(),
        sys.stdout.flush()
        self.atPrompt = 1

    Answer = Process = empQueue.doNothing

    def inform(self):
        """empQueue handler: Process an asynchronous prompt update."""
        if self.atPrompt:
            sys.stdout.write("")
            print "\n"+empDb.GetPrompt(),
            sys.stdout.flush()

    def flash(self, msg):
        """empQueue handler: Process an asynchronous line of data."""
        if self.atPrompt:
            sys.stdout.write("")
            print
            self.atPrompt = 0
        print msg

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

    def main(self):
        """empire.py callback: Start the main input/output loop."""
        # Hack!  Wait for the connect before continuing.
        while not self.stayOnline:
            cmd = raw_input("Off-line: ")
            try:
                self.ioq.HistSend(cmd)
            except IndexError:
                print "History substitution error."
        # Ok, we are online now.
        while self.stayOnline:
            pending = select.select([self.ioq, sys.stdin], [], [])[0]
            if pending and pending[0] == self.ioq:
                self.ioq.HandleInput()
                del pending[0]
            if pending and pending[0] == sys.stdin:
                try:
                    cmd = raw_input()
                except EOFError:
                    cmd = "ctld"
                    print
                if self.atPrompt:
                    sys.stdout.write("")
                    self.atPrompt = 0
                try:
                    self.ioq.HistSend(cmd)
                except IndexError:
                    print "History substitution error."
                del pending[0]
